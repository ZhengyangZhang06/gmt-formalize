import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.LinearAlgebra.Trace
import Poincare.SimonGMT.Chapter03.Rectifiable

/-!
# Simon, *Introduction to GMT*, Chapter 5: The Allard Regularity Theorem (pp. 103–130)

Frozen problem statement.  Conventions (Simon's "Notation", p. ix):
* `B_ρ(y)` is the **closed** ball (`Metric.closedBall`), `B̆_ρ(y)` the open ball (`Metric.ball`);
* `ℝ^{n+ℓ}` is `EuclideanSpace ℝ (Fin (n + ℓ))`, whose first `n` coordinates span `ℝⁿ × {0}`;
* `Hⁿ` is Mathlib's `μHE[n]` (normalized so that `Hⁿ = Lⁿ` on `n`-planes, as in Simon);
* `ω_n = π^{n/2}/Γ(n/2+1)`;
* `|A|` for a linear map is the inner-product (Hilbert–Schmidt) norm `(Σ_{ij} A_{ij}²)^{1/2}`
  (Simon p. ix and footnote 2 on p. 115).
* All results are stated for `n ≥ 1` (the book's `n`-dimensional setting) and arbitrary `ℓ`.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal

namespace GMT.Ch05

/-- Ambient space `ℝ^{n+ℓ}`. -/
abbrev Amb (n ℓ : ℕ) := EuclideanSpace ℝ (Fin (n + ℓ))

/-- Euclidean space `ℝᵐ`. -/
abbrev Rn (m : ℕ) := EuclideanSpace ℝ (Fin m)

/-- `ω_n = π^{n/2} / Γ(n/2 + 1)` (Simon, Notation p. ix): the volume of the unit ball of `ℝⁿ`. -/
noncomputable def unitBallVolume (n : ℕ) : ℝ :=
  Real.pi ^ ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2 + 1)

/-- Squared Hilbert–Schmidt ("inner product") norm `|A|² = Σ_i |A eᵢ|² = Σ_{i,j} A_{ji}²`
(Simon, Notation p. ix; Ch. 5 footnote 2 p. 115 and Remark 4.4). -/
noncomputable def hsNormSq {m k : ℕ} (A : Rn m →L[ℝ] Rn k) : ℝ :=
  ∑ i : Fin m, ‖A (EuclideanSpace.single i 1)‖ ^ 2

/-- Hilbert–Schmidt norm `|A| = (Σ_{i,j} A_{ji}²)^{1/2}`; for `A = Du` this is Simon's `|Du|`. -/
noncomputable def hsNorm {m k : ℕ} (A : Rn m →L[ℝ] Rn k) : ℝ :=
  Real.sqrt (hsNormSq A)

/-- The point `(x, y) ∈ ℝⁿ × ℝ^ℓ = ℝ^{n+ℓ}` (first `n` coordinates `x`, last `ℓ` coordinates `y`). -/
noncomputable def graphPoint {n ℓ : ℕ} (x : Rn n) (y : Rn ℓ) : Amb n ℓ :=
  WithLp.toLp 2 (Fin.append (WithLp.ofLp x) (WithLp.ofLp y))

/-- `graph u = {(x, u(x)) : x ∈ D} ⊆ ℝ^{n+ℓ}` for `u : D ⊆ ℝⁿ → ℝ^ℓ`. -/
noncomputable def graphOver {n ℓ : ℕ} (u : Rn n → Rn ℓ) (D : Set (Rn n)) : Set (Amb n ℓ) :=
  (fun x => graphPoint x (u x)) '' D

/-- The coordinate plane `ℝⁿ × {0} ⊆ ℝ^{n+ℓ}`. -/
noncomputable def horizontalPlane (n ℓ : ℕ) : Submodule ℝ (Amb n ℓ) :=
  Submodule.span ℝ (Set.range fun i : Fin n => EuclideanSpace.single (Fin.castAdd ℓ i) (1 : ℝ))

/-- The rotated plane `q(ℝⁿ × {0})` for a linear isometry `q` of `ℝ^{n+ℓ}`. -/
noncomputable def rotatedPlane {n ℓ : ℕ} (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) : Submodule ℝ (Amb n ℓ) :=
  (horizontalPlane n ℓ).map q.toLinearEquiv.toLinearMap

/-- Simon Ch. 2 §4 (p. 55), definition preceding 4.1, with `r = 1`: `S ⊆ ℝ^N` is an
`m`-dimensional `C¹` submanifold if each `y ∈ S` has open `V ⊆ ℝᵐ`, `W ∋ y` and a 1:1 `C¹` map
`φ : V → W` with `φ(V) = W ∩ S`, `φ` proper (`K ⊆ W` compact ⇒ `φ⁻¹(K)` compact in `V`) and
`Dφ(x)` of rank `m` (injective) for all `x ∈ V`. -/
def IsC1Submanifold (m : ℕ) {N : ℕ} (S : Set (EuclideanSpace ℝ (Fin N))) : Prop :=
  ∀ y ∈ S, ∃ (V : Set (Rn m)) (W : Set (EuclideanSpace ℝ (Fin N)))
    (φ : Rn m → EuclideanSpace ℝ (Fin N)),
    IsOpen V ∧ IsOpen W ∧ y ∈ W ∧ ContDiffOn ℝ 1 φ V ∧ InjOn φ V ∧ φ '' V = W ∩ S ∧
    (∀ K, IsCompact K → K ⊆ W → IsCompact (V ∩ φ ⁻¹' K)) ∧
    ∀ x ∈ V, Function.Injective (fderiv ℝ φ x)

/-- `u ∈ C^{k,α}(W)` for open `W`: `u` is `C^k` on `W`, all derivatives of order `≤ k` are bounded on
`W`, and the `k`-th derivative is `α`-Hölder on `W` (finite global seminorm).  Used for the
qualitative Hölder classes of Theorem 7.1 (any fixed norm on multilinear maps gives the same class). -/
def IsHolderCkα {m k : ℕ} (j : ℕ) (α : ℝ) (u : Rn m → Rn k) (W : Set (Rn m)) : Prop :=
  ContDiffOn ℝ j u W ∧
  (∃ B : ℝ, ∀ i ≤ j, ∀ x ∈ W, ‖iteratedFDeriv ℝ i u x‖ ≤ B) ∧
  ∃ K : ℝ, ∀ x ∈ W, ∀ y ∈ W,
    ‖iteratedFDeriv ℝ j u x - iteratedFDeriv ℝ j u y‖ ≤ K * ‖x - y‖ ^ α

/-- `h` is `C^{k,α}` in the open set `U` (locally): `C^k` on `U`, and the `k`-th derivative is
`α`-Hölder on each compact subset of `U` (Simon 7.1, "a `C^{q,α}` function in `U`"). -/
def IsLocallyHolderCkα {m k : ℕ} (j : ℕ) (α : ℝ) (h : Rn m → Rn k) (U : Set (Rn m)) : Prop :=
  ContDiffOn ℝ j h U ∧
  ∀ K, IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K,
    ‖iteratedFDeriv ℝ j h x - iteratedFDeriv ℝ j h y‖ ≤ C * ‖x - y‖ ^ α

/-- A rectifiable `n`-varifold `V = v(M, θ)` in the open set `U ⊆ ℝ^{n+ℓ}`
(Simon Ch. 4, introduction p. 85, and 3.14): only the primitive data `M ⊆ U` and `θ`, with
* `M` countably `n`-rectifiable (Ch. 3, 1.1; SimonGMT `Chapter03.CountablyRectifiable`) and
  `Hⁿ`-measurable;
* `θ` positive on `M`, `Hⁿ`-measurable, and locally `Hⁿ`-integrable on `M` in `U`.
No tangent-plane data is stored: tangent planes are *defined* below (`tangentProj`) as approximate
tangent spaces where they exist (their a.e. existence is Ch. 3, 1.9, a theorem). -/
structure RectifiableVarifold (n ℓ : ℕ) (U : Set (Amb n ℓ)) where
  /-- The carrier `M`. -/
  carrier : Set (Amb n ℓ)
  /-- The multiplicity function `θ` (its values off `M` are irrelevant). -/
  mult : Amb n ℓ → ℝ
  carrier_subset : carrier ⊆ U
  nullMeasurableSet_carrier : NullMeasurableSet carrier (μHE[n] : Measure (Amb n ℓ))
  countablyRectifiable : Poincare.SimonGMT.Chapter03.CountablyRectifiable n carrier
  mult_pos : ∀ x ∈ carrier, 0 < mult x
  aemeasurable_mult : AEMeasurable mult ((μHE[n] : Measure (Amb n ℓ)).restrict carrier)
  integrableOn_mult : ∀ K : Set (Amb n ℓ), IsCompact K → K ⊆ U →
    IntegrableOn mult (carrier ∩ K) (μHE[n] : Measure (Amb n ℓ))

namespace RectifiableVarifold

variable {n ℓ : ℕ} {U : Set (Amb n ℓ)} (V : RectifiableVarifold n ℓ U)

/-- Simon Ch. 4, 1.1: the weight measure `μ_V = Hⁿ ⌞ θ` (with `θ = 0` off `M`). -/
noncomputable def weight : Measure (Amb n ℓ) :=
  ((μHE[n] : Measure (Amb n ℓ)).restrict V.carrier).withDensity
    (fun x => ENNReal.ofReal (V.mult x))

/-- Simon Ch. 4, 1.4: `spt V = spt μ_V`, taken inside the open set `U` where `V` lives. -/
def support : Set (Amb n ℓ) := U ∩ V.weight.support

open Classical in
/-- Orthogonal projection `p_{T_x M}` onto the tangent space `T_x V` (Simon Ch. 4, 1.3): the
approximate tangent space of `M` with respect to `θ` (Ch. 3, 1.7/1.9; SimonGMT
`Chapter03.HasWeightedApproximateTangentSpaceAt`) **where it exists**, and `0` elsewhere.  It is
unique on `M` (where `θ > 0`) and exists `μ_V`-a.e. by Ch. 3, 1.9 — a theorem, not an assumption. -/
noncomputable def tangentProj (x : Amb n ℓ) : Amb n ℓ →L[ℝ] Amb n ℓ :=
  if h : ∃ P : Submodule ℝ (Amb n ℓ),
      Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x P
  then (Classical.choose h).starProjection else 0

/-- Tangential divergence `div_M X (x) = Σ_{i,j} e^{ij}(x) D_i X^j(x) = trace(DX(x) ∘ p_{T_x M})`
(Simon Ch. 2, 4.18; Ch. 4, 2.3). -/
noncomputable def divM (X : Amb n ℓ → Amb n ℓ) (x : Amb n ℓ) : ℝ :=
  LinearMap.trace ℝ (Amb n ℓ) ((fderiv ℝ X x).toLinearMap ∘ₗ (V.tangentProj x).toLinearMap)

/-- Simon Ch. 4, Definition 3.14: `V` has generalized mean curvature `H` in `U` if
`∫ div_M X dμ_V = -∫ X · H dμ_V` for all `X ∈ C¹_c(U; ℝ^{n+ℓ})`; the implicit requirement that the
right side exist for every such `X` is the local `μ_V`-integrability of `H` on `U`. -/
def HasGeneralizedMeanCurvature (H : Amb n ℓ → Amb n ℓ) : Prop :=
  LocallyIntegrableOn H U V.weight ∧
  ∀ X : Amb n ℓ → Amb n ℓ, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U →
    ∫ x, V.divM X x ∂V.weight = -∫ x, inner ℝ (X x) (H x) ∂V.weight

/-- `H` is locally in `Lᵖ(μ_V)` in `U`: `∫_K |H|ᵖ dμ_V < ∞` for every compact `K ⊆ U`. -/
def LocallyLp (H : Amb n ℓ → Amb n ℓ) (p : ℝ) : Prop :=
  ∀ K : Set (Amb n ℓ), IsCompact K → K ⊆ U → ∫⁻ x in K, ‖H x‖ₑ ^ p ∂V.weight < ∞

/-- `Θⁿ(μ_V, x) = t`: `μ_V(B_r(x)) / (ω_n rⁿ) → t` as `r ↓ 0` (Simon Ch. 1 §3; Ch. 4). -/
def HasDensity (x : Amb n ℓ) (t : ℝ) : Prop :=
  Tendsto (fun r : ℝ => V.weight (closedBall x r) / ENNReal.ofReal (unitBallVolume n * r ^ n))
    (𝓝[>] 0) (𝓝 (ENNReal.ofReal t))

/-- Simon Ch. 5, 4.1 (p. 115): tilt-excess
`E(ξ, σ, T) = σ⁻ⁿ ∫_{B_σ(ξ)} |p_{T_x M} − p_T|² dμ_V` (Hilbert–Schmidt norm, **no** factor `1/2`;
`B_σ(ξ)` closed).  Defined by the book only when `B_σ(ξ) ⊆ U`. -/
noncomputable def tiltExcess (ξ : Amb n ℓ) (σ : ℝ) (T : Submodule ℝ (Amb n ℓ)) : ℝ :=
  (σ ^ n)⁻¹ * ∫ x in closedBall ξ σ, hsNormSq (V.tangentProj x - T.starProjection) ∂V.weight

/-- `(σ^{p−n} ∫_{B_σ(ξ)} |H|ᵖ dμ_V)^{1/p}` as an extended real (no junk value when infinite). -/
noncomputable def scaledLpNorm (H : Amb n ℓ → Amb n ℓ) (p : ℝ) (ξ : Amb n ℓ) (σ : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (σ ^ (p - n)) * ∫⁻ x in closedBall ξ σ, ‖H x‖ₑ ^ p ∂V.weight) ^ (1 / p)

/-- Simon Ch. 5, p. 116 (before 4.5):
`E_*(ξ, σ, T) = max{E(ξ, σ, T), δ⁻¹ (σ^{p−n} ∫_{B_σ(ξ)} |H|ᵖ dμ_V)^{2/p}}`, `δ` as in 2.3. -/
noncomputable def tiltExcessStar (H : Amb n ℓ → Amb n ℓ) (p δ : ℝ) (ξ : Amb n ℓ) (σ : ℝ)
    (T : Submodule ℝ (Amb n ℓ)) : ℝ :=
  max (V.tiltExcess ξ σ T) (δ⁻¹ * (V.scaledLpNorm H p ξ σ).toReal ^ 2)

/-- `sup {dist(x − ξ, T) : x ∈ spt V ∩ B_σ(ξ)}` (Simon 2.5), as an extended real. -/
noncomputable def heightSup (ξ : Amb n ℓ) (σ : ℝ) (T : Submodule ℝ (Amb n ℓ)) : ℝ≥0∞ :=
  ⨆ x ∈ V.support ∩ closedBall ξ σ, ENNReal.ofReal (infDist (x - ξ) (T : Set (Amb n ℓ)))

/-- The standing hypotheses 2.3 = 5.1 of Simon Ch. 5 (pp. 108, 121), for `V` with generalized
mean curvature `H` in `U`:
`θ ≥ 1 μ_V-a.e.`, `0 ∈ spt V`, `B_ρ(0) ⊆ U`, `ω_n⁻¹ ρ⁻ⁿ μ_V(B_ρ(0)) ≤ 1 + δ`,
`(ρ^{p−n} ∫_{B_ρ(0)} |H|ᵖ dμ_V)^{1/p} ≤ δ` (and `ρ > 0`). -/
def AllardHypotheses (H : Amb n ℓ → Amb n ℓ) (p δ ρ : ℝ) : Prop :=
  0 < ρ ∧ V.HasGeneralizedMeanCurvature H ∧ (∀ᵐ x ∂V.weight, 1 ≤ V.mult x) ∧
  (0 : Amb n ℓ) ∈ V.support ∧ closedBall (0 : Amb n ℓ) ρ ⊆ U ∧
  V.weight (closedBall 0 ρ) ≤ ENNReal.ofReal ((1 + δ) * (unitBallVolume n * ρ ^ n)) ∧
  V.scaledLpNorm H p 0 ρ ≤ ENNReal.ofReal δ

/-- Simon Ch. 5, 7.2 (p. 128): `ξ ∈ spt V` is a regular point if `B̆_ρ(ξ) ∩ spt V` is an
`n`-dimensional `C¹` submanifold of `ℝ^{n+ℓ}` for some `ρ > 0`; `reg V` is the set of regular points
(and `sing V = spt V \ reg V`). -/
def regularSet : Set (Amb n ℓ) :=
  {ξ | ξ ∈ V.support ∧ ∃ ρ > 0, IsC1Submanifold n (ball ξ ρ ∩ V.support)}

end RectifiableVarifold

open RectifiableVarifold

/-- `ρ⁻¹ sup_B |u| + sup_B |Du| + ρ^α sup_{x ≠ y ∈ B} |x − y|^{−α} |Du(x) − Du(y)|` on a set `B`
(the quantity estimated in Simon 5.2), with `Du` the derivative within `B` and `|·|` the
Hilbert–Schmidt norm; as an extended real, so suprema never take junk values. -/
noncomputable def scaledC1AlphaNorm {n ℓ : ℕ} (u : Rn n → Rn ℓ) (B : Set (Rn n)) (α ρ : ℝ) :
    ℝ≥0∞ :=
  ENNReal.ofReal ρ⁻¹ * (⨆ x ∈ B, ‖u x‖ₑ) +
  (⨆ x ∈ B, ENNReal.ofReal (hsNorm (fderivWithin ℝ u B x))) +
  ENNReal.ofReal (ρ ^ α) * ⨆ x ∈ B, ⨆ y ∈ B, ⨆ (_ : x ≠ y),
    ENNReal.ofReal (hsNorm (fderivWithin ℝ u B x - fderivWithin ℝ u B y) / ‖x - y‖ ^ α)

/-- The conclusion of Simon 5.2 for radius `γρ` and constant `C`: there are a linear isometry `q`
of `ℝ^{n+ℓ}` and `u ∈ C^{1,1−n/p}(B_{γρ}(0); ℝ^ℓ)` (closed ball) with `u(0) = 0`, `Du(0) = 0`,
`spt V ∩ B_{γρ}(0) = q(graph u) ∩ B_{γρ}(0)`, and
`ρ⁻¹ sup|u| + sup|Du| + ρ^{1−n/p} [Du]_{1−n/p} ≤ C δ^{1/(2n+2)}`. -/
def AllardConclusion {n ℓ : ℕ} {U : Set (Amb n ℓ)} (V : RectifiableVarifold n ℓ U)
    (p δ ρ γ C : ℝ) : Prop :=
  ∃ (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (u : Rn n → Rn ℓ),
    ContDiffOn ℝ 1 u (closedBall 0 (γ * ρ)) ∧ u 0 = 0 ∧
    fderivWithin ℝ u (closedBall 0 (γ * ρ)) 0 = 0 ∧
    V.support ∩ closedBall 0 (γ * ρ) =
      q '' graphOver u (closedBall 0 (γ * ρ)) ∩ closedBall 0 (γ * ρ) ∧
    scaledC1AlphaNorm u (closedBall 0 (γ * ρ)) (1 - n / p) ρ ≤
      ENNReal.ofReal (C * δ ^ (1 / (2 * (n : ℝ) + 2)))

/-- `W^{1,2}(Ω)` with weak gradient `g` (Simon, Notation p. ix): `f, g ∈ L²(Ω)` and
`∫_Ω f ∇ζ = −∫_Ω ζ g` for every `ζ ∈ C^∞_c(Ω)`. -/
def IsW12WithGradient {n : ℕ} (f : Rn n → ℝ) (g : Rn n → Rn n) (Ω : Set (Rn n)) : Prop :=
  MemLp f 2 (volume.restrict Ω) ∧ MemLp g 2 (volume.restrict Ω) ∧
  ∀ ζ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ → tsupport ζ ⊆ Ω →
    ∫ x in Ω, f x • gradient ζ x = -∫ x in Ω, ζ x • g x

/-! ## Headline results -/

/-- **Simon Ch. 5, Lemma 2.1 (p. 107).**  Let `V = v(M, θ)` have generalized mean curvature `H` in
the open set `U ⊆ ℝ^{n+ℓ}` (no lower bound on `θ` is needed).  If `B_ρ(ξ) ⊆ U`, then for every
`n`-dimensional subspace `T`,
`E(ξ, ρ/2, T) ≤ C ρ⁻ⁿ ∫_{B_ρ(ξ)} (dist(x − ξ, T)/ρ)² dμ_V + C ρ^{2−n} ∫_{B_ρ(ξ)} |H|² dμ_V`,
with `C = C(n)` (independent of `ℓ`).  The `|H|²` term is an extended-real integral (it may be
infinite, in which case the inequality is trivial). -/
def TiltExcessHeightEstimate : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ C : ℝ, ∀ (ℓ : ℕ) (U : Set (Amb n ℓ)), IsOpen U →
  ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ), V.HasGeneralizedMeanCurvature H →
  ∀ (ξ : Amb n ℓ) (ρ : ℝ), 0 < ρ → closedBall ξ ρ ⊆ U →
  ∀ T : Submodule ℝ (Amb n ℓ), Module.finrank ℝ T = n →
    ENNReal.ofReal (V.tiltExcess ξ (ρ / 2) T) ≤
      ENNReal.ofReal (C * (ρ ^ n)⁻¹ *
        ∫ x in closedBall ξ ρ, (infDist (x - ξ) (T : Set (Amb n ℓ)) / ρ) ^ 2 ∂V.weight) +
      ENNReal.ofReal (C * ρ ^ ((2 : ℝ) - n)) * ∫⁻ x in closedBall ξ ρ, ‖H x‖ₑ ^ 2 ∂V.weight

/-- **Simon Ch. 5, Lemma 2.5 (Affine Approximation Lemma, p. 108)**, `p > n` (standing assumption of
the chapter).  There is `C = C(n, ℓ, p) > 0` such that if `δ ∈ (0, 1/4]` and 2.3 holds, then for each
`ξ ∈ spt V ∩ B_{δρ}(0)` and `σ ∈ (0, 2δρ]` there is an `n`-dimensional subspace `T` with
`C⁻¹ (σ⁻ⁿ ∫_{B_{σ/2}(ξ)} |p_{T_x M} − p_T|² dμ_V)^{1/2}
   ≤ σ⁻¹ sup{dist(x, ξ + T) : x ∈ spt V ∩ B_σ(ξ)} + (σ^{p−n} ∫_{B_σ(ξ)} |H|ᵖ dμ_V)^{1/p}`
and `σ⁻¹ sup{dist(x, ξ + T) : x ∈ spt V ∩ B_σ(ξ)} ≤ C δ^{1/(2n+2)}`.

*Correction:* the printed first inequality of (‡) omits the mean-curvature term
`(σ^{p−n}∫|H|ᵖ)^{1/p}`; the book derives it "directly from Remark 2.2", which contains exactly this
term, so we state the inequality that the cited argument proves.  (Since this term is `≤ δ`, it
still gives the tilt bound `σ⁻ⁿ∫_{B_{σ/2}(ξ)}|p_{T_xM} − p_T|² ≤ C δ^{1/(n+1)}` used later.) -/
def AffineApproximationLemma : Prop :=
  ∀ n ℓ : ℕ, 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∃ C : ℝ, 0 < C ∧
  ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ)
    (δ ρ : ℝ), 0 < δ → δ ≤ 1 / 4 → V.AllardHypotheses H p δ ρ →
  ∀ ξ ∈ V.support ∩ closedBall 0 (δ * ρ), ∀ σ : ℝ, 0 < σ → σ ≤ 2 * δ * ρ →
  ∃ T : Submodule ℝ (Amb n ℓ), Module.finrank ℝ T = n ∧
    ENNReal.ofReal (C⁻¹ * Real.sqrt ((σ ^ n)⁻¹ *
        ∫ x in closedBall ξ (σ / 2), hsNormSq (V.tangentProj x - T.starProjection) ∂V.weight)) ≤
      ENNReal.ofReal σ⁻¹ * V.heightSup ξ σ T + V.scaledLpNorm H p ξ σ ∧
    ENNReal.ofReal σ⁻¹ * V.heightSup ξ σ T ≤ ENNReal.ofReal (C * δ ^ (1 / (2 * (n : ℝ) + 2)))

/-- **Simon Ch. 5, Lemma 2.6 (Lipschitz Approximation Lemma, p. 110)**, `p > n`.  There are
`β = β(n, ℓ, p) ∈ (0, 1/4]` and `C = C(n, ℓ, p)` such that: let `L ∈ (0, 1]`,
`δ ∈ (0, (βL)^{2n+2}]`, 2.3 hold, `σ₀ = δρ`, and let `T₀ = q(ℝⁿ × {0})` (`q` a linear isometry) be a
plane with `dist(x, T₀) ≤ K δ^{1/(2n+2)} σ₀` for `x ∈ spt V ∩ B_{2σ₀}(0)`.  Then there is
`f : Bⁿ_{σ₀/2}(0) → ℝ^ℓ` with `Lip f ≤ L`, `sup |f| ≤ K δ^{1/(2n+2)} σ₀` and
`μ_V(B_{σ₀/2}(0) ∩ (spt V \ q(graph f))) + Hⁿ(B_{σ₀/2}(0) ∩ (q(graph f) \ spt V))
   ≤ C L⁻² ∫_{B_{σ₀}(0)} |p_{T_x M} − p_{T₀}|² dμ_V`.

The book takes (w.l.o.g., after a rotation) `T₀ = T(2σ₀, 0) = ℝⁿ × {0}` from Lemma 2.5, which
satisfies the height hypothesis with `K = 2C₂.₅`; we state the rotation explicitly and allow any
such plane. The statement remains true for every `K` with `β, C` independent of `K`: if the tilt of
`T₀` on `B_{σ₀}` exceeds `c²L²` the estimate holds with `f = 0`; otherwise `T₀` is `CL`-close to
`T(2σ₀, 0)` and the book's construction applies relative to `T₀`.
*Correction:* printed `sup|f| ≤ Cδ^{1/(2n+2)}` lacks the scale factor `σ₀` (cf. 2.7 and proof (7)). -/
def LipschitzApproximationLemma : Prop :=
  ∀ n ℓ : ℕ, 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∃ β C : ℝ, 0 < β ∧ β ≤ 1 / 4 ∧
  ∀ L K : ℝ, 0 < L → L ≤ 1 → 0 ≤ K →
  ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ)
    (δ ρ : ℝ), 0 < δ → δ ≤ (β * L) ^ (2 * n + 2) → V.AllardHypotheses H p δ ρ →
  ∀ q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ,
    (∀ x ∈ V.support ∩ closedBall 0 (2 * (δ * ρ)),
      infDist x (rotatedPlane q : Set (Amb n ℓ)) ≤ K * δ ^ (1 / (2 * (n : ℝ) + 2)) * (δ * ρ)) →
  ∃ f : Rn n → Rn ℓ, LipschitzOnWith (Real.toNNReal L) f (closedBall 0 (δ * ρ / 2)) ∧
    (∀ x ∈ closedBall (0 : Rn n) (δ * ρ / 2),
      ‖f x‖ ≤ K * δ ^ (1 / (2 * (n : ℝ) + 2)) * (δ * ρ)) ∧
    V.weight (closedBall 0 (δ * ρ / 2) ∩
        (V.support \ q '' graphOver f (closedBall 0 (δ * ρ / 2)))) +
      (μHE[n] : Measure (Amb n ℓ)) (closedBall 0 (δ * ρ / 2) ∩
        (q '' graphOver f (closedBall 0 (δ * ρ / 2)) \ V.support)) ≤
      ENNReal.ofReal (C * (L ^ 2)⁻¹ * ∫ x in closedBall 0 (δ * ρ),
        hsNormSq (V.tangentProj x - (rotatedPlane q).starProjection) ∂V.weight)

/-- **Simon Ch. 5, Corollary 2.7 (p. 113)**, `p > n`.  With the notation and assumptions of
Lemma 2.6 (as formalized in `LipschitzApproximationLemma`), `β = β(n, ℓ, p)` can be chosen so that
`sup_{ξ ∈ spt V ∩ B_{σ₀/2}(0), σ ∈ (0, σ₀/2]} σ⁻ⁿ ∫_{B_σ(ξ)} |p_{T_x M} − p_{T₀}|² dμ_V ≤ β² L²`
implies `spt V ∩ B_{σ₀/4}(0) = q(graph f) ∩ B_{σ₀/4}(0)` for some `f : Bⁿ_{σ₀/4}(0) → ℝ^ℓ` with
`Lip f ≤ L` and `sup |f| ≤ K δ^{1/(2n+2)} σ₀` (book: `C δ^{1/(2n+2)} σ₀`). -/
def LipschitzGraphCorollary : Prop :=
  ∀ n ℓ : ℕ, 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∃ β : ℝ, 0 < β ∧ β ≤ 1 / 4 ∧
  ∀ L K : ℝ, 0 < L → L ≤ 1 → 0 ≤ K →
  ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ)
    (δ ρ : ℝ), 0 < δ → δ ≤ (β * L) ^ (2 * n + 2) → V.AllardHypotheses H p δ ρ →
  ∀ q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ,
    (∀ x ∈ V.support ∩ closedBall 0 (2 * (δ * ρ)),
      infDist x (rotatedPlane q : Set (Amb n ℓ)) ≤ K * δ ^ (1 / (2 * (n : ℝ) + 2)) * (δ * ρ)) →
    (∀ ξ ∈ V.support ∩ closedBall 0 (δ * ρ / 2), ∀ σ : ℝ, 0 < σ → σ ≤ δ * ρ / 2 →
      V.tiltExcess ξ σ (rotatedPlane q) ≤ β ^ 2 * L ^ 2) →
  ∃ f : Rn n → Rn ℓ, LipschitzOnWith (Real.toNNReal L) f (closedBall 0 (δ * ρ / 4)) ∧
    (∀ x ∈ closedBall (0 : Rn n) (δ * ρ / 4),
      ‖f x‖ ≤ K * δ ^ (1 / (2 * (n : ℝ) + 2)) * (δ * ρ)) ∧
    V.support ∩ closedBall 0 (δ * ρ / 4) =
      q '' graphOver f (closedBall 0 (δ * ρ / 4)) ∩ closedBall 0 (δ * ρ / 4)

/-- **Simon Ch. 5, Lemma 3.1 (Harmonic approximation, p. 114).**  Given `ε > 0` there is
`δ = δ(n, ε) > 0` such that if `f ∈ W^{1,2}(B)`, `B = B̆₁(0)` the open unit ball of `ℝⁿ`, satisfies
`∫_B |∇f|² ≤ 1` and `|∫_B ∇f · ∇ζ dLⁿ| ≤ δ sup |∇ζ|` for every `ζ ∈ C^∞_c(B)`, then there is a
harmonic function `u` on `B` with `∫_B |∇u|² ≤ 1` and `∫_B (u − f)² ≤ ε`.
(`sup|∇ζ| ≤ M` is expressed by quantifying over all bounds `M`; the energy integrals of `u` and
`u − f` are extended-real integrals.) -/
def HarmonicApproximationLemma : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
  ∀ (f : Rn n → ℝ) (g : Rn n → Rn n), IsW12WithGradient f g (ball 0 1) →
    ∫⁻ x in ball (0 : Rn n) 1, ‖g x‖ₑ ^ 2 ≤ 1 →
    (∀ ζ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball 0 1 →
      ∀ M : ℝ, (∀ x, ‖gradient ζ x‖ ≤ M) →
        |∫ x in ball (0 : Rn n) 1, inner ℝ (g x) (gradient ζ x)| ≤ δ * M) →
    ∃ u : Rn n → ℝ, InnerProductSpace.HarmonicOnNhd u (ball 0 1) ∧
      ∫⁻ x in ball (0 : Rn n) 1, ‖gradient u x‖ₑ ^ 2 ≤ 1 ∧
      ∫⁻ x in ball (0 : Rn n) 1, ‖u x - f x‖ₑ ^ 2 ≤ ENNReal.ofReal ε

/-- **Simon Ch. 5, Theorem 4.5 (Tilt-excess Decay Theorem, p. 116)**, `p > n`.  There are
`η, δ₀ ∈ (0, 1/4]` depending only on `n, ℓ, p` such that if 2.3 holds for some `δ ∈ (0, δ₀]`, if
`σ ∈ (0, δρ/2]`, `ξ ∈ spt μ_V ∩ B_{δρ}(0)`, and `T` is any `n`-dimensional subspace, then
`E_*(ξ, ησ, S) ≤ η^{2(1−n/p)} E_*(ξ, σ, T)` for some `n`-dimensional subspace `S`. -/
def TiltExcessDecayTheorem : Prop :=
  ∀ n ℓ : ℕ, 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p →
  ∃ η δ₀ : ℝ, 0 < η ∧ η ≤ 1 / 4 ∧ 0 < δ₀ ∧ δ₀ ≤ 1 / 4 ∧
  ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ)
    (δ ρ : ℝ), 0 < δ → δ ≤ δ₀ → V.AllardHypotheses H p δ ρ →
  ∀ σ : ℝ, 0 < σ → σ ≤ δ * ρ / 2 → ∀ ξ ∈ V.support ∩ closedBall 0 (δ * ρ),
  ∀ T : Submodule ℝ (Amb n ℓ), Module.finrank ℝ T = n →
  ∃ S : Submodule ℝ (Amb n ℓ), Module.finrank ℝ S = n ∧
    V.tiltExcessStar H p δ ξ (η * σ) S ≤ η ^ (2 * (1 - n / p)) * V.tiltExcessStar H p δ ξ σ T

/-- **Simon Ch. 5, Theorem 5.2 (Allard Regularity Theorem, p. 121).**  If `p > n` is arbitrary,
then there are `δ₀ = δ₀(n, ℓ, p)`, `γ = γ(n, ℓ, p) ∈ (0, 1)` and `C = C(n, ℓ, p)` such that the
hypotheses 5.1 (`AllardHypotheses`) with `δ ≤ δ₀` imply the existence of a linear isometry `q` of
`ℝ^{n+ℓ}` and `u = (u¹, …, u^ℓ) ∈ C^{1,1−n/p}(Bⁿ_{γρ}(0); ℝ^ℓ)` with `Du(0) = 0`,
`spt V ∩ B_{γρ}(0) = q(graph u) ∩ B_{γρ}(0)` and
`ρ⁻¹ sup|u| + sup|Du| + ρ^{1−n/p} sup_{x ≠ y ∈ Bⁿ_{γρ}(0)} |x − y|^{−(1−n/p)} |Du(x) − Du(y)|
   ≤ C δ^{1/(2n+2)}`
(balls closed; see `AllardConclusion`, which also records `u(0) = 0`, automatic since `0 ∈ spt V`).
`δ > 0` is the book's standing convention for 2.3. -/
def AllardRegularityTheorem : Prop :=
  ∀ n ℓ : ℕ, 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p →
  ∃ δ₀ γ C : ℝ, 0 < δ₀ ∧ δ₀ < 1 ∧ 0 < γ ∧ γ < 1 ∧
  ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ)
    (δ ρ : ℝ), 0 < δ → δ ≤ δ₀ → V.AllardHypotheses H p δ ρ →
    AllardConclusion V p δ ρ γ C

/-- **Simon Ch. 5, Remark 5.3 (p. 122) — the extension of Allard's theorem announced for §6.**
For every `γ ∈ (0, 1)` there is `δ₀ = δ₀(γ, n, ℓ, p) ∈ (0, 1)` such that the hypotheses 5.1 with
`δ ≤ δ₀` imply the conclusion of Theorem 5.2 on `B_{γρ}(0)`.  The constant `C` of the estimate is
allowed to depend on `γ` as well (the remark does not specify it; this is the weaker reading). -/
def AllardRegularityAnyRadius : Prop :=
  ∀ n ℓ : ℕ, 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∀ γ : ℝ, 0 < γ → γ < 1 →
  ∃ δ₀ C : ℝ, 0 < δ₀ ∧ δ₀ < 1 ∧
  ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ)
    (δ ρ : ℝ), 0 < δ → δ ≤ δ₀ → V.AllardHypotheses H p δ ρ →
    AllardConclusion V p δ ρ γ C

/-- **Simon Ch. 5, Theorem 6.1 (Conical approximation, p. 124).**  Suppose `Λ > 0`,
`λ, θ, δ ∈ (0, 1/4)`, `ξ ∈ ∂B_{1−θ}(0)`, `V = v(M, θ_V)` has generalized mean curvature
`H ∈ L¹_loc(μ)` in an open `U ⊇ B₁(0)`, `μ = μ_V`,
`|μ(B₁(0))/ω_n − μ(B_λ(0))/(ω_n λⁿ)| + sup_{r ∈ [λ,1]} r^{1−n} ∫_{B_r(0)} |H| dμ ≤ δ`
and `μ(B₁(0)) ≤ Λ`.  Then for all `ρ ∈ (0, θ]` and `τ ∈ [2λ, 1]`
`μ(B_{(1−δ^{1/4})ρ}(ξ)) − Cδ^{1/4}|log λ| ≤ τ⁻ⁿ μ(B_{τρ}(τξ)) ≤ μ(B_{(1+δ^{1/4})ρ}(ξ)) + Cδ^{1/4}|log λ|`
with `C = C(n, ℓ, Λ)`.  (The supremum condition is written pointwise in `r`; the conclusion is in
`[0, ∞]`, where `a − c ≤ b` is written `a ≤ b + c`.) -/
def ConicalApproximationTheorem : Prop :=
  ∀ n ℓ : ℕ, 1 ≤ n → ∀ Λ : ℝ, 0 < Λ → ∃ C : ℝ,
  ∀ (lam θ δ : ℝ), 0 < lam → lam < 1 / 4 → 0 < θ → θ < 1 / 4 → 0 < δ → δ < 1 / 4 →
  ∀ ξ : Amb n ℓ, ‖ξ‖ = 1 - θ →
  ∀ (U : Set (Amb n ℓ)), IsOpen U → closedBall 0 1 ⊆ U →
  ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ), V.HasGeneralizedMeanCurvature H →
    (∀ r ∈ Icc lam 1,
      |(V.weight (closedBall 0 1)).toReal / unitBallVolume n -
          (V.weight (closedBall 0 lam)).toReal / (unitBallVolume n * lam ^ n)| +
        r ^ (1 - (n : ℝ)) * ∫ x in closedBall (0 : Amb n ℓ) r, ‖H x‖ ∂V.weight ≤ δ) →
    V.weight (closedBall 0 1) ≤ ENNReal.ofReal Λ →
  ∀ ρ ∈ Ioc 0 θ, ∀ τ ∈ Icc (2 * lam) 1,
    V.weight (closedBall ξ ((1 - δ ^ (1 / 4 : ℝ)) * ρ)) ≤
        ENNReal.ofReal (τ ^ n)⁻¹ * V.weight (closedBall (τ • ξ) (τ * ρ)) +
          ENNReal.ofReal (C * δ ^ (1 / 4 : ℝ) * |Real.log lam|) ∧
      ENNReal.ofReal (τ ^ n)⁻¹ * V.weight (closedBall (τ • ξ) (τ * ρ)) ≤
        V.weight (closedBall ξ ((1 + δ ^ (1 / 4 : ℝ)) * ρ)) +
          ENNReal.ofReal (C * δ ^ (1 / 4 : ℝ) * |Real.log lam|)

/-- **Simon Ch. 5, Theorem 7.1, first assertion (p. 127).**  If `V = v(M, θ)` has generalized mean
curvature `H` in the open set `U ⊆ ℝ^{n+ℓ}`, `H` is locally in `Lᵖ(μ_V)` for some `p > n`,
`θ ≥ 1 μ_V`-a.e. in `U`, and `ξ ∈ U` has `Θⁿ(μ_V, ξ) = 1`, then there are `ρ > 0` and an orthogonal
`Q` of `ℝ^{n+ℓ}` such that, up to a set of `Hⁿ`-measure zero, `Q ∘ τ(M) ∩ B̆_ρ(0) = graph u`
(`τ(x) = x − ξ`), where `u : W → ℝ^ℓ`, `W ∋ 0` open in `ℝⁿ`, is `C^{1,1−n/p}(W; ℝ^ℓ)` with
`u(0) = 0`, `Du(0) = 0`.  (*Erratum:* printed target `ℝ^k` means `ℝ^ℓ`.) -/
def DensityOneRegularity : Prop :=
  ∀ n ℓ : ℕ, 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U →
  ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (p : ℝ), (n : ℝ) < p →
    V.HasGeneralizedMeanCurvature H → V.LocallyLp H p → (∀ᵐ x ∂V.weight, 1 ≤ V.mult x) →
  ∀ ξ ∈ U, V.HasDensity ξ 1 →
  ∃ ρ > 0, ∃ (Q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (W : Set (Rn n)) (u : Rn n → Rn ℓ),
    IsOpen W ∧ (0 : Rn n) ∈ W ∧ IsHolderCkα 1 (1 - n / p) u W ∧ u 0 = 0 ∧ fderiv ℝ u 0 = 0 ∧
    (μHE[n] : Measure (Amb n ℓ))
      (symmDiff (Q '' ((fun x => x - ξ) '' V.carrier) ∩ ball 0 ρ) (graphOver u W)) = 0

/-- **Simon Ch. 5, Theorem 7.1, second assertion (p. 127).**  In the situation of the first
assertion, if moreover `θ` is positive integer-valued `μ_V`-a.e. in `U` and `H = h` on `spt V`
(`μ_V`-a.e.) for some `h ∈ C^{q,α}` in `U` (`q ∈ {0,1,2,…}`, `α ∈ (0,1)`), then for sufficiently
small `ρ > 0` the function `u` is `C^{q+2,α}(W)` and `Θⁿ(μ_V, x) = 1` on `B̆_ρ(ξ) ∩ spt V`.
(The hypotheses `H ∈ Lᵖ_loc`, `θ ≥ 1` of the first assertion are implied here.
*Erratum:* printed "`Θⁿ(μ_V, x) ≡ 1` on `B̆_ρ(ξ)`" must be restricted to `spt μ_V`, as in the third
assertion.  The third assertion (stationarity in a `C^{q+3}` submanifold `N`) is not included: as
printed, `N` is `(n+ℓ)`-dimensional in `ℝ^{n+ℓ}`, hence open, and it reduces to this one with
`h = 0`.) -/
def DensityOneHigherRegularity : Prop :=
  ∀ n ℓ : ℕ, 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U →
  ∀ (V : RectifiableVarifold n ℓ U) (H h : Amb n ℓ → Amb n ℓ) (q : ℕ) (α : ℝ), 0 < α → α < 1 →
    V.HasGeneralizedMeanCurvature H →
    (∀ᵐ x ∂V.weight, ∃ k : ℕ, 1 ≤ k ∧ V.mult x = k) →
    IsLocallyHolderCkα q α h U → (∀ᵐ x ∂V.weight, H x = h x) →
  ∀ ξ ∈ U, V.HasDensity ξ 1 →
  ∃ ρ > 0, ∃ (Q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (W : Set (Rn n)) (u : Rn n → Rn ℓ),
    IsOpen W ∧ (0 : Rn n) ∈ W ∧ IsHolderCkα (q + 2) α u W ∧ u 0 = 0 ∧ fderiv ℝ u 0 = 0 ∧
    (μHE[n] : Measure (Amb n ℓ))
      (symmDiff (Q '' ((fun x => x - ξ) '' V.carrier) ∩ ball 0 ρ) (graphOver u W)) = 0 ∧
    ∀ x ∈ ball ξ ρ ∩ V.support, V.HasDensity x 1

/-- **Simon Ch. 5, Corollary 7.3 (p. 128).**  If `V = v(M, θ)` has generalized mean curvature `H` in
the open set `U ⊆ ℝ^{n+ℓ}`, `H` is locally in `Lᵖ(μ_V)` for some `p > n`, and `θ` is positive
integer-valued `μ_V`-a.e. in `spt V`, then `reg V` is a relatively open dense subset of `spt V`:
it is open in `spt V`, and `spt V` is the closure, taken in `U`, of `reg V` (equivalently,
`sing V` is nowhere dense in `spt V`). -/
def RegularSetOpenDense : Prop :=
  ∀ n ℓ : ℕ, 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U →
  ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (p : ℝ), (n : ℝ) < p →
    V.HasGeneralizedMeanCurvature H → V.LocallyLp H p →
    (∀ᵐ x ∂V.weight, x ∈ V.support → ∃ k : ℕ, 1 ≤ k ∧ V.mult x = k) →
    (∃ O : Set (Amb n ℓ), IsOpen O ∧ V.regularSet = O ∩ V.support) ∧
      V.support = closure V.regularSet ∩ U

namespace Submission

set_option maxHeartbeats 1000000 in
/-- **Thin-cone propagation from small to large radii** (step 5 of the proof of
`AllardRegularityAnyRadius`, Simon Remark 5.3, via the conical approximation Theorem 6.1).
Assume 6.1.  If `dist(x, T) ≤ (κ/2)|x|` on `spt V ∩ B_{c₀ρ}(0)`, then `dist(y, T) ≤ κ|y|` on
`spt V ∩ B_{(1+γ)ρ/2}(0)`, as soon as `δ ≤ δ_C(n, ℓ, p, γ, κ, c₀)`.

From `any_radius_monotonicity_bounds`: `|ω_n⁻¹ t⁻ⁿ μ_V(B_t(0)) - 1| ≤ C₁δ` for `0 < t < ρ` (1a),
`∫_{B_t(0)} |H| dμ_V ≤ (1 + 2ω_n) δ t^{n-1}` (1b, by Young's inequality
`|H| ≤ a^{1-p}|H|^p + a` with `a = δ/t`), and `μ_V(B_s(z)) ≥ ω_n sⁿ/2` at support points (1d).
For `|y| > c₀ρ` rescale by `R = |y|/(1 - θ₀)`, `θ₀ = (1-γ)/8` (`any_radius_rescaled_varifold`),
apply 6.1 with `Λ = 2ω_n`, `λ = δ`, `θ = θ₀`, `δ' = 3C₁δ`, `ρ̃ = κ/8`, `τ = c₀ρ/(2R)`; the
lower density at `y` forces a point `z ∈ spt V` with `|z - τy| ≤ τκR/8` and `|z| ≤ c₀ρ/2`, and
homogeneity plus the 1-Lipschitz property of `dist(·, T)` give
`dist(y, T) ≤ (5/8)κR ≤ κ|y|`. -/
theorem any_radius_cone : ConicalApproximationTheorem → ∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∀ γ κ c₀ : ℝ, 0 < γ → γ < 1 → 0 < κ → κ ≤ (1 - γ) / 8 → 0 < c₀ → c₀ ≤ 1 / 4 → ∃ δC : ℝ, 0 < δC ∧ ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), 0 < δ → δ ≤ δC → V.AllardHypotheses H p δ ρ → ∀ T : Submodule ℝ (Amb n ℓ), (∀ x ∈ V.support ∩ closedBall 0 (c₀ * ρ), infDist x (T : Set (Amb n ℓ)) ≤ κ / 2 * ‖x‖) → ∀ y ∈ V.support ∩ closedBall 0 ((1 + γ) / 2 * ρ), infDist y (T : Set (Amb n ℓ)) ≤ κ * ‖y‖ := by
  intro hCAT n ℓ hn p hp γ κ c₀ hγ0 hγ1 hκ0 hκ hc0 hc1
  -- Constants depending only on `n, ℓ, p, γ, κ, c₀`.
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp0 : 0 < p := by linarith
  have hpn : 0 < p - n := sub_pos.2 hp
  set ω : ℝ := unitBallVolume n with hω_def
  have hω : 0 < ω := by
    rw [hω_def, unitBallVolume]
    exact div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
  -- `b = 4p/(p-n) = κ_m⁻¹`, so that `Λ = 4pδ/(p-n) = bδ`.
  set b : ℝ := 4 * p / (p - n) with hb_def
  have hb : 0 < b := by positivity
  set C1 : ℝ := 2 + 2 * ω + 13 * b + 7 * b / ω with hC1_def
  have hC1 : 0 < C1 := by positivity
  obtain ⟨C9, hC9⟩ := hCAT n ℓ hn (2 * ω) (by positivity)
  set C9' : ℝ := max C9 0
  have hC9' : 0 ≤ C9' := le_max_right _ _
  set target : ℝ := ω * (κ / 16) ^ n / 2 with htarget_def
  have htarget : 0 < target := by positivity
  -- Step 7: the threshold making `C₉' (3 C₁ δ)^{1/4} |log δ|` smaller than `ω (κ/16)ⁿ/2`.
  obtain ⟨δ5, hδ5, hδ5'⟩ : ∃ δ5 : ℝ, 0 < δ5 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ5 →
      C9' * (3 * C1 * δ) ^ (1 / 4 : ℝ) * |Real.log δ| < target := by
    have hlim : Tendsto (fun x : ℝ => C9' * (3 * C1) ^ (1 / 4 : ℝ) * |Real.log x * x ^ (1 / 4 : ℝ)|)
        (𝓝[>] 0) (𝓝 0) := by
      have h := ((tendsto_log_mul_rpow_nhdsGT_zero (r := 1 / 4) (by norm_num)).abs).const_mul
        (C9' * (3 * C1) ^ (1 / 4 : ℝ))
      simpa using h
    obtain ⟨u, hu, hsub⟩ :=
      mem_nhdsGT_iff_exists_Ioc_subset.1 ((tendsto_order.1 hlim).2 target htarget)
    refine ⟨u, hu, fun δ hδ hδu => ?_⟩
    have h : C9' * (3 * C1) ^ (1 / 4 : ℝ) * |Real.log δ * δ ^ (1 / 4 : ℝ)| < target :=
      hsub ⟨hδ, hδu⟩
    calc C9' * (3 * C1 * δ) ^ (1 / 4 : ℝ) * |Real.log δ|
        = C9' * (3 * C1) ^ (1 / 4 : ℝ) * |Real.log δ * δ ^ (1 / 4 : ℝ)| := by
          rw [Real.mul_rpow (by positivity) hδ.le, abs_mul,
            abs_of_nonneg (Real.rpow_nonneg hδ.le _)]
          ring
      _ < target := h
  refine ⟨min (1 / (4 * b)) (min (ω / (3 * b)) (min (1 / (48 * C1)) (min (1 / 8)
    (min (c₀ / 4) δ5)))), by positivity, ?_⟩
  intro U hU V H δ ρ hδ hδC hA T hT y hy
  simp only [le_min_iff] at hδC
  obtain ⟨hδb, hδω, hδC1, hδ8, hδc₀, hδδ5⟩ := hδC
  have hA' := hA
  obtain ⟨hρ, hGMC, -, h0V, hBU, hmass, hLp⟩ := hA'
  have hbδ : b * δ ≤ 1 / 4 := by
    rw [le_div_iff₀ (by positivity)] at hδb; linarith
  have hbδω : b * δ ≤ ω / 3 := by
    rw [le_div_iff₀ (by positivity)] at hδω; linarith
  have hC1δ : 3 * C1 * δ ≤ 1 / 16 := by
    rw [le_div_iff₀ (by positivity)] at hδC1; linarith
  have hδm : δ ≤ (p - n) / (4 * p) := by
    have h4 : 4 * p * δ = (b * δ) * (p - n) := by rw [hb_def]; field_simp
    rw [le_div_iff₀ (by positivity)]
    calc δ * (4 * p) = (b * δ) * (p - n) := by rw [← h4]; ring
      _ ≤ (1 / 4) * (p - n) := by gcongr
      _ ≤ p - n := by linarith
  obtain ⟨hM1, hM2, -⟩ :=
    Submission.any_radius_monotonicity_bounds n ℓ hn p hp U hU V H δ ρ hδ hδm hA
  set Λ : ℝ := 4 * p * δ / (p - n) with hΛ_def
  have hΛb : Λ = b * δ := by rw [hΛ_def, hb_def]; ring
  have hΛ0 : 0 ≤ Λ := by rw [hΛb]; positivity
  have hΛ1 : Λ ≤ 1 / 4 := hΛb ▸ hbδ
  have hΛω : Λ ≤ ω / 3 := hΛb ▸ hbδω
  -- Elementary exponential bounds (`Λ ≤ 1/4`), from `1 - x ≤ e^{-x}`.
  have hexp_aux : ∀ x : ℝ, Real.exp x * (1 - x) ≤ 1 := by
    intro x
    have h1 := Real.add_one_le_exp (-x)
    have h2 : Real.exp x * Real.exp (-x) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have h3 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos x).le
    linarith
  have hexpΛ : Real.exp Λ ≤ 3 := by
    have h1 := hexp_aux Λ
    have h2 := mul_le_mul_of_nonneg_left (show (3 : ℝ) / 4 ≤ 1 - Λ by linarith) (Real.exp_pos Λ).le
    linarith
  have hexp2Λ : Real.exp (2 * Λ) ≤ 1 + 6 * Λ := by
    have h1 := hexp_aux (2 * Λ)
    have h2 := mul_le_mul_of_nonneg_left (show (1 : ℝ) / 2 ≤ 1 - 2 * Λ by linarith)
      (Real.exp_pos (2 * Λ)).le
    have h3 : Real.exp (2 * Λ) ≤ 3 := by linarith
    have h4 := mul_le_mul_of_nonneg_left h3 hΛ0
    linarith
  have hexpneg : 1 - Λ ≤ Real.exp (-Λ) := by linarith [Real.add_one_le_exp (-Λ)]
  -- Masses of balls inside `B_ρ(0)` are finite.
  have hμρ : V.weight (closedBall 0 ρ) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmass
  have hfin : ∀ (c : Amb n ℓ) (t : ℝ), closedBall c t ⊆ closedBall 0 ρ →
      V.weight (closedBall c t) ≠ ⊤ :=
    fun c t h => ne_top_of_le_ne_top hμρ (measure_mono h)
  -- Step 1 (1a), lower bound.
  have hlow : ∀ t, 0 < t → t < ρ →
      (1 - C1 * δ) * (ω * t ^ n) ≤ (V.weight (closedBall 0 t)).toReal := by
    intro t ht htρ
    have h := hM2 0 h0V ρ t ht htρ subset_rfl
    have hωΛ : 0 ≤ ω - Λ := by linarith
    have hid : (1 - Λ) * (ω - Λ) - (1 - C1 * δ) * ω =
        2 * δ * ω + 2 * δ * ω ^ 2 + 12 * (b * δ) * ω + 6 * (b * δ) + Λ ^ 2 := by
      rw [hΛb, hC1_def]; field_simp; ring
    have key : (1 - C1 * δ) * ω ≤ Real.exp (-Λ) * (ω - Λ) := by
      calc (1 - C1 * δ) * ω ≤ (1 - Λ) * (ω - Λ) := by
            have : 0 ≤ 2 * δ * ω + 2 * δ * ω ^ 2 + 12 * (b * δ) * ω + 6 * (b * δ) + Λ ^ 2 := by
              positivity
            linarith
        _ ≤ Real.exp (-Λ) * (ω - Λ) := mul_le_mul_of_nonneg_right hexpneg hωΛ
    calc (1 - C1 * δ) * (ω * t ^ n) = ((1 - C1 * δ) * ω) * t ^ n := by ring
      _ ≤ (Real.exp (-Λ) * (ω - Λ)) * t ^ n := mul_le_mul_of_nonneg_right key (by positivity)
      _ ≤ _ := h
  -- Step 1 (1a), upper bound (let `r ↑ ρ` in (M1)).
  have hup : ∀ t, 0 < t → t < ρ →
      (V.weight (closedBall 0 t)).toReal ≤ (1 + C1 * δ) * (ω * t ^ n) := by
    intro t ht htρ
    have hlim : (V.weight (closedBall 0 t)).toReal / t ^ n ≤
        Real.exp (2 * Λ) * ((1 + δ) * ω) + 2 * Real.exp Λ * Λ := by
      have hcont : ContinuousAt (fun r : ℝ => Real.exp (2 * Λ) * ((1 + δ) * (ω * ρ ^ n) / r ^ n) +
          2 * Real.exp Λ * Λ) ρ := by
        apply ContinuousAt.add _ continuousAt_const
        apply ContinuousAt.mul continuousAt_const
        exact continuousAt_const.div (continuousAt_id.pow n) (pow_ne_zero n hρ.ne')
      have hval : Real.exp (2 * Λ) * ((1 + δ) * (ω * ρ ^ n) / ρ ^ n) + 2 * Real.exp Λ * Λ =
          Real.exp (2 * Λ) * ((1 + δ) * ω) + 2 * Real.exp Λ * Λ := by
        rw [← mul_assoc, mul_div_assoc, div_self (pow_ne_zero n hρ.ne'), mul_one]
      rw [← hval]
      refine ge_of_tendsto (hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio ρ))) ?_
      filter_upwards [Ioo_mem_nhdsLT htρ] with r hr
      have hr0 : 0 < r := ht.trans hr.1
      have h1 := hM1 0 ρ t r ht hr.1.le hr.2 subset_rfl
      have h2 : (V.weight (closedBall 0 r)).toReal ≤ (1 + δ) * (ω * ρ ^ n) :=
        ENNReal.toReal_le_of_le_ofReal (by positivity)
          ((measure_mono (closedBall_subset_closedBall hr.2.le)).trans hmass)
      calc (V.weight (closedBall 0 t)).toReal / t ^ n
          ≤ Real.exp (2 * Λ) * ((V.weight (closedBall 0 r)).toReal / r ^ n) +
              2 * Real.exp Λ * Λ := h1
        _ ≤ Real.exp (2 * Λ) * ((1 + δ) * (ω * ρ ^ n) / r ^ n) + 2 * Real.exp Λ * Λ := by
          gcongr
    have key : Real.exp (2 * Λ) * ((1 + δ) * ω) + 2 * Real.exp Λ * Λ ≤ (1 + C1 * δ) * ω := by
      have h1 : Real.exp (2 * Λ) * ((1 + δ) * ω) ≤ (1 + 6 * Λ) * ((1 + δ) * ω) :=
        mul_le_mul_of_nonneg_right hexp2Λ (by positivity)
      have h2 : 2 * Real.exp Λ * Λ ≤ 6 * Λ := by
        have := mul_le_mul_of_nonneg_right hexpΛ hΛ0
        linarith
      have hid : (1 + C1 * δ) * ω - ((1 + 6 * Λ) * ((1 + δ) * ω) + 6 * Λ) =
          δ * ω + 2 * δ * ω ^ 2 + 7 * (b * δ) * ω + (b * δ) - 6 * (b * δ) * δ * ω := by
        rw [hΛb, hC1_def]; field_simp; ring
      have h3 : 6 * (b * δ) * δ * ω ≤ 6 * (b * δ) * ω := by
        have h0 : 0 ≤ 6 * (b * δ) * ω := by positivity
        have := mul_le_mul_of_nonneg_left (show δ ≤ 1 by linarith) h0
        linarith
      have h4 : 0 ≤ δ * ω + 2 * δ * ω ^ 2 + (b * δ) * ω + (b * δ) := by positivity
      linarith
    have := (div_le_iff₀ (by positivity)).1 (hlim.trans key)
    linarith
  -- Step 1 (1a), as stated: `|ω⁻¹ t⁻ⁿ μ(B_t(0)) - 1| ≤ C₁ δ`.
  have hm1 : ∀ t, 0 < t → t < ρ →
      |(V.weight (closedBall 0 t)).toReal / (ω * t ^ n) - 1| ≤ C1 * δ := by
    intro t ht htρ
    have hpos : 0 < ω * t ^ n := by positivity
    rw [abs_le]
    constructor
    · have := (le_div_iff₀ hpos).2 (hlow t ht htρ)
      linarith
    · have := (div_le_iff₀ hpos).2 (hup t ht htρ)
      linarith
  -- Step 1 (1b): `∫_{B_t(0)} |H| dμ ≤ (1 + 2ω) δ t^{n-1}` (Young's inequality in place of Hölder).
  have hJ : ENNReal.ofReal (ρ ^ (p - n)) *
      ∫⁻ x in closedBall (0 : Amb n ℓ) ρ, ‖H x‖ₑ ^ p ∂V.weight ≤ ENNReal.ofReal (δ ^ p) := by
    have h := ENNReal.rpow_le_rpow hLp hp0.le
    simp only [RectifiableVarifold.scaledLpNorm] at h
    rwa [one_div, ENNReal.rpow_inv_rpow hp0.ne', ENNReal.ofReal_rpow_of_nonneg hδ.le hp0.le] at h
  set J := ∫⁻ x in closedBall (0 : Amb n ℓ) ρ, ‖H x‖ₑ ^ p ∂V.weight
  have hρpn : 0 < ρ ^ (p - n) := Real.rpow_pos_of_pos hρ _
  have hJfin : J ≠ ⊤ := by
    intro hJtop
    rw [hJtop, ENNReal.mul_top (ENNReal.ofReal_pos.2 hρpn).ne'] at hJ
    exact ENNReal.ofReal_ne_top (top_le_iff.1 hJ)
  have hJreal : ρ ^ (p - n) * J.toReal ≤ δ ^ p := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hJ
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hρpn.le,
      ENNReal.toReal_ofReal (by positivity)] at h
  have young : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a ^ (1 - p) * x ^ p + a := by
    intro a x ha hx
    rcases le_or_gt x a with hxa | hxa
    · have : 0 ≤ a ^ (1 - p) * x ^ p := by positivity
      linarith
    · have hx0 : 0 < x := ha.trans hxa
      have h1 : a ^ (p - 1) ≤ x ^ (p - 1) := Real.rpow_le_rpow ha.le hxa.le (by linarith)
      have h2 : x ^ p = x ^ (p - 1) * x := by
        rw [← Real.rpow_add_one hx0.ne', sub_add_cancel]
      have h3 : a ^ (1 - p) * a ^ (p - 1) = 1 := by
        rw [← Real.rpow_add ha, show (1 - p) + (p - 1) = (0 : ℝ) by ring, Real.rpow_zero]
      have h4 : 0 ≤ a ^ (1 - p) := by positivity
      calc x = a ^ (1 - p) * a ^ (p - 1) * x := by rw [h3, one_mul]
        _ ≤ a ^ (1 - p) * x ^ (p - 1) * x := by gcongr
        _ = a ^ (1 - p) * x ^ p := by rw [h2]; ring
        _ ≤ a ^ (1 - p) * x ^ p + a := by linarith
  have h1b : ∀ t, 0 < t → t < ρ → ∫⁻ x in closedBall (0 : Amb n ℓ) t, ‖H x‖ₑ ∂V.weight ≤
      ENNReal.ofReal ((1 + 2 * ω) * δ * t ^ (n - 1)) := by
    intro t ht htρ
    set a : ℝ := δ / t with ha_def
    have ha : 0 < a := div_pos hδ ht
    have hfinB : V.weight (closedBall 0 t) ≠ ⊤ := hfin 0 t (closedBall_subset_closedBall htρ.le)
    have hm : (V.weight (closedBall 0 t)).toReal ≤ 2 * ω * t ^ n := by
      have h := hup t ht htρ
      have := mul_le_mul_of_nonneg_right (show 1 + C1 * δ ≤ 2 by linarith)
        (by positivity : (0 : ℝ) ≤ ω * t ^ n)
      linarith
    have hj0 : 0 ≤ J.toReal := ENNReal.toReal_nonneg
    have hA : a ^ (1 - p) = δ ^ (1 - p) * t ^ (p - n) * t ^ (n - 1) := by
      rw [ha_def, Real.div_rpow hδ.le ht.le, div_eq_mul_inv, ← Real.rpow_neg ht.le, mul_assoc,
        ← Real.rpow_natCast, ← Real.rpow_add ht]
      congr 2
      rw [Nat.cast_sub hn, Nat.cast_one]
      ring
    have hδp : δ ^ (1 - p) * δ ^ p = δ := by
      rw [← Real.rpow_add hδ, show (1 - p) + p = (1 : ℝ) by ring, Real.rpow_one]
    have htρp : t ^ (p - n) ≤ ρ ^ (p - n) := Real.rpow_le_rpow ht.le htρ.le hpn.le
    have htn : t ^ n = t ^ (n - 1) * t := (pow_sub_one_mul (by omega) t).symm
    have hreal : a ^ (1 - p) * J.toReal + a * (V.weight (closedBall 0 t)).toReal ≤
        (1 + 2 * ω) * δ * t ^ (n - 1) := by
      have h1 : a ^ (1 - p) * J.toReal ≤ δ * t ^ (n - 1) := by
        rw [hA]
        calc δ ^ (1 - p) * t ^ (p - n) * t ^ (n - 1) * J.toReal
            ≤ δ ^ (1 - p) * ρ ^ (p - n) * t ^ (n - 1) * J.toReal := by gcongr
          _ = δ ^ (1 - p) * t ^ (n - 1) * (ρ ^ (p - n) * J.toReal) := by ring
          _ ≤ δ ^ (1 - p) * t ^ (n - 1) * δ ^ p := by gcongr
          _ = (δ ^ (1 - p) * δ ^ p) * t ^ (n - 1) := by ring
          _ = δ * t ^ (n - 1) := by rw [hδp]
      have h2 : a * (V.weight (closedBall 0 t)).toReal ≤ 2 * ω * δ * t ^ (n - 1) := by
        calc a * (V.weight (closedBall 0 t)).toReal ≤ a * (2 * ω * t ^ n) := by gcongr
          _ = 2 * ω * δ * t ^ (n - 1) := by rw [ha_def, htn]; field_simp
      linarith
    calc ∫⁻ x in closedBall (0 : Amb n ℓ) t, ‖H x‖ₑ ∂V.weight
        ≤ ∫⁻ x in closedBall (0 : Amb n ℓ) t,
            (ENNReal.ofReal (a ^ (1 - p)) * ‖H x‖ₑ ^ p + ENNReal.ofReal a) ∂V.weight := by
          apply lintegral_mono
          intro x
          dsimp only
          rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le,
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) ha.le]
          exact ENNReal.ofReal_le_ofReal (young a ‖H x‖ ha (norm_nonneg _))
      _ = ENNReal.ofReal (a ^ (1 - p)) * ∫⁻ x in closedBall (0 : Amb n ℓ) t, ‖H x‖ₑ ^ p ∂V.weight +
            ENNReal.ofReal a * V.weight (closedBall 0 t) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            setLIntegral_const]
      _ ≤ ENNReal.ofReal (a ^ (1 - p)) * J + ENNReal.ofReal a * V.weight (closedBall 0 t) := by
          gcongr
          exact lintegral_mono_set (closedBall_subset_closedBall htρ.le)
      _ = ENNReal.ofReal (a ^ (1 - p) * J.toReal + a * (V.weight (closedBall 0 t)).toReal) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_mul ha.le, ENNReal.ofReal_toReal hJfin, ENNReal.ofReal_toReal hfinB]
      _ ≤ ENNReal.ofReal ((1 + 2 * ω) * δ * t ^ (n - 1)) := ENNReal.ofReal_le_ofReal hreal
  -- Step 1 (1d): lower density bound at support points.
  have h1d : ∀ z ∈ V.support, ∀ s : ℝ, 0 < s → ‖z‖ + 2 * s ≤ ρ →
      ENNReal.ofReal (ω * s ^ n / 2) ≤ V.weight (closedBall z s) := by
    intro z hz s hs hzs
    have hsub : closedBall z (2 * s) ⊆ closedBall 0 ρ := by
      intro w hw
      rw [mem_closedBall, dist_eq_norm] at hw
      rw [mem_closedBall, dist_zero_right]
      calc ‖w‖ = ‖(w - z) + z‖ := by rw [sub_add_cancel]
        _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
        _ ≤ ρ := by linarith
    have h := hM2 z hz (2 * s) s hs (by linarith) hsub
    apply ENNReal.ofReal_le_of_le_toReal
    refine le_trans ?_ h
    have key : ω / 2 ≤ Real.exp (-Λ) * (ω - Λ) := by
      have hωΛ : 2 * ω / 3 ≤ ω - Λ := by linarith
      calc ω / 2 = (3 / 4) * (2 * ω / 3) := by ring
        _ ≤ Real.exp (-Λ) * (ω - Λ) :=
          mul_le_mul (by linarith) hωΛ (by positivity) (Real.exp_pos _).le
    calc ω * s ^ n / 2 = ω / 2 * s ^ n := by ring
      _ ≤ Real.exp (-Λ) * (ω - Λ) * s ^ n := mul_le_mul_of_nonneg_right key (by positivity)
  -- Step 2: small `|y|`.
  obtain ⟨hyV, hyB⟩ := hy
  rw [mem_closedBall, dist_zero_right] at hyB
  by_cases hsmall : ‖y‖ ≤ c₀ * ρ
  · have h := hT y ⟨hyV, by rwa [mem_closedBall, dist_zero_right]⟩
    have := mul_nonneg hκ0.le (norm_nonneg y)
    linarith
  replace hsmall : c₀ * ρ < ‖y‖ := lt_of_not_ge hsmall
  -- Step 3: rescaling by `R = |y|/(1 - θ₀)`.
  set θ₀ : ℝ := (1 - γ) / 8 with hθ₀_def
  have hθ₀ : 0 < θ₀ := by rw [hθ₀_def]; linarith
  have hθ₀8 : θ₀ ≤ 1 / 8 := by rw [hθ₀_def]; linarith
  have hcρ : 0 < c₀ * ρ := mul_pos hc0 hρ
  have hy0 : 0 < ‖y‖ := hcρ.trans hsmall
  have h1θ : 0 < 1 - θ₀ := by linarith
  set R : ℝ := ‖y‖ / (1 - θ₀) with hR_def
  have hR : 0 < R := div_pos hy0 h1θ
  have hRne : R ≠ 0 := hR.ne'
  have hyR : ‖y‖ = (1 - θ₀) * R := by rw [hR_def]; field_simp
  have hRρ : R < ρ := by
    rw [hR_def, div_lt_iff₀ h1θ, hθ₀_def]
    linarith [mul_pos (sub_pos.2 hγ1) hρ]
  have hyleR : ‖y‖ ≤ R := by
    have := mul_nonneg hθ₀.le hR.le
    rw [hyR]; linarith
  obtain ⟨V', -, -, hwV', -, -, hHV'⟩ :=
    Submission.any_radius_rescaled_varifold n ℓ U hU V 0 R hR
  have hemb : MeasurableEmbedding (fun x : Amb n ℓ => R⁻¹ • (x - 0)) := by
    simpa only [sub_zero] using measurableEmbedding_const_smul₀ (α := Amb n ℓ) (inv_ne_zero hRne)
  have hpre : ∀ (c : Amb n ℓ) (t : ℝ),
      (fun x : Amb n ℓ => R⁻¹ • (x - 0)) ⁻¹' closedBall c t = closedBall (R • c) (R * t) := by
    intro c t
    ext z
    simp only [mem_preimage, mem_closedBall, dist_eq_norm, sub_zero]
    rw [show R⁻¹ • z - c = R⁻¹ • (z - R • c) by rw [smul_sub, inv_smul_smul₀ hRne], norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR), inv_mul_le_iff₀ hR]
  have hball : ∀ (c : Amb n ℓ) (t : ℝ), V'.weight (closedBall c t) =
      (ENNReal.ofReal (R ^ n))⁻¹ * V.weight (closedBall (R • c) (R * t)) := by
    intro c t
    rw [hwV', Measure.smul_apply, hemb.map_apply, hpre, smul_eq_mul]
  have hint : ∀ r : ℝ, ∫⁻ x in closedBall (0 : Amb n ℓ) r, ‖R • H (0 + R • x)‖ₑ ∂V'.weight =
      (ENNReal.ofReal (R ^ n))⁻¹ *
        (ENNReal.ofReal R * ∫⁻ x in closedBall (0 : Amb n ℓ) (R * r), ‖H x‖ₑ ∂V.weight) := by
    intro r
    rw [hwV', Measure.restrict_smul, lintegral_smul_measure, hemb.restrict_map, hemb.lintegral_map,
      hpre, smul_zero, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, smul_eq_mul]
    congr 1
    apply lintegral_congr
    intro x
    simp only [sub_zero, zero_add, smul_inv_smul₀ hRne]
    rw [enorm_smul, Real.enorm_of_nonneg hR.le]
  -- Hypotheses of 6.1 for `V'` with `Λ = 2ω`, `λ = δ`, `θ = θ₀`, `δ' = 3 C₁ δ`.
  have hU' : IsOpen ((fun x : Amb n ℓ => 0 + R • x) ⁻¹' U) := hU.preimage (by fun_prop)
  have hB1 : closedBall (0 : Amb n ℓ) 1 ⊆ (fun x : Amb n ℓ => 0 + R • x) ⁻¹' U := by
    intro x hx
    rw [mem_closedBall, dist_zero_right] at hx
    apply hBU
    show (0 : Amb n ℓ) + R • x ∈ closedBall 0 ρ
    rw [mem_closedBall, dist_zero_right, zero_add, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
    have := mul_le_mul_of_nonneg_left hx hR.le
    linarith
  have hGMC' := hHV' H hGMC
  set ξ : Amb n ℓ := R⁻¹ • y with hξ_def
  have hξ : ‖ξ‖ = 1 - θ₀ := by
    rw [hξ_def, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR), hyR]
    field_simp
  have hRξ : R • ξ = y := by rw [hξ_def, smul_inv_smul₀ hRne]
  set τ : ℝ := c₀ * ρ / (2 * R) with hτ_def
  have hτ0 : 0 < τ := by positivity
  have hτR : τ * R = c₀ * ρ / 2 := by rw [hτ_def]; field_simp
  have hτ1 : τ ≤ 1 := by
    rw [hτ_def, div_le_one (by positivity)]; linarith
  have hτ2 : 2 * δ ≤ τ := by
    rw [hτ_def, le_div_iff₀ (by positivity)]
    linarith [mul_le_mul_of_nonneg_right hδc₀ hR.le, mul_lt_mul_of_pos_left hRρ hc0]
  set δ' : ℝ := 3 * C1 * δ with hδ'_def
  have hδ'0 : 0 < δ' := by positivity
  have hδ'14 : δ' ^ (1 / 4 : ℝ) ≤ 1 / 2 := by
    calc δ' ^ (1 / 4 : ℝ) ≤ ((1 / 2 : ℝ) ^ (4 : ℕ)) ^ (1 / 4 : ℝ) := by
          apply Real.rpow_le_rpow hδ'0.le _ (by norm_num)
          norm_num
          linarith
      _ = 1 / 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
          norm_num
  have hpinch : ∀ r ∈ Icc δ 1,
      |(V'.weight (closedBall 0 1)).toReal / ω -
          (V'.weight (closedBall 0 δ)).toReal / (ω * δ ^ n)| +
        r ^ (1 - (n : ℝ)) * ∫ x in closedBall (0 : Amb n ℓ) r, ‖R • H (0 + R • x)‖ ∂V'.weight ≤
        δ' := by
    intro r hr
    have hr0 : 0 < r := hδ.trans_le hr.1
    have hRδ : 0 < R * δ := mul_pos hR hδ
    have hRδρ : R * δ < ρ := by
      have := mul_le_mul_of_nonneg_left (show δ ≤ 1 by linarith) hR.le
      linarith
    have e1 : (V'.weight (closedBall 0 1)).toReal / ω =
        (V.weight (closedBall 0 R)).toReal / (ω * R ^ n) := by
      rw [hball, smul_zero, mul_one, ENNReal.toReal_mul, ENNReal.toReal_inv,
        ENNReal.toReal_ofReal (by positivity)]
      field_simp
    have e2 : (V'.weight (closedBall 0 δ)).toReal / (ω * δ ^ n) =
        (V.weight (closedBall 0 (R * δ))).toReal / (ω * (R * δ) ^ n) := by
      rw [hball, smul_zero, ENNReal.toReal_mul, ENNReal.toReal_inv,
        ENNReal.toReal_ofReal (by positivity), mul_pow]
      field_simp
    have hterm1 : |(V'.weight (closedBall 0 1)).toReal / ω -
        (V'.weight (closedBall 0 δ)).toReal / (ω * δ ^ n)| ≤ 2 * (C1 * δ) := by
      rw [e1, e2]
      have h1 := hm1 R hR hRρ
      have h2 := hm1 (R * δ) hRδ hRδρ
      calc _ ≤ |(V.weight (closedBall 0 R)).toReal / (ω * R ^ n) - 1| +
            |1 - (V.weight (closedBall 0 (R * δ))).toReal / (ω * (R * δ) ^ n)| :=
            abs_sub_le _ _ _
        _ ≤ C1 * δ + C1 * δ := by rw [abs_sub_comm 1]; exact add_le_add h1 h2
        _ = 2 * (C1 * δ) := by ring
    have hRr : 0 < R * r := mul_pos hR hr0
    have hRrρ : R * r < ρ := by
      have := mul_le_mul_of_nonneg_left hr.2 hR.le
      linarith
    have hL := h1b (R * r) hRr hRrρ
    have hlint : ∫⁻ x in closedBall (0 : Amb n ℓ) r, ‖R • H (0 + R • x)‖ₑ ∂V'.weight ≤
        ENNReal.ofReal ((1 + 2 * ω) * δ * r ^ (n - 1)) := by
      rw [hint r]
      calc (ENNReal.ofReal (R ^ n))⁻¹ *
            (ENNReal.ofReal R * ∫⁻ x in closedBall (0 : Amb n ℓ) (R * r), ‖H x‖ₑ ∂V.weight)
          ≤ (ENNReal.ofReal (R ^ n))⁻¹ *
            (ENNReal.ofReal R * ENNReal.ofReal ((1 + 2 * ω) * δ * (R * r) ^ (n - 1))) := by
            gcongr
        _ = ENNReal.ofReal ((1 + 2 * ω) * δ * r ^ (n - 1)) := by
            rw [← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_mul hR.le,
              ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [mul_pow, ← pow_sub_one_mul (by omega : n ≠ 0) R]
            field_simp
    have hint2 : ∫ x in closedBall (0 : Amb n ℓ) r, ‖R • H (0 + R • x)‖ ∂V'.weight ≤
        (1 + 2 * ω) * δ * r ^ (n - 1) := by
      calc ∫ x in closedBall (0 : Amb n ℓ) r, ‖R • H (0 + R • x)‖ ∂V'.weight
          ≤ ‖∫ x in closedBall (0 : Amb n ℓ) r, ‖R • H (0 + R • x)‖ ∂V'.weight‖ :=
            Real.le_norm_self _
        _ ≤ (∫⁻ x in closedBall (0 : Amb n ℓ) r,
              ENNReal.ofReal ‖‖R • H (0 + R • x)‖‖ ∂V'.weight).toReal :=
            norm_integral_le_lintegral_norm _
        _ = (∫⁻ x in closedBall (0 : Amb n ℓ) r, ‖R • H (0 + R • x)‖ₑ ∂V'.weight).toReal := by
            simp_rw [norm_norm, ofReal_norm]
        _ ≤ (1 + 2 * ω) * δ * r ^ (n - 1) :=
            ENNReal.toReal_le_of_le_ofReal (by positivity) hlint
    have hrr : r ^ (1 - (n : ℝ)) * r ^ (n - 1) = 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hr0, Nat.cast_sub hn, Nat.cast_one,
        show (1 - (n : ℝ)) + ((n : ℝ) - 1) = 0 by ring, Real.rpow_zero]
    have hterm2 : r ^ (1 - (n : ℝ)) *
        ∫ x in closedBall (0 : Amb n ℓ) r, ‖R • H (0 + R • x)‖ ∂V'.weight ≤ (1 + 2 * ω) * δ := by
      calc _ ≤ r ^ (1 - (n : ℝ)) * ((1 + 2 * ω) * δ * r ^ (n - 1)) :=
            mul_le_mul_of_nonneg_left hint2 (Real.rpow_nonneg hr0.le _)
        _ = (1 + 2 * ω) * δ * (r ^ (1 - (n : ℝ)) * r ^ (n - 1)) := by ring
        _ = (1 + 2 * ω) * δ := by rw [hrr, mul_one]
    have hC1big : 1 + 2 * ω ≤ C1 := by
      rw [hC1_def]
      have : 0 ≤ 13 * b + 7 * b / ω := by positivity
      linarith
    calc _ ≤ 2 * (C1 * δ) + (1 + 2 * ω) * δ := add_le_add hterm1 hterm2
      _ ≤ δ' := by rw [hδ'_def]; linarith [mul_le_mul_of_nonneg_right hC1big hδ.le]
  have hmass' : V'.weight (closedBall 0 1) ≤ ENNReal.ofReal (2 * ω) := by
    rw [hball, smul_zero, mul_one]
    have h := hup R hR hRρ
    have hfinR : V.weight (closedBall 0 R) ≠ ⊤ := hfin 0 R (closedBall_subset_closedBall hRρ.le)
    calc (ENNReal.ofReal (R ^ n))⁻¹ * V.weight (closedBall 0 R)
        ≤ (ENNReal.ofReal (R ^ n))⁻¹ * ENNReal.ofReal ((1 + C1 * δ) * (ω * R ^ n)) := by
          gcongr
          exact (ENNReal.le_ofReal_iff_toReal_le hfinR (by positivity)).2 h
      _ = ENNReal.ofReal ((1 + C1 * δ) * ω) := by
          rw [← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
      _ ≤ ENNReal.ofReal (2 * ω) := by
          apply ENNReal.ofReal_le_ofReal
          have := mul_le_mul_of_nonneg_right (show C1 * δ ≤ 1 by linarith) hω.le
          linarith
  have hκ8 : κ / 8 ∈ Ioc 0 θ₀ := ⟨by positivity, by linarith⟩
  obtain ⟨hcon, -⟩ := hC9 δ θ₀ δ' hδ (by linarith) hθ₀ (by linarith) hδ'0 (by linarith) ξ hξ _ hU'
    hB1 V' _ hGMC' hpinch hmass' (κ / 8) hκ8 τ ⟨hτ2, hτ1⟩
  -- Step 4: lower bound for the left side.
  have hs0 : 0 < R * (κ / 16) := by positivity
  have hLHS : ENNReal.ofReal target ≤
      V'.weight (closedBall ξ ((1 - δ' ^ (1 / 4 : ℝ)) * (κ / 8))) := by
    calc ENNReal.ofReal target
        = (ENNReal.ofReal (R ^ n))⁻¹ * ENNReal.ofReal (ω * (R * (κ / 16)) ^ n / 2) := by
          rw [← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity),
            htarget_def]
          congr 1
          rw [mul_pow]
          field_simp
      _ ≤ (ENNReal.ofReal (R ^ n))⁻¹ * V.weight (closedBall y (R * (κ / 16))) := by
          gcongr
          apply h1d y hyV _ hs0
          rw [hyR]
          linarith [mul_le_mul_of_nonneg_left hκ hR.le, mul_nonneg hθ₀.le hR.le]
      _ = V'.weight (closedBall ξ (κ / 16)) := by rw [hball, hRξ]
      _ ≤ V'.weight (closedBall ξ ((1 - δ' ^ (1 / 4 : ℝ)) * (κ / 8))) := by
          apply measure_mono
          apply closedBall_subset_closedBall
          have := mul_le_mul_of_nonneg_right (show 1 / 2 ≤ 1 - δ' ^ (1 / 4 : ℝ) by linarith)
            (by positivity : (0 : ℝ) ≤ κ / 8)
          linarith
  -- Step 5: a support point near `τ y`.
  have hpos : V.weight (closedBall (τ • y) (R * (τ * (κ / 8)))) ≠ 0 := by
    intro h0
    have hzero : V'.weight (closedBall (τ • ξ) (τ * (κ / 8))) = 0 := by
      rw [hball, smul_comm, hRξ, h0, mul_zero]
    rw [hzero, mul_zero, zero_add] at hcon
    have herr : C9 * δ' ^ (1 / 4 : ℝ) * |Real.log δ| < target := by
      calc C9 * δ' ^ (1 / 4 : ℝ) * |Real.log δ| ≤ C9' * δ' ^ (1 / 4 : ℝ) * |Real.log δ| := by
            gcongr
            exact le_max_left _ _
        _ < target := hδ5' δ hδ hδδ5
    have h := hLHS.trans hcon
    rw [ENNReal.ofReal_le_ofReal_iff'] at h
    rcases h with h | h <;> linarith
  obtain ⟨z, hzB, hzμ⟩ := Measure.nonempty_inter_support_of_pos (pos_iff_ne_zero.2 hpos)
  rw [mem_closedBall, dist_eq_norm] at hzB
  have hzn : ‖z‖ ≤ τ * R := by
    calc ‖z‖ = ‖(z - τ • y) + τ • y‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - τ • y‖ + ‖τ • y‖ := norm_add_le _ _
      _ ≤ R * (τ * (κ / 8)) + τ * ‖y‖ := by
          rw [norm_smul, Real.norm_of_nonneg hτ0.le]; linarith
      _ ≤ τ * R := by
          rw [hyR]
          linarith [mul_le_mul_of_nonneg_left (show κ / 8 ≤ θ₀ by linarith)
            (mul_nonneg hτ0.le hR.le)]
  have hzV : z ∈ V.support := by
    refine ⟨hBU ?_, hzμ⟩
    rw [mem_closedBall, dist_zero_right]
    linarith [mul_le_mul_of_nonneg_right hc1 hρ.le]
  have hzT := hT z ⟨hzV, by rw [mem_closedBall, dist_zero_right]; linarith⟩
  -- Step 6: conclusion from homogeneity and the 1-Lipschitz property of `dist(·, T)`.
  have hhom : τ * infDist y (T : Set (Amb n ℓ)) ≤ infDist (τ • y) (T : Set (Amb n ℓ)) := by
    rw [le_infDist ⟨0, T.zero_mem⟩]
    intro w hw
    have hw' : τ⁻¹ • w ∈ (T : Set (Amb n ℓ)) := T.smul_mem τ⁻¹ hw
    calc τ * infDist y (T : Set (Amb n ℓ)) ≤ τ * dist y (τ⁻¹ • w) :=
          mul_le_mul_of_nonneg_left (infDist_le_dist_of_mem hw') hτ0.le
      _ = dist (τ • y) (τ • (τ⁻¹ • w)) := by rw [dist_smul₀, Real.norm_of_nonneg hτ0.le]
      _ = dist (τ • y) w := by rw [smul_inv_smul₀ hτ0.ne']
  have htri : infDist (τ • y) (T : Set (Amb n ℓ)) ≤
      infDist z (T : Set (Amb n ℓ)) + dist (τ • y) z := infDist_le_infDist_add_dist
  rw [dist_comm, dist_eq_norm] at htri
  have hD : τ * infDist y (T : Set (Amb n ℓ)) ≤ τ * (5 / 8 * κ * R) := by
    linarith [mul_le_mul_of_nonneg_left hzn (by positivity : (0 : ℝ) ≤ κ / 2)]
  have hD' : infDist y (T : Set (Amb n ℓ)) ≤ 5 / 8 * κ * R := le_of_mul_le_mul_left hD hτ0
  rw [hyR]
  linarith [mul_le_mul_of_nonneg_left hθ₀8 (mul_pos hκ0 hR).le]

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05
