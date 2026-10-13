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

/-- Covering step in the proof of Simon Ch. 5, Theorem 7.1, second assertion (p. 127): if every
point of the open set `U` has a ball in `U` on which `F` is `C¹` with `α`-Hölder derivative, then
`F` is `C¹` on `U` and `D¹F` is `α`-Hölder on every compact `K ⊆ U`.  Pairs of points of `K` closer
than a Lebesgue number `δ` of a finite subcover lie in one ball; for the other pairs,
`‖DF(x) - DF(y)‖ ≤ 2 sup_K ‖DF‖ ≤ 2 sup_K ‖DF‖ δ^{-α} ‖x - y‖^α`. -/
theorem dohr_eb_lhr_cover_holder_one : ∀ (n : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) (U : Set (Rn n)) (F : Rn n → E), 0 < α → IsOpen U → (∀ x ∈ U, ∃ R : ℝ, 0 < R ∧ ball x R ⊆ U ∧ ContDiffOn ℝ 1 F (ball x R) ∧ ∃ C : ℝ, ∀ y ∈ ball x R, ∀ z ∈ ball x R, ‖fderiv ℝ F y - fderiv ℝ F z‖ ≤ C * ‖y - z‖ ^ α) → ContDiffOn ℝ 1 F U ∧ ∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ 1 F x - iteratedFDeriv ℝ 1 F y‖ ≤ C * ‖x - y‖ ^ α := by
  intro n E _ _ α U F hα hU hloc
  choose! R hR hRU hRF C hC using hloc
  -- Step 1: `F` is `C¹` on `U` by locality.
  have hF : ContDiffOn ℝ 1 F U := by
    refine contDiffOn_of_locally_contDiffOn fun x hx =>
      ⟨ball x (R x), isOpen_ball, mem_ball_self (hR x hx), ?_⟩
    rw [inter_eq_right.2 (hRU x hx)]
    exact hRF x hx
  refine ⟨hF, fun K hK hKU => ?_⟩
  -- Steps 2–3: `DF` is continuous on `U`, hence bounded by `S` on `K`.
  obtain ⟨S, hS⟩ := hK.exists_bound_of_continuousOn
    ((hF.continuousOn_fderiv_of_isOpen hU le_rfl).mono hKU)
  -- Step 4: finitely many hypothesis balls cover `K`; `Cs` bounds their Hölder constants.
  obtain ⟨t, htK, hKt⟩ := hK.elim_nhds_subcover (fun x => ball x (R x))
    fun x hx => ball_mem_nhds x (hR x (hKU hx))
  obtain ⟨Cs, hCs⟩ : ∃ Cs : ℝ, ∀ i ∈ t, C i ≤ Cs :=
    ⟨∑ i ∈ t, |C i|, fun i hi => (le_abs_self _).trans
      (Finset.single_le_sum (f := fun j => |C j|) (fun j _ => abs_nonneg _) hi)⟩
  -- Step 5: a Lebesgue number `δ` of this finite cover.
  obtain ⟨δ, hδ, hδK⟩ := lebesgue_number_lemma_of_metric hK
    (c := fun i : t => ball (i : Rn n) (R i)) (fun _ => isOpen_ball) fun x hx => by
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (hKt hx)
      exact mem_iUnion.2 ⟨⟨i, hi⟩, hxi⟩
  -- Steps 6–8: the Hölder bound for `DF` on `K`.
  have hD : ∀ x ∈ K, ∀ y ∈ K, ‖fderiv ℝ F x - fderiv ℝ F y‖ ≤
      max Cs (2 * S * (δ ^ α)⁻¹) * ‖x - y‖ ^ α := by
    intro x hx y hy
    have hxy : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
    rcases lt_or_ge ‖x - y‖ δ with hlt | hge
    · -- Near pairs lie in one ball of the subcover.
      obtain ⟨⟨i, hi⟩, hiδ⟩ := hδK x hx
      have hxB : x ∈ ball i (R i) := hiδ (mem_ball_self hδ)
      have hyB : y ∈ ball i (R i) := hiδ (mem_ball'.2 (by rwa [dist_eq_norm]))
      calc ‖fderiv ℝ F x - fderiv ℝ F y‖ ≤ C i * ‖x - y‖ ^ α :=
            hC i (hKU (htK i hi)) x hxB y hyB
        _ ≤ max Cs (2 * S * (δ ^ α)⁻¹) * ‖x - y‖ ^ α :=
            mul_le_mul_of_nonneg_right ((hCs i hi).trans (le_max_left _ _)) hxy
    · -- Far pairs: `‖x - y‖ ^ α ≥ δ ^ α > 0`.
      have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS x hx)
      have hδα : 0 < δ ^ α := Real.rpow_pos_of_pos hδ α
      calc ‖fderiv ℝ F x - fderiv ℝ F y‖ ≤ ‖fderiv ℝ F x‖ + ‖fderiv ℝ F y‖ := norm_sub_le _ _
        _ ≤ S + S := add_le_add (hS x hx) (hS y hy)
        _ = 2 * S * (δ ^ α)⁻¹ * δ ^ α := by rw [inv_mul_cancel_right₀ hδα.ne', two_mul]
        _ ≤ 2 * S * (δ ^ α)⁻¹ * ‖x - y‖ ^ α :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hδ.le hge hα.le) (by positivity)
        _ ≤ max Cs (2 * S * (δ ^ α)⁻¹) * ‖x - y‖ ^ α :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hxy
  -- Step 9: `D¹F(z)` is the image of `DF(z)` under a linear isometry equivalence.
  have hiso : ∀ z, iteratedFDeriv ℝ 1 F z =
      (continuousMultilinearCurryFin1 ℝ (Rn n) E).symm (fderiv ℝ F z) := by
    intro z
    ext m
    rw [iteratedFDeriv_one_apply, continuousMultilinearCurryFin1_symm_apply]
  refine ⟨max Cs (2 * S * (δ ^ α)⁻¹), fun x hx y hy => ?_⟩
  rw [hiso x, hiso y, ← map_sub, LinearIsometryEquiv.norm_map]
  exact hD x hx y hy
/-- **Uniform bounds for a `C¹` scalar function on a compact convex set** (the scalar step of the
coefficient bounds in the linear higher-regularity part of Simon 7.1).  Let `0 < α ≤ 1`, `U ⊆ ℝⁿ`
open, `K ⊆ U` compact and convex, and `f` be `C¹` on `U`.  Then some `S ≥ 0` has `|f(x)| ≤ S` and
`|f(x) − f(y)| ≤ S |x − y|^α` for all `x, y ∈ K`.
Proof: `f` and `Df` are continuous, hence bounded, on the compact `K`; the mean value inequality
on the convex `K` gives `|f(x) − f(y)| ≤ S₁ |x − y|`; and with `D = diam K`,
`t = t^α t^{1−α} ≤ D^{1−α} t^α` for `0 ≤ t ≤ D`. -/
theorem dohr_eb_lhr_cub_scalar_c1_bounds : ∀ (n : ℕ) (α : ℝ) (U K : Set (Rn n)) (f : Rn n → ℝ), 0 < α → α ≤ 1 → IsOpen U → IsCompact K → Convex ℝ K → K ⊆ U → ContDiffOn ℝ 1 f U → ∃ S : ℝ, 0 ≤ S ∧ ∀ x ∈ K, ∀ y ∈ K, |f x| ≤ S ∧ |f x - f y| ≤ S * ‖x - y‖ ^ α := by
  intro n α U K f hα0 hα1 hU hK hKc hKU hf
  -- Step 1: `f` and `Df` are continuous on `K`, and `f` is differentiable at every point of `K`.
  have hfc : ContinuousOn f K := hf.continuousOn.mono hKU
  have hdfc : ContinuousOn (fderiv ℝ f) K := (hf.continuousOn_fderiv_of_isOpen hU le_rfl).mono hKU
  have hfd : ∀ x ∈ K, DifferentiableAt ℝ f x := fun x hx =>
    (hf.differentiableOn one_ne_zero x (hKU hx)).differentiableAt (hU.mem_nhds (hKU hx))
  -- Step 2: `|f| ≤ S0` and `‖Df‖ ≤ S1` on the compact set `K`.
  obtain ⟨S0, hS0⟩ := hK.exists_bound_of_continuousOn hfc
  obtain ⟨S1, hS1⟩ := hK.exists_bound_of_continuousOn hdfc
  -- Step 3: mean value inequality on the convex set `K`.
  have hlip : ∀ x ∈ K, ∀ y ∈ K, |f x - f y| ≤ max S1 0 * ‖x - y‖ := by
    intro x hx y hy
    have h := hKc.norm_image_sub_le_of_norm_fderiv_le (C := max S1 0) hfd
      (fun z hz => (hS1 z hz).trans (le_max_left _ _)) hy hx
    rwa [Real.norm_eq_abs] at h
  -- Step 4: `‖x - y‖ ≤ D := diam K` on `K`.
  have hdist : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ Metric.diam K := fun x hx y hy => by
    rw [← dist_eq_norm]
    exact Metric.dist_le_diam_of_mem hK.isBounded hx hy
  -- Step 5: `t ≤ D^(1-α) t^α` for `0 ≤ t ≤ D`.
  have helem : ∀ t : ℝ, 0 ≤ t → t ≤ Metric.diam K →
      t ≤ Metric.diam K ^ (1 - α) * t ^ α := by
    intro t ht0 htD
    rcases ht0.eq_or_lt with rfl | htpos
    · rw [Real.zero_rpow hα0.ne', mul_zero]
    · have h1 : t ^ α * t ^ (1 - α) = t := by
        rw [← Real.rpow_add htpos, show α + (1 - α) = 1 by ring, Real.rpow_one]
      have h2 : t ^ (1 - α) ≤ Metric.diam K ^ (1 - α) :=
        Real.rpow_le_rpow ht0 htD (by linarith)
      calc t = t ^ α * t ^ (1 - α) := h1.symm
        _ ≤ t ^ α * Metric.diam K ^ (1 - α) :=
          mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg ht0 _)
        _ = Metric.diam K ^ (1 - α) * t ^ α := mul_comm _ _
  -- Steps 6-7: `S := max (max S0 0) (max S1 0 * D^(1-α))`.
  refine ⟨max (max S0 0) (max S1 0 * Metric.diam K ^ (1 - α)),
    (le_max_right _ _).trans (le_max_left _ _), ?_⟩
  intro x hx y hy
  constructor
  · calc |f x| = ‖f x‖ := (Real.norm_eq_abs _).symm
      _ ≤ S0 := hS0 x hx
      _ ≤ max S0 0 := le_max_left _ _
      _ ≤ _ := le_max_left _ _
  · calc |f x - f y| ≤ max S1 0 * ‖x - y‖ := hlip x hx y hy
      _ ≤ max S1 0 * (Metric.diam K ^ (1 - α) * ‖x - y‖ ^ α) :=
        mul_le_mul_of_nonneg_left (helem _ (norm_nonneg _) (hdist x hx y hy)) (le_max_right _ _)
      _ = (max S1 0 * Metric.diam K ^ (1 - α)) * ‖x - y‖ ^ α := (mul_assoc _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (norm_nonneg _) _)
/-- Coefficient bounds for the linear system in the proof of Simon Ch. 5, Theorem 7.1 (second
assertion, p. 127), steps 1, 2 and 6: on a finite-dimensional real normed space `L` with basis
`E₀, …, E_{N-1}`, every continuous bilinear form satisfies
`|B(P)(Q)| ≤ c (∑_{r,t} |B(E_r)(E_t)|) ‖P‖ ‖Q‖`, and likewise for the difference `B − B'` of two
forms, with `c = c₀²`, `c₀ = ∑_r ‖π_r‖` the sum of the norms of the coordinate functionals. -/
theorem dohr_eb_lhr_cub_bilinear_basis_bound : ∀ (L : Type) [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L], ∃ (N : ℕ) (E : Fin N → L) (c : ℝ), 0 ≤ c ∧ (∀ (B : L →L[ℝ] L →L[ℝ] ℝ) (P Q : L), |B P Q| ≤ c * (∑ r, ∑ t, |B (E r) (E t)|) * ‖P‖ * ‖Q‖) ∧ ∀ (B B' : L →L[ℝ] L →L[ℝ] ℝ) (P Q : L), |B P Q - B' P Q| ≤ c * (∑ r, ∑ t, |B (E r) (E t) - B' (E r) (E t)|) * ‖P‖ * ‖Q‖ := by
  intro L _ _ _
  -- Step 1: a basis `b` of `L` and its continuous coordinate functionals `π r`.
  let b := Module.finBasis ℝ L
  let π : Fin (Module.finrank ℝ L) → L →L[ℝ] ℝ := fun r =>
    LinearMap.toContinuousLinearMap (b.coord r)
  have hπ : ∀ r P, π r P = b.repr P r := fun r P => by simp [π]
  -- Step 2: `|P_r| ≤ c₀ ‖P‖` with `c₀ = ∑ r, ‖π r‖`.
  let c₀ : ℝ := ∑ r, ‖π r‖
  have hc₀ : 0 ≤ c₀ := Finset.sum_nonneg fun r _ => norm_nonneg (π r)
  have hcoord : ∀ r P, |b.repr P r| ≤ c₀ * ‖P‖ := by
    intro r P
    rw [← hπ, ← Real.norm_eq_abs]
    calc ‖π r P‖ ≤ ‖π r‖ * ‖P‖ := (π r).le_opNorm P
      _ ≤ c₀ * ‖P‖ := mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (fun s _ => norm_nonneg (π s)) (Finset.mem_univ r)) (norm_nonneg P)
  -- Step 3: `B P Q = ∑ r, ∑ t, P_r Q_t B (b r) (b t)`.
  have hexp : ∀ (B : L →L[ℝ] L →L[ℝ] ℝ) (P Q : L),
      B P Q = ∑ r, ∑ t, b.repr P r * b.repr Q t * B (b r) (b t) := by
    intro B P Q
    conv_lhs => rw [← b.sum_repr P, ← b.sum_repr Q]
    simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun t _ => by ring
  -- Step 4: `|∑ r, ∑ t, P_r Q_t β r t| ≤ c₀² (∑ r, ∑ t, |β r t|) ‖P‖ ‖Q‖` for any array `β`.
  have harr : ∀ (β : Fin (Module.finrank ℝ L) → Fin (Module.finrank ℝ L) → ℝ) (P Q : L),
      |∑ r, ∑ t, b.repr P r * b.repr Q t * β r t| ≤
        c₀ ^ 2 * (∑ r, ∑ t, |β r t|) * ‖P‖ * ‖Q‖ := by
    intro β P Q
    calc |∑ r, ∑ t, b.repr P r * b.repr Q t * β r t|
        ≤ ∑ r, |∑ t, b.repr P r * b.repr Q t * β r t| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r, ∑ t, |b.repr P r * b.repr Q t * β r t| :=
          Finset.sum_le_sum fun r _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r, ∑ t, c₀ * ‖P‖ * (c₀ * ‖Q‖) * |β r t| := by
          refine Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun t _ => ?_
          rw [abs_mul, abs_mul]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul (hcoord r P) (hcoord t Q) (abs_nonneg _) (by positivity)) (abs_nonneg _)
      _ = c₀ ^ 2 * (∑ r, ∑ t, |β r t|) * ‖P‖ * ‖Q‖ := by
          simp only [← Finset.mul_sum]
          ring
  -- Step 5: take `E = b` and `c = c₀²`; for `B − B'` subtract the two expansions termwise.
  refine ⟨Module.finrank ℝ L, b, c₀ ^ 2, by positivity, fun B P Q => ?_, fun B B' P Q => ?_⟩
  · rw [hexp B P Q]
    exact harr _ P Q
  · rw [hexp B P Q, hexp B' P Q]
    simp only [← Finset.sum_sub_distrib, ← mul_sub]
    exact harr _ P Q
/-- Coefficient bounds in the elliptic bootstrap of Simon Ch. 5, Theorem 7.1, second assertion
(p. 127): if every component `x ↦ a(x)[P][Q]` of a field `a` of continuous bilinear forms on
`L = L(ℝⁿ, ℝ^ℓ)` is `C¹` on the open set `U`, then on each compact convex `K ⊆ U` the forms `a(x)`
are uniformly bounded and uniformly `α`-Hölder in `x`.  A basis `E_r` of `L` controls every
bilinear form through its values `B(E_r, E_t)`, and each `C¹` component `a_rt(x) = a(x)[E_r][E_t]`
is bounded by `S_rt` and `α`-Hölder with constant `S_rt` on `K`; take `M := c Σ_{r,t} S_rt`. -/
theorem dohr_eb_lhr_coeff_uniform_bounds : ∀ (n ℓ : ℕ) (α : ℝ) (U K : Set (Rn n)) (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ), 0 < α → α ≤ 1 → IsOpen U → IsCompact K → Convex ℝ K → K ⊆ U → (∀ P Q : Rn n →L[ℝ] Rn ℓ, ContDiffOn ℝ 1 (fun x => a x P Q) U) → ∃ M : ℝ, ∀ x ∈ K, ∀ y ∈ K, ∀ P Q : Rn n →L[ℝ] Rn ℓ, |a x P Q| ≤ M * ‖P‖ * ‖Q‖ ∧ |a x P Q - a y P Q| ≤ M * ‖x - y‖ ^ α * ‖P‖ * ‖Q‖ := by
  intro n ℓ α U K a hα hα1 hU hK hKc hKU ha
  -- Steps 1–2: expansion of bilinear forms on a basis `E` of `L`.
  obtain ⟨N, E, c, hc, hB, hBB'⟩ :=
    Submission.dohr_eb_lhr_cub_bilinear_basis_bound (Rn n →L[ℝ] Rn ℓ)
  -- Steps 3–5: each component `a_rt` is bounded and `α`-Hölder on `K`, with constant `S r t`.
  choose S hS0 hS using fun r t : Fin N =>
    Submission.dohr_eb_lhr_cub_scalar_c1_bounds n α U K (fun x => a x (E r) (E t)) hα hα1 hU hK
      hKc hKU (ha (E r) (E t))
  -- Steps 6–7: sum the component bounds over the basis.
  refine ⟨c * ∑ r, ∑ t, S r t, fun x hx y hy P Q => ⟨?_, ?_⟩⟩
  · calc |a x P Q| ≤ c * (∑ r, ∑ t, |a x (E r) (E t)|) * ‖P‖ * ‖Q‖ := hB (a x) P Q
      _ ≤ c * (∑ r, ∑ t, S r t) * ‖P‖ * ‖Q‖ := by
        gcongr with r _ t _
        exact (hS r t x hx y hy).1
  · calc |a x P Q - a y P Q|
        ≤ c * (∑ r, ∑ t, |a x (E r) (E t) - a y (E r) (E t)|) * ‖P‖ * ‖Q‖ :=
          hBB' (a x) (a y) P Q
      _ ≤ c * (∑ r, ∑ t, S r t * ‖x - y‖ ^ α) * ‖P‖ * ‖Q‖ := by
        gcongr with r _ t _
        exact (hS r t x hx y hy).2
      _ = c * (∑ r, ∑ t, S r t) * ‖x - y‖ ^ α * ‖P‖ * ‖Q‖ := by
        simp only [← Finset.sum_mul]
        ring
/-- Continuity of a linear-form family evaluated along continuous data (in the difference-quotient
weak equation of the linear higher-regularity step of the elliptic bootstrap for Simon 7.1): if
`x ↦ Φ(x)[P]` is continuous on the open set `U` for every `P ∈ L = L(ℝⁿ, ℝ^ℓ)`, `s(x₀) ∈ U` and `s`,
`B` are continuous at `x₀`, then `x ↦ Φ(s(x))[B(x)]` is continuous at `x₀`.  Expanding `B(x)` in a
basis `(E_r)` of the finite-dimensional space `L` writes `Φ(s(x))[B(x)]` as the finite sum
`Σ_r c_r(B(x)) Φ(s(x))[E_r]` of products of functions continuous at `x₀`. -/
theorem dohr_eb_lhr_dqwe_linear_family_continuousAt : ∀ (n ℓ : ℕ) (U : Set (Rn n)) (Φ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (s : Rn n → Rn n) (B : Rn n → Rn n →L[ℝ] Rn ℓ) (x₀ : Rn n), IsOpen U → (∀ P : Rn n →L[ℝ] Rn ℓ, ContinuousOn (fun x => Φ x P) U) → s x₀ ∈ U → ContinuousAt s x₀ → ContinuousAt B x₀ → ContinuousAt (fun x => Φ (s x) (B x)) x₀ := by
  intro n ℓ U Φ s B x₀ hU hΦ hs₀ hs hB
  -- Step 1: a basis `E_r = b r` of `L`; its coordinates `c_r = b.coord r` are continuous on `L`.
  let b := Module.finBasis ℝ (Rn n →L[ℝ] Rn ℓ)
  -- Step 2: `Φ(s x)[B x] = Σ_r c_r(B x) Φ(s x)[E_r]`, by linearity of `Φ(s x)`.
  have hexp : (fun x => Φ (s x) (B x)) = fun x => ∑ r, b.repr (B x) r * Φ (s x) (b r) := by
    funext x
    conv_lhs => rw [← b.sum_repr (B x)]
    simp only [map_sum, map_smul, smul_eq_mul]
  -- Step 3: `x ↦ c_r(B x)` is continuous at `x₀`.
  have hc : ∀ r, ContinuousAt (fun x => b.repr (B x) r) x₀ := fun r =>
    (b.coord r).continuous_of_finiteDimensional.continuousAt.comp hB
  -- Step 4: `x ↦ Φ(s x)[E_r]` is continuous at `x₀`, since `U` is a neighbourhood of `s x₀`.
  have hΦr : ∀ r, ContinuousAt (fun x => Φ (s x) (b r)) x₀ := fun r =>
    ((hΦ (b r)).continuousAt (hU.mem_nhds hs₀)).comp hs
  -- Step 5: a finite sum of products of functions continuous at `x₀` is continuous at `x₀`.
  rw [hexp]
  exact tendsto_finsetSum _ fun r _ => (hc r).mul (hΦr r)
/-- **Continuity of a bilinear-form family evaluated along continuous data.**  Let
`L = L(ℝⁿ, ℝ^ℓ)`, let `U ⊆ ℝⁿ` be open and let `a : ℝⁿ → L(L, L(L, ℝ))` be such that
`x ↦ a(x)[P][Q]` is continuous on `U` for all `P, Q ∈ L`.  If `s(x₀) ∈ U` and `s`, `A`, `B` are
continuous at `x₀`, then `x ↦ a(s(x))[A(x)][B(x)]` is continuous at `x₀`.
In a basis `(E_r)` of `L` with (continuous) coordinate functionals `c_r`,
`a(s(x))[A(x)][B(x)] = Σ_r c_r(A(x)) · a(s(x))[E_r][B(x)]`, and each `x ↦ a(s(x))[E_r][B(x)]` is
continuous at `x₀` by `dohr_eb_lhr_dqwe_linear_family_continuousAt` applied to `y ↦ a(y)[E_r]`. -/
theorem dohr_eb_lhr_dqwe_bilinear_family_continuousAt : ∀ (n ℓ : ℕ) (U : Set (Rn n)) (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (s : Rn n → Rn n) (A B : Rn n → Rn n →L[ℝ] Rn ℓ) (x₀ : Rn n), IsOpen U → (∀ P Q : Rn n →L[ℝ] Rn ℓ, ContinuousOn (fun x => a x P Q) U) → s x₀ ∈ U → ContinuousAt s x₀ → ContinuousAt A x₀ → ContinuousAt B x₀ → ContinuousAt (fun x => a (s x) (A x) (B x)) x₀ := by
  intro n ℓ U a s A B x₀ hU ha hsU hs hA hB
  -- Step 1: a basis `E_r = b r` of the finite-dimensional space `L`; its coordinate functionals
  -- `c_r = b.coord r` are continuous.
  let b := Module.finBasis ℝ (Rn n →L[ℝ] Rn ℓ)
  have hc : ∀ r, Continuous fun P : Rn n →L[ℝ] Rn ℓ => b.repr P r := fun r =>
    (b.coord r).continuous_of_finiteDimensional
  -- Step 2: expanding the first slot, `a(s x)[A x][B x] = Σ_r c_r(A x) · a(s x)[E_r][B x]`.
  have hexp : ∀ x, a (s x) (A x) (B x) = ∑ r, b.repr (A x) r * a (s x) (b r) (B x) := by
    intro x
    conv_lhs => rw [← b.sum_repr (A x)]
    simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul]
  simp only [hexp]
  -- Steps 3–5: each summand is `c_r ∘ A` times `x ↦ a(s x)[E_r][B x]`, both continuous at `x₀`
  -- (the latter by the linear-family lemma for `y ↦ a(y)[E_r]`), and finite sums preserve this.
  refine tendsto_finsetSum _ fun r _ => ((hc r).continuousAt.comp hA).mul ?_
  exact Submission.dohr_eb_lhr_dqwe_linear_family_continuousAt n ℓ U (fun y => a y (b r)) s B x₀
    hU (fun P => ha (b r) P) hsU hs hB
/-- Translated weak identity (difference-quotient step of the linear higher-regularity argument in
the elliptic bootstrap of Simon Ch. 5, Theorem 7.1).  Suppose
`∫_U a(x)[Dv(x)][Dζ(x)] dx = ∫_U Φ(x)[Dζ(x)] dx` for every `C¹` map `ζ : ℝⁿ → ℝ^ℓ` with compact
support in `U`, and let `η` be `C¹` with compact support and `x + h ∈ U` for `x ∈ spt η`.  Then
`∫ a(x + h)[Dv(x + h)][Dη(x)] dx = ∫ Φ(x + h)[Dη(x)] dx` over all of `ℝⁿ`.  Proof: test with
`ζ = η(· − h)`, which is `C¹` with compact support in `U` and `Dζ = Dη(· − h)`; both integrands
vanish off `U`, so the integrals over `U` are integrals over `ℝⁿ`; finally substitute `y = x + h`
(translation invariance of Lebesgue measure). -/
theorem dohr_eb_lhr_dqwe_shifted_weak_identity : ∀ (n ℓ : ℕ) (U : Set (Rn n)) (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Φ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (v : Rn n → Rn ℓ) (h : Rn n) (η : Rn n → Rn ℓ), (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ U → ∫ x in U, a x (fderiv ℝ v x) (fderiv ℝ ζ x) = ∫ x in U, Φ x (fderiv ℝ ζ x)) → ContDiff ℝ 1 η → HasCompactSupport η → (∀ x ∈ tsupport η, x + h ∈ U) → ∫ x, a (x + h) (fderiv ℝ v (x + h)) (fderiv ℝ η x) = ∫ x, Φ (x + h) (fderiv ℝ η x) := by
  intro n ℓ U a Φ v h η hweak hη hηc hηU
  -- Step 1: the translated test function `ζ = η(· − h)` is `C¹` with compact support.
  have hζC : ContDiff ℝ 1 (fun y => η (y - h)) := hη.comp (contDiff_id.sub contDiff_const)
  have hζc : HasCompactSupport (fun y => η (y - h)) := hηc.comp_homeomorph (Homeomorph.subRight h)
  -- Step 2: `y ∈ spt ζ ⇒ y − h ∈ spt η ⇒ y = (y − h) + h ∈ U`.
  have hζU : tsupport (fun y => η (y - h)) ⊆ U := fun y hy => by
    simpa only [sub_add_cancel] using
      hηU (y - h) (tsupport_comp_subset_preimage η (continuous_id.sub continuous_const) hy)
  -- Step 3: the weak identity for `ζ`, with `Dζ(y) = Dη(y − h)`.
  have h3 := hweak (fun y => η (y - h)) hζC hζc hζU
  simp only [fderiv_comp_sub] at h3
  -- Step 4: off `U`, `y − h ∉ spt η ⊇ spt Dη`, so `Dη(y − h) = 0` and both integrands vanish.
  have hvan : ∀ y, y ∉ U → fderiv ℝ η (y - h) = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport fun hmem => hy (by
      simpa only [sub_add_cancel] using hηU (y - h) (tsupport_fderiv_subset ℝ hmem))
  have hL : ∫ y in U, a y (fderiv ℝ v y) (fderiv ℝ η (y - h)) =
      ∫ y, a y (fderiv ℝ v y) (fderiv ℝ η (y - h)) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by rw [hvan y hy, map_zero]
  have hR : ∫ y in U, Φ y (fderiv ℝ η (y - h)) = ∫ y, Φ y (fderiv ℝ η (y - h)) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by rw [hvan y hy, map_zero]
  -- Step 5: substitute `y = x + h` (Lebesgue measure is translation invariant), `x + h − h = x`.
  have e1 := integral_add_right_eq_self (μ := volume)
    (fun y => a y (fderiv ℝ v y) (fderiv ℝ η (y - h))) h
  have e2 := integral_add_right_eq_self (μ := volume) (fun y => Φ y (fderiv ℝ η (y - h))) h
  simp only [add_sub_cancel_right] at e1 e2
  rw [e1, e2, ← hL, ← hR]
  exact h3
/-- A function `F : ℝⁿ → ℝ` continuous at every point of a compact set `K` and vanishing off `K` is
Lebesgue integrable.  `K` is closed, so each `x ∉ K` has the open neighbourhood `ℝⁿ \ K` on which
`F = 0`, and `F` is continuous at `x`; at the points of `K` it is continuous by hypothesis.  Thus `F`
is continuous, and it has compact support since it vanishes off the compact set `K`, so it is
integrable for `volume`, which is finite on compact sets. -/
theorem dohr_eb_lhr_dqwe_integrable_of_continuousAt : ∀ (n : ℕ) (F : Rn n → ℝ) (K : Set (Rn n)), IsCompact K → (∀ x ∈ K, ContinuousAt F x) → (∀ x, x ∉ K → F x = 0) → Integrable F := by
  intro n F K hK hcont hzero
  -- Steps 1–3: `F` is continuous at every point; off `K` it agrees with `0` on the open
  -- neighbourhood `Kᶜ` of the point.
  have hF : Continuous F := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    by_cases hx : x ∈ K
    · exact hcont x hx
    · have hev : (fun _ => (0 : ℝ)) =ᶠ[𝓝 x] F := by
        filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
        exact (hzero y hy).symm
      exact continuousAt_const.congr hev
  -- Steps 4–5: `F` vanishes off the compact set `K`, so it has compact support and is integrable.
  exact hF.integrable_of_hasCompactSupport (HasCompactSupport.intro hK hzero)
/-- Derivative of a difference quotient (difference-quotient step of the linear higher-regularity
argument in the elliptic bootstrap of Simon Ch. 5, Theorem 7.1): if `v : ℝⁿ → ℝ^ℓ` is
differentiable at `x` and at `x + d e`, then the derivative at `x` of
`z ↦ d⁻¹ (v(z + d e) − v(z))` is `d⁻¹ (Dv(x + d e) − Dv(x))`.  For `d = 0` both sides vanish,
as `0⁻¹ = 0`.  By the chain rule `g(z) = v(z + d e)` is differentiable at `x` with
`Dg(x) = Dv(x + d e)`; the derivative of `d⁻¹ (g − v)` is then `d⁻¹ (Dg(x) − Dv(x))`. -/
theorem dohr_eb_lhr_dqwe_fderiv_diff_quot : ∀ (n ℓ : ℕ) (v : Rn n → Rn ℓ) (e x : Rn n) (d : ℝ), DifferentiableAt ℝ v x → DifferentiableAt ℝ v (x + d • e) → fderiv ℝ (fun z => d⁻¹ • (v (z + d • e) - v z)) x = d⁻¹ • (fderiv ℝ v (x + d • e) - fderiv ℝ v x) := by
  intro n ℓ v e x d hx hxd
  have hg : DifferentiableAt ℝ (fun z => v (z + d • e)) x :=
    hxd.comp x (differentiableAt_id.add_const (d • e))
  rw [fderiv_fun_const_smul (hg.fun_sub hx) d⁻¹, fderiv_fun_sub hg hx,
    fderiv_comp_add_right (d • e)]
/-- Difference quotients of a weak solution (step 3 of the linear higher-regularity argument behind
**Simon Ch. 5, Theorem 7.1(ii)**).  If `v ∈ C¹(U)` satisfies `∫_U a(x)[Dv][Dζ] = ∫_U Φ(x)[Dζ]` for
all `ζ ∈ C¹_c(U; ℝ^ℓ)`, then `w = d⁻¹ (v(· + de) − v)` satisfies `∫_B a(x)[Dw][Dζ] = ∫_B Ψ(x)[Dζ]`
on `B = B̆_{2R}(xb)` for all `ζ ∈ C¹_c(B; ℝ^ℓ)`, where
`Ψ(x) = d⁻¹ (Φ(x + de) − Φ(x)) − d⁻¹ (a(x + de) − a(x))[Dv(x + de)]`: test the equation with `ζ`
and with `ζ(· − de)`, subtract, and divide by `d`. -/
theorem dohr_eb_lhr_dq_weak_equation : ∀ (n ℓ : ℕ) (U : Set (Rn n)) (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Φ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (v : Rn n → Rn ℓ) (xb e : Rn n) (R d : ℝ), IsOpen U → 0 < R → closedBall xb (4 * R) ⊆ U → ‖e‖ ≤ 1 → d ≠ 0 → |d| < R → (∀ P Q : Rn n →L[ℝ] Rn ℓ, ContinuousOn (fun x => a x P Q) U) → (∀ P : Rn n →L[ℝ] Rn ℓ, ContinuousOn (fun x => Φ x P) U) → ContDiffOn ℝ 1 v U → (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ U → ∫ x in U, a x (fderiv ℝ v x) (fderiv ℝ ζ x) = ∫ x in U, Φ x (fderiv ℝ ζ x)) → ∃ Ψ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ, (∀ (x : Rn n) (P : Rn n →L[ℝ] Rn ℓ), Ψ x P = d⁻¹ * (Φ (x + d • e) P - Φ x P) - d⁻¹ * (a (x + d • e) (fderiv ℝ v (x + d • e)) P - a x (fderiv ℝ v (x + d • e)) P)) ∧ ∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball xb (2 * R) → ∫ x in ball xb (2 * R), a x (fderiv ℝ (fun z => d⁻¹ • (v (z + d • e) - v z)) x) (fderiv ℝ ζ x) = ∫ x in ball xb (2 * R), Ψ x (fderiv ℝ ζ x) := by
  intro n ℓ U a Φ v xb e R d hU hR hball he hd hdR ha hΦ hv hweak
  -- Step 1: `Ψ(x) := d⁻¹ (Φ(x + de) − Φ(x)) − d⁻¹ (a(x + de)[Q_x] − a(x)[Q_x])`,
  -- `Q_x := Dv(x + de)`.
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ, ∀ (x : Rn n) (P : Rn n →L[ℝ] Rn ℓ),
      Ψ x P = d⁻¹ * (Φ (x + d • e) P - Φ x P) -
        d⁻¹ * (a (x + d • e) (fderiv ℝ v (x + d • e)) P - a x (fderiv ℝ v (x + d • e)) P) :=
    ⟨fun x => d⁻¹ • (Φ (x + d • e) - Φ x) -
        d⁻¹ • (a (x + d • e) (fderiv ℝ v (x + d • e)) - a x (fderiv ℝ v (x + d • e))),
      fun x P => by simp only [sub_apply, smul_apply, smul_eq_mul]⟩
  refine ⟨Ψ, hΨ, fun ζ hζ hζc hζB => ?_⟩
  -- Step 2: for `x ∈ B := B̆_{2R}(xb)`, both `x` and `x + de` lie in `B_{4R}(xb) ⊆ U`.
  have hde : ‖d • e‖ < R := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |d| * ‖e‖ ≤ |d| * 1 := mul_le_mul_of_nonneg_left he (abs_nonneg d)
      _ < R := by rwa [mul_one]
  have hBU : ∀ x ∈ ball xb (2 * R), x ∈ U := fun x hx =>
    hball (mem_closedBall.2 (by linarith [mem_ball.1 hx]))
  have hBU' : ∀ x ∈ ball xb (2 * R), x + d • e ∈ U := by
    intro x hx
    refine hball (mem_closedBall.2 ?_)
    have h1 : dist (x + d • e) x = ‖d • e‖ := by rw [dist_eq_norm, add_sub_cancel_left]
    linarith [dist_triangle (x + d • e) x xb, mem_ball.1 hx]
  -- Step 3: `v` is differentiable and `Dv` is continuous at every point of the open set `U`.
  have hvd : ∀ y ∈ U, DifferentiableAt ℝ v y := fun y hy =>
    (hv.differentiableOn one_ne_zero y hy).differentiableAt (hU.mem_nhds hy)
  have hDv : ∀ y ∈ U, ContinuousAt (fderiv ℝ v) y := fun y hy =>
    (hv.continuousOn_fderiv_of_isOpen hU le_rfl).continuousAt (hU.mem_nhds hy)
  have hsh : ∀ x : Rn n, ContinuousAt (fun y : Rn n => y + d • e) x := fun x =>
    (continuous_id.add continuous_const).continuousAt
  -- Step 5: `K := tsupport ζ ⊆ B` is compact; `Dζ` is continuous and vanishes off `K`.
  have hK : IsCompact (tsupport ζ) := hζc
  have hDζ : Continuous (fderiv ℝ ζ) := hζ.continuous_fderiv one_ne_zero
  have hDζ0 : ∀ x, x ∉ tsupport ζ → fderiv ℝ ζ x = 0 := fun x hx =>
    fderiv_of_notMem_tsupport ℝ hx
  have hKU : ∀ x ∈ tsupport ζ, x ∈ U := fun x hx => hBU x (hζB hx)
  have hKU' : ∀ x ∈ tsupport ζ, x + d • e ∈ U := fun x hx => hBU' x (hζB hx)
  -- Step 6: the integrands `f₁, g₁, f₂, f₃, g₃` are continuous at the points of `K` and vanish
  -- off `K`, hence integrable.
  have hf1 : Integrable (fun x => a x (fderiv ℝ v x) (fderiv ℝ ζ x)) :=
    Submission.dohr_eb_lhr_dqwe_integrable_of_continuousAt n _ _ hK
      (fun x hx => Submission.dohr_eb_lhr_dqwe_bilinear_family_continuousAt n ℓ U a (fun y => y)
        (fderiv ℝ v) (fderiv ℝ ζ) x hU ha (hKU x hx) (continuousAt_id' x) (hDv x (hKU x hx))
        hDζ.continuousAt)
      (fun x hx => by rw [hDζ0 x hx, map_zero])
  have hg1 : Integrable (fun x => Φ x (fderiv ℝ ζ x)) :=
    Submission.dohr_eb_lhr_dqwe_integrable_of_continuousAt n _ _ hK
      (fun x hx => Submission.dohr_eb_lhr_dqwe_linear_family_continuousAt n ℓ U Φ (fun y => y)
        (fderiv ℝ ζ) x hU hΦ (hKU x hx) (continuousAt_id' x) hDζ.continuousAt)
      (fun x hx => by rw [hDζ0 x hx, map_zero])
  have hf2 : Integrable (fun x => a x (fderiv ℝ v (x + d • e)) (fderiv ℝ ζ x)) :=
    Submission.dohr_eb_lhr_dqwe_integrable_of_continuousAt n _ _ hK
      (fun x hx => Submission.dohr_eb_lhr_dqwe_bilinear_family_continuousAt n ℓ U a (fun y => y)
        (fun y => fderiv ℝ v (y + d • e)) (fderiv ℝ ζ) x hU ha (hKU x hx) (continuousAt_id' x)
        ((hDv _ (hKU' x hx)).comp_of_eq (hsh x) rfl) hDζ.continuousAt)
      (fun x hx => by rw [hDζ0 x hx, map_zero])
  have hf3 : Integrable (fun x => a (x + d • e) (fderiv ℝ v (x + d • e)) (fderiv ℝ ζ x)) :=
    Submission.dohr_eb_lhr_dqwe_integrable_of_continuousAt n _ _ hK
      (fun x hx => Submission.dohr_eb_lhr_dqwe_bilinear_family_continuousAt n ℓ U a
        (fun y => y + d • e) (fun y => fderiv ℝ v (y + d • e)) (fderiv ℝ ζ) x hU ha (hKU' x hx)
        (hsh x) ((hDv _ (hKU' x hx)).comp_of_eq (hsh x) rfl) hDζ.continuousAt)
      (fun x hx => by rw [hDζ0 x hx, map_zero])
  have hg3 : Integrable (fun x => Φ (x + d • e) (fderiv ℝ ζ x)) :=
    Submission.dohr_eb_lhr_dqwe_integrable_of_continuousAt n _ _ hK
      (fun x hx => Submission.dohr_eb_lhr_dqwe_linear_family_continuousAt n ℓ U Φ
        (fun y => y + d • e) (fderiv ℝ ζ) x hU hΦ (hKU' x hx) (hsh x) hDζ.continuousAt)
      (fun x hx => by rw [hDζ0 x hx, map_zero])
  -- Steps 7–8: testing with `ζ` and with `ζ(· − de)` gives `∫ f₁ = ∫ g₁` and `∫ f₃ = ∫ g₃`.
  have h7 : ∫ x, a x (fderiv ℝ v x) (fderiv ℝ ζ x) = ∫ x, Φ x (fderiv ℝ ζ x) := by
    have h := Submission.dohr_eb_lhr_dqwe_shifted_weak_identity n ℓ U a Φ v 0 ζ hweak hζ hζc
      (fun x hx => by rw [add_zero]; exact hKU x hx)
    simpa only [add_zero] using h
  have h8 : ∫ x, a (x + d • e) (fderiv ℝ v (x + d • e)) (fderiv ℝ ζ x) =
      ∫ x, Φ (x + d • e) (fderiv ℝ ζ x) :=
    Submission.dohr_eb_lhr_dqwe_shifted_weak_identity n ℓ U a Φ v (d • e) ζ hweak hζ hζc hKU'
  -- Step 9: on `B`, `Dw = d⁻¹ (Dv(· + de) − Dv)` (step 4), so
  -- `a(x)[Dw(x)][Dζ(x)] = d⁻¹ (f₂ − f₁)(x)`; both sides become integrals over `ℝⁿ` of integrands
  -- vanishing off `K ⊆ B`.
  have hlhs : ∫ x in ball xb (2 * R), a x (fderiv ℝ (fun z => d⁻¹ • (v (z + d • e) - v z)) x)
      (fderiv ℝ ζ x) = d⁻¹ * ((∫ x, a x (fderiv ℝ v (x + d • e)) (fderiv ℝ ζ x)) -
        ∫ x, a x (fderiv ℝ v x) (fderiv ℝ ζ x)) := by
    have hEq : EqOn
        (fun x => a x (fderiv ℝ (fun z => d⁻¹ • (v (z + d • e) - v z)) x) (fderiv ℝ ζ x))
        (fun x => d⁻¹ * (a x (fderiv ℝ v (x + d • e)) (fderiv ℝ ζ x) -
          a x (fderiv ℝ v x) (fderiv ℝ ζ x))) (ball xb (2 * R)) := by
      intro x hx
      simp only
      rw [Submission.dohr_eb_lhr_dqwe_fderiv_diff_quot n ℓ v e x d (hvd x (hBU x hx))
        (hvd _ (hBU' x hx)), map_smul, map_sub, smul_apply, sub_apply, smul_eq_mul]
    have hzero : ∀ x, x ∉ ball xb (2 * R) → d⁻¹ * (a x (fderiv ℝ v (x + d • e)) (fderiv ℝ ζ x) -
        a x (fderiv ℝ v x) (fderiv ℝ ζ x)) = 0 := by
      intro x hx
      rw [hDζ0 x fun h => hx (hζB h), map_zero, map_zero, sub_zero, mul_zero]
    rw [setIntegral_congr_fun measurableSet_ball hEq,
      setIntegral_eq_integral_of_forall_compl_eq_zero hzero, integral_const_mul,
      integral_sub hf2 hf1]
  have hrhs : ∫ x in ball xb (2 * R), Ψ x (fderiv ℝ ζ x) =
      d⁻¹ * ((∫ x, Φ (x + d • e) (fderiv ℝ ζ x)) - ∫ x, Φ x (fderiv ℝ ζ x)) -
        d⁻¹ * ((∫ x, a (x + d • e) (fderiv ℝ v (x + d • e)) (fderiv ℝ ζ x)) -
          ∫ x, a x (fderiv ℝ v (x + d • e)) (fderiv ℝ ζ x)) := by
    have hzero : ∀ x, x ∉ ball xb (2 * R) → Ψ x (fderiv ℝ ζ x) = 0 := by
      intro x hx
      rw [hDζ0 x fun h => hx (hζB h), map_zero]
    have hI1 : Integrable fun x => d⁻¹ * (Φ (x + d • e) (fderiv ℝ ζ x) - Φ x (fderiv ℝ ζ x)) :=
      (hg3.sub hg1).const_mul _
    have hI2 : Integrable fun x => d⁻¹ * (a (x + d • e) (fderiv ℝ v (x + d • e)) (fderiv ℝ ζ x) -
        a x (fderiv ℝ v (x + d • e)) (fderiv ℝ ζ x)) :=
      (hf3.sub hf2).const_mul _
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    simp only [hΨ]
    rw [integral_sub hI1 hI2, integral_const_mul, integral_const_mul, integral_sub hg3 hg1,
      integral_sub hf3 hf2]
  -- `LHS − RHS = d⁻¹ [(∫ f₃ − ∫ g₃) − (∫ f₁ − ∫ g₁)] = 0`.
  rw [hlhs, hrhs, h7, ← h8]
  ring
/-- Steps 2–3 of the uniform difference-quotient bounds, for one function `g`: if `g` is `C¹` on
an open `U ⊇ K` with `K` compact and `D¹g = iteratedFDeriv ℝ 1 g` is `α`-Hölder on `K` with some
constant `C`, then `Dg = fderiv ℝ g` is bounded on `K` by some `S ≥ 0` and is `α`-Hölder on `K`
with some constant `H ≥ 0`.  (`D¹g(z)` is the image of `Dg(z)` under the linear isometry
`(continuousMultilinearCurryFin1 ℝ E F).symm`; no condition on `α` is needed.) -/
theorem dohr_eb_lhr_dqub_fderiv_consts : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (α : ℝ) (U K : Set E) (g : E → F), IsOpen U → IsCompact K → K ⊆ U → ContDiffOn ℝ 1 g U → (∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ 1 g x - iteratedFDeriv ℝ 1 g y‖ ≤ C * ‖x - y‖ ^ α) → ∃ S H : ℝ, 0 ≤ S ∧ 0 ≤ H ∧ (∀ x ∈ K, ‖fderiv ℝ g x‖ ≤ S) ∧ ∀ x ∈ K, ∀ y ∈ K, ‖fderiv ℝ g x - fderiv ℝ g y‖ ≤ H * ‖x - y‖ ^ α := by
  intro E F _ _ _ _ α U K g hU hK hKU hg hC
  obtain ⟨C, hC⟩ := hC
  -- Step 1: `D¹g(z) = Ψ(Dg(z))` for the linear isometry `Ψ = (continuousMultilinearCurryFin1 ℝ E F).symm`.
  have h1 : ∀ z, iteratedFDeriv ℝ 1 g z = (continuousMultilinearCurryFin1 ℝ E F).symm (fderiv ℝ g z) := by
    intro z
    ext m
    simp [iteratedFDeriv_one_apply]
  -- Step 2: `‖Dg(x) − Dg(y)‖ = ‖Ψ(Dg(x) − Dg(y))‖ = ‖D¹g(x) − D¹g(y)‖`.
  have h2 : ∀ x y, ‖fderiv ℝ g x - fderiv ℝ g y‖ = ‖iteratedFDeriv ℝ 1 g x - iteratedFDeriv ℝ 1 g y‖ := by
    intro x y
    rw [h1 x, h1 y, ← map_sub, LinearIsometryEquiv.norm_map]
  -- Step 3: `Dg` is continuous on the open `U ⊇ K`, hence bounded by some `S₀` on the compact `K`.
  obtain ⟨S₀, hS₀⟩ := hK.exists_bound_of_continuousOn
    ((hg.continuousOn_fderiv_of_isOpen hU le_rfl).mono hKU)
  -- Step 4: `S = max S₀ 0` and `H = max C 0`, using `‖x − y‖^α ≥ 0`.
  refine ⟨max S₀ 0, max C 0, le_max_right _ _, le_max_right _ _,
    fun x hx => (hS₀ x hx).trans (le_max_left _ _), fun x hx y hy => ?_⟩
  rw [h2 x y]
  exact (hC x hx y hy).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) _))
/-- **Simon Ch. 5, proof of Theorem 7.1 (elliptic bootstrap): difference-quotient bounds.**
Let `g` be differentiable on an open `U ⊇ B_{4R}(x̄)` with `‖Dg‖ ≤ S` and
`‖Dg(z) − Dg(w)‖ ≤ H ‖z − w‖^α` on `B_{4R}(x̄)`.  If `‖e‖ ≤ 1` and `0 < |d| < R`, then on
`B̆_{2R}(x̄)` the difference quotient `d⁻¹ (g(x + d e) − g(x))` is bounded by `S` and is
`α`-Hölder with constant `H`.
Proof: for `z ∈ B̆_{2R}(x̄)` and `|s| ≤ |d|`, `z + s e ∈ B_{4R}(x̄) ⊆ U`.  The mean value inequality
on this convex ball gives `‖g(x + d e) − g(x)‖ ≤ S |d|`.  For the second bound,
`h(s) = g(x + s e) − g(y + s e)` has `‖h'(s)‖ = ‖(Dg(x + s e) − Dg(y + s e)) e‖ ≤ H ‖x − y‖^α`
for `s` between `0` and `d`, so `‖h(d) − h(0)‖ ≤ H ‖x − y‖^α |d|`; divide by `|d|`. -/
theorem dohr_eb_lhr_dqub_dq_mean_value : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (α : ℝ) (U : Set E) (g : E → F) (xb e : E) (R S H d : ℝ), IsOpen U → closedBall xb (4 * R) ⊆ U → ‖e‖ ≤ 1 → DifferentiableOn ℝ g U → (∀ z ∈ closedBall xb (4 * R), ‖fderiv ℝ g z‖ ≤ S) → (∀ z ∈ closedBall xb (4 * R), ∀ w ∈ closedBall xb (4 * R), ‖fderiv ℝ g z - fderiv ℝ g w‖ ≤ H * ‖z - w‖ ^ α) → d ≠ 0 → |d| < R → ∀ x ∈ ball xb (2 * R), ∀ y ∈ ball xb (2 * R), ‖d⁻¹ • (g (x + d • e) - g x)‖ ≤ S ∧ ‖d⁻¹ • (g (x + d • e) - g x) - d⁻¹ • (g (y + d • e) - g y)‖ ≤ H * ‖x - y‖ ^ α := by
  intro E F _ _ _ _ α U g xb e R S H d hU hKU he hg hS hH hd hdR x hx y hy
  have hdpos : 0 < |d| := abs_pos.mpr hd
  -- Step 2: for `z ∈ ball xb (2 * R)` and `|s| ≤ |d|`, `z + s • e ∈ closedBall xb (4 * R)`.
  have hgeo : ∀ z ∈ ball xb (2 * R), ∀ s : ℝ, |s| ≤ |d| → z + s • e ∈ closedBall xb (4 * R) := by
    intro z hz s hs
    rw [mem_ball, dist_eq_norm] at hz
    rw [mem_closedBall, dist_eq_norm]
    have hse : ‖s • e‖ ≤ |d| := by
      rw [norm_smul, Real.norm_eq_abs]
      calc |s| * ‖e‖ ≤ |d| * 1 := mul_le_mul hs he (norm_nonneg e) (abs_nonneg d)
        _ = |d| := mul_one _
    calc ‖z + s • e - xb‖ = ‖(z - xb) + s • e‖ := by congr 1; abel
      _ ≤ ‖z - xb‖ + ‖s • e‖ := norm_add_le _ _
      _ ≤ 4 * R := by linarith [abs_nonneg d]
  -- Step 3: `g` is differentiable at every point of `closedBall xb (4 * R) ⊆ U`.
  have hdiff : ∀ z ∈ closedBall xb (4 * R), DifferentiableAt ℝ g z := fun z hz =>
    (hg z (hKU hz)).differentiableAt (hU.mem_nhds (hKU hz))
  have hx0 : x ∈ closedBall xb (4 * R) := by
    have h := hgeo x hx 0 (by simp)
    rwa [zero_smul, add_zero] at h
  constructor
  · -- Step 4: part (a), the mean value inequality on `closedBall xb (4 * R)`.
    have hmv : ‖g (x + d • e) - g x‖ ≤ S * ‖x + d • e - x‖ :=
      (convex_closedBall xb (4 * R)).norm_image_sub_le_of_norm_fderiv_le hdiff hS hx0
        (hgeo x hx d le_rfl)
    have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS x hx0)
    have hde : ‖d • e‖ ≤ |d| := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg d) he
    rw [add_sub_cancel_left] at hmv
    rw [norm_smul, norm_inv, Real.norm_eq_abs, inv_mul_le_iff₀ hdpos]
    calc ‖g (x + d • e) - g x‖ ≤ S * ‖d • e‖ := hmv
      _ ≤ S * |d| := mul_le_mul_of_nonneg_left hde hS0
      _ = |d| * S := mul_comm _ _
  · -- Steps 5–8: part (b), the mean value inequality for `s ↦ g (x + s • e) - g (y + s • e)`.
    have hI : ∀ s ∈ uIcc (0 : ℝ) d, |s| ≤ |d| := by
      intro s hs
      simpa using Set.abs_sub_left_of_mem_uIcc hs
    have hlin : ∀ (z : E) (s : ℝ), HasDerivAt (fun σ : ℝ => z + σ • e) e s := by
      intro z s
      simpa using ((hasDerivAt_id s).smul_const e).const_add z
    have hderiv : ∀ s ∈ uIcc (0 : ℝ) d, HasDerivWithinAt
        (fun σ : ℝ => g (x + σ • e) - g (y + σ • e))
        (fderiv ℝ g (x + s • e) e - fderiv ℝ g (y + s • e) e) (uIcc (0 : ℝ) d) s := by
      intro s hs
      have hxs := hdiff _ (hgeo x hx s (hI s hs))
      have hys := hdiff _ (hgeo y hy s (hI s hs))
      exact ((hxs.hasFDerivAt.comp_hasDerivAt s (hlin x s)).sub
        (hys.hasFDerivAt.comp_hasDerivAt s (hlin y s))).hasDerivWithinAt
    have hbound : ∀ s ∈ uIcc (0 : ℝ) d,
        ‖fderiv ℝ g (x + s • e) e - fderiv ℝ g (y + s • e) e‖ ≤ H * ‖x - y‖ ^ α := by
      intro s hs
      have hxy : x + s • e - (y + s • e) = x - y := add_sub_add_right_eq_sub x y (s • e)
      calc ‖fderiv ℝ g (x + s • e) e - fderiv ℝ g (y + s • e) e‖
          = ‖(fderiv ℝ g (x + s • e) - fderiv ℝ g (y + s • e)) e‖ := by rw [sub_apply]
        _ ≤ ‖fderiv ℝ g (x + s • e) - fderiv ℝ g (y + s • e)‖ * ‖e‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖fderiv ℝ g (x + s • e) - fderiv ℝ g (y + s • e)‖ :=
            mul_le_of_le_one_right (norm_nonneg _) he
        _ ≤ H * ‖x + s • e - (y + s • e)‖ ^ α :=
            hH _ (hgeo x hx s (hI s hs)) _ (hgeo y hy s (hI s hs))
        _ = H * ‖x - y‖ ^ α := by rw [hxy]
    have hmv := (convex_uIcc (0 : ℝ) d).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
      Set.left_mem_uIcc Set.right_mem_uIcc
    simp only [zero_smul, add_zero, sub_zero, Real.norm_eq_abs] at hmv
    have hrw : d⁻¹ • (g (x + d • e) - g x) - d⁻¹ • (g (y + d • e) - g y) =
        d⁻¹ • ((g (x + d • e) - g (y + d • e)) - (g x - g y)) := by
      rw [← smul_sub]; congr 1; abel
    rw [hrw, norm_smul, norm_inv, Real.norm_eq_abs, inv_mul_le_iff₀ hdpos]
    calc ‖(g (x + d • e) - g (y + d • e)) - (g x - g y)‖ ≤ H * ‖x - y‖ ^ α * |d| := hmv
      _ = |d| * (H * ‖x - y‖ ^ α) := mul_comm _ _
/-- Difference-quotient bounds in the elliptic bootstrap for Simon Ch. 5, Theorem 7.1, second
assertion (p. 127): on a finite-dimensional real normed space `L`, real linear and bilinear forms
are bounded by `C` times their largest value on finitely many test vectors `b r`.  Take a basis
`b` of `L`; its coordinates `π r` are continuous, and `c = Σ_r ‖π r‖` gives
`|b.repr P r| ≤ c ‖P‖`.  Expanding `P` in the basis gives `|f P| ≤ N c m ‖P‖`, expanding in both
arguments gives `|β Q P| ≤ N² c² m ‖Q‖ ‖P‖`, and `C = N c + N² c²`. -/
theorem dohr_eb_lhr_dqub_form_coords : ∀ (L : Type) [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L], ∃ (N : ℕ) (b : Fin N → L) (C : ℝ), 0 ≤ C ∧ (∀ (f : L → ℝ) (m : ℝ), IsLinearMap ℝ f → 0 ≤ m → (∀ r, |f (b r)| ≤ m) → ∀ P, |f P| ≤ C * m * ‖P‖) ∧ ∀ (β : L → L → ℝ) (m : ℝ), (∀ P, IsLinearMap ℝ (fun Q => β Q P)) → (∀ Q, IsLinearMap ℝ (β Q)) → 0 ≤ m → (∀ r t, |β (b r) (b t)| ≤ m) → ∀ Q P, |β Q P| ≤ C * m * ‖Q‖ * ‖P‖ := by
  intro L _ _ _
  -- Step 1: a basis `b` of `L` indexed by `Fin N` (`N = finrank ℝ L`).
  obtain ⟨N, ⟨b⟩⟩ : ∃ N : ℕ, Nonempty (Module.Basis (Fin N) ℝ L) :=
    ⟨_, ⟨Module.finBasis ℝ L⟩⟩
  -- Step 2: the coordinates `π r = b.coord r` are continuous as `L` is finite-dimensional, and
  -- `c = Σ_r ‖π r‖` gives `|b.repr P r| ≤ c ‖P‖`.
  obtain ⟨c, hc0, hcoord⟩ : ∃ c : ℝ, 0 ≤ c ∧ ∀ r P, |b.repr P r| ≤ c * ‖P‖ := by
    let π : Fin N → L →L[ℝ] ℝ := fun r => LinearMap.toContinuousLinearMap (b.coord r)
    refine ⟨∑ r, ‖π r‖, Finset.sum_nonneg fun r _ => norm_nonneg _, fun r P => ?_⟩
    have hπ : π r P = b.repr P r := by simp [π]
    calc |b.repr P r| = ‖π r P‖ := by rw [hπ, Real.norm_eq_abs]
      _ ≤ ‖π r‖ * ‖P‖ := (π r).le_opNorm P
      _ ≤ (∑ t, ‖π t‖) * ‖P‖ := mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (fun t _ => norm_nonneg (π t)) (Finset.mem_univ r)) (norm_nonneg P)
  -- Step 3: a linear `f` is determined by its basis values, `f P = Σ_r b.repr P r · f (b r)`.
  have hexp : ∀ f : L → ℝ, IsLinearMap ℝ f → ∀ P, f P = ∑ r, b.repr P r * f (b r) := by
    intro f hf P
    calc f P = IsLinearMap.mk' f hf (∑ r, b.repr P r • b r) := by
          rw [b.sum_repr, IsLinearMap.mk'_apply]
      _ = ∑ r, b.repr P r * f (b r) := by
          simp only [map_sum, map_smul, IsLinearMap.mk'_apply, smul_eq_mul]
  -- Step 4: the linear bound `|f P| ≤ N c m ‖P‖`.
  have hlin : ∀ (f : L → ℝ) (m : ℝ), IsLinearMap ℝ f → 0 ≤ m → (∀ r, |f (b r)| ≤ m) →
      ∀ P, |f P| ≤ N * c * m * ‖P‖ := by
    intro f m hf hm hb P
    rw [hexp f hf P]
    calc |∑ r, b.repr P r * f (b r)| ≤ ∑ r, |b.repr P r * f (b r)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r : Fin N, c * ‖P‖ * m := by
          gcongr with r
          rw [abs_mul]
          exact mul_le_mul (hcoord r P) (hb r) (abs_nonneg _) (by positivity)
      _ = N * c * m * ‖P‖ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  -- Steps 5–6: expanding `β` in each argument, i.e. the linear bound for each `β (b r)` and then
  -- for `Q ↦ β Q P`, gives `|β Q P| ≤ N² c² m ‖Q‖ ‖P‖`.
  have hbil : ∀ (β : L → L → ℝ) (m : ℝ), (∀ P, IsLinearMap ℝ (fun Q => β Q P)) →
      (∀ Q, IsLinearMap ℝ (β Q)) → 0 ≤ m → (∀ r t, |β (b r) (b t)| ≤ m) →
      ∀ Q P, |β Q P| ≤ N * c * (N * c) * m * ‖Q‖ * ‖P‖ := by
    intro β m hβ₁ hβ₂ hm hb Q P
    have hr : ∀ r, |β (b r) P| ≤ N * c * m * ‖P‖ := fun r =>
      hlin (β (b r)) m (hβ₂ (b r)) hm (hb r) P
    calc |β Q P| ≤ N * c * (N * c * m * ‖P‖) * ‖Q‖ :=
          hlin (fun Q => β Q P) (N * c * m * ‖P‖) (hβ₁ P) (by positivity) hr Q
      _ = N * c * (N * c) * m * ‖Q‖ * ‖P‖ := by ring
  -- Step 7: `C = N c + N² c²` serves for both bounds.
  refine ⟨N, b, N * c + N * c * (N * c), by positivity, fun f m hf hm hb P => ?_,
    fun β m hβ₁ hβ₂ hm hb Q P => ?_⟩
  · calc |f P| ≤ N * c * m * ‖P‖ := hlin f m hf hm hb P
      _ ≤ (N * c + N * c * (N * c)) * m * ‖P‖ := by
          rw [add_mul, add_mul]
          exact le_add_of_nonneg_right (by positivity)
  · calc |β Q P| ≤ N * c * (N * c) * m * ‖Q‖ * ‖P‖ := hbil β m hβ₁ hβ₂ hm hb Q P
      _ ≤ (N * c + N * c * (N * c)) * m * ‖Q‖ * ‖P‖ := by
          rw [add_mul, add_mul, add_mul]
          exact le_add_of_nonneg_left (by positivity)
/-- **Simon Ch. 5, proof of Theorem 7.1 (elliptic bootstrap): difference quotients of a locally
`C^{1,α}` map.**  Let `v` be locally `C^{1,α}` on the open set `U ⊇ B_{4R}(xb)` and `‖e‖ ≤ 1`.
There is `S` such that for every `0 < |d| < R` the difference quotient
`w_d(z) = d⁻¹ (v(z + d e) − v(z))` satisfies the following on `B̆_{2R}(xb)`: `‖w_d‖ ≤ S`, `w_d` is
`C¹`, `Dw_d(x) = d⁻¹ (Dv(x + d e) − Dv(x))`, and `Dw_d` is `α`-Hölder.
Proof: `dohr_eb_lhr_dqub_fderiv_consts` on the compact set `K₀ = B_{4R}(xb)` gives a bound `S_v`
and a Hölder constant `H_v` for `Dv` on `K₀`; put `S = S_v`.  For `z ∈ B̆_{2R}(xb)` and `|s| ≤ |d|`,
`‖z + s e − xb‖ < 2R + R ≤ 4R`, so `z` and `z + d e` lie in `K₀ ⊆ U`.  The bound on `w_d` is part
(a) of `dohr_eb_lhr_dqub_dq_mean_value`.  The `C¹` property and the derivative formula follow from
the chain rule for the translation `z ↦ z + d e`.  Finally
`Dw_d(x) − Dw_d(y) = d⁻¹ ((Dv(x + d e) − Dv(y + d e)) − (Dv(x) − Dv(y)))` has norm at most
`2 H_v |d|⁻¹ ‖x − y‖^α`. -/
theorem dohr_eb_lhr_dqub_wd_props : ∀ (n ℓ : ℕ) (α : ℝ) (U : Set (Rn n)) (v : Rn n → Rn ℓ) (xb e : Rn n) (R : ℝ), IsOpen U → 0 < R → closedBall xb (4 * R) ⊆ U → ‖e‖ ≤ 1 → IsLocallyHolderCkα 1 α v U → ∃ S : ℝ, ∀ d : ℝ, d ≠ 0 → |d| < R → (∀ x ∈ ball xb (2 * R), ‖d⁻¹ • (v (x + d • e) - v x)‖ ≤ S) ∧ ContDiffOn ℝ 1 (fun z => d⁻¹ • (v (z + d • e) - v z)) (ball xb (2 * R)) ∧ (∀ x ∈ ball xb (2 * R), fderiv ℝ (fun z => d⁻¹ • (v (z + d • e) - v z)) x = d⁻¹ • (fderiv ℝ v (x + d • e) - fderiv ℝ v x)) ∧ ∃ K : ℝ, ∀ x ∈ ball xb (2 * R), ∀ y ∈ ball xb (2 * R), ‖fderiv ℝ (fun z => d⁻¹ • (v (z + d • e) - v z)) x - fderiv ℝ (fun z => d⁻¹ • (v (z + d • e) - v z)) y‖ ≤ K * ‖x - y‖ ^ α := by
  intro n ℓ α U v xb e R hU hR hsub he hv
  -- Step 1: `v` is `C¹` on `U`, and `D¹v` is `α`-Hölder on the compact set `K₀ = B_{4R}(xb) ⊆ U`.
  have hC1 : ContDiffOn ℝ 1 v U := by simpa using hv.1
  have hK0 : IsCompact (closedBall xb (4 * R)) := isCompact_closedBall xb (4 * R)
  -- Step 2: `‖Dv‖ ≤ S_v` and `‖Dv(z) − Dv(w)‖ ≤ H_v ‖z − w‖^α` on `K₀`.  The constant
  -- `S := S_v` does not depend on `d`.
  obtain ⟨Sv, Hv, -, -, hSv, hHv⟩ :=
    Submission.dohr_eb_lhr_dqub_fderiv_consts (Rn n) (Rn ℓ) α U (closedBall xb (4 * R)) v hU hK0
      hsub hC1 (hv.2 _ hK0 hsub)
  refine ⟨Sv, fun d hd hdR => ?_⟩
  -- Step 3: `z + s e ∈ K₀` for `z ∈ B̆_{2R}(xb)` and `|s| ≤ |d|`; in particular `z, z + d e ∈ K₀`.
  have hgeom : ∀ z ∈ ball xb (2 * R), ∀ s : ℝ, |s| ≤ |d| → z + s • e ∈ closedBall xb (4 * R) := by
    intro z hz s hs
    rw [mem_ball, dist_eq_norm] at hz
    rw [mem_closedBall, dist_eq_norm]
    have hse : ‖s • e‖ ≤ |d| := by
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_of_le_one_right (abs_nonneg s) he).trans hs
    calc ‖z + s • e - xb‖ = ‖(z - xb) + s • e‖ := by rw [sub_add_eq_add_sub]
      _ ≤ ‖z - xb‖ + ‖s • e‖ := norm_add_le _ _
      _ ≤ 4 * R := by linarith
  have hz0 : ∀ z ∈ ball xb (2 * R), z ∈ closedBall xb (4 * R) := fun z hz => by
    simpa using hgeom z hz 0 (by simp)
  have hzd : ∀ z ∈ ball xb (2 * R), z + d • e ∈ closedBall xb (4 * R) := fun z hz =>
    hgeom z hz d le_rfl
  -- Step 4: claim (i) is part (a) of `dohr_eb_lhr_dqub_dq_mean_value` (taking `y = x`).
  have hdiff : DifferentiableOn ℝ v U := hC1.differentiableOn one_ne_zero
  have hmv := Submission.dohr_eb_lhr_dqub_dq_mean_value (Rn n) (Rn ℓ) α U v xb e R Sv Hv d hU hsub
    he hdiff hSv hHv hd hdR
  -- Step 6: `w_d` has derivative `d⁻¹ (Dv(x + d e) − Dv(x))` at every `x ∈ B̆_{2R}(xb)`.
  have hderiv : ∀ x ∈ ball xb (2 * R), HasFDerivAt (fun z => d⁻¹ • (v (z + d • e) - v z))
      (d⁻¹ • (fderiv ℝ v (x + d • e) - fderiv ℝ v x)) x := by
    intro x hx
    have hxU : x ∈ U := hsub (hz0 x hx)
    have hxdU : x + d • e ∈ U := hsub (hzd x hx)
    have hv0 : DifferentiableAt ℝ v x := (hdiff x hxU).differentiableAt (hU.mem_nhds hxU)
    have hv1 : DifferentiableAt ℝ v (x + d • e) :=
      (hdiff _ hxdU).differentiableAt (hU.mem_nhds hxdU)
    have hcomp : HasFDerivAt (fun z => v (z + d • e)) (fderiv ℝ v (x + d • e)) x := by
      simpa [Function.comp_def] using
        hv1.hasFDerivAt.comp x ((hasFDerivAt_id x).add_const (d • e))
    exact (hcomp.sub hv0.hasFDerivAt).const_smul d⁻¹
  refine ⟨fun x hx => (hmv x hx x hx).1, ?_, fun x hx => (hderiv x hx).fderiv, ?_⟩
  · -- Step 5: claim (ii), since `w_d = d⁻¹ • (v ∘ τ − v)` for the translation `τ z = z + d e`.
    have hτ : ContDiffOn ℝ 1 (fun z : Rn n => z + d • e) (ball xb (2 * R)) :=
      (contDiff_id.add contDiff_const).contDiffOn
    have hτU : MapsTo (fun z : Rn n => z + d • e) (ball xb (2 * R)) U := fun z hz =>
      hsub (hzd z hz)
    have h1 : ContDiffOn ℝ 1 (fun z => v (z + d • e)) (ball xb (2 * R)) := hC1.comp hτ hτU
    have h2 : ContDiffOn ℝ 1 v (ball xb (2 * R)) := hC1.mono fun z hz => hsub (hz0 z hz)
    exact (h1.sub h2).const_smul d⁻¹
  · -- Step 7: claim (iv) with `K = 2 H_v |d|⁻¹`, using the Hölder bound of `Dv` at the four points
    -- `x, y, x + d e, y + d e ∈ K₀`.
    refine ⟨2 * Hv * |d|⁻¹, fun x hx y hy => ?_⟩
    rw [(hderiv x hx).fderiv, (hderiv y hy).fderiv]
    have heq : d⁻¹ • (fderiv ℝ v (x + d • e) - fderiv ℝ v x) -
        d⁻¹ • (fderiv ℝ v (y + d • e) - fderiv ℝ v y) =
        d⁻¹ • ((fderiv ℝ v (x + d • e) - fderiv ℝ v (y + d • e)) -
          (fderiv ℝ v x - fderiv ℝ v y)) :=
      (smul_sub _ _ _).symm.trans (by rw [sub_sub_sub_comm])
    have h1 := hHv _ (hzd x hx) _ (hzd y hy)
    rw [add_sub_add_right_eq_sub] at h1
    have h2 := hHv _ (hz0 x hx) _ (hz0 y hy)
    rw [heq, norm_smul, norm_inv, Real.norm_eq_abs]
    calc |d|⁻¹ * ‖(fderiv ℝ v (x + d • e) - fderiv ℝ v (y + d • e)) -
          (fderiv ℝ v x - fderiv ℝ v y)‖
        ≤ |d|⁻¹ * (Hv * ‖x - y‖ ^ α + Hv * ‖x - y‖ ^ α) :=
          mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add h1 h2))
            (inv_nonneg.2 (abs_nonneg d))
      _ = 2 * Hv * |d|⁻¹ * ‖x - y‖ ^ α := by ring
/-- **Simon Ch. 5, proof of Theorem 7.1 (elliptic bootstrap): `d`-uniform Hölder bound for the
forcing term of the difference-quotient system.**  Let `L = L(ℝⁿ, ℝ^ℓ)`, `U ⊇ B_{4R}(xb)` open,
`‖e‖ ≤ 1`, let the coefficients `x ↦ a(x)[P][Q]` and `x ↦ Φ(x)[P]` be `C^{1,α}` in `U` and `v` be
`C^{1,α}` in `U`.  For `0 < |d| < R` put
`F_d(x, P) = d⁻¹ (Φ(x + d e)[P] − Φ(x)[P])
  − d⁻¹ (a(x + d e)[Dv(x + d e)][P] − a(x)[Dv(x + d e)][P])`.
Then `|F_d(x, P) − F_d(y, P)| ≤ M ‖x − y‖^α ‖P‖` on `B̆_{2R}(xb)` with `M` independent of `d`.
Proof: `dohr_eb_lhr_dqub_form_coords` gives a spanning family `b` of `L` and a constant `C`
bounding linear and bilinear forms by their values on `b`.  On `K₀ = B_{4R}(xb)`,
`dohr_eb_lhr_dqub_fderiv_consts` gives a common bound `S'` and a common Hölder constant `H` for
the derivatives of the scalar coefficients `a(·)[b_r][b_t]`, `Φ(·)[b_r]`, and `S_v`, `H_v` for
`Dv`; put `M = C (H + H S_v + S' H_v)`.  The mean value inequality
`dohr_eb_lhr_dqub_dq_mean_value` bounds the difference quotients of these coefficients by `S'`
and their differences at `x, y` by `H ‖x − y‖^α`.  With
`Q_x = Dv(x + d e)` and `Q_y = Dv(y + d e)`,
`F_d(x, P) − F_d(y, P) = T(P) − β₁(Q_x, P) − β₂(Q_x − Q_y, P)` for the linear form `T` and the
bilinear forms `β₁`, `β₂` built from these difference quotients, and the coordinate bounds give
`|T(P)| + |β₁(Q_x, P)| + |β₂(Q_x − Q_y, P)| ≤ M ‖x − y‖^α ‖P‖`. -/
theorem dohr_eb_lhr_dqub_forcing_holder : ∀ (n ℓ : ℕ) (α : ℝ) (U : Set (Rn n)) (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Φ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (v : Rn n → Rn ℓ) (xb e : Rn n) (R : ℝ), IsOpen U → 0 < R → closedBall xb (4 * R) ⊆ U → ‖e‖ ≤ 1 → (∀ P Q : Rn n →L[ℝ] Rn ℓ, ContDiffOn ℝ 1 (fun x => a x P Q) U ∧ ∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ 1 (fun z => a z P Q) x - iteratedFDeriv ℝ 1 (fun z => a z P Q) y‖ ≤ C * ‖x - y‖ ^ α) → (∀ P : Rn n →L[ℝ] Rn ℓ, ContDiffOn ℝ 1 (fun x => Φ x P) U ∧ ∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ 1 (fun z => Φ z P) x - iteratedFDeriv ℝ 1 (fun z => Φ z P) y‖ ≤ C * ‖x - y‖ ^ α) → IsLocallyHolderCkα 1 α v U → ∃ M : ℝ, ∀ d : ℝ, d ≠ 0 → |d| < R → ∀ x ∈ ball xb (2 * R), ∀ y ∈ ball xb (2 * R), ∀ P : Rn n →L[ℝ] Rn ℓ, |(d⁻¹ * (Φ (x + d • e) P - Φ x P) - d⁻¹ * (a (x + d • e) (fderiv ℝ v (x + d • e)) P - a x (fderiv ℝ v (x + d • e)) P)) - (d⁻¹ * (Φ (y + d • e) P - Φ y P) - d⁻¹ * (a (y + d • e) (fderiv ℝ v (y + d • e)) P - a y (fderiv ℝ v (y + d • e)) P))| ≤ M * ‖x - y‖ ^ α * ‖P‖ := by
  intro n ℓ α U a Φ v xb e R hU hR hK0U he ha hΦ hv
  -- Step 1: a spanning family `b` of `L` and the coordinate constant `C`.
  obtain ⟨N, b, C, hC, hD1, hD2⟩ :=
    Submission.dohr_eb_lhr_dqub_form_coords (Rn n →L[ℝ] Rn ℓ)
  -- Step 2: derivative bounds and Hölder constants of the components on `K₀ = B_{4R}(xb)`.
  have hK0c : IsCompact (closedBall xb (4 * R)) := isCompact_closedBall xb (4 * R)
  have hAa : ∀ r t : Fin N, ∃ S H : ℝ, 0 ≤ S ∧ 0 ≤ H ∧
      (∀ z ∈ closedBall xb (4 * R), ‖fderiv ℝ (fun z => a z (b r) (b t)) z‖ ≤ S) ∧
      ∀ z ∈ closedBall xb (4 * R), ∀ w ∈ closedBall xb (4 * R),
        ‖fderiv ℝ (fun z => a z (b r) (b t)) z - fderiv ℝ (fun z => a z (b r) (b t)) w‖ ≤
          H * ‖z - w‖ ^ α := fun r t =>
    Submission.dohr_eb_lhr_dqub_fderiv_consts (Rn n) ℝ α U _ (fun z => a z (b r) (b t)) hU hK0c
      hK0U (ha (b r) (b t)).1 ((ha (b r) (b t)).2 _ hK0c hK0U)
  have hAΦ : ∀ r : Fin N, ∃ S H : ℝ, 0 ≤ S ∧ 0 ≤ H ∧
      (∀ z ∈ closedBall xb (4 * R), ‖fderiv ℝ (fun z => Φ z (b r)) z‖ ≤ S) ∧
      ∀ z ∈ closedBall xb (4 * R), ∀ w ∈ closedBall xb (4 * R),
        ‖fderiv ℝ (fun z => Φ z (b r)) z - fderiv ℝ (fun z => Φ z (b r)) w‖ ≤
          H * ‖z - w‖ ^ α := fun r =>
    Submission.dohr_eb_lhr_dqub_fderiv_consts (Rn n) ℝ α U _ (fun z => Φ z (b r)) hU hK0c
      hK0U (hΦ (b r)).1 ((hΦ (b r)).2 _ hK0c hK0U)
  obtain ⟨Sv, Hv, hSv0, hHv0, hSv, hHv⟩ :=
    Submission.dohr_eb_lhr_dqub_fderiv_consts (Rn n) (Rn ℓ) α U _ v hU hK0c hK0U
      (by simpa using hv.1) (hv.2 _ hK0c hK0U)
  choose Sa Ha hSa0 hHa0 hSa hHa using hAa
  choose SΦ HΦ hSΦ0 hHΦ0 hSΦ hHΦ using hAΦ
  -- Step 3: uniform constants `S'`, `H` for all components; `M` is fixed before `d`.
  set S' : ℝ := ∑ r, ∑ t, Sa r t + ∑ r, SΦ r
  set H : ℝ := ∑ r, ∑ t, Ha r t + ∑ r, HΦ r
  have hSa_sum0 : 0 ≤ ∑ r, ∑ t, Sa r t :=
    Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun t _ => hSa0 r t
  have hHa_sum0 : 0 ≤ ∑ r, ∑ t, Ha r t :=
    Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun t _ => hHa0 r t
  have hSΦ_sum0 : 0 ≤ ∑ r, SΦ r := Finset.sum_nonneg fun r _ => hSΦ0 r
  have hHΦ_sum0 : 0 ≤ ∑ r, HΦ r := Finset.sum_nonneg fun r _ => hHΦ0 r
  have hS'0 : 0 ≤ S' := add_nonneg hSa_sum0 hSΦ_sum0
  have hH0 : 0 ≤ H := add_nonneg hHa_sum0 hHΦ_sum0
  have hSa_le : ∀ r t, Sa r t ≤ S' := fun r t =>
    le_trans (Finset.single_le_sum (fun t _ => hSa0 r t) (Finset.mem_univ t))
      (le_trans (Finset.single_le_sum (f := fun r => ∑ t, Sa r t)
        (fun r _ => Finset.sum_nonneg fun t _ => hSa0 r t) (Finset.mem_univ r))
        (le_add_of_nonneg_right hSΦ_sum0))
  have hHa_le : ∀ r t, Ha r t ≤ H := fun r t =>
    le_trans (Finset.single_le_sum (fun t _ => hHa0 r t) (Finset.mem_univ t))
      (le_trans (Finset.single_le_sum (f := fun r => ∑ t, Ha r t)
        (fun r _ => Finset.sum_nonneg fun t _ => hHa0 r t) (Finset.mem_univ r))
        (le_add_of_nonneg_right hHΦ_sum0))
  have hSΦ_le : ∀ r, SΦ r ≤ S' := fun r =>
    le_trans (Finset.single_le_sum (fun r _ => hSΦ0 r) (Finset.mem_univ r))
      (le_add_of_nonneg_left hSa_sum0)
  have hHΦ_le : ∀ r, HΦ r ≤ H := fun r =>
    le_trans (Finset.single_le_sum (fun r _ => hHΦ0 r) (Finset.mem_univ r))
      (le_add_of_nonneg_left hHa_sum0)
  refine ⟨C * (H + H * Sv + S' * Hv), ?_⟩
  intro d hd hdR x hx y hy P
  -- Step 4: `x + d e, y + d e ∈ K₀`, and the bounds on `Q_x = Dv(x + d e)`, `Q_y = Dv(y + d e)`.
  have hshift : ∀ z ∈ ball xb (2 * R), z + d • e ∈ closedBall xb (4 * R) := by
    intro z hz
    rw [mem_closedBall]
    rw [mem_ball] at hz
    have h1 : dist (z + d • e) xb ≤ dist z xb + ‖d • e‖ := by
      rw [dist_eq_norm, dist_eq_norm]
      calc ‖z + d • e - xb‖ = ‖(z - xb) + d • e‖ := by congr 1; abel
        _ ≤ ‖z - xb‖ + ‖d • e‖ := norm_add_le _ _
    have h2 : ‖d • e‖ ≤ R := by
      rw [norm_smul, Real.norm_eq_abs]
      calc |d| * ‖e‖ ≤ |d| * 1 := mul_le_mul_of_nonneg_left he (abs_nonneg d)
        _ ≤ R := by linarith
    linarith
  have hxK := hshift x hx
  have hyK := hshift y hy
  set t : ℝ := ‖x - y‖ ^ α
  have ht0 : 0 ≤ t := Real.rpow_nonneg (norm_nonneg _) α
  set Qx := fderiv ℝ v (x + d • e)
  set Qy := fderiv ℝ v (y + d • e)
  have hQxb : ‖Qx‖ ≤ Sv := hSv _ hxK
  have hQxy : ‖Qx - Qy‖ ≤ Hv * t := by
    have := hHv _ hxK _ hyK
    rwa [add_sub_add_right_eq_sub] at this
  -- Step 5: the scalar difference quotients of the components, by the mean value inequality
  -- `dohr_eb_lhr_dqub_dq_mean_value` with the common constants `S'` and `H`.
  have hBa : ∀ r t', |d⁻¹ * (a (y + d • e) (b r) (b t') - a y (b r) (b t'))| ≤ S' ∧
      |d⁻¹ * (a (x + d • e) (b r) (b t') - a x (b r) (b t')) -
        d⁻¹ * (a (y + d • e) (b r) (b t') - a y (b r) (b t'))| ≤ H * t := by
    intro r t'
    have hB := Submission.dohr_eb_lhr_dqub_dq_mean_value (Rn n) ℝ α U
      (fun z => a z (b r) (b t')) xb e R S' H d hU hK0U he
      ((ha (b r) (b t')).1.differentiableOn one_ne_zero)
      (fun z hz => (hSa r t' z hz).trans (hSa_le r t'))
      (fun z hz w hw => (hHa r t' z hz w hw).trans
        (mul_le_mul_of_nonneg_right (hHa_le r t') (Real.rpow_nonneg (norm_nonneg _) α)))
      hd hdR
    refine ⟨?_, ?_⟩
    · simpa [smul_eq_mul, Real.norm_eq_abs] using (hB y hy y hy).1
    · simpa [smul_eq_mul, Real.norm_eq_abs] using (hB x hx y hy).2
  have hBΦ : ∀ r, |d⁻¹ * (Φ (x + d • e) (b r) - Φ x (b r)) -
      d⁻¹ * (Φ (y + d • e) (b r) - Φ y (b r))| ≤ H * t := by
    intro r
    have hB := Submission.dohr_eb_lhr_dqub_dq_mean_value (Rn n) ℝ α U
      (fun z => Φ z (b r)) xb e R S' H d hU hK0U he
      ((hΦ (b r)).1.differentiableOn one_ne_zero)
      (fun z hz => (hSΦ r z hz).trans (hSΦ_le r))
      (fun z hz w hw => (hHΦ r z hz w hw).trans
        (mul_le_mul_of_nonneg_right (hHΦ_le r) (Real.rpow_nonneg (norm_nonneg _) α)))
      hd hdR
    simpa [smul_eq_mul, Real.norm_eq_abs] using (hB x hx y hy).2
  -- Step 6: the linear form `T` and the bilinear forms `β₁`, `β₂`.
  let T : (Rn n →L[ℝ] Rn ℓ) → ℝ := fun P' =>
    d⁻¹ * (Φ (x + d • e) P' - Φ x P') - d⁻¹ * (Φ (y + d • e) P' - Φ y P')
  let β1 : (Rn n →L[ℝ] Rn ℓ) → (Rn n →L[ℝ] Rn ℓ) → ℝ := fun Q P' =>
    d⁻¹ * (a (x + d • e) Q P' - a x Q P') - d⁻¹ * (a (y + d • e) Q P' - a y Q P')
  let β2 : (Rn n →L[ℝ] Rn ℓ) → (Rn n →L[ℝ] Rn ℓ) → ℝ := fun Q P' =>
    d⁻¹ * (a (y + d • e) Q P' - a y Q P')
  have hTlin : IsLinearMap ℝ T := by
    constructor
    · intro P1 P2; simp only [T, map_add]; ring
    · intro c P1; simp only [T, map_smul, smul_eq_mul]; ring
  have hβ1l : ∀ P', IsLinearMap ℝ (fun Q => β1 Q P') := by
    intro P'; constructor
    · intro Q1 Q2; simp only [β1, map_add, add_apply]; ring
    · intro c Q1; simp only [β1, map_smul, smul_apply, smul_eq_mul]; ring
  have hβ1r : ∀ Q, IsLinearMap ℝ (β1 Q) := by
    intro Q; constructor
    · intro P1 P2; simp only [β1, map_add]; ring
    · intro c P1; simp only [β1, map_smul, smul_eq_mul]; ring
  have hβ2l : ∀ P', IsLinearMap ℝ (fun Q => β2 Q P') := by
    intro P'; constructor
    · intro Q1 Q2; simp only [β2, map_add, add_apply]; ring
    · intro c Q1; simp only [β2, map_smul, smul_apply, smul_eq_mul]; ring
  have hβ2r : ∀ Q, IsLinearMap ℝ (β2 Q) := by
    intro Q; constructor
    · intro P1 P2; simp only [β2, map_add]; ring
    · intro c P1; simp only [β2, map_smul, smul_eq_mul]; ring
  -- Step 7: coordinate bounds for `T(P)`, `β₁(Q_x, P)` and `β₂(Q_x − Q_y, P)`.
  have hT : |T P| ≤ C * (H * t) * ‖P‖ :=
    hD1 T (H * t) hTlin (mul_nonneg hH0 ht0) (fun r => hBΦ r) P
  have hβ1 : |β1 Qx P| ≤ C * (H * t) * ‖Qx‖ * ‖P‖ :=
    hD2 β1 (H * t) hβ1l hβ1r (mul_nonneg hH0 ht0) (fun r t' => (hBa r t').2) Qx P
  have hβ2 : |β2 (Qx - Qy) P| ≤ C * S' * ‖Qx - Qy‖ * ‖P‖ :=
    hD2 β2 S' hβ2l hβ2r hS'0 (fun r t' => (hBa r t').1) (Qx - Qy) P
  -- Step 8: `F_d(x, P) − F_d(y, P) = T(P) − β₁(Q_x, P) − β₂(Q_x − Q_y, P)`.
  have hid : (d⁻¹ * (Φ (x + d • e) P - Φ x P) - d⁻¹ * (a (x + d • e) Qx P - a x Qx P)) -
      (d⁻¹ * (Φ (y + d • e) P - Φ y P) - d⁻¹ * (a (y + d • e) Qy P - a y Qy P)) =
      T P - β1 Qx P - β2 (Qx - Qy) P := by
    simp only [T, β1, β2, map_sub, sub_apply]; ring
  -- Step 9: the triangle inequality.
  rw [hid]
  have hP0 : 0 ≤ ‖P‖ := norm_nonneg P
  have hCH : 0 ≤ C * (H * t) := mul_nonneg hC (mul_nonneg hH0 ht0)
  have hCS : 0 ≤ C * S' := mul_nonneg hC hS'0
  have e1 : |β1 Qx P| ≤ C * (H * t) * Sv * ‖P‖ :=
    hβ1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQxb hCH) hP0)
  have e2 : |β2 (Qx - Qy) P| ≤ C * S' * (Hv * t) * ‖P‖ :=
    hβ2.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQxy hCS) hP0)
  calc |T P - β1 Qx P - β2 (Qx - Qy) P|
      ≤ |T P - β1 Qx P| + |β2 (Qx - Qy) P| := abs_sub _ _
    _ ≤ |T P| + |β1 Qx P| + |β2 (Qx - Qy) P| := by
        gcongr; exact abs_sub _ _
    _ ≤ C * (H * t) * ‖P‖ + C * (H * t) * Sv * ‖P‖ + C * S' * (Hv * t) * ‖P‖ := by
        gcongr
    _ = C * (H + H * Sv + S' * Hv) * t * ‖P‖ := by ring
/-- Difference-quotient step in the proof of Simon Ch. 5, Theorem 7.1, second assertion (p. 127):
`d`-uniform bounds for `w_d = d⁻¹ (v(· + d e) - v)` and for the forcing term `F_d` of its system on
`B̆_{2R}(xb)`.  Claims (i)–(iv) hold with the `d`-independent bound `S` of
`dohr_eb_lhr_dqub_wd_props`, claim (v) with the `d`-independent constant `M'` of
`dohr_eb_lhr_dqub_forcing_holder`; `M := max S M'` serves both, as `‖x - y‖ ^ α * ‖P‖ ≥ 0`. -/
theorem dohr_eb_lhr_dq_uniform_bounds : ∀ (n ℓ : ℕ) (α : ℝ) (U : Set (Rn n)) (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Φ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (v : Rn n → Rn ℓ) (xb e : Rn n) (R : ℝ), 0 < α → α ≤ 1 → IsOpen U → 0 < R → closedBall xb (4 * R) ⊆ U → ‖e‖ ≤ 1 → (∀ P Q : Rn n →L[ℝ] Rn ℓ, ContDiffOn ℝ 1 (fun x => a x P Q) U ∧ ∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ 1 (fun z => a z P Q) x - iteratedFDeriv ℝ 1 (fun z => a z P Q) y‖ ≤ C * ‖x - y‖ ^ α) → (∀ P : Rn n →L[ℝ] Rn ℓ, ContDiffOn ℝ 1 (fun x => Φ x P) U ∧ ∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ 1 (fun z => Φ z P) x - iteratedFDeriv ℝ 1 (fun z => Φ z P) y‖ ≤ C * ‖x - y‖ ^ α) → IsLocallyHolderCkα 1 α v U → ∃ M : ℝ, ∀ d : ℝ, d ≠ 0 → |d| < R → (∀ x ∈ ball xb (2 * R), ‖d⁻¹ • (v (x + d • e) - v x)‖ ≤ M) ∧ ContDiffOn ℝ 1 (fun z => d⁻¹ • (v (z + d • e) - v z)) (ball xb (2 * R)) ∧ (∀ x ∈ ball xb (2 * R), fderiv ℝ (fun z => d⁻¹ • (v (z + d • e) - v z)) x = d⁻¹ • (fderiv ℝ v (x + d • e) - fderiv ℝ v x)) ∧ (∃ K : ℝ, ∀ x ∈ ball xb (2 * R), ∀ y ∈ ball xb (2 * R), ‖fderiv ℝ (fun z => d⁻¹ • (v (z + d • e) - v z)) x - fderiv ℝ (fun z => d⁻¹ • (v (z + d • e) - v z)) y‖ ≤ K * ‖x - y‖ ^ α) ∧ ∀ x ∈ ball xb (2 * R), ∀ y ∈ ball xb (2 * R), ∀ P : Rn n →L[ℝ] Rn ℓ, |(d⁻¹ * (Φ (x + d • e) P - Φ x P) - d⁻¹ * (a (x + d • e) (fderiv ℝ v (x + d • e)) P - a x (fderiv ℝ v (x + d • e)) P)) - (d⁻¹ * (Φ (y + d • e) P - Φ y P) - d⁻¹ * (a (y + d • e) (fderiv ℝ v (y + d • e)) P - a y (fderiv ℝ v (y + d • e)) P))| ≤ M * ‖x - y‖ ^ α * ‖P‖ := by
  intro n ℓ α U a Φ v xb e R _ _ hU hR hBU he ha hΦ hv
  -- Steps 6–8: `w_d` is bounded by `S`, `C¹`, has the stated derivative, and `Dw_d` is Hölder.
  obtain ⟨S, hS⟩ := Submission.dohr_eb_lhr_dqub_wd_props n ℓ α U v xb e R hU hR hBU he hv
  -- Step 9: the forcing term is `α`-Hölder in `x` with the constant `M'`.
  obtain ⟨M', hM'⟩ :=
    Submission.dohr_eb_lhr_dqub_forcing_holder n ℓ α U a Φ v xb e R hU hR hBU he ha hΦ hv
  -- Step 10: `M := max S M'` does not depend on `d`.
  refine ⟨max S M', fun d hd hdR => ?_⟩
  obtain ⟨hw, hC1, hDw, hHol⟩ := hS d hd hdR
  refine ⟨fun x hx => (hw x hx).trans (le_max_left S M'), hC1, hDw, hHol,
    fun x hx y hy P => (hM' d hd hdR x hx y hy P).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right S M')
    (Real.rpow_nonneg (norm_nonneg (x - y)) α)) (norm_nonneg P)
/-- **Simon Ch. 5, proof of Theorem 7.1 (elliptic bootstrap): difference quotients of a `C¹` map
into a normed space.**
If `g : ℝⁿ → E` is `C¹` on an open `U` and `K ⊆ U` is compact, then for every direction `e` the
difference quotients `d⁻¹ (g(x + d e) − g(x))` converge to `Dg(x) e` uniformly on `K` as `d → 0`,
`d ≠ 0`.  The codomain `E` is an arbitrary real normed space (e.g. `L(ℝⁿ, ℝ^ℓ)` for `g = Dv`).
Proof: `K` has a compact closed thickening `K_ε ⊆ U`, on which `Dg` is uniformly continuous
(Heine–Cantor).  Given `η > 0`, pick `θ > 0` with `‖Dg(w) − Dg(x)‖ < η/(|e| + 1)` whenever
`w, x ∈ K_ε` and `|w − x| < θ`.  For `0 < |d| < min(ε, θ)/(|e| + 1)` and `x ∈ K`, the segment
`[x, x + d e]` lies in `B_{|d e|}(x) ⊆ K_ε`, so the mean value inequality with the fixed linear map
`Dg(x)` gives `‖g(x + d e) − g(x) − Dg(x)(d e)‖ ≤ η |d| |e|/(|e| + 1)`; dividing by `|d|`,
`‖Dg(x) e − d⁻¹ (g(x + d e) − g(x))‖ ≤ η |e|/(|e| + 1) < η`. -/
theorem dohr_eb_lhr_ds_diffQuot_tendstoUniformlyOn : ∀ (n : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (g : Rn n → E) (U K : Set (Rn n)) (e : Rn n), IsOpen U → ContDiffOn ℝ 1 g U → IsCompact K → K ⊆ U → TendstoUniformlyOn (fun (d : ℝ) (x : Rn n) => d⁻¹ • (g (x + d • e) - g x)) (fun x => fderiv ℝ g x e) (𝓝[≠] 0) K := by
  intro n E _ _ g U K e hU hg hK hKU
  -- Step 1: a compact closed thickening `K_ε = cthickening ε K` of `K` inside `U`.
  obtain ⟨ε, hε, hεU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hK' : IsCompact (cthickening ε K) := hK.cthickening
  -- Step 2: `g` is differentiable on `U` and `Dg` is uniformly continuous on `K_ε`.
  have hcont : ContinuousOn (fderiv ℝ g) U := hg.continuousOn_fderiv_of_isOpen hU le_rfl
  have huc : UniformContinuousOn (fderiv ℝ g) (cthickening ε K) :=
    hK'.uniformContinuousOn_of_continuous (hcont.mono hεU)
  have hdiff : ∀ z ∈ U, DifferentiableAt ℝ g z := fun z hz =>
    (hg.differentiableOn one_ne_zero z hz).differentiableAt (hU.mem_nhds hz)
  -- Step 3: given `η > 0`, choose `θ` and restrict to `0 < |d| < min ε θ / (‖e‖ + 1)`.
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  rw [Metric.uniformContinuousOn_iff] at huc
  have he1 : 0 < ‖e‖ + 1 := by positivity
  obtain ⟨θ, hθ, hθK⟩ := huc (η / (‖e‖ + 1)) (div_pos hη he1)
  have hpos : 0 < min ε θ / (‖e‖ + 1) := div_pos (lt_min hε hθ) he1
  have hev : ∀ᶠ d in 𝓝[≠] (0 : ℝ), |d| < min ε θ / (‖e‖ + 1) := by
    apply nhdsWithin_le_nhds
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hpos] with d hd
    simpa [Real.dist_eq] using hd
  filter_upwards [hev, self_mem_nhdsWithin] with d hd hd0
  have hd0' : d ≠ 0 := hd0
  intro x hx
  -- Step 4: the segment `[x, x + d • e]` lies in `closedBall x ‖d • e‖ ⊆ K_ε ⊆ U`.
  have hde : ‖d • e‖ < min ε θ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |d| * ‖e‖ ≤ |d| * (‖e‖ + 1) := by gcongr; linarith
      _ < min ε θ / (‖e‖ + 1) * (‖e‖ + 1) := by gcongr
      _ = min ε θ := div_mul_cancel₀ _ he1.ne'
  have hball : closedBall x ‖d • e‖ ⊆ cthickening ε K :=
    (closedBall_subset_closedBall (hde.le.trans (min_le_left _ _))).trans
      (closedBall_subset_cthickening hx ε)
  have hxde : x + d • e ∈ closedBall x ‖d • e‖ := by
    rw [mem_closedBall, dist_eq_norm]; simp
  have hseg : segment ℝ x (x + d • e) ⊆ closedBall x ‖d • e‖ :=
    (convex_closedBall x _).segment_subset (mem_closedBall_self (norm_nonneg _)) hxde
  have hxK' : x ∈ cthickening ε K := self_subset_cthickening K hx
  -- Step 5: the mean value inequality with the fixed linear map `Dg(x)`.
  have hmvt : ‖g (x + d • e) - g x - fderiv ℝ g x ((x + d • e) - x)‖ ≤
      η / (‖e‖ + 1) * ‖(x + d • e) - x‖ := by
    refine (convex_segment x (x + d • e)).norm_image_sub_le_of_norm_fderiv_le'
      (fun w hw => hdiff w (hεU (hball (hseg hw)))) (fun w hw => ?_) (left_mem_segment ℝ _ _)
      (right_mem_segment ℝ _ _)
    have hw := hseg hw
    have hwx : dist w x < θ := by
      rw [mem_closedBall] at hw
      exact hw.trans_lt (hde.trans_le (min_le_right _ _))
    have := hθK w (hball hw) x hxK' hwx
    rw [dist_eq_norm] at this
    exact this.le
  have hsub : (x + d • e) - x = d • e := by abel
  rw [hsub] at hmvt
  -- Step 6: divide by `d ≠ 0`.
  rw [dist_eq_norm]
  have hrw : fderiv ℝ g x e - d⁻¹ • (g (x + d • e) - g x) =
      -(d⁻¹ • (g (x + d • e) - g x - fderiv ℝ g x (d • e))) := by
    rw [map_smul, smul_sub d⁻¹ (g (x + d • e) - g x) (d • fderiv ℝ g x e), smul_smul,
      inv_mul_cancel₀ hd0', one_smul]; abel
  rw [hrw, norm_neg, norm_smul, norm_inv, Real.norm_eq_abs]
  calc |d|⁻¹ * ‖g (x + d • e) - g x - fderiv ℝ g x (d • e)‖
      ≤ |d|⁻¹ * (η / (‖e‖ + 1) * ‖d • e‖) := by gcongr
    _ = η * (‖e‖ / (‖e‖ + 1)) := by
      rw [norm_smul, Real.norm_eq_abs]; field_simp
    _ < η * 1 := by
      gcongr
      rw [div_lt_one he1]; linarith
    _ = η := mul_one η
/-- **Simon Ch. 5, proof of Theorem 7.1 (elliptic bootstrap): the derivative of a directional
derivative of a `C²` map.**
If `v : ℝⁿ → ℝ^ℓ` is `C²` on an open `U` and `e ∈ ℝⁿ`, then at every `x ∈ U` the directional
derivative `v_e(z) = Dv(z) e` has derivative `D(v_e)(x) = D(Dv)(x) e` (symmetry of the second
derivative, proved here by difference quotients since `FDeriv.Symmetric` is not imported).
Proof: choose `r > 0` with `B_r(x) ⊆ U`.  By `dohr_eb_lhr_ds_diffQuot_tendstoUniformlyOn` for the
`C¹` map `Dv`, `T_d = d⁻¹ (Dv(· + d e) − Dv) → D(Dv)(·) e` uniformly on `B_r(x)` as `d → 0`,
`d ≠ 0`.  For `|d| < (r/2)/(‖e‖ + 1)` and `z ∈ B̆_{r/2}(x)` the points `z`, `z + d e` lie in `U`, so
`w_d = d⁻¹ (v(· + d e) − v)` has derivative `T_d(z)` at `z`.  For `y ∈ U`, `w_d(y) → Dv(y) e` (slope
of `t ↦ v(y + t e)` at `0`).  The theorem on uniform limits of derivatives
(`hasFDerivAt_of_tendstoUniformlyOnFilter`) gives `D(v_e)(x) = D(Dv)(x) e`. -/
theorem dohr_eb_lhr_ds_fderiv_dirDeriv_eq : ∀ (n ℓ : ℕ) (U : Set (Rn n)) (v : Rn n → Rn ℓ) (e : Rn n), IsOpen U → ContDiffOn ℝ 2 v U → ∀ x ∈ U, fderiv ℝ (fun z => fderiv ℝ v z e) x = fderiv ℝ (fderiv ℝ v) x e := by
  intro n ℓ U v e hU hv x hx
  -- Step 1: a closed ball `B_r(x) ⊆ U`; `v` is differentiable on `U` and `Dv` is `C¹` on `U`.
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  have hdiff : ∀ z ∈ U, DifferentiableAt ℝ v z := fun z hz =>
    (hv.differentiableOn two_ne_zero z hz).differentiableAt (hU.mem_nhds hz)
  have hDv : ContDiffOn ℝ 1 (fderiv ℝ v) U := hv.fderiv_of_isOpen hU (by norm_num)
  -- Steps 2–3: `T_d → D(Dv)(·) e` uniformly on `B_r(x)`, hence uniformly on the filter `𝓝 x`.
  have hunif : TendstoUniformlyOn
      (fun (d : ℝ) (z : Rn n) => d⁻¹ • (fderiv ℝ v (z + d • e) - fderiv ℝ v z))
      (fun z => fderiv ℝ (fderiv ℝ v) z e) (𝓝[≠] 0) (closedBall x r) :=
    Submission.dohr_eb_lhr_ds_diffQuot_tendstoUniformlyOn n (Rn n →L[ℝ] Rn ℓ) (fderiv ℝ v) U
      (closedBall x r) e hU hDv (isCompact_closedBall x r) hrU
  have hunif' : TendstoUniformlyOnFilter
      (fun (d : ℝ) (z : Rn n) => d⁻¹ • (fderiv ℝ v (z + d • e) - fderiv ℝ v z))
      (fun z => fderiv ℝ (fderiv ℝ v) z e) (𝓝[≠] 0) (𝓝 x) :=
    hunif.tendstoUniformlyOnFilter.mono_right (le_principal_iff.mpr (closedBall_mem_nhds x hr))
  -- Step 4: `w_d` has derivative `T_d(z)` at `z` for `|d| < (r/2)/(‖e‖ + 1)`, `z ∈ B̆_{r/2}(x)`.
  have he1 : 0 < ‖e‖ + 1 := by positivity
  have hρ : 0 < r / 2 / (‖e‖ + 1) := by positivity
  have hdev : ∀ᶠ d in 𝓝[≠] (0 : ℝ), |d| < r / 2 / (‖e‖ + 1) := by
    apply nhdsWithin_le_nhds
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hρ] with d hd
    simpa [Real.dist_eq] using hd
  have hzev : ∀ᶠ z in 𝓝 x, z ∈ ball x (r / 2) := Metric.ball_mem_nhds x (half_pos hr)
  have hderiv : ∀ᶠ p : ℝ × Rn n in 𝓝[≠] 0 ×ˢ 𝓝 x,
      HasFDerivAt (fun z => p.1⁻¹ • (v (z + p.1 • e) - v z))
        (p.1⁻¹ • (fderiv ℝ v (p.2 + p.1 • e) - fderiv ℝ v p.2)) p.2 := by
    filter_upwards [hdev.prod_mk hzev] with p hp
    obtain ⟨d, z⟩ := p
    obtain ⟨hd, hz⟩ := hp
    have hzr : dist z x < r / 2 := hz
    have hzU : z ∈ U := hrU (mem_closedBall.mpr (hzr.le.trans (half_le_self hr.le)))
    have hde : ‖d • e‖ < r / 2 := by
      rw [norm_smul, Real.norm_eq_abs]
      calc |d| * ‖e‖ ≤ |d| * (‖e‖ + 1) := by gcongr; linarith
        _ < r / 2 / (‖e‖ + 1) * (‖e‖ + 1) := by gcongr
        _ = r / 2 := div_mul_cancel₀ _ he1.ne'
    have hzdU : z + d • e ∈ U := by
      refine hrU (mem_closedBall.mpr ?_)
      calc dist (z + d • e) x = ‖(z - x) + d • e‖ := by rw [dist_eq_norm, add_sub_right_comm]
        _ ≤ ‖z - x‖ + ‖d • e‖ := norm_add_le _ _
        _ ≤ r := by rw [← dist_eq_norm]; linarith
    -- chain rule for the translation `z ↦ z + d e`, then difference and constant multiple rules
    have htr : HasFDerivAt (fun z => v (z + d • e)) (fderiv ℝ v (z + d • e)) z :=
      (hasFDerivAt_comp_add_right (d • e)).mpr (hdiff _ hzdU).hasFDerivAt
    exact (htr.sub (hdiff z hzU).hasFDerivAt).const_smul d⁻¹
  -- Step 5: `w_d(y) → Dv(y) e` for every `y ∈ U`: slopes of `t ↦ v(y + t e)` at `t = 0`.
  have hpt : ∀ᶠ y in 𝓝 x,
      Tendsto (fun d : ℝ => d⁻¹ • (v (y + d • e) - v y)) (𝓝[≠] 0) (𝓝 (fderiv ℝ v y e)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    have hline : HasDerivAt (fun t : ℝ => y + t • e) e 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add y
    have hvy : HasFDerivAt v (fderiv ℝ v y) (y + (0 : ℝ) • e) := by
      rw [zero_smul, add_zero]
      exact (hdiff y hy).hasFDerivAt
    have hcomp : HasDerivAt (fun t : ℝ => v (y + t • e)) (fderiv ℝ v y e) 0 :=
      hvy.comp_hasDerivAt (0 : ℝ) hline
    simpa using hcomp.tendsto_slope_zero
  -- Step 6: uniform limits of derivatives (`f d = w_d`, `f' d = T_d`, `g = v_e`).
  exact (hasFDerivAt_of_tendstoUniformlyOnFilter
    (f := fun (d : ℝ) (z : Rn n) => d⁻¹ • (v (z + d • e) - v z))
    (f' := fun (d : ℝ) (z : Rn n) => d⁻¹ • (fderiv ℝ v (z + d • e) - fderiv ℝ v z))
    (g := fun z => fderiv ℝ v z e) (g' := fun z => fderiv ℝ (fderiv ℝ v) z e)
    hunif' hderiv hpt).fderiv
/-- **Simon Ch. 5, proof of Theorem 7.1 (elliptic bootstrap): families of linear forms.**
Let `L = L(ℝⁿ, ℝ^ℓ)` and let `Φ : ℝⁿ → L* = L(L, ℝ)` be such that `x ↦ Φ(x)[P]` is `C¹` on an
open `U` for every `P ∈ L`.  Then `Φ` is `C¹` on `U` as an `L*`-valued map, and
`(DΦ(x) e)[P] = D(Φ(·)[P])(x) e` for all `x ∈ U`, `e ∈ ℝⁿ` and `P ∈ L`.
Proof: `L` is finite-dimensional; with a basis `E_r` of `L` and its continuous coordinate forms
`π_r`, linearity gives `Φ(x)[P] = Σ_r π_r(P) Φ(x)[E_r]`, so `Φ(x) = Σ_r Φ(x)[E_r] π_r` is a finite
sum of the constant forms `π_r` times `C¹` scalar functions, and `Φ` is `C¹` on `U`.  For `x ∈ U`,
`Φ` is differentiable at `x`, and the product rule for evaluation at the constant `P` gives
`D(Φ(·)[P])(x) = (DΦ(x)).flip P`. -/
theorem dohr_eb_lhr_ds_clm_family : ∀ (n ℓ : ℕ) (U : Set (Rn n)) (Φ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ), IsOpen U → (∀ P : Rn n →L[ℝ] Rn ℓ, ContDiffOn ℝ 1 (fun x => Φ x P) U) → ContDiffOn ℝ 1 Φ U ∧ ∀ x ∈ U, ∀ (e : Rn n) (P : Rn n →L[ℝ] Rn ℓ), fderiv ℝ Φ x e P = fderiv ℝ (fun z => Φ z P) x e := by
  intro n ℓ U Φ hU hΦ
  -- Step 1: a basis `b` of `L` and its continuous coordinate forms `π r`.
  let b := Module.finBasis ℝ (Rn n →L[ℝ] Rn ℓ)
  let π : Fin (Module.finrank ℝ (Rn n →L[ℝ] Rn ℓ)) → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ :=
    fun r => LinearMap.toContinuousLinearMap (b.coord r)
  -- Step 2: `Φ(x) = Σ_r Φ(x)[b r] π r` in `L*`, by linearity of `Φ(x)`; the summand is written
  -- `(π r).smulRight (Φ x (b r)) : P ↦ π r P • Φ x (b r)`, so no scalar action on `L*` is needed.
  have hexp : ∀ x, Φ x = ∑ r, (π r).smulRight (Φ x (b r)) := by
    intro x
    ext P
    have hP : Φ x P = Φ x (∑ r, b.repr P r • b r) := by rw [b.sum_repr]
    rw [hP, map_sum]
    simp [map_smul, π]
  -- Step 3: each summand is `C¹` (constant form, `C¹` coefficient), hence so are the sum and `Φ`.
  have hC1 : ContDiffOn ℝ 1 Φ U := by
    have h : ContDiffOn ℝ 1 (fun x => ∑ r, (π r).smulRight (Φ x (b r))) U :=
      ContDiffOn.sum fun r _ => contDiffOn_const.smulRight (hΦ (b r))
    exact h.congr fun x _ => hexp x
  refine ⟨hC1, fun x hx e P => ?_⟩
  -- Step 4: differentiate the evaluation `z ↦ Φ(z)[P]` at the constant `P`.
  have hd : DifferentiableAt ℝ Φ x :=
    (hC1.differentiableOn one_ne_zero x hx).differentiableAt (hU.mem_nhds hx)
  rw [fderiv_clm_apply hd (differentiableAt_const P)]
  simp
/-- **Simon Ch. 5, proof of Theorem 7.1 (elliptic bootstrap): Leibniz rule for a family of bilinear
forms.**
Let `L = L(ℝⁿ, ℝ^ℓ)`, let `a : ℝⁿ → L(L, L*)` be such that `x ↦ a(x)[P][Q]` is `C¹` on an open `U`
for all `P, Q ∈ L`, and let `w : ℝⁿ → L` be `C¹` on `U`.  Then `x ↦ a(x)[w(x)]` is `C¹` on `U` as an
`L*`-valued map, and for `x ∈ U`, `P ∈ L` and `e ∈ ℝⁿ`,
`(D(a(·)[w(·)])(x) e)[P] = a(x)[Dw(x) e][P] + D(a(·)[w(x)][P])(x) e`, with `w(x)` frozen in the
last term.
Proof: with a basis `E_r` of `L` and its continuous coordinate forms `π_r`, linearity gives
`a(z)[Q][P] = Σ_r π_r(Q) · a(z)[E_r][P]`.  So each evaluation `z ↦ a(z)[w(z)][P]` is a finite sum of
products of `C¹` functions, and `dohr_eb_lhr_ds_clm_family` makes `z ↦ a(z)[w(z)]` a `C¹` map
with `(D(a(·)[w(·)])(x) e)[P] = D(a(·)[w(·)][P])(x) e`.  The product and sum rules give
`D(a(·)[w(·)][P])(x) e = Σ_r π_r(w(x)) · D(a(·)[E_r][P])(x) e + Σ_r π_r(Dw(x) e) · a(x)[E_r][P]`;
by the expansion the second sum is `a(x)[Dw(x) e][P]`, and the first is `D(a(·)[w(x)][P])(x) e`. -/
theorem dohr_eb_lhr_ds_bilin_leibniz : ∀ (n ℓ : ℕ) (U : Set (Rn n)) (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (w : Rn n → (Rn n →L[ℝ] Rn ℓ)) (e : Rn n), IsOpen U → (∀ P Q : Rn n →L[ℝ] Rn ℓ, ContDiffOn ℝ 1 (fun x => a x P Q) U) → ContDiffOn ℝ 1 w U → ContDiffOn ℝ 1 (fun x => a x (w x)) U ∧ ∀ x ∈ U, ∀ P : Rn n →L[ℝ] Rn ℓ, fderiv ℝ (fun z => a z (w z)) x e P = a x (fderiv ℝ w x e) P + fderiv ℝ (fun z => a z (w x) P) x e := by
  intro n ℓ U a w e hU ha hw
  -- Step 1: a basis `E_r = b r` of `L` with continuous coordinate forms `π r`, and the expansion
  -- `a(z)[Q][P] = Σ_r π_r(Q) · a(z)[E_r][P]`.
  let b := Module.finBasis ℝ (Rn n →L[ℝ] Rn ℓ)
  let π : Fin (Module.finrank ℝ (Rn n →L[ℝ] Rn ℓ)) → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ :=
    fun r => LinearMap.toContinuousLinearMap (b.coord r)
  have hexp : ∀ z Q P, a z Q P = ∑ r, π r Q * a z (b r) P := by
    intro z Q P
    have hQ : a z Q = a z (∑ r, b.repr Q r • b r) := by rw [b.sum_repr]
    rw [hQ, map_sum, sum_apply]
    simp only [map_smul, smul_apply, smul_eq_mul]
    rfl
  -- Step 2: each evaluation `z ↦ a(z)[w(z)][P] = Σ_r π_r(w(z)) · a(z)[E_r][P]` is `C¹` on `U`, so
  -- `clm_family` makes `z ↦ a(z)[w(z)]` a `C¹` map into `L*` and reduces the derivative identity
  -- to the evaluation at `P`.
  have hπw : ∀ r, ContDiffOn ℝ 1 (fun z => π r (w z)) U := fun r =>
    (π r).contDiff.comp_contDiffOn hw
  have hC1P : ∀ P, ContDiffOn ℝ 1 (fun z => a z (w z) P) U := fun P =>
    (ContDiffOn.sum fun r _ => (hπw r).mul (ha (b r) P)).congr fun z _ => hexp z (w z) P
  obtain ⟨hC1, hcf⟩ := Submission.dohr_eb_lhr_ds_clm_family n ℓ U (fun z => a z (w z)) hU hC1P
  refine ⟨hC1, fun x hx P => ?_⟩
  rw [hcf x hx e P]
  -- Step 3: product and sum rules for the expansion of `z ↦ a(z)[w(z)][P]`.
  have hxU : U ∈ 𝓝 x := hU.mem_nhds hx
  have hdw : HasFDerivAt w (fderiv ℝ w x) x :=
    ((hw.differentiableOn one_ne_zero x hx).differentiableAt hxU).hasFDerivAt
  have hdA : ∀ r, HasFDerivAt (fun z => a z (b r) P) (fderiv ℝ (fun z => a z (b r) P) x) x :=
    fun r => (((ha (b r) P).differentiableOn one_ne_zero x hx).differentiableAt hxU).hasFDerivAt
  have hD : HasFDerivAt (fun z => a z (w z) P)
      (∑ r, (π r (w x) • fderiv ℝ (fun z => a z (b r) P) x
        + a x (b r) P • (π r).comp (fderiv ℝ w x))) x := by
    rw [show (fun z => a z (w z) P) = fun z => ∑ r, π r (w z) * a z (b r) P from
      funext fun z => hexp z (w z) P]
    exact HasFDerivAt.fun_sum fun r _ => ((π r).hasFDerivAt.comp x hdw).mul (hdA r)
  -- Step 4: the derivative of `z ↦ a(z)[w(x)][P]`, with `w(x)` frozen.
  have hF : HasFDerivAt (fun z => a z (w x) P)
      (∑ r, π r (w x) • fderiv ℝ (fun z => a z (b r) P) x) x := by
    rw [show (fun z => a z (w x) P) = fun z => ∑ r, π r (w x) * a z (b r) P from
      funext fun z => hexp z (w x) P]
    exact HasFDerivAt.fun_sum fun r _ => (hdA r).const_mul (π r (w x))
  -- Step 5: by the expansion, the two sums are `a(x)[Dw(x) e][P]` and `D(a(·)[w(x)][P])(x) e`.
  rw [hD.fderiv, hF.fderiv, hexp x (fderiv ℝ w x e) P]
  simp only [sum_apply, add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
    Finset.sum_add_distrib, mul_comm (a x (b _) P)]
  ring
/-- Differentiated system in the linear higher-regularity step of the elliptic bootstrap for
Simon Ch. 5, Theorem 7.1, second assertion (p. 127): translating the test functions of a weak
identity.  If `∫_U ω₁(x)[Dφ(x)] dx = ∫_U ω₂(x)[Dφ(x)] dx` for every `C¹` compactly supported
`φ` with `spt φ ⊆ U`, and `ζ` is `C¹` with compact support and `spt ζ + s e ⊆ U`, then
`∫ ω₁(y + s e)[Dζ(y)] dy = ∫ ω₂(y + s e)[Dζ(y)] dy`.
Proof: test with `φ(x) = ζ(x − s e)`, which is `C¹` with compact support,
`spt φ = spt ζ + s e ⊆ U` and `Dφ(x) = Dζ(x − s e)`.  The integrands `ω_i(x)[Dφ(x)]` vanish off
`U`, so the integrals over `U` are whole-space integrals, and the substitution `x = y + s e`
(translation invariance of Lebesgue measure) turns them into `∫ ω_i(y + s e)[Dζ(y)] dy`.  No
integrability or measurability is needed. -/
theorem dohr_eb_lhr_ds_translate_weak_eq : ∀ (n ℓ : ℕ) (U : Set (Rn n)) (ω₁ ω₂ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (e : Rn n) (s : ℝ) (ζ : Rn n → Rn ℓ), (∀ φ : Rn n → Rn ℓ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ U → ∫ x in U, ω₁ x (fderiv ℝ φ x) = ∫ x in U, ω₂ x (fderiv ℝ φ x)) → ContDiff ℝ 1 ζ → HasCompactSupport ζ → (∀ y ∈ tsupport ζ, y + s • e ∈ U) → ∫ y, ω₁ (y + s • e) (fderiv ℝ ζ y) = ∫ y, ω₂ (y + s • e) (fderiv ℝ ζ y) := by
  intro n ℓ U ω₁ ω₂ e s ζ hweak hζ hζc hζU
  -- Step 1: the translated test function `φ = ζ ∘ τ`, `τ x = x − s e`, is `C¹` with compact
  -- support.
  let φ : Rn n → Rn ℓ := ζ ∘ Homeomorph.subRight (s • e)
  have hφC : ContDiff ℝ 1 φ := hζ.comp (contDiff_id.sub contDiff_const)
  have hφc : HasCompactSupport φ := hζc.comp_homeomorph _
  -- Step 2: `tsupport φ = τ⁻¹(tsupport ζ) ⊆ U`.
  have hφU : tsupport φ ⊆ U := by
    intro x hx
    rw [tsupport_comp_eq_preimage] at hx
    simpa using hζU _ hx
  -- Step 3: `Dφ(x) = Dζ(x − s e)`.
  have hDφ : ∀ x, fderiv ℝ φ x = fderiv ℝ ζ (x - s • e) := fun x =>
    fderiv_comp_sub (f := ζ) (s • e)
  -- Steps 4–5: the integrand vanishes off `U`, and `x = y + s e` turns the whole-space integral
  -- into the translated one.
  have key : ∀ ω : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ,
      ∫ x in U, ω x (fderiv ℝ φ x) = ∫ y, ω (y + s • e) (fderiv ℝ ζ y) := by
    intro ω
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · rw [← integral_add_right_eq_self (fun x => ω x (fderiv ℝ φ x)) (s • e)]
      congr 1
      funext y
      rw [hDφ, add_sub_cancel_right]
    · intro x hx
      have hx' : x - s • e ∉ tsupport ζ := fun h => hx (by simpa using hζU _ h)
      rw [hDφ, fderiv_of_notMem_tsupport ℝ hx', map_zero]
  -- Step 6: combine with the weak identity for `φ`.
  rw [← key ω₁, ← key ω₂]
  exact hweak φ hφC hφc hφU
/-- **Simon Ch. 5, proof of Theorem 7.1 (elliptic bootstrap): differentiating a weak identity.**
Let `ω₁, ω₂ : ℝⁿ → L*` (`L = L(ℝⁿ, ℝ^ℓ)`) be `C¹` on the open set `U` and satisfy
`∫_U ω₁[Dφ] = ∫_U ω₂[Dφ]` for every `φ ∈ C¹_c(U; ℝ^ℓ)`.  Then for every direction `e` and every
`ζ ∈ C¹_c(U; ℝ^ℓ)` the functions `F_i = (Dω_i e)[Dζ]` are integrable on `U` and
`∫_U F₁ = ∫_U F₂`.
Proof: `K = spt ζ` has a compact thickening `K₁ = cthickening δ K ⊆ U`, and `y + s e ∈ K₁` for
`y ∈ K`, `|s| < ε = δ/(|e| + 1)`.  The translated integrands `ω_i(y + s e)[Dζ(y)]` and
`(Dω_i(y + s e) e)[Dζ(y)]` are continuous with support in `K`.  By the translated weak identity
(`dohr_eb_lhr_ds_translate_weak_eq`), `I_i(s) = ∫ ω_i(y + s e)[Dζ(y)] dy` satisfy `I₁ = I₂` for
`|s| < ε`.  Differentiating under the integral sign, with the integrable bound `C_i |Dζ|` where
`C_i` bounds `|Dω_i(z) e|` on `K₁`, gives `I_i'(0) = ∫ F_i` and the integrability of `F_i`;
hence `∫ F₁ = ∫ F₂`.  The `F_i` vanish off `K ⊆ U`, so the integrals over `U` agree. -/
theorem dohr_eb_lhr_ds_weak_eq_fderiv : ∀ (n ℓ : ℕ) (U : Set (Rn n)) (ω₁ ω₂ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (e : Rn n), IsOpen U → ContDiffOn ℝ 1 ω₁ U → ContDiffOn ℝ 1 ω₂ U → (∀ φ : Rn n → Rn ℓ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ U → ∫ x in U, ω₁ x (fderiv ℝ φ x) = ∫ x in U, ω₂ x (fderiv ℝ φ x)) → ∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ U → IntegrableOn (fun x => fderiv ℝ ω₁ x e (fderiv ℝ ζ x)) U ∧ IntegrableOn (fun x => fderiv ℝ ω₂ x e (fderiv ℝ ζ x)) U ∧ ∫ x in U, fderiv ℝ ω₁ x e (fderiv ℝ ζ x) = ∫ x in U, fderiv ℝ ω₂ x e (fderiv ℝ ζ x) := by
  intro n ℓ U ω₁ ω₂ e hU hω₁ hω₂ hweak ζ hζ hζc hζU
  -- Step 1: a compact thickening `K₁ = cthickening δ K` of `K = tsupport ζ` inside `U`, and
  -- `ε = δ / (‖e‖ + 1)`, so that `y + s • e ∈ K₁` for `y ∈ K` and `|s| < ε`.
  have hK : IsCompact (tsupport ζ) := hζc
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hζU
  have hK₁ : IsCompact (cthickening δ (tsupport ζ)) := hK.cthickening
  have he1 : 0 < ‖e‖ + 1 := by positivity
  obtain ⟨ε, hε, hεδ⟩ : ∃ ε : ℝ, 0 < ε ∧ ε * (‖e‖ + 1) = δ :=
    ⟨δ / (‖e‖ + 1), div_pos hδ he1, div_mul_cancel₀ δ he1.ne'⟩
  have hmemK₁ : ∀ y ∈ tsupport ζ, ∀ s ∈ ball (0 : ℝ) ε,
      y + s • e ∈ cthickening δ (tsupport ζ) := by
    intro y hy s hs
    refine mem_cthickening_of_dist_le _ y δ _ hy ?_
    rw [mem_ball, Real.dist_eq, sub_zero] at hs
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, ← hεδ]
    exact mul_le_mul hs.le (by linarith) (norm_nonneg e) hε.le
  have hmemU : ∀ y ∈ tsupport ζ, ∀ s ∈ ball (0 : ℝ) ε, y + s • e ∈ U :=
    fun y hy s hs => hδU (hmemK₁ y hy s hs)
  -- `Dζ` is continuous, vanishes off `K`, and `‖Dζ‖` is integrable.
  have hDζc : Continuous (fderiv ℝ ζ) := hζ.continuous_fderiv one_ne_zero
  have hDζ0 : ∀ y, y ∉ tsupport ζ → fderiv ℝ ζ y = 0 := fun y hy => fderiv_of_notMem_tsupport ℝ hy
  have hDζint : Integrable (fun y => ‖fderiv ℝ ζ y‖) :=
    (hDζc.integrable_of_hasCompactSupport (hζc.fderiv ℝ)).norm
  -- Integrands `y ↦ G y (Dζ y)` are supported in `K`.
  have hsupp : ∀ G : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ,
      Function.support (fun y => G y (fderiv ℝ ζ y)) ⊆ tsupport ζ := by
    intro G y hy
    by_contra hyK
    exact hy (by simp only [hDζ0 y hyK, ContinuousLinearMap.map_zero])
  -- Step 3: for `|s| < ε` the translated integrands are continuous (with support in `K`).
  have hcont : ∀ s ∈ ball (0 : ℝ) ε, ∀ g : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ, ContinuousOn g U →
      Continuous (fun y => g (y + s • e) (fderiv ℝ ζ y)) := by
    intro s hs g hg
    have htr : Continuous (fun y : Rn n => y + s • e) := continuous_id.add continuous_const
    refine ContinuousOn.continuous_of_tsupport_subset (s := (fun y => y + s • e) ⁻¹' U)
      ((hg.comp htr.continuousOn (fun y hy => hy)).clm_apply hDζc.continuousOn)
      (hU.preimage htr) ?_
    exact (closure_minimal (hsupp (fun y => g (y + s • e))) (isClosed_tsupport ζ)).trans
      (fun y hy => hmemU y hy s hs)
  -- Steps 2 and 5, for a single `ω`: `I(s) = ∫ ω(y + s • e)[Dζ y] dy` has derivative
  -- `∫ (Dω(y) e)[Dζ y] dy` at `0`, and this integrand is integrable.
  have key : ∀ ω : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ, ContDiffOn ℝ 1 ω U →
      Integrable (fun y => fderiv ℝ ω y e (fderiv ℝ ζ y)) ∧
      HasDerivAt (fun s : ℝ => ∫ y, ω (y + s • e) (fderiv ℝ ζ y))
        (∫ y, fderiv ℝ ω y e (fderiv ℝ ζ y)) 0 := by
    intro ω hω
    -- Step 2: `ω` and `z ↦ Dω(z) e` are continuous on `U`; `‖Dω(z) e‖ ≤ C` on `K₁`.
    have hωc : ContinuousOn ω U := hω.continuousOn
    have hDωe : ContinuousOn (fun z => fderiv ℝ ω z e) U :=
      (hω.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
    obtain ⟨C, hC⟩ := hK₁.exists_bound_of_continuousOn (E := (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ)
      (hDωe.mono hδU)
    have hball : ball (0 : ℝ) ε ∈ 𝓝 (0 : ℝ) := ball_mem_nhds 0 hε
    have h0 : (0 : ℝ) ∈ ball (0 : ℝ) ε := mem_ball_self hε
    -- (a) the pointwise derivative in `s` (chain rule, then evaluation at the constant `Dζ y`)
    have hderiv : ∀ y : Rn n, ∀ s ∈ ball (0 : ℝ) ε,
        HasDerivAt (fun σ : ℝ => ω (y + σ • e) (fderiv ℝ ζ y))
          (fderiv ℝ ω (y + s • e) e (fderiv ℝ ζ y)) s := by
      intro y s hs
      by_cases hy : y ∈ tsupport ζ
      · have hz := ((hω.differentiableOn one_ne_zero _ (hmemU y hy s hs)).differentiableAt
          (hU.mem_nhds (hmemU y hy s hs))).hasFDerivAt
        have hline : HasDerivAt (fun σ : ℝ => y + σ • e) e s :=
          (((hasDerivAt_id' s).smul_const e).const_add y).congr_deriv (one_smul ℝ e)
        refine (HasDerivAt.clm_apply (c := fun σ : ℝ => ω (y + σ • e))
          (u := fun _ : ℝ => fderiv ℝ ζ y) (hz.comp_hasDerivAt s hline)
          (hasDerivAt_const s (fderiv ℝ ζ y))).congr_deriv ?_
        simp only [ContinuousLinearMap.map_zero, add_zero]
      · simp only [hDζ0 y hy, ContinuousLinearMap.map_zero]
        exact hasDerivAt_const s 0
    -- (b) domination by the integrable bound `C ‖Dζ‖`
    have hbound : ∀ y : Rn n, ∀ s ∈ ball (0 : ℝ) ε,
        ‖fderiv ℝ ω (y + s • e) e (fderiv ℝ ζ y)‖ ≤ C * ‖fderiv ℝ ζ y‖ := by
      intro y s hs
      by_cases hy : y ∈ tsupport ζ
      · have h1 := hC (y + s • e) (hmemK₁ y hy s hs)
        calc ‖fderiv ℝ ω (y + s • e) e (fderiv ℝ ζ y)‖
            ≤ ‖fderiv ℝ ω (y + s • e) e‖ * ‖fderiv ℝ ζ y‖ :=
              (fderiv ℝ ω (y + s • e) e).le_opNorm _
          _ ≤ C * ‖fderiv ℝ ζ y‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      · rw [hDζ0 y hy, ContinuousLinearMap.map_zero, norm_zero, norm_zero, mul_zero]
    -- (c) differentiation under the integral sign
    obtain ⟨hint, hder⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
      (F := fun (s : ℝ) (y : Rn n) => ω (y + s • e) (fderiv ℝ ζ y))
      (F' := fun (s : ℝ) (y : Rn n) => fderiv ℝ ω (y + s • e) e (fderiv ℝ ζ y))
      (bound := fun y => C * ‖fderiv ℝ ζ y‖) hball
      (Filter.eventually_of_mem hball fun s hs => (hcont s hs ω hωc).aestronglyMeasurable)
      ((hcont 0 h0 ω hωc).integrable_of_hasCompactSupport (hζc.mono' (hsupp _)))
      (hcont 0 h0 _ hDωe).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y s hs => hbound y s hs)
      (hDζint.const_mul C)
      (Filter.Eventually.of_forall fun y s hs => hderiv y s hs)
    simp only [zero_smul, add_zero] at hint hder
    exact ⟨hint, hder⟩
  obtain ⟨hint₁, hder₁⟩ := key ω₁ hω₁
  obtain ⟨hint₂, hder₂⟩ := key ω₂ hω₂
  -- Step 4: the translated weak identity gives `I₁ = I₂` near `0`.
  have heq : (fun s : ℝ => ∫ y, ω₁ (y + s • e) (fderiv ℝ ζ y)) =ᶠ[𝓝 0]
      (fun s : ℝ => ∫ y, ω₂ (y + s • e) (fderiv ℝ ζ y)) := by
    filter_upwards [ball_mem_nhds (0 : ℝ) hε] with s hs
    exact Submission.dohr_eb_lhr_ds_translate_weak_eq n ℓ U ω₁ ω₂ e s ζ hweak hζ hζc
      (fun y hy => hmemU y hy s hs)
  -- Step 6: hence the derivatives at `0` agree.
  have hD : ∫ y, fderiv ℝ ω₁ y e (fderiv ℝ ζ y) = ∫ y, fderiv ℝ ω₂ y e (fderiv ℝ ζ y) :=
    (hder₁.congr_of_eventuallyEq heq.symm).unique hder₂
  -- Step 7: the integrands vanish off `U`.
  have hzero : ∀ (ω : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (x : Rn n), x ∉ U →
      fderiv ℝ ω x e (fderiv ℝ ζ x) = 0 := by
    intro ω x hx
    rw [hDζ0 x (fun hxK => hx (hζU hxK)), ContinuousLinearMap.map_zero]
  refine ⟨hint₁.integrableOn, hint₂.integrableOn, ?_⟩
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (hzero ω₁),
    setIntegral_eq_integral_of_forall_compl_eq_zero (hzero ω₂)]
  exact hD
/-- **Simon Ch. 5, proof of Theorem 7.1 (elliptic bootstrap): the differentiated system.**
Let `a(x)` be bilinear forms and `Φ(x)` linear forms on `L = L(ℝⁿ, ℝ^ℓ)`, componentwise `C¹` on
the open set `U`, and let `v ∈ C²(U)` solve `∫_U a(x)[Dv(x)][Dζ(x)] = ∫_U Φ(x)[Dζ(x)]` for all
`ζ ∈ C¹_c(U)`.  Then `v_e = Dv(·) e` solves `∫_U a(x)[Dv_e(x)][Dζ(x)] = ∫_U Ψ(x)[Dζ(x)]` with
`Ψ(x)[P] = D(Φ(·)[P])(x) e − D(a(·)[Dv(x)][P])(x) e` on `U`.
Proof: put `ω₁ = a(·)[Dv(·)]`, `ω₂ = Φ` (both `C¹` into `L*`) and
`Ψ(x) = DΦ(x) e − D(a(·)[Dv(x)])(x) e`, which has the stated values since evaluation commutes with
differentiation.  Differentiating the weak identity `∫_U ω₁[Dζ] = ∫_U ω₂[Dζ]` in the direction
`e` gives `∫_U (Dω₁ e)[Dζ] = ∫_U (DΦ e)[Dζ]`, both integrands integrable on `U`.  On `U` the
Leibniz rule and `D v_e = D(Dv) e` give `(Dω₁ e)[Dζ] = a[Dv_e][Dζ] + c` and
`(DΦ e)[Dζ] = Ψ[Dζ] + c` with `c(x) = D(a(·)[Dv(x)][Dζ(x)])(x) e`.  If `c` is integrable on `U`,
subtract `∫_U c`; otherwise neither `a[Dv_e][Dζ]` nor `Ψ[Dζ]` is integrable on `U` and both
integrals vanish. -/
theorem dohr_eb_lhr_differentiated_system : ∀ (n ℓ : ℕ) (U : Set (Rn n)) (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Φ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (v : Rn n → Rn ℓ) (e : Rn n), IsOpen U → (∀ P Q : Rn n →L[ℝ] Rn ℓ, ContDiffOn ℝ 1 (fun x => a x P Q) U) → (∀ P : Rn n →L[ℝ] Rn ℓ, ContDiffOn ℝ 1 (fun x => Φ x P) U) → ContDiffOn ℝ 2 v U → (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ U → ∫ x in U, a x (fderiv ℝ v x) (fderiv ℝ ζ x) = ∫ x in U, Φ x (fderiv ℝ ζ x)) → ∃ Ψ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ, (∀ x ∈ U, ∀ P : Rn n →L[ℝ] Rn ℓ, Ψ x P = fderiv ℝ (fun z => Φ z P) x e - fderiv ℝ (fun z => a z (fderiv ℝ v x) P) x e) ∧ ∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ U → ∫ x in U, a x (fderiv ℝ (fun z => fderiv ℝ v z e) x) (fderiv ℝ ζ x) = ∫ x in U, Ψ x (fderiv ℝ ζ x) := by
  intro n ℓ U a Φ v e hU ha hΦ hv hweak
  -- Step 1: `Φ` is `C¹` into `L*`, and so is the frozen family `z ↦ a(z)[Dv(x)]`; for both,
  -- evaluation at `P` commutes with differentiation.
  obtain ⟨hΦ1, hΦd⟩ := Submission.dohr_eb_lhr_ds_clm_family n ℓ U Φ hU hΦ
  have hfrozen : ∀ x ∈ U, ∀ P : Rn n →L[ℝ] Rn ℓ,
      fderiv ℝ (fun z => a z (fderiv ℝ v x)) x e P =
        fderiv ℝ (fun z => a z (fderiv ℝ v x) P) x e := fun x hx P =>
    (Submission.dohr_eb_lhr_ds_clm_family n ℓ U (fun z => a z (fderiv ℝ v x)) hU
      (fun Q => ha (fderiv ℝ v x) Q)).2 x hx e P
  -- Step 2: `Dv` is `C¹` on `U`, so `ω₁ = a(·)[Dv(·)]` is `C¹` and obeys the Leibniz rule.
  have hDv : ContDiffOn ℝ 1 (fderiv ℝ v) U := hv.fderiv_of_isOpen hU (by norm_num)
  obtain ⟨hω₁, hω₁d⟩ := Submission.dohr_eb_lhr_ds_bilin_leibniz n ℓ U a (fderiv ℝ v) e hU ha hDv
  -- Step 3: `Ψ(x) = DΦ(x) e − D(a(·)[Dv(x)])(x) e` has the stated values on `U`.
  refine ⟨fun x => fderiv ℝ Φ x e - fderiv ℝ (fun z => a z (fderiv ℝ v x)) x e, ?_, ?_⟩
  · intro x hx P
    rw [sub_apply, hΦd x hx e P, hfrozen x hx P]
  intro ζ hζ hζc hζU
  -- Step 4: differentiate the weak identity for `(ω₁, Φ)` in the direction `e`.
  obtain ⟨hF₁, hF₂, hF⟩ := Submission.dohr_eb_lhr_ds_weak_eq_fderiv n ℓ U
    (fun x => a x (fderiv ℝ v x)) Φ e hU hω₁ hΦ1 hweak ζ hζ hζc hζU
  -- Step 5: on `U`, both integrands differ from the derivatives by the same term `c`.
  obtain ⟨c, hc⟩ : ∃ c : Rn n → ℝ,
      c = fun x => fderiv ℝ (fun z => a z (fderiv ℝ v x) (fderiv ℝ ζ x)) x e := ⟨_, rfl⟩
  have hU' : MeasurableSet U := hU.measurableSet
  have h₁ : EqOn (fun x => a x (fderiv ℝ (fun z => fderiv ℝ v z e) x) (fderiv ℝ ζ x))
      (fun x => fderiv ℝ (fun x => a x (fderiv ℝ v x)) x e (fderiv ℝ ζ x) - c x) U := by
    intro x hx
    simp only [hc]
    rw [hω₁d x hx (fderiv ℝ ζ x), Submission.dohr_eb_lhr_ds_fderiv_dirDeriv_eq n ℓ U v e hU hv x hx,
      add_sub_cancel_right]
  have h₂ : EqOn (fun x => (fderiv ℝ Φ x e - fderiv ℝ (fun z => a z (fderiv ℝ v x)) x e)
      (fderiv ℝ ζ x)) (fun x => fderiv ℝ Φ x e (fderiv ℝ ζ x) - c x) U := by
    intro x hx
    simp only [hc]
    rw [sub_apply, hfrozen x hx (fderiv ℝ ζ x)]
  rw [setIntegral_congr_fun hU' h₁, setIntegral_congr_fun hU' h₂]
  -- Step 6: subtract `∫_U c` if `c` is integrable on `U`; otherwise both sides are `0`.
  by_cases hcI : IntegrableOn c U
  · rw [integral_sub hF₁ hcI, integral_sub hF₂ hcI, hF]
  · have hn₁ : ¬ IntegrableOn
        (fun x => fderiv ℝ (fun x => a x (fderiv ℝ v x)) x e (fderiv ℝ ζ x) - c x) U :=
      fun h => hcI ((hF₁.sub h).congr_fun (fun x _ => sub_sub_cancel _ _) hU')
    have hn₂ : ¬ IntegrableOn (fun x => fderiv ℝ Φ x e (fderiv ℝ ζ x) - c x) U :=
      fun h => hcI ((hF₂.sub h).congr_fun (fun x _ => sub_sub_cancel _ _) hU')
    rw [integral_undef hn₁, integral_undef hn₂]

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05
