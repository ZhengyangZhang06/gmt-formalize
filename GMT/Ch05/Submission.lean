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

/-! ### Corollary 2.7 (`LipschitzGraphCorollary`), assembled from its child lemmas -/

/-- `|(x, y)| ≤ |x| + |y|` for the point `(x, y) ∈ ℝⁿ × ℝ^ℓ = ℝ^{n+ℓ}`. -/
theorem lgc_asm_norm_graphPoint_le {n ℓ : ℕ} (x : Rn n) (y : Rn ℓ) :
    ‖graphPoint x y‖ ≤ ‖x‖ + ‖y‖ := by
  have h : ‖graphPoint x y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
    simp only [graphPoint, EuclideanSpace.norm_sq_eq, Fin.sum_univ_add, Fin.append_left,
      Fin.append_right]
  nlinarith [norm_nonneg x, norm_nonneg y, norm_nonneg (graphPoint x y),
    mul_nonneg (norm_nonneg x) (norm_nonneg y)]

/-- `t ↦ (g t, h t) ∈ ℝ^{n+ℓ}` is continuous when `g` and `h` are. -/
theorem lgc_asm_continuous_graphPoint {n ℓ : ℕ} {X : Type*} [TopologicalSpace X]
    {g : X → Rn n} {h : X → Rn ℓ} (hg : Continuous g) (hh : Continuous h) :
    Continuous fun t => graphPoint (g t) (h t) := by
  unfold graphPoint
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  induction i using Fin.addCases with
  | left j =>
    simp only [Fin.append_left]
    exact (continuous_apply j).comp ((PiLp.continuous_ofLp 2 _).comp hg)
  | right j =>
    simp only [Fin.append_right]
    exact (continuous_apply j).comp ((PiLp.continuous_ofLp 2 _).comp hh)

/-- `p_{T_x M}` is an orthogonal projection or `0`, so its operator norm is at most `1`. -/
theorem lgc_asm_norm_tangentProj_le {n ℓ : ℕ} {U : Set (Amb n ℓ)}
    (V : RectifiableVarifold n ℓ U) (x : Amb n ℓ) : ‖V.tangentProj x‖ ≤ 1 := by
  rw [RectifiableVarifold.tangentProj]
  split_ifs
  · exact Submodule.starProjection_norm_le _
  · simp

theorem lgc_asm_hsNormSq_nonneg {m k : ℕ} (A : Rn m →L[ℝ] Rn k) : 0 ≤ hsNormSq A :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- `|A|² ≤ m ‖A‖²` (Hilbert–Schmidt versus operator norm). -/
theorem lgc_asm_hsNormSq_le {m k : ℕ} (A : Rn m →L[ℝ] Rn k) : hsNormSq A ≤ m * ‖A‖ ^ 2 := by
  calc hsNormSq A ≤ ∑ _i : Fin m, ‖A‖ ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h := A.le_opNorm (EuclideanSpace.single i (1 : ℝ))
        have h1 : ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := by simp
        rw [h1, mul_one] at h
        exact pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = m * ‖A‖ ^ 2 := by simp

theorem lgc_asm_continuous_hsNormSq {m k : ℕ} :
    Continuous fun A : Rn m →L[ℝ] Rn k => hsNormSq A := by
  unfold hsNormSq
  exact continuous_finsetSum _ fun i _ =>
    ((continuous_id.clm_apply continuous_const).norm).pow 2

/-- By `lgc_tangent_plane_ae`, the tilt integrand `|p_{T_x M} − p_T|²` is `μ_V`-integrable on
every set of finite `μ_V`-measure (it is bounded by `4(n + ℓ)`). -/
theorem lgc_asm_integrableOn_tilt {n ℓ : ℕ} (hn : 1 ≤ n) {U : Set (Amb n ℓ)} (hU : IsOpen U)
    (V : RectifiableVarifold n ℓ U) (T : Submodule ℝ (Amb n ℓ)) {B : Set (Amb n ℓ)}
    (hB : V.weight B ≠ ⊤) :
    IntegrableOn (fun x => hsNormSq (V.tangentProj x - T.starProjection)) B V.weight := by
  refine Measure.integrableOn_of_bounded (M := ((n + ℓ : ℕ) : ℝ) * 2 ^ 2) hB
    (lgc_asm_continuous_hsNormSq.comp_aestronglyMeasurable
      ((Submission.lgc_tangent_plane_ae n ℓ hn U hU V).1.sub aestronglyMeasurable_const))
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (lgc_asm_hsNormSq_nonneg _)]
  refine (lgc_asm_hsNormSq_le _).trans ?_
  gcongr
  calc ‖V.tangentProj x - T.starProjection‖ ≤ ‖V.tangentProj x‖ + ‖T.starProjection‖ :=
        norm_sub_le _ _
    _ ≤ 1 + 1 := add_le_add (lgc_asm_norm_tangentProj_le V x) T.starProjection_norm_le
    _ = 2 := by norm_num

/-- **Simon Ch. 5, Corollary 2.7** (`LipschitzGraphCorollary`).  Steps 1–3 of the proof are the
children `lgc_height_cone` (with the sibling `affine_approximation_lemma` and `τ = βL`) and
`lgc_cone_graph_extension` (with `S = spt V ∩ B_{σ₀/2}(0)`, `ε = C₁βL`,
`R₀ = min{Kδ^{1/(2n+2)}σ₀, C₁βLσ₀}`); the forward inclusion is immediate, and a point of the graph
over `Bⁿ_{σ₀/4}(0)` off `spt V` is moved along the graph (intermediate value theorem) to a point at
distance `d ∈ (0, σ₀/64]` from `spt V`, where the hole estimate `lgc_hole_estimate` contradicts the
tilt hypothesis on `B_{5d/2}(y)`. -/
theorem lipschitz_graph_corollary : LipschitzGraphCorollary := by
  intro n ℓ hn p hp
  obtain ⟨δ₁, C₁, hδ₁, hC₁, hHC⟩ :=
    Submission.lgc_height_cone Submission.affine_approximation_lemma n ℓ hn p hp
  obtain ⟨δ₂, ε₂, C₂, hδ₂, hε₂, hC₂, hHE⟩ := Submission.lgc_hole_estimate n ℓ hn p hp
  -- Step 7: the choice of `β`.
  obtain ⟨β, hβpos, hβ4, hβδ₁, hβδ₂, hβC₁, hβA, hβD⟩ : ∃ β : ℝ, 0 < β ∧ β ≤ 1 / 4 ∧
      β ≤ δ₁ ∧ β ≤ δ₂ ∧ β ≤ 1 / (64 * C₁) ∧ β ≤ min 1 ε₂ / (2 * Real.sqrt ℓ * C₁ + 1) ∧
      β ≤ 1 / (C₂ * 5 ^ n + 1) := by
    refine ⟨min (1 / 4) (min δ₁ (min δ₂ (min (1 / (64 * C₁))
      (min (min 1 ε₂ / (2 * Real.sqrt ℓ * C₁ + 1)) (1 / (C₂ * 5 ^ n + 1)))))), by positivity,
      ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [min_le_iff, le_refl, true_or, or_true]
  rw [le_div_iff₀ (by positivity)] at hβC₁ hβA hβD
  refine ⟨β, hβpos, hβ4, ?_⟩
  intro L K hL hL1 hK U hU V H δ ρ hδ hδβ hAH q hheight htilt
  obtain ⟨hρ, -, -, h0, hBU, hmass, -⟩ := id hAH
  have hσ₀ : 0 < δ * ρ := mul_pos hδ hρ
  -- `δ ≤ (βL)^{2n+2} ≤ βL ≤ β ≤ 1/4`, and `δ^{1/(2n+2)} ≤ βL`.
  have hβL : β * L ≤ β := mul_le_of_le_one_right hβpos.le hL1
  have hδβL : δ ≤ β * L :=
    hδβ.trans (pow_le_of_le_one (by positivity) (by linarith) (by omega))
  have hδβ' : δ ≤ β := hδβL.trans hβL
  have hσρ : δ * ρ ≤ ρ / 4 := by nlinarith
  have hτ : δ ^ (1 / (2 * (n : ℝ) + 2)) ≤ β * L := by
    have hα : (1 / (2 * (n : ℝ) + 2)) = ((2 * n + 2 : ℕ) : ℝ)⁻¹ := by push_cast; ring
    rw [hα]
    calc δ ^ ((2 * n + 2 : ℕ) : ℝ)⁻¹ ≤ ((β * L) ^ (2 * n + 2)) ^ ((2 * n + 2 : ℕ) : ℝ)⁻¹ :=
          Real.rpow_le_rpow hδ.le hδβ (by positivity)
      _ = β * L := Real.pow_rpow_inv_natCast (by positivity) (by omega)
  -- Steps 1–2 (`lgc_height_cone` with `τ = βL`): height bound and cone condition.
  have htilt' : ∀ ξ ∈ V.support ∩ closedBall 0 (δ * ρ / 2), ∀ σ : ℝ, 0 < σ →
      σ ≤ δ * ρ / 2 → V.tiltExcess ξ σ (rotatedPlane q) ≤ (β * L) ^ 2 := by
    intro ξ hξ σ hσ hσle
    rw [mul_pow]
    exact htilt ξ hξ σ hσ hσle
  obtain ⟨hH1, hH2⟩ := hHC U hU V H δ ρ hδ (hδβ'.trans hβδ₁) hAH q (β * L) hτ htilt'
  -- Step 3 (`lgc_cone_graph_extension`): the Lipschitz graph through `spt V ∩ B_{σ₀/2}(0)`.
  have hC₁βL : C₁ * (β * L) ≤ 1 / 64 := by
    have h : C₁ * (β * L) ≤ C₁ * β := mul_le_mul_of_nonneg_left hβL hC₁.le
    linarith
  have hSh : ∀ y ∈ V.support ∩ closedBall 0 (δ * ρ / 2),
      infDist y (rotatedPlane q : Set (Amb n ℓ)) ≤
        min (K * δ ^ (1 / (2 * (n : ℝ) + 2)) * (δ * ρ)) (C₁ * (β * L) * (δ * ρ)) := by
    intro y hy
    have hy0 : ‖y‖ ≤ δ * ρ / 2 := mem_closedBall_zero_iff.1 hy.2
    exact le_min (hheight y ⟨hy.1, mem_closedBall_zero_iff.2 (by linarith)⟩)
      (hH1 y ⟨hy.1, mem_closedBall_zero_iff.2 (by linarith)⟩)
  obtain ⟨f, hfLip, hfR, hfS⟩ := Submission.lgc_cone_graph_extension n ℓ q
    (V.support ∩ closedBall 0 (δ * ρ / 2)) (C₁ * (β * L))
    (min (K * δ ^ (1 / (2 * (n : ℝ) + 2)) * (δ * ρ)) (C₁ * (β * L) * (δ * ρ)))
    (by positivity) (by linarith) (le_min (by positivity) (by positivity)) hH2 hSh
  have hsq : 2 * Real.sqrt ℓ * C₁ * β ≤ 1 - β := by
    have := min_le_left 1 ε₂
    linarith
  have hsqε : 2 * Real.sqrt ℓ * C₁ * β ≤ ε₂ := by
    have := min_le_right 1 ε₂
    linarith
  have hLipL : 2 * Real.sqrt ℓ * (C₁ * (β * L)) ≤ L := by
    have h := mul_le_mul_of_nonneg_right hsq hL.le
    have hβL0 : 0 < β * L := mul_pos hβpos hL
    nlinarith
  have hLipε : 2 * Real.sqrt ℓ * (C₁ * (β * L)) ≤ ε₂ := by
    have h : 2 * Real.sqrt ℓ * C₁ * β * L ≤ 2 * Real.sqrt ℓ * C₁ * β :=
      mul_le_of_le_one_right (by positivity) hL1
    nlinarith
  have hf64 : ∀ x, ‖f x‖ ≤ δ * ρ / 64 := fun x => by
    have h := (hfR x).trans (min_le_right _ _)
    have h' : C₁ * (β * L) * (δ * ρ) ≤ 1 / 64 * (δ * ρ) :=
      mul_le_mul_of_nonneg_right hC₁βL hσ₀.le
    linarith
  refine ⟨f, (hfLip.weaken (Real.toNNReal_le_toNNReal hLipL)).lipschitzOnWith,
    fun x _ => (hfR x).trans (min_le_left _ _), Set.Subset.antisymm ?_ ?_⟩
  · -- Step 4: `spt V ∩ B_{σ₀/4}(0) ⊆ q(graph f) ∩ B_{σ₀/4}(0)`.
    rintro y ⟨hyV, hyB⟩
    have hy0 : ‖y‖ ≤ δ * ρ / 4 := mem_closedBall_zero_iff.1 hyB
    obtain ⟨x, hxy, hqx⟩ := hfS y ⟨hyV, mem_closedBall_zero_iff.2 (by linarith)⟩
    exact ⟨⟨graphPoint x (f x), ⟨x, mem_closedBall_zero_iff.2 (hxy.trans hy0), rfl⟩, hqx⟩, hyB⟩
  · -- Step 6: a graph point over `Bⁿ_{σ₀/4}(0)` in `B_{σ₀/4}(0)` lies in `spt V`.
    rintro ζ ⟨⟨g, ⟨xz, hxz, rfl⟩, rfl⟩, hζB⟩
    refine ⟨?_, hζB⟩
    by_contra hζV
    have hxz0 : ‖xz‖ ≤ δ * ρ / 4 := mem_closedBall_zero_iff.1 hxz
    have hζ0 : ‖q (graphPoint xz (f xz))‖ ≤ δ * ρ / 4 := mem_closedBall_zero_iff.1 hζB
    have hζU : q (graphPoint xz (f xz)) ∈ U :=
      hBU (mem_closedBall_zero_iff.2 (by linarith))
    have hsuppV : V.support ⊆ V.weight.support := fun x hx => hx.2
    have hζpos : 0 < infDist (q (graphPoint xz (f xz))) V.support :=
      lt_of_lt_of_le ((Measure.isClosed_support.notMem_iff_infDist_pos ⟨0, hsuppV h0⟩).1
        fun h => hζV ⟨hζU, h⟩) (infDist_le_infDist_of_subset hsuppV ⟨0, h0⟩)
    -- Move along `t ↦ q(t x_ζ, f(t x_ζ))` to a graph point at distance `≤ σ₀/64` from `spt V`.
    obtain ⟨ζ', hζ'mem, hζ'norm, hdpos, hdle⟩ : ∃ ζ' ∈ q '' graphOver f univ,
        ‖ζ'‖ ≤ δ * ρ / 4 + δ * ρ / 64 ∧ 0 < infDist ζ' V.support ∧
          infDist ζ' V.support ≤ δ * ρ / 64 := by
      have hγc : Continuous fun t : ℝ => q (graphPoint (t • xz) (f (t • xz))) :=
        q.continuous.comp (lgc_asm_continuous_graphPoint (continuous_id.smul continuous_const)
          (hfLip.continuous.comp (continuous_id.smul continuous_const)))
      have hφc : Continuous fun t : ℝ =>
          infDist (q (graphPoint (t • xz) (f (t • xz)))) V.support :=
        (continuous_infDist_pt _).comp hγc
      have hφ0 : infDist (q (graphPoint ((0 : ℝ) • xz) (f ((0 : ℝ) • xz)))) V.support ≤
          δ * ρ / 64 := by
        calc infDist (q (graphPoint ((0 : ℝ) • xz) (f ((0 : ℝ) • xz)))) V.support
            ≤ dist (q (graphPoint ((0 : ℝ) • xz) (f ((0 : ℝ) • xz)))) 0 :=
              infDist_le_dist_of_mem h0
          _ = ‖graphPoint (0 : Rn n) (f 0)‖ := by
              rw [dist_zero_right, LinearIsometryEquiv.norm_map, zero_smul]
          _ ≤ ‖(0 : Rn n)‖ + ‖f 0‖ := lgc_asm_norm_graphPoint_le _ _
          _ ≤ δ * ρ / 64 := by rw [norm_zero, zero_add]; exact hf64 0
      have hpt : ∀ t ∈ Icc (0 : ℝ) 1,
          q (graphPoint (t • xz) (f (t • xz))) ∈ q '' graphOver f univ ∧
            ‖q (graphPoint (t • xz) (f (t • xz)))‖ ≤ δ * ρ / 4 + δ * ρ / 64 := by
        intro t ht
        refine ⟨⟨_, ⟨t • xz, mem_univ _, rfl⟩, rfl⟩, ?_⟩
        rw [LinearIsometryEquiv.norm_map]
        have htx : ‖t • xz‖ ≤ δ * ρ / 4 := by
          rw [norm_smul, Real.norm_of_nonneg ht.1]
          calc t * ‖xz‖ ≤ 1 * ‖xz‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
            _ ≤ δ * ρ / 4 := by rw [one_mul]; exact hxz0
        calc ‖graphPoint (t • xz) (f (t • xz))‖ ≤ ‖t • xz‖ + ‖f (t • xz)‖ :=
              lgc_asm_norm_graphPoint_le _ _
          _ ≤ δ * ρ / 4 + δ * ρ / 64 := add_le_add htx (hf64 _)
      by_cases h1 : infDist (q (graphPoint xz (f xz))) V.support ≤ δ * ρ / 64
      · obtain ⟨hm, hm'⟩ := hpt 1 ⟨zero_le_one, le_rfl⟩
        rw [one_smul] at hm hm'
        exact ⟨_, hm, hm', hζpos, h1⟩
      · rw [not_le] at h1
        obtain ⟨t, ht, hteq⟩ := intermediate_value_Icc zero_le_one hφc.continuousOn
          ⟨hφ0, by simpa only [one_smul] using h1.le⟩
        have hteq' : infDist (q (graphPoint (t • xz) (f (t • xz)))) V.support = δ * ρ / 64 :=
          hteq
        obtain ⟨hm, hm'⟩ := hpt t ht
        exact ⟨_, hm, hm', by rw [hteq']; positivity, hteq'.le⟩
    -- Step 5 (`lgc_hole_estimate`) at `ζ'`, with `d = dist(ζ', spt V)` and `s = d/2`.
    obtain ⟨y, hyV, hyd, hineq⟩ := hHE U hU V H δ ρ hδ (hδβ'.trans hβδ₂) hAH q f
      (2 * Real.sqrt ℓ * (C₁ * (β * L))) (by positivity) hLipε hfLip ζ' hζ'mem (by linarith)
      hdpos (by linarith)
    set d := infDist ζ' V.support
    -- `spt V ∩ B_{3s}(ζ') ⊆ spt V ∩ B_{σ₀/2}(0)` lies on the graph, hence
    -- `μ(B_{3s}(ζ') \ q(graph f)) = 0`.
    have hnull : V.weight (closedBall ζ' (3 * (d / 2)) \ q '' graphOver f univ) = 0 := by
      refine measure_mono_null (fun x hx => ?_) (Measure.measure_compl_support (μ := V.weight))
      obtain ⟨hxB, hxF⟩ := hx
      rw [Set.mem_compl_iff]
      intro hxμ
      apply hxF
      have hxζ : dist x ζ' ≤ 3 * (d / 2) := mem_closedBall.1 hxB
      have hx0 : ‖x‖ ≤ δ * ρ / 2 := by
        have h := norm_sub_norm_le x ζ'
        rw [← dist_eq_norm] at h
        linarith
      have hxU : x ∈ U := hBU (mem_closedBall_zero_iff.2 (by linarith))
      obtain ⟨x', -, hx'⟩ := hfS x ⟨⟨hxU, hxμ⟩, mem_closedBall_zero_iff.2 hx0⟩
      exact ⟨graphPoint x' (f x'), ⟨x', mem_univ _, rfl⟩, hx'⟩
    rw [hnull, ENNReal.toReal_zero, zero_add] at hineq
    -- Compare with the tilt hypothesis on `B_{5s}(y) ⊇ B_{3s}(ζ')`.
    have hy0 : ‖y‖ ≤ δ * ρ / 2 := by
      have h := norm_sub_norm_le y ζ'
      rw [← dist_eq_norm, hyd] at h
      linarith
    have hsub : closedBall ζ' (3 * (d / 2)) ⊆ closedBall y (5 * (d / 2)) := by
      intro x hx
      rw [mem_closedBall] at hx ⊢
      calc dist x y ≤ dist x ζ' + dist ζ' y := dist_triangle _ _ _
        _ ≤ 3 * (d / 2) + d := by rw [dist_comm ζ' y, hyd]; linarith
        _ = 5 * (d / 2) := by ring
    have hfin : V.weight (closedBall y (5 * (d / 2))) ≠ ⊤ := by
      refine ne_top_of_le_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmass)
        (measure_mono (closedBall_subset_closedBall' ?_))
      rw [dist_zero_right]
      linarith
    have hmono : ∫ x in closedBall ζ' (3 * (d / 2)),
          hsNormSq (V.tangentProj x - (rotatedPlane q).starProjection) ∂V.weight ≤
        ∫ x in closedBall y (5 * (d / 2)),
          hsNormSq (V.tangentProj x - (rotatedPlane q).starProjection) ∂V.weight :=
      setIntegral_mono_set (lgc_asm_integrableOn_tilt hn hU V (rotatedPlane q) hfin)
        (Filter.Eventually.of_forall fun x => lgc_asm_hsNormSq_nonneg _)
        (Filter.Eventually.of_forall fun x hx => hsub hx)
    have h5s : 0 < 5 * (d / 2) := by positivity
    have htiltY : ((5 * (d / 2)) ^ n)⁻¹ * ∫ x in closedBall y (5 * (d / 2)),
          hsNormSq (V.tangentProj x - (rotatedPlane q).starProjection) ∂V.weight ≤
        β ^ 2 * L ^ 2 :=
      htilt y ⟨hyV, mem_closedBall_zero_iff.2 hy0⟩ (5 * (d / 2)) h5s (by linarith)
    rw [inv_mul_le_iff₀ (by positivity)] at htiltY
    -- `sⁿ ≤ C₂ 5ⁿ β² L² sⁿ < sⁿ`, a contradiction.
    have hs : 0 < (d / 2) ^ n := by positivity
    have hβ2 : β ^ 2 * L ^ 2 ≤ β := by
      have hL2 : L ^ 2 ≤ 1 := pow_le_one₀ hL.le hL1
      calc β ^ 2 * L ^ 2 ≤ β ^ 2 * 1 := mul_le_mul_of_nonneg_left hL2 (by positivity)
        _ = β * β := by ring
        _ ≤ β * 1 := mul_le_mul_of_nonneg_left (by linarith) hβpos.le
        _ = β := mul_one β
    have hlt : C₂ * 5 ^ n * β < 1 := by linarith
    have hkey : C₂ * ((5 * (d / 2)) ^ n * (β ^ 2 * L ^ 2)) ≤
        (C₂ * 5 ^ n * β) * (d / 2) ^ n := by
      rw [mul_pow]
      calc C₂ * (5 ^ n * (d / 2) ^ n * (β ^ 2 * L ^ 2)) ≤ C₂ * (5 ^ n * (d / 2) ^ n * β) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hβ2 (by positivity)) hC₂.le
        _ = (C₂ * 5 ^ n * β) * (d / 2) ^ n := by ring
    have hfinal : (C₂ * 5 ^ n * β) * (d / 2) ^ n < (d / 2) ^ n := by
      calc (C₂ * 5 ^ n * β) * (d / 2) ^ n < 1 * (d / 2) ^ n := mul_lt_mul_of_pos_right hlt hs
        _ = (d / 2) ^ n := one_mul _
    have hchain := mul_le_mul_of_nonneg_left (hmono.trans htiltY) hC₂.le
    linarith

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05
