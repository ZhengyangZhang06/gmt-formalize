<!-- theorem-id: gmt-ch05/root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.unit_ball_estimate-a1.holder_improvement-a1 -->

## Theorem `Submission.dohr_eb_sch_ube_holder_improvement`

Let n, l be natural numbers, L := L(R^n, R^l) with the operator norm, g : R^n -> L, and reals alpha, M, A, Q with 0 < alpha <= 1, M >= 0, A >= 0 and Q >= 0. Call (y, rho) (y in R^n, rho real) admissible if rho > 0 and |y| + rho <= 1. Assume: (P1) for every admissible (y, rho) and all x, x' in B_{rho/2}(y): rho^{1+alpha} ||g(x) - g(x')|| <= Q |x - x'|^alpha; (P2) for every admissible (y, rho) and every real K such that ||g(x) - g(x')|| <= K |x - x'|^alpha for all x, x' in B_rho(y): rho^{1+alpha} ||g(x) - g(x')|| <= ((1/16) rho^{1+alpha} K + A) |x - x'|^alpha for all x, x' in B_{rho/2}(y); (P3) for every x in R^n and reals r, t, K with |x| + r <= 1, K >= 0, 0 < t < r and ||g(z) - g(z')|| <= K |z - z'|^alpha for all z, z' in B_r(x): ||g(x)|| <= 2M/t + t^alpha K. Then for every admissible (y, rho): (a) rho ||g(x)|| <= 32 M + Q/4 + 16 A for all x in B_{rho/2}(y); and (b) rho^{1+alpha} ||g(x) - g(x')|| <= (Q/2 + 512 M + 32 A) |x - x'|^alpha for all x, x' in B_{rho/2}(y).

Node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.unit_ball_estimate-a1.holder_improvement-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/3924

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.dohr_eb_sch_ube_holder_improvement`

```lean
∀ (n ℓ : ℕ) (g : Rn n → (Rn n →L[ℝ] Rn ℓ)) (α M A Q : ℝ), 0 < α → α ≤ 1 → 0 ≤ M → 0 ≤ A → 0 ≤ Q → (∀ (y : Rn n) (ρ : ℝ), 0 < ρ → ‖y‖ + ρ ≤ 1 → ∀ x ∈ ball y (ρ / 2), ∀ x' ∈ ball y (ρ / 2), ρ ^ (1 + α) * ‖g x - g x'‖ ≤ Q * ‖x - x'‖ ^ α) → (∀ (y : Rn n) (ρ K : ℝ), 0 < ρ → ‖y‖ + ρ ≤ 1 → (∀ x ∈ ball y ρ, ∀ x' ∈ ball y ρ, ‖g x - g x'‖ ≤ K * ‖x - x'‖ ^ α) → ∀ x ∈ ball y (ρ / 2), ∀ x' ∈ ball y (ρ / 2), ρ ^ (1 + α) * ‖g x - g x'‖ ≤ (1 / 16 * ρ ^ (1 + α) * K + A) * ‖x - x'‖ ^ α) → (∀ (x : Rn n) (r t K : ℝ), ‖x‖ + r ≤ 1 → 0 ≤ K → 0 < t → t < r → (∀ z ∈ ball x r, ∀ z' ∈ ball x r, ‖g z - g z'‖ ≤ K * ‖z - z'‖ ^ α) → ‖g x‖ ≤ 2 * M / t + t ^ α * K) → ∀ (y : Rn n) (ρ : ℝ), 0 < ρ → ‖y‖ + ρ ≤ 1 → (∀ x ∈ ball y (ρ / 2), ρ * ‖g x‖ ≤ 32 * M + Q / 4 + 16 * A) ∧ ∀ x ∈ ball y (ρ / 2), ∀ x' ∈ ball y (ρ / 2), ρ ^ (1 + α) * ‖g x - g x'‖ ≤ (Q / 2 + 512 * M + 32 * A) * ‖x - x'‖ ^ α
```

### Frozen project context

`GMT/Ch05/Contract.lean` at `ea5607598f3133b40a13241f2e51517a8c6423cd` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
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

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `accepted`.

# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.unit_ball_estimate-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.unit_ball_estimate-a1.holder_improvement-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 3, 4 and 5 of the parent proof, with the supremum Q replaced by an arbitrary constant Q >= 0 satisfying (P1), delta = 1/16, and A in the role of 2 C_delta M. The parent's H(rho) corresponds to H / rho^{1+alpha} with H := Q/4 + 16 A (the parent's bound rho^{1+alpha} H(rho) <= 4 delta Q + 32 C_delta M).
Fix an admissible (y, rho) and put H := Q/4 + 16 A >= 0.
1. Position of points. For x in B_{rho/2}(y): |x| <= |y| + |x - y| < |y| + rho/2, so |x| + rho/2 < |y| + rho <= 1. Hence (x, rho/2) and (x, rho/4) are admissible and |x| + rho/8 <= 1.
2. Numerical facts. Since 1 <= 1 + alpha <= 2 and the bases are >= 1: 2^{1+alpha} <= 2^2 = 4 and 4^{1+alpha} <= 4^2 = 16. Since 0 < alpha <= 1: 16^alpha >= 1, 8^alpha <= 8^1 = 8 and 8^alpha <= 16^alpha. Also rho^{1+alpha} = rho rho^alpha, and (rho/m)^beta = rho^beta / m^beta for m > 0 (div_rpow).
3. Hoelder bound on small balls (parent 6b). Claim: for x in B_{rho/2}(y) and z, z' in B_{rho/8}(x): rho^{1+alpha} ||g(z) - g(z')|| <= H |z - z'|^alpha.
 Proof. By (P1) for the admissible pair (x, rho/2) (whose half ball is B_{rho/4}(x)), for u, u' in B_{rho/4}(x): (rho/2)^{1+alpha} ||g(u) - g(u')|| <= Q |u - u'|^alpha, i.e. ||g(u) - g(u')|| <= K' |u - u'|^alpha with K' := Q / (rho/2)^{1+alpha}. Apply (P2) to the admissible pair (x, rho/4) (whose half ball is B_{rho/8}(x)) and this K': for z, z' in B_{rho/8}(x), (rho/4)^{1+alpha} ||g(z) - g(z')|| <= ((1/16) (rho/4)^{1+alpha} K' + A) |z - z'|^alpha. By step 2, (rho/4)^{1+alpha} = rho^{1+alpha} / 4^{1+alpha} and (rho/4)^{1+alpha} K' = Q 2^{1+alpha} / 4^{1+alpha}. Multiplying by 4^{1+alpha} > 0 gives rho^{1+alpha} ||g(z) - g(z')|| <= (Q 2^{1+alpha}/16 + A 4^{1+alpha}) |z - z'|^alpha <= (Q/4 + 16 A) |z - z'|^alpha, using Q >= 0, A >= 0, |z - z'|^alpha >= 0 and step 2.
4. Fine sup bound (parent 6c). Claim: for x in B_{rho/2}(y): rho ||g(x)|| <= 32 M + H / 16^alpha.
 Proof. By step 3, ||g(z) - g(z')|| <= K |z - z'|^alpha for z, z' in B_{rho/8}(x), with K := H / rho^{1+alpha} >= 0. Apply (P3) with r := rho/8 and t := rho/16 (|x| + rho/8 <= 1 by step 1, and 0 < t < r): ||g(x)|| <= 2M/(rho/16) + (rho/16)^alpha H / rho^{1+alpha} = 32 M / rho + (rho^alpha / 16^alpha) H / (rho rho^alpha) = (32 M + H / 16^alpha) / rho. Multiply by rho > 0.
5. Conclusion (a). Since 16^alpha >= 1 and H >= 0, H / 16^alpha <= H; by step 4, rho ||g(x)|| <= 32 M + H = 32 M + Q/4 + 16 A for x in B_{rho/2}(y).
6. Conclusion (b) (parent 6d). Let x, x' be in B_{rho/2}(y) and d := |x - x'|^alpha >= 0. Note H <= Q/2 + 512 M + 32 A since Q, M, A >= 0.
 Case |x - x'| < rho/8. Then x and x' lie in B_{rho/8}(x), and step 3 gives rho^{1+alpha} ||g(x) - g(x')|| <= H d <= (Q/2 + 512 M + 32 A) d.
 Case |x - x'| >= rho/8. By monotonicity of s -> s^alpha on [0, infinity) (alpha >= 0), d >= (rho/8)^alpha = rho^alpha / 8^alpha, so rho^alpha <= 8^alpha d <= 8 d and rho^alpha / 16^alpha <= 8^alpha d / 16^alpha <= d (step 2). By the triangle inequality and step 4 at x and at x': rho^{1+alpha} ||g(x) - g(x')|| = rho^alpha (rho ||g(x) - g(x')||) <= rho^alpha (rho ||g(x)|| + rho ||g(x')||) <= rho^alpha * 2 (32 M + H / 16^alpha) = 64 M rho^alpha + 2 H (rho^alpha / 16^alpha) <= 64 M * 8 d + 2 H d = (Q/2 + 512 M + 32 A) d, using M >= 0 and H >= 0.
In both cases (b) holds. QED
Lean proof checked at the pin (Lean 4.35.0-rc3, Mathlib 25730c7c; stated inside `namespace GMT.Ch05` with the contract's `open`s, appended to a scratch copy of the submission; the generated NodeSolution target closes by `exact Submission.dohr_eb_sch_ube_holder_improvement`; #print axioms: propext, Classical.choice, Quot.sound):
set_option maxSynthPendingDepth 3 in
theorem Submission.dohr_eb_sch_ube_holder_improvement : ∀ (n ℓ : ℕ) (g : Rn n → (Rn n →L[ℝ] Rn ℓ)) (α M A Q : ℝ), 0 < α → α ≤ 1 → 0 ≤ M → 0 ≤ A → 0 ≤ Q → (∀ (y : Rn n) (ρ : ℝ), 0 < ρ → ‖y‖ + ρ ≤ 1 → ∀ x ∈ ball y (ρ / 2), ∀ x' ∈ ball y (ρ / 2), ρ ^ (1 + α) * ‖g x - g x'‖ ≤ Q * ‖x - x'‖ ^ α) → (∀ (y : Rn n) (ρ K : ℝ), 0 < ρ → ‖y‖ + ρ ≤ 1 → (∀ x ∈ ball y ρ, ∀ x' ∈ ball y ρ, ‖g x - g x'‖ ≤ K * ‖x - x'‖ ^ α) → ∀ x ∈ ball y (ρ / 2), ∀ x' ∈ ball y (ρ / 2), ρ ^ (1 + α) * ‖g x - g x'‖ ≤ (1 / 16 * ρ ^ (1 + α) * K + A) * ‖x - x'‖ ^ α) → (∀ (x : Rn n) (r t K : ℝ), ‖x‖ + r ≤ 1 → 0 ≤ K → 0 < t → t < r → (∀ z ∈ ball x r, ∀ z' ∈ ball x r, ‖g z - g z'‖ ≤ K * ‖z - z'‖ ^ α) → ‖g x‖ ≤ 2 * M / t + t ^ α * K) → ∀ (y : Rn n) (ρ : ℝ), 0 < ρ → ‖y‖ + ρ ≤ 1 → (∀ x ∈ ball y (ρ / 2), ρ * ‖g x‖ ≤ 32 * M + Q / 4 + 16 * A) ∧ ∀ x ∈ ball y (ρ / 2), ∀ x' ∈ ball y (ρ / 2), ρ ^ (1 + α) * ‖g x - g x'‖ ≤ (Q / 2 + 512 * M + 32 * A) * ‖x - x'‖ ^ α := by
  intro n ℓ g α M A Q hα0 hα1 hM hA hQ0 hP1 hP2 hP3 y ρ hρ hyρ
  have hxnorm : ∀ x ∈ ball y (ρ / 2), ‖x‖ + ρ / 2 < 1 := by
    intro x hx
    rw [mem_ball, dist_eq_norm] at hx
    have : ‖x‖ ≤ ‖y‖ + ‖x - y‖ := by
      calc ‖x‖ = ‖y + (x - y)‖ := by rw [add_sub_cancel]
        _ ≤ ‖y‖ + ‖x - y‖ := norm_add_le _ _
    linarith
  have hR : 0 < ρ ^ (1 + α) := Real.rpow_pos_of_pos hρ _
  have hsplit : ρ ^ (1 + α) = ρ * ρ ^ α := by rw [Real.rpow_add hρ, Real.rpow_one]
  have hρα : 0 < ρ ^ α := Real.rpow_pos_of_pos hρ α
  have p2pos : (0:ℝ) < 2 ^ (1 + α) := by positivity
  have p4pos : (0:ℝ) < 4 ^ (1 + α) := by positivity
  have p2ne : (2:ℝ) ^ (1 + α) ≠ 0 := p2pos.ne'
  have p4ne : (4:ℝ) ^ (1 + α) ≠ 0 := p4pos.ne'
  have hRne : ρ ^ (1 + α) ≠ 0 := hR.ne'
  have p2le : (2:ℝ) ^ (1 + α) ≤ 4 := by
    calc (2:ℝ) ^ (1 + α) ≤ 2 ^ (2:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 4 := by rw [Real.rpow_two]; norm_num
  have p4le : (4:ℝ) ^ (1 + α) ≤ 16 := by
    calc (4:ℝ) ^ (1 + α) ≤ 4 ^ (2:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 16 := by rw [Real.rpow_two]; norm_num
  have hH0 : 0 ≤ Q / 4 + 16 * A := by linarith
  -- Step 3: Hoelder bound with constant (Q/4 + 16 A) / ρ^(1+α) on ball x (ρ/8)
  have hsmall : ∀ x ∈ ball y (ρ / 2), ∀ z ∈ ball x (ρ / 8), ∀ z' ∈ ball x (ρ / 8),
      ρ ^ (1 + α) * ‖g z - g z'‖ ≤ (Q / 4 + 16 * A) * ‖z - z'‖ ^ α := by
    intro x hx z hz z' hz'
    have hx1 := hxnorm x hx
    have hρ2 : 0 < ρ / 2 := by positivity
    have hρ4 : 0 < ρ / 4 := by positivity
    have e2 : (ρ / 2) ^ (1 + α) = ρ ^ (1 + α) / 2 ^ (1 + α) :=
      Real.div_rpow hρ.le (by norm_num) _
    have e4 : (ρ / 4) ^ (1 + α) = ρ ^ (1 + α) / 4 ^ (1 + α) :=
      Real.div_rpow hρ.le (by norm_num) _
    have hpos2 : 0 < (ρ / 2) ^ (1 + α) := Real.rpow_pos_of_pos hρ2 _
    have hHolK : ∀ u ∈ ball x (ρ / 4), ∀ u' ∈ ball x (ρ / 4),
        ‖g u - g u'‖ ≤ Q / (ρ / 2) ^ (1 + α) * ‖u - u'‖ ^ α := by
      intro u hu u' hu'
      have e : ρ / 2 / 2 = ρ / 4 := by ring
      have h := hP1 x (ρ / 2) hρ2 hx1.le u (by rwa [e]) u' (by rwa [e])
      rw [div_mul_eq_mul_div, le_div_iff₀ hpos2]
      linarith
    have hx4 : ‖x‖ + ρ / 4 ≤ 1 := by linarith
    have e8 : ρ / 4 / 2 = ρ / 8 := by ring
    have h1 := hP2 x (ρ / 4) (Q / (ρ / 2) ^ (1 + α)) hρ4 hx4 hHolK z (by rwa [e8])
      z' (by rwa [e8])
    rw [e4, e2] at h1
    have hd : 0 ≤ ‖z - z'‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
    have key : 1 / 16 * (ρ ^ (1 + α) / 4 ^ (1 + α)) * (Q / (ρ ^ (1 + α) / 2 ^ (1 + α)))
        = Q * 2 ^ (1 + α) / (16 * 4 ^ (1 + α)) := by
      field_simp
    rw [key] at h1
    have h2 : ρ ^ (1 + α) * ‖g z - g z'‖
        ≤ (Q * 2 ^ (1 + α) / 16 + A * 4 ^ (1 + α)) * ‖z - z'‖ ^ α := by
      have h3 := mul_le_mul_of_nonneg_left h1 p4pos.le
      calc ρ ^ (1 + α) * ‖g z - g z'‖
          = 4 ^ (1 + α) * (ρ ^ (1 + α) / 4 ^ (1 + α) * ‖g z - g z'‖) := by
            field_simp
        _ ≤ 4 ^ (1 + α) * ((Q * 2 ^ (1 + α) / (16 * 4 ^ (1 + α)) + A) * ‖z - z'‖ ^ α) := h3
        _ = (Q * 2 ^ (1 + α) / 16 + A * 4 ^ (1 + α)) * ‖z - z'‖ ^ α := by
            field_simp
    calc ρ ^ (1 + α) * ‖g z - g z'‖
        ≤ (Q * 2 ^ (1 + α) / 16 + A * 4 ^ (1 + α)) * ‖z - z'‖ ^ α := h2
      _ ≤ (Q / 4 + 16 * A) * ‖z - z'‖ ^ α := by
          apply mul_le_mul_of_nonneg_right _ hd
          have q1 := mul_le_mul_of_nonneg_left p2le hQ0
          have q2 := mul_le_mul_of_nonneg_left p4le hA
          linarith
  -- Step 4: sup bound
  have hsupfine : ∀ x ∈ ball y (ρ / 2), ρ * ‖g x‖ ≤ 32 * M + (Q / 4 + 16 * A) / 16 ^ α := by
    intro x hx
    have hx1 := hxnorm x hx
    have hK0 : 0 ≤ (Q / 4 + 16 * A) / ρ ^ (1 + α) := div_nonneg hH0 hR.le
    have hHol8 : ∀ z ∈ ball x (ρ / 8), ∀ z' ∈ ball x (ρ / 8),
        ‖g z - g z'‖ ≤ (Q / 4 + 16 * A) / ρ ^ (1 + α) * ‖z - z'‖ ^ α := by
      intro z hz z' hz'
      have h := hsmall x hx z hz z' hz'
      rw [div_mul_eq_mul_div, le_div_iff₀ hR]
      linarith
    have h := hP3 x (ρ / 8) (ρ / 16) ((Q / 4 + 16 * A) / ρ ^ (1 + α)) (by linarith) hK0
      (by positivity) (by linarith) hHol8
    have e16 : (ρ / 16) ^ α = ρ ^ α / 16 ^ α := Real.div_rpow hρ.le (by norm_num) _
    rw [e16, hsplit] at h
    have p16 : (0:ℝ) < 16 ^ α := by positivity
    have p16ne : (16:ℝ) ^ α ≠ 0 := p16.ne'
    have hραne : ρ ^ α ≠ 0 := hρα.ne'
    have hρne : ρ ≠ 0 := hρ.ne'
    have hid : ρ * (2 * M / (ρ / 16) + ρ ^ α / 16 ^ α * ((Q / 4 + 16 * A) / (ρ * ρ ^ α)))
        = 32 * M + (Q / 4 + 16 * A) / 16 ^ α := by
      field_simp
      ring
    calc ρ * ‖g x‖
        ≤ ρ * (2 * M / (ρ / 16) + ρ ^ α / 16 ^ α * ((Q / 4 + 16 * A) / (ρ * ρ ^ α))) :=
          mul_le_mul_of_nonneg_left h hρ.le
      _ = 32 * M + (Q / 4 + 16 * A) / 16 ^ α := hid
  have h16 : (1:ℝ) ≤ 16 ^ α := Real.one_le_rpow (by norm_num) hα0.le
  refine ⟨?_, ?_⟩
  · intro x hx
    have h := hsupfine x hx
    have : (Q / 4 + 16 * A) / 16 ^ α ≤ Q / 4 + 16 * A := div_le_self hH0 h16
    linarith
  · intro x hx x' hx'
    have hd : 0 ≤ ‖x - x'‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
    by_cases hcase : ‖x - x'‖ < ρ / 8
    · have hxin : x ∈ ball x (ρ / 8) := mem_ball_self (by positivity)
      have hx'in : x' ∈ ball x (ρ / 8) := by
        rw [mem_ball, dist_comm, dist_eq_norm]; exact hcase
      have h := hsmall x hx x hxin x' hx'in
      calc ρ ^ (1 + α) * ‖g x - g x'‖ ≤ (Q / 4 + 16 * A) * ‖x - x'‖ ^ α := h
        _ ≤ (Q / 2 + 512 * M + 32 * A) * ‖x - x'‖ ^ α := by
          apply mul_le_mul_of_nonneg_right _ hd; linarith
    · push Not at hcase
      have hdl : (ρ / 8) ^ α ≤ ‖x - x'‖ ^ α := Real.rpow_le_rpow (by positivity) hcase hα0.le
      have e8 : (ρ / 8) ^ α = ρ ^ α / 8 ^ α := Real.div_rpow hρ.le (by norm_num) _
      have p8 : (0:ℝ) < 8 ^ α := by positivity
      have p16 : (0:ℝ) < 16 ^ α := by positivity
      have hρα8 : ρ ^ α ≤ 8 ^ α * ‖x - x'‖ ^ α := by
        rw [e8, div_le_iff₀ p8] at hdl; linarith
      have h8 : (8:ℝ) ^ α ≤ 8 := by
        calc (8:ℝ) ^ α ≤ 8 ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hα1
          _ = 8 := Real.rpow_one 8
      have h816 : (8:ℝ) ^ α ≤ 16 ^ α := Real.rpow_le_rpow (by norm_num) (by norm_num) hα0.le
      have hA1 : ρ ^ α ≤ 8 * ‖x - x'‖ ^ α := by
        have := mul_le_mul_of_nonneg_right h8 hd
        linarith
      have hA2 : ρ ^ α / 16 ^ α ≤ ‖x - x'‖ ^ α := by
        have := mul_le_mul_of_nonneg_right h816 hd
        rw [div_le_iff₀ p16]
        linarith
      have hsx := hsupfine x hx
      have hsx' := hsupfine x' hx'
      have htri : ‖g x - g x'‖ ≤ ‖g x‖ + ‖g x'‖ := norm_sub_le _ _
      calc ρ ^ (1 + α) * ‖g x - g x'‖ = ρ ^ α * (ρ * ‖g x - g x'‖) := by rw [hsplit]; ring
        _ ≤ ρ ^ α * (ρ * ‖g x‖ + ρ * ‖g x'‖) := by
            apply mul_le_mul_of_nonneg_left _ hρα.le
            rw [← mul_add]
            exact mul_le_mul_of_nonneg_left htri hρ.le
        _ ≤ ρ ^ α * (2 * (32 * M + (Q / 4 + 16 * A) / 16 ^ α)) := by
            apply mul_le_mul_of_nonneg_left _ hρα.le
            linarith
        _ = 64 * M * ρ ^ α + 2 * (Q / 4 + 16 * A) * (ρ ^ α / 16 ^ α) := by ring
        _ ≤ 64 * M * (8 * ‖x - x'‖ ^ α) + 2 * (Q / 4 + 16 * A) * ‖x - x'‖ ^ α :=
            add_le_add (mul_le_mul_of_nonneg_left hA1 (by linarith))
              (mul_le_mul_of_nonneg_left hA2 (by linarith))
        _ = (Q / 2 + 512 * M + 32 * A) * ‖x - x'‖ ^ α := by ring

## Key steps

1. points x of B_{rho/2}(y) satisfy |x| + rho/2 < 1, so (x, rho/2) and (x, rho/4) are admissible and |x| + rho/8 <= 1
2. (P1) at (x, rho/2) gives the Hoelder constant K' = Q/(rho/2)^{1+alpha} on B_{rho/4}(x)
3. (P2) at (x, rho/4) with K' gives rho^{1+alpha} ||g(z) - g(z')|| <= (Q/4 + 16A) |z - z'|^alpha on B_{rho/8}(x), using 2^{1+alpha} <= 4 and 4^{1+alpha} <= 16
4. (P3) with r = rho/8, t = rho/16 gives rho ||g(x)|| <= 32M + (Q/4 + 16A)/16^alpha, hence (a)
5. (b) by cases |x - x'| < rho/8 (small-ball bound) and |x - x'| >= rho/8 (sup bound, rho^alpha <= 8 |x - x'|^alpha, rho^alpha/16^alpha <= |x - x'|^alpha)

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; cmp <snapshot>/project/GMT/Ch05/Contract.lean GMT/Ch05/Submission.lean`
- `rg -n '^def HolderOnWith|^def HolderWith' and rg -n '^(theorem|lemma|protected theorem|protected lemma) (HolderOnWith|HolderWith)?\.?(comp|smul|dist_le|mono)' <snapshot>/mathlib/Mathlib/Topology/MetricSpace/Holder.lean`
- `rg -il 'absorption|absorb' <snapshot>/mathlib/Mathlib <snapshot>/project`
- `rg -n -i 'holder|hölder|campanato|schauder' <snapshot>/project (*.lean)`
- `rg -l -i 'interior estimate|C\^\{1,\s*α\}|schauder estimate|blow-?up' <snapshot>/mathlib/Mathlib`
- `rg -n '^theorem le_csSup |^theorem csSup_le |le_csSup_of_le|theorem csSup_le' <snapshot>/mathlib/Mathlib/Order/ConditionallyCompleteLattice/Basic.lean`
- `rg -n '^theorem (div_rpow|mul_rpow|rpow_add|one_rpow|zero_rpow|rpow_pos_of_pos|rpow_nonneg|rpow_le_rpow|rpow_le_one|one_le_rpow|rpow_le_rpow_of_exponent_le|inv_rpow|rpow_two) ' <snapshot>/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`
- `rg -n "theorem ball_subset_ball'|theorem mem_ball_self" <snapshot>/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean; grep 'add_sub_cancel|mul_div_cancel' <snapshot>/mathlib/Mathlib/Algebra/Group/Basic.lean`
- `python3 gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch05.main_theorem') to obtain the replayed child scope; python3 scan of dag.json for collisions of the 4 proposed lean_names and for the sibling statuses/frozen types`
- `lake env lean Checks/AllChallenges.lean, Checks/Assembly.lean, Checks/Proof_<key>.lean for the 4 keys; in a scratch Submission copy with the children appended: lake build GMT.Ch05.Submission, then Checks/Sol_<key>.lean, Checks/Chal_<key>.lean, Checks/Sol_parent.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Holder.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Order/ConditionallyCompleteLattice/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Algebra/Group/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Order/Lattice.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Tactic/Linarith/Frontend.lean`

Pins: the snapshot fixes project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The workspace Submission.lean is byte-identical to the snapshot Contract.lean.

No relevant library result exists at the pin, so the children must be proved:
- 'absorption|absorb' matches only algebraic and lattice absorption laws (e.g. Order/Lattice.lean). There is no analytic absorption lemma.
- 'interior estimate|schauder estimate|blow-up' matches only tactic documentation (e.g. 'exponential blowup' in Tactic/Linarith/Frontend.lean).
- The project's Hoelder matches are only the contract definitions IsHolderCkα and IsLocallyHolderCkα (Contract.lean:84, 92).
- Mathlib's HolderOnWith (Topology/MetricSpace/Holder.lean:57) uses ℝ≥0 constants and edist, and its comp (line 105) multiplies exponents. It cannot express rho^{1+alpha}-weighted quotients with real constants, so the children state explicit inequalities in the style of the frozen parent.

Mathlib lemmas used in the verified child proofs:
- le_csSup and csSup_le (ConditionallyCompleteLattice/Basic.lean:197, 201).
- Real.rpow_pos_of_pos, zero_rpow, one_rpow, rpow_nonneg, rpow_add, rpow_two, mul_rpow, div_rpow, rpow_le_rpow, rpow_le_rpow_of_exponent_le, rpow_le_one, one_le_rpow (Pow/Real.lean, lines 116-677).
- Metric.ball_subset_ball' and mem_ball_self (Pseudo/Defs.lean:537, 379).
- add_sub_cancel, the to_additive form of mul_div_cancel (Group/Basic.lean:962).

The four proposed lean_names do not occur in dag.json (486 nodes at check time).

Lean checks on scratch builds at the pin:
1. All four child types and the frozen parent type elaborate in the comparator's replayed scope.
2. The frozen parent type is proved with the four child types and the three sibling types as hypotheses. Axioms: propext, Classical.choice, Quot.sound.
3. Each child is proved outright (absorption from holder_improvement). Each closes its generated NodeSolution target by `exact Submission.X` with the same three axioms.
4. Instance checks: (ρ • Φ u) P = ρ * Φ u P holds by rfl, and ‖T‖ on L(R^n,R^l) is the operator norm. smul_sub on L(R^n,R^l) needs `set_option maxSynthPendingDepth 3`.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: https://github.com/ZhengyangZhang06/gmt-formalize/pull/4524

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
