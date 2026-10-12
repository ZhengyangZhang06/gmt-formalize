<!-- theorem-id: gmt-ch05/root.lipschitz_approximation-a1.monotonicity-a1 -->

## Theorem `Submission.lip_approx_monotonicity`

Let n >= 1, l, p > n, U open, V a contract rectifiable varifold in U with generalized mean curvature H, delta > 0 and rho such that 2.3 (AllardHypotheses H p delta rho) holds, and Lambda with 4 p delta/(p - n) <= Lambda <= 1. Let y in R^(n+l), R > 0 with B_R(y) contained in B_rho(0), and 0 < s <= r < R. With mu = V.weight and closed balls: (I) s^-n mu(B_s(y)) <= e^(2 Lambda) r^-n mu(B_r(y)) + 2 e^Lambda Lambda; (II) r^-n mu(B_r(y)) <= e^(2 Lambda) s^-n mu(B_s(y)) + 2 e^Lambda Lambda + e^(2 Lambda) integral over B_r(y) minus B_s(y) of |(x - y) - p_x(x - y)|^2 |x - y|^(-n-2) dmu(x); (III) if y in spt V then e^(-Lambda)(omega_n - Lambda) <= s^-n mu(B_s(y)).

Node: `root.lipschitz_approximation-a1.monotonicity-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/114

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/692

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/744, https://github.com/ZhengyangZhang06/gmt-formalize/issues/710, https://github.com/ZhengyangZhang06/gmt-formalize/issues/747

## Lean problem

Declaration: `Submission.lip_approx_monotonicity`

```lean
∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ Λ : ℝ), 0 < δ → V.AllardHypotheses H p δ ρ → 4 * p * δ / (p - n) ≤ Λ → Λ ≤ 1 → ∀ (y : Amb n ℓ) (R : ℝ), 0 < R → closedBall y R ⊆ closedBall 0 ρ → ∀ s r : ℝ, 0 < s → s ≤ r → r < R → V.weight.real (closedBall y s) / s ^ n ≤ Real.exp (2 * Λ) * (V.weight.real (closedBall y r) / r ^ n) + 2 * Real.exp Λ * Λ ∧ V.weight.real (closedBall y r) / r ^ n ≤ Real.exp (2 * Λ) * (V.weight.real (closedBall y s) / s ^ n) + 2 * Real.exp Λ * Λ + Real.exp (2 * Λ) * ∫ x in closedBall y r \ closedBall y s, ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2) ∂V.weight ∧ (y ∈ V.support → Real.exp (-Λ) * (unitBallVolume n - Λ) ≤ V.weight.real (closedBall y s) / s ^ n)
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

- Parent DAG node: `root.lipschitz_approximation-a1`
- Child DAG node: `root.lipschitz_approximation-a1.monotonicity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 4, 3.1-3.6 (radial test field) and 4.1-4.10 (L^p mean curvature), with the coefficient in front of Lambda in 4.2 equal to kappa = (p-n)/(4p), the value required by the integration after 4.4 (as in SimonGMT Chapter04 lpMeanCurvatureKappa / LpAnnularCorrection). This is facts (M.i)-(M.v) of the parent proof, in the form used there. To avoid fixing one integrating factor in the limit eps -> 0, all estimates are derived for each cutoff and only the eps-independent bounds are passed to the limit.

Notation. mu := V.weight; p_x := V.tangentProj x; p_x^perp := I - p_x; omega_n := unitBallVolume n; kappa := (p-n)/(4p) > 0; K(z,t) := (t^(p-n) integral_(B_t(z)) |H|^p dmu)^(1/p) (V.scaledLpNorm H p z t); B_t(z) closed balls. Hypotheses: n >= 1, p > n, U open, V has generalized mean curvature H in U, 2.3 holds (AllardHypotheses H p delta rho, so rho > 0, B_rho(0) contained in U, theta >= 1 mu-a.e., 0 in spt V, K(0,rho) <= delta), delta > 0, 4p delta/(p-n) <= Lambda <= 1 (so Lambda > 0 and kappa Lambda >= delta), B_R(y) contained in B_rho(0), R > 0, 0 < s <= r < R.

0. Preliminaries.
 (0a) Since R > 0 and B_R(y) is contained in B_rho(0), |y| <= rho - R; in particular R <= rho and y lies in the open ball B^o_rho(0).
 (0b) If t > 0 and B_t(z) is contained in B_rho(0), then t <= rho and K(z,t)^p = t^(p-n) integral_(B_t(z)) |H|^p <= (t/rho)^(p-n) rho^(p-n) integral_(B_rho(0)) |H|^p <= (t/rho)^(p-n) delta^p, so K(z,t) <= (t/rho)^(1-n/p) delta <= kappa Lambda (t/rho)^(1-n/p). In particular integral_(B_rho(0)) |H|^p dmu < infinity.
 (0c) mu(B) < infinity for every closed ball B contained in B_rho(0) (compact subset of U), and H is mu-integrable on such balls (HasGeneralizedMeanCurvature includes local integrability of H on U).
 (0d) By the tangent-structure child (lip_approx_tangent_structure): x -> p_x is mu-a.e. strongly measurable, and for mu-a.e. x, p_x is the orthogonal projection onto an n-dimensional subspace and mu(B_t(x))/(omega_n t^n) -> theta(x) as t -> 0+. For every x, p_x is 0 or an orthogonal projection, so |p_x^perp v| <= |v|.

1. Cutoffs and the functions I, J, e. Let z be a point and R_z > 0 with B_(R_z)(z) contained in B_rho(0), and let Lambda_z in (0,1] satisfy K(z,R_z) <= kappa Lambda_z. Fix eps in (0,1] and phi in C^1(R, [0,1]) with phi = 1 on (-infinity, 1], phi = 0 on [1+eps, infinity), phi' <= 0 (for instance phi(u) = psi((u-1)/eps) with psi(v) = 1 for v <= 0, 1 - 3v^2 + 2v^3 for 0 <= v <= 1, 0 for v >= 1); then integral (-phi') = 1. For t in (0, R_z/(1+eps)) put
 I(t) := integral phi(|x - z|/t) dmu(x), J(t) := integral phi(|x - z|/t) g(x) dmu(x), g(x) := |p_x^perp(x - z)|^2/|x - z|^2 (g(z) := 0), e(t) := t^(-n-1) integral phi(|x - z|/t) <x - z, H(x)> dmu(x).
 The integrands vanish outside B_((1+eps)t)(z), contained in B_(R_z)(z), are mu-measurable by (0d), and 0 <= g <= 1. With psi_t(x) := d/dt[phi(|x - z|/t)] = -(|x - z|/t^2) phi'(|x - z|/t) >= 0 and |psi_t| <= (1+eps) sup|phi'|/t, differentiation under the integral sign (dominated convergence, mu(B_(R_z)(z)) < infinity) shows that I and J are C^1 with I'(t) = integral psi_t dmu and J'(t) = integral psi_t g dmu >= 0, and e is continuous (dominated by |x - z||H| on B_(R_z)(z)).
2. Radial test field (Simon 3.2). X_t(x) := phi(|x - z|/t)(x - z). It is C^1 (phi(|x - z|/t) = 1 on the open ball B^o_t(z), and |x - z| is smooth away from z), has compact support and tsupport X_t is contained in B_((1+eps)t)(z), a subset of U. For x with r_x := |x - z| > 0, DX_t(x)v = phi(r_x/t) v + (phi'(r_x/t)/(t r_x)) <x - z, v> (x - z); near z, DX_t = identity. Hence at every x where p_x is the orthogonal projection onto an n-dimensional subspace (mu-a.e. by (0d)), using trace(p_x) = n, trace((v -> <a,v> b) o p_x) = <a, p_x b> and <v, p_x v> = |p_x v|^2 = |v|^2 - |p_x^perp v|^2:
 divM X_t(x) = trace(DX_t(x) o p_x) = n phi(r_x/t) + (r_x/t) phi'(r_x/t)(1 - g(x)) = n phi(r_x/t) - t psi_t(x) + t psi_t(x) g(x).
3. First variation (Simon 3.14, 4.1). X_t is admissible in the definition of generalized mean curvature, so integral divM X_t dmu = - integral <X_t, H> dmu. By step 2 this reads n I(t) - t I'(t) + t J'(t) = - t^(n+1) e(t), i.e.
 (3.1) (t^-n I(t))' = t^-n J'(t) + e(t) for t in (0, R_z/(1+eps)).
4. Hoelder estimate (Simon 4.2-4.3 with kappa). On the support of phi(|x - z|/t), |x - z| <= (1+eps)t <= 2t and phi^(p/(p-1)) <= phi. Hoelder gives |e(t)| <= 2 t^-n (integral_(B_(R_z)(z)) |H|^p)^(1/p) I(t)^(1-1/p) = 2 t^(-n/p) (integral_(B_(R_z)(z)) |H|^p)^(1/p) (t^-n I(t))^(1-1/p). As R_z^(1-n/p) (integral_(B_(R_z)(z)) |H|^p)^(1/p) = K(z,R_z) <= kappa Lambda_z and a^(1-1/p) <= 1 + a for a >= 0:
 (4.1) |e(t)| <= 2 kappa Lambda_z R_z^-1 (t/R_z)^(-n/p) (1 + t^-n I(t)).
5. Integrating factor (Simon 4.3-4.6). Put a(t) := -e(t)/(1 + t^-n I(t)), continuous with |a(t)| <= 2 kappa Lambda_z R_z^-1 (t/R_z)^(-n/p), which is integrable near 0 because n/p < 1. Let A(t) := integral_0^t a and F(t) := exp(A(t)). Since integral_0^t 2 kappa Lambda_z R_z^-1 (tau/R_z)^(-n/p) dtau = 2 kappa Lambda_z (p/(p-n)) (t/R_z)^(1-n/p) = (Lambda_z/2)(t/R_z)^(1-n/p), we get |A(t)| <= (Lambda_z/2)(t/R_z)^(1-n/p) <= Lambda_z/2, hence
 (5.1) e^(-Lambda_z/2) <= F(t) <= e^(Lambda_z/2) and |F(t) - 1| <= e^(|A|) |A| <= Lambda_z (t/R_z)^(1-n/p) <= Lambda_z (as e^(1/2)/2 < 1 and Lambda_z <= 1).
 Let Phi(t) := F(t) t^-n I(t) + F(t) - 1 = F(t)(t^-n I(t) + 1) - 1. By (3.1), Phi' = F a (t^-n I + 1) + F (t^-n J' + e) = F t^-n J' >= 0, because a (t^-n I + 1) = -e. Hence for 0 < s' <= r' < R_z/(1+eps):
 (5.2) Phi(r') - Phi(s') = integral_(s')^(r') F(t) t^-n J'(t) dt, which lies in [0, e^(Lambda_z/2) integral_(s')^(r') t^-n J'(t) dt].
6. The annular integral (Simon 3.5-3.6). By Tonelli, integral_(s')^(r') t^-n J'(t) dt = integral g(x) (integral_(s')^(r') t^-n psi_t(x) dt) dmu(x). For x != z with rho_x := |x - z|, the substitution u = rho_x/t gives integral_(s')^(r') t^-n psi_t(x) dt = rho_x^-n integral_(rho_x/r')^(rho_x/s') u^n (-phi'(u)) du. Since -phi' >= 0 vanishes off [1, 1+eps] and has integral 1, this is 0 if rho_x <= s' or rho_x >= (1+eps) r', and at most (1+eps)^n rho_x^-n otherwise. Therefore
 (6.1) integral_(s')^(r') t^-n J'(t) dt <= (1+eps)^n D_eps(s',r'), D_eps(s',r') := integral_(B_((1+eps)r')(z) minus B_(s')(z)) |p_x^perp(x - z)|^2 |x - z|^(-n-2) dmu(x).
7. Inequalities for fixed eps. From (5.1), (5.2), (6.1), for 0 < s' <= r' < R_z/(1+eps):
 (7.1) F(s') s'^-n I(s') <= F(r') r'^-n I(r') + (F(r') - 1) - (F(s') - 1) <= e^(Lambda_z/2) r'^-n I(r') + 2 Lambda_z, hence s'^-n I(s') <= e^(Lambda_z) r'^-n I(r') + 2 e^(Lambda_z/2) Lambda_z;
 (7.2) F(r') r'^-n I(r') <= F(s') s'^-n I(s') + 2 Lambda_z + e^(Lambda_z/2)(1+eps)^n D_eps(s',r'), hence r'^-n I(r') <= e^(Lambda_z) s'^-n I(s') + 2 e^(Lambda_z/2) Lambda_z + e^(Lambda_z)(1+eps)^n D_eps(s',r').
8. Limit eps -> 0 (general inequalities). Since the indicator of [0,1] <= phi <= indicator of [0,1+eps], mu(B_t(z)) <= I(t) <= mu(B_((1+eps)t)(z)), and mu(B_((1+eps)t)(z)) decreases to mu(B_t(z)) as eps -> 0 (closed balls decrease to the closed ball; finite measure). Similarly D_eps(s',r') decreases to D(s',r') := integral_(B_(r')(z) minus B_(s')(z)) |p_x^perp(x - z)|^2 |x - z|^(-n-2) dmu (integrand <= s'^-n there, finite measure). Given 0 < s' <= r' < R_z, every small eps satisfies (1+eps) r' < R_z, and the constants in (7.1)-(7.2) do not depend on eps. Using mu(B_(s'))<= I(s') and I(r') -> mu(B_(r')) in (7.1), and mu(B_(r')) <= I(r'), I(s') -> mu(B_(s')), (1+eps)^n D_eps -> D in (7.2), we obtain for 0 < s' <= r' < R_z:
 (G1) s'^-n mu(B_(s')(z)) <= e^(Lambda_z) r'^-n mu(B_(r')(z)) + 2 e^(Lambda_z/2) Lambda_z;
 (G2) r'^-n mu(B_(r')(z)) <= e^(Lambda_z) s'^-n mu(B_(s')(z)) + 2 e^(Lambda_z/2) Lambda_z + e^(Lambda_z) D(s',r').
9. First and second assertions. Apply step 8 with z = y, R_z = R, Lambda_z = Lambda; this is allowed because K(y,R) <= kappa Lambda by (0b). Since Lambda >= 0, e^Lambda <= e^(2 Lambda) and e^(Lambda/2) <= e^Lambda, so (G1) and (G2) with s' = s, r' = r give the first two assertions, with mu(B_t(y)) = V.weight.real(closedBall y t) (finite by (0c)) and D(s,r) the integral over closedBall y r minus closedBall y s.
10. Lower density at support points (Simon 4.9, 4.10(1)). Let w in spt V with |w| < rho. Claim: liminf_(tau -> 0) tau^-n mu(B_tau(w)) >= omega_n.
 (10a) By (0d) and theta >= 1 mu-a.e. (2.3), the set Good' of x with mu(B_t(x))/(omega_n t^n) -> theta(x) >= 1 has mu-null complement; at x in Good', t^-n mu(B_t(x)) -> omega_n theta(x) >= omega_n.
 (10b) Let tau > 0 with 3 tau < rho - |w|. For x with |x - w| <= tau, B_(2 tau)(x) is contained in B_rho(0); put Lambda_tau := Lambda (2 tau/rho)^(1-n/p) in (0,1]; by (0b), K(x, 2 tau) <= kappa Lambda_tau, so (G1) applies at z = x, R_z = 2 tau, Lambda_z = Lambda_tau: for 0 < t <= tau, t^-n mu(B_t(x)) <= e^(Lambda_tau) tau^-n mu(B_tau(x)) + 2 e^(Lambda_tau/2) Lambda_tau. If x in Good', letting t -> 0 gives omega_n <= e^(Lambda_tau) tau^-n mu(B_tau(x)) + 2 e^(Lambda_tau/2) Lambda_tau.
 (10c) Since w in spt V is contained in spt mu, every open ball around w has positive mu-measure, so by (10a) there are x_k in Good' with x_k -> w. For |x_k - w| <= tau, B_tau(x_k) is contained in B_(tau + |x_k - w|)(w), and mu(B_(tau + eta)(w)) decreases to mu(B_tau(w)) as eta -> 0. Applying (10b) to x_k and letting k -> infinity: omega_n <= e^(Lambda_tau) tau^-n mu(B_tau(w)) + 2 e^(Lambda_tau/2) Lambda_tau. As tau -> 0, Lambda_tau -> 0, which proves the claim.
11. Third assertion. Let y in V.support and 0 < s < R (s <= r < R). By (0a), |y| < rho, so step 10 applies at w = y. Fix eps with (1+eps)s < R and use the objects of steps 1-7 with z = y, R_z = R, Lambda_z = Lambda. For 0 < t <= s, (5.2) and (5.1) give Phi(s) >= Phi(t) = F(t) t^-n I(t) + F(t) - 1 >= (1 - Lambda (t/R)^(1-n/p)) t^-n mu(B_t(y)) - Lambda (t/R)^(1-n/p) (using I(t) >= mu(B_t(y))). Taking liminf as t -> 0 and using step 10: Phi(s) >= omega_n. Hence F(s) s^-n I(s) >= omega_n - (F(s) - 1) >= omega_n - Lambda. If omega_n - Lambda <= 0 the third assertion holds trivially (its left side is <= 0 <= its right side). Otherwise s^-n I(s) >= (omega_n - Lambda)/F(s) >= e^(-Lambda/2)(omega_n - Lambda) >= e^(-Lambda)(omega_n - Lambda), and as I(s) <= mu(B_((1+eps)s)(y)) -> mu(B_s(y)) when eps -> 0, we get s^-n mu(B_s(y)) >= e^(-Lambda)(omega_n - Lambda).

## Key steps

1. Lp smallness propagates to sub-balls: K(z,t) <= (t/rho)^(1-n/p) delta <= kappa Lambda (t/rho)^(1-n/p)
2. Radial C^1 test field X_t = phi(|x-z|/t)(x-z); divM X_t = n phi - t psi_t + t psi_t g mu-a.e. (tangent-structure child)
3. First variation gives (t^-n I)' = t^-n J' + e
4. Hoelder with kappa = (p-n)/(4p): |e| <= 2 kappa Lambda R^-1 (t/R)^(-n/p)(1 + t^-n I)
5. Integrating factor F with e^(-Lambda/2) <= F <= e^(Lambda/2), |F-1| <= Lambda (t/R)^(1-n/p), and Phi' = F t^-n J' >= 0
6. Tonelli and substitution bound integral t^-n J' by (1+eps)^n times the annular integral
7. Fixed-eps inequalities, then eps -> 0 using right-continuity of closed-ball masses: (G1), (G2)
8. Lower density omega_n at points of spt V via (G1) at nearby density points (theta >= 1 a.e.)
9. Phi(s) >= omega_n gives the third assertion e^-Lambda (omega_n - Lambda) <= s^-n mu(B_s(y))

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json`
- `diff GMT/Ch05/Submission.lean <snapshot>/project/GMT/Ch05/Submission.lean (identical)`
- `grep -n 'def C1Approximation|def WhitneyExtension|def Rademacher' GMT/Ch02/Contract.lean; grep -n sorry GMT/Ch02/Submission.lean`
- `grep -o 'lip_approx_[a-z_]*' dag.json DAG.md dag.mmd issue-workers.json problem.json (no matches)`
- `python3 -I: list dag.json nodes with 'tangent' in id (aal_tangent_structure, rectifiableVarifold_ae_tangentProj_starProjection)`
- `grep -n 'theorem LipschitzWith.ae_differentiableAt' <snapshot>/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `grep -n 'theorem tendstoUniformlyOn_of_ae_tendsto' <snapshot>/mathlib/Mathlib/MeasureTheory/Function/Egorov.lean`
- `grep -n 'theorem measurableSet_of_differentiableAt|theorem measurable_fderiv' <snapshot>/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `grep -rn 'exists_isClosed_diff_lt' <snapshot>/mathlib/Mathlib`
- `grep -rn 'theorem isClosed_iUnion' <snapshot>/mathlib/Mathlib/Topology/LocallyFinite.lean`
- `grep -rn 'theorem contDiff_euclidean|theorem contDiff_piLp' <snapshot>/mathlib/Mathlib`
- `grep -rn 'theorem norm_fderiv_le_of_lipschitz' <snapshot>/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `grep -rn 'theorem ContinuousOn.measurable_piecewise' <snapshot>/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `grep -rn 'norm_image_sub_le_of_norm_fderiv_le' <snapshot>/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `grep -n 'theorem hausdorffMeasure_homothety_image' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `grep -n 'euclideanHausdorffMeasure_eq_volume|def MeasureTheory.Measure.euclideanHausdorffMeasure' <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `grep -rn sorry .lake/packages/simongmt/Poincare/SimonGMT (0 matches); git -C lake-packages-25730c7c/simongmt rev-parse HEAD`
- `grep -n '^theorem|^structure' SimonGMT/Chapter02/WhitneyExtension.lean SimonGMT/Chapter02/WhitneyJet.lean`
- `grep -n '^theorem' -A 12 SimonGMT/Chapter01/Lusin.lean`
- `grep -rn 'theorem simon_theorem_3_6' -A 30 SimonGMT/Chapter01/; grep -n 'def dimensionalDensityQuotient|def dimensionalUpperDensity' SimonGMT/Chapter01/Densities.lean`
- `grep -n 'theorem measure_toOuterMeasure_isBorelRegular' SimonGMT/Chapter01/Basic.lean; grep -n 'simonAreaNormalization' SimonGMT/Chapter02/AreaNormalization.lean`
- `grep -n '^theorem' SimonGMT/Chapter02/{AreaLipschitz,AreaCritical,AreaFormula,AreaNoninjective,Area}.lean; grep -rn 'theorem weighted_area_formula_volume_of_injective_derivative|theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn' SimonGMT/Chapter02`
- `grep -n '^theorem|^def' SimonGMT/Chapter03/{SubmanifoldCover,DisjointCover,Rectifiable}.lean`
- `sed -n 150,290p book/sources/chapter-02-source.txt (printed proof of Thm 1.5); sed -n 1,360p book/sources/chapter-03-source.txt (1.1-1.9)`
- `lean --root=/tmp/lipapprox-dec-v2 -o GMT/Ch05/Submission.olean GMT/Ch05/Submission.lean; lean -o LipApproxAux/WhitneyExtension.olean LipApproxAux/WhitneyExtension.lean (verbatim copy of SimonGMT Chapter02/WhitneyExtension.lean)`
- `lean --root=/tmp/lipapprox-dec-v2 c1a/Api.lean (#check of cited APIs and #print axioms for Whitney and Lusin)`
- `lean --root=/tmp/lipapprox-dec-v2 c1a/C1A.lean (C1ACheck.c1_approx_scalar, C1ACheck.c1_approx; #print axioms)`
- `python3 -I scripts/gen_checks.py decomposition statements (verifier/lean_contract.validate_lean_statement); lean check/lip_approx_*.lean; lean check/All.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch02/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/Egorov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/LocallyFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/WithLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WhitneyJet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaNormalization.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaFormula.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/DisjointCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-02-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-03-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-approximation-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-approximation-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-approximation-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-affine-approximation-a1-tangent-structure-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/lipapprox-dec-v2/c1a/C1A.lean`
- `/tmp/lipapprox-dec-v2/c1a/Api.lean`
- `/tmp/lipapprox-dec-v2/LipApproxAux/WhitneyExtension.lean`
- `/tmp/lipapprox-dec-v2/check/All.lean`

Pinned versions. Snapshot a7f8fcd21d5c8fc7 pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The pinned SimonGMT, 2b3663083f3fe399b6296fb8eaee52169170e197, lies outside the snapshot and contains no sorry. The workspace GMT/Ch05/Submission.lean is byte-identical to the snapshot copy.

C1A has no usable proof anywhere:
- GMT/Ch02/Contract.lean:199 defines C1Approximation, but GMT/Ch02/Submission.lean:377 proves its main_theorem by sorry.
- SimonGMT Chapter03/SubmanifoldCover.lean proves only the C^1-to-rectifiable direction of Lemma 1.2.
So the proof is supplied as Part A of tangent_structure.

Checked ingredients located in Mathlib (paths under mathlib/Mathlib):
- LipschitzWith.ae_differentiableAt (Analysis/Calculus/Rademacher.lean:385);
- measurableSet_of_differentiableAt and measurable_fderiv (Analysis/Calculus/FDeriv/Measurable.lean:372, 378);
- tendstoUniformlyOn_of_ae_tendsto (MeasureTheory/Function/Egorov.lean:205);
- MeasurableSet.exists_isClosed_sdiff_lt (MeasureTheory/Measure/Regular.lean, alias exists_isClosed_diff_lt at :1044);
- LocallyFinite.isClosed_iUnion (Topology/LocallyFinite.lean:128);
- contDiff_euclidean (Analysis/InnerProductSpace/Calculus.lean:339);
- norm_fderiv_le_of_lipschitz (Analysis/Calculus/FDeriv/Basic.lean:947);
- Convex.norm_image_sub_le_of_norm_fderiv_le (Analysis/Calculus/MeanValue.lean:499);
- ContinuousOn.measurable_piecewise (MeasureTheory/Constructions/BorelSpace/Basic.lean:523);
- hausdorffMeasure_homothety_image (MeasureTheory/Measure/Hausdorff.lean:1060);
- EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Geometry/Euclidean/Volume/Measure.lean:187).

Checked ingredients located in SimonGMT (paths under Poincare/SimonGMT):
- Chapter02.exists_contDiff_one_extension_of_whitney (WhitneyExtension.lean:373); its hypothesis HasWhitneyC1Compatibility (WhitneyJet.lean:34) has the fields continuous_value, continuous_derivative and remainder;
- Chapter01.exists_isClosed_continuousOn_of_measurable, the finite-measure Lusin theorem (Lusin.lean:127);
- Chapter01.simon_theorem_3_6 (DensityComparison.lean:332), with its density quotient over closed balls (Densities.lean);
- Chapter01.measure_toOuterMeasure_isBorelRegular (Basic.lean:309);
- simonHausdorffMeasureReal_nat_eq_smul_euclideanHausdorffMeasure and simonAreaNormalization_pos/_ne_top (Chapter02/AreaNormalization.lean:45, 31, 37);
- Chapter02.area_image_criticalSet_eq_zero (AreaCritical.lean:185);
- Chapter02.weighted_area_formula_volume_of_injective_derivative (WeightedArea.lean:120);
- Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn (Lipschitz.lean:216);
- Chapter03.simon_remark_1_3_nullMeasurable (DisjointCover.lean:109);
- Chapter03.HasWeightedApproximateTangentSpaceAt.unique (Rectifiable.lean:345).
None of these is the Chapter04.RectifiableVarifold that the chapter README excludes.

The book's printed proofs are followed: Thm 1.5 at book/sources/chapter-02-source.txt lines 165-270, and Ch. 3, 1.1-1.9.

Lean results:
- /tmp/lipapprox-dec-v2/c1a/C1A.lean compiles with 0 errors and no sorry.
- C1ACheck.c1_approx_scalar, C1ACheck.c1_approx, exists_contDiff_one_extension_of_whitney and exists_isClosed_continuousOn_of_measurable depend only on propext, Classical.choice and Quot.sound.
- All 11 child types elaborate in the contract scope with 0 errors and only sorry warnings, and pass validate_lean_statement.

No lip_approx_ name is reserved anywhere in the DAG. The tangent nodes of other branches, aal_tangent_structure and rectifiableVarifold_ae_tangentProj_starProjection, have different Lean types, so there is no collision and no reuse.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
