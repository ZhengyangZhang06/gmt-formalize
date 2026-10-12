<!-- theorem-id: gmt-ch05/root.lipschitz_graph_corollary-a1.density_monotonicity-a1 -->

## Theorem `Submission.lgc_density_monotonicity`

For n >= 1, l >= 0 and p > n there are delta_0 in (0, 1/8] and C_0 >= 0, depending only on n, l, p, such that: whenever U is open, V = v(M, theta) is a RectifiableVarifold n l U with generalized mean curvature H in U, 0 < delta <= delta_0 and AllardHypotheses H p delta rho (Simon 2.3) hold, then, with mu = V.weight, omega_n = unitBallVolume n, closed balls B_s(y) and p_x = V.tangentProj x: (i) mu(B_s(y)) <= 2 omega_n s^n for all y with |y| <= 3 delta rho and all 0 < s <= rho/2; (ii) mu(B_s(y)) >= omega_n s^n / 2 for all y in spt V with |y| <= 3 delta rho and all 0 < s <= rho/2; (iii) for all y with |y| <= 3 delta rho and all 0 < s <= r <= rho/2: r^-n mu(B_r(y)) <= e^2 s^-n mu(B_s(y)) + C_0 delta + e^2 * (integral over B_r(y) \ B_s(y) of |(x - y) - p_x(x - y)|^2 / |x - y|^(n+2) dmu(x)), where the ball masses are taken as real numbers (toReal) and the integral is the Bochner integral.

Node: `root.lipschitz_graph_corollary-a1.density_monotonicity-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/115

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/716

Decomposition children: None

## Lean problem

Declaration: `Submission.lgc_density_monotonicity`

```lean
∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∃ δ₀ C₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 8 ∧ 0 ≤ C₀ ∧ ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), 0 < δ → δ ≤ δ₀ → V.AllardHypotheses H p δ ρ → (∀ y : Amb n ℓ, ‖y‖ ≤ 3 * δ * ρ → ∀ s : ℝ, 0 < s → s ≤ ρ / 2 → V.weight (closedBall y s) ≤ ENNReal.ofReal (2 * unitBallVolume n * s ^ n)) ∧ (∀ y ∈ V.support, ‖y‖ ≤ 3 * δ * ρ → ∀ s : ℝ, 0 < s → s ≤ ρ / 2 → ENNReal.ofReal (unitBallVolume n * s ^ n / 2) ≤ V.weight (closedBall y s)) ∧ (∀ y : Amb n ℓ, ‖y‖ ≤ 3 * δ * ρ → ∀ s r : ℝ, 0 < s → s ≤ r → r ≤ ρ / 2 → (r ^ n)⁻¹ * (V.weight (closedBall y r)).toReal ≤ Real.exp 2 * ((s ^ n)⁻¹ * (V.weight (closedBall y s)).toReal) + C₀ * δ + Real.exp 2 * ∫ x in closedBall y r \ closedBall y s, ‖(x - y) - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2) ∂V.weight)
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

- Parent DAG node: `root.lipschitz_graph_corollary-a1`
- Child DAG node: `root.lipschitz_graph_corollary-a1.density_monotonicity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the parent proof's facts (M) and (P) (Simon Ch. 5, 2.4, with explicit constants), specialized to the three estimates used by the Lipschitz graph corollary, and the monotonicity identity of Simon Ch. 4, Section 4 (4.1-4.8), whose cutoff argument and passage eps -> 0 are those of Ch. 4, 3.3-3.6 (the cutoff phi, the squeeze 3.5 and the limit 3.6). Item (iii) is the inequality used in the parent's step 5(b) (book: 2.6 (9)), written for general radii. Two corrections to the printed Ch. 4 text are applied.
(1) The coefficient in front of Lambda in 4.2 is kappa = (p-n)/(4p), the value required by the integration after 4.4 (SimonGMT Chapter04 lpMeanCurvatureKappa).
(2) Under the contract's convention (integral of div_M X dmu = - integral of <X, H> dmu), the radial first-variation identity 4.1 carries the PLUS curvature pairing: with a(t) := t^-n I(t) and E(t) := t^(-n-1) C(t), one has a' = t^-n J' + E, where the book prints a minus sign. Consequently the cancellation factor is F = exp(integral of F_0) with F_0 := -E/(1 + a), i.e. F(t) = exp(- integral_0^t E(u)/(1 + a(u)) du).
The derivation is carried out directly for the contract's RectifiableVarifold. It uses only:
- the contract's fields nullMeasurableSet_carrier, mult_pos, aemeasurable_mult and integrableOn_mult;
- HasGeneralizedMeanCurvature;
- the sibling child tangent_plane_ae;
- general measure-theoretic facts from Mathlib.
No result about the stronger SimonGMT Chapter04.RectifiableVarifold is used, so no bridge is needed. Its corrected lemmas are cited only for comparison:
- cutoffMass_deriv_identity (n I - t I' = -t J' - C), Chapter04/MeanCurvature.lean:251;
- hasDerivAt_normalizedCutoffMass (doc: 'Corrected Simon (4.3.16) ... plus the stated mean-curvature error'), Chapter04/MeanCurvature.lean:283-286;
- cutoffCancellationFactor = exp(- integral of the coefficient), Chapter04/LpCancellation.lean:162;
- cancelledCutoffMass_squeeze and exists_cancellationFactor_squeeze_of_lt (the squeeze route of step M7), Chapter04/LpCancellation.lean:400 and Chapter04/LpAnnular.lean:47.

Notation.
- mu := V.weight = theta H^n restricted to M (M = V.carrier, theta = V.mult); spt V := V.support = U ∩ spt mu.
- p_x := V.tangentProj x and p_x^perp v := v - p_x v.
- B_t(z) := closedBall z t (closed) and B^o_t(z) := ball z t (open).
- omega_n := unitBallVolume n > 0, the volume of the closed unit ball of R^n.
- K(z,t) := V.scaledLpNorm H p z t = (t^(p-n) * integral over B_t(z) of |H|^p dmu)^(1/p), in [0, infinity].
- kappa := (p-n)/(4p) in (0, 1/4); e := exp(1).

Facts used.
(F1) [sibling child tangent_plane_ae] (a) x -> p_x is mu-a.e. strongly measurable. (b) For mu-a.e. x there is an n-dimensional subspace T_x with HasWeightedApproximateTangentSpaceAt n M theta x T_x (Simon Ch. 3, Def. 1.7) and p_x = T_x.starProjection. Hence, for mu-a.e. x, p_x is the orthogonal projection onto an n-dimensional subspace. Then:
- p_x is self-adjoint and idempotent, trace p_x = n, and <v, p_x v> = |p_x v|^2 = |v|^2 - |p_x^perp v|^2;
- for every vector a, the rank-one map v -> <a, p_x v> a has trace <a, p_x a> = |a|^2 - |p_x^perp a|^2.
By the definition of tangentProj, every p_x is an orthogonal projection or 0, so |p_x^perp v| <= |v| for all x and v.
(F1') [density at a.e. point; Simon Ch. 3, Rem. 1.8(2)] For mu-a.e. z: liminf as t -> 0+ of t^-n mu(B_t(z)) >= omega_n theta(z).
 Proof. By (F2), mu(R^(n+l) \ M) = 0, so mu-a.e. z lies in M ⊆ U and satisfies (F1)(b). Fix such z with tangent plane T, and fix eta in (0,1). Let f(w) := min{1, max{0, (1 - |w|)/eta}}. This is a compactly supported continuous function with 0 <= f <= 1, f = 1 on B_{1-eta}(0) and f = 0 off B^o_1(0).
 Let t > 0 be so small that B_t(z) ⊆ U, and let eta_{z,t}(x) := (x - z)/t (SimonGMT blowUpMap z t).
- Change of variables. eta_{z,t} is a measurable equivalence (an affine similarity of ratio 1/t), and H^n(eta_{z,t}(S)) = t^-n H^n(S) for every set S. This is translation invariance (Mathlib Isometry.euclideanHausdorffMeasure_image) combined with homothety scaling (Mathlib MeasureTheory.euclideanHausdorffMeasure_homothety_image); SimonGMT Chapter04 hausdorff_blowUp_image (TangentDensity.lean:31) combines the two in the same way. Hence H^n restricted to eta_{z,t}(M) is t^-n times the push-forward of H^n restricted to M (Mathlib MeasurableEquiv.restrict_map), and the integral over eta_{z,t}(M) of h dH^n equals t^-n times the integral over M of (h o eta_{z,t}) dH^n.
- Density. mu = (H^n restricted to M) with density ofReal o theta, where ofReal o theta is AEMeasurable (V.aemeasurable_mult) and (ofReal theta(x)).toReal = theta(x) on M. So the integral of g dmu equals the integral over M of g theta dH^n for bounded g vanishing off B_t(z) (Mathlib integral_withDensity_eq_integral_toReal_smul₀). Such integrals are finite, because theta is H^n-integrable on M ∩ B_t(z) (V.integrableOn_mult); in particular the Bochner integrals of Def. 1.7 are genuine integrals.
- Since f((x - z)/t) <= the indicator of B_t(z), these two facts give
 integral over eta_{z,t}(M) of f(w) theta(z + t w) dH^n(w) = t^-n * integral over M of f((x - z)/t) theta(x) dH^n(x) = t^-n * integral of f((x - z)/t) dmu(x) <= t^-n mu(B_t(z)).
 (Only this inequality is used below.)
 By Def. 1.7 the left side tends, as t -> 0+, to theta(z) * integral over T of f dH^n >= theta(z) H^n(T ∩ B_{1-eta}(0)) = theta(z) omega_n (1-eta)^n. Here H^n on the n-plane T is n-dimensional Lebesgue measure (Mathlib euclideanHausdorffMeasure_coe_image, InnerProductSpace.euclideanHausdorffMeasure_eq_volume), and the closed unit n-ball has volume omega_n (Mathlib InnerProductSpace.volume_closedBall). Letting eta -> 0 gives the claim.
(F2) [measure facts]
- mu(R^(n+l) \ M) = 0. M is H^n-null-measurable (V.nullMeasurableSet_carrier), so H^n restricted to M is carried by M (Mathlib ae_restrict_mem₀), and mu, a with-density measure of H^n restricted to M, is absolutely continuous with respect to it.
- mu(K) < infinity for every compact K ⊆ U, since mu(K) is the integral of theta over M ∩ K (V.integrableOn_mult).
- H is mu-integrable on compact subsets of U (LocallyIntegrableOn H U, part of HasGeneralizedMeanCurvature).
- If z in spt mu, then mu(B^o_eta(z)) > 0 for every eta > 0 (Mathlib Measure.mem_support_iff_forall).
- If mu(B_{t_1}(z)) < infinity and t_k decreases to t, then mu(B_{t_k}(z)) -> mu(B_t(z)): the closed balls decrease to the closed ball B_t(z), so continuity from above applies (Mathlib tendsto_measure_iInter_atTop).

Part I. The corrected monotonicity identity (M) for the contract's varifold.

M0. Setting. Let y in R^(n+l), R > 0 and Lambda > 0 with B_R(y) ⊆ U and K(y,R) <= kappa Lambda. Assume V has generalized mean curvature H in U.
 For x in R^(n+l) write rho_x := |x - y|. Put w(x) := |p_x^perp(x - y)|^2/rho_x^2 for x != y, and w(y) := 0. By (F1), 0 <= w <= 1 and w(x) rho_x^-n = |p_x^perp(x - y)|^2/|x - y|^(n+2) for x != y. By (F1)(a), x -> p_x agrees mu-a.e. with a Borel map (AEStronglyMeasurable.mk), so w agrees mu-a.e. with a Borel function. Clamp that function to [0,1] and set its value at y to 0. It stays Borel and still agrees with w mu-a.e., because w itself takes values in [0,1] and w(y) = 0. Replacing w by it changes none of the mu-integrals below, so we take w Borel with 0 <= w <= 1 and w(y) = 0.
 By (F2), m_R := mu(B_R(y)) < infinity and H is mu-integrable on B_R(y). Put ||H||_R := (lintegral over B_R(y) of |H|^p dmu)^(1/p). Then ||H||_R = R^(n/p - 1) K(y,R) <= kappa Lambda R^(n/p - 1) < infinity.
 Put g(t) := kappa Lambda R^-1 (t/R)^(-n/p) for t > 0. Since n/p < 1 and kappa p/(p-n) = 1/4, we have integral_0^t g = (Lambda/4)(t/R)^(1-n/p) <= Lambda/4 for 0 < t <= R.
 Sharp quantities, for 0 < t <= R and 0 < s <= r < R:
 I(t) := mu(B_t(y));
 C(t) := integral over B_t(y) of <x - y, H(x)> dmu(x);
 a(t) := t^-n I(t);
 E(t) := t^(-n-1) C(t);
 F_0(t) := -E(t)/(1 + a(t));
 F(t) := exp(integral_0^t F_0(u) du) = exp(- integral_0^t E(u)/(1 + a(u)) du);
 Phi(t) := F(t) a(t) + F(t) - 1;
 A(s,r) := integral over B_r(y) \ B_s(y) of |p_x^perp(x - y)|^2 |x - y|^(-n-2) dmu(x).
 F is well defined. Write C = C^+ - C^-, where C^(+/-)(t) := integral over B_t(y) of the positive/negative part of <x - y, H(x)>; these integrands are integrable on B_R(y). The functions t -> I(min{t, R}) and t -> C^(+/-)(min{t, R}) are nondecreasing on all of R (closed balls of negative radius are empty), hence Borel (Mathlib Monotone.measurable). So a, E and F_0 are Borel on (0, R]. Moreover rho_x <= t on B_t(y), so by Hoelder's inequality for lintegrals (Mathlib ENNReal.lintegral_mul_le_Lp_mul_Lq, exponents p and p/(p-1)) |C(t)| <= t * integral over B_t(y) of |H| dmu <= t ||H||_R I(t)^(1-1/p). Hence |E(t)| <= ||H||_R t^(-n/p) a(t)^(1-1/p) <= g(t)(1 + a(t)), using a^(1-1/p) <= 1 + a. So |F_0| <= g on (0, R], which is integrable.
 For 0 < s <= r < R, the set B_r(y) \ B_s(y) = {s < rho_x <= r} has finite measure. On it the integrand of A(s,r) is mu-a.e. strongly measurable and lies in [0, s^-n]. So A(s,r) is a finite nonnegative Bochner integral. It is literally the integral in the statement, since (x - y) - p_x(x - y) = p_x^perp(x - y).

M1. Cutoffs. Let psi(v) := 1 for v <= 0, psi(v) := 1 - 3v^2 + 2v^3 for 0 <= v <= 1, and psi(v) := 0 for v >= 1. Then psi is C^1 with 0 <= psi <= 1; psi' = -6v(1-v) <= 0 on [0,1], psi' = 0 elsewhere, and |psi'| <= 3/2.
 For eps in (0,1] put phi_eps(u) := psi((u - 1)/eps). Then:
- phi_eps is C^1, nonincreasing and valued in [0,1];
- phi_eps = 1 on (-infinity, 1] and phi_eps = 0 on [1 + eps, infinity);
- phi_eps' vanishes outside (1, 1 + eps) and |phi_eps'| <= 3/(2 eps);
- for every u, phi_eps(u) tends to the indicator of (-infinity, 1] at u as eps -> 0+ (it is 1 for u <= 1, and 0 as soon as eps < u - 1 when u > 1).

M2. Radial first variation for the contract's varifold. Fix eps in (0,1] and t > 0 with (1+eps) t <= R. Let X(x) := phi_eps(rho_x/t)(x - y).
 X is C^1: it equals x - y on the open ball B^o_t(y), and on R^(n+l) \ {y} it is a composition of C^1 maps. X vanishes off B_{(1+eps)t}(y), so it has compact support and tsupport X ⊆ B_R(y) ⊆ U; DX vanishes off B^o_{(1+eps)t}(y).
 DX(y) = I, and for x != y, DX(x) v = phi_eps(rho_x/t) v + (t rho_x)^-1 phi_eps'(rho_x/t) <x - y, v> (x - y). Hence, at every x where p_x is a rank-n orthogonal projection (mu-a.e. by (F1)), the trace facts of (F1) give
 div_M X(x) = trace(DX(x) o p_x) = n phi_eps(rho_x/t) + (rho_x/t) phi_eps'(rho_x/t)(1 - w(x)).
 At x = y both sides equal n.
 div_M X is bounded and vanishes outside B_R(y). It is mu-a.e. strongly measurable, because x -> DX(x) is continuous, x -> p_x is mu-a.e. strongly measurable, and composition and trace are continuous. Also |<X, H>| <= R |H| times the indicator of B_R(y). So both Bochner integrals in the contract's HasGeneralizedMeanCurvature are genuine integrals. The identity integral of div_M X dmu = - integral of <X, H> dmu becomes
 (1) n I_eps(t) + integral of (rho_x/t) phi_eps'(rho_x/t)(1 - w(x)) dmu(x) = -C_eps(t),
 where I_eps(t) := integral of phi_eps(rho_x/t) dmu, J_eps(t) := integral of phi_eps(rho_x/t) w(x) dmu, and C_eps(t) := integral of phi_eps(rho_x/t) <x - y, H(x)> dmu(x).

M3. The corrected radial identity. For fixed x, the map t -> phi_eps(rho_x/t) is C^1 on (0, infinity) with derivative d_t phi_eps(rho_x/t) = (rho_x/t^2)(-phi_eps'(rho_x/t)) >= 0. This derivative vanishes unless t < rho_x < (1+eps) t.
 Fix t_0 in (0, R/(1+eps)) and choose 0 < t_1 < t_0 < t_2 < R/(1+eps). For t in (t_1, t_2):
- the integrands phi_eps(rho_x/t) and phi_eps(rho_x/t) w(x) are mu-a.e. strongly measurable, bounded by 1 and vanish off B_R(y), so they are integrable (m_R < infinity);
- their t-derivatives are bounded by 3(1+eps)/(2 eps t_1) times the indicator of B_R(y), which is integrable.
 So differentiation under the integral sign (Mathlib hasDerivAt_integral_of_dominated_loc_of_deriv_le) shows that I_eps and J_eps are differentiable on (0, R/(1+eps)) with
 I_eps'(t) = integral of (rho_x/t^2)(-phi_eps'(rho_x/t)) dmu >= 0 and J_eps'(t) = integral of (rho_x/t^2)(-phi_eps'(rho_x/t)) w(x) dmu >= 0.
 Both derivatives are continuous in t, by dominated convergence. C_eps is continuous on (0, R/(1+eps)], by dominated convergence with majorant R |H| times the indicator of B_R(y).
 Since (rho_x/t) phi_eps'(rho_x/t) = -t d_t phi_eps(rho_x/t), identity (1) reads
 (2) n I_eps(t) - t I_eps'(t) + t J_eps'(t) = -C_eps(t).
 This is the radial identity with the plus curvature pairing; it agrees with SimonGMT cutoffMass_deriv_identity. With a_eps(t) := t^-n I_eps(t) and E_eps(t) := t^(-n-1) C_eps(t), we have a_eps' = t^(-n-1)(t I_eps' - n I_eps), so (2) gives
 (3) a_eps'(t) = t^-n J_eps'(t) + E_eps(t) for 0 < t < R/(1+eps).
 The printed 4.1 has a minus sign in front of the curvature term. With the contract's convention the sign is plus, as just computed.

M4. Hoelder bound for the coefficient. Let 0 < t <= R/(1+eps). On the support of phi_eps(rho_x/t) we have rho_x < (1+eps) t <= R. Write phi_eps = phi_eps^(1/p) phi_eps^(1-1/p). Apply Hoelder's inequality for lintegrals (Mathlib ENNReal.lintegral_mul_le_Lp_mul_Lq) with exponents p and p/(p-1) (p > n >= 1) to the nonnegative functions phi_eps(rho_x/t)^(1/p)|H| and phi_eps(rho_x/t)^(1-1/p). All quantities are finite, so the bound holds for the real integrals:
 |C_eps(t)| <= (1+eps) t * integral of phi_eps(rho_x/t)|H| dmu <= (1+eps) t (integral of phi_eps(rho_x/t)|H|^p dmu)^(1/p) I_eps(t)^(1-1/p) <= (1+eps) t ||H||_R I_eps(t)^(1-1/p).
 Using ||H||_R t^(-n/p) <= g(t) and a^(1-1/p) <= 1 + a for a >= 0:
 |E_eps(t)| <= (1+eps) ||H||_R t^(-n/p) a_eps(t)^(1-1/p) <= (1+eps) g(t)(1 + a_eps(t)).

M5. Corrected cancellation (integrating factor). On (0, R/(1+eps)) define F_{0,eps}(t) := -E_eps(t)/(1 + a_eps(t)). It is continuous (1 + a_eps >= 1), and |F_{0,eps}| <= (1+eps) g <= 2g, which is integrable near 0. Define
 F_eps(t) := exp(integral_0^t F_{0,eps}(u) du) = exp(- integral_0^t E_eps(u)/(1 + a_eps(u)) du).
 Then F_eps is C^1 with F_eps' = F_eps F_{0,eps}, and by (3)
 d/dt [F_eps (1 + a_eps)] = F_eps F_{0,eps}(1 + a_eps) + F_eps a_eps' = -F_eps E_eps + F_eps (t^-n J_eps' + E_eps) = F_eps t^-n J_eps'.
 The curvature terms cancel exactly because the minus sign in F_{0,eps} matches the plus pairing in (3).
 Let Phi_eps := F_eps (1 + a_eps) - 1 = F_eps a_eps + F_eps - 1. Its derivative is continuous, so the fundamental theorem of calculus gives, for 0 < s <= r < R/(1+eps),
 (4) Phi_eps(r) - Phi_eps(s) = integral_s^r F_eps(t) t^-n J_eps'(t) dt =: D_eps(s,r).
 Moreover |integral_0^t F_{0,eps}| <= (1+eps) * integral_0^t g <= (1+eps) Lambda/4. Hence e^(-(1+eps)Lambda/4) <= F_eps(t) <= e^((1+eps)Lambda/4) for 0 < t < R/(1+eps).

M6. Squeeze. Let 0 < s < r < R/(1+eps). The function (t,x) -> F_eps(t) t^-n d_t phi_eps(rho_x/t) w(x) is nonnegative and Borel: continuous in (t,x) times the Borel function w (M0). It vanishes for x outside B_R(y), so every mu-integral of it may be taken with respect to the finite measure mu restricted to B_R(y). By M3 and Tonelli for Lebesgue measure on [s, r] times that finite measure (Mathlib lintegral_lintegral_swap),
 D_eps(s,r) = integral of w(x) [integral_s^r F_eps(t) t^-n d_t phi_eps(rho_x/t) dt] dmu(x).
 Fix x != y. The factor d_t phi_eps(rho_x/t) >= 0 vanishes unless rho_x/(1+eps) < t < rho_x, where rho_x^-n <= t^-n <= (1+eps)^n rho_x^-n. Also integral_s^r d_t phi_eps(rho_x/t) dt = phi_eps(rho_x/r) - phi_eps(rho_x/s) >= 0. The point x = y contributes nothing, because w(y) = 0. With the bounds on F_eps from M5 this gives
 (5) e^(-(1+eps)Lambda/4) A_eps(s,r) <= D_eps(s,r) <= e^((1+eps)Lambda/4) (1+eps)^n A_eps(s,r),
 where A_eps(s,r) := integral over {x != y} of w(x) rho_x^-n (phi_eps(rho_x/r) - phi_eps(rho_x/s)) dmu(x) >= 0.

M7. Passage eps -> 0 to the closed-ball annular identity. Fix 0 < s < r < R and a sequence eps_k decreasing to 0 with eps_1 <= 1 and (1 + eps_1) r < R. Then (4) and (5) hold for every eps_k, and the eps_k-objects are defined on (0, r].
 (a) Pointwise limits. For 0 < t <= r and every x, phi_{eps_k}(rho_x/t) tends to the indicator of B_t(y) at x (M1), and 0 <= phi_{eps_k}(rho_x/t) <= the indicator of B_R(y). By dominated convergence (Mathlib tendsto_integral_of_dominated_convergence), with majorants the indicator of B_R(y) and R |H| times that indicator, I_{eps_k}(t) -> I(t) = mu(B_t(y)) and C_{eps_k}(t) -> C(t). Hence a_{eps_k}(t) -> a(t), E_{eps_k}(t) -> E(t) and F_{0,eps_k}(t) -> F_0(t) for every t in (0, r].
 (b) The factor. By M0, F_0 is Borel with |F_0| <= g on (0, R], and by (a) F_{0,eps_k} -> F_0 pointwise on (0, r]. By dominated convergence in u (majorant 2g), integral_0^t F_{0,eps_k} -> integral_0^t F_0 for t in (0, r]. Hence F_{eps_k}(t) -> F(t), and Phi_{eps_k}(t) = F_{eps_k}(t)(1 + a_{eps_k}(t)) - 1 -> Phi(t) for t in {s, r}.
 (c) The annular integral. The integrand of A_{eps_k}(s,r) vanishes if rho_x <= s (both cutoff values are 1) and if rho_x >= (1 + eps_k) r (both are 0). Otherwise s < rho_x < R and the integrand lies in [0, s^-n], so s^-n times the indicator of B_R(y) is an integrable majorant.
 For x != y, phi_{eps_k}(rho_x/r) - phi_{eps_k}(rho_x/s) tends to the indicator of {rho_x <= r} minus the indicator of {rho_x <= s}. That is the indicator of {s < rho_x <= r} = B_r(y) \ B_s(y). Hence A_{eps_k}(s,r) -> integral over B_r(y) \ B_s(y) of w(x) rho_x^-n dmu = A(s,r).
 The closed-ball annulus appears because phi_eps = 1 on (-infinity, 1], so the limits are indicators of the closed balls {rho_x <= t}, matching the closed balls of the contract.
 (d) Letting k -> infinity in (4) and (5):
 (6) e^(-Lambda/4) A(s,r) <= Phi(r) - Phi(s) <= e^(Lambda/4) A(s,r) for 0 < s < r < R.
 (6) holds trivially for s = r.

M8. Consequences (the facts (M) of the parent proof). For 0 < s <= r < R:
 (M.i) |integral_0^t F_0| <= integral_0^t g = (Lambda/4)(t/R)^(1-n/p) <= Lambda/4. Hence e^-Lambda <= e^(-Lambda/4) <= F(t) <= e^(Lambda/4) <= e^Lambda. By |e^u - 1| <= e^|u| |u|, |F(t) - 1| <= e^(Lambda/4)(Lambda/4)(t/R)^(1-n/p). Since e^(1/4)/4 < 1, Lambda <= 1 implies |F(t) - 1| <= Lambda (t/R)^(1-n/p) <= Lambda. Also F(t) -> 1 as t -> 0+.
 (M.ii) Phi(r) - Phi(s) = G(s,r) A(s,r) for some G(s,r) in [e^-Lambda, e^Lambda]. If A(s,r) > 0, take G(s,r) := (Phi(r) - Phi(s))/A(s,r) and use (6). If A(s,r) = 0, then Phi(r) = Phi(s) by (6), and take G(s,r) := 1.
 (M.iii) By (6), Phi is nondecreasing on (0,R), and Phi >= F - 1 >= e^-Lambda - 1 > -1. So Phi(0+) := lim as t -> 0+ of Phi(t) exists, and Phi(0+) <= Phi(t) for all t in (0,R). As F(t) -> 1, a(t) = (Phi(t) + 1)/F(t) - 1 -> Phi(0+). That is, the limit of t^-n mu(B_t(y)) as t -> 0+ exists and is <= Phi(r) for every r in (0,R).
 (M.v) If Lambda <= 1: Phi(s) <= Phi(r) gives
 F(s) a(s) = Phi(s) - (F(s) - 1) <= Phi(r) + Lambda = F(r) a(r) + (F(r) - 1) + Lambda <= e^Lambda a(r) + 2 Lambda.
 Dividing by F(s) >= e^-Lambda: a(s) <= e^(2 Lambda) a(r) + 2 e^Lambda Lambda.
 (M.vi) If Lambda <= 1: lim as t -> 0+ of a(t) <= Phi(s) = F(s) a(s) + F(s) - 1 <= e^Lambda a(s) + Lambda.
 (M.vii) If Lambda <= 1: by (M.ii) and G <= e^Lambda,
 F(r) a(r) = Phi(r) - (F(r) - 1) <= Phi(s) + e^Lambda A(s,r) + Lambda = F(s) a(s) + (F(s) - 1) + e^Lambda A(s,r) + Lambda <= e^Lambda a(s) + 2 Lambda + e^Lambda A(s,r).
 Dividing by F(r) >= e^-Lambda: a(r) <= e^(2 Lambda) a(s) + 2 e^Lambda Lambda + e^(2 Lambda) A(s,r).

Part II. Proof of the statement.
1. Constants. Put delta_0 := min{kappa/8, kappa omega_n/8, 1/(24 n)} and C_0 := 2e/kappa = 8 e p/(p - n). Both depend only on n and p. Then 0 < delta_0 <= kappa/8 < 1/32 <= 1/8 and C_0 >= 0.
2. Setup. Let 0 < delta <= delta_0 and let 2.3 hold: rho > 0, V has generalized mean curvature H in U, theta >= 1 mu-a.e., 0 in spt V, B_rho(0) ⊆ U, mu(B_rho(0)) <= (1 + delta) omega_n rho^n and K(0, rho) <= delta. Put Lambda := delta/kappa. Then Lambda <= 1/8, Lambda <= omega_n/8, 3 n delta <= 1/8 and delta <= 1/32.
 (K) Let z in R^(n+l) and R' > 0 with |z| + R' <= rho. Then B_{R'}(z) ⊆ B_rho(0) ⊆ U, and, using p > n and R' <= rho,
 K(z,R')^p = R'^(p-n) * integral over B_{R'}(z) of |H|^p dmu <= rho^(p-n) * integral over B_rho(0) of |H|^p dmu = K(0,rho)^p <= delta^p.
 So K(z,R') <= delta = kappa Lambda, and Part I applies at (z, R', Lambda), with Lambda <= 1. All balls below lie in B_rho(0), so their masses are finite and equal their real values (toReal).
3. Proof of (i). Let |y| <= 3 delta rho and 0 < s <= rho/2. Put R_y := (1 - 3 delta) rho >= (29/32) rho > rho/2 >= s. Since |y| + R_y <= rho, Part I applies at (y, R_y, Lambda) by (K).
 For every r in [s, R_y), (M.v) gives a(s) <= e^(2 Lambda) a(r) + 2 e^Lambda Lambda. Since B_r(y) ⊆ B_rho(0), a(r) <= r^-n mu(B_rho(0)) <= (1 + delta) omega_n (rho/r)^n. Letting r increase to R_y,
 a(s) <= e^(2 Lambda)(1 + delta)(1 - 3 delta)^-n omega_n + 2 e^Lambda Lambda.
 We bound each factor, using e^x <= 1/(1 - x) for 0 <= x < 1:
- e^(2 Lambda) <= e^(1/4) <= 4/3, and 1 + delta <= 33/32;
- by Bernoulli (Mathlib one_add_mul_le_pow), (1 - 3 delta)^n >= 1 - 3 n delta >= 7/8, so (1 - 3 delta)^-n <= 8/7;
- 2 e^Lambda Lambda <= 2 e^(1/8) omega_n/8 <= 2 (8/7) omega_n/8 = (2/7) omega_n.
 Hence a(s) <= (4/3)(33/32)(8/7) omega_n + (2/7) omega_n = (11/7 + 2/7) omega_n = (13/7) omega_n <= 2 omega_n, i.e. mu(B_s(y)) <= 2 omega_n s^n.
4. Proof of (ii). Let y in spt V with |y| <= 3 delta rho and 0 < s <= rho/2. Call z good if z in M, theta(z) >= 1 and the conclusion of (F1') holds at z. Each condition holds mu-a.e. (by (F2), 2.3 and (F1')), so there is a measurable mu-null set N containing every point that is not good.
 For k >= 1 put eta_k := rho/(8k). Since y in spt mu, (F2) gives mu(B^o_{eta_k}(y) \ N) = mu(B^o_{eta_k}(y)) > 0. So there is z_k in B^o_{eta_k}(y) \ N; it is good and |z_k - y| < eta_k.
 Put R_k := (1 - 3 delta) rho - eta_k >= (29/32 - 4/32) rho > rho/2 >= s. Since |z_k| + R_k < rho, Part I applies at (z_k, R_k, Lambda) by (K).
 By (M.iii), the limit of t^-n mu(B_t(z_k)) as t -> 0+ exists, and by (F1') and theta(z_k) >= 1 it is >= omega_n. Then (M.vi) at z_k with radius s < R_k, together with B_s(z_k) ⊆ B_{s + eta_k}(y), gives
 omega_n <= e^Lambda s^-n mu(B_s(z_k)) + Lambda <= e^Lambda s^-n mu(B_{s + eta_k}(y)) + Lambda.
 The closed balls B_{s + eta_k}(y) decrease to B_s(y) and are contained in B_rho(0), since |y| + s + eta_1 <= (3/32 + 1/2 + 1/8) rho < rho. Letting k -> infinity, (F2) gives omega_n <= e^Lambda s^-n mu(B_s(y)) + Lambda. Using Lambda <= omega_n/8, Lambda <= 1/8 and e^(-x) >= 1 - x,
 s^-n mu(B_s(y)) >= e^-Lambda (omega_n - Lambda) >= e^(-1/8)(7/8) omega_n >= (7/8)^2 omega_n = (49/64) omega_n >= omega_n/2.
 Hence mu(B_s(y)) >= omega_n s^n/2.
5. Proof of (iii). Let |y| <= 3 delta rho and 0 < s <= r <= rho/2. As in step 3, Part I applies at (y, R_y, Lambda), and r <= rho/2 < R_y. By (M.vii),
 r^-n mu(B_r(y)) <= e^(2 Lambda) s^-n mu(B_s(y)) + 2 e^Lambda Lambda + e^(2 Lambda) A(s,r).
 Since Lambda <= 1 and a(s), A(s,r) >= 0, the right side is at most e^2 s^-n mu(B_s(y)) + 2 e Lambda + e^2 A(s,r), and 2 e Lambda = (2e/kappa) delta = C_0 delta. By M0, A(s,r) is the Bochner integral of |(x - y) - p_x(x - y)|^2/|x - y|^(n+2) over B_r(y) \ B_s(y), and all ball masses are finite. This is (iii). QED

## Key steps

1. (F1) from tangent_plane_ae: mu-a.e. p_x is a rank-n orthogonal projection, and x -> p_x is a.e. strongly measurable; (F1'): liminf t^-n mu(B_t(z)) >= omega_n theta(z) for mu-a.e. z, from the weighted tangent plane; (F2): mu(M^c) = 0, mu finite on compacts, positivity on the support, continuity from above on closed balls
2. Radial first variation of X = phi_eps(|x-y|/t)(x-y) under the contract's convention: n I_eps - t I_eps' + t J_eps' = -C_eps, i.e. a_eps' = t^-n J_eps' + E_eps with the plus curvature pairing
3. Hoelder: |E_eps| <= (1+eps) g (1 + a_eps), where g(t) = kappa Lambda R^-1 (t/R)^(-n/p) and integral_0^t g = (Lambda/4)(t/R)^(1-n/p)
4. Corrected cancellation: F_{0,eps} = -E_eps/(1+a_eps), F_eps = exp(integral F_{0,eps}), (F_eps(1+a_eps))' = F_eps t^-n J_eps', hence Phi_eps(r) - Phi_eps(s) = integral_s^r F_eps t^-n J_eps'
5. Tonelli squeeze: e^(-(1+eps)Lambda/4) A_eps <= Phi_eps(r) - Phi_eps(s) <= e^((1+eps)Lambda/4)(1+eps)^n A_eps
6. eps -> 0 by dominated convergence: I_eps -> mu(B_t(y)), C_eps -> C, F_eps -> F = exp(-integral E/(1+a)), and A_eps -> the integral over the closed-ball annulus B_r(y) minus B_s(y); hence e^(-Lambda/4) A <= Phi(r) - Phi(s) <= e^(Lambda/4) A
7. Consequences: |F - 1| <= Lambda; Phi is nondecreasing and the density limit exists; the comparison inequalities (M.v), (M.vi) and (M.vii)
8. Constants delta_0 = min{kappa/8, kappa omega_n/8, 1/(24n)} and C_0 = 2e/kappa; every ball B_{R'}(z) inside B_rho(0) has K(z,R') <= delta = kappa Lambda
9. (i): (M.v) with r -> (1 - 3 delta) rho and the mass bound of 2.3 give mu(B_s(y)) <= (13/7) omega_n s^n
10. (ii): (M.vi) at good points z_k -> y, then continuity from above, give mu(B_s(y)) >= (49/64) omega_n s^n
11. (iii): (M.vii) with Lambda <= 1 gives the factors e^2 and 2 e Lambda = C_0 delta

## Reference use

### local-project

Queries:
- `diff <snapshot>/project/GMT/Ch05/Contract.lean GMT/Ch05/Contract.lean (identical); diff GMT/Ch05/Submission.lean GMT/Ch05/Contract.lean (identical)`
- `grep -o '"lgc_[a-z_]*"' <run>/dag.json (no match); python3 listing of every dag.json node id, status and lean_name, plus the lean_statements of aal_lp_monotonicity, aal_tangent_structure, aal_density_ge_one, aal_pinched_density_bounds and rectifiableVarifold_ae_tangentProj_starProjection`
- `grep -n 'theorem HasGeneralizedMeanCurvatureIn.cutoffMass_deriv_identity\|theorem HasGeneralizedMeanCurvatureIn.hasDerivAt_normalizedCutoffMass\b\|Corrected Simon (4.3.16)\|^def cutoffCancellationFactor\|theorem HasGeneralizedMeanCurvatureIn.hasDerivAt_cancelledCutoffMass\|theorem HasGeneralizedMeanCurvatureIn.exists_cancellationFactor_squeeze_of_lt\|structure LpAnnularCorrection\|theorem HasGeneralizedMeanCurvatureIn.cancelledCutoffMass_squeeze\|def lpMeanCurvatureKappa\|def monotonicityCutoff\|theorem integral_lpCurvatureCoefficientBound\|theorem tendsto_cutoffDefect_difference\|theorem tendsto_cutoffMass' .lake/packages/simongmt/Poincare/SimonGMT/Chapter04/*.lean`
- `grep -rn sorry .lake/packages/simongmt/Poincare/SimonGMT/Chapter04/Lp*.lean | wc -l (0)`
- `sed -n 240,330p .lake/packages/simongmt/Poincare/SimonGMT/Chapter04/MeanCurvature.lean; sed -n 1,330p .lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpCancellation.lean; sed -n 1,420p .lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpAnnular.lean; sed -n 395,420p .lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpCancellation.lean`
- `grep -n 'structure RectifiableVarifold' -A 40 .lake/packages/simongmt/Poincare/SimonGMT/Chapter04/Basic.lean`
- `sed -n 1,120p and sed -n 280,420p .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -n 'theorem hausdorff_blowUp_image\|theorem .*blowUp' .lake/packages/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `rg -n 'μHE\[' <snapshot>/mathlib/Mathlib (timed out after 120 s; replaced by the targeted greps below)`
- `grep -n 'theorem\|lemma\|notation\|def ' .lake/packages/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean; diff -q against <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (identical)`
- `timeout 100 grep -rn 'theorem hasDerivAt_integral_of_dominated_loc_of_deriv_le\b\|theorem tendsto_integral_of_dominated_convergence\b\|theorem integral_integral_swap\b\|theorem InnerProductSpace.euclideanHausdorffMeasure_eq_volume\|theorem euclideanHausdorffMeasure_coe_image\|lemma measure_compl_support' on ParametricIntegral.lean, DominatedConvergence.lean, Integral/Prod.lean, Geometry/Euclidean/Volume/Measure.lean, Measure/Support.lean`
- `timeout 100 grep -rn 'theorem integral_hasDerivAt_right\b\|theorem MeasureTheory.euclideanHausdorffMeasure_homothety_image\|theorem lintegral_mul_le_Lp_mul_Lq \|theorem lintegral_lintegral_swap \|theorem add_one_le_exp \|lemma mem_support_iff_forall\|lemma one_add_mul_le_pow\|theorem volume_closedBall\|tendsto_measure_iInter_atTop' on the corresponding <snapshot>/mathlib/Mathlib files; grep -rln 'theorem tendsto_measure_iInter_atTop' <snapshot>/mathlib/Mathlib/MeasureTheory/`
- `timeout 60 grep -rn 'theorem integral_withDensity_eq_integral_toReal_smul\b\|theorem integral_withDensity_eq_integral_toReal_smul₀\|theorem ae_restrict_mem₀\|theorem LocallyIntegrableOn.integrableOn_compact_subset\|theorem Monotone.measurable\|theorem restrict_map\b' on Bochner/ContinuousLinearMap.lean, Function/LocallyIntegrable.lean, Measure/Restrict.lean, BorelSpace/Order.lean`
- `grep -n '^3\.[0-9]' and sed -n 250,560p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `lake env lean -o /tmp/lgc-v2-check/olean/GMT/Ch05/Submission.olean GMT/Ch05/Submission.lean`
- `LEAN_PATH=/tmp/lgc-v2-check/olean:$(lake env printenv LEAN_PATH) lean /tmp/lgc-v2-check/src/Types.lean`
- `LEAN_PATH=/tmp/lgc-v2-check/olean:$(lake env printenv LEAN_PATH) lean /tmp/lgc-v2-check/src/Asm.lean (with #print axioms GMT.Ch05.Submission.lipschitz_graph_corollary)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-graph-corollary-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-graph-corollary-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-affine-approximation-a1-lp-monotonicity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/MeanCurvature.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpCancellation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpAnnular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpMeanCurvature.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/MeanInequalities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Algebra/Order/Ring/Pow.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Complex/Exponential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/tmp/lgc-v2-check/src/Types.lean`
- `/tmp/lgc-v2-check/src/Asm.lean`
- `/tmp/lgc-v2-scripts/density_monotonicity_proof.txt`

Snapshot and names. manifest.json pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The snapshot Contract.lean equals the workspace Contract.lean, and Submission.lean equals Contract.lean. No lgc_ name occurs in the snapshot or in dag.json. Related nodes in other branches (aal_lp_monotonicity, aal_tangent_structure, aal_pinched_density_bounds, rectifiableVarifold_ae_tangentProj_starProjection) carry different names and types.

Book versus library. The printed text (chapter-04.txt) has 4.1 with a minus curvature term and the integrating factor exp(+integral F_0) in 4.3-4.4. The pinned SimonGMT corrects this:
- cutoffMass_deriv_identity (Chapter04/MeanCurvature.lean:251) gives n I - rho I' = -rho J' - C.
- hasDerivAt_normalizedCutoffMass (MeanCurvature.lean:283-286) is documented as 'Corrected Simon (4.3.16) ... plus'.
- cutoffCancellationFactor (LpCancellation.lean:162) is exp(-integral).
- cancelledCutoffMass_squeeze (LpCancellation.lean:400) and exists_cancellationFactor_squeeze_of_lt (LpAnnular.lean:47) are the squeeze-and-limit route.
- lpMeanCurvatureKappa = (p-n)/(4p) (LpMeanCurvature.lean:76).
- Chapter04/Lp*.lean contains no sorry.
These results are stated for Chapter04.RectifiableVarifold, which has a measurable carrier, a stored tangent field and a globally locally finite weight (Basic.lean:53-72). They are therefore used only as cross-checks, and the corrected child proof re-derives (M) for the contract's varifold. hausdorff_blowUp_image (TangentDensity.lean:31) models the blow-up scaling.

Mathlib items used by the corrected proof, all present in the snapshot:
- hasDerivAt_integral_of_dominated_loc_of_deriv_le (ParametricIntegral.lean:286)
- tendsto_integral_of_dominated_convergence (DominatedConvergence.lean:57)
- integral_hasDerivAt_right (FundThmCalculus.lean:725)
- ENNReal.lintegral_mul_le_Lp_mul_Lq (MeanInequalities.lean:202)
- lintegral_lintegral_swap (Measure/Prod.lean:1071)
- integral_withDensity_eq_integral_toReal_smul₀ (Bochner/ContinuousLinearMap.lean:311)
- ae_restrict_mem₀ and MeasurableEquiv.restrict_map (Restrict.lean:637, 910)
- LocallyIntegrableOn.integrableOn_compact_subset (LocallyIntegrable.lean:122)
- Monotone.measurable (BorelSpace/Order.lean:790)
- mem_support_iff_forall and measure_compl_support (Support.lean:75, 202)
- tendsto_measure_iInter_atTop (Measure/Continuity.lean:220)
- one_add_mul_le_pow (Ring/Pow.lean:99) and add_one_le_exp (Complex/Exponential.lean:632)
- the notation μHE[d], Isometry.euclideanHausdorffMeasure_image, MeasureTheory.euclideanHausdorffMeasure_homothety_image, InnerProductSpace.euclideanHausdorffMeasure_eq_volume and euclideanHausdorffMeasure_coe_image (Geometry/Euclidean/Volume/Measure.lean:72, 131, 164, 191, 226)
- volume_closedBall (VolumeOfBalls.lean:324, 354)
A whole-tree rg for μHE[ timed out, so the targeted greps above were used instead.

Lean (lean-4.35.0-rc3). The five child types elaborate after importing GMT.Ch05.Submission. The parent assembly compiles to GMT.Ch05.Submission.lipschitz_graph_corollary : GMT.Ch05.LipschitzGraphCorollary, with axioms propext, sorryAx, Classical.choice and Quot.sound; sorry occurs only in the five children and the sibling placeholder.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
