<!-- theorem-id: gmt-ch05/root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1 -->

## Theorem `Submission.allard52_annular_monotonicity`

Let n >= 1 and l >= 0 be natural numbers and p a real number with p > n. Let U be an open subset of R^(n+l), V a rectifiable n-varifold in U (contract structure RectifiableVarifold n l U) with weight mu := V.weight and p_x := V.tangentProj x, and H : R^(n+l) -> R^(n+l) such that V has generalized mean curvature H in U (V.HasGeneralizedMeanCurvature H). Let y in R^(n+l) and let R, Lambda be real numbers with R > 0 and closed ball B_R(y) contained in U. Assume (T1) for mu-a.e. x: if x lies in the open ball B°_R(y), then p_x = P.starProjection for some n-dimensional subspace P; (T2) x -> p_x is a.e.-strongly measurable with respect to mu restricted to B°_R(y); 0 < Lambda <= 1; and V.scaledLpNorm H p y R <= ofReal(kappa Lambda) with kappa := (p - n)/(4p), i.e. (R^(p-n) * integral^-_{B_R(y)} |H|^p dmu)^(1/p) <= kappa Lambda in [0, infinity]. Write omega_n := unitBallVolume n, alpha' := 1 - n/p (real exponent), balls closed, and for F : R -> R put Phi(r) := F(r) * (r^n)^(-1) * mu(B_r(y)).toReal + F(r) - 1. Then there exists F : R -> R such that: (i) for every r in (0, R): e^(-Lambda) <= F(r) <= e^Lambda and |F(r) - 1| <= Lambda (r/R)^(alpha'); (ii) for all s, r with 0 < s <= r < R: Phi(s) <= Phi(r), and the lower (extended) integral over B_r(y) minus B_s(y) of ofReal(|x - y - p_x(x - y)|^2 / |x - y|^(n+2)) with respect to mu is at most ofReal(e^Lambda (Phi(r) - Phi(s))); (iii) there is a real t >= 0 with V.HasDensity y t (i.e. mu(B_r(y))/ofReal(omega_n r^n) -> ofReal t as r -> 0+) and omega_n t <= Phi(r) for every r in (0, R).

Node: `root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/580

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2677, https://github.com/ZhengyangZhang06/gmt-formalize/issues/711, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2685, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2692, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2702, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2711, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2717, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2725

## Lean problem

Declaration: `Submission.allard52_annular_monotonicity`

```lean
∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ), V.HasGeneralizedMeanCurvature H → ∀ (y : Amb n ℓ) (R Λ : ℝ), 0 < R → closedBall y R ⊆ U → (∀ᵐ x ∂V.weight, x ∈ ball y R → ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection) → AEStronglyMeasurable (fun x => V.tangentProj x) (V.weight.restrict (ball y R)) → 0 < Λ → Λ ≤ 1 → V.scaledLpNorm H p y R ≤ ENNReal.ofReal ((p - n) / (4 * p) * Λ) → ∃ F : ℝ → ℝ, (∀ r ∈ Ioo 0 R, Real.exp (-Λ) ≤ F r ∧ F r ≤ Real.exp Λ ∧ |F r - 1| ≤ Λ * (r / R) ^ (1 - (n : ℝ) / p)) ∧ (∀ s r : ℝ, 0 < s → s ≤ r → r < R → F s * (s ^ n)⁻¹ * (V.weight (closedBall y s)).toReal + F s - 1 ≤ F r * (r ^ n)⁻¹ * (V.weight (closedBall y r)).toReal + F r - 1 ∧ ∫⁻ x in closedBall y r \ closedBall y s, ENNReal.ofReal (‖x - y - V.tangentProj x (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)) ∂V.weight ≤ ENNReal.ofReal (Real.exp Λ * ((F r * (r ^ n)⁻¹ * (V.weight (closedBall y r)).toReal + F r - 1) - (F s * (s ^ n)⁻¹ * (V.weight (closedBall y s)).toReal + F s - 1)))) ∧ ∃ t : ℝ, 0 ≤ t ∧ V.HasDensity y t ∧ ∀ r ∈ Ioo 0 R, unitBallVolume n * t ≤ F r * (r ^ n)⁻¹ * (V.weight (closedBall y r)).toReal + F r - 1
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

- Parent DAG node: `root.allard_regularity-a1.density_bounds-a1`
- Child DAG node: `root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3 of the parent proof, i.e. the derivation (a)-(d) of the monotonicity facts (M.i)-(M.iii) (Simon, Introduction to GMT, Ch. 4, 4.1-4.9, with the corrected coefficient kappa = (p-n)/(4p) in 4.2; 4.7 is the annular identity), specialized to the present hypotheses: the tangent-plane facts are only used on the open ball B°_R(y), which contains the supports of all test fields. Instead of the parent's compactness extraction in (d), the passage eps -> 0 is done by dominated convergence (which gives convergence of the integrating factors for every radius) and Fatou's lemma (which gives the annular inequality in the direction needed).

Notation. mu := V.weight; B_t := closedBall y t and B°_t := ball y t; r_x := |x - y|; p_x := V.tangentProj x; kappa := (p - n)/(4p); alpha' := 1 - n/p; omega_n := unitBallVolume n; for x != y, nu(x) := |x - y - p_x(x - y)|^2/|x - y|^2, and nu(y) := 0; g(x) := |x - y - p_x(x - y)|^2/|x - y|^(n+2), so g(x) = nu(x) r_x^(-n) for x != y and g(y) = 0 (real division by 0 is 0); m(t) := mu(B_t).toReal. Since 1 <= n < p: p > 0, 0 < n/p < 1, 0 < alpha' < 1, kappa > 0 and 2 kappa/alpha' = 2 (p - n)/(4p) * p/(p - n) = 1/2. Note nu(x) >= 0 for every x.

0. Preliminary facts.
 (a) B_R is compact and contained in U, so mu(B_R) = integral over carrier cap B_R of theta dH^n < infinity (field integrableOn_mult of the structure). Hence mu(B_t) < infinity and mu(B_t) = ofReal(m(t)) for all t <= R.
 (b) HasGeneralizedMeanCurvature H contains LocallyIntegrableOn H U mu; B_R is a compact subset of U, so H is mu-integrable on B_R.
 (c) K := V.scaledLpNorm H p y R = (ofReal(R^(p-n)) * Q)^(1/p) with Q := integral^-_{B_R} |H|^p dmu. Since K <= ofReal(kappa Lambda) < infinity, ofReal(R^(p-n)) > 0 and 1/p > 0, we get Q < infinity, and N := Q^(1/p) (the L^p(mu restricted to B_R) norm of H) satisfies N = R^(n/p - 1) K <= R^(n/p - 1) kappa Lambda.
 (d) By (T1), for mu-a.e. x in B°_R, p_x is the orthogonal projection onto an n-dimensional subspace; at such x, p_x is self-adjoint and idempotent with trace n, v . p_x v = |p_x v|^2 and |v - p_x v|^2 = |v|^2 - |p_x v|^2 <= |v|^2. Hence 0 <= nu(x) <= 1 and (x - y) . p_x(x - y) = r_x^2 (1 - nu(x)) for such x != y.
 (e) By (T2), x -> p_x is a.e.-strongly measurable for mu restricted to B°_R; hence so are nu and g there (continuous operations). Fix a strongly measurable map q : R^(n+l) -> L(R^(n+l)) with q = p mu-a.e. on B°_R. Replacing p_x by q(x) in nu and g changes them only on a mu-null subset of B°_R. Every integrand below that involves nu or g vanishes outside B°_R, so the replacement changes none of the integrals below and makes all of their integrands measurable.

1. Cutoffs. Let psi(u) := 1 for u <= 0, psi(u) := 1 - 3u^2 + 2u^3 for 0 <= u <= 1, psi(u) := 0 for u >= 1. Then psi is C^1 (psi'(u) = 6u(u - 1) on [0, 1], which vanishes at 0 and 1), nonincreasing, with values in [0, 1] and |psi'| <= 3/2. For eps in (0, 1) put phi_eps(u) := psi((u - 1)/eps). Then phi_eps is C^1 and nonincreasing, 0 <= phi_eps <= 1, phi_eps = 1 on (-infinity, 1], phi_eps = 0 on [1 + eps, infinity), phi_eps' <= 0, phi_eps' = 0 outside [1, 1 + eps], |phi_eps'| <= 3/(2 eps), and integral_1^(1+eps) (-phi_eps'(u)) du = phi_eps(1) - phi_eps(1 + eps) = 1. For every u, phi_eps(u) -> 1_{u <= 1} as eps -> 0 (for u > 1, phi_eps(u) = 0 as soon as eps <= u - 1).

2. First variation with radial fields. Fix eps in (0, 1) and put R_eps := R/(1 + eps). For t in (0, R_eps) let X_t(x) := phi_eps(r_x/t)(x - y).
 (a) X_t is C^1 on R^(n+l): on B°_t we have phi_eps(r_x/t) = 1, so X_t(x) = x - y there; on {x != y}, x -> r_x is C^infinity and phi_eps is C^1. The support of X_t lies in the compact ball B_((1+eps)t), which is contained in B°_R, hence in U, because (1 + eps)t < R. So X_t is C^1 with compact support and tsupport X_t is contained in U, and the definition of V.HasGeneralizedMeanCurvature H gives integral divM X_t dmu = - integral X_t . H dmu.
 (b) For x != y and v in R^(n+l): DX_t(x)v = phi_eps(r_x/t) v + t^(-1) phi_eps'(r_x/t) r_x^(-1) ((x - y) . v)(x - y); and DX_t(y) = I. Using trace(c I o p_x) = c trace(p_x) and, for w := x - y, trace(v -> (w . p_x v) w) = w . p_x w, we get at every x in B°_R of 0(d): divM X_t(x) = trace(DX_t(x) o p_x) = n phi_eps(r_x/t) + (r_x/t) phi_eps'(r_x/t)(1 - nu(x)) (at x = y the second term is 0). If x lies outside the closed ball B_((1+eps)t), X_t vanishes on a neighbourhood of x, so divM X_t(x) = 0, and also n phi_eps(r_x/t) + (r_x/t) phi_eps'(r_x/t)(1 - nu(x)) = 0. Hence the displayed formula for divM X_t holds mu-a.e.
 (c) For t in (0, R_eps) put I_eps(t) := integral phi_eps(r_x/t) dmu, J_eps(t) := integral phi_eps(r_x/t) nu(x) dmu, E_eps(t) := integral phi_eps(r_x/t) (x - y) . H(x) dmu. The integrands vanish outside B_((1+eps)t) and are bounded there by 1, 1 (mu-a.e., by 0(d)) and (1 + eps) t |H|, so the three integrals are finite by 0(a), 0(b). For fixed x, t -> phi_eps(r_x/t) is C^1 on (0, infinity) with derivative -phi_eps'(r_x/t) r_x/t^2, which vanishes unless t < r_x <= (1 + eps)t; on a compact interval [t_1, t_2] in (0, R_eps) it is bounded by (3/(2 eps))(1 + eps)/t_1 times the indicator of B_((1+eps)t_2). Differentiation under the integral sign (dominated convergence) shows that I_eps and J_eps are C^1 on (0, R_eps) with
 t I_eps'(t) = - integral (r_x/t) phi_eps'(r_x/t) dmu, t J_eps'(t) = - integral (r_x/t) phi_eps'(r_x/t) nu(x) dmu >= 0,
 and dominated convergence shows that E_eps is continuous on (0, R_eps).
 (d) Integrating the formula of (b) and using (a): n I_eps(t) + integral (r_x/t) phi_eps'(r_x/t) dmu - integral (r_x/t) phi_eps'(r_x/t) nu dmu = -E_eps(t), i.e. n I_eps - t I_eps' + t J_eps' = -E_eps. Dividing by t^(n+1):
 (*) d/dt (t^(-n) I_eps(t)) = t^(-n) J_eps'(t) + t^(-n-1) E_eps(t), 0 < t < R_eps.

3. Hoelder bound. Let t in (0, R_eps). Since phi_eps(r_x/t) = 0 unless r_x <= (1 + eps)t <= 2t, |(x - y) . H| <= r_x |H| and 0 <= phi_eps <= 1, Hoelder's inequality applied to phi_eps^(1/p) |H| and phi_eps^(1 - 1/p) (exponents p and p/(p - 1)) gives
 |E_eps(t)| <= 2t integral phi_eps(r_x/t) |H| dmu <= 2t (integral_{B_R} |H|^p dmu)^(1/p) I_eps(t)^(1 - 1/p) = 2t N I_eps(t)^(1 - 1/p).
 With a := t^(-n) I_eps(t) >= 0 we have t^(-n) I_eps(t)^(1 - 1/p) = t^(-n/p) a^(1 - 1/p) <= t^(-n/p)(1 + a) (a^theta <= 1 + a for a >= 0 and theta in [0, 1]). Using N <= R^(n/p - 1) kappa Lambda and R^(n/p - 1) t^(-n/p) = R^(-1) (t/R)^(-n/p):
 |t^(-n-1) E_eps(t)| <= b(t) (1 + t^(-n) I_eps(t)), where b(t) := 2 kappa Lambda R^(-1) (t/R)^(-n/p).
 Hence a_eps(t) := t^(-n-1) E_eps(t)/(1 + t^(-n) I_eps(t)) is continuous on (0, R_eps) and |a_eps(t)| <= b(t) there.

4. Integrating factor. For t > 0, integral_0^t b(tau) dtau = 2 kappa Lambda R^(-1) R (t/R)^(alpha')/alpha' = (Lambda/2)(t/R)^(alpha') <= Lambda/2 for t <= R. So a_eps is integrable on (0, t] for t < R_eps. For t in (0, R_eps) define F_eps(t) := exp(- integral_0^t a_eps(tau) dtau), Psi_eps(t) := 1 + t^(-n) I_eps(t) and Phi_eps(t) := F_eps(t) Psi_eps(t) - 1 = F_eps(t) t^(-n) I_eps(t) + F_eps(t) - 1. By the fundamental theorem of calculus (a_eps continuous), F_eps is C^1 with F_eps' = -a_eps F_eps, and (*) reads Psi_eps' = t^(-n) J_eps' + a_eps Psi_eps. Hence Phi_eps' = -a_eps F_eps Psi_eps + F_eps (t^(-n) J_eps' + a_eps Psi_eps) = F_eps(t) t^(-n) J_eps'(t), a continuous nonnegative function; and F_eps(t) >= e^(-Lambda/2). Therefore, for 0 < s <= r < R_eps,
 (**) Phi_eps(r) - Phi_eps(s) = integral_s^r F_eps(t) t^(-n) J_eps'(t) dt >= e^(-Lambda/2) integral_s^r t^(-n) J_eps'(t) dt >= 0.

5. Passage eps -> 0; definition of F. For t in (0, R) put E(t) := integral_{B_t} (x - y) . H dmu and a(t) := t^(-n-1) E(t)/(1 + t^(-n) m(t)). Fix t in (0, R) and eps_0 in (0, 1) with (1 + eps_0) t < R. For eps <= eps_0 the integrands of I_eps(t) and E_eps(t) are dominated by the indicator of B_((1+eps_0)t) and by (1 + eps_0) t |H| times it (integrable by 0(a), 0(b)), and they converge pointwise to 1_{B_t}(x) and 1_{B_t}(x) (x - y) . H(x) (step 1). By dominated convergence I_eps(t) -> m(t) and E_eps(t) -> E(t); hence a_eps(t) -> a(t), and |a(t)| <= b(t) by step 3. Fix a sequence eps_k -> 0 in (0, 1). For t in (0, R): for k large, (0, t] is contained in (0, R_(eps_k)); a_(eps_k) -> a pointwise on (0, t], |a_(eps_k)| <= b with integral_0^t b < infinity, so by dominated convergence integral_0^t a_(eps_k) -> integral_0^t a. Define F(t) := exp(- integral_0^t a(tau) dtau) for t in (0, R) and F(t) := 1 for t not in (0, R). Then F_(eps_k)(t) -> F(t) and Phi_(eps_k)(t) -> Phi(t) = F(t) (t^n)^(-1) m(t) + F(t) - 1 for every t in (0, R); this Phi is the function of the statement.

6. Conclusion (i). For t in (0, R): |integral_0^t a| <= integral_0^t b = (Lambda/2)(t/R)^(alpha') <= Lambda/2. Hence e^(-Lambda) <= e^(-Lambda/2) <= F(t) <= e^(Lambda/2) <= e^Lambda, and by |e^z - 1| <= e^|z| |z|: |F(t) - 1| <= e^(Lambda/2)(Lambda/2)(t/R)^(alpha') <= Lambda (t/R)^(alpha'), since Lambda <= 1 and e^(1/2)/2 < 1.

7. Conclusion (ii), monotonicity. Let 0 < s <= r < R. For k large, r < R_(eps_k), and (**) gives Phi_(eps_k)(s) <= Phi_(eps_k)(r). Letting k -> infinity (step 5), Phi(s) <= Phi(r).

8. Conclusion (ii), annular bound. Let 0 < s <= r < R. If s = r the annulus B_r minus B_s is empty, its integral is 0 and the claim holds. Let s < r and k large so that r < R_(eps_k). The function (t, x) -> t^(-n) (r_x/t^2)(-phi_eps'(r_x/t)) nu(x) (with the measurable version of p from 0(e)) is nonnegative and measurable on [s, r] x B°_R, continuous in t and measurable in x, and it vanishes for x outside B_((1+eps)r), which lies in B°_R. Apply Tonelli's theorem to Lebesgue measure on [s, r] and the finite measure mu restricted to B°_R; together with 2(c) this gives
 integral_s^r t^(-n) J_eps'(t) dt = integral nu(x) h_eps(r_x) dmu(x), where h_eps(c) := integral_s^r t^(-n)(c/t^2)(-phi_eps'(c/t)) dt >= 0 for c > 0, and h_eps(0) := 0.
 For c in (s, r] and eps <= c/s - 1, the substitution u = c/t (dt = -(c/u^2) du) gives h_eps(c) = integral_(c/r)^(c/s) (u/c)^n (-phi_eps'(u)) du >= c^(-n) integral_1^(1+eps) (-phi_eps'(u)) du = c^(-n), because [1, 1 + eps] is contained in [c/r, c/s], -phi_eps' >= 0 and (u/c)^n >= c^(-n) for u >= 1. Consequently, for every x, liminf_k ofReal(nu(x) h_(eps_k)(r_x)) >= ofReal(nu(x) r_x^(-n)) 1_{s < r_x <= r} = ofReal(g(x)) 1_{B_r minus B_s}(x). By Fatou's lemma for [0, infinity]-valued functions and (**):
 integral^-_{B_r minus B_s} ofReal(g) dmu <= liminf_k integral^- ofReal(nu h_(eps_k)(r_x)) dmu = liminf_k integral_s^r t^(-n) J_(eps_k)'(t) dt <= e^(Lambda/2) liminf_k (Phi_(eps_k)(r) - Phi_(eps_k)(s)) = e^(Lambda/2) (Phi(r) - Phi(s)) <= e^Lambda (Phi(r) - Phi(s)),
 where all quantities after the first are finite reals and Phi(r) - Phi(s) >= 0 by step 7. Thus integral^-_{B_r minus B_s} ofReal(g) dmu <= ofReal(e^Lambda (Phi(r) - Phi(s))). Since g(x) = |x - y - p_x(x - y)|^2/|x - y|^(n+2), this is the annular bound of (ii).

9. Conclusion (iii). By step 7, Phi is nondecreasing on (0, R), and Phi(t) >= F(t) - 1 >= -Lambda because m(t) >= 0 and F(t) > 0. Hence L := lim_(t -> 0+) Phi(t) = inf over (0, R) of Phi exists in R, and L <= Phi(r) for every r in (0, R). By step 6, F(t) -> 1 as t -> 0+ (because (t/R)^(alpha') -> 0), so t^(-n) m(t) = (Phi(t) + 1)/F(t) - 1 -> L; as t^(-n) m(t) >= 0, L >= 0. omega_n = pi^(n/2)/Gamma(n/2 + 1) > 0; put t_* := L/omega_n >= 0. For t in (0, R), mu(B_t) is finite and omega_n t^n > 0, so mu(B_t)/ofReal(omega_n t^n) = ofReal(t^(-n) m(t)/omega_n), which tends to ofReal(L/omega_n) = ofReal(t_*) by continuity of ofReal; that is, V.HasDensity y t_*. Finally omega_n t_* = L <= Phi(r) for every r in (0, R). This is (iii) with t := t_*, and together with steps 6-8 proves the statement with the F of step 5.

Implementation note (non-normative). The accepted declaration dohr_local_monotonicity (candidate commit 4c0fc30d6a1cd4ba43b449f2e51583e4e473c461, GMT/Ch05/Submission.lean, a single theorem whose proof consists of local lemmas) has the same hypotheses on (V, H, y, R, Lambda), apart from the conclusion. Its proof contains Lean versions of:
- the radial first variation, as an inequality that discards the nu-term;
- the Hoelder bound on the curvature term;
- the integrating-factor monotonicity for one cutoff;
- the cutoff limit;
- the density limit.
These can be adapted. Three ingredients are new here:
- keeping the nu-term, so that the identity of step 2(d) holds with J_eps;
- the decay bound |F - 1| <= Lambda (t/R)^(alpha') of step 6;
- the Tonelli/Fatou annular estimate of step 8.
In addition, cutoffs equal to 1 on (-infinity, 1] give closed balls directly in the limit.

## Key steps

1. Finiteness of mu(B_R), integrability of H on B_R, ||H||_{L^p(B_R)} <= R^(n/p-1) kappa Lambda, and 0 <= nu <= 1 a.e. on B°_R from (T1)
2. Radial C^1 test fields phi_eps(r/t)(x - y) supported in B_((1+eps)t), inside B°_R and U, give n I - t I' + t J' = -E, i.e. d/dt(t^-n I) = t^-n J' + t^(-n-1) E
3. Hoelder: |t^(-n-1) E| <= b(t)(1 + t^-n I) with b(t) = 2 kappa Lambda R^-1 (t/R)^(-n/p) and integral_0^t b = (Lambda/2)(t/R)^(alpha')
4. Integrating factor F_eps = exp(-integral_0^t a_eps) gives (Phi_eps)' = F_eps t^-n J_eps' >= 0
5. Dominated convergence as eps -> 0 gives F_eps -> F and Phi_eps -> Phi pointwise, with e^-Lambda <= F <= e^Lambda and |F - 1| <= Lambda (t/R)^(alpha')
6. Monotonicity of Phi in the limit; Fatou plus the substitution u = c/t give the annular lower integral bound with factor e^Lambda
7. Monotone Phi bounded below and F -> 1 give the density t >= 0 with omega_n t = inf Phi <= Phi(r)

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; cmp <snapshot>/project/GMT/Ch05/Submission.lean GMT/Ch05/Submission.lean; cmp <snapshot>/project/GMT/Ch05/Contract.lean GMT/Ch05/Contract.lean`
- `rg -c -t lean 'allard52_density_constants|allard52_annular_monotonicity|allard52_support_density_ge_one|allard52_center_density_bounds|aal_allard_subball_bounds' <snapshot>/project <snapshot>/mathlib/Mathlib`
- `for pat in Allard Varifold monotonicity_formula tangentProj; do rg -l -t lean $pat <snapshot>/mathlib/Mathlib | wc -l; done`
- `rg -n (theorem setLIntegral_iUnion_of_directed | theorem lintegral_union_le | theorem lintegral_liminf_le' | theorem tendsto_measure_biInter_gt | lemma mem_support_iff_forall | theorem LocallyIntegrableOn.integrableOn_compact_subset | theorem lintegral_lintegral_swap | theorem hasDerivAt_integral_of_dominated_loc_of_deriv_le | theorem norm_image_sub_le_of_norm_deriv_le | theorem integral_hasDerivAt_right) MeasureTheory Analysis/Calculus/ParametricIntegral.lean Analysis/Calculus/MeanValue.lean, run in <snapshot>/mathlib/Mathlib`
- `rg -n (monoton|κ|kappa|2.4|density) <snapshot>/project/GMT/Ch05/README.md; sed -n 25,45p <snapshot>/project/GMT/Ch05/README.md`
- `grep -n (def lpMeanCurvatureKappa|structure LpAnnularCorrection|theorem HasGeneralizedMeanCurvatureIn.exists_lpAnnularCorrection) -A3 .lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpMeanCurvature.lean .lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpAnnular.lean`
- `python3 over dag.json: lean_name, lean_statement, status, parent and candidate_commit for the five proposed names, allard52_tangent_ae, allard52_density_bounds and every accepted node`
- `git show 595bf34cad5e797b1ca2c89a3d419f3daecdab75:GMT/Ch05/Submission.lean; git show 9f4dca65df4fbd188bea65e81c59d598279e6643:GMT/Ch05/Submission.lean | grep -n 'theorem allard52_tangent_ae'; git show 4c0fc30d6a1cd4ba43b449f2e51583e4e473c461:GMT/Ch05/Submission.lean | grep -n 'theorem dohr_local_monotonicity'`
- `toolchains/lean-4.35.0-rc3-linux/bin/lean GMT/Ch05/Submission.lean -o /tmp/db3-build/lib/GMT/Ch05/Submission.olean (LEAN_PATH = /tmp/db3-build/lib plus lake-packages-25730c7c/*/.lake/build/lib/lean)`
- `LEAN_PATH=<same> lean /tmp/db3-check/Types.lean; lean /tmp/db3-check/Assembly.lean; lean /tmp/db3-check/Appx_density_constants.lean; lean /tmp/db3-check/Appx_center_density_bounds.lean; lean /tmp/db3-check/Appx_support_density_ge_one.lean; lean /tmp/db3-check/Subball.lean`
- `python3 field-by-field comparison of the proposed subproblems with nodes/root-allard-regularity-a1-density-bounds-a1/decomposition-v2.json`
- `grep max_nodes .humanize/swarm-configs/675fa2adfe3d43c39028ca3e3199bdce.json; read _existing_lean_name_problem, _accepted_checkpoint, _install_parent_supplied_child_handoff and the node-bound check of /runtime/flows/gmt-claude-17d09e2ab055/_recursive_lean/runtime.py, and ensure in store.py`
- `sed -n 270,315p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt (Simon Ch. 5, 2.3, 2.4 and inequality (1) in the proof of 2.5)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpMeanCurvature.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpAnnular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/swarm-configs/675fa2adfe3d43c39028ca3e3199bdce.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/tmp/db3-check/Types.lean`
- `/tmp/db3-check/Assembly.lean`
- `/tmp/db3-check/Appx_density_constants.lean`
- `/tmp/db3-check/Appx_center_density_bounds.lean`
- `/tmp/db3-check/Appx_support_density_ge_one.lean`
- `/tmp/db3-check/Subball.lean`

Pins: project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d (manifest.json). The workspace Contract.lean and Submission.lean are byte-identical to the snapshot copies.

Names.
- The five proposed names have no match in the snapshot project or Mathlib (rg exit status 1).
- In dag.json (200 nodes) the four new names occur nowhere.
- aal_allard_subball_bounds is the accepted node root.affine_approximation-a1.pinched_density_bounds-a1.allard_subball_bounds-a1 (candidate 595bf34c). Its frozen lean_statement is byte-identical to the proposed one, so runtime reuse is permitted.
- allard52_tangent_ae is accepted (candidate 9f4dca65, theorem at line 816) with the type used by the assembly.

Mathlib.
- The topics Allard, Varifold, monotonicity_formula and tangentProj have 0 hits, so the annular monotonicity is new.
- Lemmas used by the child proofs exist: setLIntegral_iUnion_of_directed (Lebesgue/Basic.lean:668), lintegral_union_le (Basic.lean:632), lintegral_liminf_le' (Lebesgue/Add.lean:216), tendsto_measure_biInter_gt (Measure/Continuity.lean:266), mem_support_iff_forall (Measure/Support.lean:75), LocallyIntegrableOn.integrableOn_compact_subset (LocallyIntegrable.lean:122), lintegral_lintegral_swap (Measure/Prod.lean:1071), integral_hasDerivAt_right (FundThmCalculus.lean:725), hasDerivAt_integral_of_dominated_loc_of_deriv_le (ParametricIntegral.lean:286) and norm_image_sub_le_of_norm_deriv_le (MeanValue.lean:727).

SimonGMT.
- lpMeanCurvatureKappa n p = (p - n) / (4 * p) (LpMeanCurvature.lean:76) confirms the corrected kappa.
- LpAnnularCorrection and exists_lpAnnularCorrection (LpAnnular.lean:335, 358) are proved for the library varifold with stored tangent data. The chapter README (lines 33-38) says this needs a bridge, so annular_monotonicity re-derives the result for the contract varifold.
- The accepted dohr_local_monotonicity (4c0fc30d, line 465) has the same hypotheses but no conical term and no decay rate.

Lean checks (Lean v4.35.0-rc3).
- Types.lean: every proposed type, the tangent sibling type and the frozen parent type elaborate with only sorry warnings.
- Assembly.lean proves the exact frozen parent type from the five children and allard52_tangent_ae. #print axioms lists exactly propext, Classical.choice, Quot.sound and those six declarations.
- Appendices: density_constants and center_density_bounds use standard axioms only; support_density_ge_one uses standard axioms plus aal_allard_subball_bounds and allard52_annular_monotonicity.
- The accepted subball body recompiles with standard axioms only.
- No matrix or inline-instance constructions occur; V.weight is passed directly as the abstract measure of center_density_bounds and elaborates.

Runtime. The current config has max_nodes = 1000 against 200 existing nodes, so the 4 new nodes fit. Reused accepted nodes skip handoff installation, and ensure returns existing nodes unchanged.

Source. Simon's 2.4 and the proof of 2.5 (1) confirm the pinched density and conical-integral bounds that are formalized here with explicit constants.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: https://github.com/ZhengyangZhang06/gmt-formalize/pull/4427

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
