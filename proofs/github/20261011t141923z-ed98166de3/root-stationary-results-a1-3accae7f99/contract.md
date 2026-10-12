<!-- theorem-id: gmt-ch02/root.stationary_results-a1 -->

## Theorem `Submission.stationary_mean_curvature_and_stable_variation`

(5.5(2)) If M is an n-dimensional C² Simon submanifold of ℝ^{n+ℓ}, U is open and closure U ∩ M is compact, then M is stationary in U (IsStationaryIn) iff the mean curvature meanCurvature M y = 0 for all y ∈ M ∩ U. (5.11) If M is a C² Simon submanifold, U open with (closure M ∖ M) ∩ U = ∅, M stationary in U, and φ an admissible C³ deformation whose initial velocity X is normal to M along M, then t ↦ Hⁿ(φ_t(M ∩ K)) is differentiable near 0 and its derivative has derivative ∫_M (Σ_i|(D_{τ_i}X)^⊥|² − Σ_{i,j}(X·B(τ_i,τ_j))²) dHⁿ at 0.

Node: `root.stationary_results-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/3

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/3

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/39, https://github.com/ZhengyangZhang06/gmt-formalize/issues/40, https://github.com/ZhengyangZhang06/gmt-formalize/issues/41

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/234, https://github.com/ZhengyangZhang06/gmt-formalize/issues/236, https://github.com/ZhengyangZhang06/gmt-formalize/issues/239, https://github.com/ZhengyangZhang06/gmt-formalize/issues/240, https://github.com/ZhengyangZhang06/gmt-formalize/issues/241, https://github.com/ZhengyangZhang06/gmt-formalize/issues/242, https://github.com/ZhengyangZhang06/gmt-formalize/issues/243, https://github.com/ZhengyangZhang06/gmt-formalize/issues/244, https://github.com/ZhengyangZhang06/gmt-formalize/issues/245, https://github.com/ZhengyangZhang06/gmt-formalize/issues/247

## Lean problem

Declaration: `Submission.stationary_mean_curvature_and_stable_variation`

```lean
StationaryIffMeanCurvatureZero ∧ SecondVariationStationary
```

### Frozen project context

`GMT/Ch02/Contract.lean` at `1b1689a8deba89d58b36b1a04dba493693824437` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Basic.Real.ENatENNReal
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.LinearAlgebra.Determinant
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Algebra.Module.Determinant
import Poincare.SimonGMT.Chapter01.Hausdorff
import Poincare.SimonGMT.Chapter02.BV
import Poincare.SimonGMT.Chapter02.Submanifold

/-!
# Simon, *Introduction to GMT*, Chapter 2: Some further preliminaries from analysis (pp. 39–68)

Frozen problem statement.

Conventions (Simon's "Notation" page): `B_ρ(ξ)` is the CLOSED ball (`Metric.closedBall`);
`W ⊂⊂ U` means `closure W` is a compact subset of `U` (`Chapter02.IsRelativelyCompactIn`);
`ℝⁿ = EuclideanSpace ℝ (Fin n)` and `Lⁿ = volume`.

Hausdorff measures. `𝓗[s]` is Simon's real-dimensional Hausdorff measure
`Chapter01.simonHausdorffMeasureReal s = (ω_s / 2^s) • μH[s]`, `ω_s = π^{s/2}/Γ(s/2+1)` (Ch. 1,
2.1–2.2). For natural `n` we use Mathlib's `μHE[n]`, which equals `𝓗[n]` (SimonGMT
`Chapter02.simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure`) and equals `Lⁿ` on `ℝⁿ`.
"`Hᵐ`-measurable" (Carathéodory) is rendered as `NullMeasurableSet`/`AEMeasurable`; for sets of
finite measure (resp. functions supported in a set of σ-finite measure) these agree.

Reused SimonGMT definitions (source read and checked): `Chapter02.IsLocallyBV`,
`Chapter02.bvVariationOn` (= `|Du|(W)` for open `W` by Simon 2.4), `Chapter02.TendstoLocallyInL1On`,
`Chapter02.IsRelativelyCompactIn`, `Chapter02.IsSimonSubmanifold` (Simon 4.1), and Ch. 1
`simonHausdorffMeasureReal`, `realUnitBallVolume` (`ω_s`).
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal

namespace GMT.Ch02

open Poincare.SimonGMT

noncomputable section

/-- Euclidean space `ℝⁿ`. -/
abbrev Rn (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-- Simon's normalized `s`-dimensional Hausdorff measure (Ch. 1, 2.1–2.2), `s ∈ ℝ`, `s ≥ 0`. -/
local notation "𝓗[" s "]" => Chapter01.simonHausdorffMeasureReal s

/-- Simon's `ω_s = π^{s/2} / Γ(s/2 + 1)` (Notation page; Ch. 1 §2), as an extended real. -/
local notation "ω[" s "]" => Chapter01.realUnitBallVolume s

/-! ## Definitions -/

/-- Simon Ch. 2, 1.1 (p. 39): `Lip f`, the least Lipschitz constant of `f` (the infimum of all
valid Lipschitz constants; it is attained when `f` is Lipschitz). -/
def lipConst {α β : Type*} [PseudoEMetricSpace α] [PseudoEMetricSpace β] (f : α → β) : ℝ≥0 :=
  sInf {K : ℝ≥0 | LipschitzWith K f}

/-- Simon Ch. 2, 1.8 (p. 44): the multiplicity function `N(f, y) = H⁰(A ∩ f⁻¹{y})` of `f|A`, i.e.
the number of points (possibly `∞`) of `A` mapped to `y`. -/
def fiberCount {α β : Type*} (A : Set α) (f : α → β) (y : β) : ℝ≥0∞ :=
  ENat.toENNReal (A ∩ f ⁻¹' {y}).encard

/-- Simon Ch. 2, 3.1/3.3 (pp. 53–54): the area Jacobian `√det(L* ∘ L)` of a linear map
`L : E → F` (`L*` the adjoint). For `L = df_x` this is `Jf(x)`. -/
def areaJacobian {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] (L : E →L[ℝ] F) : ℝ :=
  Real.sqrt ((ContinuousLinearMap.adjoint L ∘L L).det)

/-- Simon Ch. 2, 2.7 (p. 51): `u ∈ BV(U)`: `U` open, `u ∈ L¹(U)` and `|Du|(U) < ∞`, where
`|Du|(U) = sup {∫_U u div g : g Lipschitz, |g| ≤ 1, spt g ⊂ U compact}` (Simon 2.4). -/
def IsBVOn {n : ℕ} (U : Set (Rn n)) (u : Rn n → ℝ) : Prop :=
  IsOpen U ∧ IntegrableOn u U volume ∧ Chapter02.bvVariationOn u U < ⊤

section Submanifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Simon Ch. 2, before 4.3 (p. 55): the tangent space `T_y M`, the set of velocities `γ'(0)` of
`C¹` curves `γ : (-1,1) → M` with `γ(0) = y`. (For a `C¹` submanifold this set is already a
linear subspace (Simon 4.3); the `span` only makes the definition total.) -/
def tangentSpace (M : Set E) (y : E) : Submodule ℝ E :=
  Submodule.span ℝ {v : E | ∃ γ : ℝ → E, ContDiffOn ℝ 1 γ (Ioo (-1) 1) ∧
    MapsTo γ (Ioo (-1) 1) M ∧ γ 0 = y ∧ HasDerivAt γ v 0}

/-- Orthogonal projection `P_y` of the ambient space onto `T_y M`; `v^⊤ = P_y v`. -/
def tangentProjection (M : Set E) (y : E) : E →L[ℝ] E :=
  (tangentSpace M y).starProjection

/-- The normal part `v^⊥ = v - P_y v` of `v` relative to `T_y M`. -/
def normalPart (M : Set E) (y v : E) : E :=
  v - tangentProjection M y v

/-- An orthonormal basis `τ₁, …, τ_n` of `T_y M`, as vectors of the ambient space. Every quantity
below built from it is independent of the choice of orthonormal basis. -/
def tangentFrame (M : Set E) (y : E) : Fin (Module.finrank ℝ (tangentSpace M y)) → E :=
  fun i ↦ ((stdOrthonormalBasis ℝ (tangentSpace M y)) i : E)

/-- Simon Ch. 2, 4.18–4.20 (p. 59): `div_M X(y) = ∑ᵢ τᵢ · D_{τᵢ} X(y)` for a vector field `X`
that is `C¹` on an open set containing `M` (`X` need not be tangent). -/
def tangentialDivergence (M : Set E) (X : E → E) (y : E) : ℝ :=
  ∑ i, inner ℝ (tangentFrame M y i) (fderiv ℝ X y (tangentFrame M y i))

/-- Simon Ch. 2, 4.23–4.26 (pp. 59–60): the second fundamental form `B_y(τ, η) ∈ (T_y M)^⊥` of a
`C²` submanifold, `τ, η ∈ T_y M`, written as `B_y(τ, η) = (D_τ P)(η)`, the derivative along `M` in
direction `τ` of the tangent-projection field `z ↦ P_z`, applied to `η`. Faithfulness: with a local
orthonormal normal frame `ν^α`, `P = I - ∑ ν^α ⊗ ν^α`, so for `η ∈ T_y M`,
`(D_τ P)η = -∑_α (η · D_τ ν^α) ν^α`, which is Simon's 4.24 (and `B_y(τ,τ) = γ''(0)^⊥`, 4.25).
The derivative within `M` is unique on `T_y M`, so the value is well defined. -/
def secondFundamentalForm (M : Set E) (y τ η : E) : E :=
  fderivWithin ℝ (tangentProjection M) M y τ η

/-- Simon Ch. 2, 4.27 (p. 60): the mean curvature vector `H(y) = ∑ᵢ B_y(τᵢ, τᵢ)`. -/
def meanCurvature (M : Set E) (y : E) : E :=
  ∑ i, secondFundamentalForm M y (tangentFrame M y i) (tangentFrame M y i)

/-- Simon Ch. 2, §6 (p. 66): for `f` that is `C¹` near `x ∈ M`, `J*_f(x) = √det(df_x ∘ df_x*)` where
`df_x = Df(x)|_{T_x M} : T_x M → F` is the induced linear map and `df_x*` its adjoint. -/
def coareaJacobian {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (M : Set E) (f : E → F) (x : E) : ℝ :=
  let L : tangentSpace M x →L[ℝ] F := (fderiv ℝ f x).comp (tangentSpace M x).subtypeL
  Real.sqrt ((L ∘L ContinuousLinearMap.adjoint L).det)

/-- Simon Ch. 2, 5.1 (p. 61): `{φ_t}_{-1<t<1}` is a 1-parameter family of diffeomorphisms of the
open set `U` such that `(t, x) ↦ φ_t(x)` is `C^r` on `(-1,1) × U`, `φ_0 = id` on `U`, and
`φ_t(x) = x` for `x ∉ K`, `K ⊂ U` compact. (Simon's `φ_t` is only defined on `U`; we normalize it to
be the identity outside `K` on the whole space, which changes nothing since `K ⊂ U`.) Diffeomorphism
of `U` is encoded as: bijection `U → U` with invertible derivative at every point of `U`. -/
def IsAdmissibleDeformation (r : ℕ∞) (U K : Set E) (φ : ℝ → E → E) : Prop :=
  IsOpen U ∧ IsCompact K ∧ K ⊆ U ∧
    ContDiffOn ℝ (r : WithTop ℕ∞) (fun p : ℝ × E ↦ φ p.1 p.2) (Ioo (-1) 1 ×ˢ U) ∧
    (∀ x ∈ U, φ 0 x = x) ∧ (∀ t ∈ Ioo (-1 : ℝ) 1, ∀ x, x ∉ K → φ t x = x) ∧
    ∀ t ∈ Ioo (-1 : ℝ) 1, BijOn (φ t) U U ∧ ∀ x ∈ U, Function.Bijective (fderiv ℝ (φ t) x)

/-- Simon Ch. 2, before 5.2 (p. 62): initial velocity `X_x = ∂φ(t,x)/∂t |_{t=0}`. -/
def initialVelocity (φ : ℝ → E → E) (x : E) : E :=
  deriv (fun t ↦ φ t x) 0

/-- Simon Ch. 2, before 5.2 (p. 62): initial acceleration `Z_x = ∂²φ(t,x)/∂t² |_{t=0}`. -/
def initialAcceleration (φ : ℝ → E → E) (x : E) : E :=
  deriv (fun t ↦ deriv (fun s ↦ φ s x) t) 0

variable [MeasurableSpace E] [BorelSpace E]

/-- Simon Ch. 2, 5.2 (p. 62): `t ↦ Hⁿ(M_t)`, `M_t = φ_t(M ∩ K)` (finite by hypothesis in 5.x). -/
def deformedArea (n : ℕ) (M K : Set E) (φ : ℝ → E → E) (t : ℝ) : ℝ :=
  (μHE[n] (φ t '' (M ∩ K))).toReal

/-- Simon Ch. 2, after 5.4 (p. 63): `M` is stationary in `U` if `Hⁿ(M ∩ K) < ∞` for each compact
`K ⊂ U` and `d/dt Hⁿ(M_t)|_{t=0} = 0` for every family `φ_t` as in 5.1 (class `C²`). -/
def IsStationaryIn (n : ℕ) (M U : Set E) : Prop :=
  (∀ K, IsCompact K → K ⊆ U → μHE[n] (M ∩ K) < ⊤) ∧
    ∀ (K : Set E) (φ : ℝ → E → E), IsAdmissibleDeformation 2 U K φ →
      HasDerivAt (deformedArea n M K φ) 0 0

/-- Simon Ch. 2, 5.4 (p. 63): the second-variation integrand at `y ∈ M`, with `X`, `Z` the initial
velocity and acceleration of `φ` and `τᵢ` an orthonormal basis of `T_y M`:
`div_M Z + (div_M X)² + ∑ᵢ |(D_{τᵢ}X)^⊥|² - ∑_{i,j} (τᵢ · D_{τⱼ}X)(τⱼ · D_{τᵢ}X)`. -/
def secondVariationIntegrand (M : Set E) (φ : ℝ → E → E) (y : E) : ℝ :=
  let X := initialVelocity φ
  let τ := tangentFrame M y
  tangentialDivergence M (initialAcceleration φ) y + tangentialDivergence M X y ^ 2 +
    ∑ i, ‖normalPart M y (fderiv ℝ X y (τ i))‖ ^ 2 -
    ∑ i, ∑ j, inner ℝ (τ i) (fderiv ℝ X y (τ j)) * inner ℝ (τ j) (fderiv ℝ X y (τ i))

/-- Simon Ch. 2, 5.11 (p. 65): the second-variation integrand for a normal initial velocity on a
stationary `M`: `∑ᵢ |(D_{τᵢ}X)^⊥|² - ∑_{i,j} (X · B(τᵢ, τⱼ))²`. -/
def stableSecondVariationIntegrand (M : Set E) (φ : ℝ → E → E) (y : E) : ℝ :=
  let X := initialVelocity φ
  let τ := tangentFrame M y
  ∑ i, ‖normalPart M y (fderiv ℝ X y (τ i))‖ ^ 2 -
    ∑ i, ∑ j, inner ℝ (X y) (secondFundamentalForm M y (τ i) (τ j)) ^ 2

end Submanifold

/-! ## Headline results -/

/-- **Simon Ch. 2, Theorem 1.2 (p. 40), Lipschitz extension.** If `A` is a non-empty subset of a
metric space `X` and `f : A → ℝ` is Lipschitz, then there is `f̄ : X → ℝ` with `Lip f̄ = Lip f` and
`f = f̄|A`. (`f̄` is required to be Lipschitz so that `Lip f̄` is meaningful.) -/
def LipschitzExtension : Prop :=
  ∀ (X : Type) [MetricSpace X] (A : Set X) (f : A → ℝ), A.Nonempty → (∃ K, LipschitzWith K f) →
    ∃ F : X → ℝ, (∃ K, LipschitzWith K F) ∧ lipConst F = lipConst f ∧ ∀ a : A, F a = f a

/-- **Simon Ch. 2, Theorem 1.4 (p. 40), Rademacher.** A Lipschitz `f : ℝⁿ → ℝ` is differentiable
(in the sense 1.4(*), i.e. Fréchet) at `Lⁿ`-a.e. point. -/
def Rademacher : Prop :=
  ∀ (n : ℕ) (f : Rn n → ℝ), (∃ K, LipschitzWith K f) → ∀ᵐ x ∂(volume : Measure (Rn n)),
    DifferentiableAt ℝ f x

/-- **Simon Ch. 2, Theorem 1.5 (p. 42), `C¹` approximation.** If `f : ℝⁿ → ℝ` is Lipschitz, then
for each `ε > 0` there is `g ∈ C¹(ℝⁿ)` with `Lⁿ({f ≠ g} ∪ {∇f ≠ ∇g}) < ε`. The set `{∇f ≠ ∇g}` is
taken to be the set of `x` at which it is NOT true that `f` is differentiable at `x` with
`Df(x) = Dg(x)` (this differs from the literal set by an `Lⁿ`-null set, by Rademacher 1.4). -/
def C1Approximation : Prop :=
  ∀ (n : ℕ) (f : Rn n → ℝ), (∃ K, LipschitzWith K f) → ∀ ε : ℝ, 0 < ε →
    ∃ g : Rn n → ℝ, ContDiff ℝ 1 g ∧
      volume ({x | f x ≠ g x} ∪ {x | ¬ HasFDerivAt f (fderiv ℝ g x) x}) < ENNReal.ofReal ε

/-- **Simon Ch. 2, Theorem 1.6 (pp. 42–43), Whitney extension.** Let `A ⊂ ℝⁿ` be closed and
`h : A → ℝ`, `ν : A → ℝⁿ` continuous, and suppose that for each compact `K ⊂ A`,
`R(x,y) = (h(y) - h(x) - ν(x)·(y - x))/|x - y| → 0` as `y → x`, `y ∈ A`, uniformly for `x ∈ K`.
Then there is a `C¹` function `g : ℝⁿ → ℝ` with `g = h` and `∇g = ν` on `A`. -/
def WhitneyExtension : Prop :=
  ∀ (n : ℕ) (A : Set (Rn n)) (h : Rn n → ℝ) (ν : Rn n → Rn n),
    IsClosed A → ContinuousOn h A → ContinuousOn ν A →
    (∀ K ⊆ A, IsCompact K → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ y ∈ A,
      0 < ‖y - x‖ → ‖y - x‖ < δ → |h y - h x - inner ℝ (ν x) (y - x)| ≤ ε * ‖y - x‖) →
    ∃ g : Rn n → ℝ, ContDiff ℝ 1 g ∧ ∀ x ∈ A, g x = h x ∧ ∀ v, fderiv ℝ g x v = inner ℝ (ν x) v

/-- **Simon Ch. 2, Theorem 1.8 (p. 44), Hausdorff measure of Lipschitz images.** `X, Y` metric
spaces, `X` σ-compact, `m ≥ 0` real, `A ⊂ X` `Hᵐ`-measurable with `Hᵐ(A) < ∞`, `f : A → Y`
Lipschitz with constant `K` (equivalently `Lip f`, which is attained). Then
(i) `f(A)` is `Hᵐ`-measurable and `Hᵐ(f(A)) ≤ Kᵐ Hᵐ(A)`;
(ii) `N(f, ·)` is `Hᵐ`-measurable on `Y` and `∫_Y N(f,y) dHᵐ(y) ≤ Kᵐ Hᵐ(A)`. -/
def LipschitzImageHausdorff : Prop :=
  ∀ (X Y : Type) [MetricSpace X] [SigmaCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] (m : ℝ) (A : Set X) (f : X → Y) (K : ℝ≥0),
    0 ≤ m → NullMeasurableSet A 𝓗[m] → 𝓗[m] A < ⊤ → LipschitzOnWith K f A →
    (NullMeasurableSet (f '' A) 𝓗[m] ∧ 𝓗[m] (f '' A) ≤ (K : ℝ≥0∞) ^ m * 𝓗[m] A) ∧
    (AEMeasurable (fiberCount A f) 𝓗[m] ∧
      ∫⁻ y, fiberCount A f y ∂𝓗[m] ≤ (K : ℝ≥0∞) ^ m * 𝓗[m] A)

/-- **Simon Ch. 2, Theorem 1.9 (p. 45), Eilenberg inequality.** `X` a σ-compact metric space,
`m ∈ {1, 2, …}`, `k > 0` real, `A ⊂ X` `H^{m+k}`-measurable with `H^{m+k}(A) < ∞`, `f : A → ℝᵐ`
Lipschitz with constant `K`. Then `y ↦ Hᵏ(A ∩ f⁻¹y)` is `Lᵐ`-measurable and
`∫_{ℝᵐ} Hᵏ(A ∩ f⁻¹y) dLᵐ(y) ≤ (ω_m ω_k / ω_{m+k}) Kᵐ H^{m+k}(A)` (Simon-normalized measures). -/
def EilenbergInequality : Prop :=
  ∀ (X : Type) [MetricSpace X] [SigmaCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (m : ℕ) (k : ℝ) (A : Set X) (f : X → Rn m) (K : ℝ≥0),
    1 ≤ m → 0 < k → NullMeasurableSet A 𝓗[m + k] → 𝓗[m + k] A < ⊤ → LipschitzOnWith K f A →
    AEMeasurable (fun y ↦ 𝓗[k] (A ∩ f ⁻¹' {y})) volume ∧
      ∫⁻ y, 𝓗[k] (A ∩ f ⁻¹' {y}) ∂volume ≤
        ω[(m : ℝ)] * ω[k] / ω[m + k] * (K : ℝ≥0∞) ^ m * 𝓗[m + k] A

/-- **Simon Ch. 2, Theorem 2.6 (p. 50), compactness for BV functions.** If `u_k ∈ BV_loc(U)` and
`sup_k (‖u_k‖_{L¹(W)} + ∫_W |Du_k|) < ∞` for each `W ⊂⊂ U`, then there are a subsequence `u_{k'}` and
`u ∈ BV_loc(U)` with `u_{k'} → u` in `L¹_loc(U)` and `∫_W |Du| ≤ liminf ∫_W |Du_{k'}|` for all
`W ⊂⊂ U`. Here `∫_W |Du| = |Du|(W) = bvVariationOn u W` (Simon 2.4), `W` ranging over open sets
(for which 2.4 characterizes `|Du|(W)`; lower semicontinuity is false for non-open `W`). -/
def BVCompactness : Prop :=
  ∀ (n : ℕ) (U : Set (Rn n)) (u : ℕ → Rn n → ℝ), (∀ k, Chapter02.IsLocallyBV U (u k)) →
    (∀ W, IsOpen W → Chapter02.IsRelativelyCompactIn W U →
      ⨆ k, (∫⁻ x in W, ‖u k x‖ₑ + Chapter02.bvVariationOn (u k) W) < ⊤) →
    ∃ (ψ : ℕ → ℕ) (v : Rn n → ℝ), StrictMono ψ ∧ Chapter02.IsLocallyBV U v ∧
      Chapter02.TendstoLocallyInL1On (fun k ↦ u (ψ k)) v U atTop ∧
      ∀ W, IsOpen W → Chapter02.IsRelativelyCompactIn W U →
        Chapter02.bvVariationOn v W ≤ liminf (fun k ↦ Chapter02.bvVariationOn (u (ψ k)) W) atTop

/-- **Simon Ch. 2, Lemma 2.7 (p. 51), Poincaré inequality for BV.** For `θ, δ ∈ (0,1)` there is
`C = C(θ, δ, n)` such that: if `U ⊂ ℝⁿ` is bounded, open, convex, `R > 0`, `ξ ∈ U`,
`B_{δR}(ξ) ⊂ U ⊂ B_R(ξ)` (closed balls), `u ∈ BV(U)` and `β ∈ ℝ` satisfies
`min{Lⁿ{x ∈ U : u ≥ β}, Lⁿ{x ∈ U : u ≤ β}} ≥ θ Lⁿ(U)`, then `∫_U |u - β| dLⁿ ≤ C R ∫_U |Du|`. -/
def BVPoincare : Prop :=
  ∀ (n : ℕ) (θ δ : ℝ), 0 < θ → θ < 1 → 0 < δ → δ < 1 →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : Set (Rn n)) (R : ℝ) (ξ : Rn n) (u : Rn n → ℝ) (β : ℝ),
      IsOpen U → Bornology.IsBounded U → Convex ℝ U → 0 < R → ξ ∈ U →
      closedBall ξ (δ * R) ⊆ U → U ⊆ closedBall ξ R → IsBVOn U u →
      ENNReal.ofReal θ * volume U ≤ min (volume {x ∈ U | β ≤ u x}) (volume {x ∈ U | u x ≤ β}) →
      ∫⁻ x in U, ‖u x - β‖ₑ ≤ ENNReal.ofReal (C * R) * Chapter02.bvVariationOn u U

/-- **Simon Ch. 2, Lemma 2.8 (p. 51), BV extension estimate.** For `δ ∈ (0,1)` there is
`C = C(δ, n)` such that: if `U, R, ξ` are as in 2.7, `u ∈ BV(ℝⁿ)` and `spt u ⊂ Ū` (`u = 0` a.e.
off `Ū`), then `|Du|(ℝⁿ \ Ū) = 0` (i.e. `∫_{ℝⁿ}|Du| = ∫_Ū |Du|`) and
`∫_{ℝⁿ} |Du| ≤ C (∫_U |Du| + R⁻¹ ∫_U |u| dLⁿ)`. -/
def BVExtensionEstimate : Prop :=
  ∀ (n : ℕ) (δ : ℝ), 0 < δ → δ < 1 →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : Set (Rn n)) (R : ℝ) (ξ : Rn n) (u : Rn n → ℝ),
      IsOpen U → Bornology.IsBounded U → Convex ℝ U → 0 < R → ξ ∈ U →
      closedBall ξ (δ * R) ⊆ U → U ⊆ closedBall ξ R → IsBVOn univ u →
      (∀ᵐ x ∂volume, x ∉ closure U → u x = 0) →
      Chapter02.bvVariationOn u (closure U)ᶜ = 0 ∧
        Chapter02.bvVariationOn u univ ≤ ENNReal.ofReal C *
          (Chapter02.bvVariationOn u U + ENNReal.ofReal R⁻¹ * ∫⁻ x in U, ‖u x‖ₑ)

/-- **Simon Ch. 2, 3.4 and 3.5 (p. 54), area formula.** `A ⊂ ℝⁿ` `Lⁿ`-measurable, `f : A → ℝᵐ`
Lipschitz, `m ≥ n`, `Jf(x) = √det(df_x* ∘ df_x)` (`df_x` = derivative of `f` within `A`, which
exists `Lⁿ`-a.e. on `A`). (3.4) `∫_{ℝᵐ} H⁰(f⁻¹(y) ∩ A) dHⁿ(y) = ∫_A Jf dLⁿ`; (3.5) for
`h ≥ 0` `Hⁿ`-measurable on `A`, `y ↦ ∑_{x ∈ A ∩ f⁻¹(y)} h(x)` is `Hⁿ`-measurable and its integral
w.r.t. `Hⁿ` equals `∫_A h Jf dHⁿ` (`Hⁿ = Lⁿ` on `ℝⁿ`).
ERRATUM: 3.4 prints `dHᵐ(y)` on the left; the correct measure is `Hⁿ` (as printed in 3.5);
with `Hᵐ`, `m > n`, the left side is `0` or `∞`. -/
def AreaFormula : Prop :=
  ∀ (n m : ℕ) (A : Set (Rn n)) (f : Rn n → Rn m) (K : ℝ≥0),
    n ≤ m → NullMeasurableSet A volume → LipschitzOnWith K f A →
    (∫⁻ y, fiberCount A f y ∂μHE[n] =
        ∫⁻ x in A, ENNReal.ofReal (areaJacobian (fderivWithin ℝ f A x)) ∂volume) ∧
    ∀ h : Rn n → ℝ≥0∞, AEMeasurable h (volume.restrict A) →
      AEMeasurable (fun y ↦ ∑' x : ↥(A ∩ f ⁻¹' {y}), h x) μHE[n] ∧
      ∫⁻ y, (∑' x : ↥(A ∩ f ⁻¹' {y}), h x) ∂μHE[n] =
        ∫⁻ x in A, h x * ENNReal.ofReal (areaJacobian (fderivWithin ℝ f A x)) ∂volume

/-- **Simon Ch. 2, 5.3 (p. 63), first variation formula.** `M` an `n`-dimensional `C¹`
submanifold of `ℝ^{n+ℓ}`, `U` open, `U ∩ M ≠ ∅`, `Hⁿ(K' ∩ M) < ∞` for compact `K' ⊂ U`, `φ_t` as
in 5.1 (class `C²`), `X` its initial velocity, `M_t = φ_t(M ∩ K)`. Then
`d/dt Hⁿ(M_t)|_{t=0} = ∫_M div_M X dHⁿ`. -/
def FirstVariation : Prop :=
  ∀ (n ℓ : ℕ) (M U K : Set (Rn (n + ℓ))) (φ : ℝ → Rn (n + ℓ) → Rn (n + ℓ)),
    Chapter02.IsSimonSubmanifold (E := Rn n) 1 M → IsOpen U → (U ∩ M).Nonempty →
    (∀ K', IsCompact K' → K' ⊆ U → μHE[n] (K' ∩ M) < ⊤) → IsAdmissibleDeformation 2 U K φ →
    HasDerivAt (deformedArea n M K φ)
      (∫ y in M, tangentialDivergence M (initialVelocity φ) y ∂μHE[n]) 0

/-- **Simon Ch. 2, 5.4 (p. 63), second variation formula.** Same setting as 5.3, `Z` the initial
acceleration. Then `t ↦ Hⁿ(M_t)` is differentiable near `0` and
`d²/dt² Hⁿ(M_t)|_{t=0} = ∫_M (div_M Z + (div_M X)² + ∑ᵢ|(D_{τᵢ}X)^⊥|² - ∑_{i,j}(τᵢ·D_{τⱼ}X)(τⱼ·D_{τᵢ}X)) dHⁿ`.
CORRECTION: Simon assumes `φ ∈ C²`, but then `Z` is only continuous and `div_M Z` is undefined (and
the expansion 5.2 to `O(t³)` needs a third derivative); we assume `φ ∈ C³`. -/
def SecondVariation : Prop :=
  ∀ (n ℓ : ℕ) (M U K : Set (Rn (n + ℓ))) (φ : ℝ → Rn (n + ℓ) → Rn (n + ℓ)),
    Chapter02.IsSimonSubmanifold (E := Rn n) 1 M → IsOpen U → (U ∩ M).Nonempty →
    (∀ K', IsCompact K' → K' ⊆ U → μHE[n] (K' ∩ M) < ⊤) → IsAdmissibleDeformation 3 U K φ →
    (∀ᶠ t in 𝓝 0, DifferentiableAt ℝ (deformedArea n M K φ) t) ∧
      HasDerivAt (deriv (deformedArea n M K φ))
        (∫ y in M, secondVariationIntegrand M φ y ∂μHE[n]) 0

/-- **Simon Ch. 2, Lemma 5.5(2) (p. 63), stationary iff `H = 0`.** `M` an `n`-dimensional `C²`
submanifold of `ℝ^{n+ℓ}` with mean curvature `H`, `U ⊂ ℝ^{n+ℓ}` open, and `Ū ∩ M` a compact subset
of `M`. Then `M` is stationary in `U` iff `H ≡ 0` on `M ∩ U`. (Part (1), for `M̄` a `C²` manifold
with boundary, is not included.) -/
def StationaryIffMeanCurvatureZero : Prop :=
  ∀ (n ℓ : ℕ) (M U : Set (Rn (n + ℓ))),
    Chapter02.IsSimonSubmanifold (E := Rn n) 2 M → IsOpen U → IsCompact (closure U ∩ M) →
    (IsStationaryIn n M U ↔ ∀ y ∈ M ∩ U, meanCurvature M y = 0)

/-- **Simon Ch. 2, Lemma 5.11 (p. 65), second variation of a stationary `M`.** `M` an
`n`-dimensional `C²` submanifold, stationary in the open `U ⊂ ℝ^{n+ℓ}`, `(M̄ \ M) ∩ U = ∅`, `φ_t` as
in 5.1 with initial velocity `X` normal to `M` (`X_y ∈ (T_y M)^⊥`, `y ∈ M`). Then
`d²/dt² Hⁿ(M_t)|_{t=0} = ∫_M (∑ᵢ |(D_{τᵢ}X)^⊥|² - ∑_{i,j} (X · B(τᵢ, τⱼ))²) dHⁿ`.
CORRECTION (as in 5.4): `φ ∈ C³` instead of `C²`. -/
def SecondVariationStationary : Prop :=
  ∀ (n ℓ : ℕ) (M U K : Set (Rn (n + ℓ))) (φ : ℝ → Rn (n + ℓ) → Rn (n + ℓ)),
    Chapter02.IsSimonSubmanifold (E := Rn n) 2 M → IsOpen U → (closure M \ M) ∩ U = ∅ →
    IsStationaryIn n M U → IsAdmissibleDeformation 3 U K φ →
    (∀ y ∈ M, ∀ v ∈ tangentSpace M y, inner ℝ (initialVelocity φ y) v = 0) →
    (∀ᶠ t in 𝓝 0, DifferentiableAt ℝ (deformedArea n M K φ) t) ∧
      HasDerivAt (deriv (deformedArea n M K φ))
        (∫ y in M, stableSecondVariationIntegrand M φ y ∂μHE[n]) 0

/-- **Simon Ch. 2, 6.3 and 6.6 (pp. 66–67), co-area formula.** `M` an `n`-dimensional `C¹`
submanifold of `ℝᴺ`, `n = m + k`, `k ≥ 1`, `f : M → ℝᵐ` `C¹` (the restriction of a `C¹` map on an
open `U ⊃ M`, Simon §4). For `g ≥ 0` `Hⁿ`-measurable on `M`, `y ↦ ∫_{f⁻¹(y)} g dHᵏ` is
`Lᵐ`-measurable and `∫_M g J*_f dHⁿ = ∫_{ℝᵐ} ∫_{f⁻¹(y)} g dHᵏ dLᵐ(y)` (6.6). 6.3 is the case
`g = 1_A`, `A ⊂ M` Borel. -/
def CoareaFormula : Prop :=
  ∀ (N m k : ℕ) (M U : Set (Rn N)) (f : Rn N → Rn m) (g : Rn N → ℝ≥0∞), 0 < k →
    Chapter02.IsSimonSubmanifold (E := Rn (m + k)) 1 M → IsOpen U → M ⊆ U →
    ContDiffOn ℝ 1 f U → AEMeasurable g (μHE[m + k].restrict M) →
    AEMeasurable (fun y ↦ ∫⁻ x in M ∩ f ⁻¹' {y}, g x ∂μHE[k]) volume ∧
      ∫⁻ x in M, g x * ENNReal.ofReal (coareaJacobian M f x) ∂μHE[m + k] =
        ∫⁻ y, ∫⁻ x in M ∩ f ⁻¹' {y}, g x ∂μHE[k] ∂volume

/-- **Simon Ch. 2, Theorem 6.4 (p. 67), `C¹` Sard-type theorem.** `M` an `n`-dimensional `C¹`
submanifold of `ℝᴺ`, `f : M → ℝᵐ` `C¹`, `n = m + k`, `k ≥ 1`,
`C = {x ∈ M : J*_f(x) = 0} = {x ∈ M : rank df_x < m}`. Then `Hᵏ(f⁻¹(y) ∩ C) = 0` for `Lᵐ`-a.e. `y`,
and for every `y`, `f⁻¹(y) ∩ C` is (relatively) closed in `M` and `f⁻¹(y) \ C` is either empty or a
`k`-dimensional `C¹` submanifold (the empty set is vacuously a submanifold). -/
def C1Sard : Prop :=
  ∀ (N m k : ℕ) (M U : Set (Rn N)) (f : Rn N → Rn m), 0 < k →
    Chapter02.IsSimonSubmanifold (E := Rn (m + k)) 1 M → IsOpen U → M ⊆ U →
    ContDiffOn ℝ 1 f U →
    {x ∈ M | coareaJacobian M f x = 0} = {x ∈ M | Module.finrank ℝ
      (LinearMap.range ((fderiv ℝ f x).toLinearMap ∘ₗ (tangentSpace M x).subtype)) < m} ∧
    (∀ᵐ y ∂(volume : Measure (Rn m)),
      μHE[k] (M ∩ f ⁻¹' {y} ∩ {x | coareaJacobian M f x = 0}) = 0) ∧
    ∀ y : Rn m, (∃ F : Set (Rn N), IsClosed F ∧
        M ∩ f ⁻¹' {y} ∩ {x | coareaJacobian M f x = 0} = M ∩ F) ∧
      Chapter02.IsSimonSubmanifold (E := Rn k) 1 ((M ∩ f ⁻¹' {y}) \ {x | coareaJacobian M f x = 0})

end

/-- The frozen Chapter 2 contract: the conjunction of all headline results. -/
theorem main_theorem : LipschitzExtension ∧ Rademacher ∧ C1Approximation ∧ WhitneyExtension ∧ LipschitzImageHausdorff ∧ EilenbergInequality ∧ BVCompactness ∧ BVPoincare ∧ BVExtensionEstimate ∧ AreaFormula ∧ FirstVariation ∧ SecondVariation ∧ StationaryIffMeanCurvatureZero ∧ SecondVariationStationary ∧ CoareaFormula ∧ C1Sard := by sorry

end GMT.Ch02
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `accepted`.

# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.stationary_results-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Introduction to GMT, Ch. 2: §4 (4.21-4.30: divergence theorem, second fundamental form, mean curvature, div_M X^⊥ = −X·H) and §5 (Lemma 5.5(2) and Lemma 5.11 with their printed proofs), pp. 59-65. Errata/readings applied (GMT/Ch02/README.md): in 5.11 the deformation is C³ instead of C²; stationarity is the variational definition IsStationaryIn (finiteness of Hⁿ(M ∩ K) for compact K ⊆ U, and zero first variation for every admissible C² deformation), so the identities used in the printed proofs are derived from it; B is the frame-free form B_y(τ,η) = (D_τP)η (equal to Simon's 4.24, see the contract docstring). The book states the divergence theorem 4.21/4.22(*) without proof; a complete proof of the compact-support version is given in Part II.1. Depends on the siblings variation_formulas (FirstVariation, SecondVariation), area_formula (area formula) and submanifold_tangent (T_yM = range Dψ, M Borel, P continuous on M).

Notation. N := n + ℓ, ℝ^d = EuclideanSpace ℝ (Fin d), Hⁿ := μHE[n]. For y ∈ M: T_y = tangentSpace M y, P_y = tangentProjection M y, τ_i = tangentFrame M y, B_y(τ,η) := secondFundamentalForm M y τ η = fderivWithin ℝ P M y τ η, H(y) := meanCurvature M y = Σ_i B_y(τ_i,τ_i), div_M Y(y) := Σ_i⟨τ_i, DY(y)τ_i⟩ (= trace(P_y DY(y)), basis independent).

PART I. PRINTED PROOFS (cleaned transcription).
4.29-4.30: decompose X = X^T + X^⊥ with X^⊥ = Σ_α(ν^α·X)ν^α; then div_M X^⊥ = Σ_α(ν^α·X)div_M ν^α, so by 4.28 div_M X^⊥ = −X·H; on the other hand ∫_M div_M X^T = −∫_{∂M} X·η by 4.21; hence ∫_M div_M X dHⁿ = −∫_M X·H dHⁿ − ∫_{∂M} X·η dH^{n−1}.
Lemma 5.5. Suppose M is a C² submanifold with mean curvature vector H and U open. (2) If Ū ∩ M is a compact subset of M, then M is stationary in U if and only if H ≡ 0 on M ∩ U. (Printed: in view of 4.30, with the remark after 5.4 that by the first variation formula stationarity is equivalent to ∫_M div_M X dHⁿ = 0 for all C¹ X with compact support in U.)
Lemma 5.11. If M is C², stationary in U, U open with (M̄∖M) ∩ U = ∅, and if X as in 5.4 has compact support in U with X_y ∈ (T_yM)^⊥ for y ∈ M, then 5.4 says d²/dt² Hⁿ(M_t)|_{t=0} = ∫_M (Σ_i|(D_{τ_i}X)^⊥|² − Σ_{i,j}(X·B(τ_i,τ_j))²) dHⁿ. Printed proof: First ∫_M div_M Z dHⁿ = 0 by virtue of the fact that M is stationary in U, and div_M X = −X·H = 0 by virtue of 4.29 and 5.5(2) and the fact that X is normal to M. The proof is then completed by noting that τ_i·D_{τ_j}X = −X·B(τ_i,τ_j) by virtue of 4.24 and the fact that X is normal to M.

PART II. COMPLETE PROOF OF StationaryIffMeanCurvatureZero ∧ SecondVariationStationary.

II.0′ Regularity and support of the initial velocity and acceleration (self-contained; these facts are not part of the exported statements of the siblings). Let φ satisfy IsAdmissibleDeformation r U K φ and Φ(t,x) := φ t x. On U, X = initialVelocity φ = ∂_tΦ(0,·) is C^{r−1} and Z = initialAcceleration φ = ∂²_tΦ(0,·) is C^{r−2} (for x ∈ U and t ∈ (−1,1), deriv (s ↦ φ s x) t = ∂_tΦ(t,x) because Φ is C^r on the open set (−1,1) × U). On the open set ℝᴺ∖K, t ↦ φ t x is constant (= x) on (−1,1), so X = 0 and Z = 0 there. Since K ⊆ U, the open sets U and ℝᴺ∖K cover ℝᴺ; hence X is C^{r−1} and Z is C^{r−2} on ℝᴺ, both vanish on ℝᴺ∖K, and so do their derivatives DX, DZ at every point of ℝᴺ∖K. In particular for r = 2, X is C¹ on ℝᴺ with X = 0 off K; for r = 3, X is C² and Z is C¹ on ℝᴺ, vanishing off K.

II.0 Geometry of a C² Simon submanifold. Let M be an n-dimensional C² Simon submanifold of ℝᴺ and ψ : V → W ∩ M a local representation of class ≥ 2 with ψ(x₀) = y₀. Write ∂_kψ, ∂_k∂_lψ for partial derivatives, g_kl := ⟨∂_kψ, ∂_lψ⟩ (C¹, positive definite), (g^{kl}) its inverse, √g := √det(g_kl) = Jψ.
G0 (projection onto the range of an injective map). For an injective linear A : ℝⁿ → ℝᴺ, A*A is invertible and Π(A) := A(A*A)⁻¹A* satisfies Π(A)* = Π(A), Π(A)² = Π(A), Π(A)A = A and Π(A)w = 0 for w ⊥ range A (A*w = 0); hence Π(A) is the orthogonal projection onto range A. The set of injective A is open and A ↦ Π(A) is C^∞ there (composition, adjoint and inversion of invertible operators are smooth). Since tangentSpace M ψ(x) = range Dψ(x) (submanifold_tangent), P_{ψ(x)} = Π(Dψ(x)) for x ∈ V.
G1 (P is C¹ along M). By G0, P∘ψ = Π∘Dψ is C¹ on V (Dψ is C¹ because ψ is C²). Choose a linear isomorphism Q₀ : ℝ^ℓ → (range Dψ(x₀))^⊥ and apply the inverse function theorem to Ξ(x,w) := ψ(x) + Q₀w (C², DΞ(x₀,0) invertible): there are open O ∋ y₀ and a C² map π : O → V with π(ψ(x)) = x for x near x₀; shrinking, by 4.2 (SimonGMT exists_open_image_eq_inter) O ∩ M = ψ(V₀) for an open V₀ on which π∘ψ = id. Then P̃ := Π(Dψ(π(·))) is C¹ on O and P̃ = P on O ∩ M. Hence HasFDerivWithinAt P (DP̃(y)) M y for y ∈ O ∩ M, and since any two derivatives within M agree on the tangent cone of M at y, which contains T_y (every v ∈ T_y is γ′(0) for a C¹ curve in M, by submanifold_tangent), B_y(τ,η) = DP̃(y)[τ]η for τ ∈ T_y (independent of the choice made by fderivWithin).
G2 (formula, symmetry, normality). For y = ψ(x), τ = Dψ(x)a, η = Dψ(x)b: differentiating P̃(ψ(x′))Dψ(x′)b = Dψ(x′)b at x′ = x in direction a gives B_y(τ,η) + P_y D²ψ(x)[a,b] = D²ψ(x)[a,b], so B_y(τ,η) = (I − P_y)D²ψ(x)[a,b]: B_y is symmetric on T_y × T_y with values in T_y^⊥. Writing τ_i = Dψ(x)a_i one has Σ_i a_i a_iᵀ = (g_kl)⁻¹, hence H(ψ(x)) = (I − P_{ψ(x)}) Σ_{k,l} g^{kl}(x)∂_k∂_lψ(x); in particular H is continuous on M.
G3 (normal fields). Each DP̃(y)[τ] is self-adjoint (derivative of a self-adjoint-valued map). If Y is C¹ near y ∈ M and P_zY(z) = 0 for all z ∈ M near y, then for τ, η ∈ T_y: ⟨η, DY(y)τ⟩ = −⟨Y(y), B_y(τ,η)⟩. Proof: z ↦ P̃(z)Y(z) is C¹ on O and vanishes on O ∩ M, so its derivative vanishes on T_y (derivative along C¹ curves in M): DP̃(y)[τ]Y(y) + P_y DY(y)τ = 0; pair with η ∈ T_y and use self-adjointness: ⟨η, DY(y)τ⟩ = ⟨η, P_yDY(y)τ⟩ = −⟨DP̃(y)[τ]η, Y(y)⟩.

II.1 Divergence identity (4.22(*) + 4.29 ⇒ 4.30 without boundary). Claim D: let M be a C² Simon submanifold, Y : ℝᴺ → ℝᴺ of class C¹ with Y = 0 outside a closed set S such that M ∩ S is compact. Then div_M Y and ⟨Y,H⟩ are bounded, continuous on M, vanish on M∖S, are integrable for Hⁿ⌊M, and ∫_M div_M Y dHⁿ = −∫_M ⟨Y, H⟩ dHⁿ.
1. Chart formula. In a C² chart, let a^j := Σ_k g^{jk}⟨Y∘ψ, ∂_kψ⟩ (C¹), so P(Y)∘ψ = Σ_j a^j∂_jψ, and Y^⊥ := (I − P∘ψ)(Y∘ψ) (C¹). Since div_M Y(ψ(x)) is the trace of P DY on T in the basis ∂_kψ, div_M Y∘ψ = Σ_{k,l} g^{kl}⟨∂_kψ, ∂_l(Y∘ψ)⟩. Expanding ∂_l(Y∘ψ) = Σ_j(∂_la^j ∂_jψ + a^j∂_l∂_jψ) + ∂_lY^⊥ and using ⟨∂_kψ, ∂_lY^⊥⟩ = −⟨∂_l∂_kψ, Y^⊥⟩ (differentiate ⟨∂_kψ, Y^⊥⟩ ≡ 0): div_M Y∘ψ = Σ_j ∂_ja^j + Σ_j a^j Σ_{k,l}g^{kl}⟨∂_kψ, ∂_l∂_jψ⟩ − ⟨Y^⊥, Σ_{k,l}g^{kl}∂_k∂_lψ⟩. Jacobi's formula gives ∂_j√g = ½√g Σ_{k,l}g^{kl}∂_jg_kl = √g Σ_{k,l}g^{kl}⟨∂_kψ, ∂_j∂_lψ⟩, and by G2 ⟨Y, H⟩∘ψ = ⟨Y^⊥, Σ_{k,l}g^{kl}∂_k∂_lψ⟩. Therefore (div_M Y + ⟨Y,H⟩)∘ψ · √g = Σ_j ∂_j(√g a^j) on V.
2. Localized identity. If ζ ∈ C_c^∞(ℝᴺ) has support in W, then ∫_M (div_M(ζY) + ⟨ζY, H⟩) dHⁿ = 0. Indeed ζY vanishes on a neighbourhood of every point of M∖spt ζ, so the integrand vanishes off ψ(Q) with Q := V ∩ ψ⁻¹(spt ζ) compact (properness); the corresponding coefficients ã^j vanish off Q; by the weighted area formula for ψ (Jψ = √g; SimonGMT integral_area_formula_of_injective_derivative / IsSimonLocalRepresentation.weighted_area_formula) the integral equals ∫_V Σ_j ∂_j(√g ã^j) dx, and each √g ã^j extends by 0 to a C¹ function with compact support on ℝⁿ, whose partial derivatives integrate to 0 (Fubini and the fundamental theorem of calculus on lines).
3. Partition of unity. Cover the compact M ∩ S by finitely many chart targets W_1, …, W_p (every point of M lies in one). For each y ∈ M ∩ S pick ρ_y > 0 with B̄(y,2ρ_y) ⊆ some W_i; finitely many balls B(y_q, ρ_q) cover M ∩ S; take bumps β_q ∈ C_c^∞(B(y_q,2ρ_q)), 0 ≤ β_q ≤ 1, β_q = 1 on B̄(y_q,ρ_q), and ζ_1 := β_1, ζ_q := β_q Π_{l<q}(1 − β_l). Then each ζ_q is supported in a chart target, and Σ_q ζ_q = 1 − Π_q(1 − β_q) = 1 on the open set O′ := ∪_q B(y_q,ρ_q) ⊇ M ∩ S. At points of M ∩ O′, Σ_qζ_qY = Y near the point; at points of M∖S, Y = 0 and all ζ_qY vanish near the point (S closed). Hence div_M Y = Σ_q div_M(ζ_qY) and ⟨Y,H⟩ = Σ_q⟨ζ_qY,H⟩ on M, and summing step 2 over q gives Claim D. Boundedness/integrability: the integrands are continuous on M (P and H continuous, Y ∈ C¹), vanish off the compact M ∩ S, and Hⁿ(M ∩ S) < ∞ (M ∩ S is covered by finitely many sets ψ_i(Q_i), Q_i compact, and Hⁿ(ψ_i(Q_i)) ≤ Lip(ψ_i|Q_i)ⁿLⁿ(Q_i) < ∞).

II.2 Lemma 5.5(2) (StationaryIffMeanCurvatureZero). Let M be a C² Simon submanifold of ℝ^{n+ℓ}, U open, closure U ∩ M compact.
4. For every compact K ⊆ U, M ∩ K = (closure U ∩ M) ∩ K is compact, hence Hⁿ(M ∩ K) < ∞ (as in step 3).
5. (⇐) Assume H = 0 on M ∩ U. The finiteness part of IsStationaryIn is step 4. Let φ be admissible of class 2 with compact K ⊆ U. If U ∩ M = ∅ then φ_t(M ∩ K) = ∅, deformedArea ≡ 0 and HasDerivAt _ 0 0 holds. Otherwise FirstVariation (C² ⇒ C¹ submanifold; finiteness from step 4) gives HasDerivAt (deformedArea n M K φ) (∫_M div_M X dHⁿ) 0, X = initialVelocity φ, which is C¹ on ℝᴺ and vanishes off K (II.0′ with r = 2). Claim D with S = K (M ∩ K compact) gives ∫_M div_M X = −∫_M⟨X,H⟩ = 0, because X = 0 off K ⊆ U and H = 0 on M ∩ U. So M is stationary in U.
6. (⇒) Assume M is stationary in U. Let ζ ∈ C_c^∞(U) be real, e ∈ ℝᴺ a unit vector, Y := ζe, S := spt ζ ⊆ U, and λ := 1/(1 + sup|DY|). Define φ_t(x) := x + λtY(x). Then φ is admissible of class 2 for U with compact set S: it is C^∞ in (t,x); φ_0 = id; φ_t = id off S; for |t| < 1, x ↦ x + λtY(x) is injective (|λtY(x) − λtY(x′)| ≤ λ sup|DY||x − x′| < |x − x′|) and surjective (Banach fixed point for the contraction x ↦ z − λtY(x)), fixes ℝᴺ∖S pointwise, hence maps S onto S and U onto U bijectively; and D_xφ_t = I + λtDY(x) is invertible (‖λtDY‖ < 1). Its initial velocity is λY. If U ∩ M = ∅ there is nothing to prove. Otherwise stationarity gives HasDerivAt A 0 0 and FirstVariation gives HasDerivAt A (λ∫_M div_M Y) 0; uniqueness of derivatives gives ∫_M div_M Y = 0, and Claim D (M ∩ S compact by step 4-type reasoning, S ⊆ U compact) gives ∫_M ζ⟨e, H⟩ dHⁿ = 0 for all such ζ, e.
7. Suppose ⟨e, H(y₀)⟩ > 0 for some y₀ ∈ M ∩ U and unit e. By continuity of H on M (G2) choose ρ > 0 with B̄(y₀,2ρ) ⊆ U and ⟨e,H⟩ > c > 0 on M ∩ B(y₀,2ρ), and ζ ∈ C_c^∞(B(y₀,2ρ)) with 0 ≤ ζ ≤ 1, ζ = 1 on B(y₀,ρ). Then ∫_M ζ⟨e,H⟩ ≥ c·Hⁿ(M ∩ B(y₀,ρ)) > 0: indeed M ∩ B(y₀,ρ) ⊇ ψ(V′) for a nonempty open V′ (chart at y₀, continuity of ψ) and Hⁿ(ψ(V′)) = ∫_{V′} Jψ dLⁿ > 0 because Jψ > 0 (Dψ injective). This contradicts step 6; replacing e by −e excludes ⟨e,H(y₀)⟩ < 0. Hence H(y₀) = 0 for all y₀ ∈ M ∩ U. Steps 5-7 prove StationaryIffMeanCurvatureZero.

II.3 Lemma 5.11 (SecondVariationStationary). Let M be a C² Simon submanifold, U open with (closure M∖M) ∩ U = ∅, M stationary in U, φ admissible of class 3 with compact K ⊆ U, and X := initialVelocity φ normal: ⟨X(y), v⟩ = 0 for y ∈ M, v ∈ T_y.
8. Local compactness: for compact S ⊆ U, M ∩ S is compact (a limit of points of M ∩ S lies in S ⊆ U and in closure M, hence in M).
9. H = 0 on M ∩ U. Fix y₀ ∈ M ∩ U, ρ > 0 with B̄(y₀,ρ) ⊆ U, U′ := B(y₀,ρ). Then closure U′ ∩ M = B̄(y₀,ρ) ∩ M is compact (step 8). M is stationary in U′: finiteness is inherited from U; and an admissible C² deformation φ′ of U′ with compact K′ ⊆ U′ is also admissible for U (C² on (−1,1) × U′ and, being x ↦ x, on the open set (−1,1) × (ℝᴺ∖K′), which together cover (−1,1) × U; φ′_0 = id on U; φ′_t maps U′ onto U′ bijectively and fixes U∖U′ ⊆ ℝᴺ∖K′, hence is a bijection of U; fderiv ℝ φ′_t x is the identity for x ∈ U∖K′), with the same deformedArea; so stationarity in U gives HasDerivAt (deformedArea n M K′ φ′) 0 0. By II.2 (⇒) applied to (M, U′), H(y₀) = 0.
10. ∫_M div_M Z dHⁿ = 0 for Z := initialAcceleration φ: Z is C¹ on ℝᴺ and vanishes off K (II.0′ with r = 3), M ∩ K is compact (step 8), so Claim D gives ∫_M div_M Z = −∫_M ⟨Z, H⟩ = 0 by step 9.
11. Pointwise identity. For y ∈ M∖K, X, Z, DX, DZ vanish at y (II.0′), so secondVariationIntegrand M φ y = 0 = stableSecondVariationIntegrand M φ y. For y ∈ M ∩ K ⊆ M ∩ U, X is C² near y and P_zX(z) = 0 for z ∈ M, so by G3 ⟨τ_j, DX(y)τ_i⟩ = −⟨X(y), B_y(τ_i,τ_j)⟩. Hence div_M X(y) = Σ_i⟨τ_i, DXτ_i⟩ = −⟨X(y), H(y)⟩ = 0 (step 9), and, by symmetry of B_y (G2), Σ_{i,j}⟨τ_i, DXτ_j⟩⟨τ_j, DXτ_i⟩ = Σ_{i,j}⟨X, B_y(τ_j,τ_i)⟩⟨X, B_y(τ_i,τ_j)⟩ = Σ_{i,j}⟨X(y), B_y(τ_i,τ_j)⟩². Therefore secondVariationIntegrand M φ y = div_M Z(y) + stableSecondVariationIntegrand M φ y for every y ∈ M.
12. Conclusion. If U ∩ M = ∅ then deformedArea n M K φ t = 0 for t ∈ (−1,1) (φ_t(M ∩ K) = ∅), so it is differentiable near 0 with deriv = 0 near 0, HasDerivAt (deriv _) 0 0, and ∫_M stableSecondVariationIntegrand = 0 because the integrand vanishes on M = M∖K. Otherwise SecondVariation (C² ⇒ C¹; finiteness from IsStationaryIn; U ∩ M ≠ ∅) gives ∀ᶠ t in 𝓝 0, DifferentiableAt ℝ (deformedArea n M K φ) t and HasDerivAt (deriv (deformedArea n M K φ)) (∫_M secondVariationIntegrand M φ y dHⁿ) 0. Measurability and integrability (the frame τ_i = tangentFrame M y is an arbitrary, possibly discontinuous choice, so basis-free expressions are used): div_M Z(y) = trace(P_y DZ(y)); and for every y ∈ M, by step 11 and Pythagoras, stableSecondVariationIntegrand M φ y = Σ_i|(DXτ_i)^⊥|² − Σ_{i,j}⟨τ_j, DX(y)τ_i⟩² = trace(P_y DX(y)*(I − P_y)DX(y)P_y) − trace(P_y DX(y)*P_y DX(y)P_y) (for y ∈ M∖K both sides vanish because X(y) = 0 and DX(y) = 0). These are continuous functions of y on M (y ↦ P_y continuous on M by submanifold_tangent; DX, DZ continuous), vanish off the set M ∩ K of finite Hⁿ-measure, and are bounded on the compact M ∩ K; hence they are Hⁿ⌊M-integrable (M is Borel). By step 11, ∫_M secondVariationIntegrand = ∫_M div_M Z + ∫_M stableSecondVariationIntegrand = ∫_M stableSecondVariationIntegrand by step 10. This proves SecondVariationStationary.

## Key steps

1. Regularity and support of X, Z; projection formula P = A(A*A)⁻¹A* and C¹ extension of P near M; B = (I−P)D²ψ, symmetric and normal; H = (I−P)Σg^{kl}∂_k∂_lψ continuous; ⟨η,DYτ⟩ = −⟨Y,B(τ,η)⟩ for normal fields.
2. Divergence identity ∫_M div_M Y = −∫_M⟨Y,H⟩ for C¹ Y vanishing off a closed S with M ∩ S compact: chart formula (div_M Y + ⟨Y,H⟩)√g = Σ∂_j(√g a^j) via Jacobi, area formula, partition of unity.
3. 5.5(2) (⇐): FirstVariation plus the divergence identity; (⇒): deformations x + λtζ(x)e are admissible, so ∫ζ⟨e,H⟩ = 0, and continuity of H with positivity of Hⁿ on chart images gives H = 0.
4. 5.11: localize stationarity to balls to get H = 0 on M ∩ U; ∫ div_M Z = 0 by the divergence identity; pointwise the second-variation integrand equals div_M Z plus the stable integrand; conclude with SecondVariation.

## Reference use

### local-project

Queries:
- `rg -n 'def BVCompactness' -A 10 project/GMT/Ch02/Contract.lean`
- `rg -n 'bvVariationOn|IsLocallyBV' project/GMT/Ch02/README.md`
- `rg -n 'theorem (IsOpen.measure_pos|IsCompact.measure_lt_top|setLIntegral_const|lintegral_add_right|le_div_iff_mul_le|div_lt_top)' mathlib/Mathlib`
- `rg -n 'theorem (_root_.)?(IsOpen.)?measure_pos' mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean; rg -n 'theorem (_root_.)?(IsCompact.)?measure_lt_top' mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/*.lean`
- `rg -n 'theorem (_root_.)?(HasCompactSupport.)?contDiff_convolution_left|theorem integral_lineDeriv_mul_eq|theorem (_root_.)?(Convex.)?addHaar_frontier|theorem convolution_tendsto_right' mathlib/Mathlib`
- `rg -n 'theorem (HasCompactSupport.contDiff_convolution_left|LipschitzWith.integral_lineDeriv_mul_eq|Convex.addHaar_frontier|mul_meas_ge_le_lintegral₀|ContDiffBump.convolution_tendsto_right)' mathlib/Mathlib`
- `rg -n 'exists_isClosed_sdiff_lt|exists_isClosed_diff_lt' mathlib/Mathlib; rg -n 'theorem LipschitzWith.ae_differentiableAt' mathlib/Mathlib/Analysis/Calculus/Rademacher.lean; rg -n 'theorem tendstoUniformlyOn_of_ae_tendsto' mathlib/Mathlib`
- `rg -il 'BoundedVariation|poincare' mathlib/Mathlib`
- `rg -n 'Submission.|theorem .*bv_compactness_poincare_extension|lipschitz_extension_and_rademacher' project`
- `grep -n '^theorem|^def|^noncomputable def' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean, then a full read of BV.lean`
- `python3 -I gen_checks.py (replays verifier gmt-compare.py contract_scope and child_modules for all 12 lean_statements); lake env lean AssemblyCheck.lean and NodeChallenge_00..11.lean against a scratch olean of GMT.Ch02.Submission`
- `#print axioms ChildCheck.unweighted_bound, ChildCheck.bvVariationOn_empty, ChildCheck.main_from_children`
- `read dag.json (active nodes) and nodes/root/decomposition-review-receipt-v1.json`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Convex/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Function/Egorov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root/decomposition-review-receipt-v1.json`
- `/tmp/gmt-ch02-decomp-v2-3S9D56/AssemblyCheck.lean`

Contract.lean:245-252 confirms that BVCompactness integrates the whole sum ‖u k x‖ₑ + bvVariationOn (u k) W over W. README row 7 describes the unweighted printed bound, but the frozen contract is authoritative, so bv_results now proves the conversion (step A0) before A1. The snapshot Mathlib supplies every fact A0 needs: _root_.IsOpen.measure_pos (OpenPos.lean:47), _root_.IsCompact.measure_lt_top (Typeclasses/Finite.lean:346), lintegral_add_right (Lebesgue/Add.lean:339), setLIntegral_const (Lebesgue/Basic.lean:121), ENNReal.le_div_iff_mul_le (ENNReal/Inv.lean:369) and ENNReal.div_lt_top (Inv.lean:214). A0 was kernel-checked as a scratch lemma against the frozen notation; it depends only on propext, Classical.choice and Quot.sound. The pinned SimonGMT BV.lean defines bvVariationOn as an iSup, over Lipschitz C_c fields with tsupport ⊆ W and sup norm ≤ 1, of ofReal ∫_W u·div g. Hence bvVariationOn u ∅ = 0, which was also kernel-checked. The same file provides ofReal_integral_le_bvVariationOn, IsC1TestField.isLipschitzTestField, bvVariationOn_le_liminf_of_locallyL1 and isLocallyBV_of_locallyL1_of_uniform_bound, which are used in A3-A4. Mathlib supplies the Section T tools: HasCompactSupport.contDiff_convolution_left, ContDiffBump.convolution_tendsto_right, LipschitzWith.integral_lineDeriv_mul_eq, Convex.addHaar_frontier and mul_meas_ge_le_lintegral₀. It also has the names cited by the unchanged children: MeasurableSet.exists_isClosed_sdiff_lt (Regular.lean:1036), LipschitzWith.ae_differentiableAt (Rademacher.lean:385) and tendstoUniformlyOn_of_ae_tendsto (Egorov.lean:205). There is no BV compactness, BV Poincaré or BV extension theorem in ℝⁿ; the BoundedVariation matches concern one-dimensional variation and vector measures. The project snapshot has no Submission.* declarations, and dag.json has only the root node, so the twelve bare lean_names do not collide. Using the comparator's own scope replay, all 12 child statements elaborate after import GMT.Ch02.Submission, the 12 generated NodeChallenge modules compile, and the 16-component constructor proves type_of% GMT.Ch02.main_theorem from the children.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
