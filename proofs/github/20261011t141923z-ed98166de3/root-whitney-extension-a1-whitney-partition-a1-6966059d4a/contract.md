<!-- theorem-id: gmt-ch02/root.whitney_extension-a1.whitney_partition-a1 -->

## Theorem `Submission.whitney_smooth_partition_of_unity`

For every n ∈ ℕ and every closed nonempty A ⊆ ℝⁿ = EuclideanSpace ℝ (Fin n), writing d(x) := dist(x, A) (Metric.infDist x A), there exist a type ι, functions φ_i : ℝⁿ → ℝ and points p_i ∈ ℝⁿ (i ∈ ι), and real numbers C ≥ 0, M ≥ 0 such that: (P1) p_i ∈ A for every i; (P2) every φ_i is C¹ at every point x ∉ A; (P3) φ_i(x) ≥ 0 for every i and every x ∉ A; (P4) every x ∉ A has a neighbourhood V and a finite set s ⊆ ι with φ_i(y) = 0 for all i ∉ s and y ∈ V; (P5) Σᶠ_i φ_i(x) = 1 for every x ∉ A; (P6) for x ∉ A, φ_i(x) ≠ 0 implies |x − p_i| ≤ C·d(x); (P7) for x ∉ A with d(x) ≤ 1, Σᶠ_i ‖Dφ_i(x)‖ ≤ M/d(x).

Node: `root.whitney_extension-a1.whitney_partition-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/3

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/34

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/294, https://github.com/ZhengyangZhang06/gmt-formalize/issues/296

## Lean problem

Declaration: `Submission.whitney_smooth_partition_of_unity`

```lean
∀ (n : ℕ) (A : Set (Rn n)), IsClosed A → A.Nonempty → ∃ (ι : Type) (φ : ι → Rn n → ℝ) (p : ι → Rn n) (C M : ℝ), 0 ≤ C ∧ 0 ≤ M ∧ (∀ i, p i ∈ A) ∧ (∀ i, ∀ x ∉ A, ContDiffAt ℝ 1 (φ i) x) ∧ (∀ i, ∀ x ∉ A, 0 ≤ φ i x) ∧ (∀ x ∉ A, ∃ s : Finset ι, ∃ V ∈ 𝓝 x, ∀ i ∉ s, ∀ y ∈ V, φ i y = 0) ∧ (∀ x ∉ A, ∑ᶠ i, φ i x = 1) ∧ (∀ i, ∀ x ∉ A, φ i x ≠ 0 → ‖x - p i‖ ≤ C * Metric.infDist x A) ∧ (∀ x ∉ A, Metric.infDist x A ≤ 1 → ∑ᶠ i, ‖fderiv ℝ (φ i) x‖ ≤ M / Metric.infDist x A)
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

- Parent DAG node: `root.whitney_extension-a1`
- Child DAG node: `root.whitney_extension-a1.whitney_partition-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: this is steps 0-3 and fact (F4) of the parent-supplied proof of WhitneyExtension (Simon, Introduction to GMT, Ch. 2, Theorem 1.6, proof supplied after [EG92], Whitney's extension theorem), extracted as a stand-alone lemma. Notation: ℝⁿ = EuclideanSpace ℝ (Fin n) with Euclidean norm |·|; ‖·‖ is the operator norm of a linear functional; B(x,ρ) and B̄(x,ρ) are the open and closed balls; U := ℝⁿ∖A; d(x) := dist(x, A) = Metric.infDist x A.

Claim. Let A ⊆ ℝⁿ be closed and nonempty. There are a type ι, functions φ_i : ℝⁿ → ℝ, points p_i ∈ ℝⁿ (i ∈ ι) and reals C ≥ 0, M ≥ 0 with
(P1) p_i ∈ A for every i;
(P2) every φ_i is C¹ at every point of U (ContDiffAt ℝ 1);
(P3) φ_i(x) ≥ 0 for every i and x ∈ U;
(P4) every x ∈ U has a neighbourhood V and a finite set s ⊆ ι with φ_i ≡ 0 on V for all i ∉ s;
(P5) Σᶠ_i φ_i(x) = 1 for every x ∈ U;
(P6) if x ∈ U and φ_i(x) ≠ 0, then |x − p_i| ≤ C·d(x);
(P7) if x ∈ U and d(x) ≤ 1, then Σᶠ_i ‖Dφ_i(x)‖ ≤ M/d(x).

Proof.

1. Distance and scale. Because A is closed and nonempty: d is 1-Lipschitz; d(x) ≤ |x − a| for a ∈ A (infDist_le_dist_of_mem); d(x) > 0 exactly for x ∈ U (IsClosed.notMem_iff_infDist_pos); and, ℝⁿ being proper, every y ∈ ℝⁿ has a nearest point a ∈ A with |y − a| = d(y) (IsClosed.exists_infDist_eq_dist). U is open. Put r(x) := min{1, d(x)}/20. Then 0 ≤ r(x) ≤ 1/20, r(x) ≤ d(x)/20, r(x) > 0 for x ∈ U, r(x) = d(x)/20 whenever d(x) ≤ 1, and |r(x) − r(y)| ≤ |x − y|/20 for all x, y (t ↦ min{1,t} is 1-Lipschitz). For n = 0 the space is a single point, so A = ℝ⁰ and U = ∅; then the construction below produces the empty family and (P1)-(P7) hold vacuously (with C = 3, M as below).

2. Covering. Apply the Vitali covering lemma (Mathlib Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall with index set U, centres x ↦ x, radii r, bound R := 1/20 and τ := 5 > 3). It gives J ⊆ U such that the closed balls B̄(s, r(s)), s ∈ J, are pairwise disjoint and every x ∈ U has some s ∈ J with B̄(x, r(x)) ⊆ B̄(s, 5r(s)); in particular |x − s| ≤ 5r(s). Write r_s := r(s); r_s > 0 because s ∈ U. (If U = ∅ then J = ∅.)

3. (F1) Comparable radii. Let s ∈ J and |x − s| ≤ 10r_s. Then |r(x) − r_s| ≤ |x − s|/20 ≤ r_s/2, so r_s/2 ≤ r(x) ≤ 3r_s/2, i.e. (2/3)r(x) ≤ r_s ≤ 2r(x). Moreover d(s) ≥ 20r_s (since r_s ≤ d(s)/20), so d(x) ≥ d(s) − |x − s| ≥ 10r_s > 0 and x ∈ U.

4. (F2) Bounded overlap. For x ∈ U let J(x) := {s ∈ J : |x − s| < 10r_s}. Claim: J(x) is finite and #J(x) ≤ N, where N := 33ⁿ depends only on n. For s ∈ J(x), (F1) gives r_s ≥ (2/3)r(x) and r_s ≤ 2r(x), so B̄(s, r_s) ⊆ B̄(x, |x − s| + r_s) ⊆ B̄(x, 11r_s) ⊆ B̄(x, 22r(x)). These closed balls are pairwise disjoint and each has Lebesgue measure at least the measure of a ball of radius (2/3)r(x) > 0. Hence for every finite F ⊆ J(x), comparing Lebesgue measures (measure of a ball of radius ρ = ρⁿ × measure of the unit ball), #F·((2/3)r(x))ⁿ ≤ (22r(x))ⁿ, i.e. #F ≤ 33ⁿ. Therefore J(x) is finite with #J(x) ≤ 33ⁿ. (Equivalently: distinct s, t ∈ J(x) satisfy |s − t| > r_s + r_t ≥ (4/3)r(x) by disjointness, so the rescaled points (s − x)/r(x), s ∈ J(x), form a (4/3)-separated subset of the fixed compact ball B̄(0, 20); a separated subset of a fixed compact set has cardinality bounded by a constant depending only on n. Any such uniform N may be used below.)

5. (F3) Local finiteness. For x₀ ∈ U let J'(x₀) := {s ∈ J : B(s, 10r_s) ∩ B(x₀, r(x₀)) ≠ ∅}. Then J(x) ⊆ J'(x₀) for every x ∈ B(x₀, r(x₀)) (x lies in both balls), and J'(x₀) is finite: if z ∈ B(s, 10r_s) ∩ B(x₀, r(x₀)), then (F1) at z gives (2/3)r(z) ≤ r_s ≤ 2r(z), while |r(z) − r(x₀)| ≤ |z − x₀|/20 < r(x₀)/20; hence r_s ≥ (2/3)(19/20)r(x₀) ≥ r(x₀)/2 and r_s ≤ 2(21/20)r(x₀) < 3r(x₀). So |s − x₀| ≤ |s − z| + |z − x₀| < 10r_s + r(x₀) < 31r(x₀) and B̄(s, r_s) ⊆ B̄(x₀, 34r(x₀)). These are pairwise disjoint balls of radius ≥ r(x₀)/2 > 0 inside B̄(x₀, 34r(x₀)), so by the measure comparison of step 4 there are at most 68ⁿ of them.

6. (F4) Anchors. For each s ∈ J fix a_s ∈ A with |s − a_s| = d(s) (step 1). If x ∈ U and s ∈ J(x), then |x − a_s| < 3d(x). Indeed d(s) ≤ d(x) + |x − s|, so |a_s − x| ≤ |a_s − s| + |s − x| = d(s) + |s − x| ≤ d(x) + 2|s − x| < d(x) + 20r_s ≤ d(x) + 40r(x) ≤ 3d(x), using r_s ≤ 2r(x) from (F1) and r(x) ≤ d(x)/20.

7. Rescaled bumps. Fix a C^∞ function θ : ℝⁿ → ℝ with 0 ≤ θ ≤ 1, θ = 1 on B̄(0,5) and θ(y) = 0 whenever |y| ≥ 9 (Mathlib: the ContDiffBump centred at 0 with rIn = 5, rOut = 9, whose support is B(0,9)). θ is C¹ with compact support, hence Lipschitz with some constant Λ ≥ 0 (ContDiff.lipschitzWith_of_hasCompactSupport). For s ∈ J let θ_s(x) := θ((x − s)/r_s). Then θ_s is C^∞ on ℝⁿ, 0 ≤ θ_s ≤ 1, θ_s(x) = 1 if |x − s| ≤ 5r_s, θ_s(x) ≠ 0 implies |x − s| < 9r_s, and θ_s is (Λ/r_s)-Lipschitz, so ‖Dθ_s(x)‖ ≤ Λ/r_s for all x (norm_fderiv_le_of_lipschitz). Two vanishing properties:
(7a) If x ∈ U and s ∈ J ∖ J(x), i.e. |x − s| ≥ 10r_s, then θ_s ≡ 0 on B(x, r_s), because |y − x| < r_s gives |y − s| > 9r_s; hence Dθ_s(x) = 0.
(7b) If x₀ ∈ U, s ∈ J ∖ J'(x₀) and y ∈ B(x₀, r(x₀)), then θ_s(y) = 0; otherwise |y − s| < 9r_s and y ∈ B(s, 10r_s) ∩ B(x₀, r(x₀)), i.e. s ∈ J'(x₀).

8. Normalising sum. Let Σ(x) := Σᶠ_{s∈J} θ_s(x). Fix x₀ ∈ U and put F := J'(x₀) (finite by step 5). By (7b), Σ(y) = Σ_{s∈F} θ_s(y) for all y ∈ B(x₀, r(x₀)), which is a neighbourhood of x₀. Hence Σ is C^∞ at x₀ and DΣ(x₀) = Σ_{s∈F} Dθ_s(x₀) = Σ_{s∈J(x₀)} Dθ_s(x₀) (by (7a), since J(x₀) ⊆ F). Using r_s ≥ (2/3)r(x₀) for s ∈ J(x₀) (F1) and #J(x₀) ≤ N (F2): ‖DΣ(x₀)‖ ≤ Σ_{s∈J(x₀)} Λ/r_s ≤ (3/2)NΛ/r(x₀). Moreover Σ(x₀) ≥ 1: by step 2 some s₀ ∈ J has |x₀ − s₀| ≤ 5r_{s₀}, so θ_{s₀}(x₀) = 1, and every other term of the finite sum is ≥ 0.

9. The family and verification. Let ι be the type of elements of J (the subtype {s // s ∈ J} of ℝⁿ). For s ∈ J put φ_s(x) := θ_s(x)/Σ(x) and p_s := a_s, and let C := 3 and M := 30ΛN(N + 1). Clearly C ≥ 0 and M ≥ 0.
(P1) p_s = a_s ∈ A.
(P2) Let x ∈ U. θ_s and Σ are C^∞ at x and Σ(x) ≥ 1 ≠ 0, so φ_s = θ_s/Σ is C^∞, in particular C¹, at x.
(P3) For x ∈ U, θ_s(x) ≥ 0 and Σ(x) ≥ 1 > 0, so φ_s(x) ≥ 0.
(P4) For x₀ ∈ U take the finite set J'(x₀) (step 5) and V := B(x₀, r(x₀)), a neighbourhood of x₀ because r(x₀) > 0. For s ∉ J'(x₀) and y ∈ V, (7b) gives θ_s(y) = 0, hence φ_s(y) = 0.
(P5) For x ∈ U, (7b) with x₀ := x shows that s ↦ θ_s(x) and s ↦ φ_s(x) are supported in the finite set J'(x); hence Σᶠ_s φ_s(x) = Σ_{s∈J'(x)} θ_s(x)/Σ(x) = Σ(x)/Σ(x) = 1.
(P6) If x ∈ U and φ_s(x) ≠ 0, then θ_s(x) ≠ 0, so |x − s| < 9r_s < 10r_s, i.e. s ∈ J(x), and (F4) gives |x − p_s| < 3d(x) = C·d(x).
(P7) Let x ∈ U with d(x) ≤ 1, so r(x) = d(x)/20. If s ∉ J(x), then θ_s, hence φ_s, vanishes on B(x, r_s) by (7a), so Dφ_s(x) = 0. If s ∈ J(x), the quotient rule gives Dφ_s(x) = Dθ_s(x)/Σ(x) − θ_s(x)·DΣ(x)/Σ(x)², and with Σ(x) ≥ 1, 0 ≤ θ_s(x) ≤ 1, ‖Dθ_s(x)‖ ≤ Λ/r_s ≤ (3/2)Λ/r(x) and step 8, ‖Dφ_s(x)‖ ≤ ‖Dθ_s(x)‖ + ‖DΣ(x)‖ ≤ (3/2)Λ(N + 1)/r(x). Therefore s ↦ ‖Dφ_s(x)‖ is supported in the finite set J(x) and Σᶠ_s ‖Dφ_s(x)‖ = Σ_{s∈J(x)} ‖Dφ_s(x)‖ ≤ N·(3/2)Λ(N + 1)/r(x) = 30ΛN(N + 1)/d(x) = M/d(x).
This proves (P1)-(P7). ∎

Remarks for formalization. (i) Finite sums: finsum_eq_sum_of_support_subset; derivative of a sum that is locally a finite sum: Filter.EventuallyEq.fderiv_eq and fderiv_fun_sum (or HasFDerivAt.sum); ContDiffAt ℝ ∞ implies ContDiffAt ℝ 1 by ContDiffAt.of_le. (ii) The constants are immaterial: any construction giving (P1)-(P7) with some C, M ≥ 0 suffices. The pinned SimonGMT sources Poincare/SimonGMT/Chapter02/WhitneyCover.lean, WhitneyPartition.lean, the nearest-anchor section of WhitneyJet.lean and the anchor lemma WhitneyBallCover.dist_near_anchor_le of WhitneyExtension.lean implement this construction with r = min{1,d}/100, enlargement 4 and bump radii 4 < 8 (exists_whitneyBallCover, whitneyWeight_contDiffAt, whitneyWeight_nonneg, whitneyWeight_eq_zero_of_notMem_nearFinset, sum_whitneyWeight_near, WhitneyBallCover.dist_near_anchor_le giving C = 2, exists_sum_norm_fderiv_whitneyWeight_bound giving M = 100·M₀ since whitneyRadius = d/100 when d ≤ 1). The prebuilt .olean files of those Whitney modules in the shared package tree are stale for Lake (lake build --no-build reports WhitneyCover and WhitneyJet as needing a rebuild), so do not import them from the submission; port their source into chapter-local modules (dropping the module/public keywords), which compiles with the pinned toolchain.

## Key steps

1. Scale r = min{1, d}/20 on U = ℝⁿ∖A; the Vitali lemma (τ = 5) selects pairwise disjoint balls B̄(s, r_s), s ∈ J, whose 5-fold enlargements cover U.
2. Geometry of the cover: comparable radii (F1), uniform overlap bound #J(x) ≤ N (F2), local finiteness of the 10-fold balls (F3), and nearest-point anchors a_s ∈ A with |x − a_s| < 3d(x) for s ∈ J(x) (F4).
3. Rescaled bumps θ_s = θ((· − s)/r_s) with ‖Dθ_s‖ ≤ Λ/r_s that vanish off B(s, 9r_s); their locally finite sum Σ is smooth on U with Σ ≥ 1 and ‖DΣ‖ ≤ (3/2)NΛ/r.
4. Set φ_s = θ_s/Σ, p_s = a_s, C = 3, M = 30ΛN(N+1), and verify (P1)-(P7) using the vanishing properties, the quotient rule and r = d/20 when d ≤ 1.

## Reference use

### local-project

Queries:
- `grep -n 'WhitneyExtension' -A 20 GMT/Ch02/Contract.lean; cmp local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean workspace GMT/Ch02/Contract.lean`
- `grep -n '^theorem\|^lemma\|^def\|^structure' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Whitney*.lean, then full reads of WhitneyJet/WhitneyCover/WhitneyPartition/WhitneyExtension.lean`
- `grep -rn 'Whitney' --include=*.lean simongmt/Poincare | grep import; cat simongmt/Poincare/SimonGMT.lean; ls simongmt/.lake/build/lib/lean/Poincare/SimonGMT/Chapter02/ | grep -i whitney`
- `rg -n 'exists_disjoint_subfamily_covering_enlargement_(closedBall|ball)' mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `rg -n 'structure ContDiffBump|one_of_mem_closedBall|theorem support_eq|protected theorem contDiff|hasCompactSupport' mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `rg -n 'exists_infDist_eq_dist|notMem_iff_infDist_pos|infDist_le_dist_of_mem|lipschitz_infDist_pt|infDist_le_infDist_add_dist' mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `rg -n 'theorem (contDiff_one_iff_fderiv|ContDiffAt.continuousAt_fderiv|IsLocalMin.fderiv_eq_zero|Filter.EventuallyEq.fderiv_eq|ContDiff.lipschitzWith_of_hasCompactSupport|norm_fderiv_le_of_lipschitz|fderiv_fun_sum|innerSL_apply|IsCompact.uniformContinuousOn_of_continuous)' mathlib/Mathlib`
- `lake build --no-build Poincare.SimonGMT.Chapter02.WhitneyPartition Poincare.SimonGMT.Chapter02.WhitneyJet (scratch project whose .lake/packages holds an isolated copy of simongmt)`
- `lean WhitneyExtensionCopy.lean; lean -o WhitneyPort/{Cover,Jet,Partition,Extension}.olean (non-module port of the four SimonGMT Whitney sources)`
- `python3 -I gen.py (gmt-compare.py child_modules/contract_scope + lean_contract.validate_lean_statement); lean NodeChallenge_00.lean NodeChallenge_01.lean; lean AssemblyCheck.lean; lean Child1Check.lean (against scratch olean of GMT.Ch02.Submission)`
- `#print axioms GMT.Ch02.assembly_check, GMT.Ch02.child1_check, Poincare.SimonGMT.Chapter02.exists_contDiff_one_extension_of_whitney, exists_sum_norm_fderiv_whitneyWeight_bound, HasWhitneyC1Compatibility.continuousAt_fderiv_whitneyExtension`
- `grep -rhoE 'whitney[A-Za-z0-9_]*' --include=*.json run directory; dag.json node lean_names`
- `find lake-packages-25730c7c/*/.lake -newer children-v1.json (shared tree untouched)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/LocalExtr/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/LinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/UniformSpace/HeineCantor.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyJet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyPartition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-whitney-extension-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-whitney-extension-a1/parent-supplied-natural-proof.md`
- `/tmp/whitney-decomp-check/gen-v1/NodeChallenge_00.lean`
- `/tmp/whitney-decomp-check/gen-v1/NodeChallenge_01.lean`
- `/tmp/whitney-decomp-check/asm/AssemblyCheck.lean`
- `/tmp/whitney-decomp-check/c1/Child1Check.lean`

Contract and library:
- The snapshot Contract.lean is byte-identical to the workspace contract, and lines 208-213 fix WhitneyExtension.
- README row 4 marks the theorem as new work.
- Mathlib 25730c7c has no Whitney extension theorem.
- Mathlib does supply every tool the children cite:
  - Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall (Vitali.lean:158);
  - ContDiffBump with one_of_mem_closedBall, support_eq, contDiff and hasCompactSupport (BumpFunction/Basic.lean:70-209);
  - IsClosed.exists_infDist_eq_dist (:615), IsClosed.notMem_iff_infDist_pos (:584), infDist_le_dist_of_mem (:500) and lipschitz_infDist_pt (:547), all in HausdorffDistance.lean;
  - contDiff_one_iff_fderiv (ContDiff/Defs.lean:1261);
  - ContDiffAt.continuousAt_fderiv (ContDiff/Comp.lean:816; its hypothesis is n ≠ 0);
  - ContDiff.lipschitzWith_of_hasCompactSupport (RCLike.lean:156);
  - norm_fderiv_le_of_lipschitz (FDeriv/Basic.lean:947);
  - Filter.EventuallyEq.fderiv_eq (FDeriv/Congr.lean:260);
  - fderiv_fun_sum and HasFDerivAt.sum (FDeriv/Add.lean);
  - IsLocalMin.fderiv_eq_zero (LocalExtr/Basic.lean:181);
  - innerSL_apply_apply (InnerProductSpace/LinearMap.lean:172).

SimonGMT reuse:
- The pinned simongmt package contains a complete general-E Whitney C¹ development in WhitneyCover, WhitneyJet, WhitneyPartition and WhitneyExtension, ending in exists_contDiff_one_extension_of_whitney. Poincare/SimonGMT.lean imports none of these files.
- WhitneyExtension has no .olean.
- lake build --no-build, run on an isolated copy of the package, reports the prebuilt WhitneyCover and WhitneyJet as out of date, so children must port the source rather than import it.
- A non-module port of all four files compiles with the pinned toolchain without errors.
- exists_contDiff_one_extension_of_whitney, exists_sum_norm_fderiv_whitneyWeight_bound and continuousAt_fderiv_whitneyExtension depend only on propext, Classical.choice and Quot.sound.

Checks on the proposed split:
- Both child lean_statements pass validate_lean_statement and elaborate in the verifier-generated NodeChallenge modules.
- AssemblyCheck proves WhitneyExtension from the two exact child types, using only the three standard axioms.
- Child1Check proves the exact partition-of-unity type from the ported SimonGMT API, again using only the three standard axioms.
- No run JSON or DAG node reserves either proposed name.
- No shared-package file was modified.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: https://github.com/ZhengyangZhang06/gmt-formalize/pull/1337

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
