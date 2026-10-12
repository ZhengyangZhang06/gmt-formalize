<!-- theorem-id: gmt-ch02/root.bv_results-a1 -->

## Theorem `Submission.bv_compactness_poincare_extension`

(2.6) If U ⊆ ℝⁿ and u_k (k ∈ ℕ) are locally BV on U (SimonGMT IsLocallyBV) and, for every open W ⊂⊂ U, sup_k ∫_W (|u_k(x)| + |Du_k|(W)) dLⁿ(x) < ∞, where |Du|(W) = SimonGMT bvVariationOn u W is an x-independent constant inside the integrand (so the hypothesis is sup_k (∫_W|u_k| + Lⁿ(W)·|Du_k|(W)) < ∞; Lean: ⨆ k, (∫⁻ x in W, ‖u k x‖ₑ + bvVariationOn (u k) W) < ⊤), then a subsequence u_{ψ(k)} (ψ strictly increasing) converges in L¹_loc(U) to a locally BV v with |Dv|(W) ≤ liminf |Du_{ψ(k)}|(W) for all open W ⊂⊂ U. (2.7) For all n and θ, δ ∈ (0,1) there is C ≥ 0 such that for bounded open convex U, R > 0, ξ ∈ U with B̄(ξ,δR) ⊆ U ⊆ B̄(ξ,R), u ∈ BV(U) (u ∈ L¹(U), |Du|(U) < ∞) and β with θLⁿ(U) ≤ min(Lⁿ{u ≥ β}, Lⁿ{u ≤ β}) (sets inside U): ∫_U|u − β| ≤ C R |Du|(U). (2.8) For all n and δ ∈ (0,1) there is C ≥ 0 such that for U, R, ξ as in 2.7 and u ∈ BV(ℝⁿ) with u = 0 a.e. off Ū: |Du|(ℝⁿ∖Ū) = 0 and |Du|(ℝⁿ) ≤ C(|Du|(U) + R⁻¹∫_U|u|).

Node: `root.bv_results-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/3

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/3

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/162, https://github.com/ZhengyangZhang06/gmt-formalize/issues/163, https://github.com/ZhengyangZhang06/gmt-formalize/issues/164, https://github.com/ZhengyangZhang06/gmt-formalize/issues/165, https://github.com/ZhengyangZhang06/gmt-formalize/issues/166, https://github.com/ZhengyangZhang06/gmt-formalize/issues/167, https://github.com/ZhengyangZhang06/gmt-formalize/issues/168, https://github.com/ZhengyangZhang06/gmt-formalize/issues/169

## Lean problem

Declaration: `Submission.bv_compactness_poincare_extension`

```lean
BVCompactness ∧ BVPoincare ∧ BVExtensionEstimate
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
- Child DAG node: `root.bv_results-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Introduction to GMT, Ch. 2 §2: Lemma 2.5, Theorem 2.6, Lemma 2.7, Lemma 2.8 with their printed proofs (pp. 48-53). Errata/readings applied (GMT/Ch02/README.md): in 2.6 the sets W ⊂⊂ U are taken open (lower semicontinuity fails for non-open W; 2.4 characterizes |Du|(W) only for open W); in 2.7, u ∈ BV(U) includes u ∈ L¹(U); in 2.8, spt u ⊂ Ū means u = 0 a.e. off Ū and ∫_{ℝⁿ}|Du| = ∫_Ū|Du| is encoded as |Du|(ℝⁿ∖Ū) = 0. Frozen form of the 2.6 hypothesis (Contract.lean, BVCompactness): it reads ⨆ k, (∫⁻ x in W, ‖u k x‖ₑ + Chapter02.bvVariationOn (u k) W) < ⊤ for every open W ⊂⊂ U, where the whole sum ‖u k x‖ₑ + bvVariationOn (u k) W is the integrand; that is, sup_k ∫_W (|u_k(x)| + |Du_k|(W)) dLⁿ(x) < ∞ with the x-independent constant |Du_k|(W) inside the integral, which equals sup_k (∫_W |u_k| + Lⁿ(W)·|Du_k|(W)) < ∞. Step A0 below derives from it the printed (unweighted) bound sup_k (∫_W |u_k| + |Du_k|(W)) < ∞ for every open W ⊂⊂ U, and only this derived finite constant is used in A1 and A4. The printed proofs cite [GT01, Thm 7.22] (compactness) and the smooth Poincaré inequality [GT01]; complete arguments are supplied. For 2.8 the printed cut-off argument is kept but the final passage to the limit is done directly on test fields (no product lower-semicontinuity is needed).

Notation (frozen definitions, SimonGMT Chapter02/BV.lean). ℝⁿ = EuclideanSpace ℝ (Fin n), Lⁿ = volume. For a vector field g, div g := trace(fderiv g) (Rademacher a.e. derivative for Lipschitz g). An admissible field for an open set W is a compactly supported Lipschitz g : ℝⁿ → ℝⁿ with tsupport g ⊆ W and sup|g| ≤ 1. |Du|(W) := bvVariationOn u W = sup over admissible g of ofReal(∫_W u div g) ∈ [0,∞]. Since g and −g are both admissible, |∫_W u div g| ≤ (sup|g|)|Du|(W) for every compactly supported Lipschitz g with tsupport g ⊆ W. W ⊆ W′ open ⇒ |Du|(W) ≤ |Du|(W′). IsLocallyBV U u: U open, u ∈ L¹_loc(U), and for each open W ⊂⊂ U a constant c(W) with ∫_W u div g ≤ c(W) sup|g| for C¹ compactly supported g, tsupport g ⊆ W. W ⊂⊂ U: closure W compact and ⊆ U. TendstoLocallyInL1On v u U: ∫_Q |v_i − u| → 0 for every compact Q ⊆ U. IsBVOn U u: U open, u ∈ L¹(U), |Du|(U) < ∞. For an open W and σ > 0 put W^(σ) := {x : dist(x, ℝⁿ∖W) > σ}, an open set, where dist(x, ∅) := +∞ (i.e. use the extended distance infEdist, so W^(σ) = ℝⁿ when W = ℝⁿ). Every point within distance ≤ σ of W^(σ) lies in W.

PART I. PRINTED PROOFS (cleaned transcription).
Lemma 2.5. If u ∈ BV_loc(U) then u_(σ) → u in L¹_loc(U) and |Du_(σ)| → |Du| as Radon measures. (Printed proof: convergence in L¹_loc is standard; (2) ∫ f|Du| ≤ liminf ∫ f|Du_(σ)| by definition of |Du|; for (3) note (4) ∫ f|Du_(σ)| = sup_{|g|≤f, g smooth} ∫ g·∇u_(σ), and for fixed smooth g with |g| ≤ f and σ < dist(spt f, ∂U): ∫ g·∇u_(σ) = −∫ u_(σ) div g = −∫ φ_σ * u div g = −∫ u φ_σ * div g = −∫ u div(φ_σ * g) ≤ ∫_{W_σ}(f + ε(σ))|Du| since |φ_σ * g| ≤ φ_σ * |g| ≤ φ_σ * f and φ_σ * f → f uniformly.)
Theorem 2.6 (printed proof). By virtue of the previous lemma, in order to prove u_{k′} → u in L¹_loc(U) for some subsequence, it is enough to prove that the sets {u ∈ C¹(U) : ∫_W (|u| + |Du|) dLⁿ ≤ c(W)}, W ⊂⊂ U (for given constants c(W) < ∞), are precompact in L¹_loc(U). For the simple proof of this (involving mollification and Arzela's theorem) see [GT01, Thm 7.22]. Finally the fact that ∫_W|Du| ≤ liminf ∫_W |Du_{k′}| is a direct consequence of the definition of |Du|, |Du_{k′}|.
Lemma 2.7 (printed proof). By rescaling x ↦ R⁻¹(x − ξ) we can assume R = 1, ξ = 0. Let β, θ be as in 2.7(*) and choose convex W ⊂⊂ U such that (*) ∫_W |u − β| ≥ ½∫_U |u − β| and such that 2.7(*) holds with W in place of U and θ/2 in place of θ (e.g. W = {x ∈ U : dist(x, ∂U) > σ} with σ small). Letting u_σ denote the mollified functions, for sufficiently small σ we have 2.7(*) with u_σ in place of u, θ/4 in place of θ and W in place of U. Hence by the usual Poincaré inequality for smooth functions we have, with suitable β(σ) → β, ∫_W |u_σ − β(σ)| ≤ c ∫_W |Du_σ|, c = c(n,θ,δ), for all sufficiently small σ. The required inequality follows by letting σ ↓ 0 and using (*) and 2.5.
Lemma 2.8 (printed proof). Assume R = 1, ξ = 0. Let d(x) = dist(x, ∂U). Since U is convex, U_σ = {x : dist(x,∂U) > σ} is convex for each σ ≥ 0 […] and 0 < d(x) < d(y) ⇒ (y − x)·Dd(x) ≥ 0 for all x ∈ U at which d is differentiable. Since B_δ(0) ⊆ U and |Dd(x)| = 1 at points of differentiability in U, taking y = −δDd(x) gives (1) x·Dd(x) ≤ −δ for a.e. x ∈ U with d(x) < dist(B_δ(0), ∂U). Let γ : ℝ → [0,1] be increasing, C¹, γ(t) = 0 for t ≤ σ/2, γ(t) = 1 for t ≥ σ, and (2) φ = γ∘d. Then (3) δ|Dφ(x)| ≤ −x·Dφ(x). By definition of |Dw|, (4) ∫|D(φu)| ≤ ∫|Dφ||u| + ∫ φ|Du|, and by (3) (5) δ∫|Dφ||u| ≤ −∫ x·Dφ |u| = ∫ |u| div(xφ) … ≤ ∫_U |D|u|| + n∫|u| ≤ ∫_U |Du| + n∫|u| (because |D|u|| ≤ |Du| by 2.5 and lower semicontinuity). Finally ∫_{ℝⁿ}|Du| ≤ liminf ∫|D(φu)| since φu → u in L¹, and 2.8 follows from (4), (5).

PART II. COMPLETE PROOF OF BVCompactness ∧ BVPoincare ∧ BVExtensionEstimate.

Section T (common tools).
T1 (mollifiers). Fix φ ∈ C_c^∞(ℝⁿ), φ ≥ 0, spt φ ⊆ B(0,1), ∫φ = 1, φ(−x) = φ(x); φ_σ(x) := σ^{−n}φ(x/σ). For F ∈ L¹(ℝⁿ), F_σ := φ_σ * F is C^∞ (Mathlib HasCompactSupport.contDiff_convolution_left), ∂_i F_σ = (∂_iφ_σ) * F, sup|F_σ| ≤ sup|φ_σ|·‖F‖₁ and Lip(F_σ) ≤ sup|Dφ_σ|·‖F‖₁.
T2 (L¹ convergence). For F ∈ L¹(ℝⁿ), ‖F_σ − F‖₁ → 0 as σ → 0. Proof: given ε choose F₀ continuous with compact support and ‖F − F₀‖₁ < ε (density of C_c in L¹); ‖φ_σ*(F − F₀)‖₁ ≤ ‖F − F₀‖₁ (Young/Tonelli, ∫φ_σ = 1); φ_σ*F₀ → F₀ uniformly (uniform continuity) with supports in a fixed compact set, hence in L¹. So limsup ‖F_σ − F‖₁ ≤ 2ε.
T3 (integration by parts for Lipschitz functions). If F : ℝⁿ → ℝ is Lipschitz and g : ℝⁿ → ℝⁿ is Lipschitz with compact support then ∫ F div g = −∫ ∇F·g (a.e. derivatives). This is the Fubini/absolute-continuity-on-lines argument of the printed proof of Rademacher; formally Mathlib LipschitzWith.integral_lineDeriv_mul_eq applied to f := F, the coordinate functions g_i = ⟨e_i, g⟩ and v := e_i, together with lineDeriv_neg and the a.e. identities lineDeriv = fderiv at differentiability points (Rademacher) and div g = Σ_i⟨e_i, Dg e_i⟩ (SimonGMT euclideanDivergence_eq_sum_inner). (If F is only Lipschitz on a neighbourhood N of tsupport g, apply this to χF with χ ∈ C_c^∞(N) equal to 1 near tsupport g.)
T4 (variation of a mollification). Let W be open, u ∈ L¹(W), F := u·1_W, σ > 0 and g a C^∞ (or C¹) compactly supported field with tsupport g ⊆ W^(σ) and sup|g| ≤ 1. Then ∫ F_σ div g = ∫ F (φ_σ * div g) = ∫_W u div(φ_σ * g) ≤ |Du|(W). Indeed Fubini and φ_σ(−x) = φ_σ(x) give the first equality; φ_σ * div g = div(φ_σ * g); and φ_σ * g is C^∞ with tsupport ⊆ tsupport g + B̄(0,σ) ⊆ W and sup|φ_σ * g| ≤ 1, hence admissible for W.
T5 (smooth duality). For w ∈ C^∞(ℝⁿ) and O open, ∫_O |∇w| ≤ sup{∫ w div g : g ∈ C_c^∞(O; ℝⁿ), |g| ≤ 1}. Proof: take compact K_l ↑ O, χ_l ∈ C_c^∞(O) with 0 ≤ χ_l ≤ 1, χ_l = 1 on K_l, and g := −χ_l ∇w/√(|∇w|² + η²) (C^∞, |g| ≤ 1). Then ∫ w div g = −∫ ∇w·g (smooth integration by parts) = ∫ χ_l |∇w|²/√(|∇w|²+η²) ≥ ∫_{K_l} (|∇w| − η) (as t²/√(t²+η²) ≥ t − η for t ≥ 0); let η → 0 and l → ∞ (monotone convergence).
T6 (gradient bound). Combining T4 and T5 (with O = W^(σ)): for u ∈ L¹(W), ∫_{W^(σ)} |∇(φ_σ*(u1_W))| ≤ |Du|(W).
T7 (translation and mollification estimate). Let W open, u ∈ L¹(W), Q compact, σ > 0 with Q + B̄(0,3σ) ⊆ W, and u_σ := φ_σ * (u1_W). Then for |z| ≤ σ: ∫_Q |u(x − z) − u(x)| dx ≤ |z| |Du|(W), and ∫_Q |u_σ − u| ≤ σ|Du|(W). Proof: for 0 < τ < σ let w := φ_τ * (u1_W) (smooth). For x ∈ Q, |w(x−z) − w(x)| ≤ |z|∫_0^1 |∇w(x − tz)| dt; integrating over Q and using Tonelli and translation invariance, ∫_Q |w(x−z) − w(x)| dx ≤ |z| ∫_{Q+B̄(0,σ)} |∇w| ≤ |z| ∫_{W^(τ)} |∇w| ≤ |z||Du|(W) (Q + B̄(0,σ) ⊆ W^(τ) because points of Q + B̄(0,σ) have distance > 2σ > τ from ℝⁿ∖W; then T6). As τ → 0, w → u1_W in L¹(ℝⁿ) (T2), and x, x − z ∈ W for x ∈ Q, so the left side converges to ∫_Q |u(x−z) − u(x)| dx. Finally, for x ∈ Q, u_σ(x) − u(x) = ∫ φ_σ(z)(u(x−z) − u(x)) dz, so by Tonelli ∫_Q |u_σ − u| ≤ ∫ φ_σ(z) ∫_Q |u(x−z) − u(x)| dx dz ≤ σ|Du|(W).
T8 (|D|u|| ≤ |Du|). For O open and u ∈ L¹_loc(O): |D|u||(O) ≤ |Du|(O). Proof: let g be admissible for O, and choose open sets W ⊂⊂ W′ ⊂⊂ O with tsupport g ⊆ W, and σ_j ↓ 0 with W ⊆ W′^(σ_j). Let w_j := φ_{σ_j} * (u1_{W′}) and ψ_η(t) := √(t² + η²) − η (smooth, |ψ_η′| ≤ 1, |ψ_η(t) − |t|| ≤ η). The function ψ_η∘w_j is globally Lipschitz (Lip ≤ Lip w_j ≤ sup|Dφ_{σ_j}|·‖u1_{W′}‖₁ by T1), so by T3 and T6, ∫ ψ_{η}(w_j) div g = −∫ ψ_η′(w_j)∇w_j·g ≤ ∫_W |∇w_j| ≤ |Du|(W′) ≤ |Du|(O). Taking η = η_j → 0, ψ_{η_j}(w_j) → |u| in L¹(W) (T2 and the two bounds on ψ_η), and div g is bounded, so ∫_O |u| div g = ∫_W |u| div g ≤ |Du|(O). Taking the supremum over g gives the claim.

Section A (Theorem 2.6, BVCompactness). Hypotheses (exact frozen form): every u_k satisfies IsLocallyBV U (so U is open, by the case k = 0, and u_k ∈ L¹_loc(U)), and for every open W ⊂⊂ U: S_W := sup_k ∫⁻_W (‖u_k(x)‖ₑ + |Du_k|(W)) dLⁿ(x) < ∞, where |Du_k|(W) := bvVariationOn (u k) W ∈ [0,∞] does not depend on x (it is a constant inside the integrand).
A0. Unweighted uniform bound. Claim: for every open W ⊂⊂ U the quantity C_W := sup_k (∫⁻_W ‖u_k‖ₑ + |Du_k|(W)) ∈ [0,∞] is finite.
(a) W = ∅. The integral over ∅ is 0 (the restricted measure is the zero measure), and |Du_k|(∅) = 0: every term of the supremum defining bvVariationOn (u k) ∅ is ofReal(∫_∅ u_k div g) = ofReal 0 = 0, and a supremum of zeros (also an empty one) is 0 in [0,∞]. Hence both terms vanish for every k and C_∅ = 0.
(b) W ≠ ∅. Then 0 < Lⁿ(W) < ∞: W is a nonempty open set and Lebesgue measure on ℝⁿ is an additive Haar measure, hence positive on nonempty open sets (Mathlib IsOpen.measure_pos; this also holds for n = 0, where ℝ⁰ is a point of measure 1); and Lⁿ(W) ≤ Lⁿ(closure W) < ∞ because closure W is compact (Mathlib IsCompact.measure_lt_top). Fix k. Since x ↦ |Du_k|(W) is constant, hence measurable, the integral splits (Mathlib lintegral_add_right with measurable_const, then setLIntegral_const): ∫⁻_W (‖u_k(x)‖ₑ + |Du_k|(W)) dx = ∫⁻_W ‖u_k‖ₑ + |Du_k|(W)·Lⁿ(W). This is ≤ S_W, so ∫⁻_W ‖u_k‖ₑ ≤ S_W and |Du_k|(W)·Lⁿ(W) ≤ S_W; dividing by Lⁿ(W) ∈ (0,∞) gives |Du_k|(W) ≤ S_W/Lⁿ(W) (ENNReal.le_div_iff_mul_le, using Lⁿ(W) ≠ 0 and Lⁿ(W) ≠ ∞). Therefore ∫⁻_W ‖u_k‖ₑ + |Du_k|(W) ≤ S_W + S_W/Lⁿ(W) for every k, and C_W ≤ S_W + S_W/Lⁿ(W) < ∞ because S_W < ∞ and Lⁿ(W) ≠ 0 (ENNReal.div_lt_top).
(c) Consequences used below. For every open W ⊂⊂ U put c_W := C_W.toReal ∈ [0,∞) (finite by (a), (b)). Then for every k: u_k is integrable on W (u_k ∈ L¹_loc(U) and closure W is a compact subset of U) with ∫_W |u_k| ≤ c_W; |Du_k|(W) ≤ C_W < ∞, so |Du_k|(W).toReal ≤ c_W. In words: sup_k (∫_W |u_k| + |Du_k|(W)) ≤ c_W < ∞, the printed hypothesis of 2.6.
A1. Total boundedness on compacts. Fix compact Q ⊆ U (if Q = ∅ there is nothing to prove). Choose δ > 0 with Q + B̄(0,2δ) ⊆ U (Q compact, U open), the open set W := {x : dist(x,Q) < δ} (so Q ⊆ W, and closure W ⊆ Q + B̄(0,δ) is compact and contained in U, i.e. W ⊂⊂ U) and σ₀ := δ/4 (so Q + B̄(0,3σ₀) ⊆ W). Let c_W ∈ [0,∞) be the finite constant of A0 for this W. Given ε > 0 choose σ ∈ (0, σ₀] with σc_W < ε/4. By T7 (applied to u_k ∈ L¹(W), with |Du_k|(W) ≤ c_W by A0(c)), ∫_Q |(u_k)_σ − u_k| ≤ σc_W < ε/4 for all k, where (u_k)_σ := φ_σ*(u_k1_W). By T1 and ‖u_k1_W‖₁ = ∫_W |u_k| ≤ c_W (A0(c)), the restrictions (u_k)_σ|_Q are bounded by B := sup|φ_σ|·c_W and Λ-Lipschitz with Λ := sup|Dφ_σ|·c_W. Elementary Arzelà-Ascoli: with η := ε/(4(Lⁿ(Q) + 1)), pick a finite η/(3Λ+1)-net q_1,…,q_p of Q and the finite grid of multiples of η/3 in [−B,B]; two functions whose rounded values at all q_i coincide differ by at most η everywhere on Q; so finitely many indices k_1,…,k_r exist such that every (u_k)_σ is within η in sup norm, hence within ε/4 in L¹(Q), of some (u_{k_s})_σ. Consequently every u_k is within ε/4 + ε/4 + ε/4 < ε in L¹(Q) of some u_{k_s}: {u_k|_Q} is totally bounded in L¹(Q).
A2. Diagonal extraction. Let Q_1 ⊆ Q_2 ⊆ … be compact with Q_j ⊆ interior Q_{j+1} and ∪Q_j = U. By A1 and the pigeonhole principle, from any subsequence one can extract a further subsequence that is Cauchy in L¹(Q_j); doing this successively for j = 1, 2, … and taking the diagonal gives a strictly increasing ψ : ℕ → ℕ such that (u_{ψ(k)}) is Cauchy in L¹(Q_j) for every j. By completeness of L¹(Q_j) let v_j be its limit; v_{j+1} = v_j a.e. on Q_j. Define v := v_j on Q_j∖Q_{j−1} (measurable representatives) and v := 0 off U. Then ∫_{Q_j} |u_{ψ(k)} − v| → 0 for every j. Every compact K ⊆ U is contained in some Q_j (it is covered by the increasing open sets interior Q_{j+1}), so TendstoLocallyInL1On (u∘ψ) v U holds; and v ∈ L¹_loc(U) since ∫_K |v| ≤ ∫_K |v − u_{ψ(k)}| + ∫_K |u_{ψ(k)}| < ∞.
A3. Lower semicontinuity: for open W ⊂⊂ U, |Dv|(W) ≤ liminf_k |Du_{ψ(k)}|(W). This is SimonGMT Poincare.SimonGMT.Chapter02.bvVariationOn_le_liminf_of_locallyL1 (for each admissible g, ∫_W v div g = lim_k ∫_W u_{ψ(k)} div g because u_{ψ(k)} → v in L¹(closure W) and div g is bounded; and each term is ≤ |Du_{ψ(k)}|(W)).
A4. v is locally BV. Let W be open with W ⊂⊂ U and c_W ≥ 0 the constant of A0. Claim: for every k and every C¹ compactly supported field g (IsC1TestField g) with tsupport g ⊆ W, ∫_W u_k div g ≤ c_W·sup|g|, where sup|g| := compactlySupportedSupNorm g ≥ 0. Put s := sup|g|. If s = 0 then g ≡ 0, so div g ≡ 0 and ∫_W u_k div g = 0 = c_W·s. If s > 0 then h := s⁻¹g is a Lipschitz test field (a compactly supported C¹ field is Lipschitz, SimonGMT IsC1TestField.isLipschitzTestField, and scaling preserves this) with tsupport h = tsupport g ⊆ W and sup|h| = 1 ≤ 1; since g is differentiable, fderiv h = s⁻¹ fderiv g, so div h = s⁻¹ div g and ∫_W u_k div h = s⁻¹∫_W u_k div g. By SimonGMT ofReal_integral_le_bvVariationOn, ofReal(s⁻¹∫_W u_k div g) ≤ |Du_k|(W) < ∞, hence s⁻¹∫_W u_k div g ≤ |Du_k|(W).toReal ≤ c_W (A0(c)), i.e. ∫_W u_k div g ≤ c_W·s. Thus the hypothesis hbound of SimonGMT isLocallyBV_of_locallyL1_of_uniform_bound holds with the constant c := c_W ≥ 0 for all indices (in particular eventually along atTop for the subsequence u_{ψ(k)}); together with U open, v ∈ L¹_loc(U), u_{ψ(k)} ∈ L¹_loc(U) and TendstoLocallyInL1On (fun k ↦ u (ψ k)) v U atTop from A2, that lemma gives IsLocallyBV U v. (Mathematically: ∫_W v div g = lim_k ∫_W u_{ψ(k)} div g ≤ c_W sup|g|, because u_{ψ(k)} → v in L¹(closure W) and div g is bounded.)
A5. A2-A4 give ψ, v with StrictMono ψ, IsLocallyBV U v, TendstoLocallyInL1On (fun k ↦ u (ψ k)) v U atTop and the liminf inequality for all open W ⊂⊂ U: BVCompactness. (If U = ∅ everything is trivial.)

Section B (Lemma 2.7, BVPoincare). Given n and θ, δ ∈ (0,1) put C := 2^{n+1}(1 + θ⁻¹) (it does not even depend on δ). Let U, R, ξ, u, β be as in the statement; in particular u ∈ L¹(U), |Du|(U) < ∞, ξ ∈ U, B̄(ξ,δR) ⊆ U ⊆ B̄(ξ,R), so 0 < Lⁿ(U) < ∞ and diam U ≤ 2R. (n = 0: U is the single point of ℝ⁰ and the hypothesis on β forces u = β there, so both sides vanish; the general argument below also covers it.)
B1. Smooth Poincaré on convex sets. If O is open, convex, bounded with Lⁿ(O) > 0 and w ∈ C¹(ℝⁿ), then ∫_O∫_O |w(x) − w(y)| dx dy ≤ 2ⁿ diam(O) Lⁿ(O) ∫_O |∇w|, hence ∫_O |w − w̄_O| ≤ 2ⁿ diam(O) ∫_O |∇w| where w̄_O is the mean of w on O. Proof: |w(x) − w(y)| ≤ |y − x| ∫_0^1 |∇w(x + t(y − x))| dt (the segment lies in O). For t ∈ [½,1] and fixed x substitute z = (1−t)x + ty: dy = t^{−n} dz ≤ 2ⁿ dz and z ∈ O; for t ∈ [0,½] and fixed y substitute z = (1−t)x + ty: dx = (1−t)^{−n} dz ≤ 2ⁿ dz. Each half contributes at most ½·diam(O)·Lⁿ(O)·2ⁿ∫_O|∇w|. Then ∫_O |w(x) − w̄_O| dx ≤ Lⁿ(O)⁻¹ ∫_O∫_O |w(x) − w(y)| dy dx.
From here on in Section B assume n ≥ 1 (so U, being bounded, is not all of ℝⁿ and d below is finite and positive exactly on U).
B2. Inner parallel sets. d(x) := dist(x, ℝⁿ∖U) is concave on U (if B(x,a) ⊆ U and B(y,b) ⊆ U then B((1−t)x+ty, (1−t)a+tb) ⊆ U by convexity), so U_σ := U^(σ) = {d > σ} is open, convex, bounded, U_σ ↑ U as σ ↓ 0, and ξ ∈ U_σ, Lⁿ(U_σ) > 0 for small σ.
B3. Approximation. Let w_σ := φ_σ*(u1_U) (C^∞). By T6, ∫_{U_σ} |∇w_σ| ≤ |Du|(U). By B1, ∫_{U_σ} |w_σ − c_σ| ≤ 2ⁿ·2R·|Du|(U), c_σ := mean of w_σ on U_σ.
B4. Limit σ → 0. By T2, ‖w_σ − u1_U‖_{L¹(ℝⁿ)} → 0; Lⁿ(U∖U_σ) → 0 and ∫_{U∖U_σ}|u| → 0. Hence ∫_{U_σ} w_σ → ∫_U u and Lⁿ(U_σ) → Lⁿ(U), so c_σ → ū := mean of u on U; and |∫_{U_σ}|w_σ − c_σ| − ∫_U |u − ū|| ≤ ‖w_σ − u1_U‖₁ + |c_σ − ū|Lⁿ(U) + ∫_{U∖U_σ}|u − ū| → 0. Therefore ∫_U |u − ū| ≤ 2^{n+1}R |Du|(U).
B5. From the mean to β. (The sets {x ∈ U : u ≥ β} and {x ∈ U : u ≤ β} are null-measurable since u is a.e.-measurable on the measurable set U, so their measures can be used in lower bounds for integrals, e.g. Mathlib mul_meas_ge_le_lintegral₀.) If β ≥ ū then |u − ū| ≥ β − ū on {x ∈ U : u ≥ β}, a set of measure ≥ θLⁿ(U); if β < ū then |u − ū| ≥ ū − β on {x ∈ U : u ≤ β}, also of measure ≥ θLⁿ(U). In both cases θLⁿ(U)|β − ū| ≤ ∫_U |u − ū|. Hence ∫_U |u − β| ≤ ∫_U |u − ū| + Lⁿ(U)|ū − β| ≤ (1 + θ⁻¹)∫_U|u − ū| ≤ C R |Du|(U). In the frozen form: ∫⁻ x in U, ‖u x − β‖ₑ ≤ ofReal(C·R)·bvVariationOn u U (both sides finite; C ≥ 0).

Section C (Lemma 2.8, BVExtensionEstimate). Given n and δ ∈ (0,1) put C := max(1 + δ⁻¹, nδ⁻¹) ≥ 0. Let U, R, ξ be as in the statement, u ∈ L¹(ℝⁿ) with |Du|(ℝⁿ) < ∞ (IsBVOn univ u) and u = 0 a.e. on ℝⁿ∖Ū. (n = 0: ℝ⁰ = U = Ū, (Ū)ᶜ = ∅ and both claims are trivial since C ≥ 1; assume n ≥ 1, so U ≠ ℝⁿ as U is bounded.)
C0. |Du|(ℝⁿ∖Ū) = 0: for g admissible for the open set ℝⁿ∖Ū, ∫_{ℝⁿ∖Ū} u div g = 0 because u = 0 a.e. there; so every term of the supremum is ofReal 0 = 0.
C1. d(x) := dist(x, ℝⁿ∖U) is 1-Lipschitz, zero off U, concave on U (B2), and |∇d(x)| = 1 at every x ∈ U where d is differentiable: |∇d| ≤ 1 by the Lipschitz bound, and if a ∉ U is a nearest point to x and e := (a − x)/|a − x| then d(x + se) ≤ d(x) − s for 0 ≤ s ≤ d(x), so ∇d(x)·e ≤ −1.
C2. Let η₀ := dist(B̄(ξ,δR), ℝⁿ∖U) > 0 (compact subset of the open U). For x ∈ U with d differentiable at x and d(x) < η₀: −(x − ξ)·∇d(x) ≥ δR. Proof: w := ξ − δR∇d(x) ∈ B̄(ξ,δR) ⊆ U, so d(w) ≥ η₀ > d(x); concavity on the segment [x,w] ⊆ U gives the supergradient inequality d(w) ≤ d(x) + ∇d(x)·(w − x); hence ∇d(x)·(ξ − x) − δR|∇d(x)|² > 0 with |∇d(x)| = 1.
C3. Cut-offs. The level sets {d = c}, c > 0, are disjoint subsets of U (finite measure), so only countably many have positive measure; choose ε_j ↓ 0 with ε_j < η₀ and Lⁿ({d = ε_j}) = Lⁿ({d = ε_j/2}) = 0. Let γ_ε(t) := min{1, max{0, 2t/ε − 1}} and φ_ε := γ_ε∘d: Lipschitz, 0 ≤ φ_ε ≤ 1, φ_ε = 0 on {d ≤ ε/2}, so tsupport φ_ε ⊆ {d ≥ ε/2}, a compact subset of U (closed and bounded); φ_ε = 1 on {d ≥ ε}; φ_ε → 1_U pointwise as ε → 0. For a.e. x: ∇φ_ε(x) = (2/ε)∇d(x) if ε/2 < d(x) < ε and ∇φ_ε(x) = 0 if d(x) < ε/2 or d(x) > ε (open sets on which φ_ε is an affine function of d, resp. constant), the two level sets being null for ε = ε_j. By C2, for a.e. x: δR|∇φ_ε(x)| ≤ −(x − ξ)·∇φ_ε(x).
C4. Key bound: ∫ |u||∇φ_ε| ≤ δ⁻¹|Du|(U) + nδ⁻¹R⁻¹∫_U |u|. Let V(x) := (x − ξ)φ_ε(x)/R: Lipschitz, tsupport V ⊆ tsupport φ_ε ⊆ U compact, |V| ≤ 1 (|x − ξ| ≤ R on U), and div V = (nφ_ε + (x − ξ)·∇φ_ε)/R a.e. Then ∫|u||∇φ_ε| ≤ (δR)⁻¹ ∫ |u|(−(x − ξ)·∇φ_ε) = (δR)⁻¹ (n∫|u|φ_ε − R∫_U |u| div V) ≤ (δR)⁻¹(n∫_U|u| + R|D|u||(U)), and |D|u||(U) ≤ |Du|(U) by T8.
C5. Bound on |Du|(ℝⁿ). Let g be admissible for ℝⁿ. Since u ∈ L¹(ℝⁿ) and div g is bounded, dominated convergence gives ∫ u div g = lim_j ∫ φ_{ε_j} u div g, because φ_ε → 1_U pointwise and u1_U = u a.e. (u = 0 a.e. off Ū, and Ū∖U = frontier U is Lⁿ-null for convex U, Mathlib Convex.addHaar_frontier). At points where φ_ε and g are differentiable (a.e.), div(φ_ε g) = φ_ε div g + ∇φ_ε·g, so ∫ φ_ε u div g = ∫_U u div(φ_ε g) − ∫ u g·∇φ_ε ≤ |Du|(U) + ∫|u||∇φ_ε| (φ_ε g is admissible for U: Lipschitz, tsupport ⊆ U compact, |φ_εg| ≤ 1) ≤ (1 + δ⁻¹)|Du|(U) + nδ⁻¹R⁻¹∫_U|u| (C4) ≤ C(|Du|(U) + R⁻¹∫_U|u|). Hence ofReal(∫ u div g) ≤ ofReal C·(|Du|(U) + ofReal R⁻¹·∫⁻_U ‖u‖ₑ), and taking the supremum over g gives the second conjunct; C0 is the first. This proves BVExtensionEstimate.

Conclusion. Sections A, B, C prove the three conjuncts BVCompactness, BVPoincare, BVExtensionEstimate.

## Key steps

1. Mollification tools: smoothness, L¹ convergence, integration by parts for Lipschitz functions, variation of a mollification bounded by |Du|(W) on inner parallel sets, smooth duality ∫|∇w| ≤ sup ∫ w div g.
2. Translation estimate ∫_Q|u_σ − u| ≤ σ|Du|(W) and |D|u||(O) ≤ |Du|(O).
3. 2.6, step A0: the frozen hypothesis sup_k ∫_W (|u_k| + |Du_k|(W)) dLⁿ < ∞ (variation inside the integrand) splits as ∫_W|u_k| + Lⁿ(W)·|Du_k|(W); for nonempty open W ⊂⊂ U, 0 < Lⁿ(W) < ∞, so dividing gives the finite unweighted constant c_W ≥ sup_k(∫_W|u_k| + |Du_k|(W)); for W = ∅ both terms vanish.
4. 2.6: total boundedness in L¹(Q) via mollification plus elementary Arzelà-Ascoli with the A0 constant c_W, diagonal Cauchy subsequence, limit v in L¹_loc, lower semicontinuity (SimonGMT bvVariationOn_le_liminf_of_locallyL1) and the local BV bound ∫_W u_k div g ≤ c_W sup|g| via SimonGMT isLocallyBV_of_locallyL1_of_uniform_bound.
5. 2.7: L¹ Poincaré inequality on convex sets with constant 2ⁿ diam for smooth functions, applied to mollifications on convex inner parallel sets, limit σ → 0, then mean-to-β step; C = 2^{n+1}(1 + 1/θ).
6. 2.8: concavity of the distance to the boundary gives −(x−ξ)·∇d ≥ δR near ∂U; Lipschitz cut-offs φ_ε = γ_ε∘d; bound ∫|u||∇φ_ε| via the field (x−ξ)φ_ε/R and |D|u|| ≤ |Du|; pass to the limit on each test field; C = max(1+1/δ, n/δ).

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

Solution PR: https://github.com/ZhengyangZhang06/gmt-formalize/pull/2859

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
