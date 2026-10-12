<!-- theorem-id: gmt-ch02/root.bv_results-a1.extension-a1 -->

## Theorem `Submission.bv_extension_estimate_theorem`

(Simon Ch. 2, Lemma 2.8, frozen contract BVExtensionEstimate.) For all n ∈ ℕ and δ ∈ (0,1) there is C ≥ 0 such that for every bounded open convex U ⊆ ℝⁿ, R > 0, ξ ∈ U with closedBall(ξ,δR) ⊆ U ⊆ closedBall(ξ,R), and every u with IsBVOn univ u (u ∈ L¹(ℝⁿ), bvVariationOn u univ < ∞) and u = 0 a.e. off closure U: bvVariationOn u (closure U)ᶜ = 0 and bvVariationOn u univ ≤ ofReal C·(bvVariationOn u U + ofReal R⁻¹·∫⁻_U ‖u‖ₑ).

Node: `root.bv_results-a1.extension-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/3

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/38

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/166

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/508, https://github.com/ZhengyangZhang06/gmt-formalize/issues/509, https://github.com/ZhengyangZhang06/gmt-formalize/issues/510, https://github.com/ZhengyangZhang06/gmt-formalize/issues/513, https://github.com/ZhengyangZhang06/gmt-formalize/issues/515, https://github.com/ZhengyangZhang06/gmt-formalize/issues/516, https://github.com/ZhengyangZhang06/gmt-formalize/issues/517, https://github.com/ZhengyangZhang06/gmt-formalize/issues/520, https://github.com/ZhengyangZhang06/gmt-formalize/issues/523

## Lean problem

Declaration: `Submission.bv_extension_estimate_theorem`

```lean
BVExtensionEstimate
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

- Parent DAG node: `root.bv_results-a1`
- Child DAG node: `root.bv_results-a1.extension-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Introduction to GMT, Ch. 2, Lemma 2.8 (pp. 51–53). Printed proof (cleaned transcription, as in the parent): “Assume R = 1, ξ = 0. Let d(x) = dist(x, ∂U). Since U is convex, U_σ = {x : dist(x,∂U) > σ} is convex for each σ ≥ 0 […] and 0 < d(x) < d(y) ⇒ (y − x)·Dd(x) ≥ 0 for all x ∈ U at which d is differentiable. Since B_δ(0) ⊆ U and |Dd(x)| = 1 at points of differentiability in U, taking y = −δDd(x) gives (1) x·Dd(x) ≤ −δ for a.e. x ∈ U with d(x) < dist(B_δ(0), ∂U). Let γ : ℝ → [0,1] be increasing, C¹, γ(t) = 0 for t ≤ σ/2, γ(t) = 1 for t ≥ σ, and (2) φ = γ∘d. Then (3) δ|Dφ(x)| ≤ −x·Dφ(x). By definition of |Dw|, (4) ∫|D(φu)| ≤ ∫|Dφ||u| + ∫ φ|Du|, and by (3) (5) δ∫|Dφ||u| ≤ −∫ x·Dφ |u| = ∫ |u| div(xφ) … ≤ ∫_U |D|u|| + n∫|u| ≤ ∫_U |Du| + n∫|u| (because |D|u|| ≤ |Du| by 2.5 and lower semicontinuity). Finally ∫_{ℝⁿ}|Du| ≤ liminf ∫|D(φu)| since φu → u in L¹, and 2.8 follows from (4), (5).”
Readings (GMT/Ch02/README.md): spt u ⊂ Ū means u = 0 a.e. off Ū, and ∫_{ℝⁿ}|Du| = ∫_Ū|Du| is encoded as |Du|(ℝⁿ∖Ū) = 0. As in the parent, the printed cut-off argument is kept, but the final limit is taken directly on test fields (no product lower semicontinuity). The cut-offs are Lipschitz, built from a piecewise-linear γ and level sets of d chosen to be null. The complete argument below is Section C of the parent proof. The inequality |D|u||(U) ≤ |Du|(U) is the sibling theorem Submission.bv_abs_variation_le.

Notation. E := ℝⁿ = EuclideanSpace ℝ (Fin n), μ := volume. |Dv|(A) := Chapter02.bvVariationOn v A. div g := Chapter02.euclideanDivergence g = trace Dg, with Dg := fderiv ℝ g (0 at points of non-differentiability). A field g ∈ C_c(E,E) is admissible for an open set A if it is Lipschitz (IsLipschitzTestField), tsupport g ⊆ A and compactlySupportedSupNorm g ≤ 1; then ‖g(x)‖ ≤ 1 for all x (le_csSup on the bounded range). By SimonGMT ofReal_integral_le_bvVariationOn, ofReal(∫_A v div g) ≤ |Dv|(A) for every admissible g. Recall also: div g is Borel (measurable_euclideanDivergence), |div g| ≤ nΛ for a Λ-Lipschitz g (norm_euclideanDivergence_le_of_lipschitz), div g = 0 off tsupport g (support_euclideanDivergence_subset), and Lipschitz maps on E are differentiable a.e. (Rademacher, LipschitzWith.ae_differentiableAt).

Choice of constant. Given n and δ ∈ (0,1), put C := max(1 + δ⁻¹, nδ⁻¹) ≥ 1 > 0. Let U, R, ξ, u satisfy the hypotheses: u ∈ L¹(E), |Du|(E) < ∞, and u = 0 a.e. on E ∖ closure U.

C0. |Du|(E ∖ closure U) = 0. The set A := (closure U)ᶜ is open and measurable. For g admissible for A: since u = 0 μ-a.e. on A (ae_restrict_iff' applied to the hypothesis), the integrand u·div g vanishes (volume.restrict A)-a.e., so ∫_A u div g = 0 and the term is ofReal 0 = 0. A supremum of zeros is 0. This proves the first conjunct (for every n).

Case n = 0. E is a single point, so U = E (it contains ξ) and |Du|(E) = |Du|(U). Since C ≥ 1, |Du|(E) ≤ ofReal C·|Du|(U) ≤ ofReal C·(|Du|(U) + ofReal R⁻¹·∫⁻_U ‖u‖ₑ). From now on n ≥ 1, so U ≠ E (U is bounded) and Uᶜ ≠ ∅.
Reduction. If |Du|(U) = ∞, the right side of the second conjunct is ∞, because ofReal C ≠ 0. Assume M_U := (|Du|(U)).toReal with |Du|(U) = ofReal M_U < ∞, and put A_U := ∫_U |u| < ∞ (so ofReal A_U = ∫⁻_U ‖u‖ₑ).

C1. The distance function. d(x) := infDist(x, Uᶜ).
 (a) d is 1-Lipschitz, d = 0 off U, and d > 0 on U (U open).
 (b) d is concave on U. Let x, y ∈ U, t ∈ (0,1), z := (1 − t)x + ty and s := (1 − t)d(x) + t d(y) > 0. Recall ball(x, d(x)) ⊆ U and ball(y, d(y)) ⊆ U. For ‖a‖ < s put a_x := a·d(x)/s and a_y := a·d(y)/s. Then (1 − t)a_x + t a_y = a, ‖a_x‖ < d(x) and ‖a_y‖ < d(y), so z + a = (1 − t)(x + a_x) + t(y + a_y) ∈ U by convexity. Hence ball(z,s) ⊆ U and d(z) ≥ s.
 (c) If x ∈ U and d is differentiable at x, then ‖Dd(x)‖ = 1. Indeed ‖Dd(x)‖ ≤ 1 since d is 1-Lipschitz. Conversely, Uᶜ is closed and nonempty and E is proper, so there is a ∈ Uᶜ with ‖x − a‖ = d(x) > 0 (IsClosed.exists_infDist_eq_dist). With e := (a − x)/‖a − x‖ and 0 ≤ s ≤ d(x), we get d(x + se) ≤ ‖x + se − a‖ = d(x) − s. Hence Dd(x)[e] ≤ −1 and ‖Dd(x)‖ ≥ 1.

C2. Key geometric inequality. Let η₀ := min{d(y) : y ∈ closedBall(ξ,δR)} > 0; this is a continuous positive function on a nonempty compact subset of U. Claim: if x ∈ U, d is differentiable at x and d(x) < η₀, then −Dd(x)[x − ξ] > δR.
 Proof. Let ν ∈ E be the gradient of d at x, so Dd(x)[h] = ⟨ν,h⟩ and ‖ν‖ = 1 by C1(c). Put w := ξ − δRν. Then w ∈ closedBall(ξ,δR) ⊆ U, so d(w) ≥ η₀ > d(x).
 The segment [x,w] lies in U, and φ(t) := d(x + t(w − x)) is concave on [0,1] by C1(b), with φ'(0) = Dd(x)[w − x]. For a concave φ the slope (φ(t) − φ(0))/t is nonincreasing in t ∈ (0,1], so φ(1) − φ(0) ≤ φ'(0). Hence
   0 < d(w) − d(x) ≤ ⟨ν, w − x⟩ = ⟨ν, ξ − x⟩ − δR‖ν‖² = −Dd(x)[x − ξ] − δR.

C3. Cut-offs.
 (a) Null level sets. For c > 0 the level sets {d = c} are pairwise disjoint measurable subsets of U, and μ(U) < ∞. So the set B of c > 0 with μ({d = c}) > 0 is countable (Mathlib Measure.countable_meas_pos_of_disjoint_iUnion). Choose ε_j ∈ (0, min(η₀, 1/(j + 1))) with ε_j ∉ B and ε_j/2 ∉ B; this is possible since the excluded set B ∪ 2B is countable. So ε_j → 0, ε_j < η₀, and μ({d = ε_j}) = μ({d = ε_j/2}) = 0.
 (b) The cut-off. For ε > 0 let γ_ε(t) := min{1, max{0, 2t/ε − 1}}; it is (2/ε)-Lipschitz, takes values in [0,1], equals 0 for t ≤ ε/2 and 1 for t ≥ ε. Put φ_ε := γ_ε ∘ d. Then:
 - φ_ε is (2/ε)-Lipschitz and 0 ≤ φ_ε ≤ 1;
 - φ_ε = 0 on {d ≤ ε/2}, so tsupport φ_ε ⊆ {d ≥ ε/2}, a closed bounded subset of U, hence compact;
 - φ_ε = 1 on {d ≥ ε};
 - φ_ε(x) → 1_U(x) as ε → 0 for every x: for x ∈ U, φ_ε(x) = 1 as soon as ε ≤ d(x); for x ∉ U, d(x) = 0 so φ_ε(x) = 0.
 (c) The a.e. inequality. Fix ε = ε_j and consider the open sets A₁ := {d < ε/2}, A₂ := {ε/2 < d < ε} and A₃ := {d > ε}. They cover E up to the μ-null set {d = ε/2} ∪ {d = ε}.
 - On A₁ and on A₃, φ_ε is locally constant, so Dφ_ε = 0 there.
 - On A₂, φ_ε = (2/ε)d − 1, so at every x ∈ A₂ where d is differentiable (a.e. by Rademacher), Dφ_ε(x) = (2/ε)Dd(x) (derivatives of functions agreeing near x coincide). For such x we have x ∈ U and d(x) < ε < η₀, so C1(c) and C2 give δR‖Dφ_ε(x)‖ = (2/ε)δR ≤ (2/ε)(−Dd(x)[x − ξ]) = −Dφ_ε(x)[x − ξ].
 Hence for μ-a.e. x:
   δR‖Dφ_ε(x)‖ ≤ −Dφ_ε(x)[x − ξ].   (C3)

C4. Key bound: for ε = ε_j, ∫ |u|‖Dφ_ε‖ ≤ δ⁻¹M_U + nδ⁻¹R⁻¹A_U.
 (a) The field V(x) := φ_ε(x)(x − ξ)/R.
 - V is Lipschitz. If φ_ε(x) ≠ 0 then x ∈ U ⊆ closedBall(ξ,R), and V(x) − V(y) = φ_ε(y)(x − y)/R + (φ_ε(x) − φ_ε(y))(x − ξ)/R, so ‖V(x) − V(y)‖ ≤ (1/R + 2/ε)‖x − y‖. The case φ_ε(y) ≠ 0 is symmetric, and if both vanish then V(x) = V(y) = 0.
 - tsupport V ⊆ tsupport φ_ε ⊆ U is compact, and ‖V(x)‖ ≤ φ_ε(x)‖x − ξ‖/R ≤ 1.
 So −V (an element of C_c(E,E)) is admissible for U.
 (b) At every x where φ_ε is differentiable (a.e.), DV(x)[h] = (φ_ε(x)h + Dφ_ε(x)[h](x − ξ))/R, so div V(x) = (nφ_ε(x) + Dφ_ε(x)[x − ξ])/R. Hence a.e. −Dφ_ε(x)[x − ξ] = nφ_ε(x) − R div V(x).
 (c) By (C3), a.e. |u|‖Dφ_ε‖ ≤ (δR)⁻¹|u|(nφ_ε − R div V). All these functions are integrable: u ∈ L¹, and φ_ε, Dφ_ε, div V are bounded and measurable. So
   ∫ |u|‖Dφ_ε‖ ≤ (δR)⁻¹(n∫|u|φ_ε − R∫|u| div V).
 (d) First term: ∫|u|φ_ε ≤ ∫_U |u| = A_U, since 0 ≤ φ_ε ≤ 1_U.
 (e) Second term. div(−V) = −div V everywhere (fderiv(−V) = −fderiv V), and div V = 0 off tsupport V ⊆ U. So
   −∫|u| div V = ∫_U |u| div(−V) ≤ (|D|u||(U)).toReal,
 by ofReal_integral_le_bvVariationOn applied to the function |u| and the admissible field −V. By the sibling theorem Submission.bv_abs_variation_le (O := U open; u is integrable on E, hence locally integrable on U), |D|u||(U) ≤ |Du|(U) = ofReal M_U < ∞. So −∫|u| div V ≤ M_U.
 Therefore ∫|u|‖Dφ_ε‖ ≤ (δR)⁻¹(nA_U + R M_U) = δ⁻¹M_U + nδ⁻¹R⁻¹A_U.

C5. Bound on |Du|(E). Let g be admissible for E = univ, Λ-Lipschitz. By iSup_le it suffices to prove ∫_E u div g ≤ C(M_U + R⁻¹A_U); note ∫ x in univ, … = ∫ x, … (Measure.restrict_univ).
 (a) Dominated convergence. φ_{ε_j} u div g → 1_U u div g pointwise (C3(b)), with dominating function nΛ|u| ∈ L¹. Also 1_U u = u a.e.: u = 0 a.e. off closure U, and closure U ∖ U = frontier U is μ-null for convex U (Mathlib Convex.addHaar_frontier). Hence ∫ u div g = lim_j ∫ φ_{ε_j} u div g.
 (b) Fix j and ε = ε_j.
 - φ_ε g is Lipschitz, being the product of two bounded Lipschitz functions; tsupport(φ_ε g) ⊆ tsupport φ_ε ⊆ U is compact; ‖φ_ε g‖ ≤ 1. So φ_ε g is admissible for U.
 - At every x where both φ_ε and g are differentiable (a.e., Rademacher), D(φ_ε g)(x)[h] = φ_ε(x)Dg(x)[h] + Dφ_ε(x)[h]·g(x). Hence div(φ_ε g)(x) = φ_ε(x) div g(x) + Dφ_ε(x)[g(x)], since the trace of h ↦ Dφ_ε(x)[h]·g(x) is Dφ_ε(x)[g(x)].
 - All integrands are integrable (u ∈ L¹, the other factors bounded measurable). So
   ∫ φ_ε u div g = ∫ u div(φ_ε g) − ∫ u Dφ_ε[g] ≤ ∫_U u div(φ_ε g) + ∫|u|‖Dφ_ε‖,
 using ‖g‖ ≤ 1, and ∫ u div(φ_ε g) = ∫_U u div(φ_ε g) because div(φ_ε g) vanishes off U.
 - Admissibility gives ofReal(∫_U u div(φ_ε g)) ≤ |Du|(U) = ofReal M_U, so ∫_U u div(φ_ε g) ≤ M_U.
 - With C4: ∫ φ_ε u div g ≤ M_U + δ⁻¹M_U + nδ⁻¹R⁻¹A_U ≤ C(M_U + R⁻¹A_U).
 (c) Letting j → ∞ in (a) gives ∫_E u div g ≤ C(M_U + R⁻¹A_U). Since C, M_U, R⁻¹, A_U ≥ 0,
   ofReal(∫_E u div g) ≤ ofReal C·(ofReal M_U + ofReal R⁻¹·ofReal A_U) = ofReal C·(|Du|(U) + ofReal R⁻¹·∫⁻_U ‖u‖ₑ).
 Taking the supremum over g gives bvVariationOn u univ ≤ ofReal C·(bvVariationOn u U + ofReal R⁻¹·∫⁻ x in U, ‖u x‖ₑ). Together with C0 this proves BVExtensionEstimate with C = max(1 + δ⁻¹, nδ⁻¹). ∎

## Key steps

1. C = max(1 + 1/δ, n/δ); C0: |Du|((closure U)ᶜ) = 0 because u = 0 a.e. there; n = 0 trivial; assume |Du|(U) < ∞.
2. C1–C2: d = dist(·,Uᶜ) is concave on U with |∇d| = 1 where differentiable; the supergradient inequality at w = ξ − δR∇d(x) gives −(x − ξ)·∇d(x) > δR when d(x) < η₀.
3. C3: choose ε_j ↓ 0 with null level sets; Lipschitz cut-offs φ_ε = γ_ε∘d satisfy δR|∇φ_ε| ≤ −(x − ξ)·∇φ_ε a.e. and φ_ε → 1_U.
4. C4: with the admissible field −V, V = φ_ε(x − ξ)/R, and Submission.bv_abs_variation_le, get ∫|u||∇φ_ε| ≤ δ⁻¹|Du|(U) + nδ⁻¹R⁻¹∫_U|u|.
5. C5: for each test field g, the a.e. product rule div(φ_ε g) = φ_ε div g + ∇φ_ε·g, admissibility of φ_ε g for U, C4, and dominated convergence (frontier of convex U is null) give ∫u div g ≤ C(|Du|(U) + R⁻¹∫_U|u|).

## Reference use

### local-project

Queries:
- `rg -n 'theorem (normed_neg|integral_normed|nonneg_normed|support_normed_eq|tsupport_normed_eq|hasCompactSupport_normed|contDiff_normed|continuous_normed)' mathlib/Mathlib/Analysis/Calculus/BumpFunction/`
- `rg -n 'contDiff_convolution_left|contDiff_convolution_right|hasFDerivAt_convolution_right' mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `rg -n 'convolution_tendsto_right' mathlib/Mathlib; rg -n 'notation.*convolution' mathlib/Mathlib/Analysis/Convolution.lean`
- `rg -in 'eLpNorm.*convolution|convolution.*eLpNorm|lintegral.*convolution|young' mathlib/Mathlib; rg -iln 'mollif' mathlib/Mathlib`
- `rg -n 'exists_hasCompactSupport' mathlib/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`
- `rg -n 'theorem (integral_lineDeriv_mul_eq|ae_lineDeriv_sum_eq|ae_differentiableAt)' mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `rg -n 'def (infEdist|infEDist|infDist|cthickening|thickening)' mathlib/Mathlib/Topology/MetricSpace`
- `rg -n 'exists_cthickening_subset_open|exists_infDist_eq_dist|lineDeriv_eq_fderiv|addHaar_frontier|countable_meas_pos_of_disjoint|lintegral_lintegral_swap|integral_comp_comm|support_convolution_subset|lipschitzWith_of_hasCompactSupport|exists_contDiff_tsupport_subset|exists_contMDiffMap_one_nhds_of_subset_interior' mathlib/Mathlib`
- `grep -n 'theorem|def' simongmt/Poincare/SimonGMT/Chapter02/BV.lean, then a full read of BV.lean`
- `grep -n 'BV|2.6|2.7|2.8|open' project/GMT/Ch02/README.md; cmp project/GMT/Ch02/Contract.lean against the workspace GMT/Ch02/Contract.lean; rg -n 'Submission.|namespace Submission' project --glob '*.lean'`
- `lean Avail.lean: #check convolution, ContDiffBump, HasCompactSupport.contDiff_convolution_left, Metric.infDist, Metric.infEDist, lineDeriv, LipschitzWith.ae_differentiableAt, LipschitzWith.integral_lineDeriv_mul_eq, Convex.addHaar_frontier, gradient, Integrable.exists_hasCompactSupport_lintegral_sub_le after import GMT.Ch02.Submission`
- `python3 -I gen_checks.py (verifier gmt-compare.py contract_scope and child_modules plus lean_contract.validate_lean_statement), then lean on NodeChallenge_00..07.lean, AssemblyCheck.lean and Sanity.lean against a scratch olean of GMT.Ch02.Submission`
- `grep -rl for each of the 8 proposed lean_names in the run directory; list lean_name of every dag.json node and every nodes/*/decomposition-v1.json subproblem`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/LineDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Convex/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-bv-results-a1/parent-child-handoff.json`
- `/tmp/bvdecomp-tYsCkA/checks/NodeChallenge_00.lean`
- `/tmp/bvdecomp-tYsCkA/checks/NodeChallenge_07.lean`
- `/tmp/bvdecomp-tYsCkA/checks/AssemblyCheck.lean`
- `/tmp/bvdecomp-tYsCkA/checks/Sanity.lean`
- `/tmp/bvdecomp-tYsCkA/checks/Avail.lean`

The snapshot Contract.lean is byte-identical to the workspace contract and defines BVCompactness, BVPoincare and BVExtensionEstimate exactly as split. README rows 7–9 and the errata at lines 87 and 94–95 match the readings used: open W in 2.6; u ∈ L¹ in 2.7; and in 2.8, u = 0 a.e. off Ū with the conclusion encoded as |Du|(ℝⁿ∖Ū) = 0. The pinned SimonGMT BV.lean supplies the definitions and every lemma cited: euclideanDivergence_eq_sum_inner, measurable_euclideanDivergence, norm_euclideanDivergence_le_of_lipschitz, support_euclideanDivergence_subset, ofReal_integral_le_bvVariationOn, IsC1TestField.isLipschitzTestField, bvVariationOn_le_liminf_of_locallyL1, isLocallyBV_of_locallyL1_of_uniform_bound and isLocallyBV_zero. The snapshot Mathlib supplies the analytic tools: ContDiffBump.normed (contDiff_normed, nonneg_normed, support_normed_eq, integral_normed), HasCompactSupport.contDiff_convolution_left/right, hasFDerivAt_convolution_right, support_convolution_subset, LipschitzWith.integral_lineDeriv_mul_eq, LipschitzWith.ae_differentiableAt, DifferentiableAt.lineDeriv_eq_fderiv, Integrable.exists_hasCompactSupport_lintegral_sub_le, IsCompact.exists_cthickening_subset_open, IsClosed.exists_infDist_eq_dist, Convex.addHaar_frontier and Measure.countable_meas_pos_of_disjoint_iUnion. Mathlib has no lemma for L¹ convergence of mollifiers (no 'mollif' match and no convolution lemma with eLpNorm or lintegral), and no BV compactness, Poincaré or extension theorem, so those are genuine new obligations. In the frozen import closure, ContDiffBump.normed, gradient, Convex.addHaar_frontier and Integrable.exists_hasCompactSupport_lintegral_sub_le are unavailable (unknown field or constant). The child statements therefore use only convolution, kernel hypotheses that avoid ContDiffBump, fderiv, ball/closedBall and SimonGMT names; child proofs may add Mathlib imports to the Submission, which the verifier permits. With the comparator's own scope replay and statement validator, all 8 lean_statements elaborate and all 8 generated NodeChallenge modules compile. Sanity.lean confirms that normed ContDiffBumps satisfy the kernel hypotheses and that convolution ρ F (lsmul ℝ ℝ) volume x = ∫ t, ρ t * F (x - t). The assembly ⟨Submission.bv_compactness_theorem, Submission.bv_poincare_theorem, Submission.bv_extension_estimate_theorem⟩ type-checks against the selected type; apart from the sorry placeholders, it depends only on propext, Classical.choice and Quot.sound. The project snapshot has no Submission.* declarations, and neither dag.json nor any node file mentions the 8 proposed names, so none of them collides with a reserved declaration.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
