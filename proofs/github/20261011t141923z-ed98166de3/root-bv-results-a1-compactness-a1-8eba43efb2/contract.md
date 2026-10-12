<!-- theorem-id: gmt-ch02/root.bv_results-a1.compactness-a1 -->

## Theorem `Submission.bv_compactness_theorem`

(Simon Ch. 2, Theorem 2.6, frozen contract BVCompactness.) For every n, every U ⊆ ℝⁿ and every sequence u_k (k ∈ ℕ) with each u_k locally BV on U (SimonGMT IsLocallyBV U (u k)) such that for every open W ⊂⊂ U (IsRelativelyCompactIn W U: closure W compact and ⊆ U) the quantity sup_k ∫⁻_W (‖u_k(x)‖ₑ + bvVariationOn (u k) W) dx is finite (the x-independent constant |Du_k|(W) = bvVariationOn (u k) W sits inside the integrand), there are a strictly increasing ψ : ℕ → ℕ and v : ℝⁿ → ℝ such that v is locally BV on U, u_{ψ(k)} → v in L¹_loc(U) (TendstoLocallyInL1On), and bvVariationOn v W ≤ liminf_k bvVariationOn (u (ψ k)) W for every open W ⊂⊂ U.

Node: `root.bv_results-a1.compactness-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/3

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/38

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/165

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/461, https://github.com/ZhengyangZhang06/gmt-formalize/issues/462, https://github.com/ZhengyangZhang06/gmt-formalize/issues/463, https://github.com/ZhengyangZhang06/gmt-formalize/issues/465, https://github.com/ZhengyangZhang06/gmt-formalize/issues/467

## Lean problem

Declaration: `Submission.bv_compactness_theorem`

```lean
BVCompactness
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
- Child DAG node: `root.bv_results-a1.compactness-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Introduction to GMT, Ch. 2, Theorem 2.6 (p. 50). Printed proof (cleaned transcription, as in the parent): “By virtue of the previous lemma, in order to prove u_{k'} → u in L¹_loc(U) for some subsequence, it is enough to prove that the sets {u ∈ C¹(U) : ∫_W (|u| + |Du|) dLⁿ ≤ c(W)}, W ⊂⊂ U (for given constants c(W) < ∞), are precompact in L¹_loc(U). For the simple proof of this (involving mollification and Arzela's theorem) see [GT01, Thm 7.22]. Finally the fact that ∫_W|Du| ≤ liminf ∫_W |Du_{k'}| is a direct consequence of the definition of |Du|, |Du_{k'}|.”
Erratum/reading (GMT/Ch02/README.md): the sets W ⊂⊂ U are open; lower semicontinuity fails for non-open W, and 2.4 characterizes |Du|(W) only for open W.
Frozen hypothesis: ⨆ k, (∫⁻ x in W, ‖u k x‖ₑ + Chapter02.bvVariationOn (u k) W) < ⊤ for every open W ⊂⊂ U. The whole sum is the integrand; step A0 converts this into the printed unweighted bound.
The complete argument below is Section A of the parent proof. The mollification estimate T7 is supplied by the sibling theorem Submission.bv_mollifier_sub_lintegral_le.

Notation. E := ℝⁿ = EuclideanSpace ℝ (Fin n), μ := volume. |Dv|(W) := Chapter02.bvVariationOn v W. For a kernel κ, κ * G := convolution κ G (lsmul ℝ ℝ) volume, so (κ * G)(x) = ∫ κ(t)G(x − t) dt = ∫ κ(x − s)G(s) ds. W ⊂⊂ U means Chapter02.IsRelativelyCompactIn W U. Fix n, U and u satisfying the hypotheses. By IsLocallyBV U (u 0), U is open, and each u_k is locally integrable on U.

A0. Unweighted uniform bound. For every open W ⊂⊂ U, put S_W := ⨆_k ∫⁻_W (‖u_k(x)‖ₑ + |Du_k|(W)) dx < ∞. Claim: C_W := ⨆_k (∫⁻_W ‖u_k‖ₑ + |Du_k|(W)) is finite.
 (a) W = ∅. The integral over ∅ is 0, because volume.restrict ∅ = 0. Also |Du_k|(∅) = 0: every term of the supremum defining bvVariationOn (u k) ∅ is ofReal(∫_∅ …) = ofReal 0 = 0, and a supremum of zeros (or an empty one) is 0. Hence C_∅ = 0.
 (b) W ≠ ∅. Then 0 < μ(W) < ∞: W is nonempty and open and μ is an additive Haar measure (IsOpen.measure_pos; for n = 0 the space is a point of measure 1), and μ(W) ≤ μ(closure W) < ∞ because closure W is compact (IsCompact.measure_lt_top). Fix k. The function x ↦ |Du_k|(W) is constant, hence measurable, so by lintegral_add_right and setLIntegral_const
   ∫⁻_W (‖u_k(x)‖ₑ + |Du_k|(W)) dx = ∫⁻_W ‖u_k‖ₑ + |Du_k|(W)·μ(W) ≤ S_W.
 Hence ∫⁻_W ‖u_k‖ₑ ≤ S_W and |Du_k|(W)·μ(W) ≤ S_W, so |Du_k|(W) ≤ S_W/μ(W) (ENNReal.le_div_iff_mul_le, using μ(W) ≠ 0 and μ(W) ≠ ∞). Thus C_W ≤ S_W + S_W/μ(W) < ∞ (ENNReal.div_lt_top).
 (c) Consequences. Put c_W := C_W.toReal ≥ 0, so ofReal c_W = C_W. Then for every k: ∫⁻_W ‖u_k‖ₑ ≤ ofReal c_W, so u_k ∈ L¹(W) with ∫_W |u_k| ≤ c_W (u_k is locally integrable on U and closure W is a compact subset of U). Also |Du_k|(W) ≤ ofReal c_W < ∞, so (|Du_k|(W)).toReal ≤ c_W. This is the printed hypothesis sup_k (∫_W|u_k| + |Du_k|(W)) < ∞.

A1. Total boundedness on compact sets. Fix a compact Q ⊆ U; if Q = ∅ there is nothing to prove. Choose δ > 0 with cthickening(2δ, Q) ⊆ U (IsCompact.exists_cthickening_subset_open). Let W := thickening(δ, Q), an open set with Q ⊆ W. Its closure is contained in cthickening(δ, Q), which is compact and ⊆ U, so W ⊂⊂ U. Let c_W be the constant of A0 for this W.
 Fix ε > 0. Choose σ ∈ (0, δ) with σ·c_W < ε/4. Let ρ be a C^∞ kernel with ρ ≥ 0, support ρ ⊆ B(0,σ) and ∫ρ = 1; e.g. the normalized ContDiffBump at 0 with rIn = σ/2 and rOut = σ (Mathlib contDiff_normed, continuous_normed, nonneg_normed, support_normed_eq, integral_normed). For x ∈ Q, closedBall(x,σ) ⊆ thickening(δ,Q) = W because σ < δ. Put v_k := ρ * (1_W u_k).
 (i) Mollification error. Q is compact, hence measurable. By the sibling theorem Submission.bv_mollifier_sub_lintegral_le (with W, Q, u_k, ρ, σ; u_k ∈ L¹(W) by A0(c)),
   ∫⁻_Q ‖v_k − u_k‖ₑ ≤ ofReal(σ)·|Du_k|(W) ≤ ofReal(σ c_W) for every k.
 (ii) Uniform bounds (T1). ρ is C¹ with compact support, hence bounded by some A_ρ and Λ_ρ-Lipschitz. Writing v_k(x) = ∫ ρ(x − s)(1_W u_k)(s) ds, for all x, y and k:
   |v_k(x)| ≤ A_ρ ∫_W |u_k| ≤ B := A_ρ c_W,
   |v_k(x) − v_k(y)| ≤ ∫ |ρ(x − s) − ρ(y − s)||1_W u_k(s)| ds ≤ Λ ‖x − y‖ with Λ := Λ_ρ c_W.
 (iii) Elementary Arzelà–Ascoli. Let η := ε/(4(μ(Q).toReal + 1)). Since Q is compact, pick a finite set {q_1, …, q_p} ⊆ Q such that every x ∈ Q satisfies ‖x − q_i‖ < η/(3Λ + 3) for some i. Let Γ be the finite set (η/3)ℤ ∩ [−B − η, B + η]. For each k let a(k) ∈ Γ^p be obtained by rounding each value v_k(q_i) ∈ [−B, B] to a nearest point of Γ, so that |v_k(q_i) − a(k)_i| ≤ η/6 for all i (the grid spacing is η/3). Γ^p is finite, so the indices k fall into finitely many classes {k : a(k) = a}; pick one representative k_s in each nonempty class (s = 1, …, r).
 If a(k) = a(k'), then |v_k(q_i) − v_{k'}(q_i)| ≤ η/6 + η/6 = η/3 for every i. For x ∈ Q, choosing q_i with ‖x − q_i‖ < η/(3Λ + 3),
   |v_k(x) − v_{k'}(x)| ≤ |v_k(x) − v_k(q_i)| + |v_k(q_i) − v_{k'}(q_i)| + |v_{k'}(q_i) − v_{k'}(x)| ≤ 2Λη/(3Λ + 3) + η/3 < 2η/3 + η/3 = η,
 because 2Λ/(3Λ + 3) < 2/3.
 Hence ∫_Q |v_k − v_{k_s}| ≤ η μ(Q) < ε/4 for the representative k_s of the class of k.
 (iv) Conclusion. For every k there is s with
   ∫⁻_Q ‖u_k − u_{k_s}‖ₑ ≤ ∫⁻_Q ‖u_k − v_k‖ₑ + ∫⁻_Q ‖v_k − v_{k_s}‖ₑ + ∫⁻_Q ‖v_{k_s} − u_{k_s}‖ₑ < ofReal(3ε/4).
 So the set {[u_k|_Q] : k ∈ ℕ} is totally bounded in the complete metric space L¹(Q) := Lp ℝ 1 (volume.restrict Q). Each u_k is integrable on Q because Q is a compact subset of U.

A2. Diagonal extraction and the limit v.
 (a) Exhaustion. If U = ∅, take ψ := id and v := 0; all claims below are then trivial (every compact K ⊆ U and every W ⊂⊂ U is empty, IsLocallyBV ∅ 0 holds by SimonGMT isLocallyBV_zero, and bvVariationOn _ ∅ = 0). Otherwise let Q_j := {x ∈ closedBall(0,j) : infDist(x, Uᶜ) ≥ 1/j} if U ≠ E, and Q_j := closedBall(0,j) if U = E (j ≥ 1). Each Q_j is compact, Q_j ⊆ U, Q_j ⊆ interior Q_{j+1}, and ∪_j Q_j = U. Every compact K ⊆ U is covered by the increasing open sets interior Q_{j+1}, hence K ⊆ Q_j for some j.
 (b) Subsequences. In a complete metric space the closure of a totally bounded set is compact (TotallyBounded.isCompact_closure / isCompact_of_totallyBounded_isClosed), and every sequence in a compact metric set has a convergent subsequence (IsCompact.tendsto_subseq). Apply this successively. Choose ψ_1 strictly increasing such that ([u_{ψ_1(k)}|_{Q_1}]) converges in L¹(Q_1). Given ψ_j, choose φ_{j+1} strictly increasing such that ([u_{ψ_j(φ_{j+1}(k))}|_{Q_{j+1}}]) converges in L¹(Q_{j+1}), and set ψ_{j+1} := ψ_j ∘ φ_{j+1}. By A1 the range of each sequence lies in a totally bounded set.
 Let ψ(k) := ψ_k(k). Then ψ is strictly increasing: ψ(k+1) = ψ_k(φ_{k+1}(k+1)) ≥ ψ_k(k+1) > ψ_k(k). For each j, (ψ(k))_{k ≥ j} is a subsequence of (ψ_j(k))_k. Hence ([u_{ψ(k)}|_{Q_j}]) converges in L¹(Q_j) for every j.
 (c) The limit. Let v_j be a representative (an a.e.-strongly measurable function) of the L¹(Q_j)-limit, so ∫⁻_{Q_j} ‖u_{ψ(k)} − v_j‖ₑ → 0. For i < j, L¹-limits are a.e. unique, so v_j = v_i a.e. on Q_i. Define v := v_1 on Q_1, v := v_j on Q_j ∖ Q_{j−1} for j ≥ 2, and v := 0 off U. Then v = v_j a.e. on Q_j for every j, so ∫⁻_{Q_j} ‖u_{ψ(k)} − v‖ₑ → 0 for every j.
 (d) Local L¹ convergence and local integrability. If K ⊆ U is compact, then K ⊆ Q_j for some j, so ∫⁻_K ‖u_{ψ(k)} − v‖ₑ ≤ ∫⁻_{Q_j} ‖u_{ψ(k)} − v‖ₑ → 0. This is Chapter02.TendstoLocallyInL1On (fun k ↦ u (ψ k)) v U atTop. Moreover v is integrable on each Q_j (it is the a.e.-limit representative of an L¹(Q_j) element). Every point of the open set U has a compact neighbourhood contained in some Q_j, so LocallyIntegrableOn v U volume.

A3. Lower semicontinuity. Let W be open with W ⊂⊂ U. Apply SimonGMT Chapter02.bvVariationOn_le_liminf_of_locallyL1 with l = atTop, hu: LocallyIntegrableOn v U (A2(d)), hv: ∀ᶠ k, LocallyIntegrableOn (u (ψ k)) U (from IsLocallyBV), hL1 from A2(d), and hW: W ⊂⊂ U. It gives bvVariationOn v W ≤ liminf_k bvVariationOn (u (ψ k)) W. (For each admissible g, ∫_W v div g = lim_k ∫_W u_{ψ(k)} div g, because u_{ψ(k)} → v in L¹(closure W) and div g is bounded; and each term is ≤ |Du_{ψ(k)}|(W).)

A4. v is locally BV. Let W be open with W ⊂⊂ U and let c_W ≥ 0 be the constant of A0. Claim: for every k and every IsC1TestField g with tsupport g ⊆ W, ∫_W u_k div g ≤ c_W·s, where s := compactlySupportedSupNorm g ≥ 0.
 - If s = 0 then g ≡ 0 (every ‖g(x)‖ ≤ s), so div g ≡ 0 and ∫_W u_k div g = 0 = c_W·s.
 - If s > 0, put h := s⁻¹g. A compactly supported C¹ field is Lipschitz (SimonGMT IsC1TestField.isLipschitzTestField), and scaling preserves this; tsupport h = tsupport g ⊆ W, and compactlySupportedSupNorm h = s⁻¹·s = 1 ≤ 1. Since g is differentiable, Dh = s⁻¹Dg, so div h = s⁻¹ div g and ∫_W u_k div h = s⁻¹∫_W u_k div g. By SimonGMT ofReal_integral_le_bvVariationOn, ofReal(s⁻¹∫_W u_k div g) ≤ |Du_k|(W) ≤ ofReal c_W (A0(c)). Hence s⁻¹∫_W u_k div g ≤ c_W, i.e. ∫_W u_k div g ≤ c_W·s.
 So the hypothesis hbound of SimonGMT Chapter02.isLocallyBV_of_locallyL1_of_uniform_bound holds with c := c_W for all indices, in particular eventually along atTop for the subsequence u_{ψ(k)}. Together with U open, LocallyIntegrableOn v U, LocallyIntegrableOn (u (ψ k)) U, and TendstoLocallyInL1On (fun k ↦ u (ψ k)) v U atTop (A2), that lemma gives IsLocallyBV U v.

A5. Conclusion. ψ is strictly increasing (A2(b)), IsLocallyBV U v (A4), TendstoLocallyInL1On (fun k ↦ u (ψ k)) v U atTop (A2(d)), and the liminf inequality holds for every open W ⊂⊂ U (A3). This is exactly BVCompactness. ∎

## Key steps

1. A0: split the frozen integrand (constant |Du_k|(W) inside) and divide by 0 < Lⁿ(W) < ∞ (W = ∅ separately) to get c_W ≥ sup_k(∫_W|u_k| + |Du_k|(W)).
2. A1: for compact Q ⊆ U, W = thickening(δ,Q) ⊂⊂ U; Submission.bv_mollifier_sub_lintegral_le gives ∫_Q|ρ*(1_W u_k) − u_k| ≤ σ c_W uniformly in k; mollifications are uniformly bounded and equi-Lipschitz; elementary Arzelà–Ascoli ⇒ {u_k|_Q} totally bounded in L¹(Q).
3. A2: compact exhaustion Q_j of U, compactness of closures of totally bounded sets in the complete spaces L¹(Q_j), diagonal subsequence ψ, glued limit v; TendstoLocallyInL1On and LocallyIntegrableOn v U.
4. A3: lower semicontinuity from SimonGMT bvVariationOn_le_liminf_of_locallyL1.
5. A4: rescale C¹ test fields by their sup norm to get ∫_W u_k div g ≤ c_W sup|g|, then SimonGMT isLocallyBV_of_locallyL1_of_uniform_bound gives IsLocallyBV U v.

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

Solution PR: https://github.com/ZhengyangZhang06/gmt-formalize/pull/2371

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
