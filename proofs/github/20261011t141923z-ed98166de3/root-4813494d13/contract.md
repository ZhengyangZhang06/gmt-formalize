<!-- theorem-id: gmt-ch02/root -->

## Theorem `GMT.Ch02.main_theorem`

# Simon GMT, Chapter 2: Some Further Preliminaries from Analysis

Prove `GMT.Ch02.main_theorem`, stated in the frozen contract `GMT/Ch02/Contract.lean`, by completing `GMT/Ch02/Submission.lean` (initially a byte copy of the contract). The statement is the conjunction of the chapter's headline results; `GMT/Ch02/README.md` maps each conjunct to the book.

Source: Leon Simon, *Introduction to Geometric Measure Theory* (2014), Chapter 2, printed pages 39–68. Read-only copies for workers: `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt` and `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/simon-gmt.pdf` (printed page = PDF page − 7).

The pinned `simongmt` package (`Poincare.SimonGMT.*`) contains an earlier kernel-checked partial formalization of the book; its proofs may be reused as library lemmas where they apply. Do not rely on its definitions that the chapter README marks as unfaithful. Toolchain Lean v4.35.0-rc3, Mathlib 25730c7c. Every definition used by the statement must stay byte-identical; only standard axioms are allowed.

Node: `root`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/3

Parent: None (root)

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/33, https://github.com/ZhengyangZhang06/gmt-formalize/issues/34, https://github.com/ZhengyangZhang06/gmt-formalize/issues/35, https://github.com/ZhengyangZhang06/gmt-formalize/issues/36, https://github.com/ZhengyangZhang06/gmt-formalize/issues/37, https://github.com/ZhengyangZhang06/gmt-formalize/issues/38, https://github.com/ZhengyangZhang06/gmt-formalize/issues/39, https://github.com/ZhengyangZhang06/gmt-formalize/issues/40, https://github.com/ZhengyangZhang06/gmt-formalize/issues/41, https://github.com/ZhengyangZhang06/gmt-formalize/issues/42, https://github.com/ZhengyangZhang06/gmt-formalize/issues/43, https://github.com/ZhengyangZhang06/gmt-formalize/issues/44

## Lean problem

Declaration: `GMT.Ch02.main_theorem`

```lean
LipschitzExtension ∧ Rademacher ∧ C1Approximation ∧ WhitneyExtension ∧ LipschitzImageHausdorff ∧ EilenbergInequality ∧ BVCompactness ∧ BVPoincare ∧ BVExtensionEstimate ∧ AreaFormula ∧ FirstVariation ∧ SecondVariation ∧ StationaryIffMeanCurvatureZero ∧ SecondVariationStationary ∧ CoareaFormula ∧ C1Sard
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

# `GMT.Ch02.main_theorem`: final root proof

Simon, *Introduction to Geometric Measure Theory* (2014), Chapter 2, "Some further preliminaries
from analysis" (printed pp. 39–68).

- Run `20261011T141923Z-ed98166de3`, DAG node `root`, issue
  <https://github.com/ZhengyangZhang06/gmt-formalize/issues/3>.
- Frozen problem: commit `1b1689a8deba89d58b36b1a04dba493693824437`, contract
  `GMT/Ch02/Contract.lean`, declaration `GMT.Ch02.main_theorem`.
- Lean target: `GMT/Ch02/Submission.lean`. Toolchain Lean `v4.35.0-rc3`, Mathlib
  `25730c7c759d108ef87ab70af2342a196760f79d`, SimonGMT package `simongmt` (namespace
  `Poincare.SimonGMT`) at `2b3663083f3fe399b6296fb8eaee52169170e197`, as pinned in
  `lakefile.toml` and `lake-manifest.json` (unchanged from the frozen commit).

## 1. Statement

The theorem is

```lean
theorem main_theorem : LipschitzExtension ∧ Rademacher ∧ C1Approximation ∧ WhitneyExtension ∧
    LipschitzImageHausdorff ∧ EilenbergInequality ∧ BVCompactness ∧ BVPoincare ∧
    BVExtensionEstimate ∧ AreaFormula ∧ FirstVariation ∧ SecondVariation ∧
    StationaryIffMeanCurvatureZero ∧ SecondVariationStationary ∧ CoareaFormula ∧ C1Sard
```

in namespace `GMT.Ch02`. Each conjunct is a closed `Prop` defined in the frozen contract. Its
docstring and `GMT/Ch02/README.md` match it to the book: Theorems 1.2, 1.4, 1.5, 1.6, 1.8, 1.9
and 2.6, Lemmas 2.7 and 2.8, items 3.4–3.5, 5.3 and 5.4, Lemmas 5.5(2) and 5.11, items 6.3/6.6,
and Theorem 6.4. The theorem itself has no hypotheses. The contract builds the book's errata into the definitions. In
3.4 the target measure is `Hⁿ`, not `Hᵐ`. In 5.4 and 5.11 the deformations are `C³`, not `C²`.
In 1.5, `{∇f ≠ ∇g}` is read up to a null set. In 2.6 the sets `W ⊂⊂ U` are open. These
corrections are part of the frozen statement. The proof below adds no assumption of its own.

The candidate `Submission.lean` keeps every line of the contract, in its original order. Three
kinds of text are added:
- the two Mathlib imports `Mathlib.Analysis.Calculus.BumpFunction.Normed` and
  `Mathlib.Analysis.Convex.Measure`, which the accepted BV child added;
- the 175 accepted child theorems `GMT.Ch02.Submission.*`;
- the proof of `main_theorem`.

## 2. The root argument

The Lean proof of `main_theorem` is:

```lean
  obtain ⟨lipschitzExtension, rademacher⟩ := Submission.lipschitz_extension_and_rademacher
  obtain ⟨bvCompactness, bvPoincare, bvExtensionEstimate⟩ :=
    Submission.bv_compactness_poincare_extension
  obtain ⟨firstVariation, secondVariation⟩ := Submission.first_and_second_variation
  obtain ⟨stationaryIffMeanCurvatureZero, secondVariationStationary⟩ :=
    Submission.stationary_mean_curvature_and_stable_variation
  exact ⟨lipschitzExtension, rademacher, Submission.c1_approximation_theorem,
    Submission.whitney_extension_theorem, Submission.lipschitz_image_hausdorff_theorem,
    Submission.eilenberg_inequality_theorem, bvCompactness, bvPoincare, bvExtensionEstimate,
    Submission.area_formula_theorem, firstVariation, secondVariation,
    stationaryIffMeanCurvatureZero, secondVariationStationary,
    Submission.coarea_formula_theorem, Submission.c1_sard_theorem⟩
```

A conjunction holds when each of its conjuncts holds. Each of the sixteen conjuncts is an
accepted, kernel-checked child theorem, or a component of one. The types of these theorems are
literally the contract's `Prop` names, so no unfolding or conversion is needed:

| # | Conjunct | Simon | Supplied by (exact type) |
|---|---|---|---|
| 1 | `LipschitzExtension` | Thm 1.2 | `Submission.lipschitz_extension_and_rademacher : LipschitzExtension ∧ Rademacher`, first component |
| 2 | `Rademacher` | Thm 1.4 | the same theorem, second component |
| 3 | `C1Approximation` | Thm 1.5 | `Submission.c1_approximation_theorem : C1Approximation` |
| 4 | `WhitneyExtension` | Thm 1.6 | `Submission.whitney_extension_theorem : WhitneyExtension` |
| 5 | `LipschitzImageHausdorff` | Thm 1.8 | `Submission.lipschitz_image_hausdorff_theorem : LipschitzImageHausdorff` |
| 6 | `EilenbergInequality` | Thm 1.9 | `Submission.eilenberg_inequality_theorem : EilenbergInequality` |
| 7 | `BVCompactness` | Thm 2.6 | `Submission.bv_compactness_poincare_extension : BVCompactness ∧ BVPoincare ∧ BVExtensionEstimate`, first component |
| 8 | `BVPoincare` | Lemma 2.7 | the same theorem, second component |
| 9 | `BVExtensionEstimate` | Lemma 2.8 | the same theorem, third component |
| 10 | `AreaFormula` | 3.4, 3.5 | `Submission.area_formula_theorem : AreaFormula` |
| 11 | `FirstVariation` | 5.3 | `Submission.first_and_second_variation : FirstVariation ∧ SecondVariation`, first component |
| 12 | `SecondVariation` | 5.4 | the same theorem, second component |
| 13 | `StationaryIffMeanCurvatureZero` | Lemma 5.5(2) | `Submission.stationary_mean_curvature_and_stable_variation : StationaryIffMeanCurvatureZero ∧ SecondVariationStationary`, first component |
| 14 | `SecondVariationStationary` | Lemma 5.11 | the same theorem, second component |
| 15 | `CoareaFormula` | 6.3, 6.6 | `Submission.coarea_formula_theorem : CoareaFormula` |
| 16 | `C1Sard` | Thm 6.4 | `Submission.c1_sard_theorem : C1Sard` |

The twelfth accepted top-level child, `Submission.simon_submanifold_tangent_basics` (Simon
4.1–4.3), is not itself a conjunct. Section 4.8 gives its exact type. It is used inside the
proofs of conjuncts 11–16, as described in Sections 3 and 4.

So the root proof is just the anonymous constructor that the accepted root decomposition (v2)
announced: `⟨h1.1, h1.2, h3, h2, h4, h5, h6.1, h6.2.1, h6.2.2, h7, h9.1, h9.2, h10.1, h10.2,
h11, h12⟩`. Here `h_i` is the child theorem of decomposition group `i`. The groups are, in order:
1. Lipschitz extension and Rademacher;
2. Whitney;
3. `C¹` approximation;
4. Lipschitz images;
5. Eilenberg;
6. BV;
7. area formula;
8. tangent basics;
9. variation;
10. stationary;
11. co-area;
12. Sard.

Group 8 is used only inside groups 9–12. The rest of this document explains why each child
theorem holds and which results it rests on.

## 3. Dependencies actually used

The following facts were computed from the compiled environment of this candidate. The method
is a transitive walk over the constants that occur in `main_theorem`'s proof term, restricted to
the module `GMT.Ch02.Submission`.

- `main_theorem` reaches all 175 accepted `GMT.Ch02.Submission.*` declarations, plus four
  `match_` auxiliaries generated by the compiler. No accepted child declaration is unused. The
  175 names equal the set of `lean_name`s of the 175 accepted DAG nodes below `root`.
- The edges among the twelve top-level children that the Lean proofs really use are:
  - `c1_approximation_theorem` uses `lipschitz_extension_and_rademacher` (Rademacher) and
    `whitney_extension_theorem`;
  - `first_and_second_variation` uses `simon_submanifold_tangent_basics`;
  - `stationary_mean_curvature_and_stable_variation` uses `first_and_second_variation` and
    `simon_submanifold_tangent_basics`;
  - `coarea_formula_theorem` uses `simon_submanifold_tangent_basics`;
  - `c1_sard_theorem` uses `coarea_formula_theorem` and `simon_submanifold_tangent_basics`;
  - none of the other top-level children uses a sibling.

  These edges form an acyclic graph. No declaration refers to `main_theorem`.
- Planned versus actual. The accepted decomposition listed `area_formula_theorem` as a
  dependency of the variation, stationary and co-area children. The Lean proofs do not use it
  that way. Each of those subtrees proves the area formula it needs on charts:
  - the variation subtree: `variation_injective_area_formula`,
    `variation_injective_weighted_area_formula`, `variation_chart_image_area` and
    `variation_submanifold_image_area`;
  - the stationary subtree: inside `chart_setIntegral_eq_zero_of_trace_fderiv_eq`. This proof
    replays SimonGMT's `Chapter02.integral_area_formula_of_injective_derivative`, whose module
    `Chapter02/WeightedArea` is outside the import closure. A proof comment there says the
    image-measure step is the same replay as in `coarea_chart_area_pullback`, but the two subtrees
    share no Lean constant;
  - the co-area subtree: inside `coarea_chart_area_pullback` and
    `coarea_chart_fiber_disintegration`.

  As a result, `Submission.area_formula_theorem` is referenced only by `main_theorem`, for
  conjunct 10. The planned edge is part of the history; it is not a dependency of the formal
  proof.

## 4. Proof of each conjunct

Each accepted child was proved from its own accepted natural-language proof, supplied by the
reviewed root decomposition. These proofs are stored under
`.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/<child>/parent-supplied-natural-proof.md`.
Deeper descendants have their own accepted proofs in their own node directories. The summaries
below describe the argument as formalized, naming the accepted helper theorems it uses. All
helper names are in `GMT.Ch02.Submission`.

### 4.1 Conjuncts 1–2: Lipschitz extension (1.2) and Rademacher (1.4)

Child `root.lipschitz_ext_rademacher-a1` (PR #170, commit `c5b5552`) proves
`lipschitz_extension_and_rademacher`.

**Lipschitz extension.** Let `A ≠ ∅` and let `f : A → ℝ` be Lipschitz. Take the McShane
extension `F(x) = inf_{a∈A} (f(a) + L d(x,a))` with `L = Lip f`:
- `F = f` on `A`;
- `F` is `L`-Lipschitz;
- restricting a Lipschitz constant of `F` to `A` gives `Lip f ≤ Lip F`, so `Lip F = Lip f`.

This is exactly the pinned SimonGMT theorem
`Poincare.SimonGMT.Chapter02.lipschitz_extension_real_optimal`. Its constant
`optimalLipschitzConstant` is `sInf {K | LipschitzWith K f}`, which is the contract's `lipConst`.
The child only reorders the components of that result.

**Rademacher.** A Lipschitz `f : ℝⁿ → ℝ` is differentiable `Lⁿ`-a.e. This is Mathlib's
`LipschitzWith.ae_differentiableAt`, applied to the add-Haar measure `volume`. Its proof is the
Morrey/Rademacher argument: directional derivatives exist a.e., a weak gradient exists, and
uniformity is obtained over a countable dense set of directions.

### 4.2 Conjunct 4: Whitney extension (1.6)

Child `root.whitney_extension-a1` (PR #2139, commit `b3fc350`) proves
`whitney_extension_theorem`. The book cites Evans–Gariepy and Federer; the child follows
[EG92].

If `A = ∅`, take `g = 0`. Otherwise:
1. Put `d = dist(·, A)` and `r = min{1, d}/20`. Vitali's covering lemma
   (`Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall`) selects disjoint balls
   whose 5-fold enlargements cover `ℝⁿ ∖ A`. The 10-fold enlargements have bounded overlap and are
   locally finite (`whitney_cover_finite_overlap`).
2. Normalized bumps give a locally finite `C¹` partition of unity `φᵢ` on `ℝⁿ ∖ A`
   (`whitney_partition_of_finite_overlap_cover`, `whitney_smooth_partition_of_unity`). Each
   `φᵢ` has an anchor `pᵢ ∈ A` with `|x − pᵢ| ≤ C d(x)` wherever `φᵢ(x) ≠ 0`. The derivatives
   satisfy `Σᵢ ‖Dφᵢ(x)‖ ≤ M/d(x)` when `d(x) ≤ 1`.
3. Set `g = h` on `A`, and `g = Σᵢ φᵢ (h(pᵢ) + ⟨ν(pᵢ), · − pᵢ⟩)` off `A`.
4. `whitney_jet_gluing_c1` shows that `g` is `C¹` with `Dg(x) = ⟨ν(x), ·⟩` on `A`:
   - off `A`, `g` is a locally finite sum of `C¹` functions, with `Σ φᵢ = 1` and `Σ Dφᵢ = 0`
     (`whitney_gluing_local_structure`);
   - at `a ∈ A`, the uniform hypothesis (W) on a compact piece of `A` around `a`, together with
     the uniform continuity of `ν` there, gives differentiability with `Dg(a) = ⟨ν(a), ·⟩`
     (`whitney_gluing_hasFDerivAt`). The estimate uses that nearby anchors satisfy
     `|x − pᵢ| ≤ C d(x)`;
   - the same estimates give `Dg(x) → ⟨ν(a), ·⟩` as `x → a`
     (`whitney_gluing_continuousAt_fderiv`).

### 4.3 Conjunct 3: `C¹` approximation (1.5)

Child `root.c1_approximation-a1` (PR #2178, commit `a147893`) proves
`c1_approximation_theorem`. It follows the printed proof on p. 44.

1. By Rademacher (conjunct 2), `f` is differentiable on a co-null Borel set `B`, with a Borel
   gradient `ν`.
2. Lusin's theorem, extended to infinite measure by working on bounded shells, gives a closed
   `C ⊆ B` with `ν|C` continuous and `Lⁿ(B ∖ C) < ε/2` (`c1approx_lusin_closed_continuousOn`).
3. The remainder moduli `η_k` of `f` on `C` are Borel, and they tend to `0` on `C`
   (`c1approx_measurable_remainder_modulus`). They are suprema over a countable dense set.
4. Egorov's theorem on shells gives a closed `A ⊆ C` with `Lⁿ(C ∖ A) < ε/2`, such that
   `η_k → 0` uniformly on every compact subset of `A`
   (`c1approx_egorov_closed_compact_uniform`).
5. This uniform convergence is exactly the Whitney hypothesis for `(A, f, ν)`. Conjunct 4 gives a
   `C¹` function `g` with `g = f` and `Dg = Df` on `A`. Hence the exceptional set lies in
   `ℝⁿ ∖ A`, whose measure is `< ε`.

### 4.4 Conjunct 5: Hausdorff measure of Lipschitz images (1.8)

Child `root.lipschitz_image_hausdorff-a1` (PR #1800, commit `bdc1b2c`) proves
`lipschitz_image_hausdorff_theorem`.

**Part (i), the inequality.** `lipschitzImage_hausdorff_image_le` takes Mathlib's covering bound
`LipschitzOnWith.hausdorffMeasure_image_le` for `μH[m]` and multiplies it by the normalization
`ω_m/2^m`. This turns it into the bound for Simon's `𝓗ᵐ = (ω_m/2^m) • μH[m]`.

**Part (i), measurability.** Use `lipschitzImage_nullMeasurableSet_image`. A Borel kernel of `A`
carries a finite measure, which is regular on the σ-compact space `X`. So `A` is a countable
union of compact sets plus an `𝓗ᵐ`-null set. Then `f(A)` is a countable union of compact images
plus a subset of the image of a null set, and that image is null by the inequality.

**Part (ii).**
1. Nested countable Borel partitions of `X` with mesh `< 1/(i+1)` exist
   (`lipschitzImage_exists_nested_partitions`).
2. The piece counts `Nᵢ(y) = Σⱼ 1_{f(A ∩ P i j)}(y)` increase to `fiberCount A f`
   (`lipschitzImage_iSup_pieceCount_eq_fiberCount`).
3. Each `Nᵢ` is a.e. measurable by (i).
4. Monotone convergence and (i) then give `∫ N ≤ Kᵐ 𝓗ᵐ(A)`.

### 4.5 Conjunct 6: Eilenberg inequality (1.9)

Child `root.eilenberg_inequality-a1` (PR #1811, commit `d818e61`) proves
`eilenberg_inequality_theorem`.

**Covering majorant.** `eilenberg_covering_majorant` replaces the upper integral of Remark 1.10 by
an explicit Borel majorant. For `E ⊆ X` with `𝓗^{m+k}(E) < ∞` it produces a Borel
`G ≥ 𝓗ᵏ(E ∩ f⁻¹{·})` with `∫ G ≤ (ω_m ω_k/ω_{m+k}) Kᵐ 𝓗^{m+k}(E)`. It is built in three steps:
1. At each scale, `eilenberg_covering_fixed_scale_majorant` uses near-optimal covers. Each
   cover set contributes `(ω_k/2^k) diam^k` on the closed set `closure f(C ∩ E)`.
2. `eilenberg_covering_lipschitz_image_volume_le` bounds the volume of these sets by the
   isodiametric inequality (Simon Ch. 1, 2.10). The child proves that inequality inline, using
   Steiner symmetrization and the Gaussian/`Γ` computation of `ω_m`. The reviewed outline cited
   SimonGMT's `simon_theorem_2_10`; the Lean proof does not use it. The SimonGMT facts
   `realUnitBallVolume_pos`, `realUnitBallVolume_ne_top` and `realUnitBallVolume_zero` give the
   normalization.
3. Fatou's lemma over scales gives `G` (`eilenberg_covering_liminf_majorant`).

**Measurability for compact sets.** For compact `Q` the fibre measure `y ↦ 𝓗ᵏ(Q ∩ f⁻¹{y})` is
Borel (`eilenberg_compact_fiber_measurable`). It is a countable supremum of finite open-cover
contents (`eilenberg_compact_hausdorff_eq_iSup_open_content`), and each content is upper
semicontinuous in `y` (`eilenberg_fiber_open_content_upperSemicontinuous`).

**Assembly.**
1. `eilenberg_compact_exhaustion` writes `A = ⋃ Q_j ∪ N`, with compact `Q_j` increasing and
   `𝓗^{m+k}(N) = 0`.
2. The majorant of `N` has integral `0`. So `𝓗ᵏ(N ∩ f⁻¹y) = 0` for a.e. `y`.
3. Continuity from below then gives a.e. measurability of `y ↦ 𝓗ᵏ(A ∩ f⁻¹y)`.
4. The inequality is the majorant of `A` itself.

### 4.6 Conjuncts 7–9: BV compactness (2.6), Poincaré (2.7) and extension (2.8)

Child `root.bv_results-a1` (PR #2859, commit `5f29a27`) proves
`bv_compactness_poincare_extension` as
`⟨bv_compactness_theorem, bv_poincare_theorem, bv_extension_estimate_theorem⟩`.

**Shared toolkit (Lemma 2.5).**
- `bv_lipschitz_integration_by_parts`: `∫ F div g = −∫ DF[g]` for compactly supported Lipschitz
  `g`. It applies Mathlib's `LipschitzWith.integral_lineDeriv_mul_eq` in each coordinate.
- `bv_mollifier_tendsto_L1`: mollifications converge in `L¹`.
- `bv_mollifier_fderiv_lintegral_le`: `∫_K |D(ρ*u)| ≤ |Du|(W)` on inner parallel sets. It
  rests on:
  - `bv_integral_convolution_mul_reflect`, `bv_euclideanDivergence_convolution` and
    `bv_mollifier_integral_mul_div_le`, which move the derivative onto the test field through
    the convolution;
  - smooth duality, `bv_lintegral_norm_fderiv_le_of_dual_compact`, with its children
    `bv_exists_contDiff_gradient_of_contDiff_two`, `bv_regularized_unit_field_admissible` and
    `bv_set_lintegral_le_of_regularized_bound`;
  - the cut-off and exhaustion lemmas `bv_exists_smooth_cutoff` and
    `bv_lintegral_open_le_of_compact`.
- `bv_mollifier_sub_lintegral_le`: `∫_Q |ρ_σ*u − u| ≤ σ |Du|(W)`. It is proved from translation
  estimates (`bv_translate_sub_lintegral_le_of_fderiv`,
  `bv_translate_sub_lintegral_le_of_tendsto`) and kernel averaging
  (`bv_convolution_sub_lintegral_le_of_translate`).
- `bv_abs_variation_le`: `|D|u||(O) ≤ |Du|(O)`. It uses smoothed absolute values and the helpers
  `bv_abs_variation_mono_set`, `bv_abs_variation_exists_kernel` and
  `bv_abs_variation_smoothed_abs`.

**Theorem 2.6.**
1. Step A0 (`bv_compactness_uniform_bounds`). The frozen hypothesis has the variation inside the
   integrand. For open `W ⊂⊂ U`, step A0 turns it into a finite constant `c_W` that bounds both
   `∫_W |u_k|` and `|Du_k|(W)`. This step was added in decomposition v2.
2. Mollifications on a thickening of each compact `Q ⊆ U` have two properties. They are
   equibounded and equi-Lipschitz (`bv_convolution_bound_and_lipschitz`). They are also within
   `σ c_W` of `u_k` in `L¹(Q)`.
3. An Arzelà-type argument then gives finite `L¹(Q)`-nets
   (`bv_lintegral_finite_net_of_lipschitz_approx`).
4. A diagonal subsequence converges in `L¹_loc(U)` (`bv_exists_subseq_tendstoLocallyInL1On`). It
   uses `bv_isOpen_exists_compact_exhaustion`,
   `bv_exists_subseq_tendsto_lintegral_of_finite_nets` and
   `bv_tendstoLocallyInL1On_of_exhaustion_limits`.
5. Lower semicontinuity is the SimonGMT theorem
   `Chapter02.bvVariationOn_le_liminf_of_locallyL1`.
6. The `BV_loc` bound of the limit comes from `bv_integral_div_le_of_variation_le` and the
   SimonGMT theorem `Chapter02.isLocallyBV_of_locallyL1_of_uniform_bound`.

**Lemma 2.7, with `C = 2^{n+1}(1 + θ⁻¹)`.**
1. `convex_poincare_smooth_lintegral_le` proves the smooth Poincaré inequality on bounded convex
   open sets, `∫_O |w − w̄| ≤ 2ⁿ diam(O) ∫_O |Dw|`.
2. It is applied to mollifications on convex inner exhaustions
   (`convex_open_exists_inner_exhaustion`).
3. The bound passes to the limit (`mean_oscillation_lintegral_le_of_approx`).
4. The level-set hypothesis replaces the mean by `β` (`poincare_level_set_lintegral_le`).

**Lemma 2.8, with `C = max(1 + δ⁻¹, nδ⁻¹)`.**
1. `|Du|((closure U)ᶜ) = 0` because `u = 0` a.e. there
   (`bv_ext_variation_eq_zero_of_ae_eq_zero`).
2. Concavity of the distance `d` to `Uᶜ` gives `−∇d(x)·(x − ξ) > δR` near `∂U`, wherever `d` is
   differentiable (`bv_ext_infDist_compl_concaveOn`, `bv_ext_norm_fderiv_infDist_eq_one`,
   `bv_ext_infDist_compl_fderiv_lt`).
3. This yields Lipschitz cut-offs `φ_j → 1_U` (`bv_ext_exists_cutoffs`).
4. Testing with the field `(x − ξ)φ_j/R` and using `bv_abs_variation_le` bounds
   `∫ |u| |Dφ_j|` (`bv_ext_lintegral_enorm_mul_fderiv_le`, `bv_ext_euclideanDivergence_smul`,
   `bv_ext_ofReal_integral_le_bvVariationOn`).
5. For an admissible field `g`, the localized pairing (`bv_ext_ofReal_integral_cutoff_le`) bounds
   `∫ φ_j u div g` by `C(|Du|(U) + R⁻¹∫_U |u|)`.
6. Pass to the limit. `φ_j → 1_U`, and `1_U u = u` a.e., because `u = 0` a.e. off `Ū` and the
   frontier of the convex set `U` is null. So dominated convergence gives
   `∫ φ_j u div g → ∫ u div g`, and the supremum over `g` is the estimate.

The SimonGMT definitions and lemmas used here are `IsC1TestField`, `IsLipschitzTestField`,
`compactlySupportedSupNorm`, `euclideanDivergence` with `euclideanDivergence_eq_sum_inner`,
`measurable_euclideanDivergence`, `norm_euclideanDivergence_le_of_lipschitz` and
`support_euclideanDivergence_subset`, `ofReal_integral_le_bvVariationOn`, and
`tendsto_integral_mul_of_lintegral_sub`. All of them come from `Poincare.SimonGMT.Chapter02.BV`.

### 4.7 Conjunct 10: area formula (3.4, 3.5, with the `Hⁿ` erratum)

Child `root.area_formula-a1` (PR #1812, commit `c3e8e8a`) proves `area_formula_theorem`.

The reviewed outline planned to call the kernel-checked SimonGMT area-formula theorems
`weighted_area_formula_lipschitzOn_fiberSum`, `aemeasurable_weightedAreaFiberSum_lipschitzOn` and
`area_formula_lipschitzOn_multiplicity`. Those theorems live in SimonGMT modules such as
`Chapter02/AreaDomain.lean` and `AreaLiteral.lean`. These modules lie outside the import closure
of the frozen header, which reaches only `Chapter02.Area`, through `Chapter02.Submanifold`. So the
accepted Lean proof carries out the same argument inline:
1. The linear case 3.1 gives `Hⁿ(L(s)) = normDet L · Lⁿ(s)`, where `normDet L = √det(L*L)`.
   This is Mathlib's `LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume`, from
   `Mathlib/Analysis/InnerProductSpace/NormDet.lean`.
2. The injective case 3.2 is for maps with injective derivative. It uses Federer's approximation
   by linear maps on countably many Borel pieces, together with density points.
3. The images of critical points are null: they are projections of the regular graphs
   `y ↦ (g y, εy)`. The images of non-differentiability points are null by Rademacher, and the
   Lipschitz image bound is SimonGMT `Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn`.
4. Countably many injective Borel branches give the multiplicity formula 3.4 and the weighted
   formula 3.5.
5. A global Lipschitz extension `g` of `f|A` has derivative equal to `fderivWithin ℝ f A` at
   `Lⁿ`-a.e. point of `A`. This matches the contract's `areaJacobian (fderivWithin ℝ f A x)`.

`Hⁿ = Lⁿ` on `ℝⁿ` (`InnerProductSpace.euclideanHausdorffMeasure_eq_volume`) and
`finrank ℝ ℝⁿ = n` identify the measures. `√det(L*L) = normDet L` identifies the Jacobians.

### 4.8 Helper: tangent spaces, Borel measurability, continuity of `P` (4.1–4.3)

Child `root.submanifold_tangent-a1` (PR #2224, commit `93f0ed9`) proves
`simon_submanifold_tangent_basics`. Its type is
`(∀ n N r M V W ψ, 1 ≤ r → IsSimonLocalRepresentation r M V W ψ → ∀ x ∈ V, tangentSpace M (ψ x) =
range (fderiv ℝ ψ x)) ∧ ∀ n N r M, IsSimonSubmanifold r M → MeasurableSet M ∧ ContinuousOn
(tangentProjection M) M`. The proof has four steps:
1. Relative properness makes `ψ⁻¹` continuous on `W ∩ M`
   (`simon_submanifold_chart_inverse_continuousOn`, Simon 4.2).
2. `range Dψ(x) ⊆ T_{ψ(x)}M`, using the rescaled chart curves
   (`simon_chart_range_fderiv_le_tangentSpace`). Conversely, a `C¹` curve in `M` lifts through
   `ψ⁻¹`, and its velocity lies in the closed subspace `range Dψ(x)`
   (`simon_lift_velocity_mem_range_fderiv`, `simon_chart_tangentSpace_le_range_fderiv`). Together
   these give `simon_submanifold_tangentSpace_eq_range`.
3. `M` is locally closed, and Lindelöf covers it by countably many charts. So `M` is Borel
   (`simon_submanifold_measurableSet`).
4. `P_{range A} = A(A*A)⁻¹A*` depends continuously on injective `A`
   (`simon_submanifold_range_starProjection_continuousOn`). Composing with `Dψ` and `ψ⁻¹` gives
   the continuity of `y ↦ P_y` on `M` (`simon_submanifold_tangentProjection_continuousOn`).

The proof uses the SimonGMT API of `Chapter02.Submanifold`: `IsSimonSubmanifold`,
`IsSimonSubmanifold.exists_localRepresentation`, `IsSimonLocalRepresentation` with `contDiffOn`,
`image_eq`, `injective_fderiv`, `isOpen_source`, `isOpen_target`, and `IsProperOnInto`.

### 4.9 Conjuncts 11–12: first and second variation (5.3, 5.4 with the `C³` correction)

Child `root.variation_formulas-a1` (PR #2470, commit `dbf2459`) proves
`first_and_second_variation`.

Put `S = M ∩ K` and `e(y) = (y, P_y)`. Define
`g(t, (x, P)) = √det(I − P + P (Dφ_t x)*(Dφ_t x) P)`.
1. For `|t| < 1`, `φ_t` is injective on `S`, with injective derivative. Two results give
   `Hⁿ(φ_t(S)) = ∫_S g(t, e y) dHⁿ(y)`:
   - the area formula on `M` (`variation_submanifold_image_area`). It is built from the
     chart-level `variation_chart_image_area`, `variation_areaJacobian_chain_rule`,
     `variation_injective_area_formula` and `variation_injective_weighted_area_formula`;
   - the Gram identity `areaJacobian(A ∘ ι_T) = √det(I − P + P A*A P)`
     (`variation_gram_det_identity`).
2. `S` is Borel and `Hⁿ(S) < ∞`. By the helper of Section 4.8, `e` is continuous on `S`, with values in a
   compact set of pairs `(x, P)` with `P` idempotent and `‖P‖ ≤ 1`.
3. `g` is `C¹` at `t = 0`, and `C²` there in class `C³` (`variation_jacobian_family`). This uses:
   - the deformation calculus `variation_deformation_calculus`, with its children
     `variation_deformation_vanish_off_closed`, `variation_deformation_partials_contDiffOn` and
     `variation_deformation_mixed_partial`;
   - the derivatives of the Gram determinant at `t = 0` (`variation_gram_det_derivatives`). These
     come from Jacobi's formula to second order (`variation_matrix_det_derivatives_at_one`,
     `variation_matrix_det_hasDerivAt_leibniz` and the first- and second-order Leibniz lemmas)
     and from the derivatives of `√` at `1` (`variation_sqrt_derivatives_at_one`).
4. The derivatives at `0` are identified as follows:
   - the first `t`-derivative is `div_M X(y)`;
   - the second `t`-derivative is `secondVariationIntegrand M φ y`. Pythagoras for the normal
     parts gives this form.
5. Differentiation under the integral sign (`variation_param_integral_deriv`, which applies
   Mathlib's `hasDerivAt_integral_of_dominated_loc_of_deriv_le`) gives 5.3 and 5.4.
6. Both integrands vanish off `K`, so `∫_S = ∫_M`.

### 4.10 Conjuncts 13–14: stationary iff `H = 0` (5.5(2)), and 5.11

Child `root.stationary_results-a1` (PR #3392, commit `529af0a`) proves
`stationary_mean_curvature_and_stable_variation`. It applies three theorems to
`simon_submanifold_tangent_basics` and to conjuncts 11–12:
- `stationary_imp_mean_curvature_zero`;
- `mean_curvature_zero_imp_stationary`;
- `second_variation_stationary_of_variations`.

**Geometry of `B` and `H`.**
1. In a `C²` chart, `B(Dψ a, Dψ b) = (D²ψ[a, b])^⊥` (`second_fundamental_form_chart_formula`).
   Its children are `sff_range_starProjection_differentiableAt`,
   `sff_immersion_local_left_inverse`, `sff_tangentProjection_local_extension`,
   `sff_projection_field_fderiv_identity` and `sff_fderivWithin_chart_direction`.
2. Consequently (`second_fundamental_form_symm_normal_continuity`):
   - `B` is symmetric and normal;
   - `H` is continuous on `M`;
   - for normal fields `Y`, `⟨η, DY τ⟩ = −⟨Y, B(τ, η)⟩`.

   The helper lemmas are `fderiv_fderiv_symm_of_contDiffAt`, `gram_operator_isUnit_of_injective`,
   `second_fundamental_form_symm_normal_of_chart_formula`,
   `inner_fderiv_normal_field_eq_neg_second_fundamental_form`,
   `mean_curvature_eq_normalPart_gram_trace`, `mean_curvature_comp_chart_continuousOn` and
   `simon_submanifold_continuousOn_of_chart_continuousOn`.

**Divergence identity (4.30).** `submanifold_divergence_identity_compact` proves
`∫_M div_M Y = −∫_M ⟨Y, H⟩` for `C¹` fields `Y` vanishing off a closed `S` with `M ∩ S` compact.
1. In a chart, `(div_M Y + ⟨Y, H⟩)∘ψ · Jψ` is the divergence of a `C¹` field
   (`chart_divergence_density_formula`). This uses Jacobi's formula and the chart trace identities
   `chart_tangentialDivergence_eq_gram_trace`, `chart_meanCurvature_eq_normalPart_gram_sum`,
   `areaJacobianAt_contDiffOn_fderiv_eq_gram_trace`, `chart_tangential_coefficient_trace_identity`
   and the lemmas below them.
2. The Euclidean divergence theorem (`euclidean_setIntegral_trace_fderiv_eq_zero`) and the chart
   area formula (`chart_setIntegral_eq_zero_of_trace_fderiv_eq`) make each chart contribution
   vanish.
3. A finite partition of unity near the compact set `M ∩ S`
   (`exists_finite_contDiff_partition_near_compact`, `tangentialDivergence_add_inner_eq_sum_partition`,
   `tangentialDivergence_meanCurvature_integrableOn`) sums the chart pieces.
4. `Hⁿ` is finite on compact subsets of `M` and positive on relatively open subsets
   (`simon_submanifold_hausdorff_finite_pos`).

**5.5(2), direction ⇐.** Assume `H = 0` on `M ∩ U` and `Ū ∩ M` compact. For a compact `K ⊆ U`,
`Hⁿ(M ∩ K) < ∞`. By 5.3 the first variation is `∫_M div_M X`, and `X` is `C¹` and vanishes off
`K` (`deformation_velocity_acceleration_regularity`). By 4.30 this equals `−∫_M ⟨X, H⟩ = 0`.

**5.5(2), direction ⇒.**
1. For each `C²` field `Y` with compact support in `U`, `x + ctY(x)` is an admissible deformation
   (`scaled_field_deformation_is_admissible`).
2. Stationarity, 5.3 and 4.30 give `∫_M ⟨Y, H⟩ = 0`.
3. Continuity of `H` and positivity of `Hⁿ` on chart pieces then force `H = 0`
   (`vector_field_eq_zero_of_integral_inner_test_fields`,
   `simon_submanifold_exists_closedBall_isCompact_inter`).

**5.11 (`C³`).**
1. `M ∩ K` is compact, and `H = 0` on `M ∩ U` by 5.5(2) (⇒). Hence `∫_M div_M Z = 0` by 4.30, and
   `⟨X, H⟩ = 0`.
2. For normal `X`, the 5.4 integrand equals `div_M Z` plus the 5.11 integrand
   (`second_variation_integrand_eq_div_accel_add_stable`). The latter is integrable
   (`stable_second_variation_integrand_integrableOn`).
3. 5.4 gives the claim. If `U ∩ M = ∅`, both sides vanish.

### 4.11 Conjunct 15: co-area formula (6.3, 6.6)

Child `root.coarea_formula-a1` (PR #2498, commit `2cdec94`) proves `coarea_formula_theorem`.

1. **Linear algebra** (`coarea_jacobian_linear_algebra`):
   - `J*_f(x) = 0` exactly when `Df(x)∘A` is not onto, for `T_xM = range A`;
   - `J*_f(x) · normDet A = normDet B` for a chart `A` with `Df(x)(Ap) = p₁` and `B b = A(0, b)`.

   The helpers are `coareaJacobian_eq_normDet_adjoint`,
   `coareaJacobian_eq_zero_iff_not_surjective`, `coarea_normDet_block_triangular`,
   `coarea_normDet_adjoint_mul_normDet_chart` and `coareaJacobian_mul_normDet_chart`.
2. **Critical fibres** (`coarea_critical_fibers_null_euclidean`, `coarea_critical_fibers_null`).
   For `Lᵐ`-a.e. `y`, `Hᵏ(M ∩ f⁻¹y ∩ {J*_f = 0}) = 0`. In the Euclidean case:
   - images of small balls around critical points lie in thin slabs
     (`euclidean_slab_inter_closedBall_volume_le`,
     `volume_image_closedBall_le_of_fderiv_not_surjective`);
   - a packing bound counts the balls (`bounded_set_closedBall_cover_card_mul_pow_le` with
     `bounded_set_separated_finset_card_mul_pow_le` and
     `exists_separated_finset_subset_cover_closedBall`);
   - compactness gives the small covers (`critical_set_small_ball_covers_of_isCompact`);
   - Fatou concludes (`ae_hausdorffMeasure_fiber_eq_zero_of_small_ball_covers`).

   The result is transferred to `M` through countably many charts and the SimonGMT Lipschitz
   image bound.
3. **Straightening charts** (`coarea_exists_straightening_chart`). At a regular point, the
   local submersion theorem gives a chart `Ψ = ψ∘Λ` with `f∘Ψ = fst`
   (`coarea_straightening_submersion_chart`, `coarea_straightening_reparametrize_chart`).
4. **One chart** (`coarea_formula_on_straightening_chart`). The area formula for `Ψ` and the
   identity of step 1 pull `∫_S g J*_f dHⁿ` back to the chart (`coarea_chart_area_pullback`).
   Tonelli and the area formula for the fibre maps `b ↦ Ψ(a, b)` identify the result with
   `∫ ∫_{S∩f⁻¹y} g dHᵏ dLᵐ(y)`, with a Borel inner integral (`coarea_chart_fiber_disintegration`).
5. **Global formula for Borel `g`** (`coarea_formula_of_measurable`). Disjointed Borel pieces of
   countably many straightening charts cover `{J*_f ≠ 0}`. On the rest `J*_f = 0`, and its fibres
   are a.e. null by step 2.
6. **Reduction.** For `g` a.e.-measurable for `Hⁿ⌊M`, take a Borel `g₀ = g` off an `Hⁿ⌊M`-null
   Borel set `Z`. The formula for `1_Z` shows that a.e. fibre meets `Z` in an `Hᵏ`-null set. Both
   conclusions then transfer from `g₀` to `g`.

### 4.12 Conjunct 16: `C¹` Sard-type theorem (6.4)

Child `root.c1_sard-a1` (PR #2771, commit `58c9211`) proves `c1_sard_theorem`. The helper of
Section 4.8 (`simon_submanifold_tangent_basics`) makes `M` Borel, makes `y ↦ P_y` continuous on
`M`, and identifies `T_{ψx}M` with `range Dψ(x)`.

1. `J*_f(x) = 0` exactly when `rank df_x < m` (`c1_sard_coarea_jacobian_eq_zero_iff`): `L L*` is
   singular exactly when `range L ≠ ℝᵐ`.
2. `J*_f` is continuous on `M`, because `df_x df_x* = Df(x) P_x Df(x)*`. Hence the critical part of
   each fibre is `M ∩ F` for a closed `F` (`c1_sard_coarea_jacobian_continuousOn`).
3. Apply the co-area formula (conjunct 15) with `g = 1_{M ∩ {J*_f = 0}}`. The left side vanishes,
   so almost every critical fibre is `Hᵏ`-null (`c1_sard_critical_fibers_null`).
4. The regular part of each fibre is a `k`-dimensional `C¹` submanifold
   (`c1_sard_regular_fiber_submanifold`). In a chart `ψ`, `G = f∘ψ` is a submersion. Its level set
   has a `C¹` local representation (`c1_sard_submersion_level_set_chart`, by the inverse function
   theorem). Composing with `ψ` is a local representation of the fibre
   (`c1_sard_local_representation_comp`, by relative properness, 4.2).

## 5. Library reuse provenance

These are existing pinned declarations, used with full kernel verification; none is a new
helper. The list below gives every SimonGMT constant reachable from `main_theorem` through the
submission's own declarations, grouped by module. It was computed from the compiled
environment; auto-generated `_proof_`/`eq_` auxiliaries are omitted.

- `Poincare.SimonGMT.Chapter01.Hausdorff`: `simonHausdorffMeasureReal` and `realUnitBallVolume`,
  both in the statement, and the lemmas `realUnitBallVolume_pos`, `realUnitBallVolume_ne_top`
  and `realUnitBallVolume_zero`.
- `Poincare.SimonGMT.Chapter02.Lipschitz`: `lipschitz_extension_real_optimal`,
  `optimalLipschitzConstant`, `IsLipschitz`, `euclideanHausdorffMeasure_image_le_of_lipschitzOn`.
- `Poincare.SimonGMT.Chapter02.BV`: the definitions `IsLocallyBV`, `bvVariationOn`,
  `TendstoLocallyInL1On` and `IsRelativelyCompactIn`, all in the statement, and the definitions
  `IsC1TestField`, `IsLipschitzTestField`, `compactlySupportedSupNorm` and
  `euclideanDivergence`. It also supplies the lemmas `IsC1TestField.isLipschitzTestField`,
  `bvVariationOn_le_liminf_of_locallyL1`, `isLocallyBV_of_locallyL1_of_uniform_bound`,
  `euclideanDivergence_eq_sum_inner`, `measurable_euclideanDivergence`,
  `norm_euclideanDivergence_le_of_lipschitz`, `ofReal_integral_le_bvVariationOn`,
  `support_euclideanDivergence_subset` and `tendsto_integral_mul_of_lintegral_sub`.
- `Poincare.SimonGMT.Chapter02.Area`: `areaJacobianAt`, `areaJacobianAt_eq_normDet`,
  `areaJacobianAt_eq_sqrt_det_adjoint_comp`, `areaJacobianAt_sq_eq_det_adjoint_comp`. These are
  used in the stationary subtree; the module is imported transitively.
- `Poincare.SimonGMT.Chapter02.Submanifold`: `IsSimonSubmanifold` (in the statement),
  `IsSimonSubmanifold.exists_localRepresentation`, `IsSimonLocalRepresentation` and its fields
  `contDiffOn`, `image_eq`, `injOn`, `injective_fderiv`, `isCompact_source_inter_preimage`,
  `isOpen_source`, `isOpen_target`, and `IsProperOnInto`.

The README of the frozen problem lists the SimonGMT definitions that the contract reuses. The
pinned package is the frozen `lake-manifest.json` revision; this candidate does not change it.

The principal Mathlib results named above all come from Mathlib `25730c7c`. Each was located in
the pinned source, and each occurs in the candidate's proof text:

| Result | Mathlib file |
|---|---|
| `LipschitzWith.ae_differentiableAt` | `Analysis/Calculus/Rademacher.lean:385` |
| `LipschitzWith.integral_lineDeriv_mul_eq` | `Analysis/Calculus/Rademacher.lean:169` |
| `LipschitzOnWith.hausdorffMeasure_image_le` | `MeasureTheory/Measure/Hausdorff.lean:733` |
| `Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall` | `MeasureTheory/Covering/Vitali.lean:158` |
| `hasDerivAt_integral_of_dominated_loc_of_deriv_le` | `Analysis/Calculus/ParametricIntegral.lean:286` |
| `LinearMap.normDet`, `LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume` | `Analysis/InnerProductSpace/NormDet.lean:69, 433` |
| `InnerProductSpace.euclideanHausdorffMeasure_eq_volume`, `EuclideanSpace.euclideanHausdorffMeasure_eq_volume` | `Geometry/Euclidean/Volume/Measure.lean:187, 191` |

The SimonGMT import graph is as follows. `Chapter02.Submanifold` imports `Chapter02.Area`, and
`Chapter02.Area` imports `Chapter02.Lipschitz`. `Chapter02.BV` imports `Chapter02.Lipschitz`, and
`Chapter02.Lipschitz` imports `Chapter01.Hausdorff`. So every SimonGMT module listed above is in
the closure of the frozen header's three SimonGMT imports.

## 6. Assumptions, axioms and checks

- **No placeholders or escape hatches.** The candidate file contains no occurrence of `sorry`,
  `admit`, `native_decide`, `implemented_by`, `extern` or `unsafe`. It has no `axiom`, `opaque`,
  `macro`, `elab`, `syntax`, `#eval` or `run_cmd` command. (The word "opaque" appears once, in a
  proof comment of the Whitney cover.) It has exactly one `namespace GMT.Ch02` / `end GMT.Ch02`
  pair, one `main_theorem`, and no duplicated declarations.
- **Axioms.** `#print axioms GMT.Ch02.main_theorem` gives `[propext, Classical.choice, Quot.sound]`.
  A sweep over all 175 `GMT.Ch02.Submission.*` declarations and `main_theorem`, using
  `Lean.collectAxioms`, found no other axiom.
- **Child interfaces.** The comparator's own `contract_scope` replay of the frozen contract scope
  was used for all 175 accepted DAG nodes. Each frozen `lean_statement` elaborates and is closed
  by `exact Submission.<lean_name>`, exactly as in the comparator's `NodeSolution` module. All
  175 pass.
- **Build.** `lake env lean GMT/Ch02/Submission.lean` succeeds with no errors and no warnings,
  in 585 s.
- **Comparator.** The exact configured comparator (`verifier/gmt-compare.py ... root`, with frozen
  commit `1b1689a`) was run on the committed Lean candidate `c19e9bff4f1e143480aba012b46adaad53a82673`.
  It printed `GMT comparator: comparator and Lean kernel accepted GMT.Ch02.main_theorem` and
  `Your solution is okay!`. The receipt is
  `cluster-state/verification/results/hoa12/20261012T201441Z-ch02-root-7_k4chuz/result.json`,
  with `status: passed`, the checks `exit_zero`, `lean_kernel_accepted` and `final_marker` all
  true, and no post-check failures. Its verdict key is
  `7b1ee3c2d3a9c5a9c6ee7734b8d716d70130e13069589e26b86361fe6fe25037`, and the Submission sha256 is
  `e0d00933f6cfaa4bd09e07c8eeae8bdfb7e327ac82522b359fb4bdf018893519`. This document is the only
  file added afterwards. It is not a comparator input, since the comparator reads only `.lean`
  files and Lake inputs.

## 7. History: decomposition and integration

The following records are preserved unchanged in the run directory under
`nodes/root/`:
- the root plan (`plan-source.md`, the scaffold from the published proof);
- the operator-supplied published-proof source (`natural-proof-source.md`);
- the decompositions `decomposition-v1.json` and `decomposition-v2.json`;
- the audits and review receipts for both versions.

The decomposition went through two versions:
- **v1.** Eleven children were accepted. `bv_results` was rejected because the BVCompactness
  hypothesis has the variation inside the integrand.
- **v2.** Accepted. It added step A0 (Section 4.6) and changed nothing else.

The twelve child solutions (PRs #170, #2139, #2178, #1800, #1811, #2859, #1812, #2224, #2470,
#3392, #2498, #2771) and the speculative root draft `0373c14` were merged into the first
integrated candidate `c35aac9`. The comparator rejected it (`nodes/root/comparator-v1.log`). The
children had inserted their theorems at the same position: right after the contract's closing
`end`, or, for the area-formula block, after `def AreaFormula`. The textual merge interleaved
these blocks. This broke proofs near lines 6259, 6874–6893,
7051, 7326–7395, 7462–7844 and 10882–10899. It also left `main_theorem` (line 12410) before
declarations that several children had placed after the `main_theorem` stub, which caused
`Unknown identifier Submission.bv_compactness_poincare_extension`.

This candidate rebuilds `Submission.lean` from the accepted child commits:
- The contract text is kept as is, and the BV child's two imports are kept.
- Each of the 175 declarations is taken verbatim. Where several children contain the same
  declaration, the copies are byte-identical; the only variation found was a trailing blank line
  after `lipschitz_extension_and_rademacher`.
- Declarations keep the relative order they have in every child.
- Every child theorem comes before `main_theorem`, whose body is the draft's assembly. No proof
  text was written or changed apart from this reordering.

## 8. Reference use

```json
[
  {
    "source": "local-project",
    "snapshot": ".humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7",
    "manifest": {"mode": "local-project", "project_commit": "1b1689a8deba89d58b36b1a04dba493693824437", "mathlib_commit": "25730c7c759d108ef87ab70af2342a196760f79d"},
    "queries": [
      "rg -n 'main_theorem' <snapshot>/project",
      "rg -n 'Submission\\.' <snapshot>/project",
      "cmp <snapshot>/project/GMT/Ch02/Contract.lean GMT/Ch02/Contract.lean; cmp <snapshot>/project/GMT/Ch02/Submission.lean <snapshot>/project/GMT/Ch02/Contract.lean",
      "cat <snapshot>/project/GMT/Ch02/README.md (statement map, reused SimonGMT definitions, errata)",
      "rg -n '^theorem LipschitzWith.ae_differentiableAt|^theorem integral_lineDeriv_mul_eq' <snapshot>/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean",
      "rg -n '^theorem hausdorffMeasure_image_le \\(h : LipschitzOnWith' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean",
      "rg -n '^theorem exists_disjoint_subfamily_covering_enlargement_closedBall' <snapshot>/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean",
      "rg -n '^theorem hasDerivAt_integral_of_dominated_loc_of_deriv_le' <snapshot>/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean",
      "rg -n '^noncomputable def normDet|^theorem euclideanHausdorffMeasure_image_eq_normDet_mul_volume' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean",
      "rg -n '^theorem (EuclideanSpace|InnerProductSpace)\\.euclideanHausdorffMeasure_eq_volume' <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean",
      "rg -n 'weighted_area_formula_lipschitzOn_fiberSum' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean <snapshot>/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean",
      "grep -n 'import' <simongmt>/Poincare/SimonGMT/{Chapter01/Hausdorff,Chapter02/BV,Chapter02/Submanifold,Chapter02/Area,Chapter02/Lipschitz}.lean (pinned simongmt 2b36630, the package of the frozen lake-manifest.json)",
      "Lean: transitive constant walk from GMT.Ch02.main_theorem over the compiled candidate (module of each constant via Environment.getModuleIdxFor?), Lean.collectAxioms over all 176 declarations, and the comparator's contract_scope replay for the 175 child statements"
    ],
    "findings": [
      "The snapshot's Contract.lean is byte-identical to the candidate's GMT/Ch02/Contract.lean. The snapshot's Submission.lean is the unsolved byte copy, whose main_theorem is `by sorry`.",
      "rg 'Submission\\.' finds only README/PROBLEM prose and no Lean declaration. No accepted child theorem exists upstream; all 175 come from the accepted child solution commits.",
      "main_theorem occurs in the snapshot only as the frozen `by sorry` statement (Ch01, Ch02, Ch08 contracts and their byte-copy submissions) and in README prose.",
      "The Mathlib declarations cited in Section 5 are at Rademacher.lean:169 and :385, Hausdorff.lean:733, Vitali.lean:158, ParametricIntegral.lean:286, NormDet.lean:69 and :433, and Volume/Measure.lean:187 and :191. These are the same lines as in the pinned build tree lake-packages-25730c7c.",
      "No match: the SimonGMT area theorem weighted_area_formula_lipschitzOn_fiberSum is not in the Mathlib files that provide the linear area formula. The SimonGMT import closure of the frozen header reaches Chapter02.Area but not AreaDomain/AreaLiteral, which is why the area child inlines the argument.",
      "README.md lists the SimonGMT material that the children reuse: lipschitz_extension_real_optimal, bvVariationOn_le_liminf_of_locallyL1, isLocallyBV_of_locallyL1_of_uniform_bound and the IsSimonSubmanifold API. It also lists the Mathlib result LipschitzWith.ae_differentiableAt.",
      "main_theorem reaches all 175 accepted Submission.* declarations. Every reached SimonGMT constant lies in Chapter01.Hausdorff, Chapter02.Lipschitz, Chapter02.BV, Chapter02.Area or Chapter02.Submanifold. Every declaration uses only the axioms propext, Classical.choice and Quot.sound."
    ],
    "files": [
      ".humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json",
      ".humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean",
      ".humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Submission.lean",
      ".humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/README.md",
      ".humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean",
      ".humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean",
      ".humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean",
      ".humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean",
      ".humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean",
      ".humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean"
    ],
    "use": "Confirms the frozen contract and that the root assembly depends only on the accepted child declarations and on the pinned SimonGMT and Mathlib revisions recorded in the manifest. Gives the exact provenance of each library declaration cited in this proof."
  }
]
```

No public web source was needed for the root step. It is a conjunction of accepted children, and
the mathematical sources (Simon; Evans–Gariepy for Whitney) are cited in the accepted child
proofs.

## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Root delivery: merge the exact checked root PR, confirm the remote tree, then link and close child review PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
