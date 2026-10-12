<!-- theorem-id: gmt-ch02/root.eilenberg_inequality-a1.compact_fiber_measurable-a1.compact_open_cover_content-a1 -->

## Theorem `Submission.eilenberg_compact_hausdorff_eq_iSup_open_content`

Let X be a metric space with its Borel σ-algebra, k > 0 real and F ⊆ X compact. For δ ∈ [0,∞] let U_δ(F) ∈ [0,∞] be the infimum (inf ∅ = ∞) of Σ_{i∈I} (ediam O_i)^k. The infimum runs over all finite sets I ⊆ ℕ and all families O : ℕ → Set X such that every O_i with i ∈ I is open with ediam O_i < δ, and F ⊆ ⋃_{i∈I} O_i. Here ediam = Metric.ediam is the extended diameter (ediam ∅ = 0), and powers in [0,∞] are ENNReal.rpow. Then μH[k](F) = sup_{n∈ℕ} U_{1/(n+1)}(F), where μH[k] = MeasureTheory.Measure.hausdorffMeasure k is Mathlib's unnormalized k-dimensional Hausdorff measure and 1/(n+1) = ((n : ℝ≥0∞) + 1)⁻¹.

Node: `root.eilenberg_inequality-a1.compact_fiber_measurable-a1.compact_open_cover_content-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/3

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/87

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.eilenberg_compact_hausdorff_eq_iSup_open_content`

```lean
∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (k : ℝ) (F : Set X), 0 < k → IsCompact F → MeasureTheory.Measure.hausdorffMeasure k F = ⨆ n : ℕ, ⨅ (I : Finset ℕ) (O : ℕ → Set X) (_ : ∀ i ∈ I, IsOpen (O i) ∧ Metric.ediam (O i) < ((n : ℝ≥0∞) + 1)⁻¹) (_ : F ⊆ ⋃ i ∈ I, O i), ∑ i ∈ I, Metric.ediam (O i) ^ k
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

- Parent DAG node: `root.eilenberg_inequality-a1.compact_fiber_measurable-a1`
- Child DAG node: `root.eilenberg_inequality-a1.compact_fiber_measurable-a1.compact_open_cover_content-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. This is Steps 3-5 of the parent-supplied proof of `eilenberg_compact_fiber_measurable`. That proof completes the measurability exercise Simon leaves after Ch. 2, Theorem 1.9, so no printed proof exists. The only change is the encoding: a finite open cover is a family O : ℕ → Set X restricted to a finite index set I ⊆ ℕ (a `Finset ℕ`), not a finite set of sets. This is exactly what `IsCompact.elim_finite_subcover` produces, so no merging of repeated sets is needed.

Conventions.
(C1) ediam = `Metric.ediam` (extended diameter; ediam ∅ = 0). For x ∈ [0,∞], x^k = `ENNReal.rpow x k`. Since k > 0:
- 0^k = 0 (`ENNReal.zero_rpow_of_pos`);
- x < ∞ implies x^k < ∞ (`ENNReal.rpow_ne_top_of_nonneg`);
- x ≤ x' implies x^k ≤ x'^k (`ENNReal.rpow_le_rpow`);
- x ↦ x^k is continuous on [0,∞] (`ENNReal.continuous_rpow_const`).
(C2) For r ∈ [0,∞] and E ⊆ X put
pre_r(E) := inf { Σ'_{n∈ℕ} [t_n ≠ ∅](ediam t_n)^k : t : ℕ → Set X, E ⊆ ⋃_n t_n, ediam t_n ≤ r for all n },
where [t ≠ ∅]x := ⨆ (_ : t.Nonempty), x, i.e. x if t ≠ ∅ and 0 if t = ∅. `MeasureTheory.Measure.hausdorffMeasure_apply` gives μH[k](E) = ⨆_{r>0} pre_r(E) for every E ⊆ X; no measurability is needed.
(C3) U_δ(E) := ⨅ (I : Finset ℕ) (O : ℕ → Set X) (_ : ∀ i ∈ I, IsOpen (O i) ∧ ediam (O i) < δ) (_ : E ⊆ ⋃ i ∈ I, O i), Σ_{i∈I} (ediam O_i)^k. The statement's right-hand side is ⨆_n U_{((n:ℝ≥0∞)+1)⁻¹}(F). A pair (I, O) satisfying both side conditions is called admissible for U_δ(E).

Proof.
1. (pre is antitone in the scale and bounded by μH[k].) Let E ⊆ X and r ≤ r'. Every family t with E ⊆ ⋃ t_n and ediam t_n ≤ r also satisfies ediam t_n ≤ r'. So the infimum defining pre_{r'}(E) runs over a larger set, and pre_{r'}(E) ≤ pre_r(E). For r > 0, pre_r(E) is one of the terms of the supremum in (C2), so pre_r(E) ≤ μH[k](E).

2. (pre_δ ≤ U_δ for every set and every δ.) Let δ ∈ [0,∞], E ⊆ X and (I, O) admissible for U_δ(E). Define t : ℕ → Set X by t_n := O_n if n ∈ I and t_n := ∅ if n ∉ I.
(a) E ⊆ ⋃_n t_n, because each x ∈ E lies in some O_i with i ∈ I, and t_i = O_i.
(b) ediam t_n ≤ δ for all n: if n ∈ I then ediam t_n = ediam O_n < δ; if n ∉ I then ediam t_n = ediam ∅ = 0 ≤ δ.
By (a), (b) and the definition of the infimum, pre_δ(E) ≤ Σ'_n [t_n ≠ ∅](ediam t_n)^k.
(c) For n ∉ I the n-th term is a supremum over the false proposition (∅).Nonempty, hence 0. So the tsum equals the finite sum over I (`tsum_eq_sum`).
(d) For n ∈ I the n-th term is ⨆_{(_ : O_n.Nonempty)} (ediam O_n)^k ≤ (ediam O_n)^k (`iSup_le`).
Hence pre_δ(E) ≤ Σ_{i∈I}(ediam O_i)^k. Taking the infimum over all admissible (I, O) gives pre_δ(E) ≤ U_δ(E).

3. (U_{2δ}(F) ≤ pre_δ(F) for the compact F and 0 < δ < ∞.) Let δ ∈ [0,∞] with 0 < δ and δ ≠ ∞. By `ENNReal.le_of_forall_pos_le_add`, it suffices to fix ε ∈ ℝ≥0 with ε > 0, assume pre_δ(F) < ∞, and prove U_{2δ}(F) ≤ pre_δ(F) + ε.
(a) Near-optimal countable cover. Since pre_δ(F) < ∞ and ε/2 ≠ 0, pre_δ(F) < pre_δ(F) + ε/2 (`ENNReal.lt_add_right`). An infimum below a bound has a term below it (`iInf_lt_iff`), so there is C : ℕ → Set X with:
- F ⊆ ⋃_n C_n;
- ediam C_n ≤ δ for every n;
- Σ'_n [C_n ≠ ∅](ediam C_n)^k < pre_δ(F) + ε/2.
(b) Error budget. Choose e : ℕ → [0,∞] with e_n > 0 for every n and Σ'_n e_n < ε/2 (`ENNReal.exists_pos_sum_of_countable'`, applied to ε/2 ≠ 0).
(c) Thickening radii. Claim: for every n there is η_n ∈ ℝ≥0 with η_n > 0, 2η_n < δ and (ediam C_n + 2η_n)^k ≤ (ediam C_n)^k + e_n.
- Since ediam C_n ≤ δ < ∞, a_n := (ediam C_n)^k < ∞ by (C1). So a_n < a_n + e_n, because e_n > 0.
- The maps g_1(η) := 2η and g_2(η) := (ediam C_n + 2η)^k from ℝ≥0 to [0,∞] are continuous. Each is built from the coercion ℝ≥0 → [0,∞], multiplication by the finite constant 2, addition of a constant and x ↦ x^k; in Lean, `fun_prop (disch := norm_num)` proves this.
- At η = 0 they take the values 0 < δ and a_n < a_n + e_n.
- The sets {η : g_1(η) < δ} and {η : g_2(η) < a_n + e_n} are open (`isOpen_lt`) and contain 0. So both strict inequalities hold on a neighbourhood of 0 in ℝ≥0.
- Every neighbourhood of 0 in ℝ≥0 contains some η > 0. Formally, the filter 𝓝[>] 0 is nontrivial, so `Filter.Eventually.exists` applies to `self_mem_nhdsWithin` combined, via `nhdsWithin_le_nhds`, with the two neighbourhood conditions.
Take such an η as η_n. The strict inequality for g_2 implies the stated non-strict one.
(d) Open enlargements. Put O_n := thickening (η_n : ℝ) C_n = {x : infEdist x C_n < η_n} (`Metric.thickening`). Then:
- O_n is open (`Metric.isOpen_thickening`);
- C_n ⊆ O_n, because η_n > 0 (`Metric.self_subset_thickening`);
- ediam O_n ≤ ediam C_n + 2η_n (`Metric.ediam_thickening_le`) ≤ δ + 2η_n < δ + δ = 2δ. The last strict inequality uses 2η_n < δ and δ ≠ ∞ (`ENNReal.add_lt_add_left`).
(e) Cost per index. For every n, (ediam O_n)^k ≤ [C_n ≠ ∅](ediam C_n)^k + e_n.
- If C_n = ∅, then O_n = thickening of ∅ = ∅ (`Metric.thickening_empty`), so (ediam O_n)^k = 0^k = 0 because k > 0.
- If C_n ≠ ∅, then [C_n ≠ ∅](ediam C_n)^k = (ediam C_n)^k (`iSup_pos`). By (d), monotonicity of x ↦ x^k and (c), (ediam O_n)^k ≤ (ediam C_n + 2η_n)^k ≤ (ediam C_n)^k + e_n.
(f) Finite subcover. F ⊆ ⋃_n C_n ⊆ ⋃_n O_n, and every O_n is open. Since F is compact, there is a finite I ⊆ ℕ (a `Finset ℕ`) with F ⊆ ⋃_{i∈I} O_i (`IsCompact.elim_finite_subcover`). By (d), (I, O) is admissible for U_{2δ}(F).
(g) Estimate.
U_{2δ}(F) ≤ Σ_{i∈I}(ediam O_i)^k
≤ Σ_{i∈I}([C_i ≠ ∅](ediam C_i)^k + e_i)   [(e), `Finset.sum_le_sum`]
≤ Σ'_i([C_i ≠ ∅](ediam C_i)^k + e_i)   [`ENNReal.sum_le_tsum`]
= Σ'_i [C_i ≠ ∅](ediam C_i)^k + Σ'_i e_i   [`ENNReal.tsum_add`]
≤ (pre_δ(F) + ε/2) + ε/2   [(a), (b)]
= pre_δ(F) + ε   [`ENNReal.add_halves`].
This proves step 3.

4. (Identification.) For n ∈ ℕ put δ_n := ((n : ℝ≥0∞) + 1)⁻¹. Then δ_n > 0 (`ENNReal.inv_pos`, since n + 1 ≠ ∞) and δ_n ≤ 1 (`ENNReal.inv_le_one`, since 1 ≤ n + 1). Rewrite μH[k](F) as ⨆_{r>0} pre_r(F) by `hausdorffMeasure_apply` and prove two inequalities.
(≤) Let r > 0. By `ENNReal.exists_inv_nat_lt` (r ≠ 0) there is n with (n : ℝ≥0∞)⁻¹ < r. Since n ≤ n + 1, δ_n ≤ n⁻¹ < r (`ENNReal.inv_le_inv`). By step 1 and step 2, pre_r(F) ≤ pre_{δ_n}(F) ≤ U_{δ_n}(F) ≤ ⨆_m U_{δ_m}(F). Taking the supremum over r > 0 gives μH[k](F) ≤ ⨆_n U_{δ_n}(F).
(≥) Fix n and put δ := δ_n/2. Then:
- δ > 0 (`ENNReal.div_pos`, since δ_n ≠ 0 and 2 ≠ ∞);
- δ ≠ ∞ (`ENNReal.div_ne_top`, since δ_n ≤ 1 < ∞ and 2 ≠ 0);
- 2δ = δ_n (`ENNReal.mul_div_cancel`).
By step 3 (F compact, k > 0), U_{δ_n}(F) = U_{2δ}(F) ≤ pre_δ(F). By step 1, pre_δ(F) ≤ μH[k](F) since δ > 0. Taking the supremum over n gives ⨆_n U_{δ_n}(F) ≤ μH[k](F).
Therefore μH[k](F) = ⨆_{n∈ℕ} U_{((n:ℝ≥0∞)+1)⁻¹}(F), which is the statement. ∎

Remarks. Compactness of F is used only in 3(f). The hypothesis k > 0 is used only in 3(c) (finiteness of a_n), in 3(e) (0^k = 0 and monotonicity) and, through step 3, in step 4. Steps 1 and 2 hold for every set and every k.

## Key steps

1. pre_r(E) is antitone in r, and pre_r(E) ≤ μH[k](E) for r > 0 by hausdorffMeasure_apply.
2. pre_δ(E) ≤ U_δ(E) for every set: pad a finite indexed open cover with ∅ and use tsum_eq_sum and [t ≠ ∅]x ≤ x.
3. For compact F and 0 < δ < ∞, U_{2δ}(F) ≤ pre_δ(F). Take a near-optimal countable cover C_n, thicken each C_n by η_n > 0 with 2η_n < δ and (ediam C_n + 2η_n)^k ≤ (ediam C_n)^k + e_n, where Σe_n < ε/2. Then extract a finite subcover by compactness and sum.
4. With δ_n = (n+1)⁻¹: for r > 0 choose δ_n < r, so pre_r ≤ pre_{δ_n} ≤ U_{δ_n}. Conversely U_{δ_n} = U_{2(δ_n/2)} ≤ pre_{δ_n/2} ≤ μH[k]. Hence μH[k](F) = ⨆_n U_{δ_n}(F).

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json (project 1b1689a8, mathlib 25730c7c)`
- `cmp local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean GMT/Ch02/Contract.lean (identical); grep -n '^end\|^section\|^noncomputable section\|^namespace\|^local notation\|^theorem main_theorem\|^open' GMT/Ch02/Contract.lean`
- `grep -n 'theorem hausdorffMeasure_apply' mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean; sed -n 520,600p (and variable context lines 121, 411, 443)`
- `grep -n 'UpperSemicontinuous.measurable\|protected theorem Measurable.iSup' mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`
- `grep -n 'theorem ediam_thickening_le\|theorem isOpen_thickening\|theorem self_subset_thickening\|theorem thickening_empty' mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `grep -rn '^noncomputable def ediam\|theorem ediam_empty\|theorem ediam_le\|theorem ediam_mono' mathlib/Mathlib/Topology`
- `grep -rn 'theorem tsum_eq_sum\|theorem tprod_eq_prod' mathlib/Mathlib/Topology/Algebra/InfiniteSum/`
- `grep -rn 'theorem exists_pos_sum_of_countable\|theorem exists_inv_nat_lt\|theorem le_of_forall_pos_le_add\|protected theorem tsum_add\|protected theorem sum_le_tsum' mathlib/Mathlib`
- `grep -n 'theorem IsCompact.elim_finite_subcover\|theorem IsCompact.diff\|theorem IsCompact.image_of_continuousOn' mathlib/Mathlib/Topology/Compactness/Compact.lean; grep -rn 'theorem rpow_ne_top_of_nonneg\|theorem zero_rpow_of_pos\|theorem rpow_le_rpow ' mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean`
- `grep -n 'theorem\|lemma\|def \|abbrev' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean; read Chapter01/HausdorffOpenCovers.lean`
- `python3 -I: collect all lean_name values in dag.json and nodes/*/*.json`
- `python3 -I scripts/gen.py (imports verifier gmt-compare.py contract_scope/child_modules and lean_contract.validate_lean_statement), then lean Challenge_child1.lean / Challenge_child2.lean against a scratch olean of GMT.Ch02.Submission built with plain `lean -o``
- `lean Final.lean (set_option autoImplicit false; CFMCheck.child1, child2, assembly, parent_from_children; #print axioms), via LSP and batch`
- `python3 -I: compare the dag.json lean_statement of root.eilenberg_inequality-a1.compact_fiber_measurable-a1 with the assembly target (identical: True)`
- `sed -n 330,420p book/chapter-02.txt (Simon Thm 1.9; measurability left as an exercise; [Fed69, 2.10.25])`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/EMetricSpace/Diam.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Algebra/InfiniteSum/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Basic/ENNReal/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/HausdorffOpenCovers.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-eilenberg-inequality-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-eilenberg-inequality-a1-compact-fiber-measurable-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/cfm-decomp-4YUkgw/checks/Challenge_child1.lean`
- `/tmp/cfm-decomp-4YUkgw/checks/Challenge_child2.lean`
- `/tmp/cfm-decomp-4YUkgw/checks/Final.lean`
- `/tmp/cfm-decomp-4YUkgw/checks/Final.batch.log`

**No existing result.** The snapshot (Mathlib 25730c7c, project 1b1689a8) has no ready-made theorem for either piece:
- No theorem on measurability of fibre Hausdorff measures.
- No theorem expressing Hausdorff measure of compact sets through finite open covers.
- SimonGMT's HausdorffOpenCovers.lean only proves that requiring open sets in countable covers leaves the fixed-scale content unchanged. Its exists_isOpen_superset_ediam_rpow_lt is an optional alternative for the thickening step and would need an extra import.

**Tools located and used.**
- Hausdorff measure and measurability: MeasureTheory.Measure.hausdorffMeasure_apply (Hausdorff.lean:546), UpperSemicontinuous.measurable (BorelSpace/Order.lean:649), Measurable.iSup (Order.lean:909).
- Thickenings and diameter: Metric.thickening with isOpen_thickening (Thickening.lean:74), thickening_empty (:79), self_subset_thickening (:309), ediam_thickening_le (:354); Metric.ediam (EMetricSpace/Diam.lean:30).
- Compactness: IsCompact.elim_finite_subcover, IsCompact.diff and IsCompact.image_of_continuousOn (Compact.lean:208/101/110).
- ENNReal sums and epsilons: ENNReal.exists_pos_sum_of_countable' (SpecificLimits/Basic.lean:649), ENNReal.le_of_forall_pos_le_add (Basic/ENNReal/Basic.lean:613), ENNReal.exists_inv_nat_lt (Basic/ENNReal/Inv.lean:650), ENNReal.tsum_add and ENNReal.sum_le_tsum (InfiniteSum/ENNReal.lean:108/119), tsum_eq_sum (additive form of tprod_eq_prod, InfiniteSum/Basic.lean:457).
- ENNReal powers: rpow_ne_top_of_nonneg, zero_rpow_of_pos and rpow_le_rpow (Pow/NNReal.lean:610/515/798).
- SimonGMT: simonHausdorffMeasureReal s = (realUnitBallVolume s / 2^s) • μH[s] (Chapter01/Hausdorff.lean:283).

**Contract scope.** The bare `end` at Contract.lean:374 closes the local notations 𝓗[·]/ω[·]. The child statements therefore spell out names explicitly. `open Poincare.SimonGMT` and namespace GMT.Ch02 (for Rn) remain in scope.

**Lean verification.**
- Both child lean_statements elaborate in the replayed comparator scope and under autoImplicit false.
- Both are proved outright in scratch Lean.
- The assembly proves the frozen parent type, which is byte-identical to dag.json.
- Every check uses only [propext, Classical.choice, Quot.sound].

**Names.** Both proposed names are unreserved.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: https://github.com/ZhengyangZhang06/gmt-formalize/pull/1560

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
