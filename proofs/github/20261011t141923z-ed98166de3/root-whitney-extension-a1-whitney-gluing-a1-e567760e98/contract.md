<!-- theorem-id: gmt-ch02/root.whitney_extension-a1.whitney_gluing-a1 -->

## Theorem `Submission.whitney_jet_gluing_c1`

Let n ∈ ℕ, ℝⁿ = EuclideanSpace ℝ (Fin n), A ⊆ ℝⁿ closed, h : ℝⁿ → ℝ, and ν : ℝⁿ → ℝⁿ continuous on A, and assume (W): for every compact K ⊆ A and every ε > 0 there is δ > 0 with |h(y) − h(x) − ⟨ν(x), y − x⟩| ≤ ε|y − x| for all x ∈ K and y ∈ A with 0 < |y − x| < δ. Let ι be a type, φ_i : ℝⁿ → ℝ and p_i ∈ ℝⁿ (i ∈ ι), and C ≥ 0, M ≥ 0 reals such that, with d(x) := dist(x, A): (P1) p_i ∈ A for all i; (P2) every φ_i is C¹ at every x ∉ A; (P3) φ_i(x) ≥ 0 for x ∉ A; (P4) every x ∉ A has a neighbourhood V and a finite s ⊆ ι with φ_i ≡ 0 on V for i ∉ s; (P5) Σᶠ_i φ_i(x) = 1 for x ∉ A; (P6) x ∉ A and φ_i(x) ≠ 0 imply |x − p_i| ≤ C·d(x); (P7) x ∉ A and d(x) ≤ 1 imply Σᶠ_i ‖Dφ_i(x)‖ ≤ M/d(x). If g : ℝⁿ → ℝ satisfies g(x) = h(x) for x ∈ A and g(x) = Σᶠ_i φ_i(x)(h(p_i) + ⟨ν(p_i), x − p_i⟩) for x ∉ A, then g is C¹ on ℝⁿ and Dg(x)v = ⟨ν(x), v⟩ for every x ∈ A and v ∈ ℝⁿ.

Node: `root.whitney_extension-a1.whitney_gluing-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/3

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/34

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/349, https://github.com/ZhengyangZhang06/gmt-formalize/issues/350, https://github.com/ZhengyangZhang06/gmt-formalize/issues/352

## Lean problem

Declaration: `Submission.whitney_jet_gluing_c1`

```lean
∀ (n : ℕ) (A : Set (Rn n)) (h : Rn n → ℝ) (ν : Rn n → Rn n) (ι : Type) (φ : ι → Rn n → ℝ) (p : ι → Rn n) (C M : ℝ) (g : Rn n → ℝ), IsClosed A → ContinuousOn ν A → (∀ K ⊆ A, IsCompact K → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ y ∈ A, 0 < ‖y - x‖ → ‖y - x‖ < δ → |h y - h x - inner ℝ (ν x) (y - x)| ≤ ε * ‖y - x‖) → 0 ≤ C → 0 ≤ M → (∀ i, p i ∈ A) → (∀ i, ∀ x ∉ A, ContDiffAt ℝ 1 (φ i) x) → (∀ i, ∀ x ∉ A, 0 ≤ φ i x) → (∀ x ∉ A, ∃ s : Finset ι, ∃ V ∈ 𝓝 x, ∀ i ∉ s, ∀ y ∈ V, φ i y = 0) → (∀ x ∉ A, ∑ᶠ i, φ i x = 1) → (∀ i, ∀ x ∉ A, φ i x ≠ 0 → ‖x - p i‖ ≤ C * Metric.infDist x A) → (∀ x ∉ A, Metric.infDist x A ≤ 1 → ∑ᶠ i, ‖fderiv ℝ (φ i) x‖ ≤ M / Metric.infDist x A) → (∀ x ∈ A, g x = h x) → (∀ x ∉ A, g x = ∑ᶠ i, φ i x * (h (p i) + inner ℝ (ν (p i)) (x - p i))) → ContDiff ℝ 1 g ∧ ∀ x ∈ A, ∀ v, fderiv ℝ g x v = inner ℝ (ν x) v
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
- Child DAG node: `root.whitney_extension-a1.whitney_gluing-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: this is steps 4-6 of the parent-supplied proof of WhitneyExtension (Simon, Introduction to GMT, Ch. 2, Theorem 1.6, proof supplied after [EG92], Whitney's extension theorem), extracted for an abstract Whitney partition of unity: the parent's constants 3 (anchor bound (F4)) and 20NC₁ (derivative bound) become the parameters C and M, and the parent's modulus ω of ν on K_a is replaced by continuity of ν at the base point (ν(p) − ν(q) = (ν(p) − ν(a)) − (ν(q) − ν(a))). Notation: ℝⁿ = EuclideanSpace ℝ (Fin n), |·| the Euclidean norm, ‖·‖ the operator norm of a linear functional, U := ℝⁿ∖A, d(x) := Metric.infDist x A, L_y := ⟨ν(y), ·⟩ (so ‖L_y − L_z‖ = |ν(y) − ν(z)|), and P_i(y) := h(p_i) + ⟨ν(p_i), y − p_i⟩, an affine function with derivative L_{p_i} at every point.

Hypotheses. A is closed, ν is continuous on A, and (W): for every compact K ⊆ A and ε > 0 there is δ > 0 with |h(y) − h(x) − ⟨ν(x), y − x⟩| ≤ ε|y − x| for all x ∈ K, y ∈ A with 0 < |y − x| < δ. The family (φ_i, p_i)_{i∈ι} and the constants C ≥ 0, M ≥ 0 satisfy (P1) p_i ∈ A; (P2) φ_i is C¹ at every x ∈ U; (P3) φ_i ≥ 0 on U; (P4) every x ∈ U has a neighbourhood V and a finite s ⊆ ι with φ_i ≡ 0 on V for i ∉ s; (P5) Σᶠ_i φ_i(x) = 1 on U; (P6) x ∈ U, φ_i(x) ≠ 0 ⇒ |x − p_i| ≤ C·d(x); (P7) x ∈ U, d(x) ≤ 1 ⇒ Σᶠ_i ‖Dφ_i(x)‖ ≤ M/d(x). Finally g = h on A and g(x) = Σᶠ_i φ_i(x)P_i(x) for x ∈ U. Claim: g is C¹ and Dg(x)v = ⟨ν(x), v⟩ for x ∈ A, v ∈ ℝⁿ. (Continuity of h on A is not needed.)

Proof.

0. Two elementary facts.
(E1) For all a, b, y ∈ ℝⁿ: h(b) + ⟨ν(b), y − b⟩ − (h(a) + ⟨ν(a), y − a⟩) = [h(b) − h(a) − ⟨ν(a), b − a⟩] + ⟨ν(b) − ν(a), y − b⟩, because ⟨ν(a), y − a⟩ = ⟨ν(a), y − b⟩ + ⟨ν(a), b − a⟩.
(E2) d(x) ≤ |x − a| for every a ∈ A (infDist_le_dist_of_mem). If A ≠ ∅, then d(x) > 0 for every x ∈ U (IsClosed.notMem_iff_infDist_pos). If A = ∅, then U = ℝⁿ, step 1 shows that g is C¹ at every point and the second conclusion is vacuous; steps 2-4 fix a point a ∈ A, so there A ≠ ∅.

1. Local structure on U. Fix x₀ ∈ U. By (P4) choose a finite s ⊆ ι and a neighbourhood V of x₀ with φ_i ≡ 0 on V for i ∉ s, and put W := V ∩ U, a neighbourhood of x₀ (U is open). For y ∈ W the functions i ↦ φ_i(y) and i ↦ φ_i(y)P_i(y) vanish outside s, so (finsum_eq_sum_of_support_subset, (P5))
(1a) g(y) = Σ_{i∈s} φ_i(y)P_i(y) and (1b) Σ_{i∈s} φ_i(y) = 1 for all y ∈ W.
(1c) G := Σ_{i∈s} φ_i·P_i is C¹ at x₀ (finite sum of products of the C¹-at-x₀ functions φ_i, by (P2), with affine functions) and g = G on W, so g is C¹ at x₀ (ContDiffAt.congr_of_eventuallyEq). Hence g is differentiable at x₀, fderiv g is continuous at x₀ (ContDiffAt.continuousAt_fderiv), and by the product rule Dg(x₀) = Σ_{i∈s} [φ_i(x₀)L_{p_i} + P_i(x₀)Dφ_i(x₀)].
(1d) Σ_{i∈s} Dφ_i(x₀) = 0, by differentiating (1b): Σ_{i∈s} φ_i equals the constant 1 on the neighbourhood W.
(1e) Dφ_i(x₀) = 0 whenever i ∉ s (φ_i ≡ 0 on V) and whenever φ_i(x₀) = 0: in the latter case φ_i ≥ 0 on the open set U ∋ x₀ (P3), so x₀ is a local minimum of φ_i, which is differentiable at x₀ (P2), hence Dφ_i(x₀) = 0 (IsLocalMin.fderiv_eq_zero).
(1f) Let S := {i ∈ s : φ_i(x₀) ≠ 0}. By (P6), |x₀ − p_i| ≤ C·d(x₀) for i ∈ S. By (1b), Σ_{i∈S} φ_i(x₀) = 1 with all φ_i(x₀) ≥ 0. By (1e), i ↦ ‖Dφ_i(x₀)‖ is supported in s, so Σ_{i∈s} ‖Dφ_i(x₀)‖ = Σᶠ_i ‖Dφ_i(x₀)‖ ≤ M/d(x₀) whenever d(x₀) ≤ 1 (P7).
(1g) Consequently, for every a ∈ ℝⁿ and every pair of reals c, q: by (1a),(1b), g(x₀) − q = Σ_{i∈S} φ_i(x₀)(P_i(x₀) − q); and by (1c),(1b),(1d),(1e), Dg(x₀) − L_a = Σ_{i∈S} φ_i(x₀)(L_{p_i} − L_a) + Σ_{i∈S} (P_i(x₀) − c)Dφ_i(x₀).

2. Uniform estimates near a ∈ A. Fix a ∈ A and ε > 0. Let K := A ∩ B̄(a, 1); K is compact (closed and bounded in ℝⁿ), K ⊆ A and a ∈ K. By (W) choose δ₁ > 0 with |h(y) − h(x) − ⟨ν(x), y − x⟩| ≤ ε|y − x| for x ∈ K, y ∈ A, 0 < |y − x| < δ₁; this inequality holds trivially when y = x. By continuity of ν at a within A choose τ > 0 with |ν(y) − ν(a)| ≤ ε for y ∈ A, |y − a| < τ. Put ρ := min{1, δ₁, τ}/(C + 2) > 0; note (C + 1)ρ < min{1, δ₁, τ} and 2ρ ≤ min{1, δ₁, τ} because C ≥ 0. Let |x − a| < ρ. Then:
(2a) d(x) ≤ |x − a| < ρ ≤ 1/2 by (E2).
(2b) If x ∈ U and φ_i(x) ≠ 0, then |x − p_i| ≤ C·d(x) ≤ C|x − a| (P6) and |p_i − a| ≤ |p_i − x| + |x − a| ≤ (C + 1)|x − a| < min{1, δ₁, τ}; so p_i ∈ K (by (P1)), |ν(p_i) − ν(a)| ≤ ε and, by (W) with base point a ∈ K and y = p_i, |h(p_i) − h(a) − ⟨ν(a), p_i − a⟩| ≤ ε|p_i − a| ≤ ε(C + 1)|x − a|.

3. Differentiability on A. Fix a ∈ A; we show HasFDerivAt g L_a a. Let ε > 0 and take ρ as in step 2; let |x − a| < ρ. Recall g(a) = h(a).
- If x ∈ A: |g(x) − g(a) − L_a(x − a)| = |h(x) − h(a) − ⟨ν(a), x − a⟩| ≤ ε|x − a|, by (W) with base point a ∈ K and y = x (|x − a| < ρ < δ₁), trivially if x = a.
- If x ∈ U: apply (1g) at x₀ := x with q := h(a) + ⟨ν(a), x − a⟩. For i ∈ S, (E1) with b := p_i, y := x gives P_i(x) − q = [h(p_i) − h(a) − ⟨ν(a), p_i − a⟩] + ⟨ν(p_i) − ν(a), x − p_i⟩, whose absolute value is ≤ ε(C + 1)|x − a| + ε·C|x − a| = ε(2C + 1)|x − a| by (2b). As the weights φ_i(x), i ∈ S, are ≥ 0 with sum 1, |g(x) − g(a) − L_a(x − a)| ≤ ε(2C + 1)|x − a|.
So |g(x) − g(a) − L_a(x − a)| ≤ (2C + 1)ε|x − a| whenever |x − a| < ρ. Since ε > 0 is arbitrary and 2C + 1 is fixed, g(x) − g(a) − L_a(x − a) = o(|x − a|), i.e. HasFDerivAt g L_a a (HasFDerivAt.of_isLittleO with Asymptotics.IsLittleO.of_bound). In particular Dg(a)v = ⟨ν(a), v⟩ for all v.

4. Continuity of Dg at points of A. Fix a ∈ A and η > 0. Choose ε > 0 with ε(1 + (3C + 1)M) < η, and ρ as in step 2 for this ε. Let |x − a| < ρ.
- If x ∈ A: by step 3, Dg(x) − Dg(a) = L_x − L_a, of norm |ν(x) − ν(a)| ≤ ε < η, since |x − a| < ρ < τ.
- If x ∈ U: choose a* ∈ A with |x − a*| = d(x) (IsClosed.exists_infDist_eq_dist; ℝⁿ is proper). Then |a* − a| ≤ |a* − x| + |x − a| ≤ 2|x − a| < 2ρ ≤ min{1, δ₁, τ}, so a* ∈ K and |ν(a*) − ν(a)| ≤ ε. For i ∈ S (notation of (1f) at x₀ := x): by (2b), |ν(p_i) − ν(a)| ≤ ε, so |ν(p_i) − ν(a*)| ≤ 2ε; |x − p_i| ≤ C·d(x); and |p_i − a*| ≤ |p_i − x| + |x − a*| ≤ (C + 1)d(x) ≤ (C + 1)|x − a| < δ₁, so (W) with base point a* ∈ K and y = p_i gives |h(p_i) − h(a*) − ⟨ν(a*), p_i − a*⟩| ≤ ε|p_i − a*| ≤ ε(C + 1)d(x). With c := P*(x) := h(a*) + ⟨ν(a*), x − a*⟩, (E1) (with a := a*, b := p_i, y := x) yields |P_i(x) − c| ≤ ε(C + 1)d(x) + 2ε·C·d(x) = ε(3C + 1)d(x). Now (1g) at x₀ := x, (1f) and d(x) ≤ 1 (2a), d(x) > 0 give
‖Dg(x) − L_a‖ ≤ Σ_{i∈S} φ_i(x)|ν(p_i) − ν(a)| + Σ_{i∈S} |P_i(x) − c|·‖Dφ_i(x)‖ ≤ ε + ε(3C + 1)d(x)·Σ_{i∈s}‖Dφ_i(x)‖ ≤ ε + ε(3C + 1)d(x)·M/d(x) = ε(1 + (3C + 1)M) < η.
Since Dg(a) = L_a (step 3), ‖Dg(x) − Dg(a)‖ < η for all |x − a| < ρ; thus fderiv g is continuous at a.

5. Conclusion. g is differentiable at every point of U (1c) and of A (step 3), so g is differentiable on ℝⁿ; fderiv g is continuous at every point of U (1c) and of A (step 4), so fderiv g is continuous. By contDiff_one_iff_fderiv, g is C¹ (ContDiff ℝ 1 g). For x ∈ A and v ∈ ℝⁿ, step 3 gives fderiv ℝ g x v = L_x v = ⟨ν(x), v⟩. ∎

Remark for formalization. The pinned SimonGMT source Poincare/SimonGMT/Chapter02/WhitneyExtension.lean (with WhitneyJet.lean) carries out the same estimates for its specific Whitney cover: whitneyAffine_sub_eq is (E1), whitneyExtension_sub_affine_eq_near_sum and whitneyExtension_fderiv_sub_eq_near_sum are (1g), HasWhitneyC1Compatibility.hasFDerivAt_whitneyExtension is step 3, continuousAt_fderiv_whitneyExtension is step 4 and contDiff_whitneyExtension is step 5; norm_sum_smul_le_of_convex_weights handles the convex combinations. Its proofs transfer to the abstract hypotheses (P1)-(P7) by replacing nearFinset with the finite set S = {i ∈ s : φ_i(x) ≠ 0} of (1f) (s from (P4)), after dropping the indices of s with φ_i(x) = 0 by (1e) (zero weight and zero derivative); the anchor bound (P6) is only available on S. That module has no prebuilt .olean in the shared package tree and its imported Whitney modules are stale for Lake, so port the source into chapter-local modules instead of importing it.

## Key steps

1. Locally on U (finite s from (P4)): g = Σ_{i∈s} φ_i P_i is C¹, Σ_{i∈s} φ_i = 1, Σ_{i∈s} Dφ_i = 0, and Dφ_i(x) = 0 wherever φ_i(x) = 0 (local minimum of a nonnegative function).
2. Near a ∈ A: (W) on the compact K = A ∩ B̄(a,1) and continuity of ν at a, with ρ = min{1,δ₁,τ}/(C+2), control every anchor p_i with φ_i(x) ≠ 0, since |p_i − a| ≤ (C+1)|x − a|.
3. First-order estimate |g(x) − g(a) − ⟨ν(a), x − a⟩| ≤ (2C+1)ε|x − a| for |x − a| < ρ, hence HasFDerivAt g ⟨ν(a),·⟩ a.
4. Derivative estimate on U via a nearest point a*: ‖Dg(x) − ⟨ν(a),·⟩‖ ≤ ε(1 + (3C+1)M); on A, ‖Dg(x) − Dg(a)‖ = |ν(x) − ν(a)| ≤ ε; hence fderiv g is continuous at a.
5. contDiff_one_iff_fderiv gives ContDiff ℝ 1 g, and fderiv ℝ g x v = ⟨ν(x), v⟩ for x ∈ A.

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

Solution PR: https://github.com/ZhengyangZhang06/gmt-formalize/pull/1970

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
