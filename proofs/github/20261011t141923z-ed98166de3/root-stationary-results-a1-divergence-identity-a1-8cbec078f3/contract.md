<!-- theorem-id: gmt-ch02/root.stationary_results-a1.divergence_identity-a1 -->

## Theorem `Submission.submanifold_divergence_identity_compact`

Assume (TH). (TH) is the frozen statement of the sibling root.submanifold_tangent-a1, taken as an explicit hypothesis: (TH1) for every Simon local representation (V, W, ψ) of class r ≥ 1 of any M ⊆ ℝᴺ, tangentSpace M (ψ x) = range Dψ(x) for x ∈ V; (TH2) every n-dimensional C^r Simon submanifold of ℝᴺ is a measurable set on which y ↦ tangentProjection M y is continuous. Let M ⊆ ℝᴺ be an n-dimensional C² Simon submanifold, Y : ℝᴺ → ℝᴺ of class C¹, and S ⊆ ℝᴺ closed with Y(x) = 0 for x ∉ S and M ∩ S compact. Then y ↦ tangentialDivergence M Y y and y ↦ ⟨Y(y), meanCurvature M y⟩ are integrable on M with respect to μHE[n], and ∫_M tangentialDivergence M Y dμHE[n] = −∫_M ⟨Y, meanCurvature M⟩ dμHE[n].

Node: `root.stationary_results-a1.divergence_identity-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/3

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/42

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/236, https://github.com/ZhengyangZhang06/gmt-formalize/issues/241, https://github.com/ZhengyangZhang06/gmt-formalize/issues/242

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/593, https://github.com/ZhengyangZhang06/gmt-formalize/issues/594, https://github.com/ZhengyangZhang06/gmt-formalize/issues/596, https://github.com/ZhengyangZhang06/gmt-formalize/issues/597, https://github.com/ZhengyangZhang06/gmt-formalize/issues/598

## Lean problem

Declaration: `Submission.submanifold_divergence_identity_compact`

```lean
((∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)) (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N), 1 ≤ r → Chapter02.IsSimonLocalRepresentation r M V W ψ → ∀ x ∈ V, tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap) ∧ ∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)), Chapter02.IsSimonSubmanifold (E := Rn n) r M → MeasurableSet M ∧ ContinuousOn (tangentProjection M) M) → ∀ (n N : ℕ) (M S : Set (Rn N)) (Y : Rn N → Rn N), Chapter02.IsSimonSubmanifold (E := Rn n) 2 M → ContDiff ℝ 1 Y → IsClosed S → (∀ x ∉ S, Y x = 0) → IsCompact (M ∩ S) → IntegrableOn (tangentialDivergence M Y) M μHE[n] ∧ IntegrableOn (fun y ↦ inner ℝ (Y y) (meanCurvature M y)) M μHE[n] ∧ ∫ y in M, tangentialDivergence M Y y ∂μHE[n] = -∫ y in M, inner ℝ (Y y) (meanCurvature M y) ∂μHE[n]
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

- Parent DAG node: `root.stationary_results-a1`
- Child DAG node: `root.stationary_results-a1.divergence_identity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

(TH) denotes the frozen statement of the sibling node root.submanifold_tangent-a1 (Submission.simon_submanifold_tangent_basics), taken here as an explicit hypothesis: (TH1) for all n, N, r ≥ 1, M ⊆ ℝᴺ and every Simon local representation (V, W, ψ) of M of class r, tangentSpace M (ψ x) = range Dψ(x) for every x ∈ V; (TH2) every n-dimensional C^r Simon submanifold M of ℝᴺ is a measurable set and y ↦ tangentProjection M y is continuous on M.
Notation. ℝ^d := EuclideanSpace ℝ (Fin d) (= Rn d); Hⁿ := μHE[n]. A chart of class r of M is a triple (V, W, ψ) with Chapter02.IsSimonLocalRepresentation r M V W ψ: V ⊆ ℝⁿ and W ⊆ ℝᴺ open, ψ C^r on V, ψ injective on V, ψ(V) = W ∩ M, ψ relatively proper (V ∩ ψ⁻¹(K) is compact for every compact K ⊆ W) and Dψ(x) injective for x ∈ V. For y ∈ M: T_y := tangentSpace M y, P_y := tangentProjection M y (orthogonal projection onto T_y), v^⊥ := normalPart M y v = v − P_y v, τ_i := tangentFrame M y i (an orthonormal basis of T_y), B_y(τ, η) := secondFundamentalForm M y τ η = (fderivWithin ℝ (tangentProjection M) M y τ) η, H(y) := meanCurvature M y = Σ_i B_y(τ_i, τ_i), div_M Y(y) := tangentialDivergence M Y y = Σ_i ⟨τ_i, DY(y)τ_i⟩, and D²ψ(x)[a, b] := fderiv ℝ (fderiv ℝ ψ) x a b (the derivative at x in direction a of x′ ↦ Dψ(x′)b).

Source: Simon, Ch. 2, 4.21-4.22(*) and 4.29-4.30 (pp. 59-61). Printed: "Nevertheless in the general case we still have (in place of 4.21) (*) ∫_M div_M X = 0 provided support X ∩ M is a compact subset of M and X_y ∈ T_yM ∀ y ∈ M" (stated without proof); "decompose X into its tangent and normal parts X = X^T + X^⊥ ... div_M X^⊥ = Σ_α (ν^α · X) div_M ν^α, so that by 4.28 (4.29) div_M X^⊥ = −X · H ... Hence (4.30) ∫_M div_M X dHⁿ = −∫_M X · H dHⁿ − ∫_{∂M} X · η dH^{n−1}". The boundaryless, compact-support version is proved here (parent proof II.1, Claim D), using the local identity of the sibling chart_divergence in place of the splitting X = X^T + X^⊥.

Setting. Assume (TH) [(TH1): T_{ψ(x)} = range Dψ(x) for charts; (TH2): every C^r Simon submanifold is measurable and y ↦ P_y is continuous on it]. M is an n-dimensional C² Simon submanifold of ℝᴺ, Y : ℝᴺ → ℝᴺ is C¹, S ⊆ ℝᴺ is closed, Y = 0 off S, and M ∩ S is compact. Hⁿ := μHE[n]; div_M Ỹ := tangentialDivergence M Ỹ; H := meanCurvature M.

0. (Preliminary facts.)
 (a) M is measurable and y ↦ P_y is continuous on M (TH2); H is continuous on M (sibling sff_properties, second conjunct).
 (b) For y ∈ M and every linear L of ℝᴺ, Σ_i ⟨τ_i, L τ_i⟩ = trace(L ∘ P_y) for every orthonormal basis (τ_i) of T_y (SimonGMT submanifoldDivergenceAt_eq_sum_inner with the basis tangentFrame M y). Hence for every C¹ field Ỹ, div_M Ỹ(y) = trace(DỸ(y) ∘ P_y) for y ∈ M, a continuous function of y on M (DỸ continuous, P continuous on M, composition and trace continuous). Also div_M(Ỹ₁ + Ỹ₂)(y) = div_M Ỹ₁(y) + div_M Ỹ₂(y) when Ỹ₁, Ỹ₂ are differentiable at y (fderiv_add), and similarly for finite sums.
 (c) If a C¹ field Ỹ vanishes outside a closed set F and y ∉ F, then Ỹ ≡ 0 on the open neighbourhood Fᶜ of y, so Ỹ(y) = 0, DỸ(y) = 0, div_M Ỹ(y) = 0 and ⟨Ỹ(y), H(y)⟩ = 0.
 (d) If F is such that M ∩ F is compact, then Hⁿ(M ∩ F) < ∞ (sibling measure_bounds, part (a)).
1. (Integrability.) Let Ỹ be C¹ and F closed with Ỹ = 0 off F and M ∩ F compact. Then f₁ := div_M Ỹ and f₂ := ⟨Ỹ, H⟩ are continuous on M (0(a), 0(b)), vanish on M ∖ F (0(c)), and are bounded on the compact set M ∩ F (IsCompact.exists_bound_of_continuousOn), so |f_i| ≤ C · 1_{M∩F} on M. Each f_i is a.e.-strongly measurable for Hⁿ restricted to M (ContinuousOn.aestronglyMeasurable on the measurable set M), and ∫_M |f_i| dHⁿ ≤ C · Hⁿ(M ∩ F) < ∞ (0(d)). Hence f₁ and f₂ are integrable on M. With Ỹ := Y and F := S this proves the first two conjuncts.
2. (Localized identity.) Let (V, W, ψ) be a chart of M of class 2 and ζ : ℝᴺ → ℝ a C^∞ function with compact support and K_ζ := tsupport ζ ⊆ W. Put Ỹ := ζ Y (C¹) and f := div_M Ỹ + ⟨Ỹ, H⟩. Claim: ∫_M f dHⁿ = 0.
 2a. Ỹ vanishes off the closed set K_ζ, and M ∩ K_ζ = ψ(V ∩ ψ⁻¹(K_ζ)) is compact (relative properness, continuity of ψ on V, K_ζ ⊆ W and W ∩ M = ψ(V)). By step 1, f is integrable on M; by 0(c), f = 0 on M ∖ K_ζ ⊇ M ∖ ψ(V) (because M ∖ ψ(V) = M ∖ W). Since M is measurable (TH2), ψ(V) = W ∩ M ⊆ M is measurable, and f = 0 on M ∖ ψ(V), ∫_M f = ∫_{ψ(V)} f (MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero with t := M, s := ψ(V)).
 2b. (Area formula.) By SimonGMT integral_area_formula_of_injective_derivative (s := V measurable; ψ differentiable at every x ∈ V; Dψ(x) injective; ψ injective on V) and finrank ℝ ℝⁿ = n: ∫_{ψ(V)} f dHⁿ = ∫_V Jψ(x) · f(ψ(x)) dHⁿ(x), where Jψ = areaJacobianAt ψ and μHE[n] on ℝⁿ is an additive Haar measure (it equals Lebesgue measure, EuclideanSpace.euclideanHausdorffMeasure_eq_volume).
 2c. By the sibling chart_divergence applied to Ỹ, there is w̃, C¹ on V, with w̃(x) = 0 whenever x ∈ V and Ỹ(ψ(x)) = 0, and trace Dw̃(x) = Jψ(x) · f(ψ(x)) for x ∈ V. Let Q := V ∩ ψ⁻¹(K_ζ), compact by relative properness. For x ∈ V ∖ Q, ψ(x) ∉ K_ζ, so Ỹ(ψ(x)) = 0 and w̃(x) = 0. Define w̄ := w̃ on V and w̄ := 0 off V. Then w̄ = w̃ on the open set V and w̄ = 0 on the open set Qᶜ (Q is closed), and V ∪ Qᶜ = ℝⁿ. Hence w̄ is C¹ on ℝⁿ with tsupport w̄ ⊆ Q compact, Dw̄ = Dw̃ on V and Dw̄ = 0 on Qᶜ ⊇ ℝⁿ ∖ V. Therefore ∫_V Jψ · (f ∘ ψ) = ∫_V trace Dw̃ = ∫_{ℝⁿ} trace Dw̄ (the last integrand vanishes off V; all integrands involved are continuous with compact support, hence integrable).
 2d. trace Dw̄(x) = Σ_{j=1}^n ⟨e_j, Dw̄(x) e_j⟩ = Σ_j Dw̄_j(x) e_j with w̄_j := ⟨e_j, w̄⟩ ∈ C¹_c(ℝⁿ) (LinearMap.trace_eq_sum_inner with the standard orthonormal basis e_j). For each j, ∫ Dw̄_j(x) e_j dx = 0: apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable with the constant function 1, g := w̄_j and v := e_j, which gives ∫ 1 · Dw̄_j(x) e_j = −∫ D1(x) e_j · w̄_j(x) = 0 (the integrability hypotheses hold because w̄_j and x ↦ Dw̄_j(x) e_j are continuous with compact support); equivalently, use Fubini and the fundamental theorem of calculus on lines parallel to e_j. Hence ∫_{ℝⁿ} trace Dw̄ = 0, and by 2a-2c, ∫_M f dHⁿ = 0.
3. (Partition of unity.) If M ∩ S = ∅, then by 0(c) div_M Y = 0 and ⟨Y, H⟩ = 0 on M, and the identity reads 0 = −0. Assume M ∩ S ≠ ∅.
 3a. For each y ∈ M ∩ S choose a chart (V_y, W_y, ψ_y) of class 2 with y ∈ W_y and ρ_y > 0 with B̄(y, 2ρ_y) ⊆ W_y. By compactness choose y_1, …, y_p ∈ M ∩ S with M ∩ S ⊆ O′ := ⋃_q B(y_q, ρ_q).
 3b. For each q let β_q : ℝᴺ → [0, 1] be C^∞ with β_q = 1 on B̄(y_q, ρ_q) and tsupport β_q = B̄(y_q, 2ρ_q) (ContDiffBump centred at y_q with rIn = ρ_q, rOut = 2ρ_q; ContDiffBump.one_of_mem_closedBall, ContDiffBump.tsupport_eq). Put ζ_q := β_q · ∏_{l<q} (1 − β_l). Each ζ_q is C^∞ with tsupport ζ_q ⊆ tsupport β_q ⊆ W_{y_q}, compact. By induction on m, Σ_{q≤m} ζ_q = 1 − ∏_{q≤m} (1 − β_q); hence Σ_q ζ_q = 1 on O′ (on B(y_q, ρ_q) the factor 1 − β_q vanishes).
 3c. For every y ∈ M, Y = Σ_q ζ_q Y on a neighbourhood of y: if y ∈ S, then y ∈ M ∩ S ⊆ O′, which is open and on which Σ_q ζ_q = 1; if y ∉ S, both sides vanish on the open set Sᶜ. Therefore (Filter.EventuallyEq.fderiv_eq) DY(y) = Σ_q D(ζ_q Y)(y), so div_M Y(y) = Σ_q div_M(ζ_q Y)(y) by 0(b), and ⟨Y(y), H(y)⟩ = Σ_q ⟨ζ_q(y) Y(y), H(y)⟩.
 3d. For each q, ζ_q Y is C¹ and vanishes off the compact set tsupport ζ_q ⊆ W_{y_q}, a chart target; by step 1 (with F := tsupport ζ_q, M ∩ F compact by 2a) div_M(ζ_q Y) and ⟨ζ_q Y, H⟩ are integrable on M, and by step 2, ∫_M (div_M(ζ_q Y) + ⟨ζ_q Y, H⟩) dHⁿ = 0. Using 3c on the measurable set M (setIntegral_congr_fun), linearity of the integral for these finitely many integrable functions, and step 1 for Y itself: ∫_M div_M Y + ∫_M ⟨Y, H⟩ = Σ_q ∫_M (div_M(ζ_q Y) + ⟨ζ_q Y, H⟩) = 0.
4. Hence ∫_M div_M Y dHⁿ = −∫_M ⟨Y, H⟩ dHⁿ, the third conjunct; together with step 1 the theorem is proved.

## Key steps

1. div_M Ỹ = trace(DỸ ∘ P) and ⟨Ỹ, H⟩ are continuous on M (TH2, sff_properties), vanish off F, are bounded on the compact M ∩ F, and Hⁿ(M ∩ F) < ∞ (measure_bounds): integrable.
2. For ζ ∈ C_c^∞ with tsupport ζ inside a chart target: ∫_M (div_M ζY + ⟨ζY,H⟩) = ∫_V Jψ·(…)∘ψ (area formula) = ∫_V trace Dw̃ (chart_divergence) = ∫_{ℝⁿ} trace Dw̄ = 0 (extension by zero, ∫ of partial derivatives of C¹_c functions vanishes).
3. Partition of unity ζ_q = β_q∏_{l<q}(1−β_l) subordinate to chart targets with Σζ_q = 1 on a neighbourhood of M ∩ S; Y = Σζ_qY near every point of M.
4. Summing the localized identities gives ∫_M div_M Y = −∫_M ⟨Y,H⟩.

## Reference use

### local-project

Queries:
- `cat -n GMT/Ch02/Contract.lean; diff GMT/Ch02/Contract.lean GMT/Ch02/Submission.lean; cat GMT/Ch02/README.md`
- `grep -rn "μHE\[" mathlib/Mathlib --include=*.lean | grep -E "notation|def "; sed -n 1,140p mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `cat -n simongmt/Poincare/SimonGMT/Chapter02/{Submanifold,SubmanifoldCalculus,SecondFundamentalForm,SecondFundamentalFormCalculus,SubmanifoldIntegral,SubmanifoldTopology,WeightedArea,Area}.lean; grep -n 'injective_area_formula_of_injective_derivative' AreaFormula.lean`
- `grep -rn "theorem ContDiffAt.isSymmSndFDerivAt\|theorem HasFDerivWithinAt.unique_on\|theorem ContDiffAt.to_localInverse\|theorem LipschitzOnWith.hausdorffMeasure_image_le\|theorem HasCompactSupport.fderiv\|theorem finrank_euclideanSpace_fin" mathlib/Mathlib`
- `grep -rn tangentConeAt mathlib/Mathlib --include=*.lean | grep -E "theorem|lemma" | grep -iE "deriv|curve|segment|mem_tangentCone"; grep -rn mapsTo_tangent mathlib/Mathlib`
- `grep -rn "integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable\|integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable" mathlib/Mathlib; grep -n "theorem\|lemma" mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `grep -rn "Submission\.\|stationary_imp_mean_curvature_zero\|second_fundamental_form_chart_formula\|submanifold_divergence_identity_compact\|deformation_velocity_acceleration_regularity" project simongmt/Poincare; python3 -I lean_name collision check against dag.json`
- `python3 -I gen_checks.py (replays verifier gmt-compare.py contract_scope/child_modules and lean_contract.validate_lean_statement for the 10 lean_statements); lake build GMT.Ch02.Submission; lake env lean NodeChallenge_00..09.lean; lake env lean AssemblyCheck.lean`
- `lake env lean LibCheck.lean: #print axioms Poincare.SimonGMT.Chapter02.{integral_area_formula_of_injective_derivative, IsSimonLocalRepresentation.area_formula, IsSimonLocalRepresentation.weighted_area_formula, IsSimonLocalRepresentation.exists_open_image_eq_inter, IsSimonLocalRepresentation.isEmbedding_chartMap, submanifoldDivergenceAt_eq_sum_inner, measurable_areaJacobianAt}; #check of every cited Mathlib lemma`
- `sed -n 1030,1420p book/chapter-02.txt (printed 4.18-5.12); read dag.json and nodes/root-stationary-results-a1/parent-child-handoff.json`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Equiv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/TangentCone/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Submanifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SecondFundamentalForm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SecondFundamentalFormCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldTopology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaFormula.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-stationary-results-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/stat-decomp2/AssemblyCheck.lean`

The frozen contract (Contract.lean lines 83-176 and 297-342) defines the key notions:
- B is fderivWithin of tangentProjection;
- H is the frame trace;
- IsStationaryIn is defined variationally.

Collision checks: the snapshot project has no Submission.* declarations and no declaration with any of the ten proposed names, and dag.json (50 nodes) has no lean_name collision.

SimonGMT supplies kernel-checked tools used by the children:
- WeightedArea.lean: integral_area_formula_of_injective_derivative and IsSimonLocalRepresentation.area_formula;
- SubmanifoldTopology.lean: IsSimonLocalRepresentation.exists_open_image_eq_inter and isEmbedding_chartMap;
- SubmanifoldCalculus.lean: submanifoldDivergenceAt_eq_sum_inner;
- measurable_areaJacobianAt.
#print axioms shows only propext, Classical.choice and Quot.sound for all of them.

SimonGMT has no divergence theorem on submanifolds (integral_submanifoldDivergence_eq_curvature_sub_boundary takes it as a hypothesis), no chart formula for the frame-free B, and nothing on admissible deformations. These are therefore genuine new obligations.

Mathlib 25730c7c supplies ContDiffAt.isSymmSndFDerivAt, HasFDerivWithinAt.unique_on, HasFDerivWithinAt.mapsTo_tangent_cone, tangentConeAt_mono, tangentConeAt_of_mem_nhds, ContDiffAt.toOpenPartialHomeomorph, ContDiffAt.to_localInverse, OpenPartialHomeomorph.contDiffAt_symm, integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable, LinearMap.normDet_ne_zero_tfae, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, LipschitzOnWith.hausdorffMeasure_image_le, ContractingWith.fixedPoint, HasCompactSupport.fderiv and ContDiffBump. exists_smooth_tsupport_subset does not exist, so it is not cited. setIntegral_eq_of_subset_of_forall_diff_eq_zero is deprecated, so the _sdiff_ name is cited.

Compile checks:
- All ten lean_statements pass the workflow validator and elaborate in the comparator-replayed contract scope; NodeChallenge_00..09 compiled with only sorry warnings.
- AssemblyCheck.lean proves the frozen parent type StationaryIffMeanCurvatureZero ∧ SecondVariationStationary from the children and the sibling types. Its axioms are sorryAx from the stubs plus propext, Classical.choice and Quot.sound.
- Glue examples that instantiate the children as their proofs use them also compile.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: https://github.com/ZhengyangZhang06/gmt-formalize/pull/2927

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
