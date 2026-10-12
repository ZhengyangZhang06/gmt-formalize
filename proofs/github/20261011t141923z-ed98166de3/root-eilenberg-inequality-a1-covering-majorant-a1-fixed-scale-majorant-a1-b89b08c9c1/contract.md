<!-- theorem-id: gmt-ch02/root.eilenberg_inequality-a1.covering_majorant-a1.fixed_scale_majorant-a1 -->

## Theorem `Submission.eilenberg_covering_fixed_scale_majorant`

Let X be a metric space with its Borel σ-algebra, m ∈ ℕ, k > 0 real, and E ⊆ X with μH[m+k](E) < ∞. Here μH is Mathlib's unnormalized Hausdorff measure, and E is arbitrary (not assumed measurable). Let K ∈ ℝ≥0, let f : X → ℝᵐ (= Rn m) be K-Lipschitz on E, and let r, ε ∈ (0,∞]. For F ⊆ X put pre^k_r(F) := inf { Σ_n [t_n ≠ ∅](ediam t_n)^k : t : ℕ → Set X, F ⊆ ⋃_n t_n, ediam t_n ≤ r for all n }, where [t ≠ ∅]x = x if t ≠ ∅ and 0 if t = ∅. Then there is a Borel measurable g : ℝᵐ → [0,∞] such that (ω_k/2^k)·pre^k_r(E ∩ f⁻¹{y}) ≤ g(y) for every y ∈ ℝᵐ, and ∫_{ℝᵐ} g dLᵐ ≤ (ω_m ω_k K^m / 2^{m+k})·(μH[m+k](E) + ε). Here ω_d = Chapter01.realUnitBallVolume d, 2^k and 2^{m+k} are real powers, and K^m is a natural power.

Node: `root.eilenberg_inequality-a1.covering_majorant-a1.fixed_scale_majorant-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/3

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/86

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/172

Decomposition children: None

## Lean problem

Declaration: `Submission.eilenberg_covering_fixed_scale_majorant`

```lean
∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (m : ℕ) (k : ℝ) (E : Set X) (f : X → Rn m) (K : ℝ≥0) (r ε : ℝ≥0∞), 0 < k → μH[(m : ℝ) + k] E < ⊤ → LipschitzOnWith K f E → 0 < r → 0 < ε → ∃ g : Rn m → ℝ≥0∞, Measurable g ∧ (∀ y, Chapter01.realUnitBallVolume k / (2 : ℝ≥0∞) ^ k * (⨅ (t : ℕ → Set X) (_ : E ∩ f ⁻¹' {y} ⊆ ⋃ n, t n) (_ : ∀ n, ediam (t n) ≤ r), ∑' n, ⨆ (_ : (t n).Nonempty), ediam (t n) ^ k) ≤ g y) ∧ ∫⁻ y, g y ∂volume ≤ Chapter01.realUnitBallVolume (m : ℝ) * Chapter01.realUnitBallVolume k * (K : ℝ≥0∞) ^ m / (2 : ℝ≥0∞) ^ ((m : ℝ) + k) * (μH[(m : ℝ) + k] E + ε)
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

- Parent DAG node: `root.eilenberg_inequality-a1.covering_majorant-a1`
- Child DAG node: `root.eilenberg_inequality-a1.covering_majorant-a1.fixed_scale_majorant-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. This is the fixed-scale part of the printed proof of Simon, Introduction to GMT, Ch. 2, Theorem 1.9 (pp. 45-46), in the completed form of the parent proof. It is the parent's steps 3-8, with the scale δ_i and slack ε_i replaced by arbitrary r, ε ∈ (0,∞].

Printed text (cleaned transcription), for a fixed i: 'pick closed subsets C_{i1}, C_{i2}, ... with diam C_{ij} < 1/i, A ⊆ ∪_j C_{ij} and (1) Σ_j ω_{m+k}(diam C_{ij}/2)^{m+k} ≤ H^{m+k}_{1/i}(A) + 1/i, and let g_i = Σ_j ω_k (diam C_{ij}/2)^k χ_{f(C_{ij})} ... (2) g_i(y) = Σ_{j : f⁻¹y ∩ C_{ij} ≠ ∅} ω_k(diam C_{ij}/2)^k ≥ H^k_{1/i}(A ∩ f⁻¹y) ... ∫ g_i dLᵐ = Σ_j ω_k (diam C_{ij}/2)^k Lᵐ(f(C_{ij})) ≤ Σ_j ω_k ω_m (Lip f)^m (diam C_{ij}/2)^{m+k} ≤ (ω_mω_k/ω_{m+k})(Lip f)^m (H^{m+k}_{1/i}(A) + 1/i)'.

Documented corrections carried over from the parent proof:
(a) f(C_{ij}) need not be Borel (X is not σ-compact here), so the indicator of the closed set closure f(C_{ij} ∩ E) is used; it has the same diameter.
(b) The covers come from Mathlib's formula `MeasureTheory.Measure.hausdorffMeasure_apply` for the unnormalized measure μH (diameters ≤ r, cost (ediam)^d). Simon's normalizations are carried as explicit constants c_k = ω_k/2^k and a = ω_mω_kK^m/2^{m+k}.

The isodiametric step is the sibling theorem `Submission.eilenberg_covering_lipschitz_image_volume_le`. No other erratum.

Conventions.
(C1) ediam = Mathlib `Metric.ediam` (ediam ∅ = 0). `LipschitzOnWith K f E` means edist (f x) (f x') ≤ K·edist x x' for x, x' ∈ E.
(C2) For d ∈ ℝ, ρ ∈ [0,∞] and F ⊆ X, pre^d_ρ(F) := ⨅ (t : ℕ → Set X) (_ : F ⊆ ⋃ n, t n) (_ : ∀ n, ediam (t n) ≤ ρ), ∑' n, ⨆ (_ : (t n).Nonempty), ediam (t n) ^ d. This is exactly the inner expression in `hausdorffMeasure_apply`: μH[d](F) = ⨆ (ρ : ℝ≥0∞) (_ : 0 < ρ), pre^d_ρ(F) for every F ⊆ X. The bracket ⨆ (_ : t.Nonempty), x equals x if t ≠ ∅ and 0 if t = ∅.
(C3) ω_d = Chapter01.realUnitBallVolume d, c_k := ω_k/2^k, s := (m:ℝ) + k, M := μH[s](E), and a := ω_m·ω_k·K^m/2^s.

To prove: g measurable, c_k·pre^k_r(E ∩ f⁻¹{y}) ≤ g(y) for all y, and ∫⁻ g dLᵐ ≤ a·(M + ε).

Proof.
1. (s > 0 and pre^s_r(E) ≤ M < ∞.) s = m + k > 0 because m ≥ 0 and k > 0. Since 0 < r, pre^s_r(E) is the term with index r in the supremum of `hausdorffMeasure_apply` for F = E. Hence pre^s_r(E) ≤ M (`le_iSup₂` at r and the proof of 0 < r), and since M < ∞, pre^s_r(E) ≠ ∞.
2. (Near-optimal cover.) As pre^s_r(E) ≠ ∞ and ε ≠ 0, pre^s_r(E) < pre^s_r(E) + ε (`ENNReal.lt_add_right`). Apply `iInf_lt_iff` three times: to the infimum over t, then over the proof of the covering property, then over the proof of the diameter bound. This yields C : ℕ → Set X with E ⊆ ⋃_l C_l, ediam C_l ≤ r for every l, and Σ'_l [C_l ≠ ∅](ediam C_l)^s < pre^s_r(E) + ε ≤ M + ε (by step 1).
3. (Trimmed pieces.) Put D_l := C_l ∩ E and d_l := ediam D_l. Since D_l ⊆ C_l, d_l ≤ ediam C_l ≤ r (`Metric.ediam_mono`).
   Claim: d_l^s ≤ [C_l ≠ ∅](ediam C_l)^s.
   - If D_l = ∅, then d_l = ediam ∅ = 0, and 0^s = 0 because s > 0 (`ENNReal.zero_rpow_of_pos`).
   - Otherwise C_l ⊇ D_l is nonempty, so the bracket is (ediam C_l)^s (`le_iSup` at the nonemptiness proof), and d_l^s ≤ (ediam C_l)^s because t ↦ t^s is monotone for s ≥ 0 (`ENNReal.rpow_le_rpow`).
   Summing over l (`ENNReal.tsum_le_tsum`) and using step 2 gives (★) Σ'_l d_l^s ≤ M + ε.
4. (Closed image sets and their volume.) Put T_l := closure (f '' D_l) ⊆ ℝᵐ; it is closed and hence Borel (`isClosed_closure.measurableSet`). Since D_l ⊆ E, f is K-Lipschitz on D_l (`LipschitzOnWith.mono`). The sibling theorem Submission.eilenberg_covering_lipschitz_image_volume_le, applied to X, m, D_l, f, K, gives Lᵐ(T_l) ≤ ω_m·K^m·d_l^m/2^m.
5. (The Borel function g.) Define g(y) := Σ'_l 1_{T_l}(y)·c_k·d_l^k, i.e. g = fun y ↦ ∑' l, Set.indicator (T l) (fun _ ↦ c_k * d_l ^ k) y. Each summand is a constant times the indicator of a measurable set, hence measurable (`measurable_const.indicator`). A countable sum of measurable [0,∞]-valued functions is measurable (`Measurable.ennreal_tsum`, deprecated but available; or `Measurable.tsum`). So g is measurable.
6. (Pointwise bound.) Fix y ∈ ℝᵐ, and put F_y := E ∩ f⁻¹{y} and t_l := D_l ∩ f⁻¹{y}.
   - (i) The t_l cover F_y: if x ∈ F_y, then x ∈ E ⊆ ⋃_l C_l, so x ∈ C_l for some l, and x ∈ C_l ∩ E ∩ f⁻¹{y} = t_l.
   - (ii) ediam t_l ≤ d_l ≤ r, because t_l ⊆ D_l.
   Using this admissible t in (C2) (`iInf₂_le_of_le` with t and the covering proof, then `iInf_le_of_le` with the diameter proof): pre^k_r(F_y) ≤ Σ'_l [t_l ≠ ∅](ediam t_l)^k.
   Multiply by c_k, which is monotone; in Lean use `gcongr c_k * ?_`, since a bare `gcongr` descends into the infimum. Moving c_k inside the sum (`ENNReal.tsum_mul_left`) gives c_k·pre^k_r(F_y) ≤ Σ'_l c_k·[t_l ≠ ∅](ediam t_l)^k.
   Termwise, c_k·[t_l ≠ ∅](ediam t_l)^k ≤ 1_{T_l}(y)·c_k·d_l^k:
   - If t_l ≠ ∅, choose x ∈ t_l. Then x ∈ D_l and f x = y, so y ∈ f '' D_l ⊆ T_l (`subset_closure`). The right side is c_k·d_l^k (`Set.indicator_of_mem`) and the left side is c_k·(ediam t_l)^k (`iSup_pos`). Finally (ediam t_l)^k ≤ d_l^k, since t ↦ t^k is monotone for k ≥ 0 (`ENNReal.rpow_le_rpow`).
   - If t_l = ∅, the left side is c_k·0 = 0 (`iSup_neg`).
   Summing (`ENNReal.tsum_le_tsum`) gives c_k·pre^k_r(E ∩ f⁻¹{y}) ≤ g(y).
7. (Exponent identity.) For every d ∈ [0,∞]: (ω_k/2^k)·d^k·(ω_m·K^m·d^m/2^m) = a·d^s. Proof:
   - Rewrite the natural powers d^m and 2^m as real powers d^(m:ℝ) and 2^(m:ℝ) (`ENNReal.rpow_natCast`, right to left).
   - Split d^((m:ℝ)+k) = d^(m:ℝ)·d^k (`ENNReal.rpow_add_of_nonneg`, using (m:ℝ) ≥ 0 and k ≥ 0). This is valid for every d, including 0 and ∞. Instantiate x := d explicitly.
   - Split 2^((m:ℝ)+k) = 2^(m:ℝ)·2^k (`ENNReal.rpow_add`, using 2 ≠ 0 and 2 ≠ ∞). Instantiate x := 2 explicitly; otherwise the rewrite may target d^((m:ℝ)+k) and demand d ≠ 0.
   - Write x/y = x·y⁻¹ (`div_eq_mul_inv`) and split (2^(m:ℝ)·2^k)⁻¹ = (2^(m:ℝ))⁻¹·(2^k)⁻¹ (`ENNReal.mul_inv`). This needs 2^(m:ℝ) ≠ 0 and 2^(m:ℝ) ≠ ∞, from `ENNReal.rpow_pos` and `ENNReal.rpow_ne_top_of_nonneg`.
   - Both sides are now equal as commutative-semiring expressions (`ring`).
8. (Integral bound.) By monotone convergence for series (`lintegral_tsum`; each summand is measurable, hence a.e.-measurable) and `lintegral_indicator_const` (T_l is measurable): ∫⁻ g dLᵐ = Σ'_l c_k·d_l^k·Lᵐ(T_l).
   By step 4 and monotonicity of multiplication, c_k·d_l^k·Lᵐ(T_l) ≤ c_k·d_l^k·(ω_m·K^m·d_l^m/2^m), which equals a·d_l^s by step 7.
   Summing (`ENNReal.tsum_le_tsum`) and factoring out a (`ENNReal.tsum_mul_left`) gives ∫⁻ g dLᵐ ≤ a·Σ'_l d_l^s. By (★) and monotonicity of multiplication by a, this is ≤ a·(M + ε).
9. (Conclusion.) g is measurable (step 5), satisfies the pointwise bound (step 6), and satisfies the integral bound (step 8). The argument is uniform in m ∈ ℕ (m = 0 included), K ≥ 0 (K = 0 included) and r, ε ∈ (0,∞]. No finiteness of r, ε or d_l is used, since all identities hold in [0,∞]. ∎

## Key steps

1. pre^{m+k}_r(E) ≤ μH[m+k](E) < ∞ (hausdorffMeasure_apply, le_iSup₂). Hence, by ENNReal.lt_add_right and iInf_lt_iff three times, there is a cover C_l of E with ediam C_l ≤ r and Σ[C_l≠∅](ediam C_l)^{m+k} < pre + ε ≤ μH[m+k](E) + ε.
2. The trimmed diameters d_l = ediam(C_l ∩ E) satisfy d_l ≤ r and Σ_l d_l^{m+k} ≤ μH[m+k](E) + ε, using m+k > 0 for the empty pieces.
3. T_l = closure f(C_l ∩ E) is closed, and by the sibling isodiametric bound Lᵐ(T_l) ≤ ω_m K^m d_l^m / 2^m.
4. g = Σ_l (ω_k/2^k) d_l^k 1_{T_l} is Borel and dominates (ω_k/2^k)·pre^k_r(E ∩ f⁻¹{y}), via the admissible cover C_l ∩ E ∩ f⁻¹{y}.
5. ∫ g = Σ_l (ω_k/2^k) d_l^k Lᵐ(T_l) ≤ Σ_l a d_l^{m+k} ≤ a(μH[m+k](E) + ε), using d^k d^m = d^{m+k} and 2^k 2^m = 2^{m+k} with a = ω_mω_kK^m/2^{m+k}.

## Reference use

### local-project

Queries:
- `cat local-references/ff09f3909baeeae7/manifest.json (mode local-project, project 1b1689a8deba89d58b36b1a04dba493693824437, mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/ff09f3909baeeae7/project/GMT/Ch02/{Contract,Submission}.lean against workspace GMT/Ch02/{Contract,Submission}.lean (identical)`
- `sed -n 530,600p mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean (hausdorffMeasure_apply, hausdorffMeasure_le_liminf_tsum)`
- `grep -n 'def ediam|theorem ediam_closure|theorem ediam_le|theorem ediam_mono|theorem ediam_empty|theorem ediam_image_le' -r mathlib/Mathlib/Topology; sed -n 1,60p mathlib/Mathlib/Topology/EMetricSpace/Diam.lean`
- `grep -rn -E 'theorem lintegral_liminf_le|theorem Measurable.liminf|theorem lintegral_tsum|theorem lintegral_indicator_const|theorem Measurable.ennreal_tsum|theorem rpow_add_of_nonneg|theorem rpow_add|theorem rpow_natCast|theorem tendsto_inv_nat_nhds_zero|theorem Tendsto.const_mul|theorem tsum_mul_left|theorem lintegral_const_mul|theorem Measurable.indicator|theorem lt_add_right|theorem mul_rpow_of_nonneg|theorem div_rpow_of_nonneg|theorem rpow_le_rpow|theorem zero_rpow_of_pos' mathlib/Mathlib`
- `grep -rn -E '(theorem|lemma) .*(Tendsto.liminf_eq|mul_iSup|le_liminf_of_le|liminf_le_liminf|iInf_lt_iff|div_pow|tsum_le_tsum)' mathlib/Mathlib`
- `grep -n 'def simonHausdorffMeasureReal|def realUnitBallVolume|theorem realUnitBallVolume_pos|theorem realUnitBallVolume_ne_top' -A6 lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `sed -n 1,60p lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/EuclideanNormalization.lean (simon_theorem_2_10)`
- `rg -n -i 'eilenberg|covering_majorant|liminf_majorant|fixed_scale' local-references/ff09f3909baeeae7/project; rg -n -i 'eilenberg' lake-packages-25730c7c/simongmt/Poincare/SimonGMT; rg -n -i 'theorem .*(lipschitz.*volume|volume.*lipschitz|image_volume)' mathlib/Mathlib lake-packages-25730c7c/simongmt/Poincare/SimonGMT`
- `find lake-packages-25730c7c/simongmt -name 'UpperIntegral*'; rg -n 'exists_measurableMajorant|upperLebesgueIntegral' lake-packages-25730c7c/simongmt/Poincare`
- `lean checks/Names.lean: #check of 54 API names (hausdorffMeasure_apply, Metric.ediam_*, simon_theorem_2_10, lintegral_liminf_le, Measurable.liminf, ENNReal.rpow_add(_of_nonneg), Filter.Tendsto.liminf_eq, ENNReal.mul_iSup, iInf_lt_iff, ...) against a scratch olean of GMT.Ch02.Submission built with plain lean -o (no lake build)`
- `python3 -I scripts/gen_challenge.py (imports verifier/gmt-compare.py child_modules/contract_scope and lean_contract.validate_lean_statement) then lean checks/final/NodeChallenge_00..02.lean`
- `lean checks/AssemblyCheck2.lean (parent frozen type from the child types as hypotheses) + #print axioms`
- `lean checks/ChildA.lean, checks/ChildC.lean (outright proofs), checks/ChildB.lean (B from A), checks/FullCheck.lean; lean -o of sim/GMT/Ch02/Submission.lean containing the children, then lean simsol/NodeSolution_00..03.lean + #print axioms`
- `python3 -I: collect all lean_name values in dag.json and nodes/*/*.json`
- `sed -n 240,600p verifier/gmt-compare.py (candidate_inputs/frozen_inputs: Submission.lean not byte-checked; new Lean files allowed only under GMT/Ch02/)`
- `grep -n '1.9|Eilenberg|isodiametric' book/chapter-02.txt; sed -n 330,425p book/chapter-02.txt`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/EMetricSpace/Diam.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Basic/ENNReal/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/EuclideanNormalization.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/UpperIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-eilenberg-inequality-a1-covering-majorant-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/covmaj-decomp-jd8mrR/checks/Names.lean`
- `/tmp/covmaj-decomp-jd8mrR/checks/final/NodeChallenge_00.lean`
- `/tmp/covmaj-decomp-jd8mrR/checks/final/NodeChallenge_01.lean`
- `/tmp/covmaj-decomp-jd8mrR/checks/final/NodeChallenge_02.lean`
- `/tmp/covmaj-decomp-jd8mrR/checks/AssemblyCheck2.lean`
- `/tmp/covmaj-decomp-jd8mrR/checks/ChildA.lean`
- `/tmp/covmaj-decomp-jd8mrR/checks/ChildB.lean`
- `/tmp/covmaj-decomp-jd8mrR/checks/ChildC.lean`
- `/tmp/covmaj-decomp-jd8mrR/checks/FullCheck.lean`
- `/tmp/covmaj-decomp-jd8mrR/sim/GMT/Ch02/Submission.lean`
- `/tmp/covmaj-decomp-jd8mrR/simsol/NodeSolution_00.lean`
- `/tmp/covmaj-decomp-jd8mrR/simsol/NodeSolution_01.lean`
- `/tmp/covmaj-decomp-jd8mrR/simsol/NodeSolution_02.lean`
- `/tmp/covmaj-decomp-jd8mrR/simsol/NodeSolution_03.lean`

**No existing result.**
- The snapshot project (identical to the workspace Contract/Submission) contains only the frozen definition EilenbergInequality (Contract.lean:232) and README row 6.
- SimonGMT has no Eilenberg, covering-majorant or fixed-scale lemma.
- No Lipschitz-image Lebesgue-volume lemma exists; the only lipschitz/volume matches are area-formula results in Chapter02/AreaLiteral.lean.
- Chapter02/UpperIntegral.lean (upperLebesgueIntegral) is not needed, because correction (b) uses an explicit liminf majorant.

**Mathlib API, all #check-ed in the pinned environment.**
- Hausdorff measure: Measure.hausdorffMeasure_apply (Hausdorff.lean:546; covers with ediam ≤ r, Nonempty-weighted cost).
- Diameters: Metric.ediam_le, Metric.ediam_mono, Metric.edist_le_ediam_of_mem (EMetricSpace/Diam.lean); Metric.ediam_closure (Instances/ENNReal/Lemmas.lean:649).
- Lebesgue integral: lintegral_liminf_le (Lebesgue/Add.lean:233), lintegral_tsum (Add.lean:362), lintegral_indicator_const (Basic.lean:541).
- Measurability: Measurable.liminf (BorelSpace/Order.lean:1058); Measurable.ennreal_tsum (deprecated but available, BorelSpace/Real.lean:354).
- ENNReal powers: ENNReal.rpow_add_of_nonneg (Pow/NNReal.lean:633), ENNReal.rpow_add (:626), ENNReal.rpow_natCast (:686), ENNReal.inv_pow, ENNReal.mul_inv.
- ENNReal sums and limits: ENNReal.mul_iSup, ENNReal.tsum_mul_left, ENNReal.tsum_le_tsum, ENNReal.lt_add_right, ENNReal.tendsto_inv_nat_nhds_zero (ENNReal/Lemmas.lean:486), ENNReal.Tendsto.const_mul (:354).
- Order and filters: Filter.Tendsto.liminf_eq (Order/LiminfLimsup.lean:195), Filter.le_liminf_of_le, Filter.liminf_le_liminf, Filter.Tendsto.eventually_le_const, iInf_lt_iff, iInf₂_le_of_le.
- Not available in this Mathlib: ENNReal.div_pow, LipschitzOnWith.edist_le_mul, mul_le_mul_left' (use gcongr). A bare gcongr descends into the infimum, so use gcongr c * ?_.

**SimonGMT (pinned package).**
- simonHausdorffMeasureReal s = (realUnitBallVolume s / 2^s) • μH[s] (Chapter01/Hausdorff.lean:283).
- realUnitBallVolume_pos and realUnitBallVolume_ne_top (:499, :506).
- simon_theorem_2_10, the isodiametric inequality for every n and every set (EuclideanNormalization.lean:24), is not imported by the contract. Adding the import to Submission.lean is allowed: the verifier does not byte-check Submission.lean.

**Contract scope.** The comparator replays the bare `end` that closes the noncomputable section, so the 𝓗[·]/ω[·] local notations are unavailable. The child statements therefore spell out Chapter01.* and μH[·], with open MeasureTheory Metric Set Filter Topology, ENNReal, NNReal and Poincare.SimonGMT in scope.

**Lean verification.**
- All three child lean_statements elaborate in the replayed scope.
- The parent frozen type follows from the fixed-scale and liminf child types with axioms [propext, Classical.choice, Quot.sound].
- The isodiametric and liminf children were proved outright, and the fixed-scale child from the isodiametric one, with standard axioms.
- Comparator-style NodeSolution modules pass for all three children and the parent against a simulated Submission.

**Name collisions.** dag.json and the node files reserve only the existing depth-1/2 names (including eilenberg_compact_exhaustion, eilenberg_compact_fiber_measurable, eilenberg_covering_majorant, eilenberg_inequality_theorem); the three new eilenberg_covering_* names are free.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: https://github.com/ZhengyangZhang06/gmt-formalize/pull/759

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
