<!-- theorem-id: gmt-ch02/root.eilenberg_inequality-a1.covering_majorant-a1 -->

## Theorem `Submission.eilenberg_covering_majorant`

Let X be a metric space with its Borel σ-algebra (no σ-compactness, no measurability of E), m ∈ ℕ, k > 0 real, E ⊆ X with 𝓗^{m+k}(E) < ∞ (Simon-normalized 𝓗^s = (ω_s/2^s)μH[s] = Chapter01.simonHausdorffMeasureReal s, ω_s = Chapter01.realUnitBallVolume s), K ∈ ℝ≥0 and f : X → ℝᵐ K-Lipschitz on E. Then there is a Borel measurable G : ℝᵐ → [0,∞] with 𝓗^k(E ∩ f⁻¹{y}) ≤ G(y) for every y ∈ ℝᵐ and ∫_{ℝᵐ} G dLᵐ ≤ (ω_m ω_k/ω_{m+k}) K^m 𝓗^{m+k}(E).

Node: `root.eilenberg_inequality-a1.covering_majorant-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/3

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/37

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/172, https://github.com/ZhengyangZhang06/gmt-formalize/issues/174, https://github.com/ZhengyangZhang06/gmt-formalize/issues/175

## Lean problem

Declaration: `Submission.eilenberg_covering_majorant`

```lean
∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (m : ℕ) (k : ℝ) (E : Set X) (f : X → Rn m) (K : ℝ≥0), 0 < k → Chapter01.simonHausdorffMeasureReal (m + k) E < ⊤ → LipschitzOnWith K f E → ∃ G : Rn m → ℝ≥0∞, Measurable G ∧ (∀ y, Chapter01.simonHausdorffMeasureReal k (E ∩ f ⁻¹' {y}) ≤ G y) ∧ ∫⁻ y, G y ∂volume ≤ Chapter01.realUnitBallVolume (m : ℝ) * Chapter01.realUnitBallVolume k / Chapter01.realUnitBallVolume (m + k) * (K : ℝ≥0∞) ^ m * Chapter01.simonHausdorffMeasureReal (m + k) E
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

- Parent DAG node: `root.eilenberg_inequality-a1`
- Child DAG node: `root.eilenberg_inequality-a1.covering_majorant-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. This is the covering half of the printed proof of Simon, Introduction to GMT, Ch. 2, Theorem 1.9 (pp. 45-46), in the completed form of the parent proof (Part II, Step 1, items 1-6). Printed text (cleaned transcription): 'For each i = 1, 2, ... pick closed subsets C_{i1}, C_{i2}, ... with diam C_{ij} < 1/i, A ⊆ ∪_j C_{ij} and (1) Σ_j ω_{m+k}(diam C_{ij}/2)^{m+k} ≤ H^{m+k}_{1/i}(A) + 1/i, and let g_i = Σ_j ω_k (diam C_{ij}/2)^k χ_{f(C_{ij})} ... (2) g_i(y) = Σ_{j : f⁻¹y ∩ C_{ij} ≠ ∅} ω_k(diam C_{ij}/2)^k ≥ H^k_{1/i}(A ∩ f⁻¹y), and hence ... ∫* H^k_{1/i}(A ∩ f⁻¹y) dLᵐ(y) ≤ ∫ g_i dLᵐ = Σ_j ω_k (diam C_{ij}/2)^k Lᵐ(f(C_{ij})) ≤ Σ_j ω_k ω_m (Lip f)^m (diam C_{ij}/2)^{m+k} ≤ (ω_mω_k/ω_{m+k})(Lip f)^m (H^{m+k}_{1/i}(A) + 1/i), where we used Lᵐ(f(C_{ij})) ≤ ω_m(diam f(C_{ij})/2)^m (isodiametric inequality 2.10) ≤ ω_m (Lip f)^m (diam C_{ij}/2)^m. Letting i → ∞ we conclude ...'. Documented corrections carried over from the parent proof: (a) f(C_{ij}) need not be Borel, so the indicator of the closed set closure f(C_{ij} ∩ E), which has the same diameter, is used instead; (b) instead of the upper integral ∫* of Remark 1.10, an explicit Borel majorant G := liminf_i g_i is built and Fatou's lemma is applied. The isodiametric inequality 2.10 is the kernel-checked SimonGMT theorem `Poincare.SimonGMT.Chapter01.simon_theorem_2_10 (n : ℕ) (A : Set (EuclideanSpace ℝ (Fin n))) : volume A ≤ realUnitBallVolume (n : ℝ) * (ediam A / 2) ^ (n : ℝ)` (valid for every n, including n = 0, and every set A); it lives in `Poincare.SimonGMT.Chapter01.EuclideanNormalization`, which must be imported (it is not imported by the frozen contract). No other erratum.

Conventions used below. (C1) All diameters are extended diameters ediam (Mathlib `Metric.ediam`, `ediam ∅ = 0`); `LipschitzOnWith K f E` means edist (f x) (f x') ≤ K·edist x x' for all x, x' ∈ E. (C2) For d ∈ ℝ, r ∈ (0,∞] and F ⊆ X put pre^d_r(F) := inf { Σ_{n∈ℕ} [t_n ≠ ∅](ediam t_n)^d : t : ℕ → Set X, F ⊆ ⋃_n t_n, ediam t_n ≤ r for all n }, where [t ≠ ∅]x := ⨆ (_ : t.Nonempty), x (that is, x if t ≠ ∅ and 0 if t = ∅). Mathlib's `MeasureTheory.Measure.hausdorffMeasure_apply` states exactly μH[d](F) = ⨆_{r>0} pre^d_r(F) for every F ⊆ X (no measurability needed). If 0 < r ≤ r' then pre^d_{r'}(F) ≤ pre^d_r(F), because every cover admissible at scale r is admissible at scale r'; in particular pre^d_r(F) ≤ μH[d](F) for every r > 0. (C3) For d ≥ 0 put c_d := ω_d/2^d, where ω_d = Chapter01.realUnitBallVolume d. Since 0 < ω_d < ∞ (`Chapter01.realUnitBallVolume_pos`, `Chapter01.realUnitBallVolume_ne_top`) and 0 < 2^d < ∞, we have 0 < c_d < ∞, and 𝓗^d(F) = c_d·μH[d](F) for every F ⊆ X (unfold `Chapter01.simonHausdorffMeasureReal d = (ω_d / 2^d) • μH[d]` and use `Measure.smul_apply`, `smul_eq_mul`). (C4) Fix the data of the statement and put s := m + k > 0, M := μH[s](E), c := ω_m ω_k/ω_s and a := ω_m ω_k K^m / 2^s. All of ω_m, ω_k, ω_s, K^m, 2^s are finite and ω_s, 2^s are nonzero, so c < ∞ and a < ∞.

Proof.
1. (Constant identity.) c·K^m·𝓗^s(E) = a·M. Indeed 𝓗^s(E) = (ω_s/2^s)·M by (C3), and (ω_mω_k/ω_s)·K^m·(ω_s/2^s) = ω_mω_kK^m/2^s = a because the factor ω_s ∈ (0,∞) cancels (ENNReal: `ENNReal.div_mul_cancel`/`ENNReal.mul_div_cancel` with ω_s ≠ 0, ω_s ≠ ⊤, plus commutativity and associativity).
2. (Finiteness.) 𝓗^s(E) = c_s·M < ∞ and c_s ≠ 0 give M < ∞. Hence pre^s_r(E) ≤ M < ∞ for every r > 0 by (C2).
3. (Near-optimal covers.) For i ∈ ℕ put δ_i := ε_i := 1/(i+1) ∈ (0,1] (as elements of ℝ≥0∞, (i+1)⁻¹). Because pre^s_{δ_i}(E) < ∞ and ε_i > 0, pre^s_{δ_i}(E) < pre^s_{δ_i}(E) + ε_i, so by the definition of the infimum (`iInf_lt_iff`) there is a sequence (C_{i,l})_{l∈ℕ} of subsets of X with E ⊆ ⋃_l C_{i,l}, ediam C_{i,l} ≤ δ_i for all l, and Σ_l [C_{i,l} ≠ ∅](ediam C_{i,l})^s ≤ pre^s_{δ_i}(E) + ε_i ≤ M + ε_i. Choose such a sequence for every i.
4. (Trimmed pieces.) Put D_{i,l} := C_{i,l} ∩ E and d_{i,l} := ediam D_{i,l}. Then d_{i,l} ≤ ediam C_{i,l} ≤ δ_i ≤ 1, so d_{i,l} < ∞. Because s > 0 we have d_{i,l}^s ≤ [C_{i,l} ≠ ∅](ediam C_{i,l})^s: if D_{i,l} = ∅ the left side is 0^s = 0; otherwise C_{i,l} ≠ ∅ and t ↦ t^s is monotone. Summing over l and using step 3: (★) Σ_l d_{i,l}^s ≤ M + ε_i.
5. (Image closures.) Put T_{i,l} := closure (f '' D_{i,l}) ⊆ ℝᵐ, a closed and therefore Borel set. For x, x' ∈ D_{i,l} ⊆ E, edist (f x) (f x') ≤ K·edist x x' ≤ K·d_{i,l}; hence ediam (f '' D_{i,l}) ≤ K·d_{i,l} (`Metric.ediam_le`), and since a closure has the same diameter (`Metric.ediam_closure`), ediam T_{i,l} ≤ K·d_{i,l}.
6. (Borel functions g_i.) Define g_i : ℝᵐ → [0,∞] by g_i(y) := Σ_{l∈ℕ} 1_{T_{i,l}}(y)·c_k·d_{i,l}^k (a tsum of `Set.indicator (T_{i,l}) (fun _ ↦ c_k * d_{i,l} ^ k)`). Each summand is a constant times the indicator of a closed set, hence Borel, and a countable sum of Borel [0,∞]-valued functions is Borel (`Measurable.ennreal_tsum`, deprecated but available; or `Measurable.tsum` from `Mathlib.MeasureTheory.Constructions.Polish.Basic`). So every g_i is measurable.
7. (Pointwise bound at scale δ_i.) Fix y ∈ ℝᵐ and put F_y := E ∩ f⁻¹{y}. The sets t_l := D_{i,l} ∩ f⁻¹{y} (l ∈ ℕ) cover F_y (a point x ∈ F_y lies in E ⊆ ⋃_l C_{i,l}), satisfy ediam t_l ≤ d_{i,l} ≤ δ_i, and if t_l ≠ ∅ then y = f(x) for some x ∈ D_{i,l}, so y ∈ f '' D_{i,l} ⊆ T_{i,l}. Therefore [t_l ≠ ∅](ediam t_l)^k ≤ 1_{T_{i,l}}(y)·d_{i,l}^k for every l (k > 0, monotonicity of t ↦ t^k), and by (C2) pre^k_{δ_i}(F_y) ≤ Σ_l 1_{T_{i,l}}(y)·d_{i,l}^k. Multiplying by c_k (`ENNReal.tsum_mul_left`): c_k·pre^k_{δ_i}(F_y) ≤ g_i(y).
8. (Integral of g_i.) By the monotone convergence theorem for series (`lintegral_tsum`) and ∫⁻ 1_T·b dLᵐ = b·Lᵐ(T) for Borel T (`lintegral_indicator_const`), ∫⁻ g_i dLᵐ = Σ_l c_k·d_{i,l}^k·Lᵐ(T_{i,l}). By `simon_theorem_2_10` with n = m (rewrite the real exponent (m:ℝ) as the natural power m by `ENNReal.rpow_natCast`) and step 5, Lᵐ(T_{i,l}) ≤ ω_m·(ediam T_{i,l}/2)^m ≤ ω_m·(K·d_{i,l}/2)^m = ω_m·K^m·d_{i,l}^m/2^m (monotonicity of x ↦ (x/2)^m, `mul_pow`, `ENNReal.inv_pow`). Hence, writing d := d_{i,l} (finite), c_k·d^k·Lᵐ(T_{i,l}) ≤ (ω_k/2^k)·d^k·ω_m·K^m·d^m/2^m = (ω_mω_kK^m/2^{k+m})·d^{k+m} = a·d^s, using d^k·d^m = d^{k+m} (first rewrite the natural powers d^m and 2^m as real powers d^(m:ℝ), 2^(m:ℝ) with `ENNReal.rpow_natCast`; then `ENNReal.rpow_add_of_nonneg`, valid also for d = 0 since k ≥ 0 and (m:ℝ) ≥ 0), 2^k·2^(m:ℝ) = 2^{k+m} (`ENNReal.rpow_add`, as 2 ≠ 0, 2 ≠ ⊤) and k + m = m + k = s. (All factors are finite, so these identities may also be checked after passing to ℝ≥0.) Summing over l and using (★): (★★) ∫⁻ g_i dLᵐ ≤ a·Σ_l d_{i,l}^s ≤ a·(M + ε_i).
9. (The majorant.) Define G(y) := liminf_{i→∞} g_i(y) (`Filter.liminf (fun i ↦ g_i y) atTop`). G is Borel (`Measurable.liminf`).
10. (G dominates the fibre measures.) Fix y ∈ ℝᵐ and r ∈ (0,∞]. Choose i₀ with δ_{i₀} ≤ r (`ENNReal.exists_inv_nat_lt`). For every i ≥ i₀ we have δ_i ≤ δ_{i₀} ≤ r, so by (C2) and step 7, c_k·pre^k_r(F_y) ≤ c_k·pre^k_{δ_i}(F_y) ≤ g_i(y). Hence c_k·pre^k_r(F_y) ≤ ⨅_{i≥i₀} g_i(y) ≤ liminf_i g_i(y) = G(y). Taking the supremum over r > 0 and using (C3), (C2) and `ENNReal.mul_iSup`: 𝓗^k(E ∩ f⁻¹{y}) = c_k·⨆_{r>0} pre^k_r(F_y) = ⨆_{r>0} c_k·pre^k_r(F_y) ≤ G(y).
11. (Integral bound.) By Fatou's lemma (`lintegral_liminf_le`, all g_i measurable) and (★★), ∫⁻ G dLᵐ ≤ liminf_i ∫⁻ g_i dLᵐ ≤ liminf_i a·(M + ε_i). Since a < ∞, M < ∞ and ε_i = (i+1)⁻¹ → 0 (`ENNReal.tendsto_inv_nat_nhds_zero` composed with the shift i ↦ i + 1, e.g. via `tendsto_add_atTop_iff_nat 1`), a·(M + ε_i) → a·M (`ENNReal.Tendsto.const_mul`, `Tendsto.const_add`), so this liminf equals a·M (`Tendsto.liminf_eq`), which equals c·K^m·𝓗^s(E) by step 1. Hence ∫⁻ G dLᵐ ≤ (ω_mω_k/ω_{m+k})·K^m·𝓗^{m+k}(E).
12. (Conclusion.) G is measurable (step 9), dominates y ↦ 𝓗^k(E ∩ f⁻¹{y}) everywhere (step 10) and satisfies the integral bound (step 11). The argument is uniform in K ≥ 0 and m ∈ ℕ (K = 0 and m = 0 included), because simon_theorem_2_10 holds in every dimension and every identity used above holds for these values. ∎

## Key steps

1. Constant identity c·K^m·𝓗^{m+k}(E) = (ω_mω_kK^m/2^{m+k})·μH[m+k](E) and finiteness of μH[m+k](E).
2. For δ_i = ε_i = 1/(i+1) choose near-optimal covers C_{i,l} of E from hausdorffMeasure_apply; trimmed diameters d_{i,l} = ediam(C_{i,l} ∩ E) satisfy Σ_l d_{i,l}^{m+k} ≤ μH[m+k](E) + ε_i.
3. Borel functions g_i = Σ_l c_k d_{i,l}^k 1_{closure f(C_{i,l} ∩ E)} satisfy c_k·pre^k_{δ_i}(E ∩ f⁻¹{y}) ≤ g_i(y) for every y.
4. Isodiametric inequality (simon_theorem_2_10) and the Lipschitz diameter bound give ∫⁻ g_i ≤ (ω_mω_kK^m/2^{m+k})(μH[m+k](E) + ε_i).
5. G := liminf g_i is Borel, dominates 𝓗^k(E ∩ f⁻¹{y}) pointwise (sup over scales), and Fatou's lemma gives ∫⁻ G ≤ (ω_mω_k/ω_{m+k})K^m𝓗^{m+k}(E).

## Reference use

### local-project

Queries:
- `cat local-references/ff09f3909baeeae7/manifest.json (project 1b1689a8, mathlib 25730c7c)`
- `rg -n 'EilenbergInequality|Eilenberg' project`
- `rg -n -i 'eilenberg' mathlib/Mathlib`
- `rg -n -i 'coarea' mathlib/Mathlib`
- `rg -n 'hausdorffMeasure.*preimage|preimage.*hausdorffMeasure' mathlib/Mathlib`
- `grep -n '^end|^section|^noncomputable section|^namespace|^local notation|^theorem main_theorem' project/GMT/Ch02/Contract.lean`
- `rg -n 'theorem hausdorffMeasure_apply|theorem hausdorffMeasure_le_liminf_sum' mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n 'theorem lintegral_liminf_le|theorem lintegral_tsum|theorem lintegral_indicator_const|theorem lintegral_eq_zero_iff' mathlib/Mathlib/MeasureTheory/Integral/Lebesgue`
- `rg -n 'theorem UpperSemicontinuous.measurable|theorem measurable_of_Iio|theorem Measurable.liminf|protected theorem Measurable.iSup|theorem Measurable.ennreal_tsum' mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace`
- `rg -n 'exists_isCompact_sdiff_lt|Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure|instance.*InnerRegularCompactLTTop' mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `rg -n 'Monotone.measure_iUnion|measure_iUnion_eq_iSup' mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `rg -n 'ediam_image_le|ediam_closure|ediam_thickening_le' mathlib/Mathlib/Topology`
- `rg -n 'rpow_add_of_nonneg|div_rpow_of_nonneg' mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean`
- `rg -n 'theorem IsCompact.elim_finite_subcover|theorem IsCompact.diff|theorem IsCompact.image_of_continuousOn|theorem ContinuousOn.preimage_isClosed_of_isClosed' mathlib/Mathlib/Topology`
- `grep -n 'theorem|lemma' mathlib/Mathlib/Order/SetAccumulate.lean`
- `grep -rn 'simon_theorem_2_10|exists_isOpen_superset_ediam_rpow_lt|def simonHausdorffMeasureReal|def realUnitBallVolume|realUnitBallVolume_pos|realUnitBallVolume_ne_top' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01`
- `read lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/LipschitzMeasurability.lean and Chapter01/RegularityCompletion.lean (compact-approximation pattern)`
- `python3 -I gen_checks.py (imports verifier gmt-compare.py contract_scope/child_modules and lean_contract.validate_lean_statement) then lean NodeChallenge_00..02.lean, AssemblyCheck.lean, ExhaustionCheck.lean, Probe.lean against a scratch olean of GMT.Ch02.Submission built with plain `lean -o` (no lake build)`
- `#print axioms assembly_check / exhaustion_check; #print EilenbergInequality; #check child targets`
- `python3 -I: collect all lean_name values in dag.json and nodes/*/*.json`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/ContinuousOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Order/SetAccumulate.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/AlgebraicTopology/EilenbergSteenrod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/EuclideanNormalization.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/HausdorffOpenCovers.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RegularityCompletion.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/LipschitzMeasurability.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/UpperIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/eilenberg-decomp-NyRDhV/checks/AssemblyCheck.lean`
- `/tmp/eilenberg-decomp-NyRDhV/checks/ExhaustionCheck.lean`
- `/tmp/eilenberg-decomp-NyRDhV/final/NodeChallenge_00.lean`

**No existing result.** No ready-made result exists in the snapshot:
- The 'eilenberg' matches in Mathlib are only the Eilenberg–Steenrod and Eilenberg–Schützenberger files.
- 'coarea' has no match.
- Hausdorff-measure preimage lemmas exist only for antilipschitz maps and isometries, with no fibre-measurability theorem.
- The project has only the frozen definition (Contract.lean:232) and README row 6.

**Contract scope.** In Contract.lean, a bare `end` at line 374 closes the noncomputable section holding the local notations 𝓗[·]/ω[·] (lines 51, 54) before main_theorem (line 377). The comparator replays that `end`, and the first draft statements were misparsed as GetElem on an auto-bound 𝓗. The final statements therefore spell out Chapter01.simonHausdorffMeasureReal and Chapter01.realUnitBallVolume; `open Poincare.SimonGMT` (line 43) is still in scope.

**Mathlib tools.**
- Hausdorff measure: hausdorffMeasure_apply (Hausdorff.lean:546; covers with ediam ≤ r and Nonempty-weighted cost) and hausdorffMeasure_le_liminf_sum (:563).
- Lebesgue integral: lintegral_liminf_le (Lebesgue/Add.lean:233), lintegral_tsum (Add.lean:362), lintegral_indicator_const (Basic.lean:541), lintegral_eq_zero_iff (Basic.lean:349).
- Measurability: UpperSemicontinuous.measurable (BorelSpace/Order.lean:649), Measurable.iSup (Order.lean:909), Measurable.liminf (Order.lean:1058), Measurable.ennreal_tsum (deprecated, BorelSpace/Real.lean:354).
- Regularity and continuity: MeasurableSet.exists_isCompact_sdiff_lt (Regular.lean:843), Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure (Regular.lean:1183), Monotone.measure_iUnion (Continuity.lean:71; arbitrary sets).
- Metric and topology: ediam_thickening_le (Thickening.lean:354), Metric.ediam_closure (ENNReal/Lemmas.lean:649), LipschitzWith.ediam_image_le (Lipschitz.lean:171), IsCompact.elim_finite_subcover/diff/image_of_continuousOn (Compact.lean:208/101/110), ContinuousOn.preimage_isClosed_of_isClosed (ContinuousOn.lean:197).
- ENNReal powers and accumulate: ENNReal.rpow_add_of_nonneg (Pow/NNReal.lean:633), ENNReal.div_rpow_of_nonneg (NNReal.lean:769), plus the accumulate lemmas (SetAccumulate.lean).
- There is no LipschitzOnWith.ediam_image_le, so child 1 bounds diameters directly with Metric.ediam_le.

**SimonGMT (pinned package).**
- simonHausdorffMeasureReal s = (realUnitBallVolume s / 2^s) • μH[s] (Hausdorff.lean:283).
- realUnitBallVolume_pos and realUnitBallVolume_ne_top (Hausdorff.lean:499, 506).
- simon_theorem_2_10, the isodiametric inequality for every n and every set (EuclideanNormalization.lean:24). It is not imported by the contract, so the child must add the import; I verified the import works alongside GMT.Ch02.Submission.
- exists_isOpen_superset_ediam_rpow_lt (HausdorffOpenCovers.lean:29; optional, needs an import).
- LipschitzMeasurability.lean shows the same restrict/Regular compact-approximation pattern that child 3 uses.
- The UpperIntegral.lean tools are not needed.

**Lean verification.**
- All three child lean_statements elaborate in the replayed comparator scope.
- AssemblyCheck.lean derives `EilenbergInequality` from the three child types using only propext, Classical.choice and Quot.sound.
- ExhaustionCheck.lean proves child 3 outright with standard axioms only.

**Name collisions.** dag.json reserves only the 12 depth-1 names and GMT.Ch02.main_theorem, so the eilenberg_-prefixed names do not collide.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: https://github.com/ZhengyangZhang06/gmt-formalize/pull/1801

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
