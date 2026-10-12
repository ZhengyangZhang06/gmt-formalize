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
import Mathlib.Analysis.Calculus.BumpFunction.Normed

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

/-- **Simon Ch. 2, proof of Theorem 2.6, step A0: unweighted uniform bounds.** For open `W ⊆ ℝⁿ`
with `Lⁿ(W) < ∞`, the frozen hypothesis `sup_k ∫_W (|u_k| + |Du_k|(W)) dLⁿ < ∞` (the constant
`|Du_k|(W)` inside the integrand) yields one real `c ≥ 0` with `∫_W |u_k| ≤ c` and `|Du_k|(W) ≤ c`
for every `k`. If `W = ∅` both quantities vanish; otherwise `0 < Lⁿ(W) < ∞`, the integral of the
constant is `|Du_k|(W) Lⁿ(W)`, and `c = S + S / Lⁿ(W)` with `S` the supremum. -/
theorem Submission.bv_compactness_uniform_bounds : ∀ (n : ℕ) (W : Set (Rn n)) (u : ℕ → Rn n → ℝ), IsOpen W → volume W < ⊤ → ⨆ k, (∫⁻ x in W, ‖u k x‖ₑ + Chapter02.bvVariationOn (u k) W) < ⊤ → ∃ c : ℝ, 0 ≤ c ∧ ∀ k, (∫⁻ x in W, ‖u k x‖ₑ) ≤ ENNReal.ofReal c ∧ Chapter02.bvVariationOn (u k) W ≤ ENNReal.ofReal c := by
  intro n W u hW hWfin hS
  rcases W.eq_empty_or_nonempty with rfl | hne
  -- Step 1: `W = ∅`. Both quantities are integrals against `volume.restrict ∅ = 0`.
  · refine ⟨0, le_rfl, fun k ↦ ⟨by simp, ?_⟩⟩
    simp [Chapter02.bvVariationOn]
  -- Step 2: `0 < Lⁿ(W) < ∞` (`Lⁿ` is positive on nonempty open sets).
  · have h0 : volume W ≠ 0 := (hW.measure_pos volume hne).ne'
    have hfin : volume W ≠ ⊤ := hWfin.ne
    set S := ⨆ k, (∫⁻ x in W, ‖u k x‖ₑ + Chapter02.bvVariationOn (u k) W)
    -- Step 3: `∫_W |u_k| + |Du_k|(W) Lⁿ(W) = ∫_W (|u_k| + |Du_k|(W)) ≤ S`.
    have hk : ∀ k, (∫⁻ x in W, ‖u k x‖ₑ) + Chapter02.bvVariationOn (u k) W * volume W ≤ S :=
      fun k ↦ by
        rw [← setLIntegral_const, ← lintegral_add_right _ measurable_const]
        exact le_iSup (fun k ↦ ∫⁻ x in W, ‖u k x‖ₑ + Chapter02.bvVariationOn (u k) W) k
    -- Step 5: `C = S + S / Lⁿ(W) < ∞`; take `c = C.toReal`, so `ofReal c = C`.
    have hC : S + S / volume W ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hS.ne, ENNReal.div_ne_top hS.ne h0⟩
    refine ⟨(S + S / volume W).toReal, ENNReal.toReal_nonneg, fun k ↦ ?_⟩
    rw [ENNReal.ofReal_toReal hC]
    -- Steps 4 and 6: `∫_W |u_k| ≤ S` and `|Du_k|(W) ≤ S / Lⁿ(W)`.
    refine ⟨le_add_right (le_self_add.trans (hk k)), le_add_left ?_⟩
    rw [ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl hfin)]
    exact le_add_self.trans (hk k)
/-- **Simon Ch. 2, proof of Theorem 2.6 (step A4): a variation bound gives the bound (2.1).** If
`|Du|(W) ≤ c` (`Chapter02.bvVariationOn`, Simon 2.4) and `g` is a compactly supported `C¹` field
with `spt g ⊆ W`, then `∫_W u div g ≤ c sup |g|`. With `s = sup |g|`: if `s = 0` then `g = 0` and
both sides vanish; otherwise `h = s⁻¹ g` is an admissible Lipschitz field in (2.4) with
`sup |h| ≤ 1` and `div h = s⁻¹ div g`, so `s⁻¹ ∫_W u div g = ∫_W u div h ≤ |Du|(W) ≤ c`. -/
theorem Submission.bv_integral_div_le_of_variation_le : ∀ (n : ℕ) (W : Set (Rn n)) (u : Rn n → ℝ) (c : ℝ), 0 ≤ c → Chapter02.bvVariationOn u W ≤ ENNReal.ofReal c → ∀ g : CompactlySupportedContinuousMap (Rn n) (Rn n), Chapter02.IsC1TestField g → tsupport g ⊆ W → (∫ x in W, u x * Chapter02.euclideanDivergence (g : Rn n → Rn n) x) ≤ c * Chapter02.compactlySupportedSupNorm g := by
  intro n W u c hc hvar g hg hsupp
  set s := Chapter02.compactlySupportedSupNorm g
  -- Step 1: `g` is bounded, so `‖g x‖ ≤ s` for every `x`, and `0 ≤ s`.
  have hbdd : BddAbove (range fun x ↦ ‖g x‖) := by
    obtain ⟨C, hC⟩ := (map_continuous g).bounded_above_of_compact_support g.hasCompactSupport
    exact ⟨C, by rintro _ ⟨x, rfl⟩; exact hC x⟩
  have hle : ∀ x, ‖g x‖ ≤ s := fun x ↦ le_csSup hbdd ⟨x, rfl⟩
  have hs0 : 0 ≤ s := (norm_nonneg _).trans (hle 0)
  rcases hs0.eq_or_lt with hs | hs
  · -- Step 2: `s = 0`, so `g = 0`, `div g = 0` and both sides vanish.
    have hg0 : (g : Rn n → Rn n) = 0 := funext fun x ↦ norm_le_zero_iff.mp (hs ▸ hle x)
    have hdiv0 : ∀ x, Chapter02.euclideanDivergence (g : Rn n → Rn n) x = 0 := fun x ↦ by
      simp [Chapter02.euclideanDivergence, hg0]
    simp [hdiv0, ← hs]
  · -- Step 3: `s > 0`; normalize to `h := s⁻¹ • g`.
    set h : CompactlySupportedContinuousMap (Rn n) (Rn n) := s⁻¹ • g
    have hcoe : (h : Rn n → Rn n) = s⁻¹ • (g : Rn n → Rn n) :=
      CompactlySupportedContinuousMap.coe_smul _ _
    -- (a) `h` is `C¹`, hence an admissible Lipschitz test field.
    have hC1 : Chapter02.IsC1TestField h := by
      unfold Chapter02.IsC1TestField
      rw [hcoe]
      exact hg.const_smul s⁻¹
    -- (b) `tsupport h ⊆ tsupport g ⊆ W`.
    have hsupp' : tsupport h ⊆ W := by
      rw [hcoe]
      exact (tsupport_smul_subset_right (fun _ ↦ s⁻¹) g).trans hsupp
    -- (c) `sup |h| = s⁻¹ s ≤ 1`.
    have hnorm : Chapter02.compactlySupportedSupNorm h ≤ 1 := by
      refine csSup_le (range_nonempty _) ?_
      rintro _ ⟨x, rfl⟩
      simp only [hcoe, Pi.smul_apply, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hs.le)]
      calc s⁻¹ * ‖g x‖ ≤ s⁻¹ * s := mul_le_mul_of_nonneg_left (hle x) (inv_nonneg.mpr hs.le)
        _ = 1 := inv_mul_cancel₀ hs.ne'
    -- (d) `div h = s⁻¹ div g`, since `D h = s⁻¹ D g` and the trace is linear.
    have hdiv : ∀ x, Chapter02.euclideanDivergence (h : Rn n → Rn n) x =
        s⁻¹ * Chapter02.euclideanDivergence (g : Rn n → Rn n) x := fun x ↦ by
      have hd : DifferentiableAt ℝ (g : Rn n → Rn n) x := hg.differentiable one_ne_zero x
      simp only [Chapter02.euclideanDivergence, hcoe, fderiv_const_smul hd,
        ContinuousLinearMap.toLinearMap_smul, map_smul, smul_eq_mul]
    -- Step 4: `h` is admissible in `bvVariationOn u W`, so `∫_W u div h ≤ c`.
    have h1 : (∫ x in W, u x * Chapter02.euclideanDivergence (h : Rn n → Rn n) x) ≤ c :=
      (ENNReal.ofReal_le_ofReal_iff hc).mp
        ((Chapter02.ofReal_integral_le_bvVariationOn u W h hC1.isLipschitzTestField hsupp'
          hnorm).trans hvar)
    -- Step 5: `∫_W u div h = s⁻¹ ∫_W u div g`; multiply by `s > 0`.
    have h2 : (∫ x in W, u x * Chapter02.euclideanDivergence (h : Rn n → Rn n) x) =
        s⁻¹ * ∫ x in W, u x * Chapter02.euclideanDivergence (g : Rn n → Rn n) x := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      simp only [hdiv x]
      ring
    rw [h2, inv_mul_le_iff₀ hs] at h1
    linarith
/-- **Simon Ch. 2, proof of Theorem 2.6: sup and Lipschitz bounds for a mollification.** For `ρ`
bounded by `A` and `K`-Lipschitz, and `F ∈ L¹(ℝⁿ)`: `|(ρ * F)(x)| ≤ A ∫ |F|` and
`|(ρ * F)(x) - (ρ * F)(y)| ≤ K |x - y| ∫ |F|` (the uniform bounds behind the Arzelà step). In the
symmetric form `(ρ * F)(z) = ∫ ρ(z - t) F(t) dt` (translation and reflection invariance of `Lⁿ`),
both follow by integrating the majorants `A |F|` and `K |x - y| |F|`. -/
theorem Submission.bv_convolution_bound_and_lipschitz : ∀ (n : ℕ) (ρ F : Rn n → ℝ) (A : ℝ) (K : ℝ≥0), (∀ x, |ρ x| ≤ A) → LipschitzWith K ρ → Integrable F volume → ∀ x y : Rn n, |convolution ρ F (ContinuousLinearMap.lsmul ℝ ℝ) volume x| ≤ A * (∫ t, |F t|) ∧ |convolution ρ F (ContinuousLinearMap.lsmul ℝ ℝ) volume x - convolution ρ F (ContinuousLinearMap.lsmul ℝ ℝ) volume y| ≤ K * ‖x - y‖ * (∫ t, |F t|) := by
  intro n ρ F A K hA hK hF x y
  -- Step 2: `(ρ * F)(z) = ∫ ρ(z - t) F(t) dt`.
  have hswap : ∀ z, convolution ρ F (ContinuousLinearMap.lsmul ℝ ℝ) volume z =
      ∫ t, ρ (z - t) * F t := fun z ↦ by
    simp only [convolution_lsmul_swap, smul_eq_mul]
  -- Step 3: `t ↦ ρ(z - t) F(t)` is integrable: `t ↦ ρ(z - t)` is continuous (`ρ` is Lipschitz)
  -- and bounded by `A`.
  have hint : ∀ z, Integrable (fun t ↦ ρ (z - t) * F t) volume := fun z ↦
    hF.bdd_mul (hK.continuous.comp (continuous_sub_left z)).aestronglyMeasurable
      (Eventually.of_forall fun t ↦ by rw [Real.norm_eq_abs]; exact hA (z - t))
  refine ⟨?_, ?_⟩
  -- Step 4: `|ρ(x - t) F(t)| ≤ A |F(t)|`.
  · calc |convolution ρ F (ContinuousLinearMap.lsmul ℝ ℝ) volume x|
        = ‖∫ t, ρ (x - t) * F t‖ := by rw [hswap, Real.norm_eq_abs]
      _ ≤ ∫ t, A * |F t| := by
        refine norm_integral_le_of_norm_le (hF.abs.const_mul A) (Eventually.of_forall fun t ↦ ?_)
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right (hA _) (abs_nonneg _)
      _ = A * ∫ t, |F t| := integral_const_mul A _
  -- Step 5: `|(ρ(x - t) - ρ(y - t)) F(t)| ≤ K |x - y| |F(t)|`.
  · calc |convolution ρ F (ContinuousLinearMap.lsmul ℝ ℝ) volume x -
          convolution ρ F (ContinuousLinearMap.lsmul ℝ ℝ) volume y|
        = ‖∫ t, (ρ (x - t) * F t - ρ (y - t) * F t)‖ := by
          rw [hswap, hswap, integral_sub (hint x) (hint y), Real.norm_eq_abs]
      _ ≤ ∫ t, K * ‖x - y‖ * |F t| := by
        refine norm_integral_le_of_norm_le (hF.abs.const_mul _) (Eventually.of_forall fun t ↦ ?_)
        rw [Real.norm_eq_abs, ← sub_mul, abs_mul]
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        have hLip := hK.dist_le_mul (x - t) (y - t)
        rwa [Real.dist_eq, dist_eq_norm, sub_sub_sub_cancel_right] at hLip
      _ = K * ‖x - y‖ * ∫ t, |F t| := integral_const_mul _ _
/-- **Simon Ch. 2, proof of Theorem 2.6: finite `L¹(Q)`-nets (the Arzelà step).** Let `Q ⊂ ℝⁿ` be
compact and `u_k ∈ L¹(Q)`. Suppose that for each `ε > 0` there are `w_k`, bounded by `B` and
`Λ`-Lipschitz on `Q` (`B`, `Λ` independent of `k`), with `∫_Q |u_k - w_k| ≤ ε`. Then for each
`ε > 0` finitely many `u_j` form an `ε`-net of `{u_k}` in `L¹(Q)`. The values of the `w_k` on a
finite `r`-net `T ⊂ Q` lie in a compact ball of `T → ℝ`, so up to `η / 2` they take finitely many
values; `w_k`, `w_j` with nearby values on `T` are uniformly `η`-close on `Q`. -/
theorem Submission.bv_lintegral_finite_net_of_lipschitz_approx : ∀ (n : ℕ) (Q : Set (Rn n)) (u : ℕ → Rn n → ℝ), IsCompact Q → (∀ k, IntegrableOn (u k) Q volume) → (∀ ε : ℝ, 0 < ε → ∃ (B Λ : ℝ) (w : ℕ → Rn n → ℝ), (∀ k, ∀ x ∈ Q, |w k x| ≤ B) ∧ (∀ k, ∀ x ∈ Q, ∀ y ∈ Q, |w k x - w k y| ≤ Λ * ‖x - y‖) ∧ ∀ k, (∫⁻ x in Q, ‖u k x - w k x‖ₑ) ≤ ENNReal.ofReal ε) → ∀ ε : ℝ, 0 < ε → ∃ F : Finset ℕ, ∀ k, ∃ j ∈ F, (∫⁻ x in Q, ‖u k x - u j x‖ₑ) < ENNReal.ofReal ε := by
  intro n Q u hQ hu happrox ε hε
  -- Step 1: `Q` is closed, hence measurable, and `Lⁿ(Q) < ∞`; put `m = Lⁿ(Q)`.
  have hQm : MeasurableSet Q := hQ.isClosed.measurableSet
  have hQfin : volume Q < ⊤ := hQ.measure_lt_top
  set m : ℝ := (volume Q).toReal with hm
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  -- Step 3: approximate at accuracy `ε / 4`; `Λ' = max Λ 0 ≥ 0` is also a Lipschitz constant.
  obtain ⟨B, Λ, w, hB, hΛ, hw⟩ := happrox (ε / 4) (by positivity)
  obtain ⟨Λ', hΛ'0, hwΛ'⟩ : ∃ Λ' : ℝ, 0 ≤ Λ' ∧
      ∀ k, ∀ x ∈ Q, ∀ y ∈ Q, |w k x - w k y| ≤ Λ' * ‖x - y‖ :=
    ⟨max Λ 0, le_max_right _ _, fun k x hx y hy ↦
      (hΛ k x hx y hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))⟩
  -- Step 4 (with the Remark's radius): `η = ε / (4 (m + 1))`, `r = η / (4 (Λ' + 1))`, and a finite
  -- `T ⊂ Q` with `Q ⊂ ⋃_{q ∈ T} B(q, r)` (open balls).
  set η : ℝ := ε / (4 * (m + 1)) with hη
  have hη0 : 0 < η := by positivity
  set r : ℝ := η / (4 * (Λ' + 1)) with hr
  have hr0 : 0 < r := by positivity
  obtain ⟨T, hTQ, hTfin, hQT⟩ := hQ.finite_cover_balls hr0
  have : Fintype T := hTfin.fintype
  -- Steps 5–6 (Remark): `p_k = (w_k(q))_{q ∈ T}` lies in the compact closed ball of radius
  -- `max B 0` of the sup-normed `T → ℝ`, so `{p_k}` has a finite `η / 2`-net `t ⊂ {p_k}`; `F`
  -- consists of one index `j` with `p_j = y` for each `y ∈ t`.
  let p : ℕ → T → ℝ := fun k q ↦ w k q
  have hpB : Set.range p ⊆ closedBall 0 (max B 0) := by
    rintro _ ⟨k, rfl⟩
    rw [mem_closedBall, dist_pi_le_iff (le_max_right _ _)]
    intro q
    rw [Real.dist_eq, Pi.zero_apply, sub_zero]
    exact (hB k q (hTQ q.2)).trans (le_max_left _ _)
  have hptb : TotallyBounded (Set.range p) := (isCompact_closedBall _ _).totallyBounded.subset hpB
  obtain ⟨t, htp, htfin, hpt⟩ := Metric.finite_approx_of_totallyBounded hptb (η / 2) (by positivity)
  refine ⟨htfin.toFinset.image (Function.invFun p), fun k ↦ ?_⟩
  obtain ⟨y, hyt, hky⟩ : ∃ y ∈ t, p k ∈ ball y (η / 2) := by
    simpa using hpt (Set.mem_range_self k)
  set j := Function.invFun p y
  have hpj : p j = y := Function.invFun_eq (htp hyt)
  refine ⟨j, Finset.mem_image.2 ⟨y, htfin.mem_toFinset.2 hyt, rfl⟩, ?_⟩
  -- Step 7: `|w_k(q) - w_j(q)| ≤ dist p_k p_j < η / 2` for `q ∈ T`.
  have hT : ∀ q ∈ T, |w k q - w j q| < η / 2 := fun q hq ↦ by
    have hd : dist (p k) (p j) < η / 2 := by rw [hpj]; exact hky
    have hq' := dist_le_pi_dist (p k) (p j) ⟨q, hq⟩
    rw [Real.dist_eq] at hq'
    exact hq'.trans_lt hd
  -- Step 8: for `x ∈ Q` and `q ∈ T` with `|x - q| < r`,
  -- `|w_k(x) - w_j(x)| ≤ Λ' r + η / 2 + Λ' r ≤ η`, since `Λ' r ≤ η / 4`.
  have hΛr : Λ' * r ≤ η / 4 := by
    rw [hr, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hQpt : ∀ x ∈ Q, ‖w k x - w j x‖ₑ ≤ ENNReal.ofReal η := fun x hx ↦ by
    obtain ⟨q, hqT, hxq⟩ : ∃ q ∈ T, x ∈ ball q r := by simpa using hQT hx
    have hq : q ∈ Q := hTQ hqT
    rw [mem_ball, dist_eq_norm] at hxq
    have h1 : |w k x - w k q| ≤ Λ' * r :=
      (hwΛ' k x hx q hq).trans (mul_le_mul_of_nonneg_left hxq.le hΛ'0)
    have h2 : |w j q - w j x| ≤ Λ' * r := by
      refine (hwΛ' j q hq x hx).trans (mul_le_mul_of_nonneg_left ?_ hΛ'0)
      rw [norm_sub_rev]
      exact hxq.le
    have h3 : |w k x - w j x| ≤ η := calc
      |w k x - w j x| = |(w k x - w k q) + (w k q - w j q) + (w j q - w j x)| := by
        congr 1; ring
      _ ≤ |w k x - w k q| + |w k q - w j q| + |w j q - w j x| := abs_add_three _ _ _
      _ ≤ η := by linarith [hT q hqT]
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal h3
  -- Step 9: `∫_Q |w_k - w_j| ≤ η m ≤ ε / 4`.
  have hηm : η * m ≤ ε / 4 := by
    rw [hη, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hwkj : (∫⁻ x in Q, ‖w k x - w j x‖ₑ) ≤ ENNReal.ofReal (ε / 4) := calc
    (∫⁻ x in Q, ‖w k x - w j x‖ₑ) ≤ ∫⁻ _ in Q, ENNReal.ofReal η :=
      setLIntegral_mono measurable_const hQpt
    _ = ENNReal.ofReal (η * m) := by
      rw [setLIntegral_const, ENNReal.ofReal_mul hη0.le, hm, ENNReal.ofReal_toReal hQfin.ne]
    _ ≤ ENNReal.ofReal (ε / 4) := ENNReal.ofReal_le_ofReal hηm
  -- Step 10: `u_k` is a.e.-strongly measurable for `Lⁿ ⌞ Q`, and so is each `w_i`, being
  -- Lipschitz, hence continuous, on the measurable set `Q`.
  have hwm : ∀ i, AEStronglyMeasurable (w i) (volume.restrict Q) := fun i ↦
    (LipschitzOnWith.of_dist_le_mul (K := Real.toNNReal Λ') fun x hx y hy ↦ by
      rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hΛ'0]
      exact hwΛ' i x hx y hy).continuousOn.aestronglyMeasurable hQm
  have hk : AEMeasurable (fun x ↦ ‖u k x - w k x‖ₑ) (volume.restrict Q) :=
    ((hu k).aestronglyMeasurable.sub (hwm k)).enorm
  have hkj : AEMeasurable (fun x ↦ ‖u k x - w k x‖ₑ + ‖w k x - w j x‖ₑ) (volume.restrict Q) :=
    hk.add ((hwm k).sub (hwm j)).enorm
  -- Step 11: `|u_k - u_j| ≤ |u_k - w_k| + |w_k - w_j| + |u_j - w_j|`; integrate (additivity with
  -- a.e.-measurable left summands) and use the approximation for `k` and `j` and Step 9.
  calc (∫⁻ x in Q, ‖u k x - u j x‖ₑ)
      ≤ ∫⁻ x in Q, (‖u k x - w k x‖ₑ + ‖w k x - w j x‖ₑ + ‖u j x - w j x‖ₑ) := by
        refine lintegral_mono fun x ↦ ?_
        calc ‖u k x - u j x‖ₑ = ‖(u k x - w k x) + (w k x - w j x) + (w j x - u j x)‖ₑ := by
              congr 1; ring
          _ ≤ ‖u k x - w k x‖ₑ + ‖w k x - w j x‖ₑ + ‖w j x - u j x‖ₑ :=
              (enorm_add_le _ _).trans (add_le_add (enorm_add_le _ _) le_rfl)
          _ = _ := by rw [enorm_sub_rev (w j x)]
    _ = (∫⁻ x in Q, ‖u k x - w k x‖ₑ) + (∫⁻ x in Q, ‖w k x - w j x‖ₑ) +
          ∫⁻ x in Q, ‖u j x - w j x‖ₑ := by
        rw [lintegral_add_left' hkj, lintegral_add_left' hk]
    _ ≤ ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) :=
        add_le_add (add_le_add (hw k) hwkj) (hw j)
    _ = ENNReal.ofReal (3 * ε / 4) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf
    _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith)
/-- **Simon Ch. 2, proof of Theorem 2.6, compact exhaustion (step 1 of the diagonal extraction).**
If `U ⊆ ℝⁿ` is open, the sets `Q j = B_{j+1}(0) ∩ {x : 1/(j+1) ≤ infEDist x Uᶜ}` are compact, lie
in `U` and increase with `j`; indeed `Q j ⊆ interior (Q (j+1))`. Every `x ∈ U` lies in some `Q j`
since `Uᶜ` is closed, so the increasing open sets `interior (Q (j+1))` cover any compact `K ⊆ U`,
and one of them already contains `K`. -/
theorem Submission.bv_isOpen_exists_compact_exhaustion : ∀ (n : ℕ) (U : Set (Rn n)), IsOpen U → ∃ Q : ℕ → Set (Rn n), (∀ j, IsCompact (Q j)) ∧ (∀ j, Q j ⊆ U) ∧ Monotone Q ∧ ∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ j, K ⊆ Q j := by
  intro n U hU
  -- `Q j = B_{j+1}(0) ∩ {x : 1/(j+1) ≤ infEDist x Uᶜ}`; no case distinction on `U` or `n`.
  let Q : ℕ → Set (Rn n) := fun j ↦
    closedBall 0 ((j : ℝ) + 1) ∩ {x | ENNReal.ofReal (1 / ((j : ℝ) + 1)) ≤ infEDist x Uᶜ}
  -- (i) A compact ball cut by a closed superlevel set of the continuous `x ↦ infEDist x Uᶜ`.
  have hQc (j : ℕ) : IsCompact (Q j) :=
    (isCompact_closedBall 0 _).inter_right (isClosed_le continuous_const continuous_infEDist)
  -- (ii) Off `U` the distance `infEDist x Uᶜ` vanishes, while `1/(j+1) > 0`.
  have hQU (j : ℕ) : Q j ⊆ U := fun x hx ↦ by
    by_contra hxU
    have h1 : ENNReal.ofReal (1 / ((j : ℝ) + 1)) ≤ infEDist x Uᶜ := hx.2
    rw [infEDist_zero_of_mem hxU] at h1
    exact absurd h1 (not_le.2 (ENNReal.ofReal_pos.2 (by positivity)))
  -- `Q j ⊆ interior (Q (j+1))`: the open set `ball 0 (j+2) ∩ {1/(j+2) < infEDist · Uᶜ}` contains
  -- `Q j` and lies in `Q (j+1)`.
  have hQint (j : ℕ) : Q j ⊆ interior (Q (j + 1)) := fun x hx ↦ by
    have h2 : ((j + 1 : ℕ) : ℝ) + 1 = (j : ℝ) + 2 := by push_cast; ring
    have h12 : ENNReal.ofReal (1 / ((j : ℝ) + 2)) < ENNReal.ofReal (1 / ((j : ℝ) + 1)) :=
      (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2
        (one_div_lt_one_div_of_lt (by positivity) (by linarith))
    refine mem_interior.2 ⟨ball 0 ((j : ℝ) + 2) ∩
        {y | ENNReal.ofReal (1 / ((j : ℝ) + 2)) < infEDist y Uᶜ}, ?_,
      isOpen_ball.inter (isOpen_lt continuous_const continuous_infEDist), ?_⟩
    · rintro y ⟨hy1, hy2⟩
      refine ⟨mem_closedBall_zero_iff.2 ?_, ?_⟩
      · rw [h2]
        exact (mem_ball_zero_iff.1 hy1).le
      · show ENNReal.ofReal (1 / (((j + 1 : ℕ) : ℝ) + 1)) ≤ infEDist y Uᶜ
        rw [h2]
        exact le_of_lt hy2
    · have hx1 : ‖x‖ ≤ (j : ℝ) + 1 := mem_closedBall_zero_iff.1 hx.1
      have hx2 : ENNReal.ofReal (1 / ((j : ℝ) + 1)) ≤ infEDist x Uᶜ := hx.2
      exact ⟨mem_ball_zero_iff.2 (by linarith), lt_of_lt_of_le h12 hx2⟩
  -- (iii) Monotonicity from `Q j ⊆ interior (Q (j+1)) ⊆ Q (j+1)`.
  have hQm : Monotone Q := monotone_nat_of_le_succ fun j ↦ (hQint j).trans interior_subset
  -- Every `x ∈ U` lies in some `Q j`: `infEDist x Uᶜ ≠ 0` because `Uᶜ` is closed.
  have hQcover (x : Rn n) (hx : x ∈ U) : ∃ j, x ∈ Q j := by
    have hx0 : infEDist x Uᶜ ≠ 0 := fun h ↦
      (mem_iff_infEDist_zero_of_closed hU.isClosed_compl).2 h hx
    obtain ⟨m, hm⟩ := ENNReal.exists_inv_nat_lt hx0
    obtain ⟨j, hj⟩ := exists_nat_ge (max ‖x‖ (m : ℝ))
    have hmj : m ≤ j + 1 := by
      have : (m : ℝ) ≤ j := (le_max_right _ _).trans hj
      have : m ≤ j := by exact_mod_cast this
      omega
    refine ⟨j, mem_closedBall_zero_iff.2 (by linarith [le_max_left ‖x‖ (m : ℝ)]), ?_⟩
    show ENNReal.ofReal (1 / ((j : ℝ) + 1)) ≤ infEDist x Uᶜ
    calc ENNReal.ofReal (1 / ((j : ℝ) + 1)) = ((j + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
          rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity : (0 : ℝ) < (j : ℝ) + 1),
            ← Nat.cast_succ, ENNReal.ofReal_natCast]
      _ ≤ (m : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 (Nat.cast_le.2 hmj)
      _ ≤ infEDist x Uᶜ := hm.le
  -- (iv) The increasing open sets `interior (Q (j+1))` cover a compact `K ⊆ U`, so one of them
  -- contains `K`.
  refine ⟨Q, hQc, hQU, hQm, fun K hK hKU ↦ ?_⟩
  obtain ⟨j, hj⟩ := hK.elim_directed_cover (fun j ↦ interior (Q (j + 1)))
    (fun _ ↦ isOpen_interior)
    (fun x hx ↦ by
      obtain ⟨j, hj⟩ := hQcover x (hKU hx)
      exact mem_iUnion.2 ⟨j, hQint j hj⟩)
    (directed_of_isDirected_le fun i j hij ↦ interior_mono (hQm (Nat.succ_le_succ hij)))
  exact ⟨j + 1, hj.trans interior_subset⟩
/-- **One subsequence converging in `L¹` on countably many sets** (steps 0 and 2–4 of the diagonal
extraction in the proof of Simon 2.6). Let `Qⱼ ⊆ ℝⁿ` (`j ∈ ℕ`) be arbitrary sets and let every `u_k`
be integrable on every `Qⱼ`. Suppose that for every `j` and `ε > 0` finitely many `u_i` form an
`ε`-net of `{u_k}` for `∫_{Qⱼ} |· - ·|`. Then one strictly increasing `ψ` and functions `Gⱼ`, each
integrable on `Qⱼ`, satisfy `∫_{Qⱼ} |u_{ψ(k)} - Gⱼ| → 0` for every `j`. The classes
`[u_k] ∈ L¹(Qⱼ)` form a totally bounded set, so its closure `Cⱼ` is compact in the complete space
`L¹(Qⱼ)`. By Tychonoff `∏ⱼ Cⱼ` is compact in the first-countable space `∏ⱼ L¹(Qⱼ)`, so the sequence
`k ↦ ([u_k])ⱼ` has a convergent subsequence; `Gⱼ` is a representative of its `j`-th limit. -/
theorem Submission.bv_exists_subseq_tendsto_lintegral_of_finite_nets : ∀ (n : ℕ) (Q : ℕ → Set (Rn n)) (u : ℕ → Rn n → ℝ), (∀ j k, IntegrableOn (u k) (Q j) volume) → (∀ j, ∀ ε : ℝ, 0 < ε → ∃ F : Finset ℕ, ∀ k, ∃ i ∈ F, (∫⁻ x in Q j, ‖u k x - u i x‖ₑ) < ENNReal.ofReal ε) → ∃ (ψ : ℕ → ℕ) (G : ℕ → Rn n → ℝ), StrictMono ψ ∧ (∀ j, IntegrableOn (G j) (Q j) volume) ∧ ∀ j, Tendsto (fun k ↦ ∫⁻ x in Q j, ‖u (ψ k) x - G j x‖ₑ) atTop (𝓝 0) := by
  intro n Q u hint hnet
  -- Step 1: `f j k = [u k]` in the complete space `L¹(Q j)`.
  have hmem : ∀ j k, MemLp (u k) 1 (volume.restrict (Q j)) :=
    fun j k ↦ memLp_one_iff_integrable.2 (hint j k)
  let f : (j : ℕ) → ℕ → Lp ℝ 1 (volume.restrict (Q j)) := fun j k ↦ (hmem j k).toLp (u k)
  -- Step 2: the `L¹(Q j)` distances are the lower integrals of the hypotheses.
  have hdist : ∀ j k i, edist (f j k) (f j i) = ∫⁻ x in Q j, ‖u k x - u i x‖ₑ := by
    intro j k i
    rw [Lp.edist_toLp_toLp, eLpNorm_one_eq_lintegral_enorm
      ((hint j k).aestronglyMeasurable.sub (hint j i).aestronglyMeasurable)]
    rfl
  -- Step 3: the finite nets make `range (f j)` totally bounded, so its closure is compact.
  have htb : ∀ j, TotallyBounded (range (f j)) := by
    intro j
    rw [totallyBounded_iff]
    intro ε hε
    obtain ⟨F, hF⟩ := hnet j ε hε
    refine ⟨f j '' F, F.finite_toSet.image _, ?_⟩
    rintro _ ⟨k, rfl⟩
    obtain ⟨i, hiF, hi⟩ := hF k
    refine mem_iUnion₂.2 ⟨f j i, mem_image_of_mem _ hiF, ?_⟩
    rw [mem_ball, dist_edist]
    exact ENNReal.toReal_lt_of_lt_ofReal (by rw [hdist]; exact hi)
  have hcpt : ∀ j, IsCompact (closure (range (f j))) :=
    fun j ↦ (htb j).closure.isCompact_of_isClosed isClosed_closure
  -- Step 4: Tychonoff and sequential compactness in the first-countable product `∏ j, L¹(Q j)`.
  obtain ⟨a, -, ψ, hψ, hlim⟩ := (isCompact_univ_pi hcpt).tendsto_subseq
    (x := fun k j ↦ f j k) fun k ↦ mem_univ_pi.2 fun j ↦ subset_closure (mem_range_self k)
  -- Step 5: `G j = ⇑(a j)` is integrable on `Q j` and `f j (ψ k) → a j` in `L¹(Q j)`.
  refine ⟨ψ, fun j ↦ ⇑(a j), hψ, fun j ↦ memLp_one_iff_integrable.1 (Lp.memLp (a j)), fun j ↦ ?_⟩
  have h1 : Tendsto (fun k ↦ edist (f j (ψ k)) (a j)) atTop (𝓝 0) :=
    tendsto_iff_edist_tendsto_0.1 (tendsto_pi_nhds.1 hlim j)
  refine h1.congr fun k ↦ ?_
  rw [Lp.edist_def, eLpNorm_one_eq_lintegral_enorm
    ((Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _))]
  refine lintegral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (hmem j (ψ k))] with x hx
  simp only [f, Pi.sub_apply, hx]
/-- **Gluing compatible `L¹` limits along a compact exhaustion** (steps 5–8 of the diagonal extraction
in the proof of Simon 2.6). Let `U ⊆ ℝⁿ` be open and `Q₀ ⊆ Q₁ ⊆ ⋯` compact sets such that every
compact `K ⊆ U` lies in some `Qⱼ`. If every `w_k` is a.e.-strongly measurable on every `Qⱼ`, every
`Gⱼ` is integrable on `Qⱼ` and `∫_{Qⱼ} |w_k - Gⱼ| → 0` as `k → ∞`, then `w_k → v` in `L¹_loc(U)` for
some `v` that is locally integrable on `U`. For `i ≤ j` the triangle inequality gives
`∫_{Qᵢ} |Gᵢ - Gⱼ| ≤ ∫_{Qᵢ} |w_k - Gᵢ| + ∫_{Qⱼ} |w_k - Gⱼ| → 0`, so `Gᵢ = Gⱼ` a.e. on `Qᵢ`. Hence
`v(x) = G_{j(x)}(x)`, where `j(x)` is the least `j` with `x ∈ Qⱼ` (and `v = 0` off `⋃ⱼ Qⱼ`),
agrees with `Gⱼ` a.e. on every `Qⱼ`. -/
theorem Submission.bv_tendstoLocallyInL1On_of_exhaustion_limits : ∀ (n : ℕ) (U : Set (Rn n)) (Q : ℕ → Set (Rn n)) (w G : ℕ → Rn n → ℝ), IsOpen U → (∀ j, IsCompact (Q j)) → Monotone Q → (∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ j, K ⊆ Q j) → (∀ j k, AEStronglyMeasurable (w k) (volume.restrict (Q j))) → (∀ j, IntegrableOn (G j) (Q j) volume) → (∀ j, Tendsto (fun k ↦ ∫⁻ x in Q j, ‖w k x - G j x‖ₑ) atTop (𝓝 0)) → ∃ v : Rn n → ℝ, LocallyIntegrableOn v U volume ∧ Chapter02.TendstoLocallyInL1On w v U atTop := by
  intro n U Q w G hU hQc hQm hcof hw hG hlim
  -- Step 0: every `Q j` is compact, hence closed and measurable.
  have hQmeas : ∀ j, MeasurableSet (Q j) := fun j ↦ (hQc j).isClosed.measurableSet
  -- Step 1: compatibility, `G i = G j` a.e. on `Q i` for `i ≤ j`.
  have compat : ∀ i j, i ≤ j → G i =ᵐ[volume.restrict (Q i)] G j := by
    intro i j hij
    have hsub : Q i ⊆ Q j := hQm hij
    have hGi : AEStronglyMeasurable (G i) (volume.restrict (Q i)) := (hG i).aestronglyMeasurable
    have hGj : AEStronglyMeasurable (G j) (volume.restrict (Q i)) :=
      (hG j).aestronglyMeasurable.mono_measure (Measure.restrict_mono hsub le_rfl)
    have hbound : ∀ k, ∫⁻ x in Q i, ‖G i x - G j x‖ₑ ≤
        (∫⁻ x in Q i, ‖w k x - G i x‖ₑ) + ∫⁻ x in Q j, ‖w k x - G j x‖ₑ := by
      intro k
      calc ∫⁻ x in Q i, ‖G i x - G j x‖ₑ
          ≤ ∫⁻ x in Q i, (‖w k x - G i x‖ₑ + ‖w k x - G j x‖ₑ) := by
            refine lintegral_mono fun x ↦ ?_
            calc ‖G i x - G j x‖ₑ = ‖(w k x - G j x) - (w k x - G i x)‖ₑ := by congr 1; ring
              _ ≤ ‖w k x - G j x‖ₑ + ‖w k x - G i x‖ₑ := enorm_sub_le
              _ = ‖w k x - G i x‖ₑ + ‖w k x - G j x‖ₑ := add_comm _ _
        _ = (∫⁻ x in Q i, ‖w k x - G i x‖ₑ) + ∫⁻ x in Q i, ‖w k x - G j x‖ₑ :=
            lintegral_add_left' ((hw i k).sub hGi).enorm _
        _ ≤ (∫⁻ x in Q i, ‖w k x - G i x‖ₑ) + ∫⁻ x in Q j, ‖w k x - G j x‖ₑ :=
            add_le_add le_rfl (lintegral_mono_set hsub)
    have hzero : ∫⁻ x in Q i, ‖G i x - G j x‖ₑ = 0 := by
      have hT : Tendsto (fun k ↦ (∫⁻ x in Q i, ‖w k x - G i x‖ₑ) +
          ∫⁻ x in Q j, ‖w k x - G j x‖ₑ) atTop (𝓝 0) := by
        simpa using (hlim i).add (hlim j)
      exact le_antisymm (ge_of_tendsto' hT hbound) zero_le
    filter_upwards [(lintegral_eq_zero_iff' (hGi.sub hGj).enorm).1 hzero] with x hx
    simpa [sub_eq_zero] using hx
  -- Step 2: gluing, `v x = G (j x) x` with `j x` the least `j` such that `x ∈ Q j`.
  classical
  let v : Rn n → ℝ := fun x ↦ if h : ∃ j, x ∈ Q j then G (Nat.find h) x else 0
  have hv : ∀ j, v =ᵐ[volume.restrict (Q j)] G j := by
    intro j
    have h1 : ∀ i, ∀ᵐ x ∂(volume : Measure (Rn n)), i ≤ j → x ∈ Q i → G i x = G j x := by
      intro i
      by_cases hij : i ≤ j
      · filter_upwards [(ae_restrict_iff' (hQmeas i)).1 (compat i j hij)] with x hx _ hxi
        exact hx hxi
      · exact Eventually.of_forall fun x h ↦ absurd h hij
    rw [EventuallyEq, ae_restrict_iff' (hQmeas j)]
    filter_upwards [ae_all_iff.2 h1] with x hx hxj
    have hex : ∃ j, x ∈ Q j := ⟨j, hxj⟩
    simp only [v, hex, ↓reduceDIte]
    exact hx _ (Nat.find_min' hex hxj) (Nat.find_spec hex)
  -- Step 3: `v` is integrable on every `Q j`.
  have hvint : ∀ j, IntegrableOn v (Q j) volume := fun j ↦ (hG j).congr_fun_ae (hv j).symm
  refine ⟨v, ?_, ?_⟩
  · -- Step 5: local integrability on the open set `U`.
    rw [locallyIntegrableOn_iff hU.isLocallyClosed]
    intro K hKU hK
    obtain ⟨j, hj⟩ := hcof K hK hKU
    exact (hvint j).mono_set hj
  · -- Step 4: convergence on every compact `K ⊆ U`, squeezed by `∫⁻_{Q j} ‖w k - G j‖ₑ → 0`.
    intro K hK hKU
    obtain ⟨j, hj⟩ := hcof K hK hKU
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hlim j)
      (fun _ ↦ zero_le) fun k ↦ ?_
    calc ∫⁻ x in K, ‖w k x - v x‖ₑ ≤ ∫⁻ x in Q j, ‖w k x - v x‖ₑ := lintegral_mono_set hj
      _ = ∫⁻ x in Q j, ‖w k x - G j x‖ₑ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hv j] with x hx
        rw [hx]

/-- **Diagonal extraction in `L¹_loc(U)`** (step A2 of the proof of Simon Ch. 2, Theorem 2.6,
p. 50). Let `U ⊆ ℝⁿ` be open and every `u_k` locally integrable on `U`. Suppose that for every
compact `Q ⊆ U` and `ε > 0` finitely many `u_j` form an `ε`-net of `{u_k}` for `∫_Q |· - ·|`. Then a
subsequence `u_{ψ(k)}` converges in `L¹_loc(U)` to some `v` that is locally integrable on `U`.
Choose a compact exhaustion `Q₀ ⊆ Q₁ ⊆ ⋯` of `U`; every `u_k` is integrable on every `Qⱼ`, so one
strictly increasing `ψ` and functions `Gⱼ` satisfy `∫_{Qⱼ} |u_{ψ(k)} - Gⱼ| → 0` for every `j`, and
the `Gⱼ` glue to the limit `v`. -/
theorem Submission.bv_exists_subseq_tendstoLocallyInL1On : ∀ (n : ℕ) (U : Set (Rn n)) (u : ℕ → Rn n → ℝ), IsOpen U → (∀ k, LocallyIntegrableOn (u k) U volume) → (∀ Q : Set (Rn n), IsCompact Q → Q ⊆ U → ∀ ε : ℝ, 0 < ε → ∃ F : Finset ℕ, ∀ k, ∃ j ∈ F, (∫⁻ x in Q, ‖u k x - u j x‖ₑ) < ENNReal.ofReal ε) → ∃ (ψ : ℕ → ℕ) (v : Rn n → ℝ), StrictMono ψ ∧ LocallyIntegrableOn v U volume ∧ Chapter02.TendstoLocallyInL1On (fun k ↦ u (ψ k)) v U atTop := by
  intro n U u hU hloc hnet
  -- Step 1: a compact exhaustion `Q 0 ⊆ Q 1 ⊆ ⋯` of `U`.
  obtain ⟨Q, hQc, hQU, hQm, hcof⟩ := Submission.bv_isOpen_exists_compact_exhaustion n U hU
  -- Every `u k` is integrable on every compact `Q j ⊆ U`.
  have hint : ∀ j k, IntegrableOn (u k) (Q j) volume :=
    fun j k ↦ (hloc k).integrableOn_compact_subset (hQU j) (hQc j)
  -- Steps 2–4: the finite nets on each `Q j` give one subsequence converging in every `L¹(Q j)`.
  obtain ⟨ψ, G, hψ, hG, hlim⟩ := Submission.bv_exists_subseq_tendsto_lintegral_of_finite_nets n Q
    u hint fun j ε hε ↦ hnet (Q j) (hQc j) (hQU j) ε hε
  -- Steps 5–8: glue the compatible limits `G j` into `v`.
  obtain ⟨v, hv, hconv⟩ := Submission.bv_tendstoLocallyInL1On_of_exhaustion_limits n U Q
    (fun k ↦ u (ψ k)) G hU hQc hQm hcof (fun j k ↦ (hint j (ψ k)).aestronglyMeasurable) hG hlim
  exact ⟨ψ, v, hψ, hv, hconv⟩
/-- **L¹ translation estimate for `C¹` functions (Simon Ch. 2, Lemma 2.5, mollifier estimate).**
Let `w : ℝⁿ → ℝ` be `C¹`, `Q ⊆ ℝⁿ` any set, `z ∈ ℝⁿ` and `M ∈ [0, ∞]`. If
`∫_{Q - s z} |Dw| ≤ M` for every `s ∈ [0, 1]`, then `∫_Q |w(x - z) - w(x)| dx ≤ |z| M`. By the
fundamental theorem of calculus along `s ↦ x - s z`, `|w(x - z) - w(x)| ≤ |z| ∫₀¹ |Dw(x - s z)| ds`.
Integrate over `Q`, swap the integrals by Tonelli (the integrand is continuous in `(x, s)`) and
translate `Q` by `-s z`, which preserves Lebesgue measure. -/
theorem Submission.bv_translate_sub_lintegral_le_of_fderiv : ∀ (n : ℕ) (w : Rn n → ℝ) (Q : Set (Rn n)) (z : Rn n) (M : ℝ≥0∞), ContDiff ℝ 1 w → (∀ s ∈ Icc (0 : ℝ) 1, ∫⁻ y in (fun x ↦ x - s • z) '' Q, ‖fderiv ℝ w y‖ₑ ≤ M) → ∫⁻ x in Q, ‖w (x - z) - w x‖ₑ ≤ ENNReal.ofReal ‖z‖ * M := by
  intro n w Q z M hw hM
  -- Step 1 (regularity): `w` is differentiable and `Dw` is continuous.
  have hdiff : Differentiable ℝ w := hw.differentiable one_ne_zero
  have hcont : Continuous (fderiv ℝ w) := hw.continuous_fderiv one_ne_zero
  -- Step 2 (pointwise FTC bound along the segment `s ↦ x - s • z`, `s ∈ [0, 1]`).
  have hpt : ∀ x, ‖w (x - z) - w x‖ₑ ≤
      ENNReal.ofReal ‖z‖ * ∫⁻ s in Icc (0 : ℝ) 1, ‖fderiv ℝ w (x - s • z)‖ₑ := by
    intro x
    have hderiv : ∀ s : ℝ,
        HasDerivAt (fun s : ℝ ↦ w (x - s • z)) (fderiv ℝ w (x - s • z) (-z)) s := by
      intro s
      have hline : HasDerivAt (fun s : ℝ ↦ x - s • z) (-z) s := by
        simpa using ((hasDerivAt_id' s).smul_const z).const_sub x
      exact (hdiff (x - s • z)).hasFDerivAt.comp_hasDerivAt s hline
    have hgc : Continuous fun s : ℝ ↦ fderiv ℝ w (x - s • z) (-z) :=
      (hcont.comp (continuous_const.sub (continuous_id.smul continuous_const))).clm_apply
        continuous_const
    have heq : w (x - z) - w x = ∫ s in Ioc (0 : ℝ) 1, fderiv ℝ w (x - s • z) (-z) := by
      rw [← intervalIntegral.integral_of_le zero_le_one,
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hderiv s)
          (hgc.intervalIntegrable 0 1)]
      simp
    rw [heq]
    calc ‖∫ s in Ioc (0 : ℝ) 1, fderiv ℝ w (x - s • z) (-z)‖ₑ
        ≤ ∫⁻ s in Ioc (0 : ℝ) 1, ‖fderiv ℝ w (x - s • z) (-z)‖ₑ :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ s in Icc (0 : ℝ) 1, ‖fderiv ℝ w (x - s • z) (-z)‖ₑ :=
          lintegral_mono_set Ioc_subset_Icc_self
      _ ≤ ∫⁻ s in Icc (0 : ℝ) 1, ENNReal.ofReal ‖z‖ * ‖fderiv ℝ w (x - s • z)‖ₑ := by
          refine lintegral_mono fun s ↦ ?_
          calc ‖fderiv ℝ w (x - s • z) (-z)‖ₑ ≤ ‖fderiv ℝ w (x - s • z)‖ₑ * ‖-z‖ₑ :=
                ContinuousLinearMap.le_opENorm _ _
            _ = ENNReal.ofReal ‖z‖ * ‖fderiv ℝ w (x - s • z)‖ₑ := by
                rw [enorm_neg, mul_comm, ofReal_norm]
      _ = ENNReal.ofReal ‖z‖ * ∫⁻ s in Icc (0 : ℝ) 1, ‖fderiv ℝ w (x - s • z)‖ₑ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  -- Step 4 (joint measurability): `(x, s) ↦ ‖Dw(x - s • z)‖ₑ` is continuous.
  have hmeas : AEMeasurable (Function.uncurry fun x (s : ℝ) ↦ ‖fderiv ℝ w (x - s • z)‖ₑ)
      ((volume.restrict Q).prod (volume.restrict (Icc (0 : ℝ) 1))) :=
    (hcont.comp (continuous_fst.sub (continuous_snd.smul continuous_const))).enorm.aemeasurable
  -- Step 5 (translation invariance): `x ↦ x - s • z` is a measure-preserving embedding.
  have htr : ∀ s ∈ Icc (0 : ℝ) 1, ∫⁻ x in Q, ‖fderiv ℝ w (x - s • z)‖ₑ ≤ M := fun s hs ↦
    ((measurePreserving_sub_right (volume : Measure (Rn n)) (s • z)).setLIntegral_comp_emb
      (measurableEmbedding_subRight (s • z)) (fun y ↦ ‖fderiv ℝ w y‖ₑ) Q).le.trans (hM s hs)
  -- Steps 3 and 6: integrate over `Q`, swap by Tonelli and use `volume [0, 1] = 1`.
  calc ∫⁻ x in Q, ‖w (x - z) - w x‖ₑ
      ≤ ∫⁻ x in Q, ENNReal.ofReal ‖z‖ * ∫⁻ s in Icc (0 : ℝ) 1, ‖fderiv ℝ w (x - s • z)‖ₑ :=
        lintegral_mono hpt
    _ = ENNReal.ofReal ‖z‖ * ∫⁻ x in Q, ∫⁻ s in Icc (0 : ℝ) 1, ‖fderiv ℝ w (x - s • z)‖ₑ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal ‖z‖ * ∫⁻ s in Icc (0 : ℝ) 1, ∫⁻ x in Q, ‖fderiv ℝ w (x - s • z)‖ₑ := by
        rw [lintegral_lintegral_swap hmeas]
    _ ≤ ENNReal.ofReal ‖z‖ * ∫⁻ _ in Icc (0 : ℝ) 1, M :=
        mul_le_mul' le_rfl (setLIntegral_mono' measurableSet_Icc htr)
    _ = ENNReal.ofReal ‖z‖ * M := by
        rw [setLIntegral_const, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one]
/-- **`L¹` translation estimates pass to `L¹` limits** (Simon Ch. 2, proof of Theorem 2.6, the
mollification step). If `w j → F` in `L¹(ℝⁿ)` and `∫_Q |w j (x - z) - w j x| dx ≤ C` for every
`j`, then `∫_Q |F (x - z) - F x| dx ≤ C`. Splitting `F (x - z) - F x` through `w j` and using the
translation invariance of Lebesgue measure bounds the left side by `e j + C + e j`, where
`e j = ∫ |w j - F| → 0`. -/
theorem Submission.bv_translate_sub_lintegral_le_of_tendsto : ∀ (n : ℕ) (F : Rn n → ℝ) (w : ℕ → Rn n → ℝ) (Q : Set (Rn n)) (z : Rn n) (C : ℝ≥0∞), AEStronglyMeasurable F volume → (∀ j, AEStronglyMeasurable (w j) volume) → Tendsto (fun j ↦ ∫⁻ x, ‖w j x - F x‖ₑ) atTop (𝓝 0) → (∀ j, ∫⁻ x in Q, ‖w j (x - z) - w j x‖ₑ ≤ C) → ∫⁻ x in Q, ‖F (x - z) - F x‖ₑ ≤ C := by
  intro n F w Q z C hF hw he hC
  -- Step 1: the translation `x ↦ x - z` preserves Lebesgue measure.
  have hT : MeasurePreserving (fun x : Rn n ↦ x - z) volume volume :=
    measurePreserving_sub_right volume z
  -- Steps 2–4: for every `j`, `∫⁻_Q ‖F (x - z) - F x‖ₑ ≤ e_j + C + e_j`.
  have hbound : ∀ j, ∫⁻ x in Q, ‖F (x - z) - F x‖ₑ ≤
      (∫⁻ x, ‖w j x - F x‖ₑ) + C + ∫⁻ x, ‖w j x - F x‖ₑ := by
    intro j
    have hFz : AEStronglyMeasurable (fun x ↦ F (x - z)) volume := hF.comp_measurePreserving hT
    have hwz : AEStronglyMeasurable (fun x ↦ w j (x - z)) volume :=
      (hw j).comp_measurePreserving hT
    have ha : AEMeasurable (fun x ↦ ‖F (x - z) - w j (x - z)‖ₑ) (volume.restrict Q) :=
      (hFz.sub hwz).enorm.restrict
    have hab : AEMeasurable (fun x ↦ ‖F (x - z) - w j (x - z)‖ₑ + ‖w j (x - z) - w j x‖ₑ)
        (volume.restrict Q) :=
      ha.add (hwz.sub (hw j)).enorm.restrict
    have htr : ∫⁻ x, ‖F (x - z) - w j (x - z)‖ₑ = ∫⁻ x, ‖w j x - F x‖ₑ :=
      calc ∫⁻ x, ‖F (x - z) - w j (x - z)‖ₑ = ∫⁻ y, ‖F y - w j y‖ₑ :=
            lintegral_sub_right_eq_self (fun y ↦ ‖F y - w j y‖ₑ) z
        _ = ∫⁻ y, ‖w j y - F y‖ₑ := lintegral_congr fun y ↦ enorm_sub_rev _ _
    calc ∫⁻ x in Q, ‖F (x - z) - F x‖ₑ
        ≤ ∫⁻ x in Q, (‖F (x - z) - w j (x - z)‖ₑ + ‖w j (x - z) - w j x‖ₑ +
            ‖w j x - F x‖ₑ) := by
          refine lintegral_mono fun x ↦ ?_
          have h : F (x - z) - F x =
              (F (x - z) - w j (x - z)) + (w j (x - z) - w j x) + (w j x - F x) := by ring
          rw [h]
          exact enorm_add₃_le
      _ = (∫⁻ x in Q, ‖F (x - z) - w j (x - z)‖ₑ) + (∫⁻ x in Q, ‖w j (x - z) - w j x‖ₑ) +
            ∫⁻ x in Q, ‖w j x - F x‖ₑ := by
          rw [lintegral_add_left' hab, lintegral_add_left' ha]
      _ ≤ (∫⁻ x, ‖w j x - F x‖ₑ) + C + ∫⁻ x, ‖w j x - F x‖ₑ :=
          add_le_add (add_le_add ((setLIntegral_le_lintegral Q _).trans htr.le) (hC j))
            (setLIntegral_le_lintegral Q _)
  -- Step 5: `e_j + C + e_j → 0 + C + 0 = C` in `ℝ≥0∞`, and the left side does not depend on `j`.
  have hlim : Tendsto (fun j ↦ (∫⁻ x, ‖w j x - F x‖ₑ) + C + ∫⁻ x, ‖w j x - F x‖ₑ) atTop
      (𝓝 C) := by
    have h := (he.add (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ C) atTop (𝓝 C))).add he
    rwa [zero_add, add_zero] at h
  exact ge_of_tendsto' hlim hbound
/-- **Kernel average of translations** (the mollification estimate in the proof of Simon Ch. 2,
Theorem 2.6, p. 50; cf. [GT01, Thm 7.22]). Let `F ∈ L¹(ℝⁿ)` and let `ρ` be a continuous kernel
with `ρ ≥ 0`, `support ρ ⊆ ball 0 σ` and `∫ ρ = 1`. If `∫_Q |F(x - t) - F(x)| dx ≤ C` for every
`|t| < σ`, then `∫_Q |ρ * F - F| ≤ C`, for any `Q ⊆ ℝⁿ` and `C ∈ [0, ∞]`. Since `∫ ρ = 1`,
`(ρ * F)(x) - F(x) = ∫ ρ(t) (F(x - t) - F(x)) dt`. Integrate over `Q`, swap the integrals by
Tonelli (joint measurability via quasi-measure-preserving subtraction) and use the bound for each
`t` with `ρ t ≠ 0`. Then `∫ ρ = 1` bounds the total by `C`. -/
theorem Submission.bv_convolution_sub_lintegral_le_of_translate : ∀ (n : ℕ) (F ρ : Rn n → ℝ) (Q : Set (Rn n)) (σ : ℝ) (C : ℝ≥0∞), Integrable F volume → Continuous ρ → (∀ x, 0 ≤ ρ x) → Function.support ρ ⊆ ball 0 σ → ∫ x, ρ x = 1 → (∀ t : Rn n, ‖t‖ < σ → ∫⁻ x in Q, ‖F (x - t) - F x‖ₑ ≤ C) → ∫⁻ x in Q, ‖convolution ρ F (ContinuousLinearMap.lsmul ℝ ℝ) volume x - F x‖ₑ ≤ C := by
  intro n F ρ Q σ C hF hρc hρn hρs hρi hT
  -- Step 1 (kernel facts): `ρ` is supported in the compact `closedBall 0 σ`, so it is integrable.
  have hρcs : HasCompactSupport ρ :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Rn n) σ)
      (hρs.trans ball_subset_closedBall)
  have hρint : Integrable ρ volume := hρc.integrable_of_hasCompactSupport hρcs
  -- Step 2 (pointwise representation): since `∫ ρ = 1`,
  -- `(ρ * F)(x) - F(x) = ∫ ρ(t) (F(x - t) - F(x)) dt`.
  have hpt : ∀ x, ‖convolution ρ F (ContinuousLinearMap.lsmul ℝ ℝ) volume x - F x‖ₑ ≤
      ∫⁻ t, ‖ρ t‖ₑ * ‖F (x - t) - F x‖ₑ := by
    intro x
    have h1 : Integrable (fun t ↦ ρ t * F (x - t)) volume := by
      simpa [ConvolutionExistsAt] using
        hρcs.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hρc hF.locallyIntegrable x
    have h2 : Integrable (fun t ↦ ρ t * F x) volume := hρint.mul_const _
    have heq : convolution ρ F (ContinuousLinearMap.lsmul ℝ ℝ) volume x - F x =
        ∫ t, (ρ t * F (x - t) - ρ t * F x) := by
      rw [integral_sub h1 h2, integral_mul_const, hρi, one_mul, convolution_lsmul]
      simp only [smul_eq_mul]
    rw [heq]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun t ↦ ?_
    rw [← mul_sub, enorm_mul]
  -- Step 3 (joint measurability): `(x, t) ↦ x - t` and `(x, t) ↦ x` are quasi-measure-preserving,
  -- and `volume.restrict Q ⊗ volume ≪ volume ⊗ volume`.
  have hmeas : AEMeasurable (Function.uncurry fun x t ↦ ‖ρ t‖ₑ * ‖F (x - t) - F x‖ₑ)
      ((volume.restrict Q).prod volume) := by
    have hsub : Measure.QuasiMeasurePreserving (fun p : Rn n × Rn n ↦ p.1 - p.2)
        (volume.prod volume) volume :=
      quasiMeasurePreserving_sub_of_right_invariant volume volume
    have hA : AEStronglyMeasurable (fun p : Rn n × Rn n ↦ F (p.1 - p.2) - F p.1)
        (volume.prod volume) :=
      (hF.aestronglyMeasurable.comp_quasiMeasurePreserving hsub).sub
        (hF.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst)
    have hB : AEMeasurable (fun p : Rn n × Rn n ↦ ‖ρ p.2‖ₑ * ‖F (p.1 - p.2) - F p.1‖ₑ)
        (volume.prod volume) :=
      (hρc.measurable.enorm.comp measurable_snd).aemeasurable.mul hA.enorm
    exact hB.mono_ac ((Measure.absolutelyContinuous_of_le Measure.restrict_le_self).prod
      Measure.AbsolutelyContinuous.rfl)
  -- Total mass of the kernel: `∫⁻ ‖ρ‖ₑ = ofReal (∫ ρ) = 1`.
  have hρ1 : ∫⁻ t, ‖ρ t‖ₑ = 1 := by
    have h1 := ofReal_integral_eq_lintegral_ofReal hρint (Eventually.of_forall hρn)
    rw [hρi, ENNReal.ofReal_one] at h1
    rw [h1]
    exact lintegral_congr fun t ↦ Real.enorm_eq_ofReal (hρn t)
  -- Steps 4–6: integrate over `Q`, swap by Tonelli, and use the translation bound where
  -- `ρ t ≠ 0`, i.e. for `‖t‖ < σ`.
  calc ∫⁻ x in Q, ‖convolution ρ F (ContinuousLinearMap.lsmul ℝ ℝ) volume x - F x‖ₑ
      ≤ ∫⁻ x in Q, ∫⁻ t, ‖ρ t‖ₑ * ‖F (x - t) - F x‖ₑ := lintegral_mono hpt
    _ = ∫⁻ t, ∫⁻ x in Q, ‖ρ t‖ₑ * ‖F (x - t) - F x‖ₑ := lintegral_lintegral_swap hmeas
    _ = ∫⁻ t, ‖ρ t‖ₑ * ∫⁻ x in Q, ‖F (x - t) - F x‖ₑ :=
        lintegral_congr fun t ↦ lintegral_const_mul' _ _ enorm_ne_top
    _ ≤ ∫⁻ t, ‖ρ t‖ₑ * C := by
        refine lintegral_mono fun t ↦ ?_
        by_cases ht : ρ t = 0
        · simp [ht]
        · gcongr
          exact hT t (mem_ball_zero_iff.1 (hρs ht))
    _ = (∫⁻ t, ‖ρ t‖ₑ) * C := lintegral_mul_const'' _ hρint.aestronglyMeasurable.enorm
    _ = C := by rw [hρ1, one_mul]
/-- **Simon Ch. 2, Lemma 2.5 (`L¹` part), convergence of mollifiers.** If `F ∈ L¹(ℝⁿ)` and the
kernels `ρ j` are continuous, nonnegative, of integral `1` and supported in the open ball
`ball 0 (σ j)` with `σ j → 0`, then `ρ j * F → F` in `L¹`. The `L¹` contraction
`‖ρ j * G‖₁ ≤ ‖G‖₁` (Tonelli and translation invariance) and the density of compactly supported
continuous `g` in `L¹` (inner and outer regularity, Urysohn, `MemLp.induction_dense`) reduce it
to such `g`, for which `ρ j * g → g` uniformly (`dist_convolution_le`) and both vanish off a
fixed ball. -/
theorem Submission.bv_mollifier_tendsto_L1 : ∀ (n : ℕ) (F : Rn n → ℝ) (ρ : ℕ → Rn n → ℝ) (σ : ℕ → ℝ), Integrable F volume → (∀ j, Continuous (ρ j)) → (∀ j x, 0 ≤ ρ j x) → (∀ j, Function.support (ρ j) ⊆ ball 0 (σ j)) → (∀ j, ∫ x, ρ j x = 1) → Tendsto σ atTop (𝓝 0) → Tendsto (fun j ↦ ∫⁻ x, ‖convolution (ρ j) F (ContinuousLinearMap.lsmul ℝ ℝ) volume x - F x‖ₑ) atTop (𝓝 0) := by
  intro n F ρ σ hF hρc hρn hρs hρi hσ
  -- Step 1 (L¹ contraction): `∫⁻ |ρ_j * G| ≤ ∫⁻ |G|` for integrable `G`, by Tonelli and
  -- translation invariance, since `∫⁻ |ρ_j| = ∫ ρ_j = 1`.
  have hcontr : ∀ j (G : Rn n → ℝ), Integrable G volume →
      ∫⁻ x, ‖convolution (ρ j) G (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ ≤ ∫⁻ x, ‖G x‖ₑ := by
    intro j G hG
    have hρ : Integrable (ρ j) volume := integrable_of_integral_eq_one (hρi j)
    have hmeas : AEStronglyMeasurable
        (fun p : Rn n × Rn n ↦ ContinuousLinearMap.lsmul ℝ ℝ (ρ j p.2) (G (p.1 - p.2)))
        (volume.prod volume) :=
      hρ.aestronglyMeasurable.convolution_integrand _ hG.aestronglyMeasurable
    have hρ1 : ∫⁻ t, ‖ρ j t‖ₑ = 1 := by
      have h1 := ofReal_integral_eq_lintegral_ofReal hρ (Eventually.of_forall (hρn j))
      rw [hρi j, ENNReal.ofReal_one] at h1
      rw [h1]
      exact lintegral_congr fun t ↦ Real.enorm_eq_ofReal (hρn j t)
    calc ∫⁻ x, ‖convolution (ρ j) G (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ
        ≤ ∫⁻ x, ∫⁻ t, ‖ContinuousLinearMap.lsmul ℝ ℝ (ρ j t) (G (x - t))‖ₑ :=
          lintegral_mono fun x ↦ enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ t, ∫⁻ x, ‖ContinuousLinearMap.lsmul ℝ ℝ (ρ j t) (G (x - t))‖ₑ :=
          lintegral_lintegral_swap hmeas.enorm
      _ = ∫⁻ t, ‖ρ j t‖ₑ * ∫⁻ x, ‖G x‖ₑ := by
          refine lintegral_congr fun t ↦ ?_
          simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, enorm_mul]
          rw [lintegral_const_mul' _ _ enorm_ne_top]
          congr 1
          exact lintegral_sub_right_eq_self (fun x ↦ ‖G x‖ₑ) t
      _ = (∫⁻ t, ‖ρ j t‖ₑ) * ∫⁻ x, ‖G x‖ₑ := lintegral_mul_const'' _ hρ.aestronglyMeasurable.enorm
      _ = ∫⁻ x, ‖G x‖ₑ := by rw [hρ1, one_mul]
  -- Step 2 (the `C_c` case): for `g` continuous with compact support, `ρ_j * g → g` uniformly
  -- (`dist_convolution_le` and uniform continuity) and both vanish off a fixed ball `S`.
  have hcc : ∀ g : Rn n → ℝ, Continuous g → HasCompactSupport g →
      Tendsto (fun j ↦ ∫⁻ x, ‖convolution (ρ j) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x - g x‖ₑ)
        atTop (𝓝 0) := by
    intro g hgc hgs
    obtain ⟨R, hR⟩ := hgs.isCompact.isBounded.subset_closedBall (0 : Rn n)
    have hgR : ∀ y, R < ‖y‖ → g y = 0 := by
      intro y hy
      refine image_eq_zero_of_notMem_tsupport fun hys ↦ ?_
      have h := hR hys
      rw [mem_closedBall, dist_zero_right] at h
      linarith
    set S : Set (Rn n) := closedBall (0 : Rn n) (R + 1) with hSdef
    have hSm : MeasurableSet S := measurableSet_closedBall
    have hSf : volume S ≠ ∞ := measure_closedBall_lt_top.ne
    have huc : UniformContinuous g := hgs.uniformContinuous_of_continuous hgc
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    obtain ⟨ε₀, hε₀, hε₀le⟩ : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ENNReal.ofReal ε₀ ≤ ε := by
      rcases eq_or_ne ε ∞ with h | h
      · exact ⟨1, one_pos, h ▸ le_top⟩
      · exact ⟨ε.toReal, ENNReal.toReal_pos hε.ne' h, (ENNReal.ofReal_toReal h).le⟩
    set m : ℝ := (volume S).toReal with hm
    have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
    set ε' : ℝ := ε₀ / (m + 1) with hε'eq
    have hε' : 0 < ε' := div_pos hε₀ (by linarith)
    obtain ⟨δ, hδ, hδg⟩ := Metric.uniformContinuous_iff.1 huc ε' hε'
    have hr : (0 : ℝ) < min δ 1 := lt_min hδ one_pos
    filter_upwards [hσ.eventually (Iio_mem_nhds hr)] with j hj
    have hjδ : σ j < δ := hj.trans_le (min_le_left _ _)
    have hj1 : σ j < 1 := hj.trans_le (min_le_right _ _)
    have hpt : ∀ x, ‖convolution (ρ j) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x - g x‖ₑ ≤
        S.indicator (fun _ ↦ ENNReal.ofReal ε') x := by
      intro x
      by_cases hx : x ∈ S
      · rw [indicator_of_mem hx]
        have hd := dist_convolution_le (μ := volume) (f := ρ j) (g := g) (x₀ := x) (R := σ j)
          (z₀ := g x) hε'.le (hρs j) (hρn j) (hρi j) hgc.aestronglyMeasurable
          (fun y hy ↦ (hδg ((mem_ball.1 hy).trans hjδ)).le)
        rw [dist_eq_norm] at hd
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal hd
      · rw [indicator_of_notMem hx]
        have hxR : R + 1 < ‖x‖ := by
          rw [hSdef, mem_closedBall, dist_zero_right, not_le] at hx
          exact hx
        have hconv : convolution (ρ j) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x = 0 := by
          rw [convolution_def]
          refine integral_eq_zero_of_ae (Eventually.of_forall fun t ↦ ?_)
          simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, Pi.zero_apply]
          by_cases ht : ρ j t = 0
          · rw [ht, zero_mul]
          · have htb : ‖t‖ < σ j := mem_ball_zero_iff.1 (hρs j ht)
            have hxt : ‖x‖ - ‖t‖ ≤ ‖x - t‖ := norm_sub_norm_le x t
            rw [hgR (x - t) (by linarith), mul_zero]
        rw [hconv, hgR x (by linarith), sub_zero, enorm_zero]
    calc ∫⁻ x, ‖convolution (ρ j) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x - g x‖ₑ
        ≤ ∫⁻ x, S.indicator (fun _ ↦ ENNReal.ofReal ε') x := lintegral_mono hpt
      _ = ENNReal.ofReal ε' * volume S := lintegral_indicator_const hSm _
      _ = ENNReal.ofReal (ε' * m) := by
          rw [ENNReal.ofReal_mul hε'.le, hm, ENNReal.ofReal_toReal hSf]
      _ ≤ ENNReal.ofReal ε₀ := by
          apply ENNReal.ofReal_le_ofReal
          rw [hε'eq, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
          nlinarith
      _ ≤ ε := hε₀le
  -- Step 3 (density of `C_c` in `L¹`): approximate indicators of finite-measure sets by inner
  -- (compact `K`) and outer (open `V`) regularity and an Urysohn function `K ≤ f ≤ V`, then
  -- extend to `L¹` by `MemLp.induction_dense`.
  have hdense : ∀ δ : ℝ≥0∞, δ ≠ 0 → ∃ g : Rn n → ℝ,
      eLpNorm (F - g) 1 volume ≤ δ ∧ (Continuous g ∧ HasCompactSupport g) := by
    intro δ hδ
    refine (memLp_one_iff_integrable.2 hF).induction_dense ENNReal.one_ne_top
      (fun g ↦ Continuous g ∧ HasCompactSupport g) ?_ ?_ hδ
    · intro c s hs hsfin ε hε
      obtain ⟨η, hηpos, hη⟩ := exists_Lp_half ℝ (volume : Measure (Rn n)) 1 hε
      obtain ⟨ζ, hζpos, hζ⟩ :=
        exists_eLpNorm_indicator_le (μ := (volume : Measure (Rn n))) ENNReal.one_ne_top c hηpos.ne'
      have hζpos' : (0 : ℝ≥0∞) < ζ := ENNReal.coe_pos.2 hζpos
      obtain ⟨K, hKs, hK, hKsmall⟩ := hs.exists_isCompact_sdiff_lt hsfin.ne hζpos'.ne'
      obtain ⟨V, hKV, hV, -, hVsmall⟩ :=
        hK.measurableSet.exists_isOpen_sdiff_lt (μ := volume) hK.measure_lt_top.ne hζpos'.ne'
      obtain ⟨f, hfK, hfc, hfV, hfI⟩ :=
        exists_continuousMap_one_of_isCompact_subset_isOpen hK hV hKV
      have hfzero : ∀ x ∉ V, f x = 0 := fun x hx ↦
        image_eq_zero_of_notMem_tsupport fun h ↦ hx (hfV h)
      have hgcont : Continuous (fun x ↦ f x * c) := f.continuous.mul continuous_const
      have hgc : HasCompactSupport (fun x ↦ f x * c) :=
        (show HasCompactSupport f from hfc).mul_right
      have hgmem : MemLp (fun x ↦ f x * c) 1 volume := hgcont.memLp_of_hasCompactSupport hgc
      have hdiff : ∀ x, ‖f x * c - K.indicator (fun _ ↦ c) x‖ ≤
          ‖(V \ K).indicator (fun _ ↦ c) x‖ := by
        intro x
        by_cases hxK : x ∈ K
        · simp [hxK, hfK hxK]
        · by_cases hxV : x ∈ V
          · simp only [indicator_of_notMem hxK, sub_zero,
              indicator_of_mem (mem_sdiff_of_mem hxV hxK), norm_mul, Real.norm_eq_abs,
              abs_of_nonneg (hfI x).1]
            exact mul_le_of_le_one_left (abs_nonneg c) (hfI x).2
          · simp [hxK, hxV, hfzero x hxV]
      have I1 : eLpNorm ((fun x ↦ f x * c) - K.indicator (fun _ ↦ c)) 1 volume ≤ η :=
        (eLpNorm_mono (hgmem.aestronglyMeasurable.sub
          (aestronglyMeasurable_const.indicator hK.measurableSet)) hdiff).trans
          (hζ _ hVsmall.le (hV.measurableSet.diff hK.measurableSet).nullMeasurableSet)
      have I2 : eLpNorm (K.indicator (fun _ ↦ c) - s.indicator (fun _ ↦ c)) 1 volume ≤ η := by
        rw [← eLpNorm_neg, neg_sub, ← indicator_sdiff hKs]
        exact hζ _ hKsmall.le (hs.diff hK.measurableSet).nullMeasurableSet
      refine ⟨fun x ↦ f x * c, ?_, hgcont, hgc⟩
      convert (hη _ _ I1 I2).le using 2
      ext x
      simp
    · intro f g hf hg
      exact ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  -- Step 4 (ε/3 argument): `ρ_j * F - F = ρ_j * (F - g) + (ρ_j * g - g) + (g - F)`.
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ : ℝ≥0∞, 0 < δ ∧ δ + (δ + δ) ≤ ε := by
    refine ⟨ε / 3, ENNReal.div_pos hε.ne' (by norm_num), ?_⟩
    have h3 : ε / 3 + (ε / 3 + ε / 3) = 3 * (ε / 3) := by ring
    rw [h3]
    exact ENNReal.mul_div_le
  obtain ⟨g, hgF, hg_cont, hg_supp⟩ := hdense δ hδpos.ne'
  have hg_int : Integrable g volume := hg_cont.integrable_of_hasCompactSupport hg_supp
  have hFg : Integrable (fun x ↦ F x - g x) volume := hF.sub hg_int
  have hg_close : ∫⁻ x, ‖F x - g x‖ₑ ≤ δ := by
    rwa [eLpNorm_one_eq_lintegral_enorm (hF.aestronglyMeasurable.sub hg_int.aestronglyMeasurable)]
      at hgF
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 (hcc g hg_cont hg_supp)) δ hδpos] with j hj
  have hρcs : HasCompactSupport (ρ j) :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 (σ j))
      ((hρs j).trans ball_subset_closedBall)
  have hexF : ConvolutionExists (ρ j) (fun x ↦ F x - g x) (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    hρcs.convolutionExists_left _ (hρc j) hFg.locallyIntegrable
  have hexg : ConvolutionExists (ρ j) g (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    hρcs.convolutionExists_left _ (hρc j) hg_int.locallyIntegrable
  have hsplit : ∀ x, convolution (ρ j) F (ContinuousLinearMap.lsmul ℝ ℝ) volume x =
      convolution (ρ j) (fun x ↦ F x - g x) (ContinuousLinearMap.lsmul ℝ ℝ) volume x +
        convolution (ρ j) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
    intro x
    have h := (hexF x).distrib_add (hexg x)
    have hfun : ((fun x ↦ F x - g x) + g) = F := by
      funext y
      simp
    rwa [hfun] at h
  have hpt : ∀ x, ‖convolution (ρ j) F (ContinuousLinearMap.lsmul ℝ ℝ) volume x - F x‖ₑ ≤
      ‖convolution (ρ j) (fun x ↦ F x - g x) (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ +
        (‖convolution (ρ j) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x - g x‖ₑ + ‖F x - g x‖ₑ) := by
    intro x
    rw [hsplit x]
    set a := convolution (ρ j) (fun x ↦ F x - g x) (ContinuousLinearMap.lsmul ℝ ℝ) volume x
    set b := convolution (ρ j) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x
    have : a + b - F x = a + ((b - g x) + -(F x - g x)) := by ring
    rw [this]
    refine (enorm_add_le _ _).trans ?_
    gcongr
    refine (enorm_add_le _ _).trans ?_
    rw [enorm_neg]
  have hcontg : Continuous (convolution (ρ j) g (ContinuousLinearMap.lsmul ℝ ℝ) volume) :=
    hρcs.continuous_convolution_left _ (hρc j) hg_int.locallyIntegrable
  have hm1 : AEMeasurable (fun x ↦ ‖F x - g x‖ₑ) volume := hFg.aestronglyMeasurable.enorm
  have hm2 : AEMeasurable
      (fun x ↦ ‖convolution (ρ j) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x - g x‖ₑ) volume :=
    (hcontg.sub hg_cont).measurable.enorm.aemeasurable
  have hm3 : AEMeasurable
      (fun x ↦ ‖convolution (ρ j) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x - g x‖ₑ + ‖F x - g x‖ₑ)
      volume :=
    hm2.add hm1
  calc ∫⁻ x, ‖convolution (ρ j) F (ContinuousLinearMap.lsmul ℝ ℝ) volume x - F x‖ₑ
      ≤ ∫⁻ x, (‖convolution (ρ j) (fun x ↦ F x - g x) (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ +
        (‖convolution (ρ j) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x - g x‖ₑ + ‖F x - g x‖ₑ)) :=
        lintegral_mono hpt
    _ = (∫⁻ x, ‖convolution (ρ j) (fun x ↦ F x - g x) (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ) +
        ((∫⁻ x, ‖convolution (ρ j) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x - g x‖ₑ) +
          ∫⁻ x, ‖F x - g x‖ₑ) := by
        rw [lintegral_add_right' _ hm3, lintegral_add_right' _ hm1]
    _ ≤ δ + (δ + δ) :=
        add_le_add ((hcontr j _ hFg).trans hg_close) (add_le_add hj hg_close)
    _ ≤ ε := hδ
/-- **Monotonicity of `bvVariationOn` in the domain.** For every `u : ℝⁿ → ℝ` and all sets
`W ⊆ O ⊆ ℝⁿ`, `bvVariationOn u W ≤ bvVariationOn u O`; no openness, measurability or integrability is
assumed. A field `g` admissible for `W` is admissible for `O`, as `tsupport g ⊆ W ⊆ O`. Since `div g`
vanishes off `tsupport g` (SimonGMT `support_euclideanDivergence_subset`), both pairings
`∫_W u div g` and `∫_O u div g` equal `∫ u div g` (`setIntegral_eq_integral_of_forall_compl_eq_zero`,
which needs no measurability of the set). -/
theorem Submission.bv_abs_variation_mono_set : ∀ (n : ℕ) (u : Rn n → ℝ) (W O : Set (Rn n)), W ⊆ O → Chapter02.bvVariationOn u W ≤ Chapter02.bvVariationOn u O := by
  intro n u W O hWO
  -- Step 2: it suffices to bound the pairing of a single field `g` admissible for `W`.
  refine iSup_le fun g ↦ iSup_le fun hg ↦ iSup_le fun hs ↦ iSup_le fun hn ↦ ?_
  -- Step 3: `g` is admissible for `O`.
  have hO : tsupport g ⊆ O := hs.trans hWO
  -- Step 1: `u · div g` vanishes off every `T ⊇ tsupport g`, because `div g` does.
  have hvan : ∀ T : Set (Rn n), tsupport g ⊆ T → ∀ x ∉ T,
      u x * Chapter02.euclideanDivergence (g : Rn n → Rn n) x = 0 := fun T hT x hx ↦ by
    rw [Function.notMem_support.mp fun h ↦ hx (hT (Chapter02.support_euclideanDivergence_subset _ h)),
      mul_zero]
  -- Steps 4–5: both set pairings equal the whole-space pairing, and `g` is admissible for `O`.
  calc ENNReal.ofReal (∫ x in W, u x * Chapter02.euclideanDivergence (g : Rn n → Rn n) x)
      = ENNReal.ofReal (∫ x in O, u x * Chapter02.euclideanDivergence (g : Rn n → Rn n) x) := by
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero (hvan W hs),
          setIntegral_eq_integral_of_forall_compl_eq_zero (hvan O hO)]
    _ ≤ Chapter02.bvVariationOn u O := Chapter02.ofReal_integral_le_bvVariationOn u O g hg hO hn
/-- **Simon Ch. 2, before 2.5 (p. 49), mollifier kernel**, as used for `|D|u|| ≤ |Du|` in the
proof of 2.8 (p. 52). For every `n` and `σ > 0` there is a `C^∞` kernel `ρ ≥ 0` on `ℝⁿ` with
`support ρ ⊆ B(0, σ)` (open ball) and `∫ ρ dLⁿ = 1`. Take the smooth bump `φ` at `0` with radii
`σ/2 < σ`. Its support is `B(0, σ)`, so `∫ φ > 0`, and `ρ = φ / ∫ φ` works. -/
theorem Submission.bv_abs_variation_exists_kernel : ∀ (n : ℕ) (σ : ℝ), 0 < σ → ∃ ρ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ρ ∧ (∀ x, 0 ≤ ρ x) ∧ Function.support ρ ⊆ ball 0 σ ∧ ∫ x, ρ x = 1 := by
  intro n σ hσ
  -- Step 1: a smooth bump `φ` at `0` with `rIn = σ/2`, `rOut = σ` (inner-product-space instance).
  obtain ⟨φ, hφ⟩ : ∃ φ : ContDiffBump (0 : Rn n), φ.rOut = σ :=
    ⟨⟨σ / 2, σ, half_pos hσ, half_lt_self hσ⟩, rfl⟩
  -- Step 2: `∫ φ > 0`, as `φ ≥ 0` is integrable with support the nonempty open ball `B(0, σ)`.
  have hpos : 0 < ∫ x, φ x := by
    refine (integral_pos_iff_support_of_nonneg φ.nonneg'
      (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport)).2 ?_
    rw [φ.support_eq]
    exact measure_ball_pos _ _ φ.rOut_pos
  -- Steps 3–6: `ρ = φ / ∫ φ` is smooth, nonnegative, supported in `B(0, σ)`, of unit mass.
  refine ⟨fun x ↦ φ x / ∫ y, φ y, φ.contDiff.div_const _, fun x ↦ div_nonneg φ.nonneg hpos.le,
    ?_, ?_⟩
  · rw [Function.support_div, φ.support_eq, Function.support_const hpos.ne', inter_univ, hφ]
  · rw [integral_div, div_self hpos.ne']
/-- **Smoothed absolute value.** For `w ∈ C¹(ℝⁿ)` and `η > 0`, `F = √(w² + η²) - η` is `C¹`,
satisfies `‖DF(x)‖ ≤ ‖Dw(x)‖` and is uniformly `η`-close to `|w|`. With `ψ(t) = √(t² + η²) - η`
and `F = ψ ∘ w`: `|t| ≤ √(t² + η²) ≤ |t| + η` gives the closeness, and the chain rule gives
`DF(x) = (w(x) / √(w(x)² + η²)) • Dw(x)` with a coefficient of absolute value at most `1`. -/
theorem Submission.bv_abs_variation_smoothed_abs : ∀ (n : ℕ) (w : Rn n → ℝ) (η : ℝ), 0 < η → ContDiff ℝ 1 w → ContDiff ℝ 1 (fun x ↦ Real.sqrt (w x ^ 2 + η ^ 2) - η) ∧ (∀ x, ‖fderiv ℝ (fun x ↦ Real.sqrt (w x ^ 2 + η ^ 2) - η) x‖ ≤ ‖fderiv ℝ w x‖) ∧ ∀ x, abs (Real.sqrt (w x ^ 2 + η ^ 2) - η - |w x|) ≤ η := by
  intro n w η hη hw
  -- Step 1: the radicand `t² + η²` is positive.
  have hpos : ∀ t : ℝ, 0 < t ^ 2 + η ^ 2 := fun t ↦ by positivity
  -- Step 2: `|t| = √(t²) ≤ √(t² + η²)`.
  have hlow : ∀ t : ℝ, |t| ≤ Real.sqrt (t ^ 2 + η ^ 2) := fun t ↦ by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg η))
  -- Step 3: `√(t² + η²) ≤ √((|t| + η)²) = |t| + η`.
  have hup : ∀ t : ℝ, Real.sqrt (t ^ 2 + η ^ 2) ≤ |t| + η := fun t ↦ by
    rw [← Real.sqrt_sq (add_nonneg (abs_nonneg t) hη.le)]
    exact Real.sqrt_le_sqrt (by nlinarith [abs_nonneg t, sq_abs t])
  refine ⟨?_, fun x ↦ ?_, fun x ↦ ?_⟩
  -- Step 5: the radicand is `C¹` and never vanishes, so `F` is `C¹`.
  · have h1 : ContDiff ℝ 1 (fun x ↦ w x ^ 2 + η ^ 2) := (hw.pow 2).add contDiff_const
    exact (h1.sqrt fun x ↦ (hpos (w x)).ne').sub contDiff_const
  -- Step 6: `ψ'(t₀) = 2t₀ / (2√(t₀² + η²))` at `t₀ = w(x)`; the chain rule gives
  -- `DF(x) = ψ'(t₀) • Dw(x)`, and `|ψ'(t₀)| ≤ 1` by Step 2.
  · have hψ : HasDerivAt (fun t : ℝ ↦ Real.sqrt (t ^ 2 + η ^ 2) - η)
        (2 * w x / (2 * Real.sqrt (w x ^ 2 + η ^ 2))) (w x) := by
      have h1 : HasDerivAt (fun t : ℝ ↦ t ^ 2 + η ^ 2) (2 * w x) (w x) := by
        simpa using (hasDerivAt_pow 2 (w x)).add_const (η ^ 2)
      exact (h1.sqrt (hpos (w x)).ne').sub_const η
    have hwx : HasFDerivAt w (fderiv ℝ w x) x := (hw.differentiable one_ne_zero x).hasFDerivAt
    have hF : HasFDerivAt (fun x ↦ Real.sqrt (w x ^ 2 + η ^ 2) - η)
        ((2 * w x / (2 * Real.sqrt (w x ^ 2 + η ^ 2))) • fderiv ℝ w x) x :=
      hψ.comp_hasFDerivAt x hwx
    have h2s : 0 < 2 * Real.sqrt (w x ^ 2 + η ^ 2) := by
      have := Real.sqrt_pos.2 (hpos (w x))
      positivity
    have hc : |2 * w x / (2 * Real.sqrt (w x ^ 2 + η ^ 2))| ≤ 1 := by
      rw [abs_div, abs_of_pos h2s, div_le_one h2s, abs_mul, abs_two]
      linarith [hlow (w x)]
    rw [hF.fderiv, norm_smul, Real.norm_eq_abs]
    calc |2 * w x / (2 * Real.sqrt (w x ^ 2 + η ^ 2))| * ‖fderiv ℝ w x‖
        ≤ 1 * ‖fderiv ℝ w x‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
      _ = ‖fderiv ℝ w x‖ := one_mul _
  -- Step 4: `-η ≤ F(x) - |w(x)| ≤ 0 ≤ η`, by Steps 2 and 3.
  · rw [abs_le]
    constructor
    · linarith [hlow (w x)]
    · linarith [hup (w x)]
/-- **Simon Ch. 2, proof of Lemma 2.5: transposing a mollification.** For `F ∈ L¹(ℝⁿ)` and
continuous, compactly supported `ρ`, `h`, with `ρ̌(t) = ρ(-t)`: `∫ (ρ * F) h = ∫ F (ρ̌ * h)` (the
step `∫ (φ_σ * u) div g = ∫ u (φ_σ * div g)`, for a kernel that need not be even). Both
convolutions are rewritten in the symmetric form `(a * b)(x) = ∫ a(x - t) b(t) dt` (translation and
reflection invariance of `Lⁿ`); then one application of Fubini to `(x, s) ↦ ρ(x - s) F(s) h(x)`
gives the identity. -/
theorem Submission.bv_integral_convolution_mul_reflect : ∀ (n : ℕ) (F ρ h : Rn n → ℝ), Integrable F volume → Continuous ρ → HasCompactSupport ρ → Continuous h → HasCompactSupport h → ∫ x, convolution ρ F (ContinuousLinearMap.lsmul ℝ ℝ) volume x * h x = ∫ x, F x * convolution (fun t ↦ ρ (-t)) h (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
  intro n F ρ h hF hρ hρc hh hhc
  -- Step 1: `ρ` is integrable and `h` is bounded, `|h| ≤ C`.
  have hρi : Integrable ρ volume := hρ.integrable_of_hasCompactSupport hρc
  obtain ⟨C, hC⟩ := hh.bounded_above_of_compact_support hhc
  -- Step 2: `(x, s) ↦ ρ(x - s) F(s) h(x)` is integrable on `ℝⁿ × ℝⁿ`: the convolution integrand
  -- `F(s) ρ(x - s)` is integrable and `h(x)` is continuous and bounded.
  have hG : Integrable (fun p : Rn n × Rn n ↦ ρ (p.1 - p.2) * F p.2 * h p.1)
      (volume.prod volume) := by
    refine ((hF.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hρi).mul_bdd
      (hh.comp continuous_fst).aestronglyMeasurable
      (Eventually.of_forall fun p ↦ hC p.1)).congr (Eventually.of_forall fun p ↦ ?_)
    simp only [Function.comp_apply, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    ring
  -- Step 3: `(ρ * F)(x) = ∫ ρ(x - s) F(s) ds` and `(ρ̌ * h)(s) = ∫ ρ(x - s) h(x) dx`; swap the
  -- order of integration once.
  calc ∫ x, convolution ρ F (ContinuousLinearMap.lsmul ℝ ℝ) volume x * h x
      = ∫ x, ∫ s, ρ (x - s) * F s * h x := by
        refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
        simp only [convolution_lsmul_swap, smul_eq_mul, ← integral_mul_const]
    _ = ∫ s, ∫ x, ρ (x - s) * F s * h x := integral_integral_swap hG
    _ = ∫ s, F s * convolution (fun t ↦ ρ (-t)) h (ContinuousLinearMap.lsmul ℝ ℝ) volume s := by
        refine integral_congr_ae (Eventually.of_forall fun s ↦ ?_)
        simp only [convolution_lsmul_swap, smul_eq_mul, neg_sub, ← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
        ring
/-- **Simon Ch. 2, proof of Lemma 2.5: divergence commutes with convolution.** For a locally
integrable kernel `κ` on `ℝⁿ` and a `C¹` vector field `g` with compact support,
`div(κ * g) = κ * div g` pointwise (the step `φ_σ * div g = div(φ_σ * g)`). By
`HasCompactSupport.hasFDerivAt_convolution_right`, `D(κ * g)(x) = ∫ κ(t) • Dg(x - t) dt`, whose
integrand is integrable because `Dg` is continuous with compact support. The trace is a continuous
linear map on `ℝⁿ →L[ℝ] ℝⁿ`, so it commutes with the integral, and
`trace (κ(t) • Dg(x - t)) = κ(t) div g(x - t)`. -/
theorem Submission.bv_euclideanDivergence_convolution : ∀ (n : ℕ) (κ : Rn n → ℝ) (g : Rn n → Rn n), LocallyIntegrable κ volume → ContDiff ℝ 1 g → HasCompactSupport g → ∀ x, Chapter02.euclideanDivergence (convolution κ g (ContinuousLinearMap.lsmul ℝ ℝ) volume) x = convolution κ (Chapter02.euclideanDivergence g) (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
  intro n κ g hκ hg hgc x
  -- Step 1: `Dg = fderiv ℝ g` is continuous with compact support.
  have hDg : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  have hDgc : HasCompactSupport (fderiv ℝ g) := hgc.fderiv ℝ
  -- Step 2: `D(κ * g)(x) = ∫ L' (κ t) (Dg (x - t)) dt` with `L' = (lsmul ℝ ℝ).precompR ℝⁿ`.
  have hD := (hgc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hκ hg x).fderiv
  -- Step 3: the integrand `t ↦ L' (κ t) (Dg (x - t))` is integrable.
  have hI := (hDgc.convolutionExists_right
    ((ContinuousLinearMap.lsmul ℝ ℝ).precompR (Rn n)) hκ hDg x).integrable
  -- Step 4: the trace, as a continuous linear map on `ℝⁿ →L[ℝ] ℝⁿ`, commutes with the integral.
  let T : (Rn n →L[ℝ] Rn n) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    (LinearMap.trace ℝ (Rn n) ∘ₗ ContinuousLinearMap.coeLM ℝ)
  have hT : ∀ A : Rn n →L[ℝ] Rn n, T A = LinearMap.trace ℝ (Rn n) A := fun A ↦ rfl
  calc Chapter02.euclideanDivergence (convolution κ g (ContinuousLinearMap.lsmul ℝ ℝ) volume) x
      = T (∫ t, (ContinuousLinearMap.lsmul ℝ ℝ).precompR (Rn n) (κ t) (fderiv ℝ g (x - t))) := by
        rw [hT, Chapter02.euclideanDivergence, hD, convolution_def]
    _ = ∫ t, T ((ContinuousLinearMap.lsmul ℝ ℝ).precompR (Rn n) (κ t) (fderiv ℝ g (x - t))) :=
        (T.integral_comp_comm hI).symm
    _ = convolution κ (Chapter02.euclideanDivergence g) (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
        -- Step 5: `L' (κ t) A = κ t • A`, so `trace (L' (κ t) (Dg (x - t))) = κ t * div g (x - t)`.
        rw [convolution_def]
        refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
        have hc : ((ContinuousLinearMap.lsmul ℝ ℝ (κ t)).comp (fderiv ℝ g (x - t)) :
            Rn n →L[ℝ] Rn n) = κ t • fderiv ℝ g (x - t) :=
          ContinuousLinearMap.ext fun v ↦ by
            simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.lsmul_apply, smul_apply]
        simp only [ContinuousLinearMap.precompR_apply, ContinuousLinearMap.compL_apply, hc, hT,
          ContinuousLinearMap.toLinearMap_smul, map_smul, smul_eq_mul,
          Chapter02.euclideanDivergence, ContinuousLinearMap.lsmul_apply]

/-- **Simon Ch. 2, proof of Lemma 2.5: the duality bound for a mollification.** Let `W ⊂ ℝⁿ` be
open, `u ∈ L¹(W)`, `ρ ≥ 0` continuous with `ρ = 0` off the open ball `{|x| < σ}` and `∫ ρ = 1`, and
`g` a `C¹` field with compact support, `|g| ≤ 1` and `B_σ(y) ⊂ W` for `y ∈ spt g`. Then
`w = ρ * (1_W u)` satisfies `∫ w div g ≤ |Du|(W)` (Simon's `∫ g · ∇u_σ = -∫ u div(φ_σ * g)`).
With `ρ̌(t) = ρ(-t)` and `G = ρ̌ * g`, transposition and `div G = ρ̌ * div g` give
`∫ w div g = ∫_W u div G`. `G` is `C¹`, hence Lipschitz, `spt G ⊂ B_σ(0) + spt g ⊂ W` is compact and
`|G| ≤ ∫ ρ̌ = 1`, so `G` is admissible in the supremum defining `|Du|(W)`. -/
theorem Submission.bv_mollifier_integral_mul_div_le : ∀ (n : ℕ) (W : Set (Rn n)) (u ρ : Rn n → ℝ) (σ : ℝ) (g : Rn n → Rn n), IsOpen W → IntegrableOn u W volume → Continuous ρ → (∀ x, 0 ≤ ρ x) → Function.support ρ ⊆ ball 0 σ → ∫ x, ρ x = 1 → ContDiff ℝ 1 g → HasCompactSupport g → (∀ x, ‖g x‖ ≤ 1) → (∀ y ∈ tsupport g, closedBall y σ ⊆ W) → ENNReal.ofReal (∫ x, convolution ρ (W.indicator u) (ContinuousLinearMap.lsmul ℝ ℝ) volume x * Chapter02.euclideanDivergence g x) ≤ Chapter02.bvVariationOn u W := by
  intro n W u ρ σ g hW hu hρ hρ0 hρs hρ1 hg hgc hg1 hgW
  -- Step 1: `F = 1_W u` is integrable, and `ρ` vanishes off the compact ball `closedBall 0 σ`.
  have hF : Integrable (W.indicator u) volume := (integrable_indicator_iff hW.measurableSet).2 hu
  have hρc : HasCompactSupport ρ := HasCompactSupport.intro (isCompact_closedBall 0 σ)
    fun x hx ↦ Function.notMem_support.1 fun h ↦ hx (ball_subset_closedBall (hρs h))
  -- Step 2: the reflected kernel `ρ̌(t) = ρ(-t)` is supported in `closedBall 0 σ`, is integrable,
  -- and `∫ ρ̌ = ∫ ρ = 1` by reflection invariance of `Lⁿ`.
  have hρrs : Function.support (fun t ↦ ρ (-t)) ⊆ closedBall (0 : Rn n) σ := fun t ht ↦ by
    have h1 : -t ∈ ball (0 : Rn n) σ := hρs (Function.mem_support.2 (Function.mem_support.1 ht))
    rw [mem_ball_zero_iff, norm_neg] at h1
    exact mem_closedBall_zero_iff.2 h1.le
  have hρri : Integrable (fun t ↦ ρ (-t)) volume :=
    (hρ.comp continuous_neg).integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_closedBall 0 σ)
        fun x hx ↦ Function.notMem_support.1 fun h ↦ hx (hρrs h))
  have hρr1 : ∫ t, ρ (-t) = 1 := (integral_neg_eq_self ρ volume).trans hρ1
  -- Step 3: `div g = trace ∘ Dg` is continuous, with support in the compact `tsupport g`.
  have hh : Continuous (Chapter02.euclideanDivergence g) := by
    let T : (Rn n →L[ℝ] Rn n) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
      (LinearMap.trace ℝ (Rn n) ∘ₗ ContinuousLinearMap.coeLM ℝ)
    exact T.continuous.comp (hg.continuous_fderiv one_ne_zero)
  have hhc : HasCompactSupport (Chapter02.euclideanDivergence g) :=
    hgc.mono' (Chapter02.support_euclideanDivergence_subset g)
  -- Step 4: the comparison field `G = ρ̌ * g` has `div G = ρ̌ * div g`.
  obtain ⟨G, hG⟩ : ∃ G, G = convolution (fun t ↦ ρ (-t)) g (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    ⟨_, rfl⟩
  have hdivG : ∀ x, Chapter02.euclideanDivergence G x =
      convolution (fun t ↦ ρ (-t)) (Chapter02.euclideanDivergence g)
        (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
    rw [hG]
    exact Submission.bv_euclideanDivergence_convolution n _ g hρri.locallyIntegrable hg hgc
  -- Step 5: transposing the mollification, `∫ w div g = ∫ F (ρ̌ * div g) = ∫_W u div G`.
  have hint : ∫ x, convolution ρ (W.indicator u) (ContinuousLinearMap.lsmul ℝ ℝ) volume x *
      Chapter02.euclideanDivergence g x = ∫ x in W, u x * Chapter02.euclideanDivergence G x := by
    rw [Submission.bv_integral_convolution_mul_reflect n (W.indicator u) ρ _ hF hρ hρc hh hhc,
      ← integral_indicator hW.measurableSet]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    by_cases hx : x ∈ W
    · simp only [Set.indicator_of_mem hx, hdivG]
    · simp only [Set.indicator_of_notMem hx, zero_mul]
  -- Step 6: `G` is `C¹`.
  have hGd : ContDiff ℝ 1 G := by
    rw [hG]
    exact hgc.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hρri.locallyIntegrable hg
  -- Step 7: `tsupport G ⊆ S := closedBall 0 σ + tsupport g ⊆ W`, and `S` is compact.
  obtain ⟨S, hS, hGS, hSW⟩ : ∃ S : Set (Rn n), IsCompact S ∧ tsupport G ⊆ S ∧ S ⊆ W := by
    open Pointwise in
    refine ⟨closedBall 0 σ + tsupport g, (isCompact_closedBall 0 σ).add hgc, ?_, ?_⟩
    · rw [hG]
      exact closure_minimal ((support_convolution_subset _).trans
        (add_subset_add hρrs (subset_tsupport g))) ((isCompact_closedBall 0 σ).add hgc).isClosed
    · rintro _ ⟨t, ht, y, hy, rfl⟩
      refine hgW y hy ?_
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_right]
      exact mem_closedBall_zero_iff.1 ht
  have hGc : HasCompactSupport G := hS.of_isClosed_subset (isClosed_tsupport G) hGS
  -- Step 8: `‖G s‖ ≤ ∫ ρ̌(t) ‖g(s - t)‖ dt ≤ ∫ ρ̌ = 1`.
  have hGle : ∀ s, ‖G s‖ ≤ 1 := by
    intro s
    rw [hG, convolution_def, ← hρr1]
    refine norm_integral_le_of_norm_le hρri (Eventually.of_forall fun t ↦ ?_)
    rw [ContinuousLinearMap.lsmul_apply, norm_smul, Real.norm_of_nonneg (hρ0 _)]
    exact mul_le_of_le_one_right (hρ0 _) (hg1 _)
  -- Step 9: `G` is an admissible field: Lipschitz (`C¹` with compact support), supported in `W`,
  -- with supremum norm at most one.
  let Gc : CompactlySupportedContinuousMap (Rn n) (Rn n) := ⟨⟨G, hGd.continuous⟩, hGc⟩
  have hLip : Chapter02.IsLipschitzTestField Gc :=
    ContDiff.lipschitzWith_of_hasCompactSupport hGc hGd one_ne_zero
  have hsupp : tsupport Gc ⊆ W := hGS.trans hSW
  have hnorm : Chapter02.compactlySupportedSupNorm Gc ≤ 1 :=
    csSup_le (range_nonempty _) (by rintro _ ⟨x, rfl⟩; exact hGle x)
  -- Step 10: the supremum defining `|Du|(W)` dominates the pairing with `G`.
  rw [hint]
  exact Chapter02.ofReal_integral_le_bvVariationOn u W Gc hLip hsupp hnorm
/-- **Riesz gradient of a `C²` function.** For `w : ℝⁿ → ℝ` of class `C²`, the vector field
`G(x) = ∑ᵢ Dw(x)(eᵢ) • eᵢ`, with `(eᵢ)` the standard orthonormal basis of `ℝⁿ`
(`EuclideanSpace.basisFun`), is `C¹`, since `Dw` is `C¹` (`ContDiff.fderiv_right`). It represents
`Dw(x)` by the orthonormal expansion `∑ᵢ ⟨eᵢ, v⟩ • eᵢ = v` (`OrthonormalBasis.sum_repr'`), and
`‖G(x)‖ = ‖Dw(x)‖`. Cauchy–Schwarz and `ContinuousLinearMap.opNorm_le_bound` give
`‖Dw(x)‖ ≤ ‖G(x)‖`. Conversely `‖G(x)‖² = Dw(x)(G(x)) ≤ ‖Dw(x)‖ ‖G(x)‖`. -/
theorem Submission.bv_exists_contDiff_gradient_of_contDiff_two : ∀ (n : ℕ) (w : Rn n → ℝ), ContDiff ℝ 2 w → ∃ G : Rn n → Rn n, ContDiff ℝ 1 G ∧ (∀ x v, inner ℝ (G x) v = fderiv ℝ w x v) ∧ ∀ x, ‖G x‖ = ‖fderiv ℝ w x‖ := by
  intro n w hw
  -- Step 1: `Dw` is `C¹`, since `w` is `C²` and `1 + 1 ≤ 2`.
  have hDw : ContDiff ℝ 1 (fderiv ℝ w) := hw.fderiv_right (by norm_num)
  -- Step 2: `G(x) = ∑ᵢ Dw(x)(eᵢ) • eᵢ`, with `e` the standard orthonormal basis of `ℝⁿ`.
  set e := EuclideanSpace.basisFun (Fin n) ℝ
  set G : Rn n → Rn n := fun x ↦ ∑ i, fderiv ℝ w x (e i) • e i with hGsum
  -- Step 3: `G` is `C¹`, as a finite sum of `C¹` scalar functions times constant vectors.
  have hG : ContDiff ℝ 1 G :=
    ContDiff.sum fun i _ ↦ (hDw.clm_apply contDiff_const).smul contDiff_const
  -- Step 4: `⟨G(x), v⟩ = ∑ᵢ ⟨eᵢ, v⟩ Dw(x)(eᵢ) = Dw(x)(∑ᵢ ⟨eᵢ, v⟩ • eᵢ) = Dw(x)(v)`.
  have hrep : ∀ x v, inner ℝ (G x) v = fderiv ℝ w x v := by
    intro x v
    calc inner ℝ (G x) v = ∑ i, inner ℝ (e i) v * fderiv ℝ w x (e i) := by
          rw [hGsum, sum_inner]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [real_inner_smul_left, mul_comm]
      _ = fderiv ℝ w x (∑ i, inner ℝ (e i) v • e i) := by
          simp only [map_sum, map_smul, smul_eq_mul]
      _ = fderiv ℝ w x v := by rw [e.sum_repr' v]
  refine ⟨G, hG, hrep, fun x ↦ le_antisymm ?_ ?_⟩
  · -- Step 6: `‖G(x)‖² = Dw(x)(G(x)) ≤ ‖Dw(x)‖ ‖G(x)‖`; divide by `‖G(x)‖` when it is positive.
    rcases (norm_nonneg (G x)).eq_or_lt with h0 | hpos
    · rw [← h0]
      exact norm_nonneg _
    · have h : ‖G x‖ * ‖G x‖ ≤ ‖fderiv ℝ w x‖ * ‖G x‖ :=
        calc ‖G x‖ * ‖G x‖ = inner ℝ (G x) (G x) := (real_inner_self_eq_norm_mul_norm (G x)).symm
          _ = fderiv ℝ w x (G x) := hrep x (G x)
          _ ≤ |fderiv ℝ w x (G x)| := le_abs_self _
          _ = ‖fderiv ℝ w x (G x)‖ := (Real.norm_eq_abs _).symm
          _ ≤ ‖fderiv ℝ w x‖ * ‖G x‖ := (fderiv ℝ w x).le_opNorm (G x)
      exact le_of_mul_le_mul_right h hpos
  · -- Step 5: Cauchy–Schwarz `|Dw(x)(v)| = |⟨G(x), v⟩| ≤ ‖G(x)‖ ‖v‖` and the operator-norm bound.
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (G x)) fun v ↦ ?_
    rw [← hrep x v, Real.norm_eq_abs]
    exact abs_real_inner_le_norm (G x) v
/-- **Regularized unit test field (Simon Ch. 2, Lemma 2.5, identity (4)).** For a `C¹` field
`G : ℝⁿ → ℝⁿ`, a `C¹` cut-off `χ` with compact support and `0 ≤ χ ≤ 1`, and `η > 0`, the field
`g = -(χ / √(‖G‖² + η²)) • G` is `C¹`, has compact support with `tsupport g ⊆ tsupport χ`, and
`‖g‖ ≤ 1`. The denominator `N = √(‖G‖² + η²)` is positive because `η > 0`, so `χ / N` is `C¹`;
`g` vanishes wherever `χ` does; and `‖g‖ = χ ‖G‖ / N ≤ 1` because `χ ≤ 1` and `‖G‖ ≤ N`. -/
theorem Submission.bv_regularized_unit_field_admissible : ∀ (n : ℕ) (G : Rn n → Rn n) (χ : Rn n → ℝ) (η : ℝ) (g : Rn n → Rn n), ContDiff ℝ 1 G → ContDiff ℝ 1 χ → HasCompactSupport χ → (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) → 0 < η → (∀ x, g x = -(χ x / Real.sqrt (‖G x‖ ^ 2 + η ^ 2)) • G x) → ContDiff ℝ 1 g ∧ HasCompactSupport g ∧ tsupport g ⊆ tsupport χ ∧ ∀ x, ‖g x‖ ≤ 1 := by
  intro n G χ η g hG hχ hχc hχb hη hg
  -- Step 0: the radicand `‖G x‖² + η²` is positive, so `N x = √(‖G x‖² + η²) > 0`.
  have hpos : ∀ x, 0 < ‖G x‖ ^ 2 + η ^ 2 := fun x => by positivity
  have hN : ∀ x, 0 < Real.sqrt (‖G x‖ ^ 2 + η ^ 2) := fun x => Real.sqrt_pos.2 (hpos x)
  -- Step 2: `support g ⊆ support χ`, since `χ x = 0` gives `g x = -(0 / N x) • G x = 0`.
  have hsupp : Function.support g ⊆ Function.support χ := by
    intro x hx
    rw [Function.mem_support] at hx ⊢
    intro h0
    apply hx
    rw [hg x, h0, zero_div, neg_zero, zero_smul]
  -- Steps 3 and 4: compact support and `tsupport g ⊆ tsupport χ` (closures) follow from Step 2.
  refine ⟨?_, hχc.mono hsupp, closure_mono hsupp, ?_⟩
  · -- Step 1: `‖G‖² + η²` is `C¹` and never `0`, so `N`, `χ / N` and `-(χ / N) • G` are `C¹`.
    rw [show g = fun x => -(χ x / Real.sqrt (‖G x‖ ^ 2 + η ^ 2)) • G x from funext hg]
    have h1 : ContDiff ℝ 1 (fun x => ‖G x‖ ^ 2 + η ^ 2) :=
      (hG.norm_sq (𝕜 := ℝ)).add contDiff_const
    have h2 : ContDiff ℝ 1 (fun x => Real.sqrt (‖G x‖ ^ 2 + η ^ 2)) :=
      h1.sqrt fun x => (hpos x).ne'
    exact ((hχ.div h2 fun x => (hN x).ne').neg).smul hG
  · -- Step 5: `‖g x‖ = χ x ‖G x‖ / N x ≤ 1`, as `0 ≤ χ x ≤ 1` and `‖G x‖ ≤ N x`.
    intro x
    rw [hg x, norm_smul, norm_neg, Real.norm_eq_abs, abs_div, abs_of_nonneg (hχb x).1,
      abs_of_pos (hN x), div_mul_eq_mul_div, div_le_one (hN x)]
    calc χ x * ‖G x‖ ≤ 1 * ‖G x‖ := mul_le_mul_of_nonneg_right (hχb x).2 (norm_nonneg _)
      _ = ‖G x‖ := one_mul _
      _ ≤ Real.sqrt (‖G x‖ ^ 2 + η ^ 2) :=
        Real.le_sqrt_of_sq_le (le_add_of_nonneg_right (sq_nonneg η))
/-- **Removing the `η`-regularization on a compact set.** Let `f ≥ 0` be continuous, `χ ≥ 0`
continuous with compact support, `χ = 1` on the compact set `L`, and suppose
`∫ χ f² / √(f² + η²) ≤ M` for every `η > 0`. Then `∫_L f ≤ M`. Pointwise on `L`,
`f - η ≤ f² / √(f² + η²)`, so `∫_L f ≤ ∫ χ f² / √(f² + η²) + η Lⁿ(L)`; letting `η → 0` gives the
bound for the Bochner integral, which equals the lower integral since `f ≥ 0` is integrable on `L`. -/
theorem Submission.bv_set_lintegral_le_of_regularized_bound : ∀ (n : ℕ) (f χ : Rn n → ℝ) (L : Set (Rn n)) (M : ℝ≥0∞), Continuous f → (∀ x, 0 ≤ f x) → Continuous χ → HasCompactSupport χ → (∀ x, 0 ≤ χ x) → IsCompact L → (∀ x ∈ L, χ x = 1) → (∀ η : ℝ, 0 < η → ENNReal.ofReal (∫ x, χ x * f x ^ 2 / Real.sqrt (f x ^ 2 + η ^ 2)) ≤ M) → ∫⁻ x in L, ENNReal.ofReal (f x) ≤ M := by
  intro n f χ L M hf hf0 hχ hχc hχ0 hL hχL hM
  -- Step 0: the case `M = ∞` is trivial; otherwise `M = ofReal m` with `m = M.toReal ≥ 0`.
  rcases eq_or_ne M ⊤ with rfl | hMtop
  · exact le_top
  obtain ⟨m, hm0, rfl⟩ : ∃ m : ℝ, 0 ≤ m ∧ M = ENNReal.ofReal m :=
    ⟨M.toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hMtop).symm⟩
  -- Step 1: `L` is measurable, and `f` and constants are integrable on the compact set `L`.
  have hLmeas : MeasurableSet L := hL.measurableSet
  have hfL : IntegrableOn f L := hf.continuousOn.integrableOn_compact hL
  -- Steps 2–6: for fixed `η > 0`, `∫_L f ≤ m + Lⁿ(L) η`.
  have key : ∀ η : ℝ, 0 < η → ∫ x in L, f x ≤ m + volume.real L * η := by
    intro η hη
    -- Step 2: `φ_η = χ f² / √(f² + η²)` is continuous, compactly supported, integrable, `≥ 0`.
    have hden : ∀ x, 0 < Real.sqrt (f x ^ 2 + η ^ 2) := fun x ↦ Real.sqrt_pos.2 (by positivity)
    have hφc : Continuous (fun x ↦ χ x * f x ^ 2 / Real.sqrt (f x ^ 2 + η ^ 2)) :=
      (hχ.mul (hf.pow 2)).div ((hf.pow 2).add continuous_const).sqrt fun x ↦ (hden x).ne'
    have hφs : HasCompactSupport (fun x ↦ χ x * f x ^ 2 / Real.sqrt (f x ^ 2 + η ^ 2)) := by
      convert hχc.mul_right (f' := fun x ↦ f x ^ 2 / Real.sqrt (f x ^ 2 + η ^ 2)) using 1
      funext x
      simp only [Pi.mul_apply, mul_div_assoc]
    have hφi : Integrable (fun x ↦ χ x * f x ^ 2 / Real.sqrt (f x ^ 2 + η ^ 2)) :=
      hφc.integrable_of_hasCompactSupport hφs
    have hφ0 : ∀ x, 0 ≤ χ x * f x ^ 2 / Real.sqrt (f x ^ 2 + η ^ 2) := fun x ↦
      div_nonneg (mul_nonneg (hχ0 x) (sq_nonneg _)) (hden x).le
    -- Step 3: the hypothesis gives `∫ φ_η ≤ m`.
    have hint : ∫ x, χ x * f x ^ 2 / Real.sqrt (f x ^ 2 + η ^ 2) ≤ m :=
      (ENNReal.ofReal_le_ofReal_iff hm0).1 (hM η hη)
    -- Step 4: `t - η ≤ t² / √(t² + η²)` for `t ≥ 0`.
    have elem : ∀ t : ℝ, 0 ≤ t → t - η ≤ t ^ 2 / Real.sqrt (t ^ 2 + η ^ 2) := by
      intro t ht
      have hs : 0 < Real.sqrt (t ^ 2 + η ^ 2) := Real.sqrt_pos.2 (by positivity)
      have hle : Real.sqrt (t ^ 2 + η ^ 2) ≤ t + η :=
        (Real.sqrt_le_left (by linarith)).2 (by nlinarith [mul_nonneg ht hη.le])
      rw [le_div_iff₀ hs]
      rcases le_or_gt t η with h | h
      · nlinarith [mul_nonneg (sub_nonneg.2 h) hs.le, sq_nonneg t]
      · nlinarith [mul_le_mul_of_nonneg_left hle (sub_nonneg.2 h.le), sq_nonneg η]
    -- Step 5: on `L`, `χ = 1`, so `f - η ≤ φ_η`.
    have hpt : ∀ x ∈ L, f x - η ≤ χ x * f x ^ 2 / Real.sqrt (f x ^ 2 + η ^ 2) := by
      intro x hx
      rw [hχL x hx, one_mul]
      exact elem (f x) (hf0 x)
    -- Step 6: `∫_L f = ∫_L (f - η) + Lⁿ(L) η ≤ ∫_L φ_η + Lⁿ(L) η ≤ ∫ φ_η + Lⁿ(L) η`.
    have hcL : IntegrableOn (fun _ : Rn n ↦ η) L := continuous_const.continuousOn.integrableOn_compact hL
    have hsplit : ∫ x in L, f x = (∫ x in L, (f x - η)) + volume.real L * η := by
      rw [integral_sub hfL hcL, setIntegral_const, smul_eq_mul]
      ring
    have hmono : ∫ x in L, (f x - η) ≤ ∫ x in L, χ x * f x ^ 2 / Real.sqrt (f x ^ 2 + η ^ 2) :=
      setIntegral_mono_on (hfL.sub hcL) hφi.integrableOn hLmeas hpt
    have hsub : ∫ x in L, χ x * f x ^ 2 / Real.sqrt (f x ^ 2 + η ^ 2) ≤
        ∫ x, χ x * f x ^ 2 / Real.sqrt (f x ^ 2 + η ^ 2) :=
      setIntegral_le_integral hφi (ae_of_all _ hφ0)
    linarith
  -- Step 7: let `η → 0` via `η = ε / (Lⁿ(L) + 1)`.
  have hLm : ∫ x in L, f x ≤ m := by
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    have hμ0 : 0 ≤ volume.real L := measureReal_nonneg
    have hη : 0 < ε / (volume.real L + 1) := div_pos hε (by linarith)
    have h1 := key _ hη
    have h2 : volume.real L * (ε / (volume.real L + 1)) ≤ ε := by
      rw [mul_div_assoc', div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  -- Step 8: convert the Bochner integral of `f ≥ 0` on `L` to the lower integral.
  calc ∫⁻ x in L, ENNReal.ofReal (f x) = ENNReal.ofReal (∫ x in L, f x) :=
        (ofReal_integral_eq_lintegral_ofReal hfL.integrable (ae_of_all _ hf0)).symm
    _ ≤ ENNReal.ofReal m := ENNReal.ofReal_le_ofReal hLm
/-- **Simon Ch. 2, proof of Lemma 2.5, a smooth cut-off.** If `L ⊆ ℝⁿ` is compact, `O ⊆ ℝⁿ` is open
and `L ⊆ O`, there is a `C^∞` function `χ : ℝⁿ → [0,1]` with `χ = 1` on `L` and compact support
`tsupport χ ⊆ O`. A margin `δ > 0` gives a compact closed thickening `C = L_δ ⊆ O` whose interior
contains `L`. The smooth Urysohn lemma on `ℝⁿ` (modelled on itself) gives a smooth `χ` with values
in `[0,1]`, `χ = 1` near `L` and `χ = 0` off `C`; hence `tsupport χ ⊆ C`. -/
theorem Submission.bv_exists_smooth_cutoff : ∀ (n : ℕ) (L O : Set (Rn n)), IsCompact L → IsOpen O → L ⊆ O → ∃ χ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ (∀ x ∈ L, χ x = 1) ∧ HasCompactSupport χ ∧ tsupport χ ⊆ O := by
  intro n L O hL hO hLO
  -- Margin: the compact closed thickening `C = cthickening δ L` lies in `O`, and `L ⊆ interior C`.
  obtain ⟨δ, hδ, hCO⟩ := hL.exists_cthickening_subset_open hO hLO
  have hLC : L ⊆ interior (cthickening δ L) :=
    (self_subset_thickening hδ L).trans (thickening_subset_interior_cthickening δ L)
  -- Smooth Urysohn function for the closed set `L` inside `interior C`.
  obtain ⟨f, hf1, hf0, hf01⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (modelWithCornersSelf ℝ (Rn n)) (n := (⊤ : ℕ∞)) hL.isClosed hLC
  -- `f` vanishes off the closed set `C`, so `tsupport f ⊆ C ⊆ O` and `tsupport f` is compact.
  have hfC : tsupport f ⊆ cthickening δ L :=
    closure_minimal (Function.support_subset_iff'.2 hf0) isClosed_cthickening
  exact ⟨f, f.contMDiff.contDiff, hf01, hf1.self_of_nhdsSet,
    hL.cthickening.of_isClosed_subset (isClosed_tsupport _) hfC, hfC.trans hCO⟩

/-- **Simon Ch. 2, proof of Lemma 2.5, smooth duality on a compact set.** Let `w : ℝⁿ → ℝ` be `C²`,
`O ⊆ ℝⁿ` open and `L ⊆ O` compact. If `-∫ Dw(x)[g(x)] dx ≤ M` for every `C¹` vector field `g` with
compact support in `O` and `‖g‖ ≤ 1`, then `∫_L ‖Dw‖ ≤ M`. With a cut-off `χ` for `L ⊆ O` and the
Riesz gradient `∇w` of `Dw`, test with `g = -(χ / √(‖∇w‖² + η²)) • ∇w`, `η > 0`: then
`-Dw[g] = χ ‖Dw‖² / √(‖Dw‖² + η²)`, and letting `η → 0` (with `χ = 1` on `L`) gives the bound. -/
theorem Submission.bv_lintegral_norm_fderiv_le_of_dual_compact : ∀ (n : ℕ) (w : Rn n → ℝ) (O L : Set (Rn n)) (M : ℝ≥0∞), ContDiff ℝ 2 w → IsOpen O → IsCompact L → L ⊆ O → (∀ g : Rn n → Rn n, ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ O → (∀ x, ‖g x‖ ≤ 1) → ENNReal.ofReal (-∫ x, fderiv ℝ w x (g x)) ≤ M) → ∫⁻ x in L, ‖fderiv ℝ w x‖ₑ ≤ M := by
  intro n w O L M hw hO hL hLO hdual
  -- Cut-off `χ` for `L ⊆ O`, and the `C¹` Riesz gradient `G` of `Dw`, with `‖G‖ = ‖Dw‖`.
  obtain ⟨χ, hχ, hχ01, hχL, hχc, hχO⟩ := Submission.bv_exists_smooth_cutoff n L O hL hO hLO
  obtain ⟨G, hG, hGDw, hGnorm⟩ := Submission.bv_exists_contDiff_gradient_of_contDiff_two n w hw
  -- For `η > 0`, `g = -(χ / √(‖G‖² + η²)) • G` is admissible (`tsupport g ⊆ tsupport χ ⊆ O`),
  -- and `-Dw(x)[g(x)] = χ(x) ‖Dw(x)‖² / √(‖Dw(x)‖² + η²)` because `Dw(x)[G(x)] = ‖G(x)‖²`.
  have hreg : ∀ η : ℝ, 0 < η → ENNReal.ofReal
      (∫ x, χ x * ‖fderiv ℝ w x‖ ^ 2 / Real.sqrt (‖fderiv ℝ w x‖ ^ 2 + η ^ 2)) ≤ M := by
    intro η hη
    obtain ⟨hg, hgc, hgχ, hg1⟩ := Submission.bv_regularized_unit_field_admissible n G χ η
      (fun x => -(χ x / Real.sqrt (‖G x‖ ^ 2 + η ^ 2)) • G x) hG
      (hχ.of_le (by exact_mod_cast le_top)) hχc hχ01 hη fun x => rfl
    have hpt : ∀ x, -fderiv ℝ w x (-(χ x / Real.sqrt (‖G x‖ ^ 2 + η ^ 2)) • G x) =
        χ x * ‖fderiv ℝ w x‖ ^ 2 / Real.sqrt (‖fderiv ℝ w x‖ ^ 2 + η ^ 2) := by
      intro x
      rw [map_smul, smul_eq_mul, ← hGDw, real_inner_self_eq_norm_sq, hGnorm]
      ring
    have hbound := hdual _ hg hgc (hgχ.trans hχO) hg1
    rwa [← integral_neg, integral_congr_ae (ae_of_all _ hpt)] at hbound
  -- Let `η → 0` for the continuous `f = ‖Dw‖ ≥ 0`, and use `ofReal ‖·‖ = ‖·‖ₑ`.
  simpa only [ofReal_norm] using Submission.bv_set_lintegral_le_of_regularized_bound n
    (fun x => ‖fderiv ℝ w x‖) χ L M (hw.continuous_fderiv two_ne_zero).norm
    (fun x => norm_nonneg _) hχ.continuous hχc (fun x => (hχ01 x).1) hL hχL hreg
/-- **Simon Ch. 2, proof of Lemma 2.5, passage from compact subsets to an open set.** If `O ⊆ ℝⁿ`
is open, `f ≥ 0` is measurable and `∫⁻_L f dLⁿ ≤ M` for every compact `L ⊆ O`, then
`∫⁻_O f dLⁿ ≤ M`. A closed exhaustion `F l` of `O` cut down by the balls `B_l(0)` gives compact
sets `L l = F l ∩ B_l(0)` increasing to `O`. Then `1_{L l} f` increase to `1_O f`, and monotone
convergence gives `∫⁻_O f = sup_l ∫⁻_{L l} f ≤ M`. -/
theorem Submission.bv_lintegral_open_le_of_compact : ∀ (n : ℕ) (O : Set (Rn n)) (f : Rn n → ℝ≥0∞) (M : ℝ≥0∞), IsOpen O → Measurable f → (∀ L, IsCompact L → L ⊆ O → ∫⁻ x in L, f x ≤ M) → ∫⁻ x in O, f x ≤ M := by
  intro n O f M hO hf hM
  -- A closed exhaustion `F l` of `O`, cut down to the compact sets `L l = F l ∩ B_l(0)`.
  obtain ⟨F, hFc, hFO, hFU, hFm⟩ := hO.exists_iUnion_isClosed
  let L : ℕ → Set (Rn n) := fun l ↦ F l ∩ closedBall 0 l
  have hLc (l : ℕ) : IsCompact (L l) := (isCompact_closedBall 0 l).inter_left (hFc l)
  have hLO (l : ℕ) : L l ⊆ O := inter_subset_left.trans (hFO l)
  have hLm : Monotone L := fun i j hij ↦
    inter_subset_inter (hFm hij) (closedBall_subset_closedBall (Nat.cast_le.2 hij))
  have hLU : ⋃ l, L l = O := by
    refine Subset.antisymm (iUnion_subset hLO) fun x hx ↦ ?_
    rw [← hFU] at hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    obtain ⟨j, hj⟩ := exists_nat_ge ‖x‖
    exact mem_iUnion.2 ⟨max i j, hFm (le_max_left i j) hi,
      mem_closedBall_zero_iff.2 (hj.trans (Nat.cast_le.2 (le_max_right i j)))⟩
  -- The measurable functions `1_{L l} f` increase to `1_O f`; apply monotone convergence.
  have hLmeas (l : ℕ) : MeasurableSet (L l) := (hLc l).isClosed.measurableSet
  calc ∫⁻ x in O, f x
      = ∫⁻ x, ⨆ l, (L l).indicator f x := by
        rw [← lintegral_indicator hO.measurableSet, ← hLU]
        simp_rw [indicator_iUnion_apply bot_eq_zero]
    _ = ⨆ l, ∫⁻ x, (L l).indicator f x :=
        lintegral_iSup (fun l ↦ hf.indicator (hLmeas l))
          fun i j hij ↦ indicator_le_indicator_of_subset (hLm hij) fun _ ↦ zero_le
    _ = ⨆ l, ∫⁻ x in L l, f x := iSup_congr fun l ↦ lintegral_indicator (hLmeas l) f
    _ ≤ M := iSup_le fun l ↦ hM (L l) (hLc l) (hLO l)
/-- **Integration by parts against a compactly supported Lipschitz vector field.** For `F ∈ C¹(ℝⁿ)`
and a `K`-Lipschitz `g : ℝⁿ → ℝⁿ` with compact support, `∫ F div g = -∫ DF(x)[g(x)] dx`, where
`div g = trace Dg` and `Dg = fderiv ℝ g` (which is `0` where `g` is not differentiable). This is the
Fubini / absolute-continuity-on-lines step of Simon's proof of Rademacher's theorem (Ch. 2, 1.4).
`F` is replaced by `χF` for a smooth bump `χ` equal to `1` near `spt g`; Mathlib's
`LipschitzWith.integral_lineDeriv_mul_eq` is applied to each coordinate `⟨eᵢ, g⟩`; the line
derivatives are identified with `fderiv` (everywhere for `χF`, a.e. for `g` by Rademacher's
theorem); and the identities are summed over the standard orthonormal basis `(eᵢ)`. -/
theorem Submission.bv_lipschitz_integration_by_parts : ∀ (n : ℕ) (F : Rn n → ℝ) (g : Rn n → Rn n) (K : ℝ≥0), ContDiff ℝ 1 F → LipschitzWith K g → HasCompactSupport g → ∫ x, F x * Chapter02.euclideanDivergence g x = -∫ x, fderiv ℝ F x (g x) := by
  intro n F g K hF hg hgc
  -- Step 3 (cut-off): `G = χF`, with `χ` a smooth bump equal to `1` on a ball `U ⊇ tsupport g`,
  -- is `C¹` with compact support and equals `F` on the open set `U`.
  obtain ⟨G, hG, hGc, U, hU, hSU, hEq⟩ : ∃ G : Rn n → ℝ, ContDiff ℝ 1 G ∧ HasCompactSupport G ∧
      ∃ U : Set (Rn n), IsOpen U ∧ tsupport g ⊆ U ∧ EqOn G F U := by
    obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.subset_ball (0 : Rn n)
    let χ : ContDiffBump (0 : Rn n) :=
      ⟨max R 1, max R 1 + 1, lt_of_lt_of_le one_pos (le_max_right _ _), lt_add_one _⟩
    refine ⟨fun x ↦ χ x * F x, χ.contDiff.mul hF, χ.hasCompactSupport.mul_right,
      ball 0 (max R 1), isOpen_ball, hR.trans (ball_subset_ball (le_max_left _ _)), fun x hx ↦ ?_⟩
    simp [χ.one_of_mem_closedBall (ball_subset_closedBall hx)]
  -- `G` is Lipschitz (`C¹` with compact support) and differentiable everywhere.
  obtain ⟨L, hL⟩ := hG.lipschitzWith_of_hasCompactSupport hGc one_ne_zero
  have hGd : Differentiable ℝ G := hG.differentiable one_ne_zero
  -- The coordinates `gᵢ = ⟨eᵢ, g⟩` in the standard orthonormal basis `(eᵢ)` are `K`-Lipschitz
  -- with compact support.
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let gi : Fin n → Rn n → ℝ := fun i x ↦ inner ℝ (b i) (g x)
  have hgi_lip : ∀ i, LipschitzWith K (gi i) := fun i ↦ by
    have h1 : LipschitzWith 1 (fun y : Rn n ↦ inner ℝ (b i) y) :=
      LipschitzWith.of_dist_le_mul fun y z ↦ by
        rw [dist_eq_norm, dist_eq_norm, ← inner_sub_right]
        simpa [b.norm_eq_one] using norm_inner_le_norm (𝕜 := ℝ) (b i) (y - z)
    have h2 := h1.comp hg
    rw [one_mul] at h2
    exact h2
  have hgi_c : ∀ i, HasCompactSupport (gi i) := fun i ↦
    hgc.comp_left (g := fun y : Rn n ↦ inner ℝ (b i) y) (inner_zero_right (b i))
  -- Steps 4–5: Lipschitz integration by parts for `G` and `gᵢ` in the direction `eᵢ`. Here
  -- `lineDeriv G x eᵢ = DG(x)[eᵢ]` everywhere, and `lineDeriv gᵢ x (-eᵢ) = -⟨eᵢ, Dg(x)[eᵢ]⟩` at
  -- every point where `g` is differentiable, i.e. a.e. by Rademacher's theorem.
  have hcoord : ∀ i, ∫ x, fderiv ℝ G x (b i) * gi i x
      = -∫ x, inner ℝ (b i) (fderiv ℝ g x (b i)) * G x := fun i ↦ by
    calc ∫ x, fderiv ℝ G x (b i) * gi i x
        = ∫ x, lineDeriv ℝ G x (b i) * gi i x := by
          congr 1
          funext x
          rw [(hGd x).lineDeriv_eq_fderiv]
      _ = ∫ x, lineDeriv ℝ (gi i) x (-b i) * G x :=
          hL.integral_lineDeriv_mul_eq (hgi_lip i) (hgi_c i) (b i)
      _ = ∫ x, -(inner ℝ (b i) (fderiv ℝ g x (b i)) * G x) := by
          refine integral_congr_ae ?_
          filter_upwards [hg.ae_differentiableAt (μ := volume)] with x hx
          have hd : HasFDerivAt (gi i) ((innerSL ℝ (b i)).comp (fderiv ℝ g x)) x :=
            (innerSL ℝ (b i)).hasFDerivAt.comp x hx.hasFDerivAt
          rw [hd.differentiableAt.lineDeriv_eq_fderiv, hd.fderiv]
          simp
      _ = -∫ x, inner ℝ (b i) (fderiv ℝ g x (b i)) * G x := integral_neg _
  -- The summands are integrable: the first is continuous with compact support; the second is
  -- measurable, bounded by `K` (as `‖Dg(x)‖ ≤ K`) and multiplied by the integrable `G`.
  have hint1 : ∀ i, Integrable (fun x ↦ fderiv ℝ G x (b i) * gi i x) := fun i ↦
    Continuous.integrable_of_hasCompactSupport
      (((hG.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul
        (continuous_const.inner hg.continuous)) (hgi_c i).mul_left
  have hint2 : ∀ i, Integrable (fun x ↦ inner ℝ (b i) (fderiv ℝ g x (b i)) * G x) := fun i ↦ by
    refine (hG.continuous.integrable_of_hasCompactSupport hGc).bdd_mul (c := K)
      (measurable_const.inner (measurable_fderiv_apply_const ℝ g (b i))).aestronglyMeasurable
      (Eventually.of_forall fun x ↦ ?_)
    calc ‖inner ℝ (b i) (fderiv ℝ g x (b i))‖ ≤ ‖b i‖ * ‖fderiv ℝ g x (b i)‖ :=
          norm_inner_le_norm _ _
      _ ≤ ‖b i‖ * (‖fderiv ℝ g x‖ * ‖b i‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ K := by
          simpa only [b.norm_eq_one, one_mul, mul_one] using
            norm_fderiv_le_of_lipschitz ℝ hg (x₀ := x)
  -- Step 6 (summation): `Σᵢ DG(x)[eᵢ] gᵢ(x) = DG(x)[g(x)]` and `Σᵢ ⟨eᵢ, Dg(x) eᵢ⟩ = div g(x)`.
  have hsum1 : ∀ x, fderiv ℝ G x (g x) = ∑ i, fderiv ℝ G x (b i) * gi i x := fun x ↦ by
    conv_lhs => rw [← b.sum_repr' (g x)]
    simp [gi, map_sum, map_smul, smul_eq_mul, mul_comm]
  have hsum2 : ∀ x, G x * Chapter02.euclideanDivergence g x
      = ∑ i, inner ℝ (b i) (fderiv ℝ g x (b i)) * G x := fun x ↦ by
    rw [Chapter02.euclideanDivergence_eq_sum_inner b g x, Finset.mul_sum]
    simp [mul_comm]
  have hGibp : ∫ x, G x * Chapter02.euclideanDivergence g x = -∫ x, fderiv ℝ G x (g x) := by
    simp_rw [hsum1, hsum2]
    rw [integral_finsetSum _ fun i _ ↦ hint2 i, integral_finsetSum _ fun i _ ↦ hint1 i]
    simp_rw [hcoord, Finset.sum_neg_distrib, neg_neg]
  -- Step 7: replacing `G` by `F` changes neither integrand. Off `tsupport g`, `div g` and `g`
  -- vanish; on it, `G = F` and `DG = DF`, as `G = F` on the open set `U ⊇ tsupport g`.
  have h1 : ∫ x, F x * Chapter02.euclideanDivergence g x
      = ∫ x, G x * Chapter02.euclideanDivergence g x := by
    congr 1
    funext x
    by_cases hx : x ∈ tsupport g
    · rw [hEq (hSU hx)]
    · have h0 : Chapter02.euclideanDivergence g x = 0 := by
        by_contra h
        exact hx (Chapter02.support_euclideanDivergence_subset g h)
      simp [h0]
  have h2 : ∫ x, fderiv ℝ F x (g x) = ∫ x, fderiv ℝ G x (g x) := by
    congr 1
    funext x
    by_cases hx : x ∈ tsupport g
    · rw [(Filter.eventuallyEq_of_mem (hU.mem_nhds (hSU hx)) hEq).fderiv_eq]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  rw [h1, h2, hGibp]
/-- **Simon Ch. 2, Lemma 2.5 (`L¹` part), convergence of mollifiers.** If `F ∈ L¹(ℝⁿ)` and the
kernels `ρ j` are continuous, nonnegative, of integral `1` and supported in the open ball
`ball 0 (σ j)` with `σ j → 0`, then `ρ j * F → F` in `L¹`. The `L¹` contraction
`‖ρ j * G‖₁ ≤ ‖G‖₁` (Tonelli and translation invariance) and the density of compactly supported
continuous `g` in `L¹` (inner and outer regularity, Urysohn, `MemLp.induction_dense`) reduce it
to such `g`, for which `ρ j * g → g` uniformly (`dist_convolution_le`) and both vanish off a
fixed ball. -/
theorem Submission.bv_mollifier_tendsto_L1 : ∀ (n : ℕ) (F : Rn n → ℝ) (ρ : ℕ → Rn n → ℝ) (σ : ℕ → ℝ), Integrable F volume → (∀ j, Continuous (ρ j)) → (∀ j x, 0 ≤ ρ j x) → (∀ j, Function.support (ρ j) ⊆ ball 0 (σ j)) → (∀ j, ∫ x, ρ j x = 1) → Tendsto σ atTop (𝓝 0) → Tendsto (fun j ↦ ∫⁻ x, ‖convolution (ρ j) F (ContinuousLinearMap.lsmul ℝ ℝ) volume x - F x‖ₑ) atTop (𝓝 0) := by
  intro n F ρ σ hF hρc hρn hρs hρi hσ
  -- Step 1 (L¹ contraction): `∫⁻ |ρ_j * G| ≤ ∫⁻ |G|` for integrable `G`, by Tonelli and
  -- translation invariance, since `∫⁻ |ρ_j| = ∫ ρ_j = 1`.
  have hcontr : ∀ j (G : Rn n → ℝ), Integrable G volume →
      ∫⁻ x, ‖convolution (ρ j) G (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ ≤ ∫⁻ x, ‖G x‖ₑ := by
    intro j G hG
    have hρ : Integrable (ρ j) volume := integrable_of_integral_eq_one (hρi j)
    have hmeas : AEStronglyMeasurable
        (fun p : Rn n × Rn n ↦ ContinuousLinearMap.lsmul ℝ ℝ (ρ j p.2) (G (p.1 - p.2)))
        (volume.prod volume) :=
      hρ.aestronglyMeasurable.convolution_integrand _ hG.aestronglyMeasurable
    have hρ1 : ∫⁻ t, ‖ρ j t‖ₑ = 1 := by
      have h1 := ofReal_integral_eq_lintegral_ofReal hρ (Eventually.of_forall (hρn j))
      rw [hρi j, ENNReal.ofReal_one] at h1
      rw [h1]
      exact lintegral_congr fun t ↦ Real.enorm_eq_ofReal (hρn j t)
    calc ∫⁻ x, ‖convolution (ρ j) G (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ
        ≤ ∫⁻ x, ∫⁻ t, ‖ContinuousLinearMap.lsmul ℝ ℝ (ρ j t) (G (x - t))‖ₑ :=
          lintegral_mono fun x ↦ enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ t, ∫⁻ x, ‖ContinuousLinearMap.lsmul ℝ ℝ (ρ j t) (G (x - t))‖ₑ :=
          lintegral_lintegral_swap hmeas.enorm
      _ = ∫⁻ t, ‖ρ j t‖ₑ * ∫⁻ x, ‖G x‖ₑ := by
          refine lintegral_congr fun t ↦ ?_
          simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, enorm_mul]
          rw [lintegral_const_mul' _ _ enorm_ne_top]
          congr 1
          exact lintegral_sub_right_eq_self (fun x ↦ ‖G x‖ₑ) t
      _ = (∫⁻ t, ‖ρ j t‖ₑ) * ∫⁻ x, ‖G x‖ₑ := lintegral_mul_const'' _ hρ.aestronglyMeasurable.enorm
      _ = ∫⁻ x, ‖G x‖ₑ := by rw [hρ1, one_mul]
  -- Step 2 (the `C_c` case): for `g` continuous with compact support, `ρ_j * g → g` uniformly
  -- (`dist_convolution_le` and uniform continuity) and both vanish off a fixed ball `S`.
  have hcc : ∀ g : Rn n → ℝ, Continuous g → HasCompactSupport g →
      Tendsto (fun j ↦ ∫⁻ x, ‖convolution (ρ j) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x - g x‖ₑ)
        atTop (𝓝 0) := by
    intro g hgc hgs
    obtain ⟨R, hR⟩ := hgs.isCompact.isBounded.subset_closedBall (0 : Rn n)
    have hgR : ∀ y, R < ‖y‖ → g y = 0 := by
      intro y hy
      refine image_eq_zero_of_notMem_tsupport fun hys ↦ ?_
      have h := hR hys
      rw [mem_closedBall, dist_zero_right] at h
      linarith
    set S : Set (Rn n) := closedBall (0 : Rn n) (R + 1) with hSdef
    have hSm : MeasurableSet S := measurableSet_closedBall
    have hSf : volume S ≠ ∞ := measure_closedBall_lt_top.ne
    have huc : UniformContinuous g := hgs.uniformContinuous_of_continuous hgc
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    obtain ⟨ε₀, hε₀, hε₀le⟩ : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ENNReal.ofReal ε₀ ≤ ε := by
      rcases eq_or_ne ε ∞ with h | h
      · exact ⟨1, one_pos, h ▸ le_top⟩
      · exact ⟨ε.toReal, ENNReal.toReal_pos hε.ne' h, (ENNReal.ofReal_toReal h).le⟩
    set m : ℝ := (volume S).toReal with hm
    have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
    set ε' : ℝ := ε₀ / (m + 1) with hε'eq
    have hε' : 0 < ε' := div_pos hε₀ (by linarith)
    obtain ⟨δ, hδ, hδg⟩ := Metric.uniformContinuous_iff.1 huc ε' hε'
    have hr : (0 : ℝ) < min δ 1 := lt_min hδ one_pos
    filter_upwards [hσ.eventually (Iio_mem_nhds hr)] with j hj
    have hjδ : σ j < δ := hj.trans_le (min_le_left _ _)
    have hj1 : σ j < 1 := hj.trans_le (min_le_right _ _)
    have hpt : ∀ x, ‖convolution (ρ j) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x - g x‖ₑ ≤
        S.indicator (fun _ ↦ ENNReal.ofReal ε') x := by
      intro x
      by_cases hx : x ∈ S
      · rw [indicator_of_mem hx]
        have hd := dist_convolution_le (μ := volume) (f := ρ j) (g := g) (x₀ := x) (R := σ j)
          (z₀ := g x) hε'.le (hρs j) (hρn j) (hρi j) hgc.aestronglyMeasurable
          (fun y hy ↦ (hδg ((mem_ball.1 hy).trans hjδ)).le)
        rw [dist_eq_norm] at hd
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal hd
      · rw [indicator_of_notMem hx]
        have hxR : R + 1 < ‖x‖ := by
          rw [hSdef, mem_closedBall, dist_zero_right, not_le] at hx
          exact hx
        have hconv : convolution (ρ j) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x = 0 := by
          rw [convolution_def]
          refine integral_eq_zero_of_ae (Eventually.of_forall fun t ↦ ?_)
          simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, Pi.zero_apply]
          by_cases ht : ρ j t = 0
          · rw [ht, zero_mul]
          · have htb : ‖t‖ < σ j := mem_ball_zero_iff.1 (hρs j ht)
            have hxt : ‖x‖ - ‖t‖ ≤ ‖x - t‖ := norm_sub_norm_le x t
            rw [hgR (x - t) (by linarith), mul_zero]
        rw [hconv, hgR x (by linarith), sub_zero, enorm_zero]
    calc ∫⁻ x, ‖convolution (ρ j) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x - g x‖ₑ
        ≤ ∫⁻ x, S.indicator (fun _ ↦ ENNReal.ofReal ε') x := lintegral_mono hpt
      _ = ENNReal.ofReal ε' * volume S := lintegral_indicator_const hSm _
      _ = ENNReal.ofReal (ε' * m) := by
          rw [ENNReal.ofReal_mul hε'.le, hm, ENNReal.ofReal_toReal hSf]
      _ ≤ ENNReal.ofReal ε₀ := by
          apply ENNReal.ofReal_le_ofReal
          rw [hε'eq, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
          nlinarith
      _ ≤ ε := hε₀le
  -- Step 3 (density of `C_c` in `L¹`): approximate indicators of finite-measure sets by inner
  -- (compact `K`) and outer (open `V`) regularity and an Urysohn function `K ≤ f ≤ V`, then
  -- extend to `L¹` by `MemLp.induction_dense`.
  have hdense : ∀ δ : ℝ≥0∞, δ ≠ 0 → ∃ g : Rn n → ℝ,
      eLpNorm (F - g) 1 volume ≤ δ ∧ (Continuous g ∧ HasCompactSupport g) := by
    intro δ hδ
    refine (memLp_one_iff_integrable.2 hF).induction_dense ENNReal.one_ne_top
      (fun g ↦ Continuous g ∧ HasCompactSupport g) ?_ ?_ hδ
    · intro c s hs hsfin ε hε
      obtain ⟨η, hηpos, hη⟩ := exists_Lp_half ℝ (volume : Measure (Rn n)) 1 hε
      obtain ⟨ζ, hζpos, hζ⟩ :=
        exists_eLpNorm_indicator_le (μ := (volume : Measure (Rn n))) ENNReal.one_ne_top c hηpos.ne'
      have hζpos' : (0 : ℝ≥0∞) < ζ := ENNReal.coe_pos.2 hζpos
      obtain ⟨K, hKs, hK, hKsmall⟩ := hs.exists_isCompact_sdiff_lt hsfin.ne hζpos'.ne'
      obtain ⟨V, hKV, hV, -, hVsmall⟩ :=
        hK.measurableSet.exists_isOpen_sdiff_lt (μ := volume) hK.measure_lt_top.ne hζpos'.ne'
      obtain ⟨f, hfK, hfc, hfV, hfI⟩ :=
        exists_continuousMap_one_of_isCompact_subset_isOpen hK hV hKV
      have hfzero : ∀ x ∉ V, f x = 0 := fun x hx ↦
        image_eq_zero_of_notMem_tsupport fun h ↦ hx (hfV h)
      have hgcont : Continuous (fun x ↦ f x * c) := f.continuous.mul continuous_const
      have hgc : HasCompactSupport (fun x ↦ f x * c) :=
        (show HasCompactSupport f from hfc).mul_right
      have hgmem : MemLp (fun x ↦ f x * c) 1 volume := hgcont.memLp_of_hasCompactSupport hgc
      have hdiff : ∀ x, ‖f x * c - K.indicator (fun _ ↦ c) x‖ ≤
          ‖(V \ K).indicator (fun _ ↦ c) x‖ := by
        intro x
        by_cases hxK : x ∈ K
        · simp [hxK, hfK hxK]
        · by_cases hxV : x ∈ V
          · simp only [indicator_of_notMem hxK, sub_zero,
              indicator_of_mem (mem_sdiff_of_mem hxV hxK), norm_mul, Real.norm_eq_abs,
              abs_of_nonneg (hfI x).1]
            exact mul_le_of_le_one_left (abs_nonneg c) (hfI x).2
          · simp [hxK, hxV, hfzero x hxV]
      have I1 : eLpNorm ((fun x ↦ f x * c) - K.indicator (fun _ ↦ c)) 1 volume ≤ η :=
        (eLpNorm_mono (hgmem.aestronglyMeasurable.sub
          (aestronglyMeasurable_const.indicator hK.measurableSet)) hdiff).trans
          (hζ _ hVsmall.le (hV.measurableSet.diff hK.measurableSet).nullMeasurableSet)
      have I2 : eLpNorm (K.indicator (fun _ ↦ c) - s.indicator (fun _ ↦ c)) 1 volume ≤ η := by
        rw [← eLpNorm_neg, neg_sub, ← indicator_sdiff hKs]
        exact hζ _ hKsmall.le (hs.diff hK.measurableSet).nullMeasurableSet
      refine ⟨fun x ↦ f x * c, ?_, hgcont, hgc⟩
      convert (hη _ _ I1 I2).le using 2
      ext x
      simp
    · intro f g hf hg
      exact ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  -- Step 4 (ε/3 argument): `ρ_j * F - F = ρ_j * (F - g) + (ρ_j * g - g) + (g - F)`.
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ : ℝ≥0∞, 0 < δ ∧ δ + (δ + δ) ≤ ε := by
    refine ⟨ε / 3, ENNReal.div_pos hε.ne' (by norm_num), ?_⟩
    have h3 : ε / 3 + (ε / 3 + ε / 3) = 3 * (ε / 3) := by ring
    rw [h3]
    exact ENNReal.mul_div_le
  obtain ⟨g, hgF, hg_cont, hg_supp⟩ := hdense δ hδpos.ne'
  have hg_int : Integrable g volume := hg_cont.integrable_of_hasCompactSupport hg_supp
  have hFg : Integrable (fun x ↦ F x - g x) volume := hF.sub hg_int
  have hg_close : ∫⁻ x, ‖F x - g x‖ₑ ≤ δ := by
    rwa [eLpNorm_one_eq_lintegral_enorm (hF.aestronglyMeasurable.sub hg_int.aestronglyMeasurable)]
      at hgF
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 (hcc g hg_cont hg_supp)) δ hδpos] with j hj
  have hρcs : HasCompactSupport (ρ j) :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 (σ j))
      ((hρs j).trans ball_subset_closedBall)
  have hexF : ConvolutionExists (ρ j) (fun x ↦ F x - g x) (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    hρcs.convolutionExists_left _ (hρc j) hFg.locallyIntegrable
  have hexg : ConvolutionExists (ρ j) g (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    hρcs.convolutionExists_left _ (hρc j) hg_int.locallyIntegrable
  have hsplit : ∀ x, convolution (ρ j) F (ContinuousLinearMap.lsmul ℝ ℝ) volume x =
      convolution (ρ j) (fun x ↦ F x - g x) (ContinuousLinearMap.lsmul ℝ ℝ) volume x +
        convolution (ρ j) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
    intro x
    have h := (hexF x).distrib_add (hexg x)
    have hfun : ((fun x ↦ F x - g x) + g) = F := by
      funext y
      simp
    rwa [hfun] at h
  have hpt : ∀ x, ‖convolution (ρ j) F (ContinuousLinearMap.lsmul ℝ ℝ) volume x - F x‖ₑ ≤
      ‖convolution (ρ j) (fun x ↦ F x - g x) (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ +
        (‖convolution (ρ j) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x - g x‖ₑ + ‖F x - g x‖ₑ) := by
    intro x
    rw [hsplit x]
    set a := convolution (ρ j) (fun x ↦ F x - g x) (ContinuousLinearMap.lsmul ℝ ℝ) volume x
    set b := convolution (ρ j) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x
    have : a + b - F x = a + ((b - g x) + -(F x - g x)) := by ring
    rw [this]
    refine (enorm_add_le _ _).trans ?_
    gcongr
    refine (enorm_add_le _ _).trans ?_
    rw [enorm_neg]
  have hcontg : Continuous (convolution (ρ j) g (ContinuousLinearMap.lsmul ℝ ℝ) volume) :=
    hρcs.continuous_convolution_left _ (hρc j) hg_int.locallyIntegrable
  have hm1 : AEMeasurable (fun x ↦ ‖F x - g x‖ₑ) volume := hFg.aestronglyMeasurable.enorm
  have hm2 : AEMeasurable
      (fun x ↦ ‖convolution (ρ j) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x - g x‖ₑ) volume :=
    (hcontg.sub hg_cont).measurable.enorm.aemeasurable
  have hm3 : AEMeasurable
      (fun x ↦ ‖convolution (ρ j) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x - g x‖ₑ + ‖F x - g x‖ₑ)
      volume :=
    hm2.add hm1
  calc ∫⁻ x, ‖convolution (ρ j) F (ContinuousLinearMap.lsmul ℝ ℝ) volume x - F x‖ₑ
      ≤ ∫⁻ x, (‖convolution (ρ j) (fun x ↦ F x - g x) (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ +
        (‖convolution (ρ j) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x - g x‖ₑ + ‖F x - g x‖ₑ)) :=
        lintegral_mono hpt
    _ = (∫⁻ x, ‖convolution (ρ j) (fun x ↦ F x - g x) (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ) +
        ((∫⁻ x, ‖convolution (ρ j) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x - g x‖ₑ) +
          ∫⁻ x, ‖F x - g x‖ₑ) := by
        rw [lintegral_add_right' _ hm3, lintegral_add_right' _ hm1]
    _ ≤ δ + (δ + δ) :=
        add_le_add ((hcontr j _ hFg).trans hg_close) (add_le_add hj hg_close)
    _ ≤ ε := hδ

/-- **Gradient bound for a mollification (Simon Ch. 2, proof of Lemma 2.5).** Let `W ⊆ ℝⁿ` be
open, `u ∈ L¹(W)`, and let `ρ ≥ 0` be a `C²` kernel with `spt ρ ⊆ B_σ(0)` (open ball) and
`∫ ρ = 1`. If `B_σ(x) ⊆ W` (closed ball) for every `x ∈ K`, then `w = ρ * (1_W u)` satisfies
`∫_K |Dw| ≤ |Du|(W)`. The set `O = {x : B_σ(x) ⊆ W}` is open and contains `K`, and `w` is `C²`.
For a `C¹` field `g` with compact support in `O` and `|g| ≤ 1`, integration by parts
(`Submission.bv_lipschitz_integration_by_parts`) gives `-∫ Dw[g] = ∫ w div g`, which is at most
`|Du|(W)` by the duality bound `Submission.bv_mollifier_integral_mul_div_le`. Smooth duality
(`Submission.bv_lintegral_norm_fderiv_le_of_dual_compact`) then bounds `∫_L |Dw|` for each
compact `L ⊆ O`, compact exhaustion (`Submission.bv_lintegral_open_le_of_compact`) bounds
`∫_O |Dw|`, and `K ⊆ O` finishes. -/
theorem Submission.bv_mollifier_fderiv_lintegral_le : ∀ (n : ℕ) (W K : Set (Rn n)) (u ρ : Rn n → ℝ) (σ : ℝ), IsOpen W → IntegrableOn u W volume → ContDiff ℝ 2 ρ → (∀ x, 0 ≤ ρ x) → Function.support ρ ⊆ ball 0 σ → ∫ x, ρ x = 1 → (∀ x ∈ K, closedBall x σ ⊆ W) → ∫⁻ x in K, ‖fderiv ℝ (convolution ρ (W.indicator u) (ContinuousLinearMap.lsmul ℝ ℝ) volume) x‖ₑ ≤ Chapter02.bvVariationOn u W := by
  intro n W K u ρ σ hW hu hρ hρ0 hρs hρ1 hK
  set w := convolution ρ (W.indicator u) (ContinuousLinearMap.lsmul ℝ ℝ) volume
  -- Step 0: `O = {x : B_σ(x) ⊆ W}` is open. If `B_σ(x) ⊆ W`, then some `δ`-neighbourhood of the
  -- compact set `B_σ(x)` lies in `W`, and for `|y - x| < δ` each `z ∈ B_σ(y)` is within `|x - y|`
  -- of `z + (x - y) ∈ B_σ(x)`, so `B_σ(y) ⊆ W`.
  let O : Set (Rn n) := {x | closedBall x σ ⊆ W}
  have hO : IsOpen O := by
    refine Metric.isOpen_iff.2 fun x hx ↦ ?_
    obtain ⟨δ, hδ, hδW⟩ := (isCompact_closedBall x σ).exists_cthickening_subset_open hW hx
    refine ⟨δ, hδ, fun y hy z hz ↦ hδW (mem_cthickening_of_dist_le z (z + (x - y)) δ _ ?_ ?_)⟩
    · rw [mem_closedBall, dist_eq_norm] at hz ⊢
      rwa [show z + (x - y) - x = z - y by abel]
    · rw [dist_self_add_right, ← dist_eq_norm]
      exact (mem_ball'.1 hy).le
  have hKO : K ⊆ O := fun x hx ↦ hK x hx
  -- `ρ` has compact support (in `B_σ(0)`) and `1_W u` is integrable, so `w` is `C²`.
  have hρc : HasCompactSupport ρ :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 σ)
      (hρs.trans ball_subset_closedBall)
  have hF : Integrable (W.indicator u) volume := (integrable_indicator_iff hW.measurableSet).2 hu
  have hw : ContDiff ℝ 2 w :=
    hρc.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hρ hF.locallyIntegrable
  -- Step 1 (dual bound): a `C¹` field `g` with compact support is Lipschitz, so integration by
  -- parts gives `-∫ Dw[g] = ∫ w div g`, and the duality bound applies as `tsupport g ⊆ O`.
  have hdual : ∀ g : Rn n → Rn n, ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ O →
      (∀ x, ‖g x‖ ≤ 1) →
      ENNReal.ofReal (-∫ x, fderiv ℝ w x (g x)) ≤ Chapter02.bvVariationOn u W := by
    intro g hg hgc hgO hg1
    obtain ⟨C, hC⟩ := hg.lipschitzWith_of_hasCompactSupport hgc one_ne_zero
    rw [← Submission.bv_lipschitz_integration_by_parts n w g C (hw.of_le one_le_two) hC hgc]
    exact Submission.bv_mollifier_integral_mul_div_le n W u ρ σ g hW hu hρ.continuous hρ0 hρs hρ1
      hg hgc hg1 fun y hy ↦ hgO hy
  -- Steps 2–3: smooth duality on each compact `L ⊆ O`, exhaustion of `O` by compact sets (the
  -- integrand `‖Dw‖ₑ` is continuous, hence measurable), and monotonicity in the set, `K ⊆ O`.
  have hmeas : Measurable fun x ↦ ‖fderiv ℝ w x‖ₑ :=
    (hw.continuous_fderiv two_ne_zero).enorm.measurable
  calc ∫⁻ x in K, ‖fderiv ℝ w x‖ₑ ≤ ∫⁻ x in O, ‖fderiv ℝ w x‖ₑ := lintegral_mono_set hKO
    _ ≤ Chapter02.bvVariationOn u W :=
      Submission.bv_lintegral_open_le_of_compact n O (fun x ↦ ‖fderiv ℝ w x‖ₑ) _ hO hmeas
        fun L hL hLO ↦
          Submission.bv_lintegral_norm_fderiv_le_of_dual_compact n w O L _ hw hO hL hLO hdual

/-- **Simon Ch. 2, proof of Theorem 2.6 (mollifier estimate).** If `W` is open, `u ∈ L¹(W)` and
the continuous kernel `ρ ≥ 0` has integral `1` and support in `ball 0 σ`, then
`∫_Q |ρ * (1_W u) - u| ≤ σ |Du|(W)` for every measurable `Q` with `closedBall x σ ⊆ W` for `x ∈ Q`.
For `‖z‖ < σ` the translation estimate `∫_Q |F(x - z) - F(x)| ≤ ‖z‖ |Du|(W)`, `F = 1_W u`, holds for
the smooth mollifications `w_j = ψ_j * F` (normed bumps of radius `τ_j → 0`) by the gradient bound
on the translates `Q - s z`, and passes to `F` in the `L¹` limit `w_j → F`; averaging the
translates against `ρ` gives the claim. -/
theorem Submission.bv_mollifier_sub_lintegral_le : ∀ (n : ℕ) (W Q : Set (Rn n)) (u ρ : Rn n → ℝ) (σ : ℝ), IsOpen W → IntegrableOn u W volume → MeasurableSet Q → Continuous ρ → (∀ x, 0 ≤ ρ x) → Function.support ρ ⊆ ball 0 σ → ∫ x, ρ x = 1 → (∀ x ∈ Q, closedBall x σ ⊆ W) → ∫⁻ x in Q, ‖convolution ρ (W.indicator u) (ContinuousLinearMap.lsmul ℝ ℝ) volume x - u x‖ₑ ≤ ENNReal.ofReal σ * Chapter02.bvVariationOn u W := by
  intro n W Q u ρ σ hW hu hQ hρc hρn hρs hρi hQW
  have hF : Integrable (W.indicator u) volume := (integrable_indicator_iff hW.measurableSet).2 hu
  -- Step 0: `σ > 0`, since otherwise `ball 0 σ = ∅` forces `ρ = 0`, contradicting `∫ ρ = 1`.
  have hσ : 0 < σ := by
    by_contra hσ
    have hρ0 : ρ = 0 :=
      Function.support_eq_empty_iff.1 (subset_eq_empty hρs (ball_eq_empty.2 (not_lt.1 hσ)))
    simp [hρ0] at hρi
  -- Step 1: the translation estimate `∫_Q |F(x - z) - F(x)| ≤ ‖z‖ |Du|(W)` for `‖z‖ < σ`.
  have htrans : ∀ z : Rn n, ‖z‖ < σ →
      ∫⁻ x in Q, ‖W.indicator u (x - z) - W.indicator u x‖ₑ ≤
        ENNReal.ofReal ‖z‖ * Chapter02.bvVariationOn u W := by
    intro z hz
    -- Smooth kernels `ψ j` (normed bumps) of radius `τ j = (σ - ‖z‖) / (j + 2) → 0`.
    set τ : ℕ → ℝ := fun j ↦ (σ - ‖z‖) / (j + 2)
    have hτpos : ∀ j, 0 < τ j := fun j ↦ div_pos (sub_pos.2 hz) (by positivity)
    have hτle : ∀ j, τ j ≤ σ - ‖z‖ := fun j ↦
      div_le_self (sub_pos.2 hz).le (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
    have hτlim : Tendsto τ atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    let c : ℕ → ContDiffBump (0 : Rn n) := fun j ↦
      ⟨τ j / 2, τ j, half_pos (hτpos j), half_lt_self (hτpos j)⟩
    set ψ : ℕ → Rn n → ℝ := fun j ↦ (c j).normed volume
    have hψs : ∀ j, Function.support (ψ j) ⊆ ball 0 (τ j) := fun j ↦
      (c j).support_normed_eq.subset
    set w : ℕ → Rn n → ℝ :=
      fun j ↦ convolution (ψ j) (W.indicator u) (ContinuousLinearMap.lsmul ℝ ℝ) volume
    have hwc : ∀ j, ContDiff ℝ 1 (w j) := fun j ↦
      (c j).hasCompactSupport_normed.contDiff_convolution_left _ (c j).contDiff_normed
        hF.locallyIntegrable
    -- Gradient bound on the translates `Q - s z`, `s ∈ [0, 1]`: for `x ∈ Q`,
    -- `closedBall (x - s z) (τ j) ⊆ closedBall x σ ⊆ W` because `τ j + s ‖z‖ ≤ σ`.
    have hgrad : ∀ j, ∀ s ∈ Icc (0 : ℝ) 1,
        ∫⁻ y in (fun x ↦ x - s • z) '' Q, ‖fderiv ℝ (w j) y‖ₑ ≤ Chapter02.bvVariationOn u W := by
      intro j s hs
      refine Submission.bv_mollifier_fderiv_lintegral_le n W _ u (ψ j) (τ j) hW hu
        (c j).contDiff_normed (c j).nonneg_normed (hψs j) (c j).integral_normed ?_
      rintro _ ⟨x, hx, rfl⟩
      refine (closedBall_subset_closedBall' (?_ : τ j + dist (x - s • z) x ≤ σ)).trans (hQW x hx)
      rw [dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg hs.1]
      nlinarith [hτle j, hs.2, norm_nonneg z]
    -- The smooth translation estimate for each `w j` passes to the `L¹` limit `w j → F`.
    exact Submission.bv_translate_sub_lintegral_le_of_tendsto n (W.indicator u) w Q z _
      hF.aestronglyMeasurable (fun j ↦ (hwc j).continuous.aestronglyMeasurable)
      (Submission.bv_mollifier_tendsto_L1 n (W.indicator u) ψ τ hF
        (fun j ↦ (c j).continuous_normed) (fun j ↦ (c j).nonneg_normed) hψs
        (fun j ↦ (c j).integral_normed) hτlim)
      fun j ↦ Submission.bv_translate_sub_lintegral_le_of_fderiv n (w j) Q z _ (hwc j) (hgrad j)
  -- Steps 2–3: average the translation estimate against `ρ`, whose support lies in `ball 0 σ`.
  have hconv := Submission.bv_convolution_sub_lintegral_le_of_translate n (W.indicator u) ρ Q σ
    (ENNReal.ofReal σ * Chapter02.bvVariationOn u W) hF hρc hρn hρs hρi fun t ht ↦
      (htrans t ht).trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ht.le) zero_le)
  -- On `Q` we have `1_W u = u`, because `x ∈ closedBall x σ ⊆ W`.
  refine (setLIntegral_congr_fun hQ fun x hx ↦ ?_).trans_le hconv
  simp only [indicator_of_mem (hQW x hx (mem_closedBall_self hσ.le))]
/-- **`|D|u||(O) ≤ |Du|(O)`, as used in Simon's proof of Ch. 2, Lemma 2.8.** For `O` open and
`u ∈ L¹_loc(O)`, the variation (2.4) of `|u|` on `O` is at most that of `u`. Fix an admissible
Lipschitz field `g` with `S = spt g ⊂ O` and thicken `S ⊂ V ⊂ V' ⊂⊂ O`. The mollifications
`w_j = ρ_j * (1_{V'} u)` satisfy `∫_V |Dw_j| ≤ |Du|(V') ≤ |Du|(O)`. For the smoothed absolute value
`F_j = √(w_j² + η_j²) - η_j`, integration by parts gives `∫ F_j div g = -∫ DF_j[g] ≤ ∫_V |Dw_j|`.
Since `F_j → |u|` in `L¹(V)` and `div g` is bounded and vanishes off `S`, the limit is
`∫_O |u| div g ≤ |Du|(O)`. -/
theorem Submission.bv_abs_variation_le : ∀ (n : ℕ) (O : Set (Rn n)) (u : Rn n → ℝ), IsOpen O → LocallyIntegrableOn u O volume → Chapter02.bvVariationOn (fun x ↦ |u x|) O ≤ Chapter02.bvVariationOn u O := by
  intro n O u hO hu
  -- Step 0 (reduction): it suffices to bound `∫_O |u| div g` for one admissible field `g`.
  refine iSup_le fun g ↦ iSup_le fun hg ↦ iSup_le fun hgO ↦ iSup_le fun hgn ↦ ?_
  obtain ⟨Λ, hΛ⟩ := hg
  set S : Set (Rn n) := tsupport (g : Rn n → Rn n)
  have hScpt : IsCompact S := g.hasCompactSupport.isCompact
  have hSmeas : MeasurableSet S := (isClosed_tsupport _).measurableSet
  have hg1 : ∀ x, ‖g x‖ ≤ 1 := fun x ↦
    (le_csSup (g.continuous.norm.bddAbove_range_of_hasCompactSupport g.hasCompactSupport.norm)
      (mem_range_self x)).trans hgn
  have hdiv0 : ∀ x, x ∉ S → Chapter02.euclideanDivergence (g : Rn n → Rn n) x = 0 := by
    intro x hx
    by_contra h
    exact hx (Chapter02.support_euclideanDivergence_subset _ h)
  -- Step 1 (neighbourhoods): `S ⊆ V = thickening (δ/4) S ⊆ V' = thickening δ S ⊆ O`, with
  -- `closure V'` compact in `O`, so `u` is integrable on `V'`.
  obtain ⟨δ, hδ, hδO⟩ := hScpt.exists_cthickening_subset_open hO hgO
  set V : Set (Rn n) := thickening (δ / 4) S
  set V' : Set (Rn n) := thickening δ S
  have hK : IsCompact (cthickening δ S) := hScpt.cthickening
  have hV'K : V' ⊆ cthickening δ S := thickening_subset_cthickening δ S
  have hVV' : V ⊆ V' := thickening_mono (by linarith) S
  have hSV : S ⊆ V := self_subset_thickening (by linarith) S
  have hV'O : V' ⊆ O := hV'K.trans hδO
  have hV'open : IsOpen V' := isOpen_thickening
  have hVmeas : MeasurableSet V := isOpen_thickening.measurableSet
  have hV'meas : MeasurableSet V' := hV'open.measurableSet
  have hVfin : volume V ≠ ∞ :=
    ((measure_mono (hVV'.trans hV'K)).trans_lt hK.measure_lt_top).ne
  have huV' : IntegrableOn u V' volume := (hu.integrableOn_compact_subset hδO hK).mono_set hV'K
  have huV : IntegrableOn u V volume := huV'.mono_set hVV'
  have hu'int : Integrable (V'.indicator u) volume := huV'.integrable_indicator hV'meas
  -- Step 2 (mollification): radii `σ j ≤ δ/4`, `σ j → 0`, kernels `ρ j` and `w j = ρ j * 1_{V'} u`.
  obtain ⟨η, hηpos, hη1, hηlim⟩ : ∃ η : ℕ → ℝ, (∀ j, 0 < η j) ∧ (∀ j, η j ≤ 1) ∧
      Tendsto η atTop (𝓝 0) :=
    ⟨fun j ↦ 1 / ((j : ℝ) + 1), fun j ↦ Nat.one_div_pos_of_nat,
      fun j ↦ (div_le_one (by positivity)).2 (by linarith [(j.cast_nonneg : (0 : ℝ) ≤ j)]),
      tendsto_one_div_add_atTop_nhds_zero_nat⟩
  obtain ⟨σ, hσpos, hσle, hσlim⟩ : ∃ σ : ℕ → ℝ, (∀ j, 0 < σ j) ∧ (∀ j, σ j ≤ δ / 4) ∧
      Tendsto σ atTop (𝓝 0) :=
    ⟨fun j ↦ δ / 4 * η j, fun j ↦ mul_pos (by linarith) (hηpos j),
      fun j ↦ mul_le_of_le_one_right (by linarith) (hη1 j),
      by simpa only [mul_zero] using hηlim.const_mul (δ / 4)⟩
  choose ρ hρs hρn hρsupp hρi using fun j ↦
    Submission.bv_abs_variation_exists_kernel n (σ j) (hσpos j)
  have hρ2 : ∀ j, ContDiff ℝ 2 (ρ j) := fun j ↦ (hρs j).of_le (WithTop.coe_le_coe.2 le_top)
  have hρc : ∀ j, HasCompactSupport (ρ j) := fun j ↦
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 (σ j))
      ((hρsupp j).trans ball_subset_closedBall)
  set w : ℕ → Rn n → ℝ := fun j ↦
    convolution (ρ j) (V'.indicator u) (ContinuousLinearMap.lsmul ℝ ℝ) volume
  have hw1 : ∀ j, ContDiff ℝ 1 (w j) := fun j ↦
    (hρc j).contDiff_convolution_left (n := 1) (ContinuousLinearMap.lsmul ℝ ℝ)
      ((hρs j).of_le (WithTop.coe_le_coe.2 le_top)) hu'int.locallyIntegrable
  -- `closedBall x (σ j) ⊆ V'` for `x ∈ V`, so the gradient bound of the mollifier applies:
  -- `∫_V ‖D w j‖ ≤ |Du|(V') ≤ |Du|(O)`.
  have hball : ∀ j, ∀ x ∈ V, closedBall x (σ j) ⊆ V' := fun j x hx ↦
    (closedBall_subset_cthickening hx (σ j)).trans <|
      (cthickening_thickening_subset (hσpos j).le (δ / 4) S).trans <|
        cthickening_subset_thickening' hδ (by linarith [hσle j]) S
  have hgrad : ∀ j, ∫⁻ x in V, ‖fderiv ℝ (w j) x‖ₑ ≤ Chapter02.bvVariationOn u O := fun j ↦
    (Submission.bv_mollifier_fderiv_lintegral_le n V' V u (ρ j) (σ j) hV'open huV' (hρ2 j)
      (hρn j) (hρsupp j) (hρi j) (hball j)).trans
      (Submission.bv_abs_variation_mono_set n u V' O hV'O)
  -- Step 3 (smoothed absolute value): `F j = √((w j)² + (η j)²) - η j`.
  set F : ℕ → Rn n → ℝ := fun j x ↦ Real.sqrt (w j x ^ 2 + η j ^ 2) - η j
  have hF : ∀ j, ContDiff ℝ 1 (F j) ∧ (∀ x, ‖fderiv ℝ (F j) x‖ ≤ ‖fderiv ℝ (w j) x‖) ∧
      ∀ x, abs (F j x - |w j x|) ≤ η j := fun j ↦
    Submission.bv_abs_variation_smoothed_abs n (w j) (η j) (hηpos j) (hw1 j)
  -- Step 4 (integration by parts): `∫ F j div g = -∫ D(F j)[g] ≤ ∫_S ‖D w j‖ ≤ |Du|(O)`.
  have hIbound : ∀ j, ENNReal.ofReal (∫ x, F j x * Chapter02.euclideanDivergence g x) ≤
      Chapter02.bvVariationOn u O := by
    intro j
    obtain ⟨hF1, hFd, -⟩ := hF j
    have hpt : ∀ x, ‖fderiv ℝ (F j) x (g x)‖ₑ ≤ S.indicator (fun x ↦ ‖fderiv ℝ (w j) x‖ₑ) x := by
      intro x
      by_cases hx : x ∈ S
      · rw [indicator_of_mem hx]
        calc ‖fderiv ℝ (F j) x (g x)‖ₑ ≤ ‖fderiv ℝ (F j) x‖ₑ * ‖g x‖ₑ :=
              ContinuousLinearMap.le_opENorm _ _
          _ ≤ ‖fderiv ℝ (w j) x‖ₑ * 1 := by
              gcongr
              · rw [← ofReal_norm, ← ofReal_norm]
                exact ENNReal.ofReal_le_ofReal (hFd x)
              · rw [← ofReal_norm, ← ENNReal.ofReal_one]
                exact ENNReal.ofReal_le_ofReal (hg1 x)
          _ = ‖fderiv ℝ (w j) x‖ₑ := mul_one _
      · rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx, map_zero, enorm_zero]
    rw [Submission.bv_lipschitz_integration_by_parts n (F j) g Λ hF1 hΛ g.hasCompactSupport]
    calc ENNReal.ofReal (-∫ x, fderiv ℝ (F j) x (g x))
        ≤ ‖-∫ x, fderiv ℝ (F j) x (g x)‖ₑ := Real.ofReal_le_enorm _
      _ = ‖∫ x, fderiv ℝ (F j) x (g x)‖ₑ := enorm_neg _
      _ ≤ ∫⁻ x, ‖fderiv ℝ (F j) x (g x)‖ₑ := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ x, S.indicator (fun x ↦ ‖fderiv ℝ (w j) x‖ₑ) x := lintegral_mono hpt
      _ = ∫⁻ x in S, ‖fderiv ℝ (w j) x‖ₑ := lintegral_indicator hSmeas _
      _ ≤ ∫⁻ x in V, ‖fderiv ℝ (w j) x‖ₑ := lintegral_mono_set hSV
      _ ≤ Chapter02.bvVariationOn u O := hgrad j
  -- Step 5 (limit): `div g` vanishes off `S ⊆ V`, so all integrals may be taken over `V`, where
  -- `F j → |u|` in `L¹`: `|F j - |u|| ≤ η j + |w j - 1_{V'} u|` on `V`.
  have hIV : ∀ j, ∫ x, F j x * Chapter02.euclideanDivergence g x =
      ∫ x in V, F j x * Chapter02.euclideanDivergence g x := fun j ↦
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [hdiv0 x fun h ↦ hx (hSV h), mul_zero]).symm
  have hOV : ∫ x in O, |u x| * Chapter02.euclideanDivergence g x =
      ∫ x in V, |u x| * Chapter02.euclideanDivergence g x := by
    have h1 : ∀ x ∉ O, |u x| * Chapter02.euclideanDivergence g x = 0 := fun x hx ↦ by
      rw [hdiv0 x fun h ↦ hx (hgO h), mul_zero]
    have h2 : ∀ x ∉ V, |u x| * Chapter02.euclideanDivergence g x = 0 := fun x hx ↦ by
      rw [hdiv0 x fun h ↦ hx (hSV h), mul_zero]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero h1,
      setIntegral_eq_integral_of_forall_compl_eq_zero h2]
  have hL1 : Tendsto (fun j ↦ ∫⁻ x in V, ‖F j x - |u x|‖ₑ) atTop (𝓝 0) := by
    have hconv := Submission.bv_mollifier_tendsto_L1 n (V'.indicator u) ρ σ hu'int
      (fun j ↦ (hρs j).continuous) hρn hρsupp hρi hσlim
    have hη' : Tendsto (fun j ↦ ENNReal.ofReal (η j) * volume V) atTop (𝓝 0) := by
      simpa only [ENNReal.ofReal_zero, zero_mul] using
        ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal hηlim) (Or.inr hVfin)
    have hmaj := hη'.add hconv
    rw [add_zero] at hmaj
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmaj
      (fun _ ↦ zero_le) fun j ↦ ?_
    have hpt : ∀ x ∈ V, ‖F j x - |u x|‖ₑ ≤ ENNReal.ofReal (η j) + ‖w j x - V'.indicator u x‖ₑ := by
      intro x hx
      rw [indicator_of_mem (hVV' hx) u, Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
        ← ENNReal.ofReal_add (hηpos j).le (abs_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ((abs_sub_le _ (|w j x|) _).trans (add_le_add ?_ ?_))
      · exact (hF j).2.2 x
      · exact abs_abs_sub_abs_le_abs_sub _ _
    calc ∫⁻ x in V, ‖F j x - |u x|‖ₑ
        ≤ ∫⁻ x in V, (ENNReal.ofReal (η j) + ‖w j x - V'.indicator u x‖ₑ) :=
          setLIntegral_mono' hVmeas hpt
      _ = ENNReal.ofReal (η j) * volume V + ∫⁻ x in V, ‖w j x - V'.indicator u x‖ₑ := by
          rw [lintegral_add_left measurable_const, setLIntegral_const]
      _ ≤ ENNReal.ofReal (η j) * volume V + ∫⁻ x, ‖w j x - V'.indicator u x‖ₑ := by
          gcongr
          exact Measure.restrict_le_self
  have hlim : Tendsto (fun j ↦ ∫ x in V, F j x * Chapter02.euclideanDivergence g x) atTop
      (𝓝 (∫ x in V, |u x| * Chapter02.euclideanDivergence g x)) :=
    Chapter02.tendsto_integral_mul_of_lintegral_sub (μ := volume.restrict V) (v := F)
      (u := fun x ↦ |u x|) (w := Chapter02.euclideanDivergence (g : Rn n → Rn n))
      (continuous_abs.comp_aestronglyMeasurable huV.aestronglyMeasurable)
      (Eventually.of_forall fun j ↦
        ((hF j).1.continuous.continuousOn.integrableOn_compact hK).mono_set (hVV'.trans hV'K))
      (Chapter02.measurable_euclideanDivergence _).aestronglyMeasurable
      (ae_of_all _ (Chapter02.norm_euclideanDivergence_le_of_lipschitz hΛ)) hL1
  have hlim' : Tendsto (fun j ↦ ENNReal.ofReal (∫ x, F j x * Chapter02.euclideanDivergence g x))
      atTop (𝓝 (ENNReal.ofReal (∫ x in O, |u x| * Chapter02.euclideanDivergence g x))) := by
    rw [hOV]
    refine (ENNReal.tendsto_ofReal hlim).congr fun j ↦ ?_
    rw [hIV j]
  exact le_of_tendsto' hlim' hIbound
/-- **Simon Ch. 2, Theorem 2.6 (p. 50), compactness for BV functions.** If `u_k ∈ BV_loc(U)` and
`sup_k ∫_W (|u_k| + |Du_k|(W)) < ∞` for every open `W ⊂⊂ U`, then some subsequence `u_{ψ(k)}`
converges in `L¹_loc(U)` to a `v ∈ BV_loc(U)` with `|Dv|(W) ≤ liminf_k |Du_{ψ(k)}|(W)` for every
open `W ⊂⊂ U`. A0: `∫_W |u_k| ≤ c_W` and `|Du_k|(W) ≤ c_W`. A1: for compact `Q ⊆ U` and
`W = thickening (δ / 2) Q ⊂⊂ U`, the mollifications `ρ_σ * (1_W u_k)` are equibounded,
equi-Lipschitz and within `σ c_W` of `u_k` in `L¹(Q)`, so `{u_k}` has finite `L¹(Q)`-nets.
A2: a diagonal subsequence converges in `L¹_loc(U)`. A3–A4: lower semicontinuity and the uniform
bound (2.1) pass to the limit. -/
theorem Submission.bv_compactness_theorem : BVCompactness := by
  intro n U u hBV hS
  -- `U` is open and every `u_k` is locally integrable on `U`.
  have hU : IsOpen U := (hBV 0).1
  have hloc : ∀ k, LocallyIntegrableOn (u k) U volume := fun k ↦ (hBV k).2.1
  -- Step A0: for open `W ⊂⊂ U`, one `c ≥ 0` bounds `∫_W |u_k|` and `|Du_k|(W)` for all `k`
  -- (`Lⁿ(W) ≤ Lⁿ(closure W) < ∞`).
  have hA0 : ∀ W, IsOpen W → Chapter02.IsRelativelyCompactIn W U → ∃ c : ℝ, 0 ≤ c ∧
      ∀ k, (∫⁻ x in W, ‖u k x‖ₑ) ≤ ENNReal.ofReal c ∧
        Chapter02.bvVariationOn (u k) W ≤ ENNReal.ofReal c := fun W hW hWU ↦
    Submission.bv_compactness_uniform_bounds n W u hW
      ((measure_mono subset_closure).trans_lt hWU.1.measure_lt_top) (hS W hW hWU)
  -- Step A1: `{u_k}` has finite `L¹(Q)`-nets on every compact `Q ⊆ U`.
  have hA1 : ∀ Q : Set (Rn n), IsCompact Q → Q ⊆ U → ∀ ε : ℝ, 0 < ε →
      ∃ F : Finset ℕ, ∀ k, ∃ j ∈ F, (∫⁻ x in Q, ‖u k x - u j x‖ₑ) < ENNReal.ofReal ε := by
    intro Q hQ hQU
    -- `cthickening δ Q ⊆ U`, and `W = thickening (δ / 2) Q` is open with `W ⊂⊂ U`.
    obtain ⟨δ, hδ, hδU⟩ := hQ.exists_cthickening_subset_open hU hQU
    set W := thickening (δ / 2) Q
    have hWo : IsOpen W := isOpen_thickening
    have hWcl : closure W ⊆ cthickening (δ / 2) Q := closure_thickening_subset_cthickening _ _
    have hWU : Chapter02.IsRelativelyCompactIn W U :=
      ⟨hQ.cthickening.of_isClosed_subset isClosed_closure hWcl,
        hWcl.trans ((cthickening_mono (by linarith) Q).trans hδU)⟩
    obtain ⟨c, hc, hcu⟩ := hA0 W hWo hWU
    have hWint : ∀ k, IntegrableOn (u k) W volume := fun k ↦
      ((hloc k).integrableOn_compact_subset hWU.2 hWU.1).mono_set subset_closure
    -- `F_k = 1_W u_k` is integrable with `∫ |F_k| = ∫_W |u_k| ≤ c`.
    have hFint : ∀ k, Integrable (W.indicator (u k)) volume := fun k ↦
      (hWint k).integrable_indicator hWo.measurableSet
    have hF1 : ∀ k, (∫ t, |W.indicator (u k) t|) ≤ c := fun k ↦ by
      have h := integral_norm_eq_lintegral_enorm (hFint k).aestronglyMeasurable
      simp only [Real.norm_eq_abs] at h
      rw [h]
      refine ENNReal.toReal_le_of_le_ofReal hc ?_
      simp_rw [enorm_indicator_eq_indicator_enorm]
      rw [lintegral_indicator hWo.measurableSet]
      exact (hcu k).1
    refine Submission.bv_lintegral_finite_net_of_lipschitz_approx n Q u hQ
      (fun k ↦ (hloc k).integrableOn_compact_subset hQU hQ) fun ε hε ↦ ?_
    -- Mollifier radius `σ = min (δ / 4) (ε / (c + 1))`, so `σ < δ / 2` and `σ c ≤ ε`.
    set σ := min (δ / 4) (ε / (c + 1))
    have hσ : 0 < σ := lt_min (by positivity) (by positivity)
    have hσδ : σ < δ / 2 := (min_le_left _ _).trans_lt (by linarith)
    have hσc : σ * c ≤ ε := calc
      σ * c ≤ ε / (c + 1) * c := mul_le_mul_of_nonneg_right (min_le_right _ _) hc
      _ ≤ ε := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        nlinarith
    -- Kernel: the normalized bump `ρ` at `0` with radii `σ / 2 < σ`; it is continuous, `≥ 0`,
    -- supported in `B(0, σ)`, of integral `1`, bounded by some `A` and `K`-Lipschitz.
    let f : ContDiffBump (0 : Rn n) := ⟨σ / 2, σ, half_pos hσ, half_lt_self hσ⟩
    set ρ : Rn n → ℝ := f.normed volume
    have hρcs : HasCompactSupport ρ := f.hasCompactSupport_normed
    have hρC1 : ContDiff ℝ 1 ρ := f.contDiff_normed
    obtain ⟨K, hK⟩ := hρC1.lipschitzWith_of_hasCompactSupport hρcs one_ne_zero
    obtain ⟨A, hA⟩ := f.continuous_normed.bounded_above_of_compact_support hρcs
    have hA' : ∀ x, |ρ x| ≤ A := fun x ↦ (Real.norm_eq_abs _).symm.trans_le (hA x)
    have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA' 0)
    -- `w_k = ρ * (1_W u_k)`: bounded by `A c` and `K c`-Lipschitz, by the convolution bounds.
    refine ⟨A * c, K * c, fun k ↦ convolution ρ (W.indicator (u k))
      (ContinuousLinearMap.lsmul ℝ ℝ) volume, fun k x _ ↦ ?_, fun k x _ y _ ↦ ?_, fun k ↦ ?_⟩
    · exact (Submission.bv_convolution_bound_and_lipschitz n ρ _ A K hA' hK (hFint k) x x).1.trans
        (mul_le_mul_of_nonneg_left (hF1 k) hA0)
    · calc _ ≤ K * ‖x - y‖ * (∫ t, |W.indicator (u k) t|) :=
            (Submission.bv_convolution_bound_and_lipschitz n ρ _ A K hA' hK (hFint k) x y).2
        _ ≤ K * ‖x - y‖ * c := mul_le_mul_of_nonneg_left (hF1 k) (by positivity)
        _ = K * c * ‖x - y‖ := by ring
    -- Mollifier estimate: `∫_Q |u_k - w_k| ≤ σ |Du_k|(W) ≤ σ c ≤ ε`, since `B_σ(x) ⊆ W` on `Q`.
    · have hball : ∀ x ∈ Q, closedBall x σ ⊆ W := fun x hx y hy ↦
        mem_thickening_iff.2 ⟨x, hx, (mem_closedBall.1 hy).trans_lt hσδ⟩
      calc (∫⁻ x in Q, ‖u k x - convolution ρ (W.indicator (u k))
            (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ)
          = ∫⁻ x in Q, ‖convolution ρ (W.indicator (u k))
              (ContinuousLinearMap.lsmul ℝ ℝ) volume x - u k x‖ₑ :=
            lintegral_congr fun x ↦ enorm_sub_rev _ _
        _ ≤ ENNReal.ofReal σ * Chapter02.bvVariationOn (u k) W :=
          Submission.bv_mollifier_sub_lintegral_le n W Q (u k) ρ σ hWo (hWint k)
            hQ.isClosed.measurableSet f.continuous_normed f.nonneg_normed
            f.support_normed_eq.subset f.integral_normed hball
        _ ≤ ENNReal.ofReal σ * ENNReal.ofReal c := by gcongr; exact (hcu k).2
        _ = ENNReal.ofReal (σ * c) := (ENNReal.ofReal_mul hσ.le).symm
        _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hσc
  -- Step A2: a diagonal subsequence `u_{ψ(k)}` converges in `L¹_loc(U)` to `v ∈ L¹_loc(U)`.
  obtain ⟨ψ, v, hψ, hv, hL1⟩ :=
    Submission.bv_exists_subseq_tendstoLocallyInL1On n U u hU hloc hA1
  have hlocψ : ∀ᶠ k in atTop, LocallyIntegrableOn (u (ψ k)) U volume :=
    Eventually.of_forall fun k ↦ hloc (ψ k)
  refine ⟨ψ, v, hψ, ?_, hL1, fun W hW hWU ↦ ?_⟩
  -- Step A4: by A0, every `u_{ψ(k)}` satisfies (2.1) on `W` with the constant `c_W`, and this
  -- bound passes to the `L¹_loc` limit `v`.
  · refine Chapter02.isLocallyBV_of_locallyL1_of_uniform_bound hU hv hlocψ hL1
      fun W hW hWU ↦ ?_
    obtain ⟨c, hc, hcu⟩ := hA0 W hW hWU
    exact ⟨c, hc, Eventually.of_forall fun k g hg hgW ↦
      Submission.bv_integral_div_le_of_variation_le n W (u (ψ k)) c hc (hcu (ψ k)).2 g hg hgW⟩
  -- Step A3: lower semicontinuity of `|D·|(W)` under `L¹_loc(U)` convergence.
  · exact Chapter02.bvVariationOn_le_liminf_of_locallyL1 hv hlocψ hL1 hWU

/-- The frozen Chapter 2 contract: the conjunction of all headline results. -/
theorem main_theorem : LipschitzExtension ∧ Rademacher ∧ C1Approximation ∧ WhitneyExtension ∧ LipschitzImageHausdorff ∧ EilenbergInequality ∧ BVCompactness ∧ BVPoincare ∧ BVExtensionEstimate ∧ AreaFormula ∧ FirstVariation ∧ SecondVariation ∧ StationaryIffMeanCurvatureZero ∧ SecondVariationStationary ∧ CoareaFormula ∧ C1Sard := by sorry

end GMT.Ch02
