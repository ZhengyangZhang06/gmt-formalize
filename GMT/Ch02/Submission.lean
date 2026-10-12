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
import Mathlib.Analysis.Convex.Measure

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

/-- **Simon Ch. 2, 3.4 and 3.5 (p. 54), area formula**, with the dimension of the target
measure corrected to `n` (see `AreaFormula`). The proof is the argument of the pinned SimonGMT
library (`Poincare/SimonGMT/Chapter02/Area*.lean`, not imported here), carried out inline:
the linear case 3.1 (`LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume`); the
injective case 3.2 for maps with injective derivative, by Federer's approximation of the map by
linear maps on countably many Borel pieces and Lebesgue density points; null images of critical
points (projections of the regular graphs `y ↦ (g y, ε y)`) and of nondifferentiability points
(Rademacher); countably many injective Borel branches for the multiplicity (3.4) and the weights
(3.5); and a global Lipschitz extension `g` of `f|A` whose derivative is a.e. on `A` the within
derivative of `f`. -/
theorem Submission.area_formula_theorem : AreaFormula := by
  intro n m A f K _hnm hA hL
  have hdim : Module.finrank ℝ (Rn n) = n := finrank_euclideanSpace_fin
  have hvol : (μHE[n] : Measure (Rn n)) = volume := by
    have h := InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := Rn n)
    rwa [hdim] at h
  -- Simon (3.1): the linear area formula, for any target space
  have hlin : ∀ (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F]
      [BorelSpace F] (L : Rn n →ₗ[ℝ] F) (s : Set (Rn n)),
      μHE[n] (L '' s) = ENNReal.ofReal L.normDet * volume s := by
    intro F _ _ _ _ L s
    have h := L.euclideanHausdorffMeasure_image_eq_normDet_mul_volume s
    rwa [hdim] at h
  -- `normDet L = √det(L* L)` and its continuity in `L`
  have hsqrt : ∀ (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
      (L : Rn n →L[ℝ] F), Real.sqrt ((ContinuousLinearMap.adjoint L ∘L L).det) = L.normDet := by
    intro F _ _ _ L
    rw [← L.normDet_sq]
    exact Real.sqrt_sq L.normDet_nonneg
  have hcont : ∀ (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F],
      Continuous (fun L : Rn n →L[ℝ] F ↦ L.normDet) := by
    intro F _ _ _
    have h : (fun L : Rn n →L[ℝ] F ↦ L.normDet) =
        fun L ↦ Real.sqrt ((ContinuousLinearMap.adjoint L ∘L L).det) :=
      funext fun L ↦ (hsqrt F L).symm
    rw [h]
    exact Real.continuous_sqrt.comp (ContinuousLinearMap.continuous_det.comp
      (Continuous.clm_comp ContinuousLinearMap.adjoint.continuous continuous_id))
  -- comparison of image measures from a comparison of distances
  have hcmp : ∀ (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F]
      [BorelSpace F] (u v : Rn n → F) (s : Set (Rn n)) (C : ℝ≥0), InjOn v s →
      (∀ x ∈ s, ∀ y ∈ s, dist (u x) (u y) ≤ C * dist (v x) (v y)) →
      μHE[n] (u '' s) ≤ (C : ℝ≥0∞) ^ n * μHE[n] (v '' s) := by
    intro F _ _ _ _ u v s C hv huv
    have hh : LipschitzOnWith C (u ∘ Function.invFunOn v s) (v '' s) := by
      rw [lipschitzOnWith_iff_dist_le_mul]
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simpa only [Function.comp_apply, hv.leftInvOn_invFunOn hx, hv.leftInvOn_invFunOn hy]
        using huv x hx y hy
    have himage : (u ∘ Function.invFunOn v s) '' (v '' s) = u '' s := by
      rw [image_comp, hv.invFunOn_image Subset.rfl]
    rw [← himage]
    exact Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hh
  -- near an injective linear map: Jacobian and image-measure comparisons, and injectivity
  have hrad : ∀ (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
      [MeasurableSpace F] [BorelSpace F] (L : Rn n →L[ℝ] F), Function.Injective L →
      ∀ q : ℝ≥0, 1 < q → ∃ δ : ℝ≥0, 0 < δ ∧
        (∀ B : Rn n →L[ℝ] F, ‖B - L‖ ≤ δ →
          ENNReal.ofReal B.normDet ≤ q * ENNReal.ofReal L.normDet ∧
          ENNReal.ofReal L.normDet ≤ q * ENNReal.ofReal B.normDet) ∧
        (∀ (t : Set (Rn n)) (u : Rn n → F), ApproximatesLinearOn u L t δ →
          InjOn u t ∧ μHE[n] (u '' t) ≤ q * (ENNReal.ofReal L.normDet * volume t) ∧
          ENNReal.ofReal L.normDet * volume t ≤ q * μHE[n] (u '' t)) := by
    intro F _ _ _ _ _ L hL q hq
    obtain ⟨C, -, hC⟩ : ∃ C > (0 : ℝ≥0), AntilipschitzWith C L :=
      L.toLinearMap.exists_antilipschitzWith (LinearMap.ker_eq_bot.mpr hL)
    have hJ : 0 < L.normDet := lt_of_le_of_ne L.normDet_nonneg
      (Ne.symm ((L.toLinearMap.normDet_ne_zero_tfae.out 1 5).mpr hL))
    have hmul : L.normDet < (q : ℝ) * L.normDet := lt_mul_of_one_lt_left hJ hq
    obtain ⟨ε, hε, hεL⟩ := Metric.eventually_nhds_iff.mp
      (((hcont F).continuousAt.eventually_lt continuousAt_const hmul).and
        (continuousAt_const.eventually_lt (continuousAt_const.mul (hcont F).continuousAt) hmul))
    have h1 : ∀ᶠ δ : ℝ≥0 in 𝓝 0, δ * C < 1 :=
      (continuousAt_id.mul continuousAt_const).eventually_lt continuousAt_const
        (show (0 : ℝ≥0) * C < 1 by rw [zero_mul]; exact one_pos)
    have h2 : ∀ᶠ δ : ℝ≥0 in 𝓝 0, (1 + δ * C) ^ n < q :=
      ((continuousAt_const.add (continuousAt_id.mul continuousAt_const)).pow _).eventually_lt
        continuousAt_const (show (1 + 0 * C) ^ n < q by rw [zero_mul, add_zero, one_pow]; exact hq)
    have h3 : ∀ᶠ δ : ℝ≥0 in 𝓝 0, ((1 - δ * C)⁻¹) ^ n < q := by
      have hne : (1 : ℝ≥0) - 0 * C ≠ 0 := by rw [zero_mul, tsub_zero]; exact one_ne_zero
      exact ((ContinuousAt.inv₀ (continuousAt_const.sub (continuousAt_id.mul continuousAt_const))
        hne).pow _).eventually_lt continuousAt_const
        (show ((1 - 0 * C)⁻¹) ^ n < q by rw [zero_mul, tsub_zero, inv_one, one_pow]; exact hq)
    have h4 : ∀ᶠ δ : ℝ≥0 in 𝓝 0, (δ : ℝ) < ε :=
      NNReal.continuous_coe.continuousAt.eventually_lt continuousAt_const
        (show ((0 : ℝ≥0) : ℝ) < ε by rw [NNReal.coe_zero]; exact hε)
    obtain ⟨δ, ⟨⟨⟨hδ1, hδ2⟩, hδ3⟩, hδ4⟩, hδ⟩ :=
      ((((h1.and h2).and h3).and h4).filter_mono nhdsWithin_le_nhds |>.and
        (self_mem_nhdsWithin : Ioi (0 : ℝ≥0) ∈ 𝓝[>] 0)).exists
    refine ⟨δ, hδ, fun B hB ↦ ?_, fun t u hu ↦ ?_⟩
    · obtain ⟨hup, hlo⟩ := hεL (show dist B L < ε by rw [dist_eq_norm]; exact hB.trans_lt hδ4)
      constructor
      · rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg q)]
        exact ENNReal.ofReal_le_ofReal hup.le
      · rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg q)]
        exact ENNReal.ofReal_le_ofReal hlo.le
    · have hδC : (δ : ℝ) * C < 1 := by rw [← NNReal.coe_mul]; exact hδ1
      have key : ∀ x ∈ t, ∀ y ∈ t, ‖u x - u y - (L x - L y)‖ ≤ (δ : ℝ) * C * ‖L x - L y‖ := by
        intro x hx y hy
        have h := hu x hx y hy
        rw [map_sub] at h
        have h' : ‖x - y‖ ≤ C * ‖L x - L y‖ := by
          rw [← dist_eq_norm, ← dist_eq_norm]; exact hC.le_mul_dist x y
        rw [mul_assoc]
        exact h.trans (mul_le_mul_of_nonneg_left h' δ.2)
      have hlo : ∀ x ∈ t, ∀ y ∈ t,
          dist (L x) (L y) ≤ ((1 - δ * C)⁻¹ : ℝ≥0) * dist (u x) (u y) := by
        intro x hx y hy
        rw [dist_eq_norm, dist_eq_norm, NNReal.coe_inv, NNReal.coe_sub hδ1.le, NNReal.coe_one,
          NNReal.coe_mul, inv_mul_eq_div, le_div_iff₀ (sub_pos.mpr hδC)]
        have hk := key x hx y hy
        have htri : ‖L x - L y‖ ≤ ‖u x - u y‖ + ‖u x - u y - (L x - L y)‖ := by
          have := norm_sub_le (u x - u y) (u x - u y - (L x - L y))
          rwa [sub_sub_cancel] at this
        linarith
      have hinj : InjOn u t := by
        intro x hx y hy hxy
        apply hL
        apply dist_le_zero.mp
        have := hlo x hx y hy
        rwa [hxy, dist_self, mul_zero] at this
      refine ⟨hinj, ?_, ?_⟩
      · calc
          μHE[n] (u '' t) ≤ ((1 + δ * C : ℝ≥0) : ℝ≥0∞) ^ n * μHE[n] (L '' t) := by
            apply hcmp F u L t _ hL.injOn
            intro x hx y hy
            rw [dist_eq_norm, dist_eq_norm, NNReal.coe_add, NNReal.coe_one, NNReal.coe_mul,
              add_mul, one_mul, add_comm]
            exact (norm_le_norm_sub_add _ _).trans (add_le_add_left (key x hx y hy) _)
          _ = ((1 + δ * C : ℝ≥0) : ℝ≥0∞) ^ n * (ENNReal.ofReal L.normDet * volume t) := by
            rw [← hlin F L.toLinearMap t]; rfl
          _ ≤ q * (ENNReal.ofReal L.normDet * volume t) := by
            refine mul_le_mul' ?_ le_rfl
            rw [← ENNReal.coe_pow]; exact ENNReal.coe_le_coe.mpr hδ2.le
      · calc
          ENNReal.ofReal L.normDet * volume t = μHE[n] (L '' t) := (hlin F L.toLinearMap t).symm
          _ ≤ (((1 - δ * C)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ n * μHE[n] (u '' t) := hcmp F L u t _ hinj hlo
          _ ≤ q * μHE[n] (u '' t) := by
            refine mul_le_mul' ?_ le_rfl
            rw [← ENNReal.coe_pow]; exact ENNReal.coe_le_coe.mpr hδ3.le
  -- density-point control of derivatives on approximation pieces: Mathlib's argument in
  -- `MeasureTheory/Function/Jacobian.lean`, for rectangular maps as in SimonGMT `AreaDerivative`
  open scoped Pointwise in
  have hdens : ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (u : Rn n → F)
      (s : Set (Rn n)) (B : Rn n →L[ℝ] F) (δ : ℝ≥0), ApproximatesLinearOn u B s δ →
      MeasurableSet s → ∀ u' : Rn n → Rn n →L[ℝ] F, (∀ x ∈ s, HasFDerivWithinAt u (u' x) s x) →
      ∀ᵐ x ∂(volume.restrict s), ‖u' x - B‖₊ ≤ δ := by
    intro F _ _ u s B δ hu hs u' hu'
    filter_upwards [Besicovitch.ae_tendsto_measure_inter_div volume s, ae_restrict_mem hs]
    intro x hx xs
    apply ContinuousLinearMap.opNorm_le_bound _ δ.2 fun z ↦ ?_
    suffices H : ∀ ε, 0 < ε → ‖(u' x - B) z‖ ≤ (δ + ε) * (‖z‖ + ε) + ‖u' x - B‖ * ε by
      have : Tendsto (fun ε : ℝ ↦ ((δ : ℝ) + ε) * (‖z‖ + ε) + ‖u' x - B‖ * ε) (𝓝[>] 0)
          (𝓝 ((δ + 0) * (‖z‖ + 0) + ‖u' x - B‖ * 0)) :=
        Tendsto.mono_left (Continuous.tendsto (by fun_prop) 0) nhdsWithin_le_nhds
      simp only [add_zero, mul_zero] at this
      apply le_of_tendsto_of_tendsto tendsto_const_nhds this
      filter_upwards [self_mem_nhdsWithin]
      exact H
    intro ε εpos
    have B₁ : ∀ᶠ r in 𝓝[>] (0 : ℝ), (s ∩ ({x} + r • closedBall z ε)).Nonempty :=
      Measure.eventually_nonempty_inter_smul_of_density_one volume s x hx _
        measurableSet_closedBall (measure_closedBall_pos volume z εpos).ne'
    obtain ⟨ρ, ρpos, hρ⟩ :
        ∃ ρ > 0, ball x ρ ∩ s ⊆ {y : Rn n | ‖u y - u x - (u' x) (y - x)‖ ≤ ε * ‖y - x‖} :=
      mem_nhdsWithin_iff.1 ((hu' x xs).isLittleO.bound εpos)
    have B₂ : ∀ᶠ r in 𝓝[>] (0 : ℝ), {x} + r • closedBall z ε ⊆ ball x ρ :=
      nhdsWithin_le_nhds
        (eventually_singleton_add_smul_subset isBounded_closedBall (ball_mem_nhds x ρpos))
    obtain ⟨r, ⟨y, ⟨ys, hy⟩⟩, rρ, rpos⟩ : ∃ r : ℝ, (s ∩ ({x} + r • closedBall z ε)).Nonempty ∧
        {x} + r • closedBall z ε ⊆ ball x ρ ∧ 0 < r :=
      (B₁.and (B₂.and self_mem_nhdsWithin)).exists
    obtain ⟨a, az, ya⟩ : ∃ a, a ∈ closedBall z ε ∧ y = x + r • a := by
      simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hy
      rcases hy with ⟨a, az, ha⟩
      exact ⟨a, az, by simp only [ha, add_neg_cancel_left]⟩
    have norm_a : ‖a‖ ≤ ‖z‖ + ε :=
      calc
        ‖a‖ = ‖z + (a - z)‖ := by simp only [add_sub_cancel]
        _ ≤ ‖z‖ + ‖a - z‖ := norm_add_le _ _
        _ ≤ ‖z‖ + ε := by grw [mem_closedBall_iff_norm.1 az]
    have I : r * ‖(u' x - B) a‖ ≤ r * (δ + ε) * (‖z‖ + ε) :=
      calc
        r * ‖(u' x - B) a‖ = ‖(u' x - B) (r • a)‖ := by
          simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
        _ = ‖u y - u x - B (y - x) - (u y - u x - (u' x) (y - x))‖ := by
          simp only [ya, add_sub_cancel_left, sub_sub_sub_cancel_left, FunLike.coe_sub,
            Pi.sub_apply, map_smul, smul_sub]
        _ ≤ ‖u y - u x - B (y - x)‖ + ‖u y - u x - (u' x) (y - x)‖ := norm_sub_le _ _
        _ ≤ δ * ‖y - x‖ + ε * ‖y - x‖ := add_le_add (hu _ ys _ xs) (hρ ⟨rρ hy, ys⟩)
        _ = r * (δ + ε) * ‖a‖ := by
          simp only [ya, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
          ring
        _ ≤ r * (δ + ε) * (‖z‖ + ε) := by gcongr
    calc
      ‖(u' x - B) z‖ = ‖(u' x - B) a + (u' x - B) (z - a)‖ := by
        congr 1
        simp only [FunLike.coe_sub, map_sub, Pi.sub_apply]
        abel
      _ ≤ ‖(u' x - B) a‖ + ‖(u' x - B) (z - a)‖ := norm_add_le _ _
      _ ≤ (δ + ε) * (‖z‖ + ε) + ‖u' x - B‖ * ‖z - a‖ := by
        apply add_le_add
        · rw [mul_assoc] at I; exact (mul_le_mul_iff_right₀ rpos).1 I
        · apply ContinuousLinearMap.le_opNorm
      _ ≤ (δ + ε) * (‖z‖ + ε) + ‖u' x - B‖ * ε := by
        rw [mem_closedBall_iff_norm'] at az
        gcongr
  -- Simon (3.2) for injective maps with injective derivatives, any target space
  have hV : ∀ (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
      [MeasurableSpace F] [BorelSpace F] (s : Set (Rn n)) (u : Rn n → F)
      (u' : Rn n → Rn n →L[ℝ] F), MeasurableSet s → (∀ x ∈ s, HasFDerivWithinAt u (u' x) s x) →
      (∀ x ∈ s, Function.Injective (u' x)) → InjOn u s →
      μHE[n] (u '' s) = ∫⁻ x in s, ENNReal.ofReal (u' x).normDet := by
    intro F _ _ _ _ _ s u u' hs hu' hreg hinj
    have hcomp : ∀ q : ℝ≥0, 1 < q →
        μHE[n] (u '' s) ≤ (q : ℝ≥0∞) ^ 2 * ∫⁻ x in s, ENNReal.ofReal (u' x).normDet ∧
        ∫⁻ x in s, ENNReal.ofReal (u' x).normDet ≤ (q : ℝ≥0∞) ^ 2 * μHE[n] (u '' s) := by
      intro q hq
      rcases eq_empty_or_nonempty s with rfl | hsne
      · simp
      have hchoice : ∀ L : Rn n →L[ℝ] F, ∃ δ : ℝ≥0, 0 < δ ∧ (Function.Injective L →
          (∀ B : Rn n →L[ℝ] F, ‖B - L‖ ≤ δ →
            ENNReal.ofReal B.normDet ≤ q * ENNReal.ofReal L.normDet ∧
            ENNReal.ofReal L.normDet ≤ q * ENNReal.ofReal B.normDet) ∧
          (∀ (t : Set (Rn n)) (v : Rn n → F), ApproximatesLinearOn v L t δ →
            InjOn v t ∧ μHE[n] (v '' t) ≤ q * (ENNReal.ofReal L.normDet * volume t) ∧
            ENNReal.ofReal L.normDet * volume t ≤ q * μHE[n] (v '' t))) := by
        intro L
        by_cases hL : Function.Injective L
        · obtain ⟨δ, hδ, h⟩ := hrad F L hL q hq
          exact ⟨δ, hδ, fun _ ↦ h⟩
        · exact ⟨1, one_pos, fun h ↦ (hL h).elim⟩
      choose δ hδpos hδ using hchoice
      obtain ⟨t, L, hdisj, ht, hcover, happrox, hactual⟩ :=
        exists_partition_approximatesLinearOn_of_hasFDerivWithinAt u s u' hu' δ
          (fun L ↦ (hδpos L).ne')
      have hLreg (i : ℕ) : Function.Injective (L i) := by
        obtain ⟨x, hx, hLx⟩ := hactual hsne i
        rw [hLx]; exact hreg x hx
      have hseq : s = ⋃ i, s ∩ t i := by
        rw [← inter_iUnion]; exact (inter_eq_left.mpr hcover).symm
      have hsumimage : μHE[n] (u '' s) = ∑' i, μHE[n] (u '' (s ∩ t i)) := by
        conv_lhs => rw [hseq, image_iUnion]
        apply measure_iUnion
        · intro i j hij
          exact Disjoint.image (Disjoint.mono inter_subset_right inter_subset_right (hdisj hij))
            hinj inter_subset_left inter_subset_left
        · intro i
          exact (hs.inter (ht i)).image_of_continuousOn_injOn
            (fun x hx ↦ (hu' x hx.1).continuousWithinAt.mono inter_subset_left)
            (hinj.mono inter_subset_left)
      have hsumint : ∫⁻ x in s, ENNReal.ofReal (u' x).normDet =
          ∑' i, ∫⁻ x in s ∩ t i, ENNReal.ofReal (u' x).normDet := by
        conv_lhs => rw [hseq]
        exact lintegral_iUnion (fun i ↦ hs.inter (ht i))
          (pairwise_disjoint_mono hdisj (fun _ ↦ inter_subset_right)) _
      have hpiece (i : ℕ) :
          μHE[n] (u '' (s ∩ t i)) ≤
              (q : ℝ≥0∞) ^ 2 * ∫⁻ x in s ∩ t i, ENNReal.ofReal (u' x).normDet ∧
            ∫⁻ x in s ∩ t i, ENNReal.ofReal (u' x).normDet ≤
              (q : ℝ≥0∞) ^ 2 * μHE[n] (u '' (s ∩ t i)) := by
        have hJ := (hδ (L i) (hLreg i)).1
        obtain ⟨-, harea_upper, harea_lower⟩ := (hδ (L i) (hLreg i)).2 (s ∩ t i) u (happrox i)
        have hderiv := hdens F u (s ∩ t i) (L i) (δ (L i)) (happrox i) (hs.inter (ht i)) u'
          (fun x hx ↦ (hu' x hx.1).mono inter_subset_left)
        have hJupper : ∫⁻ x in s ∩ t i, ENNReal.ofReal (u' x).normDet ≤
            q * (ENNReal.ofReal (L i).normDet * volume (s ∩ t i)) := by
          calc
            _ ≤ ∫⁻ _ in s ∩ t i, (q : ℝ≥0∞) * ENNReal.ofReal (L i).normDet := by
              apply lintegral_mono_ae
              filter_upwards [hderiv] with x hx
              exact (hJ (u' x) hx).1
            _ = _ := by rw [setLIntegral_const, mul_assoc]
        have hJlower : ENNReal.ofReal (L i).normDet * volume (s ∩ t i) ≤
            q * ∫⁻ x in s ∩ t i, ENNReal.ofReal (u' x).normDet := by
          calc
            _ = ∫⁻ _ in s ∩ t i, ENNReal.ofReal (L i).normDet := (setLIntegral_const _ _).symm
            _ ≤ ∫⁻ x in s ∩ t i, (q : ℝ≥0∞) * ENNReal.ofReal (u' x).normDet := by
              apply lintegral_mono_ae
              filter_upwards [hderiv] with x hx
              exact (hJ (u' x) hx).2
            _ = _ := lintegral_const_mul' _ _ ENNReal.coe_ne_top
        constructor
        · calc
            _ ≤ q * (ENNReal.ofReal (L i).normDet * volume (s ∩ t i)) := harea_upper
            _ ≤ q * (q * ∫⁻ x in s ∩ t i, ENNReal.ofReal (u' x).normDet) :=
              mul_le_mul' le_rfl hJlower
            _ = _ := by rw [pow_two, mul_assoc]
        · calc
            _ ≤ q * (ENNReal.ofReal (L i).normDet * volume (s ∩ t i)) := hJupper
            _ ≤ q * (q * μHE[n] (u '' (s ∩ t i))) := mul_le_mul' le_rfl harea_lower
            _ = _ := by rw [pow_two, mul_assoc]
      rw [hsumimage, hsumint, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
      exact ⟨ENNReal.tsum_le_tsum (fun i ↦ (hpiece i).1),
        ENNReal.tsum_le_tsum (fun i ↦ (hpiece i).2)⟩
    have hlimit (a : ℝ≥0∞) : Tendsto (fun q : ℝ≥0 ↦ (q : ℝ≥0∞) ^ 2 * a) (𝓝[>] 1) (𝓝 a) := by
      have hcoe : Tendsto (fun q : ℝ≥0 ↦ (q : ℝ≥0∞)) (𝓝[>] 1) (𝓝 1) :=
        (ENNReal.tendsto_coe.2 tendsto_id).mono_left nhdsWithin_le_nhds
      simpa only [one_pow, one_mul] using
        ENNReal.Tendsto.mul_const (ENNReal.Tendsto.pow (n := 2) hcoe) (Or.inl (by simp))
    apply le_antisymm
    · apply ge_of_tendsto (hlimit _)
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact (hcomp q hq).1
    · apply ge_of_tendsto (hlimit _)
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact (hcomp q hq).2
  -- a global Lipschitz extension `g` of `f|A` (coordinatewise McShane extension)
  obtain ⟨g, Kg, hg, hfg⟩ : ∃ (g : Rn n → Rn m) (Kg : ℝ≥0), LipschitzWith Kg g ∧ EqOn f g A := by
    let e := EuclideanSpace.equiv (Fin m) ℝ
    obtain ⟨G, hG, hGe⟩ :=
      ((e : Rn m →L[ℝ] (Fin m → ℝ)).lipschitzWith.comp_lipschitzOnWith hL).extend_pi
    refine ⟨e.symm ∘ G, _, (e.symm : (Fin m → ℝ) →L[ℝ] Rn m).lipschitzWith.comp hG, fun x hx ↦ ?_⟩
    change f x = e.symm (G x)
    rw [← hGe hx]
    exact (e.symm_apply_apply (f x)).symm
  have hgc : Continuous g := hg.continuous
  have hgm : Measurable g := hgc.measurable
  -- Lebesgue-null sets have `μHE[n]`-null images under `g`
  have hnullg : ∀ s : Set (Rn n), volume s = 0 → μHE[n] (g '' s) = 0 := by
    intro s hs
    have h := Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
      (hg.lipschitzOnWith (s := s))
    rw [hvol, hs, mul_zero] at h
    exact le_antisymm h bot_le
  -- a Borel subset `A'` of `A` of full measure
  obtain ⟨A', hA'A, hA'm, hA'ae⟩ := hA.exists_measurable_subset_ae_eq
  -- the within derivative of `f` on `A` is a.e. the derivative of the extension
  have hder : ∀ᵐ x ∂(volume.restrict A), fderivWithin ℝ f A x = fderiv ℝ g x := by
    obtain ⟨t, hts, ht, htae⟩ := (hA.inter
      (measurableSet_of_differentiableAt ℝ g).nullMeasurableSet).exists_measurable_subset_ae_eq
    have he : t =ᵐ[volume] A := htae.trans (by
      filter_upwards [hg.ae_differentiableAt (μ := volume)] with x hx
      simp only [mem_inter_iff, mem_ofPred_eq, hx, and_true])
    have hd (x : Rn n) (hx : x ∈ t) : HasFDerivWithinAt f (fderiv ℝ g x) A x :=
      (hts hx).2.hasFDerivAt.hasFDerivWithinAt.congr hfg (hfg (hts hx).1)
    have hz := hdens (Rn m) (fun _ ↦ (0 : Rn m)) t 0 0 (fun x _ y _ ↦ by simp) ht
      (fun x ↦ fderivWithin ℝ f A x - fderiv ℝ g x)
      (fun x hx ↦ ((((hd x hx).differentiableWithinAt.hasFDerivWithinAt.mono
        fun _ hy ↦ (hts hy).1)).sub ((hd x hx).mono fun _ hy ↦ (hts hy).1)).congr
          (fun y _ ↦ (sub_self (f y)).symm) (sub_self (f x)).symm)
    rw [Measure.restrict_congr_set he] at hz
    filter_upwards [hz] with x hx
    have hn : ‖fderivWithin ℝ f A x - fderiv ℝ g x‖₊ = 0 :=
      le_antisymm (by simpa only [sub_zero] using hx) bot_le
    exact sub_eq_zero.mp (nnnorm_eq_zero.mp hn)
  -- the regular set of `g`
  have hinjiff : ∀ L : Rn n →L[ℝ] Rn m, Function.Injective L ↔ L.normDet ≠ 0 := fun L ↦
    (L.toLinearMap.normDet_ne_zero_tfae.out 1 5).symm
  set R : Set (Rn n) := {x | DifferentiableAt ℝ g x ∧ Function.Injective (fderiv ℝ g x)}
  have hRm : MeasurableSet R := by
    have hR : R = {x | DifferentiableAt ℝ g x} ∩ (fun x ↦ (fderiv ℝ g x).normDet) ⁻¹' {0}ᶜ := by
      ext x
      simp only [R, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_compl_iff, mem_singleton_iff,
        hinjiff]
    rw [hR]
    exact (measurableSet_of_differentiableAt ℝ g).inter
      (((hcont (Rn m)).measurable.comp (measurable_fderiv ℝ g)) (measurableSet_singleton 0).compl)
  have hJ0 : ∀ x, DifferentiableAt ℝ g x → x ∉ R → (fderiv ℝ g x).normDet = 0 :=
    fun x hd hR ↦ by_contra fun hne ↦ hR ⟨hd, (hinjiff _).mpr hne⟩
  -- an auxiliary Euclidean space `W = ℝᵐ × ℝⁿ`, with its inclusions and projections
  obtain ⟨W, _, _, _, _, _, I₁, I₂, P₁, P₂, h11, h12, h21, h22, hI₁⟩ :
      ∃ (W : Type) (_ : NormedAddCommGroup W) (_ : InnerProductSpace ℝ W)
        (_ : FiniteDimensional ℝ W) (_ : MeasurableSpace W) (_ : BorelSpace W)
        (I₁ : Rn m →L[ℝ] W) (I₂ : Rn n →L[ℝ] W) (P₁ : W →L[ℝ] Rn m) (P₂ : W →L[ℝ] Rn n),
        (∀ a, P₁ (I₁ a) = a) ∧ (∀ b, P₁ (I₂ b) = 0) ∧ (∀ a, P₂ (I₁ a) = 0) ∧
        (∀ b, P₂ (I₂ b) = b) ∧ ∀ a, ‖I₁ a‖ = ‖a‖ := by
    refine ⟨WithLp 2 (Rn m × Rn n), inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance,
      (WithLp.prodContinuousLinearEquiv 2 ℝ (Rn m) (Rn n)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.inl ℝ (Rn m) (Rn n)),
      (WithLp.prodContinuousLinearEquiv 2 ℝ (Rn m) (Rn n)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.inr ℝ (Rn m) (Rn n)),
      (ContinuousLinearMap.fst ℝ (Rn m) (Rn n)).comp
        (WithLp.prodContinuousLinearEquiv 2 ℝ (Rn m) (Rn n)).toContinuousLinearMap,
      (ContinuousLinearMap.snd ℝ (Rn m) (Rn n)).comp
        (WithLp.prodContinuousLinearEquiv 2 ℝ (Rn m) (Rn n)).toContinuousLinearMap,
      fun a ↦ rfl, fun b ↦ rfl, fun a ↦ rfl, fun b ↦ rfl, fun a ↦ ?_⟩
    rw [WithLp.prod_norm_eq_of_L2]
    simp
  -- for `ε ≠ 0`, the derivative `I₁ L + ε I₂` of the graph `y ↦ (g y, ε y)` is injective
  have hMinj : ∀ (L : Rn n →L[ℝ] Rn m) (ε : ℝ), ε ≠ 0 → Function.Injective (I₁ ∘L L + ε • I₂) := by
    intro L ε hε x y hxy
    have h := congrArg P₂ hxy
    simp only [add_apply, ContinuousLinearMap.comp_apply, smul_apply, map_add, map_smul, h21, h22,
      zero_add] at h
    exact smul_right_injective (Rn n) hε h
  -- critical points have null image: compare with the regular graphs, `ε` adapted to the piece
  have hcrit :
      μHE[n] (g '' {x | DifferentiableAt ℝ g x ∧ ¬ Function.Injective (fderiv ℝ g x)}) = 0 := by
    set Cr := {x | DifferentiableAt ℝ g x ∧ ¬ Function.Injective (fderiv ℝ g x)}
    have hCrm : MeasurableSet Cr := by
      have hC : Cr = {x | DifferentiableAt ℝ g x} \ R := by
        ext x
        simp only [Cr, R, mem_ofPred_eq, Set.mem_sdiff, not_and]
        exact ⟨fun h ↦ ⟨h.1, fun _ ↦ h.2⟩, fun h ↦ ⟨h.1, h.2 h.1⟩⟩
      rw [hC]
      exact (measurableSet_of_differentiableAt ℝ g).diff hRm
    have hsmall : ∀ η : ℝ, 0 < η → ∀ L : Rn n →L[ℝ] Rn m, ∃ ε : ℝ, ∃ δ : ℝ≥0, 0 < ε ∧ 0 < δ ∧
        (¬ Function.Injective L → (I₁ ∘L L + ε • I₂).normDet < η) ∧
        ∀ (t : Set (Rn n)) (u : Rn n → W),
          ApproximatesLinearOn u (I₁ ∘L L + ε • I₂) t δ →
          μHE[n] (u '' t) ≤ 2 * (ENNReal.ofReal (I₁ ∘L L + ε • I₂).normDet * volume t) := by
      intro η hη L
      obtain ⟨ε, hεpos, hεη⟩ : ∃ ε : ℝ, 0 < ε ∧
          (¬ Function.Injective L → (I₁ ∘L L + ε • I₂).normDet < η) := by
        by_cases hL : Function.Injective L
        · exact ⟨1, one_pos, fun h ↦ (h hL).elim⟩
        have hni : ¬ Function.Injective (I₁ ∘L L + (0 : ℝ) • I₂) := fun hinj ↦
          hL fun a b hab ↦ hinj (by
            rw [add_apply, add_apply, smul_apply, smul_apply, zero_smul, zero_smul, add_zero,
              add_zero, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hab])
        have hz : (I₁ ∘L L + (0 : ℝ) • I₂).normDet = 0 :=
          ((I₁ ∘L L + (0 : ℝ) • I₂).toLinearMap.normDet_eq_zero_tfae.out 1 6).mpr hni
        have h0 : (I₁ ∘L L + (0 : ℝ) • I₂).normDet < η := by rw [hz]; exact hη
        have hc : Continuous (fun ε : ℝ ↦ (I₁ ∘L L + ε • I₂).normDet) :=
          (hcont _).comp (continuous_const.add (continuous_id.smul continuous_const))
        obtain ⟨ε, hε1, hε2⟩ := ((hc.continuousAt.eventually_lt continuousAt_const h0).filter_mono
          nhdsWithin_le_nhds |>.and (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
        exact ⟨ε, hε2, fun _ ↦ hε1⟩
      obtain ⟨δ, hδ, -, h⟩ := hrad _ (I₁ ∘L L + ε • I₂) (hMinj L ε hεpos.ne') 2 one_lt_two
      exact ⟨ε, δ, hεpos, hδ, hεη, fun t u hu ↦ (h t u hu).2.1⟩
    have hk : ∀ k : ℕ, μHE[n] (g '' (Cr ∩ closedBall 0 k)) = 0 := by
      intro k
      have hS : MeasurableSet (Cr ∩ closedBall (0 : Rn n) k) := hCrm.inter measurableSet_closedBall
      have hSfin : volume (Cr ∩ closedBall (0 : Rn n) k) ≠ ⊤ :=
        ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono inter_subset_right)
      have hbound : ∀ η : ℝ, 0 < η → μHE[n] (g '' (Cr ∩ closedBall 0 k)) ≤
          (‖P₁‖₊ : ℝ≥0∞) ^ n * 2 * volume (Cr ∩ closedBall (0 : Rn n) k) * ENNReal.ofReal η := by
        intro η hη
        choose ε δ hεpos hδpos hεη hδ using hsmall η hη
        obtain ⟨t, L, hd, ht, hcover, happrox, hactual⟩ :=
          exists_partition_approximatesLinearOn_of_hasFDerivWithinAt g (Cr ∩ closedBall 0 k)
            (fderiv ℝ g) (fun x hx ↦ hx.1.1.hasFDerivAt.hasFDerivWithinAt) δ
            (fun L ↦ (hδpos L).ne')
        rcases eq_empty_or_nonempty (Cr ∩ closedBall (0 : Rn n) k) with hE | hne
        · rw [hE, image_empty, measure_empty]; exact zero_le
        have hpiece : ∀ i, μHE[n] (g '' ((Cr ∩ closedBall 0 k) ∩ t i)) ≤ (‖P₁‖₊ : ℝ≥0∞) ^ n *
            (2 * (ENNReal.ofReal η * volume ((Cr ∩ closedBall 0 k) ∩ t i))) := by
          intro i
          obtain ⟨x, hx, hLx⟩ := hactual hne i
          have hLni : ¬ Function.Injective (L i) := by rw [hLx]; exact hx.1.2
          have hGa : ApproximatesLinearOn (fun y ↦ I₁ (g y) + ε (L i) • I₂ y)
              (I₁ ∘L L i + ε (L i) • I₂) ((Cr ∩ closedBall 0 k) ∩ t i) (δ (L i)) := by
            intro a ha b hb
            have he : I₁ (g a) + ε (L i) • I₂ a - (I₁ (g b) + ε (L i) • I₂ b) -
                (I₁ ∘L L i + ε (L i) • I₂) (a - b) = I₁ (g a - g b - L i (a - b)) := by
              simp only [add_apply, ContinuousLinearMap.comp_apply, smul_apply, map_sub]
              abel
            rw [he, hI₁]
            exact happrox i a ha b hb
          have hPG : g '' ((Cr ∩ closedBall 0 k) ∩ t i) =
              P₁ '' ((fun y ↦ I₁ (g y) + ε (L i) • I₂ y) '' ((Cr ∩ closedBall 0 k) ∩ t i)) := by
            rw [image_image]
            refine image_congr fun y _ ↦ ?_
            rw [map_add, map_smul, h11, h12, smul_zero, add_zero]
          calc
            μHE[n] (g '' ((Cr ∩ closedBall 0 k) ∩ t i))
                ≤ (‖P₁‖₊ : ℝ≥0∞) ^ n * μHE[n] ((fun y ↦ I₁ (g y) + ε (L i) • I₂ y) ''
                  ((Cr ∩ closedBall 0 k) ∩ t i)) := by
              rw [hPG]
              exact Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
                P₁.lipschitzWith.lipschitzOnWith
            _ ≤ (‖P₁‖₊ : ℝ≥0∞) ^ n * (2 * (ENNReal.ofReal (I₁ ∘L L i + ε (L i) • I₂).normDet *
                  volume ((Cr ∩ closedBall 0 k) ∩ t i))) :=
              mul_le_mul' le_rfl (hδ (L i) _ _ hGa)
            _ ≤ _ := mul_le_mul' le_rfl (mul_le_mul' le_rfl
                (mul_le_mul' (ENNReal.ofReal_le_ofReal (hεη _ hLni).le) le_rfl))
        have hU : Cr ∩ closedBall (0 : Rn n) k = ⋃ i, (Cr ∩ closedBall 0 k) ∩ t i := by
          rw [← inter_iUnion, inter_eq_left.mpr hcover]
        calc
          μHE[n] (g '' (Cr ∩ closedBall 0 k))
              ≤ ∑' i, μHE[n] (g '' ((Cr ∩ closedBall 0 k) ∩ t i)) := by
            conv_lhs => rw [hU, image_iUnion]
            exact measure_iUnion_le _
          _ ≤ ∑' i, (‖P₁‖₊ : ℝ≥0∞) ^ n *
                (2 * (ENNReal.ofReal η * volume ((Cr ∩ closedBall 0 k) ∩ t i))) :=
            ENNReal.tsum_le_tsum hpiece
          _ = (‖P₁‖₊ : ℝ≥0∞) ^ n * (2 * (ENNReal.ofReal η *
                volume (Cr ∩ closedBall (0 : Rn n) k))) := by
            rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
              ← measure_iUnion (pairwise_disjoint_mono hd fun _ ↦ inter_subset_right)
                (fun i ↦ hS.inter (ht i)), ← hU]
          _ = _ := by ring
      have hC : (‖P₁‖₊ : ℝ≥0∞) ^ n * 2 * volume (Cr ∩ closedBall (0 : Rn n) k) ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
          ENNReal.ofNat_ne_top) hSfin
      have hlim : Tendsto (fun η : ℝ ↦ (‖P₁‖₊ : ℝ≥0∞) ^ n * 2 *
          volume (Cr ∩ closedBall (0 : Rn n) k) * ENNReal.ofReal η) (𝓝[>] 0) (𝓝 0) := by
        have h := ENNReal.Tendsto.const_mul
          (ENNReal.tendsto_ofReal ((continuous_id.tendsto (0 : ℝ)).mono_left
            (nhdsWithin_le_nhds (s := Ioi 0)))) (Or.inr hC)
        rwa [id, ENNReal.ofReal_zero, mul_zero] at h
      exact le_antisymm (ge_of_tendsto hlim (by
        filter_upwards [self_mem_nhdsWithin] with η hη using hbound η hη)) bot_le
    have hcover : Cr ⊆ ⋃ k : ℕ, Cr ∩ closedBall 0 k := fun x hx ↦ by
      obtain ⟨k, hk⟩ := exists_nat_ge ‖x‖
      exact mem_iUnion.mpr ⟨k, hx, by rw [mem_closedBall, dist_zero_right]; exact hk⟩
    exact measure_mono_null (image_mono hcover) (by rw [image_iUnion]; exact measure_iUnion_null hk)
  -- nondifferentiability points have null image (Rademacher)
  have hnd : μHE[n] (g '' {x | ¬ DifferentiableAt ℝ g x}) = 0 :=
    hnullg _ (ae_iff.mp (hg.ae_differentiableAt (μ := volume)))
  -- countably many disjoint Borel pieces of `A' ∩ R` on which `g` is injective
  obtain ⟨T, hTm, hTd, hTU, hTi⟩ : ∃ T : ℕ → Set (Rn n), (∀ i, MeasurableSet (T i)) ∧
      Pairwise (Function.onFun Disjoint T) ∧ (⋃ i, T i) = A' ∩ R ∧ ∀ i, InjOn g (T i) := by
    rcases eq_empty_or_nonempty (A' ∩ R) with hE | hne
    · exact ⟨fun _ ↦ ∅, fun _ ↦ MeasurableSet.empty, fun _ _ _ ↦ disjoint_bot_left,
        by rw [hE, iUnion_empty], fun _ ↦ injOn_empty _⟩
    have hchoice : ∀ L : Rn n →L[ℝ] Rn m, ∃ δ : ℝ≥0, 0 < δ ∧ (Function.Injective L →
        ∀ (t : Set (Rn n)) (v : Rn n → Rn m), ApproximatesLinearOn v L t δ → InjOn v t) := by
      intro L
      by_cases hLi : Function.Injective L
      · obtain ⟨δ, hδ, -, h⟩ := hrad (Rn m) L hLi 2 one_lt_two
        exact ⟨δ, hδ, fun _ t v hv ↦ (h t v hv).1⟩
      · exact ⟨1, one_pos, fun h ↦ (hLi h).elim⟩
    choose δ hδpos hδ using hchoice
    obtain ⟨t, L, hd, ht, hcover, happrox, hactual⟩ :=
      exists_partition_approximatesLinearOn_of_hasFDerivWithinAt g (A' ∩ R) (fderiv ℝ g)
        (fun x hx ↦ hx.2.1.hasFDerivAt.hasFDerivWithinAt) δ (fun L ↦ (hδpos L).ne')
    refine ⟨fun i ↦ (A' ∩ R) ∩ t i, fun i ↦ (hA'm.inter hRm).inter (ht i),
      pairwise_disjoint_mono hd (fun _ ↦ inter_subset_right),
      by rw [← inter_iUnion]; exact inter_eq_left.mpr hcover, fun i ↦ ?_⟩
    obtain ⟨x, hx, hLx⟩ := hactual hne i
    exact hδ (L i) (hLx ▸ hx.2.2) _ _ (happrox i)
  have hTR : ∀ i, T i ⊆ A' ∩ R := fun i ↦ hTU ▸ subset_iUnion T i
  -- Simon (3.5) on one injective piece, with a Borel weight
  have hpiece : ∀ B : Set (Rn n), MeasurableSet B → B ⊆ R → InjOn g B →
      ∀ w : Rn n → ℝ≥0∞, Measurable w →
      Measurable (fun y ↦ ∑' x : ↥(B ∩ g ⁻¹' {y}), w x) ∧
      ∫⁻ y, ∑' x : ↥(B ∩ g ⁻¹' {y}), w x ∂μHE[n] =
        ∫⁻ x in B, ENNReal.ofReal (fderiv ℝ g x).normDet * w x := by
    intro B hB hBR hBi w hw
    have hval : ∀ x ∈ B, ∑' z : ↥(B ∩ g ⁻¹' {g x}), w z = w x := by
      intro x hx
      have hBx : B ∩ g ⁻¹' {g x} = {x} := by
        ext z
        simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
        exact ⟨fun h ↦ hBi h.1 hx h.2, by rintro rfl; exact ⟨hx, rfl⟩⟩
      rw [hBx, tsum_singleton]
    have hzero : ∀ y, y ∉ g '' B → ∑' z : ↥(B ∩ g ⁻¹' {y}), w z = 0 := by
      intro y hy
      have hBy : B ∩ g ⁻¹' {y} = ∅ := by
        ext z
        simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_empty_iff_false,
          iff_false, not_and]
        exact fun hz hzy ↦ hy ⟨z, hz, hzy⟩
      rw [hBy, tsum_empty]
    have hemb := hgc.continuousOn.measurableEmbedding hB hBi
    have hS : (fun y ↦ ∑' x : ↥(B ∩ g ⁻¹' {y}), w x) =
        Function.extend (B.domRestrict g) (fun x : B ↦ w x) (fun _ ↦ 0) := by
      funext y
      by_cases hy : y ∈ g '' B
      · obtain ⟨x, hx, rfl⟩ := hy
        rw [hval x hx]
        exact (hemb.injective.extend_apply (fun x : B ↦ w x) (fun _ ↦ 0) ⟨x, hx⟩).symm
      · rw [hzero y hy]
        exact (Function.extend_apply' (f := B.domRestrict g) (fun x : B ↦ w x) (fun _ ↦ 0) y
          fun hex ↦ hy (by rcases hex with ⟨⟨a, haB⟩, ha⟩; exact ⟨a, haB, ha⟩)).symm
    have hSm : Measurable (fun y ↦ ∑' x : ↥(B ∩ g ⁻¹' {y}), w x) := by
      rw [hS]; exact hemb.measurable_extend (hw.comp measurable_subtype_coe) measurable_const
    refine ⟨hSm, ?_⟩
    have hJm : Measurable (fun x ↦ ENNReal.ofReal (fderiv ℝ g x).normDet) :=
      ((hcont (Rn m)).measurable.comp (measurable_fderiv ℝ g)).ennreal_ofReal
    have hmap : Measure.map g ((volume.restrict B).withDensity
        (fun x ↦ ENNReal.ofReal (fderiv ℝ g x).normDet)) = μHE[n].restrict (g '' B) := by
      ext T hT
      rw [Measure.map_apply hgm hT, withDensity_apply _ (hgm hT),
        Measure.restrict_restrict (hgm hT), Measure.restrict_apply hT, inter_comm T,
        ← image_inter_preimage, inter_comm B]
      exact (hV (Rn m) _ g (fun x ↦ fderiv ℝ g x) ((hgm hT).inter hB)
        (fun x hx ↦ (hBR hx.2).1.hasFDerivAt.hasFDerivWithinAt) (fun x hx ↦ (hBR hx.2).2)
        (hBi.mono inter_subset_right)).symm
    calc
      ∫⁻ y, ∑' x : ↥(B ∩ g ⁻¹' {y}), w x ∂μHE[n]
          = ∫⁻ y in g '' B, ∑' x : ↥(B ∩ g ⁻¹' {y}), w x ∂μHE[n] := by
        refine (setLIntegral_eq_of_support_subset fun y hy ↦ ?_).symm
        by_contra h
        exact hy (hzero y h)
      _ = ∫⁻ x in B, ENNReal.ofReal (fderiv ℝ g x).normDet * ∑' z : ↥(B ∩ g ⁻¹' {g x}), w z := by
        rw [← hmap, lintegral_map hSm hgm]
        exact lintegral_withDensity_eq_lintegral_mul _ hJm (hSm.comp hgm)
      _ = ∫⁻ x in B, ENNReal.ofReal (fderiv ℝ g x).normDet * w x :=
        setLIntegral_congr_fun hB (fun x hx ↦ by rw [hval x hx])
  -- summing over the pieces: Simon (3.5) on `A' ∩ R` for Borel weights
  have hmain : ∀ w : Rn n → ℝ≥0∞, Measurable w →
      Measurable (fun y ↦ ∑' x : ↥(A' ∩ R ∩ g ⁻¹' {y}), w x) ∧
      ∫⁻ y, ∑' x : ↥(A' ∩ R ∩ g ⁻¹' {y}), w x ∂μHE[n] =
        ∫⁻ x in A' ∩ R, ENNReal.ofReal (fderiv ℝ g x).normDet * w x := by
    intro w hw
    have hsplit : ∀ y, ∑' x : ↥(A' ∩ R ∩ g ⁻¹' {y}), w x =
        ∑' i, ∑' x : ↥(T i ∩ g ⁻¹' {y}), w x := by
      intro y
      rw [← hTU, iUnion_inter]
      exact ENNReal.tsum_biUnion fun i _ j _ hij ↦
        (hTd hij).mono inter_subset_left inter_subset_left
    have hP := fun i ↦ hpiece (T i) (hTm i) (fun x hx ↦ (hTR i hx).2) (hTi i) w hw
    simp only [hsplit]
    refine ⟨Measurable.tsum fun i ↦ (hP i).1, ?_⟩
    rw [lintegral_tsum fun i ↦ (hP i).1.aemeasurable, ← hTU, lintegral_iUnion hTm hTd]
    exact tsum_congr fun i ↦ (hP i).2
  have hAJ : ∀ L : Rn n →L[ℝ] Rn m, areaJacobian L = L.normDet := fun L ↦ hsqrt (Rn m) L
  -- the weighted formula (Simon 3.5) on the original data
  have hfinal : ∀ h : Rn n → ℝ≥0∞, AEMeasurable h (volume.restrict A) →
      AEMeasurable (fun y ↦ ∑' x : ↥(A ∩ f ⁻¹' {y}), h x) μHE[n] ∧
      ∫⁻ y, (∑' x : ↥(A ∩ f ⁻¹' {y}), h x) ∂μHE[n] =
        ∫⁻ x in A, h x * ENNReal.ofReal (areaJacobian (fderivWithin ℝ f A x)) := by
    intro h hh
    have hhe : ∀ᵐ x ∂volume, x ∈ A → h x = hh.mk h x := (ae_restrict_iff'₀ hA).mp hh.ae_eq_mk
    have hbad1 : volume (A \ A') = 0 := (ae_eq_set.mp hA'ae).2
    have hbad2 : volume {x | x ∈ A ∧ h x ≠ hh.mk h x} = 0 :=
      measure_mono_null (fun x hx ↦ show ¬(x ∈ A → h x = hh.mk h x) from
        fun hcon ↦ hx.2 (hcon hx.1)) (ae_iff.mp hhe)
    have hZ : μHE[n] (g '' (A \ A') ∪ g '' {x | x ∈ A ∧ h x ≠ hh.mk h x} ∪
        g '' {x | ¬ DifferentiableAt ℝ g x} ∪
        g '' {x | DifferentiableAt ℝ g x ∧ ¬ Function.Injective (fderiv ℝ g x)}) = 0 :=
      measure_union_null (measure_union_null (measure_union_null (hnullg _ hbad1)
        (hnullg _ hbad2)) hnd) hcrit
    have hae : (fun y ↦ ∑' x : ↥(A ∩ f ⁻¹' {y}), h x) =ᵐ[μHE[n]]
        (fun y ↦ ∑' x : ↥(A' ∩ R ∩ g ⁻¹' {y}), hh.mk h x) := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hZ] with y hy
      have hset : A ∩ f ⁻¹' {y} = A' ∩ R ∩ g ⁻¹' {y} := by
        ext x
        simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
        constructor
        · rintro ⟨hxA, hfx⟩
          have hgx : g x = y := (hfg hxA).symm.trans hfx
          refine ⟨⟨by_contra fun hn ↦ hy (Or.inl (Or.inl (Or.inl ⟨x, ⟨hxA, hn⟩, hgx⟩))),
            by_contra fun hn ↦ ?_⟩, hgx⟩
          by_cases hd : DifferentiableAt ℝ g x
          · exact hy (Or.inr ⟨x, ⟨hd, fun hi ↦ hn ⟨hd, hi⟩⟩, hgx⟩)
          · exact hy (Or.inl (Or.inr ⟨x, hd, hgx⟩))
        · rintro ⟨⟨hxA', -⟩, hgx⟩
          exact ⟨hA'A hxA', (hfg (hA'A hxA')).trans hgx⟩
      show ∑' x : ↥(A ∩ f ⁻¹' {y}), h x = ∑' x : ↥(A' ∩ R ∩ g ⁻¹' {y}), hh.mk h x
      rw [hset]
      refine tsum_congr fun x ↦ by_contra fun hne ↦ ?_
      exact hy (Or.inl (Or.inl (Or.inr ⟨x, ⟨hA'A x.2.1.1, hne⟩, x.2.2⟩)))
    obtain ⟨hm1, hm2⟩ := hmain (hh.mk h) hh.measurable_mk
    refine ⟨hm1.aemeasurable.congr hae.symm, ?_⟩
    rw [lintegral_congr_ae hae, hm2, setLIntegral_congr hA'ae.symm,
      ← lintegral_indicator (hA'm.inter hRm), ← lintegral_indicator hA'm]
    refine lintegral_congr_ae ?_
    filter_upwards [hg.ae_differentiableAt (μ := volume), (ae_restrict_iff'₀ hA).mp hder, hhe]
      with x hxd hxder hxh
    by_cases hxA' : x ∈ A'
    · have hxA := hA'A hxA'
      rw [indicator_of_mem hxA', hxh hxA, hxder hxA, hAJ]
      by_cases hxR : x ∈ R
      · rw [indicator_of_mem (show x ∈ A' ∩ R from ⟨hxA', hxR⟩), mul_comm]
      · rw [indicator_of_notMem (show x ∉ A' ∩ R from fun h ↦ hxR h.2), hJ0 x hxd hxR,
          ENNReal.ofReal_zero, mul_zero]
    · rw [indicator_of_notMem hxA', indicator_of_notMem (show x ∉ A' ∩ R from fun h ↦ hxA' h.1)]
  refine ⟨?_, hfinal⟩
  have h1 := (hfinal (fun _ ↦ 1) aemeasurable_const).2
  simp only [one_mul] at h1
  rw [← h1]
  exact lintegral_congr fun y ↦ (ENNReal.tsum_set_one _).symm

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

/-- **Simon Ch. 2, proof of Theorem 1.5 (p. 44), Lusin's theorem for sets of infinite measure.** If
`S ⊆ ℝⁿ` is Borel and `ν : ℝⁿ → ℝᵐ` is Borel, then for each `ε > 0` there is a closed `C ⊆ S` with
`ν|C` continuous and `Lⁿ(S \ C) < ε` (Simon Ch. 1, Theorem 1.17, extended to `Lⁿ(S) = ∞`). On a
Borel set `E` of finite measure, closed inner approximations (weak regularity of `Lⁿ`) of
`E ∩ ν⁻¹(U)` and `E \ ν⁻¹(U)`, `U` running through a countable basis of `ℝᵐ`, cut out a closed
`F ⊆ E` on which `ν⁻¹(U)` is relatively open for every basic `U`. Applied to `S ∩ P j` for the
bounded shells `P j = {j ≤ |x| < j + 1}`, this gives a locally finite family of closed sets whose
union is the required `C`. -/
theorem Submission.c1approx_lusin_closed_continuousOn : ∀ (n m : ℕ) (S : Set (Rn n)) (ν : Rn n → Rn m), MeasurableSet S → Measurable ν → ∀ ε : ℝ, 0 < ε → ∃ C ⊆ S, IsClosed C ∧ ContinuousOn ν C ∧ volume (S \ C) < ENNReal.ofReal ε := by
  intro n m S ν hS hν ε hε
  -- Lusin on a Borel set `E` of finite measure: a countable basis `b` of `ℝᵐ`, and for each
  -- `U ∈ b` closed `A U ⊆ E ∩ ν⁻¹(U)`, `B U ⊆ E \ ν⁻¹(U)` with `Lⁿ(E \ (A U ∪ B U)) < η U`.
  have fin_lusin : ∀ E : Set (Rn n), MeasurableSet E → volume E ≠ ∞ → ∀ δ : ℝ≥0∞, δ ≠ 0 →
      ∃ F ⊆ E, IsClosed F ∧ ContinuousOn ν F ∧ volume (E \ F) < δ := by
    intro E hE hEfin δ hδ
    obtain ⟨b, hbc, -, hb⟩ := TopologicalSpace.exists_countable_basis (Rn m)
    have : Countable b := hbc.to_subtype
    have hδ2 : δ / 2 ≠ 0 := (ENNReal.half_pos hδ).ne'
    obtain ⟨η, hηpos, hηsum⟩ := ENNReal.exists_pos_sum_of_countable' hδ2 b
    have hAB : ∀ U : b, ∃ A B : Set (Rn n), A ⊆ E ∩ ν ⁻¹' (U : Set (Rn m)) ∧
        B ⊆ E \ ν ⁻¹' (U : Set (Rn m)) ∧ IsClosed A ∧ IsClosed B ∧
        volume (E \ (A ∪ B)) < η U := by
      intro U
      have hU : MeasurableSet (ν ⁻¹' (U : Set (Rn m))) := hν (hb.isOpen U.2).measurableSet
      have hη2 : η U / 2 ≠ 0 := (ENNReal.half_pos (hηpos U).ne').ne'
      obtain ⟨A, hAsub, hAc, hAμ⟩ := (hE.inter hU).exists_isClosed_sdiff_lt
        (ne_top_of_le_ne_top hEfin (measure_mono inter_subset_left)) hη2
      obtain ⟨B, hBsub, hBc, hBμ⟩ := (hE.diff hU).exists_isClosed_sdiff_lt
        (ne_top_of_le_ne_top hEfin (measure_mono sdiff_subset)) hη2
      refine ⟨A, B, hAsub, hBsub, hAc, hBc, ?_⟩
      have hsub : E \ (A ∪ B) ⊆ ((E ∩ ν ⁻¹' (U : Set (Rn m))) \ A) ∪
          ((E \ ν ⁻¹' (U : Set (Rn m))) \ B) := by
        rintro x ⟨hxE, hxAB⟩
        by_cases hx : x ∈ ν ⁻¹' (U : Set (Rn m))
        · exact Or.inl ⟨⟨hxE, hx⟩, fun h ↦ hxAB (Or.inl h)⟩
        · exact Or.inr ⟨⟨hxE, hx⟩, fun h ↦ hxAB (Or.inr h)⟩
      calc volume (E \ (A ∪ B))
          ≤ volume ((E ∩ ν ⁻¹' (U : Set (Rn m))) \ A) +
              volume ((E \ ν ⁻¹' (U : Set (Rn m))) \ B) :=
            (measure_mono hsub).trans (measure_union_le _ _)
        _ < η U / 2 + η U / 2 := ENNReal.add_lt_add hAμ hBμ
        _ = η U := ENNReal.add_halves _
    choose A B hAsub hBsub hAc hBc hABμ using hAB
    obtain ⟨F0, hF0sub, hF0c, hF0μ⟩ := hE.exists_isClosed_sdiff_lt hEfin hδ2
    refine ⟨F0 ∩ ⋂ U, (A U ∪ B U), inter_subset_left.trans hF0sub,
      hF0c.inter (isClosed_iInter fun U ↦ (hAc U).union (hBc U)), ?_, ?_⟩
    · -- For `x ∈ F` and open `t ∋ ν x` pick `U ∈ b` with `ν x ∈ U ⊆ t`; then `(B U)ᶜ` is an
      -- open neighbourhood of `x` whose points in `F` lie in `A U ⊆ ν⁻¹(U)`.
      rw [_root_.continuousOn_iff]
      intro x _ t ht hxt
      obtain ⟨U, hUb, hxU, hUt⟩ := hb.exists_subset_of_mem_open hxt ht
      refine ⟨(B ⟨U, hUb⟩)ᶜ, (hBc _).isOpen_compl, fun hxB ↦ (hBsub _ hxB).2 hxU, ?_⟩
      rintro y ⟨hyB, -, hy⟩
      rcases mem_iInter.1 hy ⟨U, hUb⟩ with hyA | hyB'
      · exact hUt (hAsub _ hyA).2
      · exact absurd hyB' hyB
    · have hsub : E \ (F0 ∩ ⋂ U, (A U ∪ B U)) ⊆ (E \ F0) ∪ ⋃ U, E \ (A U ∪ B U) := by
        rintro x ⟨hxE, hx⟩
        by_cases h0 : x ∈ F0
        · obtain ⟨U, hU⟩ : ∃ U, x ∉ A U ∪ B U := by
            by_contra! hcon
            exact hx ⟨h0, mem_iInter.2 hcon⟩
          exact Or.inr (mem_iUnion.2 ⟨U, hxE, hU⟩)
        · exact Or.inl ⟨hxE, h0⟩
      calc volume (E \ (F0 ∩ ⋂ U, (A U ∪ B U)))
          ≤ volume (E \ F0) + volume (⋃ U, E \ (A U ∪ B U)) :=
            (measure_mono hsub).trans (measure_union_le _ _)
        _ ≤ volume (E \ F0) + ∑' U, volume (E \ (A U ∪ B U)) := by
            gcongr; exact measure_iUnion_le _
        _ < δ / 2 + δ / 2 :=
            ENNReal.add_lt_add hF0μ ((ENNReal.tsum_le_tsum fun U ↦ (hABμ U).le).trans_lt hηsum)
        _ = δ := ENNReal.add_halves δ
  -- The half-open shells `P j = {j ≤ |x| < j + 1}`: Borel, bounded, and covering `ℝⁿ`.
  let P : ℕ → Set (Rn n) := fun j ↦ ball (0 : Rn n) ((j : ℝ) + 1) \ ball 0 (j : ℝ)
  have hPmeas : ∀ j, MeasurableSet (P j) := fun j ↦ measurableSet_ball.diff measurableSet_ball
  have hPfin : ∀ j, volume (S ∩ P j) ≠ ∞ := fun j ↦
    ((measure_mono (inter_subset_right.trans sdiff_subset)).trans_lt measure_ball_lt_top).ne
  have hcover : ∀ x : Rn n, ∃ j, x ∈ P j := by
    intro x
    refine ⟨⌊‖x‖⌋₊, ?_, ?_⟩
    · simp only [mem_ball, dist_zero_right]; exact Nat.lt_floor_add_one _
    · simp only [mem_ball, dist_zero_right, not_lt]; exact Nat.floor_le (norm_nonneg _)
  -- Closed `C j ⊆ S ∩ P j` with `ν|C j` continuous and losses `δ j` summing to less than `ε`.
  obtain ⟨δ, hδpos, hδsum⟩ :=
    ENNReal.exists_pos_sum_of_countable' (ENNReal.ofReal_pos.2 hε).ne' ℕ
  have hpiece : ∀ j, ∃ F ⊆ S ∩ P j, IsClosed F ∧ ContinuousOn ν F ∧
      volume ((S ∩ P j) \ F) < δ j :=
    fun j ↦ fin_lusin _ (hS.inter (hPmeas j)) (hPfin j) _ (hδpos j).ne'
  choose C hCsub hCclosed hCcont hCμ using hpiece
  -- `ball x 1` meets `C j ⊆ P j` only for `j < ⌈|x| + 1⌉`, so the family `C` is locally finite.
  have hlf : LocallyFinite C := by
    intro x
    refine ⟨ball x 1, ball_mem_nhds x one_pos, (Set.finite_Iio ⌈‖x‖ + 1⌉₊).subset ?_⟩
    rintro j ⟨y, hyC, hyx⟩
    have hyP := (hCsub j hyC).2
    simp only [P, Set.mem_sdiff, mem_ball, dist_zero_right, not_lt] at hyP
    rw [mem_ball, dist_eq_norm] at hyx
    have hy : ‖y‖ < ‖x‖ + 1 := by linarith [norm_sub_norm_le y x]
    exact Nat.lt_ceil.2 (lt_of_le_of_lt hyP.2 hy)
  refine ⟨⋃ j, C j, iUnion_subset fun j ↦ (hCsub j).trans inter_subset_left,
    hlf.isClosed_iUnion hCclosed, hlf.continuousOn_iUnion hCclosed hCcont, ?_⟩
  -- `S \ ⋃ j, C j ⊆ ⋃ j, (S ∩ P j) \ C j`, of measure at most `∑ j, δ j < ε`.
  have hsub : S \ ⋃ j, C j ⊆ ⋃ j, (S ∩ P j) \ C j := by
    rintro x ⟨hxS, hxC⟩
    obtain ⟨j, hj⟩ := hcover x
    exact mem_iUnion.2 ⟨j, ⟨hxS, hj⟩, fun h ↦ hxC (mem_iUnion.2 ⟨j, h⟩)⟩
  calc volume (S \ ⋃ j, C j) ≤ ∑' j, volume ((S ∩ P j) \ C j) :=
        (measure_mono hsub).trans (measure_iUnion_le _)
    _ ≤ ∑' j, δ j := ENNReal.tsum_le_tsum fun j ↦ (hCμ j).le
    _ < ENNReal.ofReal ε := hδsum
/-- **Simon Ch. 2, proof of Theorem 1.5 (p. 44), Borel remainder moduli.** For a Lipschitz
`f : ℝⁿ → ℝ`, a Borel `ν : ℝⁿ → ℝⁿ` and any `C ⊆ ℝⁿ` there are Borel functions `η k` with
`|f y - f x - ν(x)·(y - x)| ≤ η k x |y - x|` for `x, y ∈ C`, `0 < |y - x| < 1/(k + 1)`, and
`η k x → 0` at each `x ∈ C` where `f` has derivative `v ↦ ν(x)·v`. Simon's
`η_k(x) = sup {|R(x,y)| : y ∈ C ∩ B_{1/k}(x) \ {x}}` is replaced by the supremum of the quotients
`|R(x,q)|`, `0 < |q - x| < 1/(k + 1)`, over a countable dense `D ⊆ ℝⁿ`; it is Borel, and it
dominates `|R(x,y)|` at every `y` with `0 < |y - x| < 1/(k + 1)` by continuity in `y`. -/
theorem Submission.c1approx_measurable_remainder_modulus : ∀ (n : ℕ) (K : ℝ≥0) (C : Set (Rn n)) (f : Rn n → ℝ) (ν : Rn n → Rn n), LipschitzWith K f → Measurable ν → ∃ η : ℕ → Rn n → ℝ, (∀ k, Measurable (η k)) ∧ (∀ k : ℕ, ∀ x ∈ C, ∀ y ∈ C, 0 < ‖y - x‖ → ‖y - x‖ < 1 / ((k : ℝ) + 1) → |f y - f x - inner ℝ (ν x) (y - x)| ≤ η k x * ‖y - x‖) ∧ ∀ x ∈ C, HasFDerivAt f (innerSL ℝ (ν x)) x → Tendsto (fun k ↦ η k x) atTop (𝓝 0) := by
  intro n K C f ν hf hν
  -- A countable dense set `D ⊆ ℝⁿ`.
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Rn n)
  have : Countable D := hDc.to_subtype
  have : Nonempty D := hDd.nonempty.to_subtype
  -- The remainder quotient `ρ x q = |f q - f x - ν(x)·(q - x)| / |q - x|` lies in `[0, K + |ν x|]`.
  let ρ : Rn n → Rn n → ℝ := fun x q ↦ |f q - f x - inner ℝ (ν x) (q - x)| / ‖q - x‖
  have hρ0 (x q : Rn n) : 0 ≤ ρ x q := by positivity
  have hρK (x q : Rn n) : ρ x q ≤ K + ‖ν x‖ := by
    refine div_le_of_le_mul₀ (norm_nonneg _) (by positivity) ?_
    calc |f q - f x - inner ℝ (ν x) (q - x)| ≤ |f q - f x| + |inner ℝ (ν x) (q - x)| := abs_sub _ _
      _ ≤ K * ‖q - x‖ + ‖ν x‖ * ‖q - x‖ := by
        gcongr
        · rw [← Real.dist_eq, ← dist_eq_norm]
          exact hf.dist_le_mul q x
        · exact abs_real_inner_le_norm _ _
      _ = (K + ‖ν x‖) * ‖q - x‖ := by ring
  -- `φ k q` is `ρ (·) q` on the open set `U k q = {x | 0 < |q - x| < 1/(k + 1)}` and `0` off it;
  -- `η k = sup_{q ∈ D} φ k q`.
  let U : ℕ → Rn n → Set (Rn n) := fun k q ↦ {x | 0 < ‖q - x‖ ∧ ‖q - x‖ < 1 / ((k : ℝ) + 1)}
  have hU (k : ℕ) (q : Rn n) : IsOpen (U k q) :=
    (isOpen_lt continuous_const (continuous_const.sub continuous_id).norm).inter
      (isOpen_lt (continuous_const.sub continuous_id).norm continuous_const)
  let φ : ℕ → Rn n → Rn n → ℝ := fun k q ↦ (U k q).indicator fun x ↦ ρ x q
  have hφ0 (k : ℕ) (q x : Rn n) : 0 ≤ φ k q x := indicator_nonneg (fun x _ ↦ hρ0 x q) x
  have hbdd (k : ℕ) (x : Rn n) : BddAbove (range fun q : D ↦ φ k q x) := by
    refine ⟨K + ‖ν x‖, ?_⟩
    rintro _ ⟨q, rfl⟩
    exact (indicator_le_self' (fun x _ ↦ hρ0 x q) x).trans (hρK x q)
  let η : ℕ → Rn n → ℝ := fun k x ↦ ⨆ q : D, φ k q x
  refine ⟨η, fun k ↦ ?_, fun k x _ y _ hpos hlt ↦ ?_, fun x _ hfd ↦ ?_⟩
  · -- Each `φ k q` is Borel, and `η k` is a countable supremum of them.
    refine Measurable.iSup fun q ↦ Measurable.indicator ?_ (hU k q).measurableSet
    have hfm : Measurable f := hf.continuous.measurable
    exact (continuous_abs.measurable.comp ((measurable_const.sub hfm).sub
      (hν.inner (measurable_const.sub measurable_id)))).div (measurable_const.sub measurable_id).norm
  · -- The `q` with `|f q - f x - ν(x)·(q - x)| ≤ η k x |q - x|` form a closed set containing the
    -- points of `D` in the open set `{q | 0 < |q - x| < 1/(k + 1)}`, which are dense in it.
    have hF : IsClosed {q : Rn n | |f q - f x - inner ℝ (ν x) (q - x)| ≤ η k x * ‖q - x‖} :=
      isClosed_le ((hf.continuous.sub continuous_const).sub
        (continuous_const.inner (continuous_id.sub continuous_const))).abs
        (continuous_const.mul (continuous_id.sub continuous_const).norm)
    have hV : IsOpen {q : Rn n | 0 < ‖q - x‖ ∧ ‖q - x‖ < 1 / ((k : ℝ) + 1)} :=
      (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).inter
        (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const)
    refine closure_minimal (fun q hq ↦ ?_) hF (hDd.open_subset_closure_inter hV ⟨hpos, hlt⟩)
    have hle : φ k q x ≤ η k x := le_ciSup (hbdd k x) ⟨q, hq.2⟩
    rw [show φ k q x = ρ x q from indicator_of_mem hq.1 _] at hle
    exact (div_le_iff₀ hq.1.1).1 hle
  · -- Given `δ > 0`, the `o(|y - x|)` estimate holds on `ball x r`; once `1/(k + 1) < r`, every
    -- `φ k q x` is at most `δ / 2`.
    refine Metric.tendsto_atTop.2 fun δ hδ ↦ ?_
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 (hfd.isLittleO.bound (half_pos hδ))
    obtain ⟨k₀, hk₀⟩ := exists_nat_one_div_lt hr
    refine ⟨k₀, fun k hk ↦ ?_⟩
    have hle : η k x ≤ δ / 2 := by
      refine ciSup_le fun q ↦ indicator_apply_le' (fun hq ↦ ?_) fun _ ↦ (half_pos hδ).le
      have hqr : dist (q : Rn n) x < r := by
        rw [dist_eq_norm]
        exact hq.2.trans_le ((Nat.one_div_le_one_div hk).trans hk₀.le)
      have h := hball hqr
      rw [innerSL_apply_apply, Real.norm_eq_abs] at h
      exact (div_le_iff₀ hq.1).2 h
    have h0 : 0 ≤ η k x := Real.iSup_nonneg fun q ↦ hφ0 k q x
    rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
    exact hle.trans_lt (half_lt_self hδ)
/-- **Simon Ch. 2, proof of Theorem 1.5 (p. 44), Egorov step with a closed set.** If `C ⊆ ℝⁿ` is
Borel and the Borel functions `F k` converge to the Borel function `G` at every point of `C`, then
for each `ε > 0` there is a closed `A ⊆ C` with `Lⁿ(C \ A) < ε` such that `F k → G` uniformly on
every compact subset of `A`. Egorov's theorem on the bounded shells `P j = {j ≤ |x| < j + 1}` and
closed inner approximation (weak regularity of `Lⁿ`) give closed `Fc j ⊆ P j` of total loss `ε/2`
on which `F k → G` uniformly. The family `Fc` is locally finite, so `A = ⋃ j, Fc j` is closed, and
a compact `K ⊆ A` meets only finitely many `Fc j`. -/
theorem Submission.c1approx_egorov_closed_compact_uniform : ∀ (n : ℕ) (C : Set (Rn n)) (F : ℕ → Rn n → ℝ) (G : Rn n → ℝ), MeasurableSet C → (∀ k, Measurable (F k)) → Measurable G → (∀ x ∈ C, Tendsto (fun k ↦ F k x) atTop (𝓝 (G x))) → ∀ ε : ℝ, 0 < ε → ∃ A ⊆ C, IsClosed A ∧ volume (C \ A) < ENNReal.ofReal ε ∧ ∀ K ⊆ A, IsCompact K → TendstoUniformlyOn F G atTop K := by
  intro n C F G hC hF hG hconv ε hε
  -- The shells `P j = {j ≤ |x| < j + 1}`: Borel, bounded, and covering `ℝⁿ`.
  let P : ℕ → Set (Rn n) := fun j ↦ {x | (j : ℝ) ≤ ‖x‖ ∧ ‖x‖ < j + 1}
  have hPmeas (j : ℕ) : MeasurableSet (P j) :=
    (measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_lt measurable_norm measurable_const)
  have hCP (j : ℕ) : MeasurableSet (C ∩ P j) := hC.inter (hPmeas j)
  have hCPfin (j : ℕ) : volume (C ∩ P j) ≠ ∞ :=
    ((measure_mono fun x hx ↦ mem_closedBall_zero_iff.2 hx.2.2.le).trans_lt
      measure_closedBall_lt_top).ne
  have hmemP (x : Rn n) : x ∈ P ⌊‖x‖⌋₊ := ⟨Nat.floor_le (norm_nonneg x), Nat.lt_floor_add_one _⟩
  -- Egorov on `C ∩ P j`, then a closed inner approximation of the good set, each with loss
  -- `η j = ε 2^{-j-3}`.
  let η : ℕ → ℝ≥0∞ := fun j ↦ ENNReal.ofReal (ε / 2 ^ (j + 3))
  have hη (j : ℕ) : 0 < η j := ENNReal.ofReal_pos.2 (by positivity)
  have hEg (j : ℕ) : ∃ t ⊆ C ∩ P j, MeasurableSet t ∧ volume t ≤ η j ∧
      TendstoUniformlyOn F G atTop ((C ∩ P j) \ t) :=
    tendstoUniformlyOn_of_ae_tendsto (fun k ↦ (hF k).stronglyMeasurable) hG.stronglyMeasurable
      (hCP j) (hCPfin j) (ae_of_all _ fun x hx ↦ hconv x hx.1) (hη j)
  choose t _ ht htη htunif using hEg
  have hcl (j : ℕ) : ∃ Fc ⊆ (C ∩ P j) \ t j, IsClosed Fc ∧ volume (((C ∩ P j) \ t j) \ Fc) < η j :=
    ((hCP j).diff (ht j)).exists_isClosed_sdiff_lt
      ((measure_mono sdiff_subset).trans_lt (hCPfin j).lt_top).ne (hη j).ne'
  choose Fc hFc hFcc hFcη using hcl
  have hFcP (j : ℕ) : Fc j ⊆ P j := (hFc j).trans (sdiff_subset.trans inter_subset_right)
  refine ⟨⋃ j, Fc j, iUnion_subset fun j ↦ (hFc j).trans (sdiff_subset.trans inter_subset_left),
    ?_, ?_, ?_⟩
  · -- `ball x 1` meets `Fc j ⊆ P j` only for `j < ⌈|x|⌉ + 1`, so `⋃ j, Fc j` is closed.
    refine LocallyFinite.isClosed_iUnion (fun x ↦ ?_) hFcc
    refine ⟨ball x 1, ball_mem_nhds x one_pos, (finite_lt_nat (⌈‖x‖⌉₊ + 1)).subset ?_⟩
    rintro j ⟨y, hyF, hyx⟩
    have hj : (j : ℝ) ≤ ‖y‖ := (hFcP j hyF).1
    have hy : ‖y‖ - ‖x‖ < 1 := (norm_sub_norm_le y x).trans_lt (mem_ball_iff_norm.1 hyx)
    have hx := Nat.le_ceil ‖x‖
    have : (j : ℝ) < ⌈‖x‖⌉₊ + 1 := by linarith
    exact_mod_cast this
  · -- `C \ ⋃ j, Fc j ⊆ ⋃ j, (t j ∪ (A'_j \ Fc j))` has measure `≤ ∑ j, 2 η j = ε/2 < ε`.
    have hsub : C \ ⋃ j, Fc j ⊆ ⋃ j, (t j ∪ (((C ∩ P j) \ t j) \ Fc j)) := by
      rintro x ⟨hxC, hxA⟩
      refine mem_iUnion.2 ⟨⌊‖x‖⌋₊, ?_⟩
      by_cases hxt : x ∈ t ⌊‖x‖⌋₊
      · exact Or.inl hxt
      · exact Or.inr ⟨⟨⟨hxC, hmemP x⟩, hxt⟩, fun hxF ↦ hxA (mem_iUnion.2 ⟨_, hxF⟩)⟩
    have h2η (j : ℕ) : η j + η j = ENNReal.ofReal (ε / 2 / 2 / 2 ^ j) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    have hsum : ∑' j, (η j + η j) = ENNReal.ofReal (ε / 2) := by
      rw [tsum_congr h2η, ← ENNReal.ofReal_tsum_of_nonneg (fun j ↦ by positivity)
        (summable_geometric_two' _), tsum_geometric_two']
    calc volume (C \ ⋃ j, Fc j)
        ≤ volume (⋃ j, (t j ∪ (((C ∩ P j) \ t j) \ Fc j))) := measure_mono hsub
      _ ≤ ∑' j, volume (t j ∪ (((C ∩ P j) \ t j) \ Fc j)) := measure_iUnion_le _
      _ ≤ ∑' j, (η j + η j) := ENNReal.tsum_le_tsum fun j ↦
          (measure_union_le _ _).trans (add_le_add (htη j) (hFcη j).le)
      _ = ENNReal.ofReal (ε / 2) := hsum
      _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith)
  · -- A compact `K ⊆ A` lies in `closedBall 0 J`, hence in `Fc 0 ∪ ⋯ ∪ Fc J`, and the uniform
    -- convergence on the finitely many good sets `A'_j`, `j ≤ J`, passes to `K`.
    intro K hKA hK
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
    obtain ⟨J, hJ⟩ := exists_nat_ge R
    intro u hu
    have hev : ∀ᶠ k in atTop, ∀ j ∈ Finset.range (J + 1), ∀ x, x ∈ (C ∩ P j) \ t j →
        (G x, F k x) ∈ u :=
      (eventually_all_finset _).2 fun j _ ↦ htunif j u hu
    filter_upwards [hev] with k hk x hx
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hKA hx)
    have h1 : (j : ℝ) ≤ ‖x‖ := (hFcP j hj).1
    have h2 : ‖x‖ ≤ R := mem_closedBall_zero_iff.1 (hR hx)
    have hjJ : (j : ℝ) ≤ J := by linarith
    exact hk j (Finset.mem_range_succ_iff.2 (by exact_mod_cast hjJ)) x (hFc j hj)
/-- **Simon Ch. 2, Theorems 1.2 and 1.4.** McShane's optimal Lipschitz extension and
Rademacher's theorem. -/
theorem Submission.lipschitz_extension_and_rademacher : LipschitzExtension ∧ Rademacher := by
  refine ⟨?_, ?_⟩
  · intro X _ A f hA hf
    obtain ⟨F, hFLip, hEq, hconst⟩ :=
      Poincare.SimonGMT.Chapter02.lipschitz_extension_real_optimal hA f hf
    exact ⟨F, hFLip, hconst, hEq⟩
  · rintro n f ⟨K, hK⟩
    exact hK.ae_differentiableAt
/-- **Simon Ch. 2, toward Theorem 1.6 (pp. 42–43): a Whitney cover of `ℝⁿ ∖ A`.** Let `A ⊆ ℝⁿ` be
closed and nonempty, and put `r(x) = min{1, d(x, A)}/20`. Vitali's lemma (closed balls, `τ = 5`)
selects `J ⊆ ℝⁿ ∖ A` such that the balls `B̄(s, r(s))`, `s ∈ J`, are pairwise disjoint and every
`x ∉ A` lies within `5r(s)` of some `s ∈ J`. The sets `J(x) = {s ∈ J : |x - s| < 10r(s)}` have at
most `N` elements for one `N`, and the sets `J'(x) = {s ∈ J : B(s, 10r(s)) ∩ B(x, r(x)) ≠ ∅}` are
finite: rescaling by `r(x)` maps `J'(x) ⊇ J(x)` injectively onto a `1/2`-separated subset of
`B̄(0, 31)`. -/
theorem Submission.whitney_cover_finite_overlap : ∀ (n : ℕ) (A : Set (Rn n)), IsClosed A → A.Nonempty → ∃ (J : Set (Rn n)) (N : ℕ), J ⊆ Aᶜ ∧ (∀ x ∉ A, ∃ s ∈ J, ‖x - s‖ ≤ 5 * (min 1 (Metric.infDist s A) / 20)) ∧ (∀ x ∉ A, Set.Finite {s : Rn n | s ∈ J ∧ ‖x - s‖ < 10 * (min 1 (Metric.infDist s A) / 20)} ∧ Set.ncard {s : Rn n | s ∈ J ∧ ‖x - s‖ < 10 * (min 1 (Metric.infDist s A) / 20)} ≤ N) ∧ (∀ x ∉ A, Set.Finite {s : Rn n | s ∈ J ∧ ∃ z : Rn n, ‖z - s‖ < 10 * (min 1 (Metric.infDist s A) / 20) ∧ ‖z - x‖ < min 1 (Metric.infDist x A) / 20}) := by
  intro n A hA hne
  -- Step 1: the scale `r(x) = min{1, d(x)}/20` is in `[0, 1/20]`, positive off `A`, and
  -- `1/20`-Lipschitz.
  obtain ⟨r, hr⟩ : ∃ r : Rn n → ℝ, ∀ x, r x = min 1 (infDist x A) / 20 := ⟨_, fun _ ↦ rfl⟩
  simp only [← hr]
  have r_nonneg : ∀ x, 0 ≤ r x := fun x ↦ by
    have h : 0 ≤ min 1 (infDist x A) := le_min zero_le_one infDist_nonneg
    rw [hr]
    linarith
  have r_le : ∀ x, r x ≤ 1 / 20 := fun x ↦ by
    have h := min_le_left (1 : ℝ) (infDist x A)
    rw [hr]
    linarith
  have r_pos : ∀ x ∉ A, 0 < r x := fun x hx ↦ by
    have h : 0 < min 1 (infDist x A) := lt_min one_pos ((hA.notMem_iff_infDist_pos hne).mp hx)
    rw [hr]
    linarith
  have r_lip : ∀ x y, r x ≤ r y + ‖x - y‖ / 20 := fun x y ↦ by
    have h := ((lipschitz_infDist_pt A).const_min 1).dist_le_mul x y
    simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
    rw [dist_eq_norm] at h
    have h' := (abs_sub_le_iff.mp h).1
    rw [hr, hr]
    linarith
  -- Step 2 (F1): `|x - s| ≤ 10r(s)` gives `(2/3)r(x) ≤ r(s) ≤ 2r(x)`.
  have comp : ∀ x s, ‖x - s‖ ≤ 10 * r s → r s ≤ 2 * r x ∧ 2 * r x ≤ 3 * r s := fun x s h ↦ by
    have h₁ := r_lip x s
    have h₂ := r_lip s x
    rw [norm_sub_rev] at h₂
    constructor <;> linarith
  -- Step 3: Vitali selection on `ℝⁿ ∖ A` with radii `r ≤ 1/20` and `τ = 5`.
  obtain ⟨J, hJA, hJd, hJc⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall
    Aᶜ (fun x ↦ x) r (1 / 20) (fun x _ ↦ r_le x) 5 (by norm_num)
  -- Step 4: distinct `s, s' ∈ J` satisfy `|s - s'| > r(s)`.
  have sep : ∀ s ∈ J, ∀ s' ∈ J, s ≠ s' → r s < ‖s - s'‖ := fun s hs s' hs' hss' ↦ by
    refine not_le.mp fun h ↦ ?_
    have h₁ : s' ∈ closedBall s (r s) := by rwa [mem_closedBall, dist_eq_norm, norm_sub_rev]
    have h₂ : s' ∈ closedBall s' (r s') := mem_closedBall_self (r_nonneg s')
    exact Set.disjoint_left.mp (hJd hs hs' hss') h₁ h₂
  -- Step 5: a `δ`-separated subset of a totally bounded `K` injects into a finite `δ/2`-net of `K`.
  have packing : ∀ K : Set (Rn n), TotallyBounded K → ∀ δ : ℝ, 0 < δ → ∃ N : ℕ,
      ∀ S : Set (Rn n), S ⊆ K → S.Pairwise (fun y z ↦ δ ≤ dist y z) → S.Finite ∧ S.ncard ≤ N := by
    intro K hK δ hδ
    obtain ⟨T, hT, hKT⟩ := Metric.totallyBounded_iff.mp hK (δ / 2) (by positivity)
    refine ⟨T.ncard, fun S hSK hS ↦ ?_⟩
    have hq : ∀ y : S, ∃ q : T, dist (y : Rn n) q < δ / 2 := fun y ↦ by
      obtain ⟨q, hqT, hyq⟩ := mem_iUnion₂.mp (hKT (hSK y.2))
      exact ⟨⟨q, hqT⟩, hyq⟩
    choose q hq using hq
    have hinj : Function.Injective q := fun y y' hyy' ↦ by
      by_contra hne
      have h₁ := hS y.2 y'.2 (fun h ↦ hne (Subtype.ext h))
      have h₂ := dist_triangle (y : Rn n) (q y') y'
      have h₃ := hq y
      rw [hyy'] at h₃
      have h₄ := hq y'
      rw [dist_comm] at h₄
      linarith
    have : Finite T := hT.to_subtype
    have : Finite S := Finite.of_injective q hinj
    exact ⟨S.toFinite, Nat.card_le_card_of_injective q hinj⟩
  obtain ⟨N, hN⟩ := packing (closedBall 0 31) (isCompact_closedBall _ _).totallyBounded (1 / 2)
    (by norm_num)
  -- Steps 6–7 (F2, F3): for `x ∉ A`, `c ↦ (c - x)/r(x)` maps `J'(x)` injectively onto a
  -- `1/2`-separated subset of `B̄(0, 31)`, so `J'(x)` is finite with at most `N` elements.
  have key : ∀ x ∉ A, {s | s ∈ J ∧ ∃ z, ‖z - s‖ < 10 * r s ∧ ‖z - x‖ < r x}.Finite ∧
      {s | s ∈ J ∧ ∃ z, ‖z - s‖ < 10 * r s ∧ ‖z - x‖ < r x}.ncard ≤ N := by
    intro x hx
    have hρ := r_pos x hx
    obtain ⟨f, hf⟩ : ∃ f : Rn n → Rn n, ∀ c, f c = (r x)⁻¹ • (c - x) := ⟨_, fun _ ↦ rfl⟩
    have hfinj : Function.Injective f := fun c c' h ↦ by
      rw [hf, hf] at h
      exact sub_left_inj.mp (smul_right_injective (Rn n) (inv_ne_zero hρ.ne') h)
    have hfnorm : ∀ c, ‖f c‖ = (r x)⁻¹ * ‖c - x‖ := fun c ↦ by
      rw [hf, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hρ]
    have hfdist : ∀ c c', dist (f c) (f c') = (r x)⁻¹ * ‖c - c'‖ := fun c c' ↦ by
      rw [dist_eq_norm, hf, hf, ← smul_sub, sub_sub_sub_cancel_right, norm_smul, norm_inv,
        Real.norm_eq_abs, abs_of_pos hρ]
    -- For `s ∈ J'(x)` with witness `z`: `r(s) > r(x)/2` and `|s - x| < 31r(x)`.
    have hbd : ∀ s ∈ {s | s ∈ J ∧ ∃ z, ‖z - s‖ < 10 * r s ∧ ‖z - x‖ < r x},
        r x < 2 * r s ∧ ‖s - x‖ < 31 * r x := by
      rintro s ⟨-, z, hzs, hzx⟩
      obtain ⟨h₁, h₂⟩ := comp z s hzs.le
      have h₃ := r_lip z x
      have h₄ := r_lip x z
      rw [norm_sub_rev] at h₄
      have h₅ := norm_sub_le_norm_sub_add_norm_sub s z x
      rw [norm_sub_rev s z] at h₅
      have h₆ := r_nonneg s
      constructor <;> linarith
    have hsub : f '' {s | s ∈ J ∧ ∃ z, ‖z - s‖ < 10 * r s ∧ ‖z - x‖ < r x} ⊆ closedBall 0 31 := by
      rintro _ ⟨s, hs, rfl⟩
      rw [mem_closedBall, dist_zero_right, hfnorm, inv_mul_le_iff₀ hρ]
      linarith [(hbd s hs).2]
    have hsep : (f '' {s | s ∈ J ∧ ∃ z, ‖z - s‖ < 10 * r s ∧ ‖z - x‖ < r x}).Pairwise
        (fun y z ↦ 1 / 2 ≤ dist y z) := by
      rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩ hne
      have hss' : s ≠ s' := fun h ↦ hne (congrArg f h)
      rw [hfdist, le_inv_mul_iff₀ hρ]
      linarith [sep s hs.1 s' hs'.1 hss', (hbd s hs).1]
    obtain ⟨hfin, hcard⟩ := hN _ hsub hsep
    exact ⟨hfin.of_finite_image hfinj.injOn, Set.ncard_image_of_injective _ hfinj ▸ hcard⟩
  -- Step 8: (C1)–(C4); `J(x) ⊆ J'(x)` (take `z = x`), so (C3) follows from the bound on `J'(x)`.
  refine ⟨J, N, hJA, fun x hx ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ (key x hx).1⟩
  · obtain ⟨s, hs, hxs⟩ := hJc x hx
    exact ⟨s, hs, by simpa [dist_eq_norm] using hxs (mem_closedBall_self (r_nonneg x))⟩
  · have hJJ' : {s | s ∈ J ∧ ‖x - s‖ < 10 * r s} ⊆
        {s | s ∈ J ∧ ∃ z, ‖z - s‖ < 10 * r s ∧ ‖z - x‖ < r x} := fun s hs ↦
      ⟨hs.1, x, hs.2, by rw [sub_self, norm_zero]; exact r_pos x hx⟩
    obtain ⟨hfin, hcard⟩ := key x hx
    exact ⟨hfin.subset hJJ', (Set.ncard_le_ncard hJJ' hfin).trans hcard⟩
/-- **Simon Ch. 2, Theorem 1.6 (proof after [EG92]), Whitney partition of unity from a ball
cover.** Let `A ⊆ ℝⁿ` be closed and nonempty, `d(x) = dist(x, A)` and `r(x) = min{1, d(x)}/20`.
Let `J ⊆ ℝⁿ ∖ A` be such that the balls `B̄(s, 5r(s))`, `s ∈ J`, cover `ℝⁿ ∖ A`, each `x ∉ A`
lies in at most `N` of the balls `B(s, 10r(s))`, and only finitely many of these meet
`B(x, r(x))`. Then the normalised bumps `φ_s = θ_s / Σ_t θ_t`, with `θ_s = 1` on `B̄(s, 5r(s))`
and `θ_s = 0` off `B(s, 9r(s))`, form a locally finite `C¹` partition of unity on `ℝⁿ ∖ A`. If
`φ_s(x) ≠ 0` then `|x - p_s| ≤ 3d(x)` for a nearest point `p_s ∈ A` to `s`, and
`Σ_s ‖Dφ_s(x)‖ ≤ M/d(x)` when `d(x) ≤ 1`, with `M = 30ΛN(N + 1)` for a Lipschitz constant `Λ`
of `θ`. -/
theorem Submission.whitney_partition_of_finite_overlap_cover : ∀ (n : ℕ) (A J : Set (Rn n)) (N : ℕ), IsClosed A → A.Nonempty → J ⊆ Aᶜ → (∀ x ∉ A, ∃ s ∈ J, ‖x - s‖ ≤ 5 * (min 1 (Metric.infDist s A) / 20)) → (∀ x ∉ A, Set.Finite {s : Rn n | s ∈ J ∧ ‖x - s‖ < 10 * (min 1 (Metric.infDist s A) / 20)} ∧ Set.ncard {s : Rn n | s ∈ J ∧ ‖x - s‖ < 10 * (min 1 (Metric.infDist s A) / 20)} ≤ N) → (∀ x ∉ A, Set.Finite {s : Rn n | s ∈ J ∧ ∃ z : Rn n, ‖z - s‖ < 10 * (min 1 (Metric.infDist s A) / 20) ∧ ‖z - x‖ < min 1 (Metric.infDist x A) / 20}) → ∃ (ι : Type) (φ : ι → Rn n → ℝ) (p : ι → Rn n) (C M : ℝ), 0 ≤ C ∧ 0 ≤ M ∧ (∀ i, p i ∈ A) ∧ (∀ i, ∀ x ∉ A, ContDiffAt ℝ 1 (φ i) x) ∧ (∀ i, ∀ x ∉ A, 0 ≤ φ i x) ∧ (∀ x ∉ A, ∃ s : Finset ι, ∃ V ∈ 𝓝 x, ∀ i ∉ s, ∀ y ∈ V, φ i y = 0) ∧ (∀ x ∉ A, ∑ᶠ i, φ i x = 1) ∧ (∀ i, ∀ x ∉ A, φ i x ≠ 0 → ‖x - p i‖ ≤ C * Metric.infDist x A) ∧ (∀ x ∉ A, Metric.infDist x A ≤ 1 → ∑ᶠ i, ‖fderiv ℝ (φ i) x‖ ≤ M / Metric.infDist x A) := by
  intro n A J N hA hne hJ hcov hnear hwide
  classical
  -- The scale `r(x) = min{1, d(x)}/20`, kept opaque through its defining equation.
  obtain ⟨r, hr⟩ : ∃ r : Rn n → ℝ, ∀ x, r x = min 1 (infDist x A) / 20 := ⟨_, fun _ => rfl⟩
  simp only [← hr] at hcov hnear hwide
  have hr0 : ∀ x, 0 ≤ r x := fun x => by
    rw [hr]; exact div_nonneg (le_min zero_le_one infDist_nonneg) (by norm_num)
  have hr20 : ∀ x, 20 * r x ≤ infDist x A := fun x => by
    rw [hr]; linarith [min_le_right (1 : ℝ) (infDist x A)]
  have hrpos : ∀ x, x ∉ A → 0 < r x := fun x hx => by
    rw [hr]; exact div_pos (lt_min one_pos ((hA.notMem_iff_infDist_pos hne).mp hx)) (by norm_num)
  have hreq : ∀ x, infDist x A ≤ 1 → r x = infDist x A / 20 := fun x h => by
    rw [hr, min_eq_right h]
  -- `r` is `1/20`-Lipschitz, so the radii of nearby balls are comparable.
  have hrlip : ∀ x y, r x ≤ r y + ‖x - y‖ / 20 := fun x y => by
    have h := ((lipschitz_infDist_pt A).const_min 1).dist_le_mul x y
    simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
    have h' := (abs_sub_le_iff.mp h).1
    rw [dist_eq_norm] at h'
    rw [hr, hr]; linarith
  have hcomp : ∀ x s, ‖x - s‖ ≤ 10 * r s → r s ≤ 2 * r x ∧ 2 / 3 * r x ≤ r s := fun x s h => by
    have h₁ := hrlip x s
    have h₂ := hrlip s x
    rw [norm_sub_rev] at h₂
    have hs := hr0 s
    constructor <;> linarith
  have hJpos : ∀ s : J, 0 < r s := fun s => hrpos s (hJ s.2)
  -- The base bump `θ`: `1` on `B̄(0, 5)`, support `B(0, 9)`, `Λ`-Lipschitz.
  obtain ⟨θ, hθin, hθout⟩ : ∃ θ : ContDiffBump (0 : Rn n), θ.rIn = 5 ∧ θ.rOut = 9 :=
    ⟨⟨5, 9, by norm_num, by norm_num⟩, rfl, rfl⟩
  have hθC : ContDiff ℝ 1 θ := θ.contDiff (n := 1)
  obtain ⟨Λ, hΛ⟩ := hθC.lipschitzWith_of_hasCompactSupport θ.hasCompactSupport one_ne_zero
  -- The rescaled bumps `θ_s(x) = θ((x - s)/r_s)`.
  obtain ⟨b, hb⟩ : ∃ b : Rn n → Rn n → ℝ, ∀ s x, b s x = θ ((r s)⁻¹ • (x - s)) :=
    ⟨_, fun _ _ => rfl⟩
  have hbC : ∀ s, ContDiff ℝ 1 (b s) := fun s => by
    rw [show b s = fun x => θ ((r s)⁻¹ • (x - s)) from funext (hb s)]
    exact hθC.comp ((contDiff_id.sub contDiff_const).const_smul _)
  have hb0 : ∀ s x, 0 ≤ b s x := fun s x => by rw [hb]; exact θ.nonneg
  have hb1 : ∀ s x, b s x ≤ 1 := fun s x => by rw [hb]; exact θ.le_one
  have hbone : ∀ s x, 0 < r s → ‖x - s‖ ≤ 5 * r s → b s x = 1 := fun s x hs hx => by
    rw [hb]
    apply θ.one_of_mem_closedBall
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hs.le),
      hθin, inv_mul_le_iff₀ hs]
    linarith
  have hbzero : ∀ s x, 0 < r s → 9 * r s ≤ ‖x - s‖ → b s x = 0 := fun s x hs hx => by
    rw [hb]
    apply Function.notMem_support.mp
    rw [θ.support_eq, mem_ball, dist_zero_right, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hs.le), hθout, not_lt, le_inv_mul_iff₀ hs]
    linarith
  have hbne : ∀ s x, 0 < r s → b s x ≠ 0 → ‖x - s‖ < 9 * r s := fun s x hs hx =>
    lt_of_not_ge fun h => hx (hbzero s x hs h)
  -- If `|x - s| ≥ 10r_s`, then `θ_s` vanishes on `B(x, r_s)`.
  have hbev : ∀ s x, 0 < r s → 10 * r s ≤ ‖x - s‖ → b s =ᶠ[𝓝 x] fun _ => 0 := fun s x hs hx => by
    filter_upwards [ball_mem_nhds x hs] with y hy
    apply hbzero s y hs
    rw [mem_ball, dist_eq_norm] at hy
    have := norm_sub_le_norm_sub_add_norm_sub x y s
    rw [norm_sub_rev x y] at this
    linarith
  -- `‖Dθ_s‖ ≤ Λ/r_s`: `θ_s` is `θ` composed with a `(1/r_s)`-Lipschitz affine map.
  have hbder : ∀ s, 0 < r s → ∀ x, ‖fderiv ℝ (b s) x‖ ≤ Λ / r s := fun s hs x => by
    have hf : LipschitzWith (Real.toNNReal (r s)⁻¹) (fun y : Rn n => (r s)⁻¹ • (y - s)) := by
      apply LipschitzWith.of_dist_le_mul
      intro y z
      rw [Real.coe_toNNReal _ (inv_nonneg.mpr hs.le), dist_eq_norm, dist_eq_norm, ← smul_sub,
        sub_sub_sub_cancel_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hs.le)]
    rw [show b s = θ ∘ fun y : Rn n => (r s)⁻¹ • (y - s) from funext (hb s)]
    refine (norm_fderiv_le_of_lipschitz ℝ (hΛ.comp hf)).trans_eq ?_
    rw [NNReal.coe_mul, Real.coe_toNNReal _ (inv_nonneg.mpr hs.le), div_eq_mul_inv]
  -- The finite sets `J'(x) ⊇ J(x)` of the hypotheses, as finsets of the index type `J`.
  have hF : ∀ x, x ∉ A → ∃ F : Finset J,
      ∀ s : J, s ∈ F ↔ ∃ z : Rn n, ‖z - s‖ < 10 * r s ∧ ‖z - x‖ < r x := fun x hx => by
    refine ⟨((hwide x hx).preimage Subtype.val_injective.injOn).toFinset, fun s => ?_⟩
    rw [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_ofPred_eq]
    exact ⟨fun h => h.2, fun h => ⟨s.2, h⟩⟩
  choose F hFmem using hF
  have hG : ∀ x, x ∉ A → ∃ G : Finset J,
      (∀ s : J, s ∈ G ↔ ‖x - s‖ < 10 * r s) ∧ G.card ≤ N := fun x hx => by
    have hfin : ((↑) ⁻¹' {s : Rn n | s ∈ J ∧ ‖x - s‖ < 10 * r s} : Set J).Finite :=
      (hnear x hx).1.preimage Subtype.val_injective.injOn
    refine ⟨hfin.toFinset, fun s => ?_, ?_⟩
    · rw [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_ofPred_eq]
      exact ⟨fun h => h.2, fun h => ⟨s.2, h⟩⟩
    · rw [← Set.ncard_eq_toFinset_card _ hfin,
        Set.ncard_preimage_of_injective_subset_range Subtype.val_injective]
      · exact (hnear x hx).2
      · intro s hs
        exact ⟨⟨s, hs.1⟩, rfl⟩
  choose G hGmem hGcard using hG
  -- For `s ∉ J'(x)`, `θ_s` vanishes on `B(x, r(x))`.
  have hbF : ∀ x (hx : x ∉ A) y, ‖y - x‖ < r x → ∀ s : J, s ∉ F x hx → b s y = 0 :=
    fun x hx y hy s hs => by
      by_contra hne'
      apply hs
      rw [hFmem]
      have := hbne s y (hJpos s) hne'
      exact ⟨y, by linarith [hJpos s], hy⟩
  -- The normalising sum `Σ = Σᶠ_s θ_s` is the finite sum over `J'(x)` on `B(x, r(x))`, so it is
  -- `C¹` there. The cover gives `Σ ≥ 1`, and only `s ∈ J(x)` contribute to `DΣ(x)`.
  obtain ⟨S, hS⟩ : ∃ S : Rn n → ℝ, ∀ x, S x = ∑ᶠ s : J, b s x := ⟨_, fun _ => rfl⟩
  have hSloc : ∀ x (hx : x ∉ A) y, ‖y - x‖ < r x → S y = ∑ s ∈ F x hx, b s y :=
    fun x hx y hy => by
      rw [hS]
      apply finsum_eq_sum_of_support_subset
      intro s hs
      by_contra h'
      exact hs (hbF x hx y hy s h')
  have hSev : ∀ x (hx : x ∉ A), S =ᶠ[𝓝 x] fun y => ∑ s ∈ F x hx, b s y := fun x hx => by
    filter_upwards [ball_mem_nhds x (hrpos x hx)] with y hy
    rw [mem_ball, dist_eq_norm] at hy
    exact hSloc x hx y hy
  have hSC : ∀ x, x ∉ A → ContDiffAt ℝ 1 S x := fun x hx =>
    (ContDiff.sum (f := fun (s : J) => b s) fun s _ => hbC s).contDiffAt.congr_of_eventuallyEq
      (hSev x hx)
  have hS1 : ∀ x, x ∉ A → 1 ≤ S x := fun x hx => by
    have hx0 : ‖x - x‖ < r x := by rw [sub_self, norm_zero]; exact hrpos x hx
    rw [hSloc x hx x hx0]
    obtain ⟨s, hs, hxs⟩ := hcov x hx
    have hspos : 0 < r s := hrpos s (hJ hs)
    have hi : (⟨s, hs⟩ : J) ∈ F x hx := (hFmem x hx _).2 ⟨x, by linarith, hx0⟩
    calc (1 : ℝ) = b s x := (hbone s x hspos hxs).symm
      _ ≤ ∑ t ∈ F x hx, b t x :=
        Finset.single_le_sum (f := fun t : J => b t x) (fun t _ => hb0 t x) hi
  have hSpos : ∀ x, x ∉ A → 0 < S x := fun x hx => lt_of_lt_of_le one_pos (hS1 x hx)
  have hSder : ∀ x (hx : x ∉ A), fderiv ℝ S x = ∑ s ∈ G x hx, fderiv ℝ (b s) x := fun x hx => by
    rw [(hSev x hx).fderiv_eq,
      fderiv_fun_sum (A := fun (s : J) => b s) fun s _ => (hbC s).differentiable one_ne_zero x]
    symm
    apply Finset.sum_subset
    · intro s hs
      rw [hGmem] at hs
      exact (hFmem x hx s).2 ⟨x, hs, by rw [sub_self, norm_zero]; exact hrpos x hx⟩
    · intro s _ hs
      rw [hGmem, not_lt] at hs
      rw [(hbev s x (hJpos s) hs).fderiv_eq]
      exact fderiv_const_apply 0
  -- The partition `φ_s = θ_s/Σ` with anchors `p_s ∈ A` nearest to `s`, `C = 3`, `M = 30ΛN(N + 1)`.
  obtain ⟨φ, hφ⟩ : ∃ φ : J → Rn n → ℝ, ∀ s x, φ s x = b s x / S x := ⟨_, fun _ _ => rfl⟩
  choose a ha hda using fun s : J => hA.exists_infDist_eq_dist hne (s : Rn n)
  refine ⟨J, φ, a, 3, 30 * Λ * N * (N + 1), by norm_num, by positivity, ha, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `φ_s` is `C¹` off `A`.
    intro s x hx
    rw [show φ s = fun y => b s y / S y from funext (hφ s)]
    exact (hbC s).contDiffAt.div (hSC x hx) (hSpos x hx).ne'
  · -- `φ_s ≥ 0` off `A`.
    intro s x hx
    rw [hφ]
    exact div_nonneg (hb0 s x) (hSpos x hx).le
  · -- Near `x ∉ A`, only the `φ_s` with `s ∈ J'(x)` are nonzero.
    intro x hx
    refine ⟨F x hx, ball x (r x), ball_mem_nhds x (hrpos x hx), fun s hs y hy => ?_⟩
    rw [mem_ball, dist_eq_norm] at hy
    rw [hφ, hbF x hx y hy s hs, zero_div]
  · -- `Σᶠ_s φ_s(x) = (Σ_{s ∈ J'(x)} θ_s(x))/Σ(x) = 1`.
    intro x hx
    have hx0 : ‖x - x‖ < r x := by rw [sub_self, norm_zero]; exact hrpos x hx
    have hsupp : Function.support (fun s : J => φ s x) ⊆ ↑(F x hx) := by
      intro s hs
      by_contra h'
      exact hs (by show φ s x = 0; rw [hφ, hbF x hx x hx0 s h', zero_div])
    rw [finsum_eq_sum_of_support_subset _ hsupp]
    simp only [hφ]
    rw [← Finset.sum_div, ← hSloc x hx x hx0]
    exact div_self (hSpos x hx).ne'
  · -- `φ_s(x) ≠ 0` gives `|x - s| < 9r_s`, so `|x - p_s| ≤ |x - s| + d(s) ≤ d(x) + 2|x - s|`, and
    -- `r_s ≤ 2r(x) ≤ d(x)/10` bounds this by `3d(x)`.
    intro s x hx hφ0
    have hθ : b s x ≠ 0 := fun h0 => hφ0 (by rw [hφ, h0, zero_div])
    have hlt := hbne s x (hJpos s) hθ
    have h1 : infDist (s : Rn n) A ≤ infDist x A + dist (s : Rn n) x :=
      infDist_le_infDist_add_dist
    rw [dist_eq_norm, norm_sub_rev] at h1
    have h2 := hda s
    rw [dist_eq_norm] at h2
    have h3 := norm_sub_le_norm_sub_add_norm_sub x (s : Rn n) (a s)
    have h4 := (hcomp x s (by linarith [hJpos s])).1
    have h5 := hr20 x
    have h6 := hr0 x
    linarith
  · -- For `s ∈ J(x)`, `r_s ≥ 2r(x)/3`, so `‖Dθ_s(x)‖ ≤ T = 3Λ/(2r(x))` and `‖DΣ(x)‖ ≤ NT`.
    intro x hx hd1
    have hrx := hrpos x hx
    have hreqx := hreq x hd1
    obtain ⟨T, hT⟩ : ∃ T : ℝ, T = 3 / 2 * Λ / r x := ⟨_, rfl⟩
    have hT0 : 0 ≤ T := by rw [hT]; positivity
    have hbump : ∀ s ∈ G x hx, ‖fderiv ℝ (b s) x‖ ≤ T := by
      intro s hs
      rw [hGmem] at hs
      have hsr := hJpos s
      have hlow := (hcomp x s hs.le).2
      refine (hbder s hsr x).trans ?_
      rw [hT, div_le_div_iff₀ hsr hrx]
      have := mul_le_mul_of_nonneg_left hlow Λ.coe_nonneg
      linarith
    have hcard : ((G x hx).card : ℝ) ≤ N := by exact_mod_cast hGcard x hx
    have hsum : ‖fderiv ℝ S x‖ ≤ (N : ℝ) * T := by
      rw [hSder x hx]
      calc ‖∑ s ∈ G x hx, fderiv ℝ (b s) x‖
          ≤ ∑ s ∈ G x hx, ‖fderiv ℝ (b s) x‖ := norm_sum_le _ _
        _ ≤ ∑ _s ∈ G x hx, T := Finset.sum_le_sum hbump
        _ = ((G x hx).card : ℝ) * T := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (N : ℝ) * T := mul_le_mul_of_nonneg_right hcard hT0
    -- Off `J(x)`, `φ_s` vanishes near `x`, so `Dφ_s(x) = 0`.
    have hφev : ∀ s : J, s ∉ G x hx → fderiv ℝ (φ s) x = 0 := by
      intro s hs
      rw [hGmem, not_lt] at hs
      have hev : φ s =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [hbev s x (hJpos s) hs] with y hy
        rw [hφ, hy, zero_div]
      rw [hev.fderiv_eq]
      exact fderiv_const_apply 0
    -- Quotient rule: `‖Dφ_s(x)‖ ≤ ‖Dθ_s(x)‖ + ‖DΣ(x)‖` since `Σ(x) ≥ 1` and `0 ≤ θ_s ≤ 1`.
    have hφder : ∀ s : J, ‖fderiv ℝ (φ s) x‖ ≤ ‖fderiv ℝ (b s) x‖ + ‖fderiv ℝ S x‖ := by
      intro s
      have hS1x := hS1 x hx
      have hSx := hSpos x hx
      have hSi : (S x)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hS1x
      have hSi2 : (S x ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hS1x)
      have hbd := ((hbC s).differentiable one_ne_zero x).hasFDerivAt
      have hSd := ((hSC x hx).differentiableAt one_ne_zero).hasFDerivAt
      have hi := (hasDerivAt_inv hSx.ne').comp_hasFDerivAt x hSd
      have hprod := hbd.fun_mul hi
      have hder : fderiv ℝ (φ s) x =
          b s x • (-(S x ^ 2)⁻¹ • fderiv ℝ S x) + (S x)⁻¹ • fderiv ℝ (b s) x := by
        rw [show φ s = fun y => b s y * ((fun t : ℝ => t⁻¹) ∘ S) y from
          funext fun y => by rw [hφ, div_eq_mul_inv, Function.comp_apply]]
        exact hprod.fderiv
      rw [hder]
      have hb0x := hb0 s x
      have hb1x := hb1 s x
      calc ‖b s x • (-(S x ^ 2)⁻¹ • fderiv ℝ S x) + (S x)⁻¹ • fderiv ℝ (b s) x‖
          ≤ ‖b s x • (-(S x ^ 2)⁻¹ • fderiv ℝ S x)‖ + ‖(S x)⁻¹ • fderiv ℝ (b s) x‖ :=
            norm_add_le _ _
        _ = b s x * ((S x ^ 2)⁻¹ * ‖fderiv ℝ S x‖) + (S x)⁻¹ * ‖fderiv ℝ (b s) x‖ := by
          rw [norm_smul, norm_smul, norm_smul, Real.norm_of_nonneg hb0x, norm_neg,
            Real.norm_of_nonneg (inv_nonneg.mpr (sq_nonneg (S x))),
            Real.norm_of_nonneg (inv_nonneg.mpr hSx.le)]
        _ ≤ ‖fderiv ℝ (b s) x‖ + ‖fderiv ℝ S x‖ := by
          have h₁ := mul_le_mul_of_nonneg_right hSi (norm_nonneg (fderiv ℝ (b s) x))
          have h₂ := mul_le_mul_of_nonneg_right hSi2 (norm_nonneg (fderiv ℝ S x))
          have h₃ := mul_le_mul_of_nonneg_right hb1x
            (mul_nonneg (inv_nonneg.mpr (sq_nonneg (S x))) (norm_nonneg (fderiv ℝ S x)))
          linarith
    have hsupp : Function.support (fun s : J => ‖fderiv ℝ (φ s) x‖) ⊆ ↑(G x hx) := by
      intro s hs
      by_contra h'
      exact hs (by show ‖fderiv ℝ (φ s) x‖ = 0; rw [hφev s h', norm_zero])
    rw [finsum_eq_sum_of_support_subset _ hsupp]
    have hw : ∀ s ∈ G x hx, ‖fderiv ℝ (φ s) x‖ ≤ T + (N : ℝ) * T := fun s hs =>
      (hφder s).trans (add_le_add (hbump s hs) hsum)
    calc ∑ s ∈ G x hx, ‖fderiv ℝ (φ s) x‖
        ≤ ∑ _s ∈ G x hx, (T + (N : ℝ) * T) := Finset.sum_le_sum hw
      _ = ((G x hx).card : ℝ) * (T + (N : ℝ) * T) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) * (T + (N : ℝ) * T) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 30 * Λ * N * (N + 1) / infDist x A := by
        rw [hT, hreqx]
        field_simp
        ring
/-- **Simon Ch. 2, proof of Theorem 1.6 (pp. 42–43), Whitney gluing off `A`: local structure.**
Let `A ⊆ ℝⁿ` be closed, let the weights `φ i` (`i : ι`) be nonnegative and `C¹` off `A`, locally
finitely supported off `A`, with `∑ᶠ i, φ i = 1` off `A`, and let `g = ∑ᶠ i, φ i * P i` off `A`,
where `P i y = h (p i) + ⟪ν (p i), y - p i⟫` is affine. Then at each `x ∉ A`, `g` is `C¹` at `x`
and a finite `S` with `φ i x > 0` on `S` carries every sum: `∑_{i∈S} φ i x = 1`,
`g x = ∑_{i∈S} φ i x * P i x`, `Dg(x) = ∑_{i∈S} (φ i x • ⟪ν (p i), ·⟫ + P i x • Dφ i (x))`,
`∑_{i∈S} Dφ i (x) = 0` and `∑ᶠ i, ‖Dφ i (x)‖ = ∑_{i∈S} ‖Dφ i (x)‖`. Near `x` both finsums are
sums over the finite `s` given by local finiteness, so the product, sum and constant rules apply;
`S = {i ∈ s | φ i x ≠ 0}`, and an index with `φ i x = 0` has `Dφ i (x) = 0` because `x` is then a
local minimum of `φ i ≥ 0` on the open set `ℝⁿ \ A`. -/
theorem Submission.whitney_gluing_local_structure : ∀ (n : ℕ) (A : Set (Rn n)) (h : Rn n → ℝ) (ν : Rn n → Rn n) (ι : Type) (φ : ι → Rn n → ℝ) (p : ι → Rn n) (g : Rn n → ℝ), IsClosed A → (∀ i, ∀ x ∉ A, ContDiffAt ℝ 1 (φ i) x) → (∀ i, ∀ x ∉ A, 0 ≤ φ i x) → (∀ x ∉ A, ∃ s : Finset ι, ∃ V ∈ 𝓝 x, ∀ i ∉ s, ∀ y ∈ V, φ i y = 0) → (∀ x ∉ A, ∑ᶠ i, φ i x = 1) → (∀ x ∉ A, g x = ∑ᶠ i, φ i x * (h (p i) + inner ℝ (ν (p i)) (x - p i))) → ∀ x ∉ A, ContDiffAt ℝ 1 g x ∧ ∃ S : Finset ι, (∀ i ∈ S, 0 < φ i x) ∧ ∑ i ∈ S, φ i x = 1 ∧ g x = ∑ i ∈ S, φ i x * (h (p i) + inner ℝ (ν (p i)) (x - p i)) ∧ fderiv ℝ g x = ∑ i ∈ S, (φ i x • innerSL ℝ (ν (p i)) + (h (p i) + inner ℝ (ν (p i)) (x - p i)) • fderiv ℝ (φ i) x) ∧ ∑ i ∈ S, fderiv ℝ (φ i) x = 0 ∧ ∑ᶠ i, ‖fderiv ℝ (φ i) x‖ = ∑ i ∈ S, ‖fderiv ℝ (φ i) x‖ := by
  intro n A h ν ι φ p g hA hφC1 hφnn hlf hsum hgU x hx
  classical
  obtain ⟨s, V, hV, hVzero⟩ := hlf x hx
  -- The affine pieces `P i`: derivative `⟪ν (p i), ·⟫` everywhere, and `C¹`.
  set P : ι → Rn n → ℝ := fun i y => h (p i) + inner ℝ (ν (p i)) (y - p i)
  have hPderiv : ∀ i y, HasFDerivAt (P i) (innerSL ℝ (ν (p i))) y := by
    intro i y
    have h1 := (((innerSL ℝ (ν (p i))).hasFDerivAt (x := y - p i)).comp y
      ((hasFDerivAt_id y).sub_const (p i))).const_add (h (p i))
    simpa [P, Function.comp_def, innerSL_apply_apply] using h1
  have hPcd : ∀ i, ContDiff ℝ 1 (P i) := by
    intro i
    exact contDiff_const.add ((innerSL ℝ (ν (p i))).contDiff.comp (contDiff_id.sub contDiff_const))
  -- On `W = V ∩ Aᶜ ∈ 𝓝 x` both finsums are finite sums over `s`.
  have hU : (Aᶜ : Set (Rn n)) ∈ 𝓝 x := hA.isOpen_compl.mem_nhds hx
  have hW : V ∩ Aᶜ ∈ 𝓝 x := inter_mem hV hU
  have hrep : ∀ y ∈ V ∩ Aᶜ, g y = ∑ i ∈ s, φ i y * P i y ∧ ∑ i ∈ s, φ i y = 1 := by
    intro y hy
    have hsupp1 : Function.support (fun i => φ i y) ⊆ ↑s := by
      intro i hi
      by_contra his
      exact hi (hVzero i his y hy.1)
    have hsupp2 : Function.support (fun i => φ i y * P i y) ⊆ ↑s := by
      intro i hi
      by_contra his
      apply hi
      simp [hVzero i his y hy.1]
    constructor
    · rw [hgU y hy.2, finsum_eq_sum_of_support_subset _ hsupp2]
    · rw [← finsum_eq_sum_of_support_subset _ hsupp1]
      exact hsum y hy.2
  have hg_ev : g =ᶠ[𝓝 x] fun y => ∑ i ∈ s, φ i y * P i y := by
    filter_upwards [hW] with y hy using (hrep y hy).1
  have hsum_ev : (fun y => ∑ i ∈ s, φ i y) =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
    filter_upwards [hW] with y hy using (hrep y hy).2
  -- `g` is `C¹` at `x`; its derivative, and that of `∑ i ∈ s, φ i = 1`, as sums over `s`.
  have hGcd : ContDiffAt ℝ 1 (fun y => ∑ i ∈ s, φ i y * P i y) x :=
    ContDiffAt.sum fun i _ => (hφC1 i x hx).mul (hPcd i).contDiffAt
  have hgcd : ContDiffAt ℝ 1 g x := hGcd.congr_of_eventuallyEq hg_ev
  have hφdiff : ∀ i, DifferentiableAt ℝ (φ i) x := fun i =>
    (hφC1 i x hx).differentiableAt (by norm_num)
  have hGderiv : HasFDerivAt (fun y => ∑ i ∈ s, φ i y * P i y)
      (∑ i ∈ s, (φ i x • innerSL ℝ (ν (p i)) + P i x • fderiv ℝ (φ i) x)) x := by
    apply HasFDerivAt.fun_sum
    intro i _
    exact (hφdiff i).hasFDerivAt.mul (hPderiv i x)
  have hfd_s : fderiv ℝ g x = ∑ i ∈ s, (φ i x • innerSL ℝ (ν (p i)) + P i x • fderiv ℝ (φ i) x) := by
    rw [hg_ev.fderiv_eq, hGderiv.fderiv]
  have hD0_s : ∑ i ∈ s, fderiv ℝ (φ i) x = 0 := by
    have h1 : HasFDerivAt (fun y => ∑ i ∈ s, φ i y) (∑ i ∈ s, fderiv ℝ (φ i) x) x :=
      HasFDerivAt.fun_sum fun i _ => (hφdiff i).hasFDerivAt
    have h2 : HasFDerivAt (fun y => ∑ i ∈ s, φ i y) (0 : Rn n →L[ℝ] ℝ) x :=
      (hasFDerivAt_const (1 : ℝ) x).congr_of_eventuallyEq hsum_ev
    exact h1.unique h2
  -- Indices with zero weight at `x` have zero derivative there (local minimum of `φ i ≥ 0`).
  have hzero : ∀ i, φ i x = 0 → fderiv ℝ (φ i) x = 0 := by
    intro i hi
    apply IsLocalMin.fderiv_eq_zero
    filter_upwards [hU] with y hy
    rw [hi]
    exact hφnn i y hy
  have hxV : x ∈ V := mem_of_mem_nhds hV
  have hout : ∀ i, i ∉ s → φ i x = 0 := fun i hi => hVzero i hi x hxV
  -- `S = {i ∈ s | φ i x ≠ 0}`: dropping the other indices of `s` changes no sum.
  let S : Finset ι := s.filter (fun i => φ i x ≠ 0)
  have hSpos : ∀ i ∈ S, 0 < φ i x := by
    intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    exact lt_of_le_of_ne (hφnn i x hx) (Ne.symm hi')
  have hS1 : ∑ i ∈ S, φ i x = 1 := by
    have := (hrep x ⟨hxV, hx⟩).2
    rw [← this]
    exact Finset.sum_filter_ne_zero s
  refine ⟨hgcd, S, hSpos, hS1, ?_, ?_, ?_, ?_⟩
  · rw [(hrep x ⟨hxV, hx⟩).1]
    symm
    apply Finset.sum_filter_of_ne
    intro i _ hne h0
    exact hne (by rw [h0, zero_mul])
  · rw [hfd_s]
    symm
    apply Finset.sum_filter_of_ne
    intro i _ hne h0
    exact hne (by rw [h0, hzero i h0, zero_smul, smul_zero, add_zero])
  · rw [← hD0_s]
    apply Finset.sum_filter_of_ne
    intro i _ hne h0
    exact hne (hzero i h0)
  · apply finsum_eq_sum_of_support_subset
    intro i hi
    have hne : fderiv ℝ (φ i) x ≠ 0 := by
      intro h0
      exact hi (by simp [h0])
    have hφne : φ i x ≠ 0 := fun h0 => hne (hzero i h0)
    have his : i ∈ s := by
      by_contra his
      exact hφne (hout i his)
    exact Finset.mem_filter.mpr ⟨his, hφne⟩

/-- Whitney gluing on `A` (the step `∇g = ν` on `A` in the proof of Simon Ch. 2, Theorem 1.6).
Let `A` be closed, `ν` continuous on `A`, and `h`, `ν` satisfy 1.6 (∗) uniformly on compact
subsets of `A`. If `g = h` on `A` and, at each `x ∉ A`, `g(x)` is a convex combination
`∑ᵢ φᵢ(x) (h(pᵢ) + ν(pᵢ)·(x - pᵢ))` over finitely many anchors `pᵢ ∈ A` with
`|x - pᵢ| ≤ C dist(x, A)`, then `g` is differentiable at every `a ∈ A` with `Dg(a) = ν(a)·`. -/
theorem Submission.whitney_gluing_hasFDerivAt : (∀ (n : ℕ) (A : Set (Rn n)) (h : Rn n → ℝ) (ν : Rn n → Rn n) (ι : Type) (φ : ι → Rn n → ℝ) (p : ι → Rn n) (C : ℝ) (g : Rn n → ℝ), IsClosed A → ContinuousOn ν A → (∀ K ⊆ A, IsCompact K → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ y ∈ A, 0 < ‖y - x‖ → ‖y - x‖ < δ → |h y - h x - inner ℝ (ν x) (y - x)| ≤ ε * ‖y - x‖) → 0 ≤ C → (∀ i, p i ∈ A) → (∀ x ∈ A, g x = h x) → (∀ x ∉ A, ∃ S : Finset ι, (∀ i ∈ S, 0 ≤ φ i x ∧ ‖x - p i‖ ≤ C * Metric.infDist x A) ∧ ∑ i ∈ S, φ i x = 1 ∧ g x = ∑ i ∈ S, φ i x * (h (p i) + inner ℝ (ν (p i)) (x - p i))) → ∀ a ∈ A, HasFDerivAt g (innerSL ℝ (ν a)) a) := by
  intro n A h ν ι φ p C g hA hν hW hC hp hgA hrep a ha
  apply HasFDerivAt.of_isLittleO
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  have hC1 : 0 < 2 * C + 1 := by linarith
  set ε := c / (2 * C + 1) with hε_def
  have hε : 0 < ε := div_pos hc hC1
  have hεc : (2 * C + 1) * ε = c := by rw [hε_def]; field_simp
  set K : Set (Rn n) := A ∩ closedBall a 1 with hK_def
  have hK : IsCompact K := (isCompact_closedBall a 1).inter_left hA
  obtain ⟨δ₁, hδ₁, hWK⟩ := hW K inter_subset_left hK ε hε
  obtain ⟨τ, hτ, hντ⟩ := Metric.continuousWithinAt_iff.mp (hν a ha) ε hε
  set r := min 1 (min δ₁ τ) with hr_def
  have hr : 0 < r := lt_min one_pos (lt_min hδ₁ hτ)
  have hrδ : r ≤ δ₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hrτ : r ≤ τ := (min_le_right _ _).trans (min_le_right _ _)
  set ρ := r / (C + 2) with hρ_def
  have hC2 : 0 < C + 2 := by linarith
  have hρ : 0 < ρ := div_pos hr hC2
  have hρr : (C + 1) * ρ < r := by
    rw [hρ_def, mul_div_assoc', div_lt_iff₀ hC2]
    nlinarith
  have hρr' : ρ < r := by
    have : ρ ≤ (C + 1) * ρ := by nlinarith
    linarith
  have haK : a ∈ K := ⟨ha, mem_closedBall_self zero_le_one⟩
  have hWa : ∀ b ∈ A, ‖b - a‖ < δ₁ → |h b - h a - inner ℝ (ν a) (b - a)| ≤ ε * ‖b - a‖ := by
    intro b hb hba
    rcases eq_or_ne b a with rfl | hne
    · simp
    · exact hWK a haK b hb (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) hba
  filter_upwards [Metric.ball_mem_nhds a hρ] with x hx
  have hxa : ‖x - a‖ < ρ := by simpa [dist_eq_norm] using hx
  rw [innerSL_apply_apply, hgA a ha, Real.norm_eq_abs, ← hεc]
  by_cases hxA : x ∈ A
  · rw [hgA x hxA]
    have h1 := hWa x hxA (by linarith)
    have h2 : ε * ‖x - a‖ ≤ (2 * C + 1) * ε * ‖x - a‖ := by
      have : ε ≤ (2 * C + 1) * ε := by nlinarith
      exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
    exact h1.trans h2
  · obtain ⟨S, hS, hS1, hval⟩ := hrep x hxA
    have hid : g x - h a - inner ℝ (ν a) (x - a) = ∑ i ∈ S, φ i x *
        ((h (p i) + inner ℝ (ν (p i)) (x - p i)) - (h a + inner ℝ (ν a) (x - a))) := by
      rw [hval]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hS1, one_mul]
      ring
    rw [hid]
    have hdx : infDist x A ≤ ‖x - a‖ := by rw [← dist_eq_norm]; exact infDist_le_dist_of_mem ha
    have hterm : ∀ i ∈ S, |(h (p i) + inner ℝ (ν (p i)) (x - p i)) - (h a + inner ℝ (ν a) (x - a))|
        ≤ (2 * C + 1) * ε * ‖x - a‖ := by
      intro i hi
      have hxp : ‖x - p i‖ ≤ C * ‖x - a‖ := (hS i hi).2.trans (mul_le_mul_of_nonneg_left hdx hC)
      have hpa : ‖p i - a‖ ≤ (C + 1) * ‖x - a‖ := by
        calc ‖p i - a‖ = ‖(x - a) - (x - p i)‖ := by congr 1; abel
          _ ≤ ‖x - a‖ + ‖x - p i‖ := norm_sub_le _ _
          _ ≤ ‖x - a‖ + C * ‖x - a‖ := by linarith
          _ = (C + 1) * ‖x - a‖ := by ring
      have hpa_lt : ‖p i - a‖ < r := by
        have : (C + 1) * ‖x - a‖ ≤ (C + 1) * ρ := mul_le_mul_of_nonneg_left hxa.le (by linarith)
        linarith
      have hνi : ‖ν (p i) - ν a‖ ≤ ε := by
        have := hντ (hp i) (by rw [dist_eq_norm]; linarith)
        rw [dist_eq_norm] at this
        exact this.le
      have hWi := hWa (p i) (hp i) (by linarith)
      have hE1 : (h (p i) + inner ℝ (ν (p i)) (x - p i)) - (h a + inner ℝ (ν a) (x - a)) =
          (h (p i) - h a - inner ℝ (ν a) (p i - a)) + inner ℝ (ν (p i) - ν a) (x - p i) := by
        have hsplit : x - a = (x - p i) + (p i - a) := by abel
        rw [inner_sub_left, hsplit, inner_add_right]
        ring
      rw [hE1]
      calc |(h (p i) - h a - inner ℝ (ν a) (p i - a)) + inner ℝ (ν (p i) - ν a) (x - p i)|
          ≤ |h (p i) - h a - inner ℝ (ν a) (p i - a)| + |inner ℝ (ν (p i) - ν a) (x - p i)| :=
            abs_add_le _ _
        _ ≤ ε * ‖p i - a‖ + ‖ν (p i) - ν a‖ * ‖x - p i‖ :=
            add_le_add hWi (abs_real_inner_le_norm _ _)
        _ ≤ ε * ((C + 1) * ‖x - a‖) + ε * (C * ‖x - a‖) := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left hpa hε.le
            · exact mul_le_mul hνi hxp (norm_nonneg _) hε.le
        _ = (2 * C + 1) * ε * ‖x - a‖ := by ring
    calc |∑ i ∈ S, φ i x * ((h (p i) + inner ℝ (ν (p i)) (x - p i)) - (h a + inner ℝ (ν a) (x - a)))|
        ≤ ∑ i ∈ S, |φ i x * ((h (p i) + inner ℝ (ν (p i)) (x - p i)) - (h a + inner ℝ (ν a) (x - a)))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ S, φ i x * |(h (p i) + inner ℝ (ν (p i)) (x - p i)) - (h a + inner ℝ (ν a) (x - a))| := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [abs_mul, abs_of_nonneg (hS i hi).1]
      _ ≤ ∑ i ∈ S, φ i x * ((2 * C + 1) * ε * ‖x - a‖) := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_left (hterm i hi) (hS i hi).1
      _ = (2 * C + 1) * ε * ‖x - a‖ := by rw [← Finset.sum_mul, hS1, one_mul]

/-- **Simon Ch. 2, Theorem 1.6 (pp. 42–43), Whitney extension: continuity of `Dg` on `A`.** Let
`A ⊂ ℝⁿ` be closed, `ν` continuous on `A`, `(h, ν)` satisfy the uniform first-order condition of
1.6 on compact subsets of `A`, `C, M ≥ 0`, and the anchors `pᵢ` lie in `A`. Suppose
`Dg(x) = ⟨ν(x), ·⟩` for `x ∈ A`, and for `x ∉ A`, with `d = dist(·, A)`, there is a finite `S` with
`Dg(x) = ∑_{i ∈ S} (φᵢ(x) ⟨ν(pᵢ), ·⟩ + Pᵢ(x) Dφᵢ(x))`, `Pᵢ(x) = h(pᵢ) + ⟨ν(pᵢ), x - pᵢ⟩`,
where `φᵢ(x) ≥ 0`, `|x - pᵢ| ≤ C d(x)`, `∑ φᵢ(x) = 1`, `∑ Dφᵢ(x) = 0`, and
`∑ ‖Dφᵢ(x)‖ ≤ M / d(x)` if `d(x) ≤ 1`. Then `Dg` is continuous at every `a ∈ A`. For `x ∉ A`
near `a`, `Dg(x) - ⟨ν(a), ·⟩ = ∑ φᵢ(x) ⟨ν(pᵢ) - ν(a), ·⟩ + ∑ (Pᵢ(x) - c) Dφᵢ(x)`, where `c` is
the jet of a nearest point `a* ∈ A` evaluated at `x`; `|Pᵢ(x) - c| ≤ ε(3C + 1) d(x)` then gives
`‖Dg(x) - Dg(a)‖ ≤ ε(1 + (3C + 1)M)`. -/
theorem Submission.whitney_gluing_continuousAt_fderiv : ∀ (n : ℕ) (A : Set (Rn n)) (h : Rn n → ℝ) (ν : Rn n → Rn n) (ι : Type) (φ : ι → Rn n → ℝ) (p : ι → Rn n) (C M : ℝ) (g : Rn n → ℝ), IsClosed A → ContinuousOn ν A → (∀ K ⊆ A, IsCompact K → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ y ∈ A, 0 < ‖y - x‖ → ‖y - x‖ < δ → |h y - h x - inner ℝ (ν x) (y - x)| ≤ ε * ‖y - x‖) → 0 ≤ C → 0 ≤ M → (∀ i, p i ∈ A) → (∀ x ∈ A, fderiv ℝ g x = innerSL ℝ (ν x)) → (∀ x ∉ A, ∃ S : Finset ι, (∀ i ∈ S, 0 ≤ φ i x ∧ ‖x - p i‖ ≤ C * Metric.infDist x A) ∧ ∑ i ∈ S, φ i x = 1 ∧ ∑ i ∈ S, fderiv ℝ (φ i) x = 0 ∧ (Metric.infDist x A ≤ 1 → ∑ i ∈ S, ‖fderiv ℝ (φ i) x‖ ≤ M / Metric.infDist x A) ∧ fderiv ℝ g x = ∑ i ∈ S, (φ i x • innerSL ℝ (ν (p i)) + (h (p i) + inner ℝ (ν (p i)) (x - p i)) • fderiv ℝ (φ i) x)) → ∀ a ∈ A, ContinuousAt (fderiv ℝ g) a := by
  intro n A h ν ι φ p C M g hA hν hW hC hM hp hFD hrep a ha
  rw [Metric.continuousAt_iff]
  intro η hη
  -- Step 1: `ε = η / (2B)` with `B = 1 + (3C + 1)M ≥ 1`, so `εB < η` and `ε < η`.
  have hB : 0 < 1 + (3 * C + 1) * M := by nlinarith
  set ε := η / (2 * (1 + (3 * C + 1) * M)) with hε_def
  have hε : 0 < ε := div_pos hη (by linarith)
  have hεB : ε * (1 + (3 * C + 1) * M) < η := by
    rw [hε_def, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  have hεη : ε < η := by
    have h0 : 0 ≤ (3 * C + 1) * M := mul_nonneg (by linarith) hM
    have : ε ≤ ε * (1 + (3 * C + 1) * M) := by nlinarith [mul_nonneg hε.le h0]
    linarith
  -- Step 2: the uniform condition on the compact `K = A ∩ B̄(a, 1)` gives `δ₁`.
  set K : Set (Rn n) := A ∩ closedBall a 1 with hK_def
  have hK : IsCompact K := (isCompact_closedBall a 1).inter_left hA
  obtain ⟨δ₁, hδ₁, hWK⟩ := hW K inter_subset_left hK ε hε
  -- Step 3: continuity of `ν` on `A` at `a` gives `τ`.
  obtain ⟨τ, hτ, hντ⟩ := Metric.continuousWithinAt_iff.mp (hν a ha) ε hε
  -- Step 4: `r = min {1, δ₁, τ}` and `ρ = r / (C + 2)`.
  set r := min 1 (min δ₁ τ) with hr_def
  have hr : 0 < r := lt_min one_pos (lt_min hδ₁ hτ)
  have hr1 : r ≤ 1 := min_le_left _ _
  have hrδ : r ≤ δ₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hrτ : r ≤ τ := (min_le_right _ _).trans (min_le_right _ _)
  have hC2 : 0 < C + 2 := by linarith
  set ρ := r / (C + 2) with hρ_def
  have hρ : 0 < ρ := div_pos hr hC2
  have hρr : (C + 1) * ρ < r := by
    rw [hρ_def, mul_div_assoc', div_lt_iff₀ hC2]
    nlinarith
  have hρr2 : 2 * ρ ≤ r := by
    rw [hρ_def, mul_div_assoc', div_le_iff₀ hC2]
    nlinarith
  have hρr' : ρ < r := by
    have : ρ ≤ (C + 1) * ρ := by nlinarith
    linarith
  -- (2a): the uniform estimate with base point in `K`, including the trivial case `y = b`.
  have hWK' : ∀ b ∈ K, ∀ y ∈ A, ‖y - b‖ < δ₁ →
      |h y - h b - inner ℝ (ν b) (y - b)| ≤ ε * ‖y - b‖ := by
    intro b hb y hy hyb
    rcases eq_or_ne y b with rfl | hne
    · simp
    · exact hWK b hb y hy (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) hyb
  -- (3a): `‖ν(b) - ν(a)‖ < ε` for `b ∈ A` with `‖b - a‖ < r`.
  have hνa : ∀ b ∈ A, ‖b - a‖ < r → ‖ν b - ν a‖ < ε := by
    intro b hb hba
    have := hντ hb (by rw [dist_eq_norm]; linarith)
    rwa [dist_eq_norm] at this
  -- Step 5: let `‖x - a‖ < ρ`.
  refine ⟨ρ, hρ, fun x hx => ?_⟩
  have hxa : ‖x - a‖ < ρ := by rwa [dist_eq_norm] at hx
  rw [dist_eq_norm, hFD a ha]
  by_cases hxA : x ∈ A
  · -- Case `x ∈ A`: `‖Dg(x) - Dg(a)‖ = ‖ν(x) - ν(a)‖ < ε < η`.
    rw [hFD x hxA, ← map_sub, innerSL_apply_norm]
    exact (hνa x hxA (by linarith)).trans hεη
  · -- Case `x ∉ A`.
    obtain ⟨S, hS, hS1, hD0, hDbound, hfd⟩ := hrep x hxA
    -- (a): `0 < d(x) ≤ ‖x - a‖ < 1`.
    have hne : A.Nonempty := ⟨a, ha⟩
    have hdpos : 0 < infDist x A := (hA.notMem_iff_infDist_pos hne).mp hxA
    have hdx : infDist x A ≤ ‖x - a‖ := by rw [← dist_eq_norm]; exact infDist_le_dist_of_mem ha
    have hd1 : infDist x A ≤ 1 := by linarith
    -- (b): a nearest point `a' ∈ A` of `x` lies in `K` and `‖ν(a') - ν(a)‖ < ε`.
    obtain ⟨a', ha', hda'⟩ := hA.exists_infDist_eq_dist hne x
    have hxa' : ‖x - a'‖ = infDist x A := by rw [hda', dist_eq_norm]
    have ha'a : ‖a' - a‖ < r := by
      have : ‖a' - a‖ ≤ ‖x - a'‖ + ‖x - a‖ := by
        calc ‖a' - a‖ = ‖(x - a) - (x - a')‖ := by congr 1; abel
          _ ≤ ‖x - a‖ + ‖x - a'‖ := norm_sub_le _ _
          _ = ‖x - a'‖ + ‖x - a‖ := add_comm _ _
      linarith
    have ha'K : a' ∈ K := ⟨ha', by rw [mem_closedBall, dist_eq_norm]; linarith⟩
    have hνa' : ‖ν a' - ν a‖ < ε := hνa a' ha' ha'a
    set d := infDist x A with hd_def
    set c := h a' + inner ℝ (ν a') (x - a') with hc_def
    -- (c): `‖ν(pᵢ) - ν(a)‖ ≤ ε` for `i ∈ S`.
    have hνi : ∀ i ∈ S, ‖ν (p i) - ν a‖ ≤ ε := by
      intro i hi
      have hxp : ‖x - p i‖ ≤ C * ‖x - a‖ := (hS i hi).2.trans (mul_le_mul_of_nonneg_left hdx hC)
      have hpa : ‖p i - a‖ ≤ (C + 1) * ‖x - a‖ := by
        calc ‖p i - a‖ = ‖(x - a) - (x - p i)‖ := by congr 1; abel
          _ ≤ ‖x - a‖ + ‖x - p i‖ := norm_sub_le _ _
          _ ≤ ‖x - a‖ + C * ‖x - a‖ := by linarith
          _ = (C + 1) * ‖x - a‖ := by ring
      have : (C + 1) * ‖x - a‖ ≤ (C + 1) * ρ := mul_le_mul_of_nonneg_left hxa.le (by linarith)
      exact (hνa (p i) (hp i) (by linarith)).le
    -- (d), (e): `|Pᵢ(x) - c| ≤ ε(3C + 1)d` for `i ∈ S`, via (E1).
    have hPi : ∀ i ∈ S, |(h (p i) + inner ℝ (ν (p i)) (x - p i)) - c| ≤ ε * (3 * C + 1) * d := by
      intro i hi
      have hxp : ‖x - p i‖ ≤ C * d := (hS i hi).2
      have hpa' : ‖p i - a'‖ ≤ (C + 1) * d := by
        calc ‖p i - a'‖ = ‖(x - a') - (x - p i)‖ := by congr 1; abel
          _ ≤ ‖x - a'‖ + ‖x - p i‖ := norm_sub_le _ _
          _ ≤ d + C * d := by rw [hxa']; linarith
          _ = (C + 1) * d := by ring
      have hpa'δ : ‖p i - a'‖ < δ₁ := by
        have : (C + 1) * d ≤ (C + 1) * ρ := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        linarith
      have hWi := hWK' a' ha'K (p i) (hp i) hpa'δ
      have hνpa' : ‖ν (p i) - ν a'‖ ≤ 2 * ε := by
        calc ‖ν (p i) - ν a'‖ = ‖(ν (p i) - ν a) - (ν a' - ν a)‖ := by congr 1; abel
          _ ≤ ‖ν (p i) - ν a‖ + ‖ν a' - ν a‖ := norm_sub_le _ _
          _ ≤ ε + ε := add_le_add (hνi i hi) hνa'.le
          _ = 2 * ε := by ring
      have hE1 : (h (p i) + inner ℝ (ν (p i)) (x - p i)) - c =
          (h (p i) - h a' - inner ℝ (ν a') (p i - a')) + inner ℝ (ν (p i) - ν a') (x - p i) := by
        have hsplit : x - a' = (x - p i) + (p i - a') := by abel
        rw [hc_def, inner_sub_left, hsplit, inner_add_right]
        ring
      rw [hE1]
      calc |(h (p i) - h a' - inner ℝ (ν a') (p i - a')) + inner ℝ (ν (p i) - ν a') (x - p i)|
          ≤ |h (p i) - h a' - inner ℝ (ν a') (p i - a')| + |inner ℝ (ν (p i) - ν a') (x - p i)| :=
            abs_add_le _ _
        _ ≤ ε * ‖p i - a'‖ + ‖ν (p i) - ν a'‖ * ‖x - p i‖ :=
            add_le_add hWi (abs_real_inner_le_norm _ _)
        _ ≤ ε * ((C + 1) * d) + (2 * ε) * (C * d) := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left hpa' hε.le
            · exact mul_le_mul hνpa' hxp (norm_nonneg _) (by linarith)
        _ = ε * (3 * C + 1) * d := by ring
    -- (f): `Dg(x) - ⟨ν(a), ·⟩ = ∑ φᵢ(x) (L_{ν(pᵢ)} - L_{ν(a)}) + ∑ (Pᵢ(x) - c) Dφᵢ(x)`.
    have hrepr : fderiv ℝ g x - innerSL ℝ (ν a) =
        ∑ i ∈ S, φ i x • (innerSL ℝ (ν (p i)) - innerSL ℝ (ν a)) +
          ∑ i ∈ S, ((h (p i) + inner ℝ (ν (p i)) (x - p i)) - c) • fderiv ℝ (φ i) x := by
      rw [hfd]
      simp_rw [smul_sub, sub_smul]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        ← Finset.sum_smul, ← Finset.smul_sum, hS1, hD0, one_smul, smul_zero, sub_zero]
      abel
    rw [hrepr]
    -- (g): the first sum has norm `≤ ε`, the second `≤ ε(3C + 1)M`.
    have hfirst : ‖∑ i ∈ S, φ i x • (innerSL ℝ (ν (p i)) - innerSL ℝ (ν a))‖ ≤ ε := by
      calc ‖∑ i ∈ S, φ i x • (innerSL ℝ (ν (p i)) - innerSL ℝ (ν a))‖
          ≤ ∑ i ∈ S, ‖φ i x • (innerSL ℝ (ν (p i)) - innerSL ℝ (ν a))‖ := norm_sum_le _ _
        _ = ∑ i ∈ S, φ i x * ‖ν (p i) - ν a‖ := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [norm_smul, Real.norm_of_nonneg (hS i hi).1, ← map_sub, innerSL_apply_norm]
        _ ≤ ∑ i ∈ S, φ i x * ε := by
            apply Finset.sum_le_sum
            intro i hi
            exact mul_le_mul_of_nonneg_left (hνi i hi) (hS i hi).1
        _ = ε := by rw [← Finset.sum_mul, hS1, one_mul]
    have hsecond : ‖∑ i ∈ S, ((h (p i) + inner ℝ (ν (p i)) (x - p i)) - c) • fderiv ℝ (φ i) x‖ ≤
        ε * (3 * C + 1) * M := by
      calc ‖∑ i ∈ S, ((h (p i) + inner ℝ (ν (p i)) (x - p i)) - c) • fderiv ℝ (φ i) x‖
          ≤ ∑ i ∈ S, ‖((h (p i) + inner ℝ (ν (p i)) (x - p i)) - c) • fderiv ℝ (φ i) x‖ :=
            norm_sum_le _ _
        _ = ∑ i ∈ S, |(h (p i) + inner ℝ (ν (p i)) (x - p i)) - c| * ‖fderiv ℝ (φ i) x‖ := by
            apply Finset.sum_congr rfl
            intro i _
            rw [norm_smul, Real.norm_eq_abs]
        _ ≤ ∑ i ∈ S, (ε * (3 * C + 1) * d) * ‖fderiv ℝ (φ i) x‖ := by
            apply Finset.sum_le_sum
            intro i hi
            exact mul_le_mul_of_nonneg_right (hPi i hi) (norm_nonneg _)
        _ = (ε * (3 * C + 1) * d) * ∑ i ∈ S, ‖fderiv ℝ (φ i) x‖ := by rw [Finset.mul_sum]
        _ ≤ (ε * (3 * C + 1) * d) * (M / d) := by
            apply mul_le_mul_of_nonneg_left (hDbound hd1)
            have : 0 ≤ 3 * C + 1 := by linarith
            positivity
        _ = ε * (3 * C + 1) * M := by field_simp
    calc ‖∑ i ∈ S, φ i x • (innerSL ℝ (ν (p i)) - innerSL ℝ (ν a)) +
          ∑ i ∈ S, ((h (p i) + inner ℝ (ν (p i)) (x - p i)) - c) • fderiv ℝ (φ i) x‖
        ≤ ‖∑ i ∈ S, φ i x • (innerSL ℝ (ν (p i)) - innerSL ℝ (ν a))‖ +
          ‖∑ i ∈ S, ((h (p i) + inner ℝ (ν (p i)) (x - p i)) - c) • fderiv ℝ (φ i) x‖ :=
          norm_add_le _ _
      _ ≤ ε + ε * (3 * C + 1) * M := add_le_add hfirst hsecond
      _ = ε * (1 + (3 * C + 1) * M) := by ring
      _ < η := hεB

/-- Simon Ch. 2, Theorem 1.6, gluing step: let `A ⊆ ℝⁿ` be closed, `(h, ν)` a Whitney jet on `A`
(`ν` continuous on `A`, `R(x,y) → 0` uniformly on compact subsets of `A`), and `(φᵢ, pᵢ)` a locally
finite partition of unity on `ℝⁿ \ A` with anchors `pᵢ ∈ A`, `|x - pᵢ| ≤ C d(x)` where `φᵢ(x) ≠ 0`,
and `∑ᶠ ‖Dφᵢ(x)‖ ≤ M / d(x)` where `d(x) = dist(x, A) ≤ 1`. Then the function `g = h` on `A`,
`g = ∑ᶠ φᵢ (h(pᵢ) + ⟨ν(pᵢ), · - pᵢ⟩)` off `A` is `C¹` with `Dg(x)v = ⟨ν(x), v⟩` for `x ∈ A`. -/
theorem Submission.whitney_jet_gluing_c1 : (∀ (n : ℕ) (A : Set (Rn n)) (h : Rn n → ℝ) (ν : Rn n → Rn n) (ι : Type) (φ : ι → Rn n → ℝ) (p : ι → Rn n) (C M : ℝ) (g : Rn n → ℝ), IsClosed A → ContinuousOn ν A → (∀ K ⊆ A, IsCompact K → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ y ∈ A, 0 < ‖y - x‖ → ‖y - x‖ < δ → |h y - h x - inner ℝ (ν x) (y - x)| ≤ ε * ‖y - x‖) → 0 ≤ C → 0 ≤ M → (∀ i, p i ∈ A) → (∀ i, ∀ x ∉ A, ContDiffAt ℝ 1 (φ i) x) → (∀ i, ∀ x ∉ A, 0 ≤ φ i x) → (∀ x ∉ A, ∃ s : Finset ι, ∃ V ∈ 𝓝 x, ∀ i ∉ s, ∀ y ∈ V, φ i y = 0) → (∀ x ∉ A, ∑ᶠ i, φ i x = 1) → (∀ i, ∀ x ∉ A, φ i x ≠ 0 → ‖x - p i‖ ≤ C * Metric.infDist x A) → (∀ x ∉ A, Metric.infDist x A ≤ 1 → ∑ᶠ i, ‖fderiv ℝ (φ i) x‖ ≤ M / Metric.infDist x A) → (∀ x ∈ A, g x = h x) → (∀ x ∉ A, g x = ∑ᶠ i, φ i x * (h (p i) + inner ℝ (ν (p i)) (x - p i))) → ContDiff ℝ 1 g ∧ ∀ x ∈ A, ∀ v, fderiv ℝ g x v = inner ℝ (ν x) v) := by
  intro n A h ν ι φ p C M g hA hν hW hC hM hp hφC1 hφnn hlf hsum hanchor hder hgA hgU
  -- Step 1: off `A`, `g` is `C¹` and is a finite convex combination of the affine jets.
  have hloc := Submission.whitney_gluing_local_structure n A h ν ι φ p g hA hφC1 hφnn hlf hsum hgU
  -- Step 3: `Dg(a) = ⟨ν(a), ·⟩` for `a ∈ A`.
  have hdiffA : ∀ a ∈ A, HasFDerivAt g (innerSL ℝ (ν a)) a := by
    refine Submission.whitney_gluing_hasFDerivAt n A h ν ι φ p C g hA hν hW hC hp hgA ?_
    intro x hx
    obtain ⟨-, S, hpos, hS1, hgx, -, -, -⟩ := hloc x hx
    exact ⟨S, fun i hi => ⟨(hpos i hi).le, hanchor i x hx (hpos i hi).ne'⟩, hS1, hgx⟩
  have hfderivA : ∀ x ∈ A, fderiv ℝ g x = innerSL ℝ (ν x) := fun x hx => (hdiffA x hx).fderiv
  -- Step 4: `Dg` is continuous at every `a ∈ A`.
  have hcontA : ∀ a ∈ A, ContinuousAt (fderiv ℝ g) a := by
    refine Submission.whitney_gluing_continuousAt_fderiv n A h ν ι φ p C M g hA hν hW hC hM hp
      hfderivA ?_
    intro x hx
    obtain ⟨-, S, hpos, hS1, -, hDg, hD0, hnorm⟩ := hloc x hx
    exact ⟨S, fun i hi => ⟨(hpos i hi).le, hanchor i x hx (hpos i hi).ne'⟩, hS1, hD0,
      fun hd => hnorm.symm.le.trans (hder x hx hd), hDg⟩
  -- Step 5: `g` is differentiable with continuous derivative at points of `A` and off `A`.
  refine ⟨contDiff_one_iff_fderiv.mpr ⟨fun x => ?_, continuous_iff_continuousAt.mpr fun x => ?_⟩,
    fun x hx v => by rw [hfderivA x hx, innerSL_apply_apply]⟩
  · by_cases hx : x ∈ A
    · exact (hdiffA x hx).differentiableAt
    · exact (hloc x hx).1.differentiableAt (by norm_num)
  · by_cases hx : x ∈ A
    · exact hcontA x hx
    · exact (hloc x hx).1.continuousAt_fderiv (by norm_num)

/-- **Simon Ch. 2, proof of Theorem 1.6 (pp. 42–43), Whitney partition of unity.** For closed
nonempty `A ⊆ ℝⁿ` and `d = dist(·, A)` there are weights `φ_i`, `C¹`, `≥ 0`, locally finite and
summing to `1` on `ℝⁿ ∖ A`, and anchors `p_i ∈ A` with `|x - p_i| ≤ C d(x)` whenever `φ_i(x) ≠ 0`
and `∑ᶠ i, ‖Dφ_i(x)‖ ≤ M / d(x)` when `d(x) ≤ 1`. With `r = min{1, d}/20`, the Vitali lemma gives
centres `J ⊆ ℝⁿ ∖ A` such that every `x ∉ A` has some `s ∈ J` with `|x - s| ≤ 5 r(s)`, at most
`N` centres with `|x - s| < 10 r(s)`, and only finitely many `s` whose open ball of radius
`10 r(s)` meets the open ball of radius `r(x)` about `x`. The rescaled bumps over this cover,
normalised by their sum and anchored at nearest points of `A`, are the required weights. -/
theorem Submission.whitney_smooth_partition_of_unity : ∀ (n : ℕ) (A : Set (Rn n)), IsClosed A → A.Nonempty → ∃ (ι : Type) (φ : ι → Rn n → ℝ) (p : ι → Rn n) (C M : ℝ), 0 ≤ C ∧ 0 ≤ M ∧ (∀ i, p i ∈ A) ∧ (∀ i, ∀ x ∉ A, ContDiffAt ℝ 1 (φ i) x) ∧ (∀ i, ∀ x ∉ A, 0 ≤ φ i x) ∧ (∀ x ∉ A, ∃ s : Finset ι, ∃ V ∈ 𝓝 x, ∀ i ∉ s, ∀ y ∈ V, φ i y = 0) ∧ (∀ x ∉ A, ∑ᶠ i, φ i x = 1) ∧ (∀ i, ∀ x ∉ A, φ i x ≠ 0 → ‖x - p i‖ ≤ C * Metric.infDist x A) ∧ (∀ x ∉ A, Metric.infDist x A ≤ 1 → ∑ᶠ i, ‖fderiv ℝ (φ i) x‖ ≤ M / Metric.infDist x A) := by
  intro n A hA hne
  -- Steps 1–5 (Vitali cover of `ℝⁿ ∖ A`): covering, bounded overlap `N`, local finiteness.
  obtain ⟨J, N, hJ, hcov, hover, hloc⟩ := Submission.whitney_cover_finite_overlap n A hA hne
  -- Steps 6–9: nearest-point anchors and the normalised rescaled bumps over that cover.
  exact Submission.whitney_partition_of_finite_overlap_cover n A J N hA hne hJ hcov hover hloc

/-- **Simon Ch. 2, Theorem 1.6 (pp. 42–43), Whitney extension** (DAG node
`root.whitney_extension-a1`). If `A = ∅` take `g = 0`. Otherwise take a Whitney partition of
unity `φᵢ` of `ℝⁿ \ A` with anchors `pᵢ ∈ A` (`Submission.whitney_smooth_partition_of_unity`),
put `g = h` on `A` and `g = ∑ᶠ i, φᵢ · (h(pᵢ) + ⟨ν(pᵢ), · - pᵢ⟩)` off `A`, and conclude by the
`C¹` gluing lemma `Submission.whitney_jet_gluing_c1`. -/
theorem Submission.whitney_extension_theorem : WhitneyExtension := by
  intro n A h ν hA _ hν hW
  rcases A.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ ↦ 0, contDiff_const, fun x hx ↦ absurd hx (notMem_empty x)⟩
  obtain ⟨ι, φ, p, C, M, hC, hM, hp, hφ, hφ0, hloc, hsum, hanchor, hdφ⟩ :=
    Submission.whitney_smooth_partition_of_unity n A hA hne
  classical
  let g : Rn n → ℝ := fun x ↦
    if x ∈ A then h x else ∑ᶠ i, φ i x * (h (p i) + inner ℝ (ν (p i)) (x - p i))
  have hgA : ∀ x ∈ A, g x = h x := fun x hx ↦ ite_eq_left hx
  obtain ⟨hg, hDg⟩ := Submission.whitney_jet_gluing_c1 n A h ν ι φ p C M g hA hν hW hC hM hp hφ
    hφ0 hloc hsum hanchor hdφ hgA fun x hx ↦ ite_eq_right hx
  exact ⟨g, hg, fun x hx ↦ ⟨hgA x hx, hDg x hx⟩⟩

/-- **Simon Ch. 2, Theorem 1.5 (p. 42), `C¹` approximation**, by the printed proof (p. 44).
`f` is differentiable on a co-null Borel set `B` (Rademacher 1.4) with Borel gradient `ν`. Lusin
gives a closed `C ⊆ B` with `ν|C` continuous and `Lⁿ(B ∖ C) < ε/2`. The remainder moduli `η_k`
of `f` on `C` tend to `0` on `C`, and Egorov gives a closed `A ⊆ C` with `Lⁿ(C ∖ A) < ε/2` on
whose compact subsets `η_k → 0` uniformly. That is the hypothesis of Whitney 1.6 for `(A, f, ν)`,
and the resulting `C¹` function `g` satisfies `g = f` and `Dg = Df` on `A`, where
`Lⁿ(ℝⁿ ∖ A) < ε`. -/
theorem Submission.c1_approximation_theorem : C1Approximation := by
  intro n f hf ε hε
  obtain ⟨K, hK⟩ := hf
  -- Steps 1–2: `B = {x | DifferentiableAt ℝ f x}` is Borel and co-null, `ν = ∇f` is Borel.
  have hB : MeasurableSet {x : Rn n | DifferentiableAt ℝ f x} :=
    measurableSet_of_differentiableAt ℝ f
  have hB_null : volume {x : Rn n | ¬ DifferentiableAt ℝ f x} = 0 :=
    ae_iff.1 (Submission.lipschitz_extension_and_rademacher.2 n f ⟨K, hK⟩)
  obtain ⟨ν, hν, hν_fderiv⟩ : ∃ ν : Rn n → Rn n, Measurable ν ∧
      ∀ x, innerSL ℝ (ν x) = fderiv ℝ f x :=
    ⟨fun x ↦ (InnerProductSpace.toDual ℝ (Rn n)).symm (fderiv ℝ f x),
      (InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.measurable.comp (measurable_fderiv ℝ f),
      fun x ↦ ContinuousLinearMap.ext fun v ↦ by
        rw [innerSL_apply_apply, InnerProductSpace.toDual_symm_apply]⟩
  -- Step 3 (Lusin): a closed `C ⊆ B` with `ν|C` continuous and `Lⁿ(B ∖ C) < ε/2`.
  obtain ⟨C, hCB, hC, hνC, hBC⟩ :=
    Submission.c1approx_lusin_closed_continuousOn n n _ ν hB hν (ε / 2) (half_pos hε)
  have hCf : ∀ x ∈ C, HasFDerivAt f (fderiv ℝ f x) x := fun x hx ↦
    DifferentiableAt.hasFDerivAt (hCB hx)
  -- Step 4: Borel remainder moduli `η_k` on `C`, tending to `0` at every point of `C`.
  obtain ⟨η, hη, hη_le, hη_lim⟩ :=
    Submission.c1approx_measurable_remainder_modulus n K C f ν hK hν
  -- Steps 5–6 (Egorov): a closed `A ⊆ C` with `Lⁿ(C ∖ A) < ε/2` and `η_k → 0` uniformly on
  -- every compact subset of `A`.
  obtain ⟨A, hAC, hA, hCA, hA_unif⟩ :=
    Submission.c1approx_egorov_closed_compact_uniform n C η (fun _ ↦ 0) hC.measurableSet hη
      measurable_const (fun x hx ↦ hη_lim x hx (by rw [hν_fderiv]; exact hCf x hx)) (ε / 2)
      (half_pos hε)
  -- Step 7: the hypothesis of Whitney's theorem for `(A, f, ν)`, with `δ = 1 / (k + 1)`.
  have hW : ∀ L ⊆ A, IsCompact L → ∀ ε' : ℝ, 0 < ε' → ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ L, ∀ y ∈ A,
      0 < ‖y - x‖ → ‖y - x‖ < δ → |f y - f x - inner ℝ (ν x) (y - x)| ≤ ε' * ‖y - x‖ := by
    intro L hLA hL ε' hε'
    obtain ⟨k, hk⟩ := eventually_atTop.1
      (Metric.tendstoUniformlyOn_iff.1 (hA_unif L hLA hL) ε' hε')
    refine ⟨1 / ((k : ℝ) + 1), by positivity, fun x hx y hy hxy hxyk ↦ ?_⟩
    have hηk : η k x < ε' := by
      have h := hk k le_rfl x hx
      simp only [Real.dist_eq, zero_sub, abs_neg] at h
      exact (le_abs_self _).trans_lt h
    calc |f y - f x - inner ℝ (ν x) (y - x)| ≤ η k x * ‖y - x‖ :=
          hη_le k x (hAC (hLA hx)) y (hAC hy) hxy hxyk
      _ ≤ ε' * ‖y - x‖ := mul_le_mul_of_nonneg_right hηk.le (norm_nonneg _)
  obtain ⟨g, hg, hgA⟩ :=
    Submission.whitney_extension_theorem n A f ν hA hK.continuous.continuousOn (hνC.mono hAC) hW
  refine ⟨g, hg, ?_⟩
  -- Step 8: the exceptional set lies in `ℝⁿ ∖ A ⊆ (ℝⁿ ∖ B) ∪ (B ∖ C) ∪ (C ∖ A)`.
  have hsub : {x | f x ≠ g x} ∪ {x | ¬ HasFDerivAt f (fderiv ℝ g x) x} ⊆
      {x | ¬ DifferentiableAt ℝ f x} ∪ ({x | DifferentiableAt ℝ f x} \ C) ∪ (C \ A) := by
    intro x hx
    by_cases hxA : x ∈ A
    · obtain ⟨hgx, hDg⟩ := hgA x hxA
      have hfg : fderiv ℝ g x = fderiv ℝ f x := by
        rw [← hν_fderiv]
        ext v
        rw [hDg v, innerSL_apply_apply]
      rcases hx with hx | hx
      · exact (hx hgx.symm).elim
      · exact (hx (hfg ▸ hCf x (hAC hxA))).elim
    · by_cases hxC : x ∈ C
      · exact Or.inr ⟨hxC, hxA⟩
      · by_cases hxB : DifferentiableAt ℝ f x
        · exact Or.inl (Or.inr ⟨hxB, hxC⟩)
        · exact Or.inl (Or.inl hxB)
  calc volume ({x | f x ≠ g x} ∪ {x | ¬ HasFDerivAt f (fderiv ℝ g x) x})
      ≤ volume ({x | ¬ DifferentiableAt ℝ f x} ∪ ({x | DifferentiableAt ℝ f x} \ C) ∪ (C \ A)) :=
        measure_mono hsub
    _ ≤ volume {x | ¬ DifferentiableAt ℝ f x} + volume ({x | DifferentiableAt ℝ f x} \ C) +
          volume (C \ A) :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
        rw [hB_null, zero_add]
        exact ENNReal.add_lt_add hBC hCA
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le, add_halves]
/-- **Simon Ch. 2, Theorem 1.8(i) (pp. 44–45), measure of a Lipschitz image.** For metric spaces
`X, Y`, real `m ≥ 0`, an arbitrary `E ⊆ X` (no measurability needed) and `f` `K`-Lipschitz on `E`,
`𝓗ᵐ(f(E)) ≤ Kᵐ 𝓗ᵐ(E)`. The covering argument is Mathlib's
`LipschitzOnWith.hausdorffMeasure_image_le` for `μH[m]`; multiplying it by the common
normalization `ω_m / 2^m` of `𝓗ᵐ = (ω_m / 2^m) • μH[m]` gives the bound for `𝓗ᵐ`. -/
theorem Submission.lipschitzImage_hausdorff_image_le : ∀ (X Y : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] (m : ℝ) (E : Set X) (f : X → Y) (K : ℝ≥0), 0 ≤ m → LipschitzOnWith K f E → Chapter01.simonHausdorffMeasureReal m (f '' E) ≤ (K : ℝ≥0∞) ^ m * Chapter01.simonHausdorffMeasureReal m E := by
  intro X Y _ _ _ _ _ _ m E f K hm hf
  -- The covering argument for the unnormalized measure: `μH[m] (f '' E) ≤ Kᵐ μH[m] E`.
  have h := hf.hausdorffMeasure_image_le hm
  -- `𝓗ᵐ S = (ω_m / 2^m) * μH[m] S` on `Y` and on `X`; scale `h` by `ω_m / 2^m` and reassociate.
  simp only [Chapter01.simonHausdorffMeasureReal, Measure.smul_apply, smul_eq_mul]
  calc Chapter01.realUnitBallVolume m / 2 ^ m * μH[m] (f '' E)
      ≤ Chapter01.realUnitBallVolume m / 2 ^ m * ((K : ℝ≥0∞) ^ m * μH[m] E) := by gcongr
    _ = (K : ℝ≥0∞) ^ m * (Chapter01.realUnitBallVolume m / 2 ^ m * μH[m] E) :=
      mul_left_comm _ _ _

/-- **Simon Ch. 2, Theorem 1.8(i) (pp. 44–45), measurability of a Lipschitz image.** If `X` is a
σ-compact metric space, `m ≥ 0`, `A ⊆ X` is `𝓗^m`-measurable with `𝓗^m(A) < ∞` and `f` is
`K`-Lipschitz on `A`, then `f(A)` is `𝓗^m`-measurable. A Borel kernel `B ⊆ A` with
`𝓗^m(A \ B) = 0` has finite measure, so `𝓗^m ⌞ B` is a finite, hence regular, measure on the
σ-compact space `X` (Simon's appeal to Ch. 1, 1.15(2)) and gives compact `C j ⊆ B` with
`𝓗^m(B \ C j) < 1/j`. Then `f(A) = ⋃ j, f(C j) ∪ (f(A) \ ⋃ j, f(C j))`: the first set is a
countable union of compact sets, and the second lies in the image of the `𝓗^m`-null set
`A \ ⋃ j, C j`, which is null by the first part (`Submission.lipschitzImage_hausdorff_image_le`). -/
theorem Submission.lipschitzImage_nullMeasurableSet_image : ∀ (X Y : Type) [MetricSpace X] [SigmaCompactSpace X] [MeasurableSpace X] [BorelSpace X] [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] (m : ℝ) (A : Set X) (f : X → Y) (K : ℝ≥0), 0 ≤ m → NullMeasurableSet A (Chapter01.simonHausdorffMeasureReal m) → Chapter01.simonHausdorffMeasureReal m A < ⊤ → LipschitzOnWith K f A → NullMeasurableSet (f '' A) (Chapter01.simonHausdorffMeasureReal m) := by
  intro X Y _ _ _ _ _ _ _ m A f K hm hA hAfin hf
  -- Null subsets of `A` have null images: `𝓗^m(f(E)) ≤ K^m 𝓗^m(E) = 0`.
  have hnull (E : Set X) (hEA : E ⊆ A) (hE : Chapter01.simonHausdorffMeasureReal m E = 0) :
      Chapter01.simonHausdorffMeasureReal m (f '' E) = 0 := by
    have h := Submission.lipschitzImage_hausdorff_image_le X Y m E f K hm (hf.mono hEA)
    rwa [hE, mul_zero, nonpos_iff_eq_zero] at h
  -- A Borel kernel `B ⊆ A` with `𝓗^m(A \ B) = 0`; it has finite measure.
  obtain ⟨B, hBA, hBmeas, hBae⟩ := hA.exists_measurable_subset_ae_eq
  have hAB : Chapter01.simonHausdorffMeasureReal m (A \ B) = 0 := ae_le_set.mp hBae.symm.le
  have hBfin : Chapter01.simonHausdorffMeasureReal m B ≠ ⊤ :=
    ne_top_of_le_ne_top hAfin.ne (measure_mono hBA)
  -- `ν = 𝓗^m ⌞ B` is a finite Borel measure on the σ-compact metric space `X`, hence regular:
  -- there are compact `C j ⊆ B` with `ν(B \ C j) < 1/j`.
  let ν : Measure X := (Chapter01.simonHausdorffMeasureReal m).restrict B
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 hBfin
  have : ν.Regular := inferInstance
  choose C hCB hCc hBC using fun j : ℕ ↦
    hBmeas.exists_isCompact_sdiff_lt (μ := ν) (measure_ne_top ν B)
      (show ((j : ℝ≥0∞)⁻¹) ≠ 0 by simp)
  have hCA (j : ℕ) : C j ⊆ A := (hCB j).trans hBA
  -- The Borel set `B \ ⋃ j, C j ⊆ B` has `𝓗^m`-measure `ν(B \ ⋃ j, C j) ≤ ν(B \ C j) < 1/j`.
  have hBCmeas : MeasurableSet (B \ ⋃ j, C j) :=
    hBmeas.diff (MeasurableSet.iUnion fun j ↦ (hCc j).measurableSet)
  have hBC0 : Chapter01.simonHausdorffMeasureReal m (B \ ⋃ j, C j) = 0 := by
    have h : ν (B \ ⋃ j, C j) = 0 := by
      refine le_antisymm (ge_of_tendsto ENNReal.tendsto_inv_nat_nhds_zero ?_) bot_le
      filter_upwards [] with j
      exact (measure_mono (show B \ ⋃ i, C i ⊆ B \ C j from
        fun x hx ↦ ⟨hx.1, fun hxC ↦ hx.2 (mem_iUnion.2 ⟨j, hxC⟩)⟩)).trans (hBC j).le
    change (Chapter01.simonHausdorffMeasureReal m).restrict B (B \ ⋃ j, C j) = 0 at h
    rwa [Measure.restrict_apply hBCmeas, inter_eq_left.2 sdiff_subset] at h
  -- Hence `D = A \ ⋃ j, C j ⊆ (A \ B) ∪ (B \ ⋃ j, C j)` is `𝓗^m`-null.
  have hD : Chapter01.simonHausdorffMeasureReal m (A \ ⋃ j, C j) = 0 := by
    refine measure_mono_null (show A \ ⋃ j, C j ⊆ (A \ B) ∪ (B \ ⋃ j, C j) from
      fun x hx ↦ ?_) (measure_union_null hAB hBC0)
    by_cases hxB : x ∈ B
    · exact mem_union_right _ ⟨hxB, hx.2⟩
    · exact mem_union_left _ ⟨hx.1, hxB⟩
  -- `G = ⋃ j, f(C j) ⊆ f(A)` is Borel, each `f(C j)` being compact.
  have hGmeas : MeasurableSet (⋃ j, f '' C j) :=
    MeasurableSet.iUnion fun j ↦
      ((hCc j).image_of_continuousOn (hf.mono (hCA j)).continuousOn).measurableSet
  have hGA : (⋃ j, f '' C j) ⊆ f '' A := iUnion_subset fun j ↦ image_mono (hCA j)
  -- `f(A) \ G ⊆ f(D)`, which is `𝓗^m`-null.
  have hrest : f '' A \ ⋃ j, f '' C j ⊆ f '' (A \ ⋃ j, C j) := by
    rintro y ⟨⟨x, hxA, rfl⟩, hy⟩
    refine ⟨x, ⟨hxA, fun hxC ↦ ?_⟩, rfl⟩
    obtain ⟨j, hxj⟩ := mem_iUnion.1 hxC
    exact hy (mem_iUnion.2 ⟨j, mem_image_of_mem f hxj⟩)
  rw [← union_sdiff_cancel hGA]
  exact hGmeas.nullMeasurableSet.union
    (NullMeasurableSet.of_null (measure_mono_null hrest (hnull _ sdiff_subset hD)))
/-- **Simon Ch. 2, proof of Theorem 1.8(ii) (p. 45), nested partitions.** A separable metric space
`X` has countable Borel partitions `(P i j)_j`, `i ∈ ℕ`, into pieces of mesh `< 1/(i+1)`, each
refining the previous one. For a dense sequence `q`, level `i` uses the disjointed balls
`Q i l = B(q l, rᵢ) \ ⋃_{l' < l} B(q l', rᵢ)`, `rᵢ = 1/(3(i+1))`; then `P 0 = Q 0` and
`P (i+1) n = P i u ∩ Q (i+1) v`, where `(u, v) = Nat.unpair n`. -/
theorem Submission.lipschitzImage_exists_nested_partitions : ∀ (X : Type) [MetricSpace X] [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [BorelSpace X], ∃ P : ℕ → ℕ → Set X, (∀ i j, MeasurableSet (P i j)) ∧ (∀ i j k, j ≠ k → Disjoint (P i j) (P i k)) ∧ (∀ i, ⋃ j, P i j = Set.univ) ∧ (∀ i j, ∀ x ∈ P i j, ∀ x' ∈ P i j, dist x x' < 1 / ((i : ℝ) + 1)) ∧ (∀ i j, ∃ k, P (i + 1) j ⊆ P i k) := by
  intro X _ _ _ _
  -- Empty `X`: all pieces are empty.
  rcases isEmpty_or_nonempty X with hX | hX
  · exact ⟨fun _ _ ↦ ∅, fun _ _ ↦ MeasurableSet.empty, fun _ _ _ _ ↦ empty_disjoint _,
      fun _ ↦ eq_univ_of_forall isEmptyElim, fun _ _ x ↦ isEmptyElim x, fun _ _ ↦ ⟨0, subset_rfl⟩⟩
  -- A dense sequence `q`, and the level-`i` pieces `Q i l`: Borel, disjoint, covering, and
  -- contained in `B(q l, 1/(3(i+1)))`.
  obtain ⟨q, hq⟩ := TopologicalSpace.exists_dense_seq X
  obtain ⟨Q, hQmeas, hQdisj, hQcov, hQball⟩ : ∃ Q : ℕ → ℕ → Set X,
      (∀ i l, MeasurableSet (Q i l)) ∧ (∀ i l l', l ≠ l' → Disjoint (Q i l) (Q i l')) ∧
      (∀ i (x : X), ∃ l, x ∈ Q i l) ∧ ∀ i l, Q i l ⊆ ball (q l) (1 / ((i : ℝ) + 1) / 3) := by
    refine ⟨fun i ↦ disjointed fun l ↦ ball (q l) (1 / ((i : ℝ) + 1) / 3),
      fun i ↦ MeasurableSet.disjointed fun _ ↦ measurableSet_ball,
      fun i _ _ h ↦ disjoint_disjointed _ h, fun i x ↦ ?_,
      fun i ↦ disjointed_subset fun l ↦ ball (q l) (1 / ((i : ℝ) + 1) / 3)⟩
    obtain ⟨l, hl⟩ := hq.exists_dist_lt x (by positivity : (0 : ℝ) < 1 / ((i : ℝ) + 1) / 3)
    have hx : x ∈ ⋃ l, ball (q l) (1 / ((i : ℝ) + 1) / 3) := mem_iUnion.2 ⟨l, mem_ball.2 hl⟩
    rw [← iUnion_disjointed] at hx
    exact mem_iUnion.1 hx
  -- The refinement: `P 0 = Q 0` and `P (i+1) n = P i (unpair n).1 ∩ Q (i+1) (unpair n).2`.
  obtain ⟨P, hP0, hPsucc⟩ : ∃ P : ℕ → ℕ → Set X, (∀ n, P 0 n = Q 0 n) ∧
      ∀ i n, P (i + 1) n = P i (Nat.unpair n).1 ∩ Q (i + 1) (Nat.unpair n).2 :=
    ⟨fun i ↦ Nat.rec (motive := fun _ ↦ ℕ → Set X) (Q 0)
      (fun i Pi n ↦ Pi (Nat.unpair n).1 ∩ Q (i + 1) (Nat.unpair n).2) i, fun _ ↦ rfl,
      fun _ _ ↦ rfl⟩
  have hPcov : ∀ i (x : X), ∃ j, x ∈ P i j := by
    intro i x
    induction i with
    | zero =>
      obtain ⟨l, hl⟩ := hQcov 0 x
      exact ⟨l, (hP0 l).symm ▸ hl⟩
    | succ i ih =>
      obtain ⟨j, hj⟩ := ih
      obtain ⟨l, hl⟩ := hQcov (i + 1) x
      refine ⟨Nat.pair j l, ?_⟩
      rw [hPsucc, Nat.unpair_pair]
      exact ⟨hj, hl⟩
  refine ⟨P, fun i ↦ ?_, fun i ↦ ?_, fun i ↦ eq_univ_of_forall fun x ↦ mem_iUnion.2 (hPcov i x),
    fun i n x hx x' hx' ↦ ?_,
    fun i n ↦ ⟨(Nat.unpair n).1, (hPsucc i n).subset.trans inter_subset_left⟩⟩
  · -- Borel.
    induction i with
    | zero => exact fun n ↦ (hP0 n).symm ▸ hQmeas 0 n
    | succ i ih => exact fun n ↦ (hPsucc i n).symm ▸ (ih _).inter (hQmeas _ _)
  · -- Disjoint: distinct `n, n'` have distinct `unpair n, unpair n'`.
    induction i with
    | zero => intro j k hjk; rw [hP0, hP0]; exact hQdisj 0 j k hjk
    | succ i ih =>
      intro j k hjk
      rw [hPsucc, hPsucc]
      by_cases hu : (Nat.unpair j).1 = (Nat.unpair k).1
      · have hv : (Nat.unpair j).2 ≠ (Nat.unpair k).2 := fun hv ↦
          hjk (by rw [← Nat.pair_unpair j, ← Nat.pair_unpair k, hu, hv])
        exact (hQdisj _ _ _ hv).mono inter_subset_right inter_subset_right
      · exact (ih _ _ hu).mono inter_subset_left inter_subset_left
  · -- Mesh: `P i n` lies in a ball of radius `1/(3(i+1))`.
    obtain ⟨l, hl⟩ : ∃ l, P i n ⊆ Q i l := by
      cases i with
      | zero => exact ⟨n, (hP0 n).subset⟩
      | succ i => exact ⟨(Nat.unpair n).2, (hPsucc i n).subset.trans inter_subset_right⟩
    have h₁ := mem_ball.1 (hQball i l (hl hx))
    have h₂ := mem_ball.1 (hQball i l (hl hx'))
    have hi : (0 : ℝ) < 1 / ((i : ℝ) + 1) := by positivity
    linarith [dist_triangle_right x x' (q l)]
/-- **Simon Ch. 2, Theorem 1.8(ii), counting step (p. 45).** For nested partitions `P i ·` of `X`
into pieces any two of whose points are at distance `< 1/(i+1)`, the piece counts
`N_i(y) = ∑ⱼ 1_{f(A ∩ P i j)}(y)` increase pointwise to the multiplicity `N(f, y) = fiberCount A f y`. -/
theorem Submission.lipschitzImage_iSup_pieceCount_eq_fiberCount : ∀ (X Y : Type) [MetricSpace X] (A : Set X) (f : X → Y) (P : ℕ → ℕ → Set X), (∀ i j k, j ≠ k → Disjoint (P i j) (P i k)) → (∀ i, ⋃ j, P i j = Set.univ) → (∀ i j, ∀ x ∈ P i j, ∀ x' ∈ P i j, dist x x' < 1 / ((i : ℝ) + 1)) → (∀ i j, ∃ k, P (i + 1) j ⊆ P i k) → ∀ y : Y, Monotone (fun i ↦ ∑' j, (f '' (A ∩ P i j)).indicator (1 : Y → ℝ≥0∞) y) ∧ ⨆ i, ∑' j, (f '' (A ∩ P i j)).indicator (1 : Y → ℝ≥0∞) y = fiberCount A f y := by
  intro X Y _ A f P hdisj hcov hdiam hnest y
  -- Every point lies in exactly one piece of each level.
  have hmem : ∀ i (x : X), ∃ j, x ∈ P i j := fun i x ↦ by
    have hx : x ∈ ⋃ j, P i j := by rw [hcov i]; exact Set.mem_univ x
    exact Set.mem_iUnion.1 hx
  have uniq : ∀ {i j k : ℕ} {x : X}, x ∈ P i j → x ∈ P i k → j = k := by
    intro i j k x hj hk
    by_contra hne
    exact Set.disjoint_left.1 (hdisj i j k hne) hj hk
  choose p hp using hmem
  choose q hq using hnest
  set S := A ∩ f ⁻¹' {y}
  -- `N_i(y)` is the cardinality of `p i '' S`, the set of `j` with `y ∈ f(A ∩ P i j)`.
  have hiff : ∀ i j, y ∈ f '' (A ∩ P i j) ↔ j ∈ p i '' S := by
    intro i j
    constructor
    · rintro ⟨x, ⟨hxA, hxP⟩, hfx⟩
      exact ⟨x, ⟨hxA, hfx⟩, uniq (hp i x) hxP⟩
    · rintro ⟨x, ⟨hxA, hfx⟩, rfl⟩
      exact ⟨x, ⟨hxA, hp i x⟩, hfx⟩
  have hN : ∀ i, ∑' j, (f '' (A ∩ P i j)).indicator (1 : Y → ℝ≥0∞) y =
      ((p i '' S).encard : ℝ≥0∞) := by
    intro i
    have hind : ∀ j, (f '' (A ∩ P i j)).indicator (1 : Y → ℝ≥0∞) y =
        (p i '' S).indicator (fun _ ↦ (1 : ℝ≥0∞)) j := by
      intro j
      by_cases hj : j ∈ p i '' S
      · rw [Set.indicator_of_mem hj, Set.indicator_of_mem ((hiff i j).2 hj), Pi.one_apply]
      · rw [Set.indicator_of_notMem hj, Set.indicator_of_notMem (mt (hiff i j).1 hj)]
    rw [tsum_congr hind, ← tsum_subtype, ENNReal.tsum_set_one]
  -- (a) `p i '' S` is the image of `p (i + 1) '' S` under the nesting map `q i`.
  have hmono : ∀ i, (p i '' S).encard ≤ (p (i + 1) '' S).encard := by
    intro i
    have himage : p i '' S = q i '' (p (i + 1) '' S) := by
      rw [Set.image_image]
      exact Set.image_congr fun x _ ↦ uniq (hp i x) (hq i (p (i + 1) x) (hp (i + 1) x))
    rw [himage]
    exact Set.encard_image_le _ _
  -- (c) A finite `F ⊆ S` with `n` points meets `n` distinct pieces once `1/(i+1)` is below all
  -- distances between distinct points of `F`.
  have hexh : ∀ n : ℕ, (n : ℕ∞) ≤ S.encard → ∃ i, (n : ℕ∞) ≤ (p i '' S).encard := by
    intro n hn
    obtain ⟨F, hFS, hFn⟩ := Set.exists_subset_encard_eq hn
    have hFfin : F.Finite := Set.finite_of_encard_eq_coe hFn
    have hev : ∀ᶠ i : ℕ in atTop, ∀ z ∈ F ×ˢ F, z.1 ≠ z.2 → 1 / ((i : ℝ) + 1) < dist z.1 z.2 := by
      rw [Filter.eventually_all_finite (hFfin.prod hFfin)]
      intro z _
      by_cases hz : z.1 = z.2
      · exact Filter.Eventually.of_forall fun _ h ↦ absurd hz h
      · filter_upwards [tendsto_one_div_add_atTop_nhds_zero_nat.eventually
          (gt_mem_nhds (dist_pos.2 hz))] with i hi _
        exact hi
    obtain ⟨i, hi⟩ := hev.exists
    have hinj : Set.InjOn (p i) F := by
      intro x hx x' hx' hxx'
      by_contra hne
      have hx'P : x' ∈ P i (p i x) := by rw [hxx']; exact hp i x'
      exact absurd ((hi (x, x') ⟨hx, hx'⟩ hne).trans (hdiam i (p i x) x (hp i x) x' hx'P))
        (lt_irrefl _)
    refine ⟨i, ?_⟩
    calc (n : ℕ∞) = F.encard := hFn.symm
      _ = (p i '' F).encard := hinj.encard_image.symm
      _ ≤ (p i '' S).encard := Set.encard_le_encard (Set.image_mono hFS)
  simp only [hN]
  refine ⟨monotone_nat_of_le_succ fun i ↦ ENat.toENNReal_le.2 (hmono i), ?_⟩
  show ⨆ i, ((p i '' S).encard : ℝ≥0∞) = ((S.encard : ℕ∞) : ℝ≥0∞)
  -- (b) `N_i(y) ≤ encard S`; the reverse inequality for the supremum follows from (c).
  refine le_antisymm (iSup_le fun i ↦ ENat.toENNReal_le.2 (Set.encard_image_le _ _)) ?_
  rcases eq_or_ne S.encard ⊤ with htop | htop
  · rw [htop, ENat.toENNReal_top]
    refine top_le_iff.2 (ENNReal.eq_top_of_forall_nnreal_le fun r ↦ ?_)
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ENNReal.coe_ne_top : (r : ℝ≥0∞) ≠ ⊤)
    obtain ⟨i, hi⟩ := hexh n (by rw [htop]; exact le_top)
    calc (r : ℝ≥0∞) ≤ n := hn.le
      _ = ((n : ℕ∞) : ℝ≥0∞) := (ENat.toENNReal_coe n).symm
      _ ≤ ((p i '' S).encard : ℝ≥0∞) := ENat.toENNReal_le.2 hi
      _ ≤ ⨆ i, ((p i '' S).encard : ℝ≥0∞) := le_iSup (fun i ↦ ((p i '' S).encard : ℝ≥0∞)) i
  · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 htop
    obtain ⟨i, hi⟩ := hexh k hk.le
    calc ((S.encard : ℕ∞) : ℝ≥0∞) = ((k : ℕ∞) : ℝ≥0∞) := by rw [hk]
      _ ≤ ((p i '' S).encard : ℝ≥0∞) := ENat.toENNReal_le.2 hi
      _ ≤ ⨆ i, ((p i '' S).encard : ℝ≥0∞) := le_iSup (fun i ↦ ((p i '' S).encard : ℝ≥0∞)) i

/-- **Simon Ch. 2, Theorem 1.8 (p. 44).** (i) is the two image results applied to `A`. (ii): cut `A`
along nested Borel partitions `P i ·` of `X` of mesh `< 1/(i+1)`. The piece counts
`N_i(y) = ∑'_j 1_{f(A ∩ P i j)}(y)` are a.e.-measurable (each `f(A ∩ P i j)` is null-measurable by
(i)) and increase to `fiberCount A f`, so by monotone convergence `∫ N = sup_i ∫ N_i`, where
`∫ N_i = ∑'_j Hᵐ(f(A ∩ P i j)) ≤ Kᵐ ∑'_j Hᵐ(A ∩ P i j) = Kᵐ Hᵐ(A)`. -/
theorem Submission.lipschitz_image_hausdorff_theorem : LipschitzImageHausdorff := by
  intro X Y _ _ _ _ _ _ _ m A f K hm hA hAfin hf
  refine ⟨⟨Submission.lipschitzImage_nullMeasurableSet_image X Y m A f K hm hA hAfin hf,
    Submission.lipschitzImage_hausdorff_image_le X Y m A f K hm hf⟩, ?_⟩
  obtain ⟨P, hPmeas, hPdisj, hPcover, hPdiam, hPnest⟩ :=
    Submission.lipschitzImage_exists_nested_partitions X
  have hcount := Submission.lipschitzImage_iSup_pieceCount_eq_fiberCount X Y A f P hPdisj hPcover
    hPdiam hPnest
  have hpiece (i j : ℕ) : NullMeasurableSet (A ∩ P i j) (Chapter01.simonHausdorffMeasureReal m) :=
    hA.inter (hPmeas i j).nullMeasurableSet
  have himage (i j : ℕ) :
      NullMeasurableSet (f '' (A ∩ P i j)) (Chapter01.simonHausdorffMeasureReal m) :=
    Submission.lipschitzImage_nullMeasurableSet_image X Y m (A ∩ P i j) f K hm (hpiece i j)
      ((measure_mono Set.inter_subset_left).trans_lt hAfin) (hf.mono Set.inter_subset_left)
  have hind (i j : ℕ) : AEMeasurable ((f '' (A ∩ P i j)).indicator (1 : Y → ℝ≥0∞))
      (Chapter01.simonHausdorffMeasureReal m) :=
    aemeasurable_one.indicator₀ (himage i j)
  have hN (i : ℕ) : AEMeasurable (fun y ↦ ∑' j, (f '' (A ∩ P i j)).indicator (1 : Y → ℝ≥0∞) y)
      (Chapter01.simonHausdorffMeasureReal m) :=
    AEMeasurable.tsum (hind i)
  have hfib : fiberCount A f =
      fun y ↦ ⨆ i, ∑' j, (f '' (A ∩ P i j)).indicator (1 : Y → ℝ≥0∞) y :=
    funext fun y ↦ (hcount y).2.symm
  refine ⟨by rw [hfib]; exact AEMeasurable.iSup hN, ?_⟩
  calc ∫⁻ y, fiberCount A f y ∂Chapter01.simonHausdorffMeasureReal m
      = ⨆ i, ∫⁻ y, ∑' j, (f '' (A ∩ P i j)).indicator (1 : Y → ℝ≥0∞) y
          ∂Chapter01.simonHausdorffMeasureReal m := by
        rw [hfib]
        exact lintegral_iSup' hN (ae_of_all _ fun y ↦ (hcount y).1)
    _ ≤ (K : ℝ≥0∞) ^ m * Chapter01.simonHausdorffMeasureReal m A := by
        refine iSup_le fun i ↦ ?_
        calc ∫⁻ y, ∑' j, (f '' (A ∩ P i j)).indicator (1 : Y → ℝ≥0∞) y
              ∂Chapter01.simonHausdorffMeasureReal m
            = ∑' j, Chapter01.simonHausdorffMeasureReal m (f '' (A ∩ P i j)) := by
              rw [lintegral_tsum (hind i)]
              exact tsum_congr fun j ↦ lintegral_indicator_one₀ (himage i j)
          _ ≤ ∑' j, (K : ℝ≥0∞) ^ m * Chapter01.simonHausdorffMeasureReal m (A ∩ P i j) :=
              ENNReal.tsum_le_tsum fun j ↦ Submission.lipschitzImage_hausdorff_image_le X Y m
                (A ∩ P i j) f K hm (hf.mono Set.inter_subset_left)
          _ = (K : ℝ≥0∞) ^ m * Chapter01.simonHausdorffMeasureReal m A := by
              rw [ENNReal.tsum_mul_left, ← measure_iUnion₀ (f := fun j ↦ A ∩ P i j)
                (fun j k hjk ↦ ((hPdisj i j k hjk).mono Set.inter_subset_right
                  Set.inter_subset_right).aedisjoint) (hpiece i), ← Set.inter_iUnion, hPcover i,
                Set.inter_univ]
/-- **Simon Ch. 2, proof of Theorem 1.9 (p. 46), isodiametric step.** If `f : X → ℝᵐ` is
`K`-Lipschitz on `D`, then `Lᵐ(closure f(D)) ≤ ω_m Kᵐ (diam D)ᵐ / 2ᵐ`: the closed set `closure f(D)` has
diameter `diam f(D) ≤ K diam D`, and the isodiametric inequality (Simon Ch. 1, 2.10)
`Lᵐ(A) ≤ ω_m (diam A / 2)ᵐ` is applied to it. The isodiametric inequality is proved inline:
successive coordinate Steiner symmetrizations of a compact set (Fubini for the volume, a slice
estimate for the diameter) give a centrally symmetric compact set, which lies in a ball of radius
`diam / 2`; the ball volume `ω_m rᵐ` comes from the Gaussian integral and the `Γ` integral. -/
theorem Submission.eilenberg_covering_lipschitz_image_volume_le : ∀ (X : Type) [MetricSpace X] (m : ℕ) (D : Set X) (f : X → Rn m) (K : ℝ≥0), LipschitzOnWith K f D → volume (closure (f '' D)) ≤ Chapter01.realUnitBallVolume (m : ℝ) * (K : ℝ≥0∞) ^ m * ediam D ^ m / (2 : ℝ≥0∞) ^ m := by
  intro X _ m D f K hf
  -- `diam f(D) ≤ K diam D`.
  have hfD : ediam (f '' D) ≤ K * ediam D := by
    refine ediam_le ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩
    calc edist (f x) (f x') ≤ K * edist x x' := hf hx hx'
      _ ≤ K * ediam D := by gcongr; exact edist_le_ediam_of_mem hx hx'
  rcases m with _ | n
  · -- `ℝ⁰` is a single point of volume one.
    simp only [pow_zero, mul_one, div_one, Nat.cast_zero, Chapter01.realUnitBallVolume_zero]
    calc volume (closure (f '' D)) ≤ volume (univ : Set (Rn 0)) := measure_mono (subset_univ _)
      _ = 1 := by rw [volume_euclideanSpace_eq_dirac, measure_univ]
  -- The unit ball of `ℝⁿ⁺¹` has volume `ω_{n+1}`.
  have hball : volume (ball (0 : Rn (n + 1)) 1) = Chapter01.realUnitBallVolume ((n + 1 : ℕ) : ℝ) := by
    -- The Gaussian integral `∫ exp (-‖x‖²) = π^{(n+1)/2}`, by Tonelli over the coordinates.
    have hG1 : ∫⁻ t : ℝ, ENNReal.ofReal (Real.exp (-t ^ 2)) = ENNReal.ofReal (√Real.pi) := by
      have h := integral_gaussian 1
      rw [div_one] at h
      rw [← h, ofReal_integral_eq_lintegral_ofReal (integrable_exp_neg_mul_sq one_pos)
        (ae_of_all _ fun t => (Real.exp_pos _).le)]
      simp only [neg_mul, one_mul]
    have hprod : ∀ k : ℕ, ∫⁻ y : Fin k → ℝ, ∏ i, ENNReal.ofReal (Real.exp (-y i ^ 2)) =
        ENNReal.ofReal (√Real.pi) ^ k := by
      have hg : Measurable fun t : ℝ => ENNReal.ofReal (Real.exp (-t ^ 2)) := by fun_prop
      intro k
      induction k with
      | zero => simp [volume_pi]
      | succ k ih =>
        rw [← ((volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0).symm).lintegral_comp_emb
          (MeasurableEquiv.measurableEmbedding _)]
        simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply,
          Fin.prod_univ_succ, Fin.insertNth_zero', Fin.cons_zero, Fin.cons_succ]
        rw [show (volume : Measure (ℝ × (Fin k → ℝ))) = volume.prod volume from rfl,
          lintegral_prod_mul (g := fun z : Fin k → ℝ => ∏ i, ENNReal.ofReal (Real.exp (-z i ^ 2)))
            hg.aemeasurable (Finset.measurable_prod _ fun i _ => hg.comp (measurable_pi_apply i)).aemeasurable,
          hG1, ih, pow_succ']
    have hgauss : ∫⁻ x : Rn (n + 1), ENNReal.ofReal (Real.exp (-‖x‖ ^ 2)) =
        ENNReal.ofReal (√Real.pi) ^ (n + 1) := by
      rw [← (PiLp.volume_preserving_toLp (Fin (n + 1))).lintegral_comp (by fun_prop), ← hprod]
      congr 1
      funext y
      rw [EuclideanSpace.norm_sq_eq, ← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le),
        ← Real.exp_sum, ← Finset.sum_neg_distrib]
      simp [Real.norm_eq_abs, sq_abs]
    -- Layer cake: `exp (-‖x‖²) = ∫_{‖x‖²}^∞ e^{-t} dt`, then Tonelli and the `Γ` integral.
    set V := volume (ball (0 : Rn (n + 1)) 1)
    have hlayer : ∫⁻ x : Rn (n + 1), ENNReal.ofReal (Real.exp (-‖x‖ ^ 2)) =
        V * ENNReal.ofReal (Real.Gamma (((n + 1 : ℕ) : ℝ) / 2 + 1)) := by
      let F : Rn (n + 1) × ℝ → ℝ≥0∞ :=
        {p | ‖p.1‖ ^ 2 < p.2}.indicator fun p => ENNReal.ofReal (Real.exp (-p.2))
      have hF : Measurable F :=
        (by fun_prop : Measurable fun p : Rn (n + 1) × ℝ => ENNReal.ofReal (Real.exp (-p.2))).indicator
          (measurableSet_lt (by fun_prop) (by fun_prop))
      have hpt : ∀ x : Rn (n + 1), ENNReal.ofReal (Real.exp (-‖x‖ ^ 2)) = ∫⁻ t in Ioi 0, F (x, t) := by
        intro x
        rw [← integral_exp_neg_Ioi, ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi _)
          (ae_of_all _ fun t => (Real.exp_pos _).le)]
        change _ = ∫⁻ t in Ioi 0, (Ioi (‖x‖ ^ 2)).indicator (fun t => ENNReal.ofReal (Real.exp (-t))) t
        rw [lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
          inter_eq_left.mpr (Ioi_subset_Ioi (by positivity))]
      have hslice : ∀ t ∈ Ioi (0 : ℝ), ∫⁻ x, F (x, t) =
          ENNReal.ofReal (Real.exp (-t) * t ^ (((n + 1 : ℕ) : ℝ) / 2)) * V := by
        intro t ht
        have hset : {x : Rn (n + 1) | ‖x‖ ^ 2 < t} = ball 0 (√t) := by
          ext x
          rw [mem_ofPred_eq, mem_ball_zero_iff, Real.lt_sqrt (norm_nonneg x)]
        change ∫⁻ x, {x : Rn (n + 1) | ‖x‖ ^ 2 < t}.indicator (fun _ => ENNReal.ofReal (Real.exp (-t))) x = _
        rw [hset, lintegral_indicator_const measurableSet_ball,
          Measure.addHaar_ball_of_pos _ _ (Real.sqrt_pos.mpr ht), finrank_euclideanSpace_fin, ← mul_assoc,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
          ← Real.rpow_mul (le_of_lt ht), one_div_mul_eq_div]
      calc ∫⁻ x : Rn (n + 1), ENNReal.ofReal (Real.exp (-‖x‖ ^ 2))
          = ∫⁻ x, ∫⁻ t in Ioi 0, F (x, t) := lintegral_congr fun x => hpt x
        _ = ∫⁻ t in Ioi 0, ∫⁻ x, F (x, t) := lintegral_lintegral_swap hF.aemeasurable
        _ = ∫⁻ t in Ioi 0, ENNReal.ofReal (Real.exp (-t) * t ^ (((n + 1 : ℕ) : ℝ) / 2)) * V :=
          setLIntegral_congr_fun measurableSet_Ioi hslice
        _ = V * ENNReal.ofReal (Real.Gamma (((n + 1 : ℕ) : ℝ) / 2 + 1)) := by
          rw [lintegral_mul_const _ (by fun_prop), mul_comm, Real.Gamma_eq_integral (by positivity),
            add_sub_cancel_right, ofReal_integral_eq_lintegral_ofReal
              (by
                have h := Real.GammaIntegral_convergent (s := ((n + 1 : ℕ) : ℝ) / 2 + 1) (by positivity)
                rwa [add_sub_cancel_right] at h)
              (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
                have : (0 : ℝ) < t := ht
                positivity)]
    have hGpos : 0 < Real.Gamma (((n + 1 : ℕ) : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
    rw [hgauss] at hlayer
    rw [Chapter01.realUnitBallVolume, ENNReal.ofReal_div_of_pos hGpos, ENNReal.eq_div_iff
      (ENNReal.ofReal_pos.mpr hGpos).ne' ENNReal.ofReal_ne_top, mul_comm, ← hlayer,
      ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul Real.pi_pos.le]
    congr 2
    ring
  -- A compact set has a centrally symmetric compact replacement with no larger diameter and no
  -- smaller volume (successive coordinate Steiner symmetrizations).
  have hrep : ∀ A₀ : Set (Rn (n + 1)), IsCompact A₀ → ∃ L : Set (Rn (n + 1)), IsCompact L ∧
      ediam L ≤ ediam A₀ ∧ volume A₀ ≤ volume L ∧ ∀ x ∈ L, -x ∈ L := by
    intro A₀ hA₀
    -- One-dimensional step: centering two real slices keeps every cross distance `≤ d`.
    have hcen : ∀ (S T : Set ℝ) (d x y : ℝ), (∀ a ∈ S, ∀ b ∈ T, dist a b ≤ d) → S.Nonempty →
        T.Nonempty → |x| ≤ (volume S).toReal / 2 → |y| ≤ (volume T).toReal / 2 → dist x y ≤ d := by
      intro S T d x y hST ⟨a₀, ha₀⟩ ⟨b₀, hb₀⟩ hx hy
      have hab : ∀ a ∈ S, ∀ b ∈ T, a - b ≤ d ∧ b - a ≤ d := fun a ha b hb =>
        abs_sub_le_iff.mp (by simpa only [Real.dist_eq] using hST a ha b hb)
      have hbl : BddBelow S := ⟨b₀ - d, fun a ha => by linarith [(hab a ha b₀ hb₀).2]⟩
      have hbu : BddAbove S := ⟨b₀ + d, fun a ha => by linarith [(hab a ha b₀ hb₀).1]⟩
      have hT : ∀ b ∈ T, sSup S - d ≤ b ∧ b ≤ sInf S + d := fun b hb =>
        ⟨by linarith [csSup_le ⟨a₀, ha₀⟩ fun a ha => (by linarith [(hab a ha b hb).1] : a ≤ b + d)],
          by linarith [le_csInf ⟨a₀, ha₀⟩ fun a ha => (by linarith [(hab a ha b hb).2] : b - d ≤ a)]⟩
      have h1 : (volume S).toReal ≤ sSup S - sInf S := by
        refine ENNReal.toReal_le_of_le_ofReal (by linarith [csInf_le hbl ha₀, le_csSup hbu ha₀]) ?_
        rw [← Real.volume_Icc]
        exact measure_mono (subset_Icc_csInf_csSup hbl hbu)
      have h2 : (volume T).toReal ≤ sInf S + d - (sSup S - d) := by
        refine ENNReal.toReal_le_of_le_ofReal (by linarith [hT b₀ hb₀]) ?_
        rw [← Real.volume_Icc]
        exact measure_mono fun b hb => hT b hb
      rw [Real.dist_eq]
      linarith [abs_sub x y]
    -- Changing the `j`-th coordinate changes squared distances only in that coordinate.
    have hupd : ∀ (j : Fin (n + 1)) (x y : Rn (n + 1)) (a b : ℝ),
        dist (WithLp.toLp 2 (Function.update x.ofLp j a)) (WithLp.toLp 2 (Function.update y.ofLp j b)) ^ 2 =
          dist x y ^ 2 - dist (x j) (y j) ^ 2 + dist a b ^ 2 := by
      intro j x y a b
      rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ j),
        ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
      simp only [Function.update_self]
      rw [Finset.sum_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi),
        Function.update_of_ne (Finset.ne_of_mem_erase hi)]]
      ring
    -- Coordinate Steiner symmetrization: each slice along the `j`-th axis is replaced by the
    -- centered closed interval of the same length.
    let St : Fin (n + 1) → Set (Rn (n + 1)) → Set (Rn (n + 1)) := fun j A =>
      {x | {t : ℝ | WithLp.toLp 2 (Function.update x.ofLp j t) ∈ A}.Nonempty ∧
        |x j| ≤ (volume {t : ℝ | WithLp.toLp 2 (Function.update x.ofLp j t) ∈ A}).toReal / 2}
    have hdiam : ∀ (j : Fin (n + 1)) (A : Set (Rn (n + 1))), ediam (St j A) ≤ ediam A := by
      intro j A
      by_cases hfin : ediam A = ∞
      · rw [hfin]
        exact le_top
      have hbdd : Bornology.IsBounded A := isBounded_iff_ediam_ne_top.mpr hfin
      rw [← ENNReal.ofReal_toReal hfin]
      refine ediam_le_of_forall_dist_le fun x hx y hy => ?_
      obtain ⟨⟨a₀, ha₀⟩, hx⟩ := hx
      obtain ⟨⟨b₀, hb₀⟩, hy⟩ := hy
      have hsq : ∀ a ∈ {t : ℝ | WithLp.toLp 2 (Function.update x.ofLp j t) ∈ A},
          ∀ b ∈ {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A},
          dist a b ^ 2 ≤ (ediam A).toReal ^ 2 - dist x y ^ 2 + dist (x j) (y j) ^ 2 := by
        intro a ha b hb
        have h := pow_le_pow_left₀ dist_nonneg (dist_le_diam_of_mem hbdd ha hb) 2
        rw [hupd] at h
        change _ ≤ (ediam A).toReal ^ 2 at h
        linarith
      have hD := (sq_nonneg _).trans (hsq a₀ ha₀ b₀ hb₀)
      have hc := hcen _ _ _ (x j) (y j) (fun a ha b hb => Real.le_sqrt_of_sq_le (hsq a ha b hb))
        ⟨a₀, ha₀⟩ ⟨b₀, hb₀⟩ hx hy
      have h2 := pow_le_pow_left₀ dist_nonneg hc 2
      rw [Real.sq_sqrt hD] at h2
      exact (pow_le_pow_iff_left₀ dist_nonneg ENNReal.toReal_nonneg two_ne_zero).mp (by linarith)
    have hvol : ∀ (j : Fin (n + 1)) (A : Set (Rn (n + 1))), IsCompact A → volume A ≤ volume (St j A) := by
      intro j A hA
      set S := St j A
      -- `ℝⁿ⁺¹ ≃ ℝ × ℝⁿ`, splitting off the `j`-th coordinate, preserves volume.
      let φ : ℝ × (Fin n → ℝ) → Rn (n + 1) := fun p =>
        WithLp.toLp 2 ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) j).symm p)
      have hφ : MeasurePreserving φ volume volume := (PiLp.volume_preserving_toLp (Fin (n + 1))).comp
        (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) j).symm
      have hφj (t : ℝ) (z : Fin n → ℝ) : φ (t, z) j = t :=
        Fin.insertNth_apply_same (α := fun _ : Fin (n + 1) => ℝ) j t z
      have hφsl (t : ℝ) (z : Fin n → ℝ) :
          {s : ℝ | WithLp.toLp 2 (Function.update (φ (t, z)).ofLp j s) ∈ A} = (fun s => φ (s, z)) ⁻¹' A := by
        ext s
        change WithLp.toLp 2 (Function.update (j.insertNth t z) j s) ∈ A ↔ WithLp.toLp 2 (j.insertNth s z) ∈ A
        rw [Fin.update_insertNth]
      have hT := measurableSet_toMeasurable volume S
      calc volume A = volume (φ ⁻¹' A) := (hφ.measure_preimage hA.measurableSet.nullMeasurableSet).symm
        _ = ∫⁻ z, volume ((fun t => φ (t, z)) ⁻¹' A) :=
          Measure.prod_apply_symm (hA.measurableSet.preimage hφ.measurable)
        _ ≤ ∫⁻ z, volume ((fun t => φ (t, z)) ⁻¹' toMeasurable volume S) := lintegral_mono fun z => ?_
        _ = volume (φ ⁻¹' toMeasurable volume S) := (Measure.prod_apply_symm (hT.preimage hφ.measurable)).symm
        _ = volume S := by rw [hφ.measure_preimage hT.nullMeasurableSet, measure_toMeasurable]
      -- Each slice has the length of its centered interval, which lies in the slice of `S`.
      rcases eq_empty_or_nonempty ((fun t => φ (t, z)) ⁻¹' A) with h | h
      · rw [h, measure_empty]
        exact zero_le
      have hfin : volume ((fun t => φ (t, z)) ⁻¹' A) ≠ ∞ := by
        refine ne_top_of_le_ne_top ((hA.image (by fun_prop : Continuous fun x : Rn (n + 1) => x j)).measure_lt_top.ne)
          (measure_mono fun t ht => ⟨φ (t, z), ht, hφj t z⟩)
      calc volume ((fun t => φ (t, z)) ⁻¹' A)
          = volume (Icc (-((volume ((fun t => φ (t, z)) ⁻¹' A)).toReal / 2))
              ((volume ((fun t => φ (t, z)) ⁻¹' A)).toReal / 2)) := by
            rw [Real.volume_Icc, sub_neg_eq_add, add_halves, ENNReal.ofReal_toReal hfin]
        _ ≤ _ := measure_mono fun t ht => subset_toMeasurable volume S
            ⟨by rw [hφsl]; exact h, by rw [hφj, hφsl]; exact abs_le.mpr ht⟩
    -- Symmetrization along `j` creates symmetry under sign changes of the `j`-th coordinate and
    -- keeps the sign-change symmetries already present.
    have hsym : ∀ (j : Fin (n + 1)) (s : Finset (Fin (n + 1))) (A : Set (Rn (n + 1))),
        (∀ x ∈ A, ∀ y : Rn (n + 1), (∀ k, y k = x k ∨ (k ∈ s ∧ y k = -x k)) → y ∈ A) →
        ∀ x ∈ closure (St j A), ∀ y : Rn (n + 1), (∀ k, y k = x k ∨ (k ∈ insert j s ∧ y k = -x k)) →
          y ∈ closure (St j A) := by
      intro j s A hA x hx y hy
      let σ : Rn (n + 1) → Rn (n + 1) := fun z => WithLp.toLp 2 fun k => if y k = x k then z k else -z k
      have hσ : Continuous σ :=
        (PiLp.continuous_toLp 2 _).comp (continuous_pi fun k => by split_ifs <;> fun_prop)
      have hσx : σ x = y := by
        ext k
        change (if y k = x k then x k else -x k) = y k
        split_ifs with h
        exacts [h.symm, ((hy k).resolve_left h).2.symm]
      rw [← hσx]
      refine map_mem_closure hσ hx fun z hz => ?_
      -- the slices of `A` through `z` and `σ z` along `j` agree
      have hsl : {t : ℝ | WithLp.toLp 2 (Function.update (σ z).ofLp j t) ∈ A} =
          {t : ℝ | WithLp.toLp 2 (Function.update z.ofLp j t) ∈ A} := by
        ext t
        constructor <;> intro ht <;> refine hA _ ht _ fun k => ?_
        all_goals
          by_cases hk : k = j
          · subst hk
            simp
          by_cases h : y k = x k
          · simp [σ, Function.update_of_ne hk, h]
          exact Or.inr ⟨(Finset.mem_insert.mp ((hy k).resolve_left h).1).resolve_left hk,
            by simp [σ, Function.update_of_ne hk, h]⟩
      obtain ⟨hne, habs⟩ := hz
      refine ⟨hsl ▸ hne, ?_⟩
      rw [hsl]
      by_cases h : y j = x j <;> simpa [σ, h] using habs
    -- Symmetrize successively in every coordinate.
    have hsteps : ∀ s : Finset (Fin (n + 1)), ∃ M : Set (Rn (n + 1)), IsCompact M ∧ ediam M ≤ ediam A₀ ∧
        volume A₀ ≤ volume M ∧ ∀ x ∈ M, ∀ y : Rn (n + 1), (∀ k, y k = x k ∨ (k ∈ s ∧ y k = -x k)) → y ∈ M := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        refine ⟨A₀, hA₀, le_rfl, le_rfl, fun x hx y hy => ?_⟩
        have : y = x := by
          ext k
          rcases hy k with h | ⟨h, _⟩
          exacts [h, absurd h (Finset.notMem_empty k)]
        exact this ▸ hx
      | insert j s _ ih =>
        obtain ⟨M, hM, hdM, hvM, hsM⟩ := ih
        refine ⟨closure (St j M), (isBounded_iff_ediam_ne_top.mpr (ne_top_of_le_ne_top
          hM.isBounded.ediam_ne_top (hdiam j M))).isCompact_closure, ?_,
          hvM.trans ((hvol j M hM).trans (measure_mono subset_closure)), hsym j s M hsM⟩
        rw [ediam_closure]
        exact (hdiam j M).trans hdM
    obtain ⟨M, hM, hdM, hvM, hsM⟩ := hsteps Finset.univ
    exact ⟨M, hM, hdM, hvM, fun x hx => hsM x hx (-x) fun k => Or.inr ⟨Finset.mem_univ k, rfl⟩⟩
  -- The isodiametric inequality for the closed set `closure f(D)`.
  have hiso : volume (closure (f '' D)) ≤
      Chapter01.realUnitBallVolume ((n + 1 : ℕ) : ℝ) * (ediam (f '' D) / 2) ^ (n + 1) := by
    by_cases hfin : ediam (f '' D) = ∞
    · rw [hfin, ENNReal.top_div_of_ne_top ENNReal.ofNat_ne_top, ENNReal.top_pow n.succ_ne_zero,
        ENNReal.mul_top (Chapter01.realUnitBallVolume_pos (by positivity)).ne']
      exact le_top
    obtain ⟨L, hL, hdL, hvL, hsL⟩ := hrep _ (isBounded_iff_ediam_ne_top.mpr hfin).isCompact_closure
    -- a centrally symmetric set lies in the closed ball of radius `diam / 2` about `0`
    have hLball : L ⊆ closedBall 0 (diam L / 2) := fun x hx => by
      have h := dist_le_diam_of_mem hL.isBounded hx (hsL x hx)
      rw [dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ x, norm_smul, Real.norm_two] at h
      rw [mem_closedBall, dist_zero_right]
      linarith
    calc volume (closure (f '' D)) ≤ volume (closedBall (0 : Rn (n + 1)) (diam L / 2)) :=
          hvL.trans (measure_mono hLball)
      _ = Chapter01.realUnitBallVolume ((n + 1 : ℕ) : ℝ) * (ediam L / 2) ^ (n + 1) := by
        rw [Measure.addHaar_closedBall _ _ (by positivity), finrank_euclideanSpace_fin, hball, mul_comm,
          ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_ofNat, diam,
          ENNReal.ofReal_toReal hL.isBounded.ediam_ne_top]
      _ ≤ _ := by
        gcongr _ * (?_ / 2) ^ _
        exact hdL.trans (ediam_closure _).le
  calc volume (closure (f '' D))
      ≤ Chapter01.realUnitBallVolume ((n + 1 : ℕ) : ℝ) * (ediam (f '' D) / 2) ^ (n + 1) := hiso
    _ ≤ Chapter01.realUnitBallVolume ((n + 1 : ℕ) : ℝ) * (K * ediam D / 2) ^ (n + 1) := by gcongr
    _ = _ := by
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_pow, mul_pow, ENNReal.inv_pow]
      ring

/-- **Simon Ch. 2, proof of Theorem 1.9 (pp. 45–46), one scale of the covering argument.** Put
`s = m + k`. As `0 < r`, the size-`r` premeasure of `E` (the inner infimum of
`hausdorffMeasure_apply`) is at most `μH[s](E) < ∞`, so some cover `C` of `E` has
`ediam (C l) ≤ r` and `∑ (ediam (C l))^s < μH[s](E) + ε`. With `d l = ediam (C l ∩ E)`,
`g = ∑_l (ω_k/2^k) (d l)^k 1_{closure f(C l ∩ E)}` is Borel and dominates `ω_k/2^k` times the
size-`r` premeasure of each fibre `E ∩ f⁻¹{y}`, which is covered by the `C l ∩ E ∩ f⁻¹{y}`.
By `eilenberg_covering_lipschitz_image_volume_le`, `∫ g ≤ ∑_l a (d l)^s ≤ a (μH[s](E) + ε)` with
`a = ω_m ω_k K^m / 2^s`. Simon's `f(C_ij)` is replaced by the closed set `closure f(C l ∩ E)`,
which is Borel without σ-compactness of `X`. -/
theorem Submission.eilenberg_covering_fixed_scale_majorant : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (m : ℕ) (k : ℝ) (E : Set X) (f : X → Rn m) (K : ℝ≥0) (r ε : ℝ≥0∞), 0 < k → μH[(m : ℝ) + k] E < ⊤ → LipschitzOnWith K f E → 0 < r → 0 < ε → ∃ g : Rn m → ℝ≥0∞, Measurable g ∧ (∀ y, Chapter01.realUnitBallVolume k / (2 : ℝ≥0∞) ^ k * (⨅ (t : ℕ → Set X) (_ : E ∩ f ⁻¹' {y} ⊆ ⋃ n, t n) (_ : ∀ n, ediam (t n) ≤ r), ∑' n, ⨆ (_ : (t n).Nonempty), ediam (t n) ^ k) ≤ g y) ∧ ∫⁻ y, g y ∂volume ≤ Chapter01.realUnitBallVolume (m : ℝ) * Chapter01.realUnitBallVolume k * (K : ℝ≥0∞) ^ m / (2 : ℝ≥0∞) ^ ((m : ℝ) + k) * (μH[(m : ℝ) + k] E + ε) := by
  intro X _ _ _ m k E f K r ε hk hE hf hr hε
  have hs : 0 < (m : ℝ) + k := add_pos_of_nonneg_of_pos (Nat.cast_nonneg m) hk
  -- A cover `C` of `E` by sets of diameter `≤ r` with `∑ (ediam (C l))^s < μH[s](E) + ε`.
  have hpre : (⨅ (t : ℕ → Set X) (_ : E ⊆ ⋃ n, t n) (_ : ∀ n, ediam (t n) ≤ r),
      ∑' n, ⨆ (_ : (t n).Nonempty), ediam (t n) ^ ((m : ℝ) + k)) ≤ μH[(m : ℝ) + k] E := by
    rw [Measure.hausdorffMeasure_apply]
    exact le_iSup₂_of_le r hr le_rfl
  have hlt := (ENNReal.lt_add_right (ne_top_of_le_ne_top hE.ne hpre) hε.ne').trans_le
    (add_le_add hpre le_rfl)
  obtain ⟨C, hlt⟩ := iInf_lt_iff.1 hlt
  obtain ⟨hEC, hlt⟩ := iInf_lt_iff.1 hlt
  obtain ⟨hCr, hlt⟩ := iInf_lt_iff.1 hlt
  -- The trimmed pieces `C l ∩ E` still have `∑ (ediam (C l ∩ E))^s ≤ μH[s](E) + ε`.
  have hsum : ∑' l, ediam (C l ∩ E) ^ ((m : ℝ) + k) ≤ μH[(m : ℝ) + k] E + ε := by
    refine le_trans (ENNReal.tsum_le_tsum fun l ↦ ?_) hlt.le
    rcases (C l ∩ E).eq_empty_or_nonempty with h | h
    · rw [h, Metric.ediam_empty, ENNReal.zero_rpow_of_pos hs]
      exact zero_le
    · rw [iSup_pos (h.mono inter_subset_left)]
      exact ENNReal.rpow_le_rpow (Metric.ediam_mono inter_subset_left) hs.le
  -- `(ω_k/2^k) d^k (ω_m K^m d^m / 2^m) = a d^s` for every `d ∈ [0, ∞]`.
  have h2m₀ : (2 : ℝ≥0∞) ^ (m : ℝ) ≠ 0 := (ENNReal.rpow_pos (by norm_num) (by norm_num)).ne'
  have h2m : (2 : ℝ≥0∞) ^ (m : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (Nat.cast_nonneg m) (by norm_num)
  have hexp (d : ℝ≥0∞) : Chapter01.realUnitBallVolume k / 2 ^ k * d ^ k *
      (Chapter01.realUnitBallVolume (m : ℝ) * (K : ℝ≥0∞) ^ m * d ^ m / 2 ^ m) =
      Chapter01.realUnitBallVolume (m : ℝ) * Chapter01.realUnitBallVolume k * (K : ℝ≥0∞) ^ m /
        (2 : ℝ≥0∞) ^ ((m : ℝ) + k) * d ^ ((m : ℝ) + k) := by
    rw [← ENNReal.rpow_natCast d m, ← ENNReal.rpow_natCast 2 m,
      ENNReal.rpow_add_of_nonneg (x := d) _ _ (Nat.cast_nonneg m) hk.le,
      ENNReal.rpow_add (x := 2) _ _ two_ne_zero ENNReal.ofNat_ne_top]
    simp only [div_eq_mul_inv, ENNReal.mul_inv (Or.inl h2m₀) (Or.inl h2m)]
    ring
  refine ⟨fun y ↦ ∑' l, (closure (f '' (C l ∩ E))).indicator
      (fun _ ↦ Chapter01.realUnitBallVolume k / 2 ^ k * ediam (C l ∩ E) ^ k) y,
    Measurable.tsum fun l ↦ measurable_const.indicator isClosed_closure.measurableSet,
    fun y ↦ ?_, ?_⟩
  · -- The pieces `C l ∩ E ∩ f⁻¹{y}` form an admissible cover of the fibre.
    have hcov : E ∩ f ⁻¹' {y} ⊆ ⋃ l, C l ∩ E ∩ f ⁻¹' {y} := by
      rintro x ⟨hxE, hxy⟩
      obtain ⟨l, hl⟩ := mem_iUnion.1 (hEC hxE)
      exact mem_iUnion.2 ⟨l, ⟨hl, hxE⟩, hxy⟩
    have hdiam (l : ℕ) : ediam (C l ∩ E ∩ f ⁻¹' {y}) ≤ r :=
      (Metric.ediam_mono (inter_subset_left.trans inter_subset_left)).trans (hCr l)
    calc _ ≤ Chapter01.realUnitBallVolume k / 2 ^ k * ∑' l,
          ⨆ (_ : (C l ∩ E ∩ f ⁻¹' {y}).Nonempty), ediam (C l ∩ E ∩ f ⁻¹' {y}) ^ k := by
          gcongr Chapter01.realUnitBallVolume k / 2 ^ k * ?_
          exact iInf₂_le_of_le (fun l ↦ C l ∩ E ∩ f ⁻¹' {y}) hcov (iInf_le_of_le hdiam le_rfl)
      _ = ∑' l, Chapter01.realUnitBallVolume k / 2 ^ k *
          ⨆ (_ : (C l ∩ E ∩ f ⁻¹' {y}).Nonempty), ediam (C l ∩ E ∩ f ⁻¹' {y}) ^ k :=
          ENNReal.tsum_mul_left.symm
      _ ≤ _ := ENNReal.tsum_le_tsum fun l ↦ ?_
    rcases (C l ∩ E ∩ f ⁻¹' {y}).eq_empty_or_nonempty with h | h
    · simp [h]
    · have hy : y ∈ closure (f '' (C l ∩ E)) := by
        obtain ⟨x, hxD, hxy⟩ := h
        exact subset_closure ⟨x, hxD, hxy⟩
      rw [iSup_pos h, indicator_of_mem hy]
      gcongr Chapter01.realUnitBallVolume k / 2 ^ k * ?_
      exact ENNReal.rpow_le_rpow (Metric.ediam_mono inter_subset_left) hk.le
  · -- `∫ g = ∑ (ω_k/2^k) (d l)^k Lᵐ(closure f(C l ∩ E)) ≤ ∑ a (d l)^s ≤ a (μH[s](E) + ε)`.
    rw [lintegral_tsum fun l ↦
      (measurable_const.indicator isClosed_closure.measurableSet).aemeasurable]
    calc _ ≤ ∑' l, Chapter01.realUnitBallVolume (m : ℝ) * Chapter01.realUnitBallVolume k *
          (K : ℝ≥0∞) ^ m / (2 : ℝ≥0∞) ^ ((m : ℝ) + k) * ediam (C l ∩ E) ^ ((m : ℝ) + k) := by
          refine ENNReal.tsum_le_tsum fun l ↦ ?_
          rw [lintegral_indicator_const isClosed_closure.measurableSet, ← hexp]
          gcongr
          exact Submission.eilenberg_covering_lipschitz_image_volume_le X m (C l ∩ E) f K
            (hf.mono inter_subset_right)
      _ = Chapter01.realUnitBallVolume (m : ℝ) * Chapter01.realUnitBallVolume k *
          (K : ℝ≥0∞) ^ m / (2 : ℝ≥0∞) ^ ((m : ℝ) + k) *
          ∑' l, ediam (C l ∩ E) ^ ((m : ℝ) + k) := ENNReal.tsum_mul_left
      _ ≤ _ := by gcongr
/-- **Simon Ch. 2, proof of Theorem 1.9 (p. 46), limiting step**, with an explicit Borel majorant
in place of the upper integral. If `c` times the `r i`-scale Hausdorff pre-measure of `F y` is
bounded by measurable `g i y`, `∫⁻ g i ∂ν ≤ b i`, `r i → 0` and `b i → L`, then
`G = liminf g i` is a measurable majorant of `c * μH[d] (F y)` with `∫⁻ G ∂ν ≤ L` (Fatou). -/
theorem Submission.eilenberg_covering_liminf_majorant : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (Y : Type) [MeasurableSpace Y] (ν : Measure Y) (d : ℝ) (c : ℝ≥0∞) (F : Y → Set X) (r : ℕ → ℝ≥0∞) (g : ℕ → Y → ℝ≥0∞) (b : ℕ → ℝ≥0∞) (L : ℝ≥0∞), Tendsto r atTop (𝓝 0) → (∀ i, Measurable (g i)) → (∀ (i : ℕ) (y : Y), c * (⨅ (t : ℕ → Set X) (_ : F y ⊆ ⋃ n, t n) (_ : ∀ n, ediam (t n) ≤ r i), ∑' n, ⨆ (_ : (t n).Nonempty), ediam (t n) ^ d) ≤ g i y) → (∀ i, ∫⁻ y, g i y ∂ν ≤ b i) → Tendsto b atTop (𝓝 L) → ∃ G : Y → ℝ≥0∞, Measurable G ∧ (∀ y, c * μH[d] (F y) ≤ G y) ∧ ∫⁻ y, G y ∂ν ≤ L := by
  intro X _ _ _ Y _ ν d c F r g b L hr hg hcov hint hb
  refine ⟨fun y ↦ liminf (fun i ↦ g i y) atTop, Measurable.liminf hg, fun y ↦ ?_, ?_⟩
  · -- At each scale `R > 0`, eventually `r i ≤ R`, and covers at scale `r i` are admissible at `R`.
    rw [Measure.hausdorffMeasure_apply, ENNReal.mul_iSup]
    refine iSup_le fun R ↦ ?_
    rw [ENNReal.mul_iSup]
    refine iSup_le fun hR ↦ le_liminf_of_le (by isBoundedDefault) ?_
    filter_upwards [hr.eventually_le_const hR] with i hi
    refine le_trans ?_ (hcov i y)
    gcongr c * ?_
    exact le_iInf fun t ↦ le_iInf fun ht ↦ le_iInf fun htr ↦
      iInf₂_le_of_le t ht (iInf_le_of_le (fun n ↦ (htr n).trans hi) le_rfl)
  · -- Fatou's lemma, then `∫⁻ g i ∂ν ≤ b i → L`.
    calc ∫⁻ y, liminf (fun i ↦ g i y) atTop ∂ν
        ≤ liminf (fun i ↦ ∫⁻ y, g i y ∂ν) atTop := lintegral_liminf_le hg
      _ ≤ liminf b atTop := liminf_le_liminf (Eventually.of_forall hint)
      _ = L := hb.liminf_eq
/-- **Simon Ch. 2, Theorem 1.9 (p. 45), measurability of `y ↦ Hᵏ(A ∩ f⁻¹y)`**: for compact `F`
and `k > 0`, `μH[k](F)` is the supremum over `n` of the finite open-cover content of `F` at scale
`(n + 1)⁻¹`. Padding a finite open cover by `∅` bounds the fixed-scale precontent of
`hausdorffMeasure_apply` by the open content at the same scale. Conversely, thickening each set of
a near-optimal countable cover at scale `δ / 2` by a radius `ηₙ > 0` with `2ηₙ < δ / 2` and cost
`eₙ` (`∑ eₙ < ε / 2`), then extracting a finite subcover by compactness, bounds the open content
at scale `δ` by the precontent at scale `δ / 2` plus `ε`. -/
theorem Submission.eilenberg_compact_hausdorff_eq_iSup_open_content : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (k : ℝ) (F : Set X), 0 < k → IsCompact F → MeasureTheory.Measure.hausdorffMeasure k F = ⨆ n : ℕ, ⨅ (I : Finset ℕ) (O : ℕ → Set X) (_ : ∀ i ∈ I, IsOpen (O i) ∧ Metric.ediam (O i) < ((n : ℝ≥0∞) + 1)⁻¹) (_ : F ⊆ ⋃ i ∈ I, O i), ∑ i ∈ I, Metric.ediam (O i) ^ k := by
  intro X _ _ _ k F hk hF
  -- Step 1: the fixed-scale precontent of `hausdorffMeasure_apply` is antitone in the scale.
  have hmono : ∀ r r' : ℝ≥0∞, r ≤ r' →
      (⨅ (t : ℕ → Set X) (_ : F ⊆ ⋃ n, t n) (_ : ∀ n, ediam (t n) ≤ r'),
        ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ k) ≤
      ⨅ (t : ℕ → Set X) (_ : F ⊆ ⋃ n, t n) (_ : ∀ n, ediam (t n) ≤ r),
        ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ k := fun r r' h =>
    iInf_mono fun t => iInf_mono fun _ => iInf_mono' fun ht => ⟨fun n => (ht n).trans h, le_rfl⟩
  -- Step 2: padding a finite open cover by `∅` shows precontent ≤ open content.
  have hpre_le : ∀ δ : ℝ≥0∞,
      (⨅ (t : ℕ → Set X) (_ : F ⊆ ⋃ n, t n) (_ : ∀ n, ediam (t n) ≤ δ),
        ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ k) ≤
      ⨅ (I : Finset ℕ) (O : ℕ → Set X) (_ : ∀ i ∈ I, IsOpen (O i) ∧ ediam (O i) < δ)
        (_ : F ⊆ ⋃ i ∈ I, O i), ∑ i ∈ I, ediam (O i) ^ k := by
    intro δ
    refine le_iInf fun I => le_iInf fun O => le_iInf fun hO => le_iInf fun hcov => ?_
    set t : ℕ → Set X := fun n => if n ∈ I then O n else ∅
    have htcov : F ⊆ ⋃ n, t n := by
      intro x hx
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (hcov hx)
      exact mem_iUnion.2 ⟨i, by simp [t, hi, hxi]⟩
    have htdiam : ∀ n, ediam (t n) ≤ δ := by
      intro n
      by_cases hn : n ∈ I
      · simpa only [t, hn, ite_true] using (hO n hn).2.le
      · simp [t, hn]
    calc _ ≤ ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ k :=
          iInf_le_of_le t (iInf_le_of_le htcov (iInf_le_of_le htdiam le_rfl))
      _ = ∑ n ∈ I, ⨆ _ : (t n).Nonempty, ediam (t n) ^ k :=
          tsum_eq_sum fun n hn => by simp [t, hn]
      _ ≤ ∑ n ∈ I, ediam (O n) ^ k :=
          Finset.sum_le_sum fun n hn => iSup_le fun _ => by simp [t, hn]
  -- Step 3: thickening a near-optimal countable cover at scale `δ/2` and extracting a finite
  -- subcover by compactness shows open content at scale `δ` ≤ precontent at scale `δ/2`.
  have hle_pre : ∀ δ : ℝ≥0∞, 0 < δ → δ ≠ ∞ →
      (⨅ (I : Finset ℕ) (O : ℕ → Set X) (_ : ∀ i ∈ I, IsOpen (O i) ∧ ediam (O i) < δ)
        (_ : F ⊆ ⋃ i ∈ I, O i), ∑ i ∈ I, ediam (O i) ^ k) ≤
      ⨅ (t : ℕ → Set X) (_ : F ⊆ ⋃ n, t n) (_ : ∀ n, ediam (t n) ≤ δ / 2),
        ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ k := by
    intro δ hδpos hδ
    have hδ2 : δ / 2 ≠ ∞ := ENNReal.div_ne_top hδ two_ne_zero
    have hδ2pos : 0 < δ / 2 := ENNReal.half_pos hδpos.ne'
    refine ENNReal.le_of_forall_pos_le_add fun ε hε hlt => ?_
    have hε2 : (ε : ℝ≥0∞) / 2 ≠ 0 := (ENNReal.half_pos (by exact_mod_cast hε.ne')).ne'
    obtain ⟨C, hCcov, hCdiam, hCsum⟩ : ∃ C : ℕ → Set X, F ⊆ ⋃ n, C n ∧
        (∀ n, ediam (C n) ≤ δ / 2) ∧
        ∑' n, ⨆ _ : (C n).Nonempty, ediam (C n) ^ k <
          (⨅ (t : ℕ → Set X) (_ : F ⊆ ⋃ n, t n) (_ : ∀ n, ediam (t n) ≤ δ / 2),
            ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ k) + ε / 2 := by
      have := ENNReal.lt_add_right hlt.ne hε2
      simpa only [iInf_lt_iff, exists_prop] using this
    obtain ⟨e, he0, hesum⟩ := ENNReal.exists_pos_sum_of_countable' hε2 ℕ
    have hη : ∀ n, ∃ η : ℝ≥0, 0 < η ∧ 2 * (η : ℝ≥0∞) < δ / 2 ∧
        (ediam (C n) + 2 * η) ^ k < ediam (C n) ^ k + e n := by
      intro n
      have hfin : ediam (C n) ^ k ≠ ∞ :=
        ENNReal.rpow_ne_top_of_nonneg hk.le (ne_top_of_le_ne_top hδ2 (hCdiam n))
      have hc1 : Continuous fun η : ℝ≥0 => 2 * (η : ℝ≥0∞) :=
        (ENNReal.continuous_const_mul (by norm_num)).comp ENNReal.continuous_coe
      have hc2 : Continuous fun η : ℝ≥0 => (ediam (C n) + 2 * (η : ℝ≥0∞)) ^ k :=
        ENNReal.continuous_rpow_const.comp (continuous_const.add hc1)
      have h1 : ∀ᶠ η : ℝ≥0 in 𝓝 0, 2 * (η : ℝ≥0∞) < δ / 2 :=
        (hc1.tendsto 0).eventually_lt_const (by simpa using hδ2pos)
      have h2 : ∀ᶠ η : ℝ≥0 in 𝓝 0, (ediam (C n) + 2 * (η : ℝ≥0∞)) ^ k < ediam (C n) ^ k + e n :=
        (hc2.tendsto 0).eventually_lt_const
          (by simpa using ENNReal.lt_add_right hfin (he0 n).ne')
      obtain ⟨η, ⟨hη1, hη2⟩, hη0⟩ :=
        (((h1.and h2).filter_mono nhdsWithin_le_nhds).and
          (eventually_mem_nhdsWithin (s := Ioi (0 : ℝ≥0)) (a := 0))).exists
      exact ⟨η, hη0, hη1, hη2⟩
    choose η hη0 hη1 hη2 using hη
    set O : ℕ → Set X := fun n => thickening (η n : ℝ) (C n)
    have hOdiam : ∀ n, ediam (O n) < δ := fun n =>
      calc ediam (O n) ≤ ediam (C n) + 2 * η n := ediam_thickening_le _
        _ ≤ δ / 2 + 2 * η n := add_le_add (hCdiam n) le_rfl
        _ < δ / 2 + δ / 2 := ENNReal.add_lt_add_left hδ2 (hη1 n)
        _ = δ := ENNReal.add_halves δ
    have hcost : ∀ n, ediam (O n) ^ k ≤ (⨆ _ : (C n).Nonempty, ediam (C n) ^ k) + e n := by
      intro n
      rcases (C n).eq_empty_or_nonempty with hC | hC
      · simp [O, hC, ENNReal.zero_rpow_of_pos hk]
      · rw [iSup_pos hC]
        calc ediam (O n) ^ k ≤ (ediam (C n) + 2 * η n) ^ k :=
              ENNReal.rpow_le_rpow (ediam_thickening_le _) hk.le
          _ ≤ ediam (C n) ^ k + e n := (hη2 n).le
    obtain ⟨I, hI⟩ := hF.elim_finite_subcover O (fun n => isOpen_thickening)
      (hCcov.trans (iUnion_mono fun n =>
        self_subset_thickening (by exact_mod_cast hη0 n) (C n)))
    calc (⨅ (I : Finset ℕ) (O : ℕ → Set X) (_ : ∀ i ∈ I, IsOpen (O i) ∧ ediam (O i) < δ)
          (_ : F ⊆ ⋃ i ∈ I, O i), ∑ i ∈ I, ediam (O i) ^ k)
        ≤ ∑ i ∈ I, ediam (O i) ^ k :=
          iInf_le_of_le I (iInf_le_of_le O (iInf_le_of_le
            (fun i _ => ⟨isOpen_thickening, hOdiam i⟩) (iInf_le_of_le hI le_rfl)))
      _ ≤ ∑ i ∈ I, ((⨆ _ : (C i).Nonempty, ediam (C i) ^ k) + e i) :=
          Finset.sum_le_sum fun i _ => hcost i
      _ ≤ ∑' i, ((⨆ _ : (C i).Nonempty, ediam (C i) ^ k) + e i) := ENNReal.sum_le_tsum I
      _ = (∑' i, ⨆ _ : (C i).Nonempty, ediam (C i) ^ k) + ∑' i, e i := ENNReal.tsum_add
      _ ≤ ((⨅ (t : ℕ → Set X) (_ : F ⊆ ⋃ n, t n) (_ : ∀ n, ediam (t n) ≤ δ / 2),
            ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ k) + ε / 2) + ε / 2 :=
          add_le_add hCsum.le hesum.le
      _ = _ := by rw [add_assoc, ENNReal.add_halves]
  -- Step 4: compare both sides along the scales `(n + 1)⁻¹`.
  rw [Measure.hausdorffMeasure_apply]
  apply le_antisymm
  · refine iSup₂_le fun r hr => ?_
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hr.ne'
    have hnr : ((n : ℝ≥0∞) + 1)⁻¹ ≤ r := (ENNReal.inv_le_inv' le_self_add).trans hn.le
    exact (hmono _ _ hnr).trans ((hpre_le _).trans (le_iSup (fun m : ℕ =>
      ⨅ (I : Finset ℕ) (O : ℕ → Set X)
        (_ : ∀ i ∈ I, IsOpen (O i) ∧ ediam (O i) < ((m : ℝ≥0∞) + 1)⁻¹)
        (_ : F ⊆ ⋃ i ∈ I, O i), ∑ i ∈ I, ediam (O i) ^ k) n))
  · refine iSup_le fun n => ?_
    have hpos : 0 < ((n : ℝ≥0∞) + 1)⁻¹ := ENNReal.inv_pos.2 (by simp)
    have hne : ((n : ℝ≥0∞) + 1)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (by simp)
    exact (hle_pre _ hpos hne).trans
      (le_iSup₂_of_le (((n : ℝ≥0∞) + 1)⁻¹ / 2) (ENNReal.half_pos hpos.ne') le_rfl)
/-- **Simon Ch. 2, Theorem 1.9 (p. 45), measurability of `y ↦ Hᵏ(A ∩ f⁻¹y)`**: upper
semicontinuity of the finite open-cover content of the fibres `Q ∩ f⁻¹{y}`, for compact `Q` and
`f` continuous on `Q`. A cover `(I, O)` of the fibre over `y₀` with sum `< t` has open union `W`;
`f '' (Q \ W)` is compact, hence closed, and misses `y₀`, and off it the same cover still covers
the fibre. -/
theorem Submission.eilenberg_fiber_open_content_upperSemicontinuous : ∀ (X : Type) [MetricSpace X] (m : ℕ) (k : ℝ) (δ : ℝ≥0∞) (Q : Set X) (f : X → Rn m), IsCompact Q → ContinuousOn f Q → UpperSemicontinuous (fun y : Rn m ↦ ⨅ (I : Finset ℕ) (O : ℕ → Set X) (_ : ∀ i ∈ I, IsOpen (O i) ∧ Metric.ediam (O i) < δ) (_ : Q ∩ f ⁻¹' {y} ⊆ ⋃ i ∈ I, O i), ∑ i ∈ I, Metric.ediam (O i) ^ k) := by
  intro X _ m k δ Q f hQ hf y₀ t ht
  simp only [iInf_lt_iff] at ht
  obtain ⟨I, O, hO, hcov, hS⟩ := ht
  have hW : IsOpen (⋃ i ∈ I, O i) := isOpen_biUnion fun i hi ↦ (hO i hi).1
  have hK : IsClosed (f '' (Q \ ⋃ i ∈ I, O i)) :=
    ((hQ.diff hW).image_of_continuousOn (hf.mono sdiff_subset)).isClosed
  have hy₀ : y₀ ∈ (f '' (Q \ ⋃ i ∈ I, O i))ᶜ := by
    rintro ⟨x, ⟨hxQ, hxW⟩, rfl⟩
    exact hxW (hcov ⟨hxQ, rfl⟩)
  filter_upwards [hK.isOpen_compl.mem_nhds hy₀] with y hy
  -- Off `f '' (Q \ W)` the fibre over `y` lies in `W`, so `(I, O)` stays admissible.
  have hcov' : Q ∩ f ⁻¹' {y} ⊆ ⋃ i ∈ I, O i := fun x ⟨hxQ, hxy⟩ ↦
    by_contra fun hxW ↦ hy ⟨x, ⟨hxQ, hxW⟩, hxy⟩
  exact lt_of_le_of_lt (iInf_le_of_le I <| iInf_le_of_le O <| iInf_le_of_le hO <|
    iInf_le_of_le hcov' le_rfl) hS

/-- **Simon Ch. 2, Theorem 1.9 (pp. 45–46), measurability of `y ↦ Hᵏ(A ∩ f⁻¹y)`**, for compact
`A = Q` (Simon leaves this measurability as an exercise). For `f` continuous on `Q` every fibre
`Q ∩ f⁻¹{y}` is compact, so its `μH[k]` is the countable supremum over `n` of its finite open-cover
contents at scale `(n + 1)⁻¹` (`eilenberg_compact_hausdorff_eq_iSup_open_content`). Each content is
upper semicontinuous in `y` (`eilenberg_fiber_open_content_upperSemicontinuous`), hence Borel, and
`𝓗[k] = (ω_k / 2^k) • μH[k]`. -/
theorem Submission.eilenberg_compact_fiber_measurable : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (m : ℕ) (k : ℝ) (Q : Set X) (f : X → Rn m), 0 < k → IsCompact Q → ContinuousOn f Q → Measurable (fun y ↦ Chapter01.simonHausdorffMeasureReal k (Q ∩ f ⁻¹' {y})) := by
  intro X _ _ _ m k Q f hk hQ hf
  -- Each fibre is a closed subset of the compact set `Q`, hence compact.
  have hfib (y : Rn m) : IsCompact (Q ∩ f ⁻¹' {y}) :=
    hQ.of_isClosed_subset (hf.preimage_isClosed_of_isClosed hQ.isClosed isClosed_singleton)
      inter_subset_left
  have hμ : Measurable fun y : Rn m ↦ μH[k] (Q ∩ f ⁻¹' {y}) := by
    simp_rw [fun y ↦ Submission.eilenberg_compact_hausdorff_eq_iSup_open_content X k _ hk (hfib y)]
    exact Measurable.iSup fun n ↦
      (Submission.eilenberg_fiber_open_content_upperSemicontinuous X m k _ Q f hQ hf).measurable
  simp only [Chapter01.simonHausdorffMeasureReal, Measure.smul_apply, smul_eq_mul]
  exact hμ.const_mul _
/-- **Simon Ch. 2, proof of Theorem 1.8(i) (p. 45), compact exhaustion**, as used for Theorem 1.9.
In a σ-compact metric space, a `μ`-null-measurable `A` with `μ A < ∞` contains increasing compact
`Q j` with `μ (A \ ⋃ j, Q j) = 0`. A Borel kernel `B ⊆ A`, `B =ᵐ[μ] A`, carries the finite, hence
regular, measure `μ.restrict B`; it gives compact `K j ⊆ B` with `μ (B \ K j) < j⁻¹`, and
`Q = accumulate K` collects their finite unions. -/
theorem Submission.eilenberg_compact_exhaustion : ∀ (X : Type) [MetricSpace X] [SigmaCompactSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) (A : Set X), NullMeasurableSet A μ → μ A < ⊤ → ∃ Q : ℕ → Set X, (∀ j, IsCompact (Q j)) ∧ (∀ j, Q j ⊆ A) ∧ Monotone Q ∧ μ (A \ ⋃ j, Q j) = 0 := by
  intro X _ _ _ _ μ A hA hAfin
  obtain ⟨B, hBA, hB, hBae⟩ := hA.exists_measurable_subset_ae_eq
  have : IsFiniteMeasure (μ.restrict B) :=
    isFiniteMeasure_restrict.2 ((measure_mono hBA).trans_lt hAfin).ne
  have hK (j : ℕ) : ∃ K, K ⊆ B ∧ IsCompact K ∧ μ.restrict B (B \ K) < (j : ℝ≥0∞)⁻¹ :=
    hB.exists_isCompact_sdiff_lt (measure_ne_top _ _)
      (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top j))
  choose K hKB hKc hKlt using hK
  refine ⟨accumulate K, isCompact_accumulate hKc,
    fun j ↦ (accumulate_subset_iUnion j).trans ((iUnion_subset hKB).trans hBA),
    monotone_accumulate, ?_⟩
  -- `B \ ⋃ j, K j` is null, its measure being below every `j⁻¹`.
  have hnull : μ (B \ ⋃ j, K j) = 0 := by
    by_contra h
    obtain ⟨j, hj⟩ := ENNReal.exists_inv_nat_lt h
    have hle : μ (B \ ⋃ j, K j) ≤ μ.restrict B (B \ K j) := by
      rw [Measure.restrict_eq_self μ sdiff_subset]
      exact measure_mono (sdiff_subset_sdiff_right (subset_iUnion K j))
    exact lt_asymm hj (hle.trans_lt (hKlt j))
  rw [iUnion_accumulate]
  refine measure_mono_null (fun x hx ↦ ?_) (measure_union_null (ae_eq_set.1 hBae).2 hnull)
  by_cases hxB : x ∈ B
  exacts [Or.inr ⟨hxB, hx.2⟩, Or.inl ⟨hx.1, hxB⟩]
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
/-- **Level-set (Markov) step of Simon 2.7.** Let `U ⊆ ℝⁿ` be measurable, `u` a.e.-measurable on
`U`, `θ > 0`, and let `β, c` be constants with
`θ Lⁿ(U) ≤ min {Lⁿ{x ∈ U : u ≥ β}, Lⁿ{x ∈ U : u ≤ β}}` (outer measures; the level sets need not be
measurable). Then `∫_U |u - β| ≤ (1 + θ⁻¹) ∫_U |u - c|` in `[0, ∞]`. Write `I = ∫_U |u - c|` and
`a = |c - β|`. The triangle inequality gives `∫_U |u - β| ≤ I + a Lⁿ(U)`. The level set `{u ≥ β}`
(if `c ≤ β`) or `{u ≤ β}` (if `β < c`) lies in `{|u - c| ≥ a}`, so Markov's inequality
(`mul_meas_ge_le_lintegral₀`) gives `a θ Lⁿ(U) ≤ I`; multiplying by `θ⁻¹` gives `a Lⁿ(U) ≤ θ⁻¹ I`. -/
theorem Submission.poincare_level_set_lintegral_le : ∀ (n : ℕ) (U : Set (Rn n)) (u : Rn n → ℝ) (θ β c : ℝ), MeasurableSet U → AEMeasurable u (volume.restrict U) → 0 < θ → ENNReal.ofReal θ * volume U ≤ min (volume {x ∈ U | β ≤ u x}) (volume {x ∈ U | u x ≤ β}) → ∫⁻ x in U, ‖u x - β‖ₑ ≤ ENNReal.ofReal (1 + θ⁻¹) * ∫⁻ x in U, ‖u x - c‖ₑ := by
  intro n U u θ β c hU hu hθ hlev
  -- Step 1: integrate `‖u x - β‖ₑ ≤ ‖u x - c‖ₑ + ‖c - β‖ₑ` over `U`.
  have h1 : ∫⁻ x in U, ‖u x - β‖ₑ ≤ (∫⁻ x in U, ‖u x - c‖ₑ) + ‖c - β‖ₑ * volume U :=
    calc ∫⁻ x in U, ‖u x - β‖ₑ ≤ ∫⁻ x in U, (‖u x - c‖ₑ + ‖c - β‖ₑ) :=
          lintegral_mono fun x ↦ by
            simpa only [sub_add_sub_cancel] using enorm_add_le (u x - c) (c - β)
      _ = (∫⁻ x in U, ‖u x - c‖ₑ) + ‖c - β‖ₑ * volume U := by
          rw [lintegral_add_right _ measurable_const, setLIntegral_const]
  -- Step 2: the relevant level set lies in `{‖c - β‖ₑ ≤ ‖u - c‖ₑ}`; apply Markov on `U`.
  have hlevel : ENNReal.ofReal θ * volume U ≤ volume ({x | ‖c - β‖ₑ ≤ ‖u x - c‖ₑ} ∩ U) := by
    rcases le_or_gt c β with hcb | hbc
    · -- (a) `c ≤ β`: if `β ≤ u x` then `|u x - c| ≥ β - c = |c - β|`.
      have hsub : {x ∈ U | β ≤ u x} ⊆ {x | ‖c - β‖ₑ ≤ ‖u x - c‖ₑ} ∩ U := fun x hx ↦ by
        refine ⟨?_, hx.1⟩
        show ‖c - β‖ₑ ≤ ‖u x - c‖ₑ
        rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, abs_sub_comm c β,
          abs_of_nonneg (sub_nonneg.2 hcb)]
        exact ENNReal.ofReal_le_ofReal (by linarith [hx.2, le_abs_self (u x - c)])
      exact (hlev.trans (min_le_left _ _)).trans (measure_mono hsub)
    · -- (b) `β < c`: if `u x ≤ β` then `|u x - c| ≥ c - β = |c - β|`.
      have hsub : {x ∈ U | u x ≤ β} ⊆ {x | ‖c - β‖ₑ ≤ ‖u x - c‖ₑ} ∩ U := fun x hx ↦ by
        refine ⟨?_, hx.1⟩
        show ‖c - β‖ₑ ≤ ‖u x - c‖ₑ
        rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, abs_of_pos (sub_pos.2 hbc)]
        exact ENNReal.ofReal_le_ofReal (by linarith [hx.2, neg_le_abs (u x - c)])
      exact (hlev.trans (min_le_right _ _)).trans (measure_mono hsub)
  have h2 : ‖c - β‖ₑ * (ENNReal.ofReal θ * volume U) ≤ ∫⁻ x in U, ‖u x - c‖ₑ :=
    calc ‖c - β‖ₑ * (ENNReal.ofReal θ * volume U)
        ≤ ‖c - β‖ₑ * volume ({x | ‖c - β‖ₑ ≤ ‖u x - c‖ₑ} ∩ U) := by gcongr
      _ = ‖c - β‖ₑ * (volume.restrict U) {x | ‖c - β‖ₑ ≤ ‖u x - c‖ₑ} := by
          rw [Measure.restrict_apply' hU]
      _ ≤ ∫⁻ x in U, ‖u x - c‖ₑ := mul_meas_ge_le_lintegral₀ (hu.sub_const c).enorm _
  -- Step 3: multiply by `ofReal θ⁻¹`, using `ofReal θ⁻¹ * ofReal θ = 1`.
  have hinv : ENNReal.ofReal θ⁻¹ * ENNReal.ofReal θ = 1 := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hθ.le), inv_mul_cancel₀ hθ.ne', ENNReal.ofReal_one]
  have h3 : ‖c - β‖ₑ * volume U ≤ ENNReal.ofReal θ⁻¹ * ∫⁻ x in U, ‖u x - c‖ₑ :=
    calc ‖c - β‖ₑ * volume U
        = ENNReal.ofReal θ⁻¹ * ENNReal.ofReal θ * (‖c - β‖ₑ * volume U) := by
          rw [hinv, one_mul]
      _ = ENNReal.ofReal θ⁻¹ * (‖c - β‖ₑ * (ENNReal.ofReal θ * volume U)) := by ring
      _ ≤ ENNReal.ofReal θ⁻¹ * ∫⁻ x in U, ‖u x - c‖ₑ := by gcongr
  -- Step 4: `I + ofReal θ⁻¹ * I = ofReal (1 + θ⁻¹) * I`.
  calc ∫⁻ x in U, ‖u x - β‖ₑ ≤ (∫⁻ x in U, ‖u x - c‖ₑ) + ‖c - β‖ₑ * volume U := h1
    _ ≤ (∫⁻ x in U, ‖u x - c‖ₑ) + ENNReal.ofReal θ⁻¹ * ∫⁻ x in U, ‖u x - c‖ₑ := by gcongr
    _ = ENNReal.ofReal (1 + θ⁻¹) * ∫⁻ x in U, ‖u x - c‖ₑ := by
        rw [ENNReal.ofReal_add zero_le_one (inv_nonneg.2 hθ.le), ENNReal.ofReal_one, add_mul,
          one_mul]
/-- **Poincaré inequality for `C¹` functions on bounded convex open sets** (step B1 of the proof of
Simon 2.7, "the usual Poincaré inequality for smooth functions"). If `O ⊆ ℝⁿ` is open, bounded and
convex and `w` is `C¹`, then `∫_O |w - w̄| ≤ 2ⁿ diam(O) ∫_O |Dw|`, where `w̄` is the mean of `w` over
`O`. For `x, y ∈ O` the fundamental theorem of calculus along the segment gives
`|w(x) - w(y)| ≤ diam(O) ∫₀¹ |Dw(x + t(y - x))| dt`. After Tonelli, the dilation `y ↦ (1 - t)x + ty`
(for `t ≥ 1/2`) or `x ↦ (1 - t)x + ty` (for `t < 1/2`) costs a factor at most `2ⁿ`
(`Measure.map_addHaar_smul`), and averaging over `y` bounds `|w(x) - w̄|`. -/
theorem Submission.convex_poincare_smooth_lintegral_le : ∀ (n : ℕ) (O : Set (Rn n)) (w : Rn n → ℝ), IsOpen O → Bornology.IsBounded O → Convex ℝ O → ContDiff ℝ 1 w → ∫⁻ x in O, ‖w x - (volume O).toReal⁻¹ * ∫ y in O, w y‖ₑ ≤ ENNReal.ofReal (2 ^ n * Metric.diam O) * ∫⁻ x in O, ‖fderiv ℝ w x‖ₑ := by
  intro n O w hO hOb hOc hw
  -- Step 1: the case `O = ∅` is trivial.
  rcases O.eq_empty_or_nonempty with rfl | hne
  · simp
  -- Step 3: dilation identity `∫⁻ F(a + s•y) dy = ofReal((sⁿ)⁻¹) ∫⁻ F`.
  have dil : ∀ (F : Rn n → ℝ≥0∞) (a : Rn n) (s : ℝ), 0 < s →
      ∫⁻ y, F (a + s • y) = ENNReal.ofReal ((s ^ n)⁻¹) * ∫⁻ y, F y := by
    intro F a s hs
    have hmap := Measure.map_addHaar_smul (volume : Measure (Rn n)) hs.ne'
    rw [finrank_euclideanSpace_fin, abs_of_pos (inv_pos.mpr (pow_pos hs n))] at hmap
    have hemb : MeasurableEmbedding (fun y : Rn n ↦ s • y) :=
      (Homeomorph.smulOfNeZero s hs.ne').measurableEmbedding
    calc ∫⁻ y, F (a + s • y)
          = ∫⁻ z, F (a + z) ∂(Measure.map (fun y : Rn n ↦ s • y) volume) := by
          rw [hemb.lintegral_map]
      _ = ENNReal.ofReal ((s ^ n)⁻¹) * ∫⁻ z, F (a + z) := by
          rw [hmap, lintegral_smul_measure]; rfl
      _ = ENNReal.ofReal ((s ^ n)⁻¹) * ∫⁻ y, F y := by
          rw [lintegral_add_left_eq_self]
  have half : ∀ s : ℝ, 1 / 2 ≤ s → ENNReal.ofReal ((s ^ n)⁻¹) ≤ 2 ^ n := by
    intro s hs
    have hs0 : 0 < s := by linarith
    have h1 : s⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hs0 (by norm_num)]; linarith
    calc ENNReal.ofReal ((s ^ n)⁻¹) ≤ ENNReal.ofReal (2 ^ n) := by
          apply ENNReal.ofReal_le_ofReal
          rw [← inv_pow]
          exact pow_le_pow_left₀ (inv_nonneg.mpr hs0.le) h1 n
      _ = 2 ^ n := by rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  -- Step 4 (first half): FTC along the segment.
  have seg : ∀ x y : Rn n, ‖w x - w y‖ₑ
      ≤ ∫⁻ t in Ioc (0:ℝ) 1, ‖fderiv ℝ w (x + t • (y - x))‖ₑ * ‖y - x‖ₑ := by
    intro x y
    have hdiff : Differentiable ℝ w := hw.differentiable one_ne_zero
    have hderiv : ∀ t ∈ uIcc (0:ℝ) 1, HasDerivAt (fun t : ℝ ↦ w (x + t • (y - x)))
        (fderiv ℝ w (x + t • (y - x)) (y - x)) t := by
      intro t _
      have hg : HasDerivAt (fun t : ℝ ↦ x + t • (y - x)) (y - x) t := by
        simpa using ((hasDerivAt_id t).smul_const (y - x)).const_add x
      exact (hdiff _).hasFDerivAt.comp_hasDerivAt t hg
    have hint : IntervalIntegrable (fun t : ℝ ↦ fderiv ℝ w (x + t • (y - x)) (y - x))
        volume 0 1 := by
      have hcont : Continuous (fun z ↦ fderiv ℝ w z) := hw.continuous_fderiv one_ne_zero
      apply Continuous.intervalIntegrable
      fun_prop
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    rw [intervalIntegral.integral_of_le zero_le_one] at hftc
    simp only [zero_smul, add_zero, one_smul, add_sub_cancel] at hftc
    calc ‖w x - w y‖ₑ = ‖w y - w x‖ₑ := by rw [← enorm_neg, neg_sub]
      _ = ‖∫ t in Ioc (0:ℝ) 1, fderiv ℝ w (x + t • (y - x)) (y - x)‖ₑ := by rw [hftc]
      _ ≤ ∫⁻ t in Ioc (0:ℝ) 1, ‖fderiv ℝ w (x + t • (y - x)) (y - x)‖ₑ :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ t in Ioc (0:ℝ) 1, ‖fderiv ℝ w (x + t • (y - x))‖ₑ * ‖y - x‖ₑ := by
          apply lintegral_mono
          intro t
          exact ContinuousLinearMap.le_opENorm _ _
  -- Steps 5–6: Tonelli and the dilation bound.
  have double : ∀ F : Rn n → ℝ≥0∞, Measurable F →
      ∫⁻ x in O, ∫⁻ y in O, ∫⁻ t in Ioc (0:ℝ) 1, F (x + t • (y - x))
        ≤ 2 ^ n * (∫⁻ z, F z) * volume O := by
    intro F hF
    have swap1 : ∀ x, ∫⁻ y in O, ∫⁻ t in Ioc (0:ℝ) 1, F (x + t • (y - x))
        = ∫⁻ t in Ioc (0:ℝ) 1, ∫⁻ y in O, F (x + t • (y - x)) := by
      intro x
      apply lintegral_lintegral_swap
      exact (hF.comp (by fun_prop)).aemeasurable
    have swap2 : ∫⁻ x in O, ∫⁻ t in Ioc (0:ℝ) 1, ∫⁻ y in O, F (x + t • (y - x))
        = ∫⁻ t in Ioc (0:ℝ) 1, ∫⁻ x in O, ∫⁻ y in O, F (x + t • (y - x)) := by
      apply lintegral_lintegral_swap
      exact (Measurable.lintegral_prod_right'
        (f := fun q : (Rn n × ℝ) × Rn n ↦ F (q.1.1 + q.1.2 • (q.2 - q.1.1)))
        (hF.comp (by fun_prop))).aemeasurable
    rw [lintegral_congr swap1, swap2]
    -- Step 6: `J(t) ≤ 2ⁿ (∫⁻ F) μ(O)` for `t ∈ (0, 1]`.
    have hJ : ∀ t ∈ Ioc (0:ℝ) 1, ∫⁻ x in O, ∫⁻ y in O, F (x + t • (y - x))
        ≤ 2 ^ n * (∫⁻ z, F z) * volume O := by
      intro t ht
      by_cases h2 : 1 / 2 ≤ t
      · -- (a) `t ≥ 1/2`: dilate in `y`.
        calc ∫⁻ x in O, ∫⁻ y in O, F (x + t • (y - x))
              ≤ ∫⁻ x in O, 2 ^ n * ∫⁻ z, F z := by
              apply lintegral_mono; intro x
              calc ∫⁻ y in O, F (x + t • (y - x)) ≤ ∫⁻ y, F (x + t • (y - x)) :=
                    setLIntegral_le_lintegral _ _
                _ = ∫⁻ y, F ((1 - t) • x + t • y) := by
                    congr 1; ext y; congr 1; module
                _ = ENNReal.ofReal ((t ^ n)⁻¹) * ∫⁻ z, F z := dil F ((1 - t) • x) t ht.1
                _ ≤ 2 ^ n * ∫⁻ z, F z := by gcongr; exact half t h2
          _ = 2 ^ n * (∫⁻ z, F z) * volume O := setLIntegral_const _ _
      · -- (b) `t < 1/2`: swap `x` and `y`, then dilate in `x`.
        push Not at h2
        have hm : Measurable (Function.uncurry fun x y : Rn n ↦ F (x + t • (y - x))) :=
          hF.comp (by fun_prop)
        rw [lintegral_lintegral_swap hm.aemeasurable]
        calc ∫⁻ y in O, ∫⁻ x in O, F (x + t • (y - x))
              ≤ ∫⁻ y in O, 2 ^ n * ∫⁻ z, F z := by
              apply lintegral_mono; intro y
              calc ∫⁻ x in O, F (x + t • (y - x)) ≤ ∫⁻ x, F (x + t • (y - x)) :=
                    setLIntegral_le_lintegral _ _
                _ = ∫⁻ x, F (t • y + (1 - t) • x) := by
                    congr 1; ext x; congr 1; module
                _ = ENNReal.ofReal (((1 - t) ^ n)⁻¹) * ∫⁻ z, F z :=
                    dil F (t • y) (1 - t) (by linarith)
                _ ≤ 2 ^ n * ∫⁻ z, F z := by gcongr; exact half (1 - t) (by linarith)
          _ = 2 ^ n * (∫⁻ z, F z) * volume O := setLIntegral_const _ _
    calc ∫⁻ t in Ioc (0:ℝ) 1, ∫⁻ x in O, ∫⁻ y in O, F (x + t • (y - x))
          ≤ ∫⁻ t in Ioc (0:ℝ) 1, 2 ^ n * (∫⁻ z, F z) * volume O :=
          setLIntegral_mono' measurableSet_Ioc hJ
      _ = 2 ^ n * (∫⁻ z, F z) * volume O := by
          rw [setLIntegral_const, Real.volume_Ioc]; simp
  -- Step 7: the mean step, `‖w x - w̄‖ₑ ≤ μ(O)⁻¹ ∫⁻_O ‖w x - w y‖ₑ dy`.
  have hm0 : volume O ≠ 0 := (hO.measure_pos volume hne).ne'
  have hmt : volume O ≠ ⊤ := hOb.measure_lt_top.ne
  have hwint : IntegrableOn w O volume :=
    (hw.continuous.continuousOn.integrableOn_compact hOb.isCompact_closure).mono_set subset_closure
  have mean : ∀ x, ‖w x - (volume O).toReal⁻¹ * ∫ y in O, w y‖ₑ
      ≤ (volume O)⁻¹ * ∫⁻ y in O, ‖w x - w y‖ₑ := by
    intro x
    have hI : ∫ y in O, (w x - w y) = (volume O).toReal * w x - ∫ y in O, w y := by
      rw [integral_sub (integrableOn_const (C := w x) hmt) hwint, setIntegral_const, smul_eq_mul,
        measureReal_def]
    have hmR : (volume O).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hm0, hmt⟩
    have key : w x - (volume O).toReal⁻¹ * ∫ y in O, w y
        = (volume O).toReal⁻¹ * ∫ y in O, (w x - w y) := by
      rw [hI]; field_simp
    have hinv : ‖(volume O).toReal⁻¹‖ₑ = (volume O)⁻¹ := by
      rw [Real.enorm_of_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg), ← ENNReal.toReal_inv,
        ENNReal.ofReal_toReal (ENNReal.inv_ne_top.mpr hm0)]
    rw [key, enorm_mul, hinv]
    gcongr
    exact enorm_integral_le_lintegral_enorm _
  -- Step 2 and Step 4 (second half): the indicator `F` and the pointwise segment bound.
  have hcont : Continuous (fun z ↦ fderiv ℝ w z) := hw.continuous_fderiv one_ne_zero
  set F : Rn n → ℝ≥0∞ := O.indicator (fun z ↦ ‖fderiv ℝ w z‖ₑ) with hFdef
  have hF : Measurable F := (hcont.enorm.measurable).indicator hO.measurableSet
  have hFint : ∫⁻ z, F z = ∫⁻ x in O, ‖fderiv ℝ w x‖ₑ := lintegral_indicator hO.measurableSet _
  set D := Metric.diam O with hD
  have hseg : ∀ x ∈ O, ∀ y ∈ O, ‖w x - w y‖ₑ
      ≤ ENNReal.ofReal D * ∫⁻ t in Ioc (0:ℝ) 1, F (x + t • (y - x)) := by
    intro x hx y hy
    calc ‖w x - w y‖ₑ ≤ ∫⁻ t in Ioc (0:ℝ) 1, ‖fderiv ℝ w (x + t • (y - x))‖ₑ * ‖y - x‖ₑ :=
          seg x y
      _ ≤ ∫⁻ t in Ioc (0:ℝ) 1, ENNReal.ofReal D * F (x + t • (y - x)) := by
          apply setLIntegral_mono' measurableSet_Ioc
          intro t ht
          have hmem : x + t • (y - x) ∈ O := hOc.add_smul_sub_mem hx hy ⟨ht.1.le, ht.2⟩
          rw [hFdef, indicator_of_mem hmem, mul_comm]
          gcongr
          rw [← ofReal_norm, ← dist_eq_norm]
          exact ENNReal.ofReal_le_ofReal (dist_le_diam_of_mem hOb hy hx)
      _ = ENNReal.ofReal D * ∫⁻ t in Ioc (0:ℝ) 1, F (x + t • (y - x)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  -- (★) `∫⁻_O ∫⁻_O ‖w x - w y‖ₑ ≤ diam(O) 2ⁿ (∫⁻ F) μ(O)`.
  have hstar : ∫⁻ x in O, ∫⁻ y in O, ‖w x - w y‖ₑ
      ≤ ENNReal.ofReal D * (2 ^ n * (∫⁻ z, F z) * volume O) := by
    calc ∫⁻ x in O, ∫⁻ y in O, ‖w x - w y‖ₑ
          ≤ ∫⁻ x in O, ∫⁻ y in O, ENNReal.ofReal D * ∫⁻ t in Ioc (0:ℝ) 1, F (x + t • (y - x)) := by
          apply setLIntegral_mono' hO.measurableSet; intro x hx
          apply setLIntegral_mono' hO.measurableSet; intro y hy
          exact hseg x hx y hy
      _ = ENNReal.ofReal D * ∫⁻ x in O, ∫⁻ y in O, ∫⁻ t in Ioc (0:ℝ) 1, F (x + t • (y - x)) := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1; ext x
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal D * (2 ^ n * (∫⁻ z, F z) * volume O) := by
          gcongr; exact double F hF
  -- Step 8: integrate the mean step over `x` and cancel `μ(O)⁻¹ μ(O) = 1`.
  calc ∫⁻ x in O, ‖w x - (volume O).toReal⁻¹ * ∫ y in O, w y‖ₑ
        ≤ ∫⁻ x in O, (volume O)⁻¹ * ∫⁻ y in O, ‖w x - w y‖ₑ := lintegral_mono mean
    _ = (volume O)⁻¹ * ∫⁻ x in O, ∫⁻ y in O, ‖w x - w y‖ₑ :=
        lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hm0)
    _ ≤ (volume O)⁻¹ * (ENNReal.ofReal D * (2 ^ n * (∫⁻ z, F z) * volume O)) := by gcongr
    _ = ((volume O)⁻¹ * volume O) * (2 ^ n * ENNReal.ofReal D * ∫⁻ z, F z) := by ring
    _ = ENNReal.ofReal (2 ^ n * D) * ∫⁻ x in O, ‖fderiv ℝ w x‖ₑ := by
        rw [ENNReal.inv_mul_cancel hm0 hmt, one_mul, hFint, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
/-- **Inner exhaustion of an open convex set** (Simon 2.7, "`W = {x ∈ U : dist(x, ∂U) > σ}`").
Every open convex `U ⊆ ℝⁿ` is the increasing union of open convex sets `O_j` with
`closedBall x σ_j ⊆ U` for `x ∈ O_j`, where `σ_j > 0` and `σ_j → 0`. Take `σ_j = 1/(j+1)`. If
`U = ℝⁿ`, let `O_j = ℝⁿ`. Otherwise `Uᶜ` is closed and nonempty; with `d = infDist(·, Uᶜ)` let
`O_j = {d > σ_j}`. A point `z` with `dist(x, z) < d(x)` lies in `U`; this gives the margins and
`O_j ⊆ U`, and `d > 0` on `U` gives `⋃_j O_j = U`. Convexity: if `‖v‖ < min(d(x), d(y))` then
`x + v, y + v ∈ U`, so `a(x + v) + b(y + v) = ax + by + v ∈ U`; hence `d(ax + by) ≥ min(d(x), d(y))`. -/
theorem Submission.convex_open_exists_inner_exhaustion : ∀ (n : ℕ) (U : Set (Rn n)), IsOpen U → Convex ℝ U → ∃ (O : ℕ → Set (Rn n)) (σ : ℕ → ℝ), Monotone O ∧ ⋃ j, O j = U ∧ Tendsto σ atTop (𝓝 0) ∧ ∀ j, IsOpen (O j) ∧ Convex ℝ (O j) ∧ 0 < σ j ∧ ∀ x ∈ O j, closedBall x (σ j) ⊆ U := by
  intro n U hU hconv
  -- Step 1: the radii `σ_j = 1/(j+1)` are positive and decreasing.
  have hσpos : ∀ j : ℕ, (0 : ℝ) < 1 / ((j : ℝ) + 1) := fun j ↦ by positivity
  have hσanti : ∀ i j : ℕ, i ≤ j → 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) := fun i j hij ↦
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
  by_cases hUniv : U = univ
  · -- Step 2: `U = ℝⁿ`; take `O_j = ℝⁿ`.
    subst hUniv
    exact ⟨fun _ ↦ univ, fun j ↦ 1 / ((j : ℝ) + 1), monotone_const, iUnion_const _,
      tendsto_one_div_add_atTop_nhds_zero_nat,
      fun j ↦ ⟨isOpen_univ, convex_univ, hσpos j, fun _ _ ↦ subset_univ _⟩⟩
  -- Step 3: `Uᶜ` is closed and nonempty; `O_j = {x | σ_j < infDist x Uᶜ}`.
  have hne : (Uᶜ).Nonempty := nonempty_compl.2 hUniv
  have hcl : IsClosed Uᶜ := hU.isClosed_compl
  -- (a) A point closer to `x` than `infDist x Uᶜ` lies in `U`.
  have key : ∀ x z : Rn n, dist x z < infDist x Uᶜ → z ∈ U := fun x z h ↦
    notMem_compl_iff.1 (notMem_of_dist_lt_infDist h)
  refine ⟨fun j ↦ {x | 1 / ((j : ℝ) + 1) < infDist x Uᶜ}, fun j ↦ 1 / ((j : ℝ) + 1), ?_, ?_,
    tendsto_one_div_add_atTop_nhds_zero_nat, fun j ↦ ⟨?_, ?_, hσpos j, ?_⟩⟩
  · -- (b) Monotone: `σ_j ≤ σ_i` for `i ≤ j`.
    intro i j hij x hx
    exact (hσanti i j hij).trans_lt hx
  · -- (e) Union: `x ∈ O_j` gives `x ∈ U` by (a); `x ∈ U` gives `0 < infDist x Uᶜ`.
    ext x
    simp only [mem_iUnion, mem_ofPred_eq]
    constructor
    · rintro ⟨j, hj⟩
      exact key x x (by rw [dist_self]; exact (hσpos j).trans hj)
    · intro hx
      exact exists_nat_one_div_lt ((hcl.notMem_iff_infDist_pos hne).1 (notMem_compl_iff.2 hx))
  · -- (c) Open: `infDist · Uᶜ` is continuous.
    exact isOpen_lt continuous_const (continuous_infDist_pt _)
  · -- (f) Convex: `min (infDist x Uᶜ) (infDist y Uᶜ) ≤ infDist (a • x + b • y) Uᶜ`.
    intro x hx y hy a b ha hb hab
    simp only [mem_ofPred_eq] at hx hy ⊢
    refine (lt_min hx hy).trans_le ((le_infDist hne).2 fun p hp ↦ not_lt.1 fun hlt ↦ hp ?_)
    -- `v = p - (a • x + b • y)` has `‖v‖ < min (infDist x Uᶜ) (infDist y Uᶜ)`, so `x + v`,
    -- `y + v ∈ U` by (a), and `a • (x + v) + b • (y + v) = p` lies in `U` by convexity.
    rw [dist_comm, dist_eq_norm] at hlt
    have hxv : x + (p - (a • x + b • y)) ∈ U := key x _ (by
      rw [dist_eq_norm, sub_add_cancel_left, norm_neg]
      exact hlt.trans_le (min_le_left _ _))
    have hyv : y + (p - (a • x + b • y)) ∈ U := key y _ (by
      rw [dist_eq_norm, sub_add_cancel_left, norm_neg]
      exact hlt.trans_le (min_le_right _ _))
    have hcomb : a • (x + (p - (a • x + b • y))) + b • (y + (p - (a • x + b • y))) = p := by
      rw [smul_add, smul_add, add_add_add_comm, ← add_smul, hab, one_smul, add_sub_cancel]
    exact hcomb ▸ hconv hxv hyv ha hb hab
  · -- (d) Margin: `dist x p ≤ σ_j < infDist x Uᶜ` for `p ∈ closedBall x σ_j`.
    intro x hx p hp
    rw [mem_closedBall, dist_comm] at hp
    exact key x p (hp.trans_lt hx)
/-- **Mean-oscillation bounds pass to the `L¹` limit along an increasing exhaustion** (step B4 of
the proof of Simon 2.7, "letting `σ ↓ 0`"). Let measurable `O j` increase to `U` with `μ(U) < ∞`,
`u ∈ L¹(U)` and `w j ∈ L¹(O j)`. If `e_j = ∫⁻_{O j} ‖w j - u‖ₑ → 0` and `∫⁻_{O j} ‖w j - c_j‖ₑ ≤ K`
for the means `c_j` of `w j` over `O j`, then `∫⁻_U ‖u - ū‖ₑ ≤ K` for the mean `ū` of `u` over `U`.
Since `μ(O j) → μ(U)` and `|∫_{O j} w j - ∫_{O j} u| ≤ e_j`, `c_j → ū`; the integrated triangle
inequality gives `∫⁻_{O j} ‖u - ū‖ₑ ≤ K + e_j + ‖c_j - ū‖ₑ μ(U)`, and `∫⁻_U = ⨆ j, ∫⁻_{O j}`
(`setLIntegral_iUnion_of_directed`). -/
theorem Submission.mean_oscillation_lintegral_le_of_approx : ∀ (n : ℕ) (U : Set (Rn n)) (u : Rn n → ℝ) (O : ℕ → Set (Rn n)) (w : ℕ → Rn n → ℝ) (K : ℝ≥0∞), volume U < ⊤ → IntegrableOn u U volume → (∀ j, MeasurableSet (O j)) → Monotone O → ⋃ j, O j = U → (∀ j, IntegrableOn (w j) (O j) volume) → Tendsto (fun j ↦ ∫⁻ x in O j, ‖w j x - u x‖ₑ) atTop (𝓝 0) → (∀ j, ∫⁻ x in O j, ‖w j x - (volume (O j)).toReal⁻¹ * ∫ y in O j, w j y‖ₑ ≤ K) → ∫⁻ x in U, ‖u x - (volume U).toReal⁻¹ * ∫ y in U, u y‖ₑ ≤ K := by
  intro n U u O w K hUfin hu hOm hOmono hOU hw he hK
  -- Step 1: every `O j` lies in `U`.
  have hsub : ∀ j, O j ⊆ U := fun j ↦ hOU ▸ subset_iUnion O j
  -- Step 2: the case `μ(U) = 0` is trivial.
  by_cases hU0 : volume U = 0
  · rw [setLIntegral_measure_zero U _ hU0]
    exact zero_le
  -- Step 3: `μ(O_j) → μ(U)` by continuity from below.
  have hmeas : Tendsto (fun j ↦ (volume (O j)).toReal) atTop (𝓝 (volume U).toReal) := by
    have h := tendsto_measure_iUnion_atTop (μ := volume) hOmono
    rw [hOU] at h
    exact (ENNReal.tendsto_toReal hUfin.ne).comp h
  -- Step 4: `∫_{O_j} u → ∫_U u`.
  have hint_u : Tendsto (fun j ↦ ∫ y in O j, u y) atTop (𝓝 (∫ y in U, u y)) := by
    have h := tendsto_setIntegral_of_monotone (μ := volume) (f := u) hOm hOmono (hOU.symm ▸ hu)
    rwa [hOU] at h
  -- Step 5: `|∫_{O_j} w_j − ∫_{O_j} u| ≤ e_j → 0`, hence `∫_{O_j} w_j → ∫_U u`.
  have hdiff : Tendsto (fun j ↦ (∫ y in O j, w j y) - ∫ y in O j, u y) atTop (𝓝 0) := by
    refine tendsto_zero_iff_enorm_tendsto_zero.mpr
      (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds he (fun j ↦ zero_le)
        (fun j ↦ ?_))
    show ‖(∫ y in O j, w j y) - ∫ y in O j, u y‖ₑ ≤ ∫⁻ x in O j, ‖w j x - u x‖ₑ
    rw [← integral_sub (hw j) (hu.mono_set (hsub j))]
    exact enorm_integral_le_lintegral_enorm _
  have hint_w : Tendsto (fun j ↦ ∫ y in O j, w j y) atTop (𝓝 (∫ y in U, u y)) := by
    simpa using hdiff.add hint_u
  -- Step 6: the means `c_j` converge to `ū`.
  have hM : (volume U).toReal ≠ 0 := (ENNReal.toReal_pos hU0 hUfin.ne).ne'
  have hc : Tendsto (fun j ↦ (volume (O j)).toReal⁻¹ * ∫ y in O j, w j y) atTop
      (𝓝 ((volume U).toReal⁻¹ * ∫ y in U, u y)) := (hmeas.inv₀ hM).mul hint_w
  have hc' : Tendsto (fun j ↦ ‖(volume (O j)).toReal⁻¹ * (∫ y in O j, w j y) -
      (volume U).toReal⁻¹ * ∫ y in U, u y‖ₑ * volume U) atTop (𝓝 0) := by
    have h1 := tendsto_zero_iff_enorm_tendsto_zero.mp (tendsto_sub_nhds_zero_iff.mpr hc)
    simpa using ENNReal.Tendsto.mul_const h1 (Or.inr hUfin.ne)
  have hr := he.add hc'
  rw [add_zero] at hr
  -- Step 7: the integrated triangle inequality on each `O_j`.
  have hbound : ∀ j, ∫⁻ x in O j, ‖u x - (volume U).toReal⁻¹ * ∫ y in U, u y‖ₑ ≤
      K + ((∫⁻ x in O j, ‖w j x - u x‖ₑ) + ‖(volume (O j)).toReal⁻¹ * (∫ y in O j, w j y) -
        (volume U).toReal⁻¹ * ∫ y in U, u y‖ₑ * volume U) := by
    intro j
    set ub := (volume U).toReal⁻¹ * ∫ y in U, u y
    set cj := (volume (O j)).toReal⁻¹ * ∫ y in O j, w j y
    have hpt : ∀ x, ‖u x - ub‖ₑ ≤ ‖w j x - u x‖ₑ + (‖w j x - cj‖ₑ + ‖cj - ub‖ₑ) := by
      intro x
      calc ‖u x - ub‖ₑ = ‖-(w j x - u x) + ((w j x - cj) + (cj - ub))‖ₑ := by congr 1; ring
        _ ≤ ‖-(w j x - u x)‖ₑ + ‖(w j x - cj) + (cj - ub)‖ₑ := enorm_add_le _ _
        _ ≤ ‖w j x - u x‖ₑ + (‖w j x - cj‖ₑ + ‖cj - ub‖ₑ) := by
          rw [enorm_neg]
          gcongr
          exact enorm_add_le _ _
    have hae : AEMeasurable (fun x ↦ ‖w j x - u x‖ₑ) (volume.restrict (O j)) :=
      ((hw j).sub (hu.mono_set (hsub j))).aemeasurable.enorm
    calc ∫⁻ x in O j, ‖u x - ub‖ₑ
        ≤ ∫⁻ x in O j, ‖w j x - u x‖ₑ + (‖w j x - cj‖ₑ + ‖cj - ub‖ₑ) := lintegral_mono hpt
      _ = (∫⁻ x in O j, ‖w j x - u x‖ₑ) +
            ((∫⁻ x in O j, ‖w j x - cj‖ₑ) + ‖cj - ub‖ₑ * volume (O j)) := by
          rw [lintegral_add_left' hae, lintegral_add_right _ measurable_const, setLIntegral_const]
      _ ≤ (∫⁻ x in O j, ‖w j x - u x‖ₑ) + (K + ‖cj - ub‖ₑ * volume U) := by
          gcongr
          · exact hK j
          · exact hsub j
      _ = K + ((∫⁻ x in O j, ‖w j x - u x‖ₑ) + ‖cj - ub‖ₑ * volume U) := add_left_comm _ _ _
  -- Step 8: for each fixed `j`, `∫⁻_{O_j} ‖u − ū‖ₑ ≤ K`.
  have hO : ∀ j, ∫⁻ x in O j, ‖u x - (volume U).toReal⁻¹ * ∫ y in U, u y‖ₑ ≤ K := by
    intro j
    have hlim := (tendsto_const_nhds (x := K)).add hr
    rw [add_zero] at hlim
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop j] with k hk
    exact (lintegral_mono_set (hOmono hk)).trans (hbound k)
  -- Step 9: pass to the directed union `⋃ j, O j = U`.
  calc ∫⁻ x in U, ‖u x - (volume U).toReal⁻¹ * ∫ y in U, u y‖ₑ
      = ∫⁻ x in ⋃ j, O j, ‖u x - (volume U).toReal⁻¹ * ∫ y in U, u y‖ₑ := by rw [hOU]
    _ = ⨆ j, ∫⁻ x in O j, ‖u x - (volume U).toReal⁻¹ * ∫ y in U, u y‖ₑ :=
        setLIntegral_iUnion_of_directed _ hOmono.directed_le
    _ ≤ K := iSup_le hO
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
/-- **Concavity of the distance to the complement of a convex set** (Simon 2.8, proof, C1(b)).
For a convex `U ⊆ ℝⁿ`, `d(x) = infDist x Uᶜ` is concave on `U`; `U` need not be open, and
`infDist x ∅ = 0`. Fix `x, y ∈ U` and `a, b ≥ 0` with `a + b = 1`, and put `z = a • x + b • y`,
`s = a d(x) + b d(y)`. Suppose some `p ∈ Uᶜ` had `dist z p < s`, and put `h = p - z`. Then the
shifted points `x + (d(x)/s) • h` and `y + (d(y)/s) • h` lie in `U`
(`Metric.ball_infDist_compl_subset`), and their `a, b`-combination is `p`. This contradicts
convexity, so `s ≤ d(z)` by `Metric.le_infDist`. -/
theorem Submission.bv_ext_infDist_compl_concaveOn : ∀ (n : ℕ) (U : Set (Rn n)), Convex ℝ U → ConcaveOn ℝ U (fun x ↦ infDist x Uᶜ) := by
  intro n U hU
  -- Step 1: fix `x, y ∈ U` and weights `a, b ≥ 0` with `a + b = 1`.
  refine ⟨hU, fun x hx y hy a b ha hb hab ↦ ?_⟩
  simp only [smul_eq_mul]
  -- Step 2: if `Uᶜ = ∅` both sides vanish; otherwise it suffices to bound `dist z p`, `p ∈ Uᶜ`.
  rcases (Uᶜ).eq_empty_or_nonempty with hE | hne
  · simp [hE]
  rw [le_infDist hne]
  intro p hp
  -- Step 4: suppose `dist z p < s`; then `s > 0`, and `h = p - z` has `‖h‖ < s`.
  by_contra! hlt
  set s := a * infDist x Uᶜ + b * infDist y Uᶜ
  have hs0 : 0 < s := dist_nonneg.trans_lt hlt
  set h := p - (a • x + b • y) with hh
  have hnorm : ‖h‖ < s := by rwa [hh, ← dist_eq_norm, dist_comm]
  -- Steps 3 and 5: each shifted point `q + (d(q)/s) • h`, `q ∈ U`, lies in `U`.
  have hshift : ∀ q ∈ U, q + (infDist q Uᶜ / s) • h ∈ U := by
    intro q hq
    rcases (infDist_nonneg (x := q) (s := Uᶜ)).eq_or_lt with h0 | hpos
    · rw [← h0, zero_div, zero_smul, add_zero]
      exact hq
    · apply ball_infDist_compl_subset
      rw [mem_ball, dist_self_add_left, norm_smul, Real.norm_of_nonneg (div_nonneg hpos.le hs0.le)]
      calc infDist q Uᶜ / s * ‖h‖ < infDist q Uᶜ / s * s := by gcongr
        _ = infDist q Uᶜ := div_mul_cancel₀ _ hs0.ne'
  -- Step 6: the `a, b`-combination of the shifted points is `z + h = p`, so `p ∈ U`.
  have hcoef : a * (infDist x Uᶜ / s) + b * (infDist y Uᶜ / s) = 1 := by
    rw [mul_div_assoc', mul_div_assoc', ← add_div, div_self hs0.ne']
  have hp' : a • (x + (infDist x Uᶜ / s) • h) + b • (y + (infDist y Uᶜ / s) • h) = p := by
    calc a • (x + (infDist x Uᶜ / s) • h) + b • (y + (infDist y Uᶜ / s) • h)
        = (a • x + b • y) + (a * (infDist x Uᶜ / s) + b * (infDist y Uᶜ / s)) • h := by
          simp only [smul_add, smul_smul, add_smul]
          abel
      _ = p := by rw [hcoef, one_smul, hh, add_sub_cancel]
  exact hp (hp' ▸ hU (hshift x hx) (hshift y hy) ha hb hab)
/-- **Unit gradient of the distance function off a closed set** (Simon 2.8 proof, C1(c), with `S`
in place of `Uᶜ`). If `S ⊆ ℝⁿ` is closed and nonempty, `x ∉ S` and `d = infDist · S` is
differentiable at `x`, then `‖Dd(x)‖ = 1`. Since `d` is 1-Lipschitz, `‖Dd(x)‖ ≤ 1`
(`norm_fderiv_le_of_lipschitz`). Conversely, take a nearest point `a ∈ S`
(`IsClosed.exists_infDist_eq_dist`), `ρ = d(x) > 0` and the unit vector `e = ρ⁻¹ • (a - x)`. Then
`d(x + t • e) ≤ ρ - t` for `0 ≤ t ≤ ρ`, so the right difference quotients of `t ↦ d(x + t • e)` at
`0` give `Dd(x) e ≤ -1`, and `‖Dd(x)‖ ≥ |Dd(x) e| ≥ 1`. -/
theorem Submission.bv_ext_norm_fderiv_infDist_eq_one : ∀ (n : ℕ) (S : Set (Rn n)) (x : Rn n), IsClosed S → S.Nonempty → x ∉ S → DifferentiableAt ℝ (fun y ↦ infDist y S) x → ‖fderiv ℝ (fun y ↦ infDist y S) x‖ = 1 := by
  intro n S x hS hne hx hd
  set L := fderiv ℝ (fun y ↦ infDist y S) x with hL
  -- Step 1: `infDist · S` is 1-Lipschitz, so `‖L‖ ≤ 1`.
  have hup : ‖L‖ ≤ 1 := by
    simpa using norm_fderiv_le_of_lipschitz ℝ (x₀ := x) (lipschitz_infDist_pt S)
  -- Step 2: a nearest point `a ∈ S`, with `ρ = infDist x S = ‖a - x‖ > 0`.
  obtain ⟨a, haS, hda⟩ := hS.exists_infDist_eq_dist hne x
  have hρ : 0 < infDist x S := (hS.notMem_iff_infDist_pos hne).1 hx
  set ρ := infDist x S with hρdef
  have hax : ‖a - x‖ = ρ := by rw [hda, dist_comm, dist_eq_norm]
  -- Step 3: along the unit vector `e` towards `a`, `infDist (x + t • e) S ≤ ρ - t` on `[0, ρ]`.
  set e : Rn n := ρ⁻¹ • (a - x) with he
  have he1 : ‖e‖ = 1 := by
    rw [he, norm_smul, hax, Real.norm_eq_abs, abs_inv, abs_of_pos hρ, inv_mul_cancel₀ hρ.ne']
  have hdec : ∀ t : ℝ, 0 ≤ t → t ≤ ρ → infDist (x + t • e) S ≤ ρ - t := by
    intro t ht0 htρ
    have hvec : a - (x + t • e) = (1 - t / ρ) • (a - x) := by
      rw [he, smul_smul, sub_smul, one_smul, div_eq_mul_inv]; abel
    have hcoef : 0 ≤ 1 - t / ρ := by rw [sub_nonneg, div_le_one hρ]; exact htρ
    calc infDist (x + t • e) S ≤ dist (x + t • e) a := infDist_le_dist_of_mem haS
      _ = ρ - t := by
        rw [dist_comm, dist_eq_norm, hvec, norm_smul, hax, Real.norm_eq_abs, abs_of_nonneg hcoef]
        field_simp
  -- Step 4: `t ↦ infDist (x + t • e) S` has derivative `L e` at `0`; its right difference
  -- quotients are `≤ -1` on `(0, ρ]`, hence `L e ≤ -1`.
  have hderiv : HasDerivAt (fun t : ℝ ↦ infDist (x + t • e) S) (L e) 0 := by
    have hline : HasDerivAt (fun t : ℝ ↦ x + t • e) e 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add x
    have hdx : HasFDerivAt (fun y ↦ infDist y S) L (x + (0 : ℝ) • e) := by
      simpa using hd.hasFDerivAt
    exact hdx.comp_hasDerivAt (0 : ℝ) hline
  have hLe : L e ≤ -1 := by
    refine le_of_tendsto hderiv.tendsto_slope_zero_right ?_
    filter_upwards [Ioc_mem_nhdsGT hρ] with t ht
    have h3 := hdec t ht.1.le ht.2
    simp only [zero_add, zero_smul, add_zero, smul_eq_mul]
    rw [inv_mul_le_iff₀ ht.1]
    linarith
  -- Step 5: `1 ≤ -L e = ‖L e‖ ≤ ‖L‖ * ‖e‖ = ‖L‖`.
  have hlow : 1 ≤ ‖L‖ := by
    have h := L.le_opNorm e
    rw [he1, mul_one, Real.norm_eq_abs, abs_of_neg (by linarith)] at h
    linarith
  -- Step 6: combine the two bounds.
  exact le_antisymm hup hlow
/-- **Divergence of a scalar multiple** (Simon 2.8 proof, C4(b) and C5(b)). If `φ : ℝⁿ → ℝ` and
`g : ℝⁿ → ℝⁿ` are differentiable at `x`, then `div(φ g)(x) = φ(x) div g(x) + Dφ(x)[g(x)]`. By the
product rule (`fderiv_fun_smul`), `D(φ g)(x) = φ(x) Dg(x) + Dφ(x).smulRight (g x)`. The trace is
linear, and the rank-one map `h ↦ Dφ(x)[h] g(x)` has trace `Dφ(x)[g(x)]`
(`LinearMap.trace_smulRight`). -/
theorem Submission.bv_ext_euclideanDivergence_smul : ∀ (n : ℕ) (φ : Rn n → ℝ) (g : Rn n → Rn n) (x : Rn n), DifferentiableAt ℝ φ x → DifferentiableAt ℝ g x → Chapter02.euclideanDivergence (fun y ↦ φ y • g y) x = φ x * Chapter02.euclideanDivergence g x + fderiv ℝ φ x (g x) := by
  intro n φ g x hφ hg
  -- Step 1: the divergence is the trace of the derivative, viewed as a linear map.
  unfold Chapter02.euclideanDivergence
  -- Step 2: product rule `D(φ g)(x) = φ(x) • Dg(x) + Dφ(x).smulRight (g x)`. The coercion to linear
  -- maps and the trace are additive and commute with scalar multiplication.
  rw [fderiv_fun_smul hφ hg, ContinuousLinearMap.toLinearMap_add,
    ContinuousLinearMap.toLinearMap_smul, map_add, map_smul, smul_eq_mul]
  -- Step 3: the coercion of `Dφ(x).smulRight (g x)` is definitionally
  -- `(Dφ(x) : ℝⁿ →ₗ[ℝ] ℝ).smulRight (g x)`, whose trace is `Dφ(x)[g(x)]`.
  congr 1
  exact LinearMap.trace_smulRight (fderiv ℝ φ x).toLinearMap (g x)
/-- **Admissible fields for `|Dv|(W)` (Simon 2.4).** A `K`-Lipschitz, compactly supported field
`G : ℝⁿ → ℝⁿ` with `spt G ⊆ W` and `|G| ≤ 1` is one of the fields in the supremum defining
`Chapter02.bvVariationOn v W`, so `ofReal (∫_W v div G) ≤ |Dv|(W)`. No openness or measurability of
`W` and no integrability of `v` is needed: this is the defining supremum bound. `G` is packaged as
`g ∈ C_c(ℝⁿ, ℝⁿ)` with `⇑g = G`. It is Lipschitz with constant `K`, and `sup |g| ≤ 1` by `csSup_le`. -/
theorem Submission.bv_ext_ofReal_integral_le_bvVariationOn : ∀ (n : ℕ) (W : Set (Rn n)) (v : Rn n → ℝ) (G : Rn n → Rn n) (K : ℝ≥0), LipschitzWith K G → HasCompactSupport G → tsupport G ⊆ W → (∀ x, ‖G x‖ ≤ 1) → ENNReal.ofReal (∫ x in W, v x * Chapter02.euclideanDivergence G x) ≤ Chapter02.bvVariationOn v W := by
  intro n W v G K hG hcs hsupp hnorm
  -- Step 1: package `G` (continuous, being Lipschitz) as `g ∈ C_c(ℝⁿ, ℝⁿ)`; `⇑g` is `G` by definition.
  let g : CompactlySupportedContinuousMap (Rn n) (Rn n) := ⟨⟨G, hG.continuous⟩, hcs⟩
  -- Step 2: `g` is a Lipschitz test field with constant `K`, and `tsupport ⇑g = tsupport G ⊆ W`.
  have hg : Chapter02.IsLipschitzTestField g := ⟨K, hG⟩
  -- Step 3: `sup |g| ≤ 1`, since the range of `‖g ·‖` is nonempty and bounded by `1`.
  have hn : Chapter02.compactlySupportedSupNorm g ≤ 1 :=
    csSup_le (range_nonempty _) (by rintro _ ⟨x, rfl⟩; exact hnorm x)
  -- Step 4: the defining supremum bound for the admissible field `g`.
  exact Chapter02.ofReal_integral_le_bvVariationOn v W g hg hsupp hn

/-- **Weighted gradient estimate** (Simon 2.8 proof, C4, Simon's (5)). Let `U ⊆ B_R(ξ)` be open,
`u ∈ L¹(ℝⁿ)` and `φ : ℝⁿ → ℝ` Lipschitz with `0 ≤ φ ≤ 1`, `spt φ ⊆ U` compact and
`r |Dφ(x)| ≤ -Dφ(x)[x - ξ]` for a.e. `x`. Then `r ∫ |u| |Dφ| ≤ R |D|u||(U) + n ∫_U |u|`. The field
`V = φ (x - ξ)/R` is Lipschitz with `spt V ⊆ U` compact and `|V| ≤ 1`, so `-V` is admissible for
`|D|u||(U)`. By Rademacher, `R div V = n φ + Dφ[x - ξ]` a.e., so
`r |u| |Dφ| ≤ n |u| φ - R |u| div V` a.e., and integrating gives the estimate. -/
theorem Submission.bv_ext_lintegral_enorm_mul_fderiv_le : ∀ (n : ℕ) (U : Set (Rn n)) (ξ : Rn n) (R r : ℝ) (u φ : Rn n → ℝ), IsOpen U → 0 < R → U ⊆ closedBall ξ R → Integrable u volume → (∃ K, LipschitzWith K φ) → (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) → HasCompactSupport φ → tsupport φ ⊆ U → (∀ᵐ x ∂volume, r * ‖fderiv ℝ φ x‖ ≤ -fderiv ℝ φ x (x - ξ)) → ENNReal.ofReal r * ∫⁻ x, ‖u x‖ₑ * ‖fderiv ℝ φ x‖ₑ ≤ ENNReal.ofReal R * Chapter02.bvVariationOn (fun x ↦ |u x|) U + (n : ℝ≥0∞) * ∫⁻ x in U, ‖u x‖ₑ := by
  rintro n U ξ R r u φ hUo hR hUB hu ⟨K, hφ⟩ hφ01 hφcs hφU hdir
  -- Step 1: the case `r ≤ 0` is trivial, since then `ofReal r = 0`.
  rcases le_or_gt r 0 with hr | hr
  · rw [ENNReal.ofReal_of_nonpos hr, zero_mul]
    exact bot_le
  -- Step 2: the field `V = φ • c`, where `c y = R⁻¹ • (y - ξ)`.
  set c : Rn n → Rn n := fun y ↦ R⁻¹ • (y - ξ) with hc_def
  set V : Rn n → Rn n := fun y ↦ φ y • c y with hV_def
  have hRinv : 0 ≤ R⁻¹ := inv_nonneg.mpr hR.le
  -- (i) `‖y - ξ‖ ≤ R` wherever `φ y ≠ 0`, since then `y ∈ tsupport φ ⊆ U ⊆ B_R(ξ)`.
  have hball : ∀ y, φ y ≠ 0 → ‖y - ξ‖ ≤ R := fun y hy ↦ by
    have hy' : y ∈ closedBall ξ R := hUB (hφU (subset_tsupport φ hy))
    rwa [mem_closedBall, dist_eq_norm] at hy'
  have hφ1 : ∀ x, ‖φ x‖ ≤ 1 := fun x ↦ by
    rw [Real.norm_of_nonneg (hφ01 x).1]
    exact (hφ01 x).2
  -- (ii) `V` is `(K + R⁻¹)`-Lipschitz: if `φ x ≠ 0`, then
  -- `V x - V y = R⁻¹ • ((φ x - φ y) • (x - ξ) + φ y • (x - y))`.
  have hkey : ∀ x y, φ x ≠ 0 → ‖V x - V y‖ ≤ (K + R⁻¹) * ‖x - y‖ := fun x y hx ↦ by
    have hsplit : V x - V y = R⁻¹ • ((φ x - φ y) • (x - ξ) + φ y • (x - y)) := by
      simp only [hV_def, hc_def]
      module
    have hφxy : ‖φ x - φ y‖ ≤ K * ‖x - y‖ := by
      simpa only [dist_eq_norm] using hφ.dist_le_mul x y
    rw [hsplit, norm_smul, Real.norm_of_nonneg hRinv]
    calc R⁻¹ * ‖(φ x - φ y) • (x - ξ) + φ y • (x - y)‖
        ≤ R⁻¹ * (‖φ x - φ y‖ * ‖x - ξ‖ + ‖φ y‖ * ‖x - y‖) := by
          gcongr
          rw [← norm_smul, ← norm_smul]
          exact norm_add_le _ _
      _ ≤ R⁻¹ * (K * ‖x - y‖ * R + 1 * ‖x - y‖) := by
          gcongr
          · exact hball x hx
          · exact hφ1 y
      _ = (K + R⁻¹) * ‖x - y‖ := by
          field_simp
  -- The case `φ y ≠ 0` is symmetric, and `V x = V y = 0` if `φ x = φ y = 0`.
  have hVlip : LipschitzWith (K + R⁻¹.toNNReal) V := by
    refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_add, Real.coe_toNNReal _ hRinv]
    by_cases hx : φ x = 0
    · by_cases hy : φ y = 0
      · simp only [hV_def, hx, hy, zero_smul, sub_self, norm_zero]
        positivity
      · rw [norm_sub_rev, norm_sub_rev x y]
        exact hkey y x hy
    · exact hkey x y hx
  -- (iii) `V` has compact support and `tsupport V ⊆ tsupport φ ⊆ U`.
  have hVcs : HasCompactSupport V := hφcs.smul_right
  have hVU : tsupport V ⊆ U := (tsupport_smul_subset_left φ c).trans hφU
  -- (iv) `‖V y‖ = φ y ‖y - ξ‖ / R ≤ 1`.
  have hV1 : ∀ y, ‖V y‖ ≤ 1 := fun y ↦ by
    by_cases hy : φ y = 0
    · simp [hV_def, hy]
    · calc ‖V y‖ = ‖φ y‖ * (R⁻¹ * ‖y - ξ‖) := by
            rw [hV_def, hc_def]
            simp only
            rw [norm_smul, norm_smul, Real.norm_of_nonneg hRinv]
        _ ≤ 1 * (R⁻¹ * R) := by
            gcongr
            · exact hφ1 y
            · exact hball y hy
        _ = 1 := by field_simp
  -- Step 3: `-V` is admissible for `U`, so `ofReal b ≤ |D|u||(U)`.
  have hadm : ENNReal.ofReal (∫ x in U, |u x| * Chapter02.euclideanDivergence (-V) x) ≤
      Chapter02.bvVariationOn (fun x ↦ |u x|) U :=
    Submission.bv_ext_ofReal_integral_le_bvVariationOn n U (fun x ↦ |u x|) (-V) _ hVlip.neg
      hVcs.neg (by rw [tsupport_neg]; exact hVU) (fun y ↦ by rw [Pi.neg_apply, norm_neg]; exact hV1 y)
  -- Step 4: `div (-V) = - div V`, and `div (-V)` vanishes off `tsupport (-V) ⊆ U`.
  have hdivneg : ∀ x, Chapter02.euclideanDivergence (-V) x = -Chapter02.euclideanDivergence V x := by
    intro x
    unfold Chapter02.euclideanDivergence
    rw [fderiv_neg, ContinuousLinearMap.toLinearMap_neg, map_neg]
  set b : ℝ := ∫ x in U, |u x| * Chapter02.euclideanDivergence (-V) x with hb_def
  have hb : b = -∫ x, |u x| * Chapter02.euclideanDivergence V x := by
    rw [hb_def, setIntegral_eq_integral_of_forall_compl_eq_zero, ← integral_neg]
    · simp only [hdivneg, mul_neg]
    · intro x hx
      have h0 : Chapter02.euclideanDivergence (-V) x = 0 := Function.notMem_support.mp fun h ↦
        hx ((tsupport_neg V ▸ hVU) (Chapter02.support_euclideanDivergence_subset (-V) h))
      rw [h0, mul_zero]
  -- Step 5: `Dc = R⁻¹ • id`, so `div c = n / R`, and where `φ` is differentiable (a.e., by
  -- Rademacher) the product rule gives `-Dφ(x)[x - ξ] = n φ(x) - R div V(x)`.
  have hc_deriv : ∀ x, HasFDerivAt c (R⁻¹ • ContinuousLinearMap.id ℝ (Rn n)) x := fun x ↦
    ((hasFDerivAt_id x).sub_const ξ).const_smul R⁻¹
  have hdivc : ∀ x, Chapter02.euclideanDivergence c x = R⁻¹ * n := by
    intro x
    unfold Chapter02.euclideanDivergence
    rw [(hc_deriv x).fderiv, ContinuousLinearMap.toLinearMap_smul, map_smul,
      ContinuousLinearMap.coe_id, LinearMap.trace_id, finrank_euclideanSpace_fin, smul_eq_mul]
  have hdivV : ∀ᵐ x ∂(volume : Measure (Rn n)),
      -fderiv ℝ φ x (x - ξ) = n * φ x - R * Chapter02.euclideanDivergence V x := by
    filter_upwards [hφ.ae_differentiableAt] with x hφx
    have h := Submission.bv_ext_euclideanDivergence_smul n φ c x hφx (hc_deriv x).differentiableAt
    rw [hdivc x] at h
    rw [h]
    simp only [hc_def, map_smul, smul_eq_mul]
    field_simp
    ring
  -- Step 6: the pointwise a.e. inequality `r |u| ‖Dφ‖ ≤ n |u| φ - R |u| div V`.
  have hpt : ∀ᵐ x ∂(volume : Measure (Rn n)),
      r * (|u x| * ‖fderiv ℝ φ x‖) ≤
        n * (|u x| * φ x) - R * (|u x| * Chapter02.euclideanDivergence V x) := by
    filter_upwards [hdir, hdivV] with x hx hxV
    have hux : 0 ≤ |u x| := abs_nonneg _
    have := mul_le_mul_of_nonneg_left hx hux
    rw [hxV] at this
    nlinarith [this]
  -- Step 7: integrability: `|u| ∈ L¹` times the bounded measurable `‖Dφ‖ ≤ K`, `φ ≤ 1` and
  -- `|div V| ≤ n (K + R⁻¹)`.
  have hint1 : Integrable fun x ↦ |u x| * ‖fderiv ℝ φ x‖ :=
    hu.abs.mul_bdd (measurable_fderiv ℝ φ).norm.aestronglyMeasurable
      (ae_of_all _ fun x ↦ (norm_norm _).trans_le (norm_fderiv_le_of_lipschitz ℝ hφ))
  have hint2 : Integrable fun x ↦ |u x| * φ x :=
    hu.abs.mul_bdd hφ.continuous.aestronglyMeasurable (ae_of_all _ hφ1)
  have hint3 : Integrable fun x ↦ |u x| * Chapter02.euclideanDivergence V x :=
    hu.abs.mul_bdd (Chapter02.measurable_euclideanDivergence _).aestronglyMeasurable
      (ae_of_all _ (Chapter02.norm_euclideanDivergence_le_of_lipschitz hVlip))
  -- Step 8: integrate the pointwise inequality.
  have hineq : r * ∫ x, |u x| * ‖fderiv ℝ φ x‖ ≤
      n * (∫ x, |u x| * φ x) - R * ∫ x, |u x| * Chapter02.euclideanDivergence V x := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul, ← integral_sub]
    · exact integral_mono_ae (hint1.const_mul r) ((hint2.const_mul _).sub (hint3.const_mul _)) hpt
    · exact hint2.const_mul _
    · exact hint3.const_mul _
  -- Step 9: the first term: `|u| φ` vanishes off `U` and `|u| φ ≤ |u|`, so `∫ |u| φ ≤ a`.
  set a : ℝ := ∫ x in U, |u x| with ha_def
  have hfirst : ∫ x, |u x| * φ x ≤ a := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := U)]
    · refine setIntegral_mono_on hint2.integrableOn hu.abs.integrableOn hUo.measurableSet
        fun x _ ↦ ?_
      exact mul_le_of_le_one_right (abs_nonneg _) (hφ01 x).2
    · intro x hx
      rw [image_eq_zero_of_notMem_tsupport fun h ↦ hx (hφU h), mul_zero]
  have hA : ENNReal.ofReal a = ∫⁻ x in U, ‖u x‖ₑ := by
    rw [ha_def, ← ofReal_integral_norm_eq_lintegral_enorm hu.integrableOn]
    simp only [Real.norm_eq_abs]
  -- Step 10: the second term is `-∫ |u| div V = b` (Step 4), and `ofReal b ≤ |D|u||(U)`.
  -- Step 11: so `r ∫ |u| ‖Dφ‖ ≤ n a + R b`; convert to `[0, ∞]`.
  have hreal : r * ∫ x, |u x| * ‖fderiv ℝ φ x‖ ≤ n * a + R * b := by
    rw [hb]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [mul_le_mul_of_nonneg_left hfirst hn0]
  have hlint : ∫⁻ x, ‖u x‖ₑ * ‖fderiv ℝ φ x‖ₑ = ENNReal.ofReal (∫ x, |u x| * ‖fderiv ℝ φ x‖) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint1
      (ae_of_all _ fun x ↦ mul_nonneg (abs_nonneg _) (norm_nonneg _))]
    refine lintegral_congr fun x ↦ ?_
    rw [ENNReal.ofReal_mul (abs_nonneg _), ← Real.norm_eq_abs, ofReal_norm, ofReal_norm]
  calc ENNReal.ofReal r * ∫⁻ x, ‖u x‖ₑ * ‖fderiv ℝ φ x‖ₑ
      = ENNReal.ofReal (r * ∫ x, |u x| * ‖fderiv ℝ φ x‖) := by
        rw [hlint, ENNReal.ofReal_mul hr.le]
    _ ≤ ENNReal.ofReal (n * a + R * b) := ENNReal.ofReal_le_ofReal hreal
    _ ≤ ENNReal.ofReal (n * a) + ENNReal.ofReal (R * b) := ENNReal.ofReal_add_le
    _ = (n : ℝ≥0∞) * ENNReal.ofReal a + ENNReal.ofReal R * ENNReal.ofReal b := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast,
          ENNReal.ofReal_mul hR.le]
    _ ≤ (n : ℝ≥0∞) * (∫⁻ x in U, ‖u x‖ₑ) +
          ENNReal.ofReal R * Chapter02.bvVariationOn (fun x ↦ |u x|) U := by
        rw [hA]
        gcongr
    _ = ENNReal.ofReal R * Chapter02.bvVariationOn (fun x ↦ |u x|) U +
          (n : ℝ≥0∞) * ∫⁻ x in U, ‖u x‖ₑ :=
        add_comm _ _
/-- **Simon Ch. 2, 2.8, estimate (4) for one test field.** Let `u ∈ L¹(ℝⁿ)`, let `φ` be Lipschitz
with `0 ≤ φ ≤ 1`, compact support and `tsupport φ ⊆ U`, and let `g` be a Lipschitz `C_c` test
field with `sup |g| ≤ 1`. Then `∫ φ u div g ≤ |Du|(U) + ∫ |u| |Dφ|` in `[0, ∞]`. The field
`ψ = φ • g` is admissible for `bvVariationOn u U`, and wherever `φ` and `g` are differentiable
(a.e., by Rademacher) `div ψ = φ div g + Dφ[g]`, so `φ u div g ≤ u div ψ + |u| ‖Dφ‖` a.e. Since
`div ψ` vanishes off `tsupport ψ ⊆ U`, `∫ u div ψ = ∫_U u div ψ ≤ |Du|(U)`. -/
theorem Submission.bv_ext_ofReal_integral_cutoff_le : ∀ (n : ℕ) (U : Set (Rn n)) (u φ : Rn n → ℝ) (g : CompactlySupportedContinuousMap (Rn n) (Rn n)), IsOpen U → Integrable u volume → (∃ K, LipschitzWith K φ) → (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) → HasCompactSupport φ → tsupport φ ⊆ U → Chapter02.IsLipschitzTestField g → Chapter02.compactlySupportedSupNorm g ≤ 1 → ENNReal.ofReal (∫ x, φ x * u x * Chapter02.euclideanDivergence (g : Rn n → Rn n) x) ≤ Chapter02.bvVariationOn u U + ∫⁻ x, ‖u x‖ₑ * ‖fderiv ℝ φ x‖ₑ := by
  rintro n U u φ g - hu ⟨Kφ, hφ⟩ hφ01 hφcs hφU ⟨Kg, hg⟩ hgn
  -- Step 1: `‖g x‖ ≤ compactlySupportedSupNorm g ≤ 1`, and `‖φ x‖ ≤ 1`.
  have hg1 : ∀ x, ‖g x‖ ≤ 1 := by
    obtain ⟨C, hC⟩ := g.continuous.bounded_above_of_compact_support g.hasCompactSupport
    have hbdd : BddAbove (range fun x ↦ ‖g x‖) := ⟨C, by rintro _ ⟨y, rfl⟩; exact hC y⟩
    exact fun x ↦ (le_csSup hbdd ⟨x, rfl⟩).trans hgn
  have hφ1 : ∀ x, ‖φ x‖ ≤ 1 := fun x ↦ by
    rw [Real.norm_of_nonneg (hφ01 x).1]
    exact (hφ01 x).2
  -- Step 2: `ψ = φ • g` is `(Kφ + Kg)`-Lipschitz, compactly supported in `U`, and `‖ψ‖ ≤ 1`.
  set ψ : Rn n → Rn n := fun y ↦ φ y • g y with hψ_def
  have hψ : LipschitzWith (Kφ + Kg) ψ := by
    refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
    have hφxy : ‖φ x - φ y‖ ≤ Kφ * ‖x - y‖ := by
      simpa only [dist_eq_norm] using hφ.dist_le_mul x y
    have hgxy : ‖g x - g y‖ ≤ Kg * ‖x - y‖ := by
      simpa only [dist_eq_norm] using hg.dist_le_mul x y
    have hgx := hg1 x
    have hφy := hφ1 y
    have hsplit : ψ x - ψ y = (φ x - φ y) • g x + φ y • (g x - g y) := by
      simp only [hψ_def]
      rw [sub_smul, smul_sub, sub_add_sub_cancel]
    rw [dist_eq_norm, dist_eq_norm, hsplit]
    calc ‖(φ x - φ y) • g x + φ y • (g x - g y)‖
        ≤ ‖φ x - φ y‖ * ‖g x‖ + ‖φ y‖ * ‖g x - g y‖ := by
          rw [← norm_smul, ← norm_smul]
          exact norm_add_le _ _
      _ ≤ Kφ * ‖x - y‖ * 1 + 1 * (Kg * ‖x - y‖) := by gcongr
      _ = ((Kφ + Kg : ℝ≥0) : ℝ) * ‖x - y‖ := by push_cast; ring
  have hψcs : HasCompactSupport ψ := hφcs.smul_right
  have hψU : tsupport ψ ⊆ U := (tsupport_smul_subset_left φ (g : Rn n → Rn n)).trans hφU
  have hψ1 : ∀ x, ‖ψ x‖ ≤ 1 := fun x ↦ by
    calc ‖ψ x‖ = ‖φ x‖ * ‖g x‖ := norm_smul _ _
      _ ≤ 1 := (mul_le_of_le_one_left (norm_nonneg _) (hφ1 x)).trans (hg1 x)
  -- Step 3: `ψ` is admissible in `U`, and `∫_U u div ψ = ∫ u div ψ` since `div ψ = 0` off
  -- `tsupport ψ ⊆ U`.
  have hset : ∫ x in U, u x * Chapter02.euclideanDivergence ψ x =
      ∫ x, u x * Chapter02.euclideanDivergence ψ x := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ ?_
    rw [Function.notMem_support.mp fun h ↦
      hx (hψU (Chapter02.support_euclideanDivergence_subset ψ h)), mul_zero]
  have hadm : ENNReal.ofReal (∫ x, u x * Chapter02.euclideanDivergence ψ x) ≤
      Chapter02.bvVariationOn u U := by
    rw [← hset]
    exact Submission.bv_ext_ofReal_integral_le_bvVariationOn n U u ψ (Kφ + Kg) hψ hψcs hψU hψ1
  -- Steps 4–5: where `φ` and `g` are differentiable (a.e., Rademacher), the product rule gives
  -- `div ψ = φ div g + Dφ[g]`, so `φ u div g = u div ψ - u Dφ[g] ≤ u div ψ + |u| ‖Dφ‖`.
  have hpt : ∀ᵐ x ∂(volume : Measure (Rn n)),
      φ x * u x * Chapter02.euclideanDivergence (g : Rn n → Rn n) x ≤
        u x * Chapter02.euclideanDivergence ψ x + |u x| * ‖fderiv ℝ φ x‖ := by
    filter_upwards [hφ.ae_differentiableAt, hg.ae_differentiableAt] with x hφx hgx
    have hdiv : Chapter02.euclideanDivergence ψ x =
        φ x * Chapter02.euclideanDivergence (g : Rn n → Rn n) x + fderiv ℝ φ x (g x) :=
      Submission.bv_ext_euclideanDivergence_smul n φ g x hφx hgx
    have hD : ‖fderiv ℝ φ x (g x)‖ ≤ ‖fderiv ℝ φ x‖ := by
      simpa only [mul_one] using (fderiv ℝ φ x).le_opNorm_of_le (hg1 x)
    have hneg : -(u x * fderiv ℝ φ x (g x)) ≤ |u x| * ‖fderiv ℝ φ x‖ :=
      calc -(u x * fderiv ℝ φ x (g x)) ≤ |u x * fderiv ℝ φ x (g x)| := neg_le_abs _
        _ = |u x| * ‖fderiv ℝ φ x (g x)‖ := by rw [abs_mul, Real.norm_eq_abs]
        _ ≤ |u x| * ‖fderiv ℝ φ x‖ := by gcongr
    rw [hdiv]
    linarith
  -- Step 6: integrability, from `|φ| ≤ 1`, `|div g| ≤ n Kg`, `|div ψ| ≤ n (Kφ + Kg)` and
  -- `‖Dφ‖ ≤ Kφ`.
  have hint₁ : Integrable fun x ↦
      φ x * u x * Chapter02.euclideanDivergence (g : Rn n → Rn n) x :=
    (hu.bdd_mul hφ.continuous.aestronglyMeasurable (ae_of_all _ hφ1)).mul_bdd
      (Chapter02.measurable_euclideanDivergence _).aestronglyMeasurable
      (ae_of_all _ (Chapter02.norm_euclideanDivergence_le_of_lipschitz hg))
  have hint₂ : Integrable fun x ↦ u x * Chapter02.euclideanDivergence ψ x :=
    hu.mul_bdd (Chapter02.measurable_euclideanDivergence _).aestronglyMeasurable
      (ae_of_all _ (Chapter02.norm_euclideanDivergence_le_of_lipschitz hψ))
  have hint₃ : Integrable fun x ↦ |u x| * ‖fderiv ℝ φ x‖ :=
    hu.abs.mul_bdd (measurable_fderiv ℝ φ).norm.aestronglyMeasurable
      (ae_of_all _ fun x ↦ (norm_norm _).trans_le (norm_fderiv_le_of_lipschitz ℝ hφ))
  -- Step 7: integrate the a.e. inequality.
  have hle : ∫ x, φ x * u x * Chapter02.euclideanDivergence (g : Rn n → Rn n) x ≤
      (∫ x, u x * Chapter02.euclideanDivergence ψ x) + ∫ x, |u x| * ‖fderiv ℝ φ x‖ := by
    rw [← integral_add hint₂ hint₃]
    exact integral_mono_ae hint₁ (hint₂.add hint₃) hpt
  -- Step 8: pass to `[0, ∞]`, where `ofReal (∫ |u| ‖Dφ‖) = ∫⁻ ‖u‖ₑ ‖Dφ‖ₑ`.
  have hlint : ENNReal.ofReal (∫ x, |u x| * ‖fderiv ℝ φ x‖) =
      ∫⁻ x, ‖u x‖ₑ * ‖fderiv ℝ φ x‖ₑ := by
    rw [ofReal_integral_eq_lintegral_ofReal hint₃
      (ae_of_all _ fun x ↦ mul_nonneg (abs_nonneg _) (norm_nonneg _))]
    refine lintegral_congr fun x ↦ ?_
    rw [ENNReal.ofReal_mul (abs_nonneg _), ← Real.norm_eq_abs, ofReal_norm, ofReal_norm]
  calc ENNReal.ofReal (∫ x, φ x * u x * Chapter02.euclideanDivergence (g : Rn n → Rn n) x)
      ≤ ENNReal.ofReal ((∫ x, u x * Chapter02.euclideanDivergence ψ x) +
          ∫ x, |u x| * ‖fderiv ℝ φ x‖) := ENNReal.ofReal_le_ofReal hle
    _ ≤ ENNReal.ofReal (∫ x, u x * Chapter02.euclideanDivergence ψ x) +
          ENNReal.ofReal (∫ x, |u x| * ‖fderiv ℝ φ x‖) := ENNReal.ofReal_add_le
    _ ≤ Chapter02.bvVariationOn u U + ∫⁻ x, ‖u x‖ₑ * ‖fderiv ℝ φ x‖ₑ :=
      add_le_add hadm hlint.le
/-- **`|Du|(A) = 0` when `u = 0` a.e. on `A`** (Simon 2.8, proof, C0). For a measurable
`A ⊆ ℝⁿ` and `u` vanishing `Lⁿ`-a.e. on `A`, every term `∫_A u div g` of the supremum
`bvVariationOn u A` has an integrand that vanishes `(volume.restrict A)`-a.e.
(`ae_restrict_iff'`), so it is `ofReal 0 = 0`. A supremum of zeros is `0`. -/
theorem Submission.bv_ext_variation_eq_zero_of_ae_eq_zero : ∀ (n : ℕ) (A : Set (Rn n)) (u : Rn n → ℝ), MeasurableSet A → (∀ᵐ x ∂volume, x ∈ A → u x = 0) → Chapter02.bvVariationOn u A = 0 := by
  intro n A u hA hu
  -- Step 2: since `A` is measurable, `u = 0` holds `(volume.restrict A)`-a.e.
  have hu' : ∀ᵐ x ∂(volume.restrict A), u x = 0 := (ae_restrict_iff' hA).2 hu
  -- Step 1: `0 ≤ bvVariationOn u A`, so it suffices to bound every admissible term by `0`.
  refine le_antisymm (iSup_le fun g ↦ iSup_le fun _ ↦ iSup_le fun _ ↦ iSup_le fun _ ↦ ?_) bot_le
  -- Step 3: the integrand `u · div g` vanishes a.e. on `A`, so the term is `ofReal 0 = 0`.
  have h0 : ∫ x in A, u x * Chapter02.euclideanDivergence (g : Rn n → Rn n) x = 0 :=
    integral_eq_zero_of_ae (hu'.mono fun x hx ↦ by simp [hx])
  rw [h0, ENNReal.ofReal_zero]
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
/-- **Simon Ch. 2, Lemma 2.7 (p. 51), Poincaré inequality for BV**, with `C = 2^{n+1}(1 + θ⁻¹)`.
Exhaust `U` by convex open sets `O j` with margins `σ j → 0`
(`convex_open_exists_inner_exhaustion`) and mollify: `w j = ρ j * 1_U u` with normalized bump
kernels `ρ j` supported in `ball 0 (σ j)`. On `O j` the smooth Poincaré inequality, the mollifier
gradient bound `∫_{O j} |Dw j| ≤ |Du|(U)` and `diam (O j) ≤ diam U ≤ 2R` give
`∫_{O j} |w j - c_j| ≤ 2ⁿ 2R |Du|(U)` for the means `c_j`. Since `w j → 1_U u = u` in `L¹(O j)`
(`bv_mollifier_tendsto_L1`), this passes to `∫_U |u - ū| ≤ 2ⁿ 2R |Du|(U)`
(`mean_oscillation_lintegral_le_of_approx`), and the level-set hypothesis replaces the mean `ū` by
`β` at the cost of a factor `1 + θ⁻¹` (`poincare_level_set_lintegral_le`). -/
theorem Submission.bv_poincare_theorem : BVPoincare := by
  intro n θ δ hθ _ _ _
  refine ⟨2 ^ (n + 1) * (1 + θ⁻¹), by positivity, ?_⟩
  intro U R ξ u β hUo hUb hUc hR _ _ hUR hBV hlevel
  obtain ⟨-, hu, -⟩ := hBV
  -- B2: convex open sets `O j` increasing to `U`, with margins `σ j → 0`.
  obtain ⟨O, σ, hOmono, hOU, hσ, hO⟩ :=
    Submission.convex_open_exists_inner_exhaustion n U hUo hUc
  have hOsub : ∀ j, O j ⊆ U := fun j ↦ hOU ▸ subset_iUnion O j
  -- B3: normalized bump kernels `ρ j` supported in `ball 0 (σ j)`.
  obtain ⟨ρ, hρc, hρd, hρn, hρs, hρi, hρcs⟩ : ∃ ρ : ℕ → Rn n → ℝ, (∀ j, Continuous (ρ j)) ∧
      (∀ j (m : ℕ∞), ContDiff ℝ m (ρ j)) ∧ (∀ j x, 0 ≤ ρ j x) ∧
      (∀ j, Function.support (ρ j) ⊆ ball 0 (σ j)) ∧ (∀ j, ∫ x, ρ j x = 1) ∧
      ∀ j, HasCompactSupport (ρ j) := by
    let φ : ℕ → ContDiffBump (0 : Rn n) := fun j ↦
      ⟨σ j / 2, σ j, half_pos (hO j).2.2.1, half_lt_self (hO j).2.2.1⟩
    exact ⟨fun j ↦ (φ j).normed volume, fun j ↦ (φ j).continuous_normed,
      fun j _ ↦ (φ j).contDiff_normed, fun j ↦ (φ j).nonneg_normed,
      fun j ↦ (φ j).support_normed_eq.subset, fun j ↦ (φ j).integral_normed,
      fun j ↦ (φ j).hasCompactSupport_normed⟩
  -- The mollified functions `w j = ρ j * 1_U u` are `C¹`, hence integrable on the bounded `O j`.
  have hF : Integrable (U.indicator u) volume := (integrable_indicator_iff hUo.measurableSet).2 hu
  set w : ℕ → Rn n → ℝ := fun j ↦
    convolution (ρ j) (U.indicator u) (ContinuousLinearMap.lsmul ℝ ℝ) volume
  have hwC : ∀ j, ContDiff ℝ 1 (w j) := fun j ↦
    (hρcs j).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (hρd j 1)
      hF.locallyIntegrable
  have hwint : ∀ j, IntegrableOn (w j) (O j) volume := fun j ↦
    ((hwC j).continuous.continuousOn.integrableOn_compact
      (hUb.subset (hOsub j)).isCompact_closure).mono_set subset_closure
  -- B4, approximation: `∫⁻_{O j} ‖w j - u‖ₑ ≤ ∫⁻ ‖w j - 1_U u‖ₑ → 0`, as `1_U u = u` on `O j`.
  have he : Tendsto (fun j ↦ ∫⁻ x in O j, ‖w j x - u x‖ₑ) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (Submission.bv_mollifier_tendsto_L1 n (U.indicator u) ρ σ hF hρc hρn hρs hρi hσ)
      (fun j ↦ zero_le) fun j ↦ ?_
    calc ∫⁻ x in O j, ‖w j x - u x‖ₑ = ∫⁻ x in O j, ‖w j x - U.indicator u x‖ₑ :=
          setLIntegral_congr_fun (hO j).1.measurableSet fun x hx ↦ by
            rw [indicator_of_mem (hOsub j hx)]
      _ ≤ ∫⁻ x, ‖w j x - U.indicator u x‖ₑ := setLIntegral_le_lintegral _ _
  -- B3, uniform bound: smooth Poincaré on `O j`, `diam (O j) ≤ diam U ≤ 2R`, and the mollifier
  -- gradient bound `∫⁻_{O j} ‖D w j‖ₑ ≤ |Du|(U)`, valid as `closedBall x (σ j) ⊆ U` for `x ∈ O j`.
  have hdiam : Metric.diam U ≤ 2 * R :=
    (Metric.diam_mono hUR isBounded_closedBall).trans (Metric.diam_closedBall hR.le)
  have hK : ∀ j, ∫⁻ x in O j, ‖w j x - (volume (O j)).toReal⁻¹ * ∫ y in O j, w j y‖ₑ ≤
      ENNReal.ofReal (2 ^ n * (2 * R)) * Chapter02.bvVariationOn u U := by
    intro j
    calc ∫⁻ x in O j, ‖w j x - (volume (O j)).toReal⁻¹ * ∫ y in O j, w j y‖ₑ
        ≤ ENNReal.ofReal (2 ^ n * Metric.diam (O j)) * ∫⁻ x in O j, ‖fderiv ℝ (w j) x‖ₑ :=
          Submission.convex_poincare_smooth_lintegral_le n (O j) (w j) (hO j).1
            (hUb.subset (hOsub j)) (hO j).2.1 (hwC j)
      _ ≤ ENNReal.ofReal (2 ^ n * (2 * R)) * Chapter02.bvVariationOn u U := by
          gcongr
          · exact (Metric.diam_mono (hOsub j) hUb).trans hdiam
          · exact Submission.bv_mollifier_fderiv_lintegral_le n U (O j) u (ρ j) (σ j) hUo hu
              (hρd j 2) (hρn j) (hρs j) (hρi j) (hO j).2.2.2
  -- B4, limit: `∫⁻_U ‖u - ū‖ₑ ≤ 2ⁿ (2R) |Du|(U)` for the mean `ū` of `u` over `U`.
  have hmean := Submission.mean_oscillation_lintegral_le_of_approx n U u O w _
    hUb.measure_lt_top hu (fun j ↦ (hO j).1.measurableSet) hOmono hOU hwint he hK
  -- B5: from the mean `ū` to `β`.
  calc ∫⁻ x in U, ‖u x - β‖ₑ
      ≤ ENNReal.ofReal (1 + θ⁻¹) * ∫⁻ x in U, ‖u x - (volume U).toReal⁻¹ * ∫ y in U, u y‖ₑ :=
        Submission.poincare_level_set_lintegral_le n U u θ β _ hUo.measurableSet
          (Integrable.aemeasurable hu) hθ hlevel
    _ ≤ ENNReal.ofReal (1 + θ⁻¹) *
          (ENNReal.ofReal (2 ^ n * (2 * R)) * Chapter02.bvVariationOn u U) := by
        gcongr
    _ = ENNReal.ofReal (2 ^ (n + 1) * (1 + θ⁻¹) * R) * Chapter02.bvVariationOn u U := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring
/-- **Simon Ch. 2, Lemma 5.11 (p. 65), integrability of the stable second-variation integrand.**
Let `M` be measurable with `y ↦ P_y` continuous on `M`, `X` the initial velocity of `φ`, `C¹` and
vanishing off the closed set `K`, `M ∩ K` compact with `Hⁿ(M ∩ K) < ∞`, and
`η · D_τ X(y) = -X(y) · B_y(τ, η)` for `y ∈ M` and `τ, η ∈ T_y M`. Then the integrand
`∑ᵢ |(D_{τᵢ}X)^⊥|² - ∑_{i,j} (X · B(τᵢ, τⱼ))²` vanishes on `M \ K` and is `Hⁿ`-integrable on `M`.
The frame `τ` is chosen pointwise, so the integrand is first written frame-free on `M` as
`tr(DX* (I - P) DX ∘ P) - tr(DX* P DX ∘ P)`, using `∑ᵢ τᵢ · L τᵢ = tr(L ∘ P)`, the hypothesis and
Parseval in `T_y M`. This is continuous on `M`, hence measurable and bounded on `M ∩ K`. -/
theorem Submission.stable_second_variation_integrand_integrableOn : ∀ (n N : ℕ) (M K : Set (Rn N)) (φ : ℝ → Rn N → Rn N), MeasurableSet M → ContinuousOn (tangentProjection M) M → ContDiff ℝ 1 (initialVelocity φ) → IsClosed K → (∀ x ∉ K, initialVelocity φ x = 0) → IsCompact (M ∩ K) → μHE[n] (M ∩ K) < ⊤ → (∀ y ∈ M, ∀ τ ∈ tangentSpace M y, ∀ η ∈ tangentSpace M y, inner ℝ η (fderiv ℝ (initialVelocity φ) y τ) = -inner ℝ (initialVelocity φ y) (secondFundamentalForm M y τ η)) → (∀ y ∈ M, y ∉ K → stableSecondVariationIntegrand M φ y = 0) ∧ IntegrableOn (stableSecondVariationIntegrand M φ) M μHE[n] := by
  intro n N M K φ hM hP hX hK hXK hMK hfin hB
  -- Step 1: `DX = 0` off `K`, since `X = 0` on the open set `Kᶜ`.
  have hD0 : ∀ y, y ∉ K → fderiv ℝ (initialVelocity φ) y = 0 := by
    intro y hy
    have hev : initialVelocity φ =ᶠ[𝓝 y] fun _ => (0 : Rn N) := by
      filter_upwards [hK.isOpen_compl.mem_nhds hy] with x hx using hXK x hx
    rw [hev.fderiv_eq, fderiv_const_apply]
  -- Step 2: conclusion (i), as `X(y) = 0` and `DX(y) = 0` for `y ∉ K`.
  have hS0 : ∀ y ∈ M, y ∉ K → stableSecondVariationIntegrand M φ y = 0 := by
    intro y _ hy
    simp [stableSecondVariationIntegrand, normalPart, hD0 y hy, hXK y hy]
  refine ⟨hS0, ?_⟩
  -- Step 3: frame sums are traces, `∑ᵢ ⟨τᵢ, L τᵢ⟩ = tr (L ∘ P_y)`: write `P_y = ι ∘ q_y`, use
  -- cyclicity of the trace and the trace formula in the orthonormal basis `τ` of `T_y`.
  have htr : ∀ (y : Rn N) (L : Rn N →L[ℝ] Rn N),
      ∑ i, inner ℝ (tangentFrame M y i) (L (tangentFrame M y i)) =
        LinearMap.trace ℝ (Rn N) (L ∘L tangentProjection M y).toLinearMap := by
    intro y L
    have hLP : (L ∘L tangentProjection M y).toLinearMap =
        (L.toLinearMap ∘ₗ (tangentSpace M y).subtype) ∘ₗ
          (tangentSpace M y).orthogonalProjectionOnto.toLinearMap := rfl
    rw [hLP, LinearMap.trace_comp_comm',
      LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ (tangentSpace M y))]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe,
      Submodule.coe_subtype, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
    rfl
  -- Step 4: on `M` the integrand `S` equals `F := tr (DX* (I - P) DX ∘ P) - tr (DX* P DX ∘ P)`.
  let F : Rn N → ℝ := fun y =>
    LinearMap.trace ℝ (Rn N) ((ContinuousLinearMap.adjoint (fderiv ℝ (initialVelocity φ) y) ∘L
        (ContinuousLinearMap.id ℝ (Rn N) - tangentProjection M y) ∘L
          fderiv ℝ (initialVelocity φ) y) ∘L tangentProjection M y).toLinearMap -
      LinearMap.trace ℝ (Rn N) ((ContinuousLinearMap.adjoint (fderiv ℝ (initialVelocity φ) y) ∘L
        tangentProjection M y ∘L fderiv ℝ (initialVelocity φ) y) ∘L
          tangentProjection M y).toLinearMap
  have hSF : ∀ y ∈ M, stableSecondVariationIntegrand M φ y = F y := by
    intro y hy
    -- (a) `v - P v ⊥ P v`.
    have horth : ∀ v : Rn N,
        inner ℝ (v - tangentProjection M y v) (tangentProjection M y v) = 0 := fun v =>
      Submodule.starProjection_inner_eq_zero v _
        (Submodule.starProjection_apply_mem (tangentSpace M y) v)
    -- (b) `‖(DX τᵢ)^⊥‖² = ⟨τᵢ, DX* (I - P) DX τᵢ⟩`.
    have h1 : ∀ i, ‖normalPart M y (fderiv ℝ (initialVelocity φ) y (tangentFrame M y i))‖ ^ 2 =
        inner ℝ (tangentFrame M y i)
          ((ContinuousLinearMap.adjoint (fderiv ℝ (initialVelocity φ) y) ∘L
            (ContinuousLinearMap.id ℝ (Rn N) - tangentProjection M y) ∘L
              fderiv ℝ (initialVelocity φ) y) (tangentFrame M y i)) := by
      intro i
      set v := fderiv ℝ (initialVelocity φ) y (tangentFrame M y i)
      set P := tangentProjection M y
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
        ContinuousLinearMap.comp_apply, sub_apply, ContinuousLinearMap.id_apply, normalPart,
        ← real_inner_self_eq_norm_sq]
      have e1 : inner ℝ (v - P v) (v - P v) = inner ℝ v (v - P v) - inner ℝ (P v) (v - P v) :=
        inner_sub_left _ _ _
      have e2 : inner ℝ (P v) (v - P v) = inner ℝ (v - P v) (P v) := real_inner_comm _ _
      rw [e1, e2, horth v, sub_zero]
    -- (c) by (h) and Parseval in `T_y`, `∑ⱼ ⟨X, B(τᵢ, τⱼ)⟩² = ‖P DX τᵢ‖² = ⟨τᵢ, DX* P DX τᵢ⟩`.
    have h2 : ∀ i, ∑ j, inner ℝ (initialVelocity φ y)
          (secondFundamentalForm M y (tangentFrame M y i) (tangentFrame M y j)) ^ 2 =
        inner ℝ (tangentFrame M y i)
          ((ContinuousLinearMap.adjoint (fderiv ℝ (initialVelocity φ) y) ∘L
            tangentProjection M y ∘L fderiv ℝ (initialVelocity φ) y) (tangentFrame M y i)) := by
      intro i
      set b := stdOrthonormalBasis ℝ (tangentSpace M y)
      set v := fderiv ℝ (initialVelocity φ) y (tangentFrame M y i)
      have hsq : ∀ j, inner ℝ (initialVelocity φ y)
          (secondFundamentalForm M y (tangentFrame M y i) (tangentFrame M y j)) ^ 2 =
          inner ℝ (b j) ((tangentSpace M y).orthogonalProjectionOnto v) ^ 2 := by
        intro j
        have h := hB y hy (tangentFrame M y i) (b i).2 (tangentFrame M y j) (b j).2
        rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
        change _ = inner ℝ (tangentFrame M y j)
          (fderiv ℝ (initialVelocity φ) y (tangentFrame M y i)) ^ 2
        rw [h, neg_sq]
      rw [Finset.sum_congr rfl fun j _ => hsq j, OrthonormalBasis.sum_sq_inner_right,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
        ContinuousLinearMap.comp_apply]
      have hn : ‖(tangentSpace M y).orthogonalProjectionOnto v‖ = ‖tangentProjection M y v‖ := rfl
      have e1 := horth v
      rw [inner_sub_left] at e1
      rw [hn, ← real_inner_self_eq_norm_sq]
      linarith
    -- (d) sum over `i` and use step 3.
    show ∑ i, ‖normalPart M y (fderiv ℝ (initialVelocity φ) y (tangentFrame M y i))‖ ^ 2 -
        ∑ i, ∑ j, inner ℝ (initialVelocity φ y)
          (secondFundamentalForm M y (tangentFrame M y i) (tangentFrame M y j)) ^ 2 = F y
    rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_congr rfl fun i _ => h2 i, htr, htr]
  -- Step 5: `F` is continuous on `M`.
  have hDc : Continuous (fderiv ℝ (initialVelocity φ)) := hX.continuous_fderiv one_ne_zero
  have hDadj : Continuous fun y => ContinuousLinearMap.adjoint (fderiv ℝ (initialVelocity φ) y) :=
    (ContinuousLinearMap.adjoint : (Rn N →L[ℝ] Rn N) ≃ₗᵢ⋆[ℝ] (Rn N →L[ℝ] Rn N)).continuous.comp hDc
  have htrc : Continuous fun A : Rn N →L[ℝ] Rn N => LinearMap.trace ℝ (Rn N) A.toLinearMap :=
    (LinearMap.trace ℝ (Rn N) ∘ₗ ContinuousLinearMap.coeLM ℝ).continuous_of_finiteDimensional
  have hIP : ContinuousOn (fun y => ContinuousLinearMap.id ℝ (Rn N) - tangentProjection M y) M :=
    continuousOn_const.sub hP
  have hFc : ContinuousOn F M :=
    (htrc.comp_continuousOn
        ((hDadj.continuousOn.clm_comp (hIP.clm_comp hDc.continuousOn)).clm_comp hP)).sub
      (htrc.comp_continuousOn
        ((hDadj.continuousOn.clm_comp (hP.clm_comp hDc.continuousOn)).clm_comp hP))
  -- Step 6: `S = F` on `M`, so `S` is a.e.-strongly measurable for `Hⁿ ⌊ M`.
  have hSm : AEStronglyMeasurable (stableSecondVariationIntegrand M φ) (μHE[n].restrict M) := by
    refine (hFc.aestronglyMeasurable hM).congr ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' hM]
    exact Filter.Eventually.of_forall fun y hy => (hSF y hy).symm
  -- Step 7: `|S| = |F| ≤ C` on the compact set `M ∩ K`.
  obtain ⟨C, hC⟩ := hMK.exists_bound_of_continuousOn (hFc.mono inter_subset_left)
  -- Step 8: `S` is integrable on `K ∩ M`, which has finite measure.
  have hKm : MeasurableSet K := hK.measurableSet
  have hint : IntegrableOn (stableSecondVariationIntegrand M φ) (K ∩ M) μHE[n] := by
    have hKfin : (μHE[n].restrict M) K ≠ ⊤ := by
      rw [Measure.restrict_apply hKm, inter_comm]
      exact hfin.ne
    have hbdd : ∀ᵐ y ∂((μHE[n].restrict M).restrict K),
        ‖stableSecondVariationIntegrand M φ y‖ ≤ C := by
      rw [Measure.restrict_restrict hKm, ae_restrict_iff' (hKm.inter hM)]
      exact Filter.Eventually.of_forall fun y hy => hSF y hy.2 ▸ hC y ⟨hy.2, hy.1⟩
    have h := Measure.integrableOn_of_bounded hKfin hSm hbdd
    rwa [IntegrableOn, Measure.restrict_restrict hKm] at h
  -- Step 9: `S = 0` on `M \ K`, so integrability extends to `M`.
  exact hint.of_forall_sdiff_eq_zero hM fun y hy => hS0 y hy.1 fun hyK => hy.2 ⟨hyK, hy.1⟩
/-- **Simon Ch. 2, Lemma 5.11 (p. 65), pointwise integrand identity.** With `X`, `Z` the initial
velocity and acceleration of `φ`, `τᵢ` the orthonormal frame of `T_y M`, `B_y` the second
fundamental form and `H` the mean curvature: if `B_y` is symmetric on `T_y M`,
`η · D_τ X(y) = -X(y) · B_y(τ, η)` for `τ, η ∈ T_y M` (4.24 with `X` normal), and `X(y) · H(y) = 0`
(5.5(2)), then the 5.4 integrand at `y` is `div_M Z(y)` plus the 5.11 integrand. Indeed
`div_M X = -X · H = 0` and `(τᵢ · D_{τⱼ}X)(τⱼ · D_{τᵢ}X) = (X · B(τᵢ, τⱼ))²`. -/
theorem Submission.second_variation_integrand_eq_div_accel_add_stable : ∀ (N : ℕ) (M : Set (Rn N)) (φ : ℝ → Rn N → Rn N) (y : Rn N), (∀ τ ∈ tangentSpace M y, ∀ η ∈ tangentSpace M y, secondFundamentalForm M y τ η = secondFundamentalForm M y η τ) → (∀ τ ∈ tangentSpace M y, ∀ η ∈ tangentSpace M y, inner ℝ η (fderiv ℝ (initialVelocity φ) y τ) = -inner ℝ (initialVelocity φ y) (secondFundamentalForm M y τ η)) → inner ℝ (initialVelocity φ y) (meanCurvature M y) = 0 → secondVariationIntegrand M φ y = tangentialDivergence M (initialAcceleration φ) y + stableSecondVariationIntegrand M φ y := by
  intro N M φ y hS hN hH
  -- Step 1: each frame vector `τᵢ` lies in `T_y M`.
  have hmem : ∀ i, tangentFrame M y i ∈ tangentSpace M y := fun i ↦
    ((stdOrthonormalBasis ℝ (tangentSpace M y)) i).2
  -- Step 2: `div_M X(y) = ∑ᵢ τᵢ · D_{τᵢ}X(y) = -X(y) · ∑ᵢ B_y(τᵢ, τᵢ) = -X(y) · H(y) = 0`.
  have hdiv : tangentialDivergence M (initialVelocity φ) y = 0 := by
    have h : tangentialDivergence M (initialVelocity φ) y =
        -inner ℝ (initialVelocity φ y) (meanCurvature M y) := by
      rw [tangentialDivergence, meanCurvature, inner_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ hN _ (hmem i) _ (hmem i)
    rw [h, hH, neg_zero]
  -- Step 3: `(τᵢ · D_{τⱼ}X)(τⱼ · D_{τᵢ}X) = (-X · B(τᵢ, τⱼ))² = (X · B(τᵢ, τⱼ))²`, by the normal
  -- identity applied twice and the symmetry of `B_y`.
  have hcross : ∀ i j,
      inner ℝ (tangentFrame M y i) (fderiv ℝ (initialVelocity φ) y (tangentFrame M y j)) *
        inner ℝ (tangentFrame M y j) (fderiv ℝ (initialVelocity φ) y (tangentFrame M y i)) =
      inner ℝ (initialVelocity φ y)
        (secondFundamentalForm M y (tangentFrame M y i) (tangentFrame M y j)) ^ 2 := by
    intro i j
    rw [hN _ (hmem j) _ (hmem i), hN _ (hmem i) _ (hmem j), hS _ (hmem j) _ (hmem i)]
    ring
  -- Step 4: substitute both identities into the 5.4 integrand and regroup.
  simp only [secondVariationIntegrand, stableSecondVariationIntegrand, hdiv, hcross]
  ring
/-- **Regularity and support of the initial velocity and acceleration** (Simon Ch. 2, 5.1–5.2,
pp. 61–62). If `φ` is an admissible `C^r` deformation of `U` fixing the outside of the compact set
`K ⊆ U`, then `X = initialVelocity φ` is `C^{r-1}` and `Z = initialAcceleration φ` is `C^{r-2}` on
all of `ℝᴺ`, and both vanish off `K`; this is stated for `r = 2` and `r = 3`. With
`Φ(t, x) = φ t x` and `e = (1, 0)`, the chain rule along `s ↦ (s, x)` gives `X(x) = DΦ(0, x) e`
and `Z(x) = D²Φ(0, x) e e` for `x ∈ U`. Off `K`, `t ↦ φ t x` is constant on `(-1, 1)`, so
`X = Z = 0` on the open set `Kᶜ`. Since `U ∪ Kᶜ = ℝᴺ` and `ContDiff` is local, `X` and `Z` are
`C^{r-1}` and `C^{r-2}` on `ℝᴺ`. -/
theorem Submission.deformation_velocity_acceleration_regularity : (∀ (N : ℕ) (U K : Set (Rn N)) (φ : ℝ → Rn N → Rn N), IsAdmissibleDeformation 2 U K φ → ContDiff ℝ 1 (initialVelocity φ) ∧ ∀ x ∉ K, initialVelocity φ x = 0) ∧ ∀ (N : ℕ) (U K : Set (Rn N)) (φ : ℝ → Rn N → Rn N), IsAdmissibleDeformation 3 U K φ → ContDiff ℝ 2 (initialVelocity φ) ∧ ContDiff ℝ 1 (initialAcceleration φ) ∧ ∀ x ∉ K, initialVelocity φ x = 0 ∧ initialAcceleration φ x = 0 := by
  -- Steps 1-6 for an arbitrary order `r`; step 7 specialises to `r = 2, 3`.
  have key : ∀ (N : ℕ) (r : ℕ∞) (U K : Set (Rn N)) (φ : ℝ → Rn N → Rn N),
      IsAdmissibleDeformation r U K φ →
      (∀ x ∉ K, initialVelocity φ x = 0 ∧ initialAcceleration φ x = 0) ∧
      (∀ k : ℕ, ((k + 1 : ℕ) : WithTop ℕ∞) ≤ (r : WithTop ℕ∞) →
        ContDiff ℝ k (initialVelocity φ)) ∧
      (∀ k : ℕ, ((k + 2 : ℕ) : WithTop ℕ∞) ≤ (r : WithTop ℕ∞) →
        ContDiff ℝ k (initialAcceleration φ)) := by
    intro N r U K φ hφ
    obtain ⟨hU, hK, hKU, hC, -, hfix, -⟩ := hφ
    set Φ : ℝ × Rn N → Rn N := fun p ↦ φ p.1 p.2
    set O : Set (ℝ × Rn N) := Ioo (-1 : ℝ) 1 ×ˢ U
    have hO : IsOpen O := isOpen_Ioo.prod hU
    have hIoo0 : Ioo (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
    -- Step 2: chain rule along the slice `s ↦ (s, x)`.
    have htime : ∀ (t : ℝ) (x : Rn N), DifferentiableAt ℝ Φ (t, x) →
        HasDerivAt (fun s ↦ φ s x) (fderiv ℝ Φ (t, x) ((1 : ℝ), (0 : Rn N))) t := by
      intro t x h
      exact h.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
    -- Step 5: vanishing off `K`.
    have hderiv_off : ∀ x ∉ K, ∀ t ∈ Ioo (-1 : ℝ) 1, deriv (fun s ↦ φ s x) t = 0 := by
      intro x hx t ht
      have : (fun s ↦ φ s x) =ᶠ[𝓝 t] fun _ ↦ x := by
        filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
        exact hfix s hs x hx
      rw [this.deriv_eq, deriv_const]
    have hvan : ∀ x ∉ K, initialVelocity φ x = 0 ∧ initialAcceleration φ x = 0 := by
      intro x hx
      refine ⟨hderiv_off x hx 0 (by norm_num), ?_⟩
      have : (fun t ↦ deriv (fun s ↦ φ s x) t) =ᶠ[𝓝 0] fun _ ↦ (0 : Rn N) := by
        filter_upwards [hIoo0] with t ht
        exact hderiv_off x hx t ht
      unfold initialAcceleration
      rw [this.deriv_eq, deriv_const]
    -- Step 6: patching over `U ∪ Kᶜ = ℝᴺ`.
    have glue : ∀ (k : ℕ) (F : Rn N → Rn N), ContDiffOn ℝ k F U → (∀ x ∉ K, F x = 0) →
        ContDiff ℝ k F := by
      intro k F hF hF0
      refine contDiff_iff_contDiffAt.2 fun x ↦ ?_
      by_cases hx : x ∈ U
      · exact hF.contDiffAt (hU.mem_nhds hx)
      · have hxK : x ∉ K := fun h ↦ hx (hKU h)
        have : F =ᶠ[𝓝 x] fun _ ↦ (0 : Rn N) := by
          filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hxK] with y hy
          exact hF0 y hy
        exact contDiffAt_const.congr_of_eventuallyEq this
    -- The smooth slice `j x = (0, x)` maps `U` into `O`.
    have hj : ContDiffOn ℝ ⊤ (fun x : Rn N ↦ ((0 : ℝ), x)) U :=
      (contDiff_const.prodMk contDiff_id).contDiffOn
    have hjmaps : MapsTo (fun x : Rn N ↦ ((0 : ℝ), x)) U O := fun x hx ↦
      ⟨⟨by norm_num, by norm_num⟩, hx⟩
    refine ⟨hvan, ?_, ?_⟩
    · -- Steps 1-3: `X = (DΦ · e) ∘ j` on `U`.
      intro k hk
      have hD : ContDiffOn ℝ k (fderiv ℝ Φ) O := hC.fderiv_of_isOpen hO (by exact_mod_cast hk)
      have hg : ContDiffOn ℝ k (fun p ↦ fderiv ℝ Φ p ((1 : ℝ), (0 : Rn N))) O :=
        hD.clm_apply contDiffOn_const
      have hXU : ContDiffOn ℝ k
          (fun x : Rn N ↦ fderiv ℝ Φ ((0 : ℝ), x) ((1 : ℝ), (0 : Rn N))) U :=
        hg.comp (hj.of_le le_top) hjmaps
      refine glue k _ (hXU.congr fun x hx ↦ ?_) (fun x hx ↦ (hvan x hx).1)
      have hdiff : DifferentiableAt ℝ Φ ((0 : ℝ), x) :=
        (hC.contDiffAt (hO.mem_nhds (hjmaps hx))).differentiableAt (by
          intro h; rw [h] at hk; exact absurd hk (by norm_num))
      exact (htime 0 x hdiff).deriv
    · -- Steps 1 and 4: `Z = (D²Φ · e · e) ∘ j` on `U`.
      intro k hk
      have hD1 : ContDiffOn ℝ (k + 1 : ℕ) (fderiv ℝ Φ) O :=
        hC.fderiv_of_isOpen hO (le_of_eq_of_le (by push_cast; ring) hk)
      have hD2 : ContDiffOn ℝ k (fderiv ℝ (fderiv ℝ Φ)) O :=
        hD1.fderiv_of_isOpen hO (by push_cast; exact le_rfl)
      have hg : ContDiffOn ℝ k
          (fun p ↦ fderiv ℝ (fderiv ℝ Φ) p ((1 : ℝ), (0 : Rn N)) ((1 : ℝ), (0 : Rn N))) O :=
        (hD2.clm_apply contDiffOn_const).clm_apply contDiffOn_const
      have hZU : ContDiffOn ℝ k (fun x : Rn N ↦
          fderiv ℝ (fderiv ℝ Φ) ((0 : ℝ), x) ((1 : ℝ), (0 : Rn N)) ((1 : ℝ), (0 : Rn N))) U :=
        hg.comp (hj.of_le le_top) hjmaps
      refine glue k _ (hZU.congr fun x hx ↦ ?_) (fun x hx ↦ (hvan x hx).2)
      have hdiffΦ : ∀ t ∈ Ioo (-1 : ℝ) 1, DifferentiableAt ℝ Φ (t, x) := by
        intro t ht
        exact (hC.contDiffAt (hO.mem_nhds ⟨ht, hx⟩)).differentiableAt (by
          intro h; rw [h] at hk; exact absurd hk (by norm_num))
      have hEq : (fun t ↦ deriv (fun s ↦ φ s x) t) =ᶠ[𝓝 0]
          fun t ↦ fderiv ℝ Φ (t, x) ((1 : ℝ), (0 : Rn N)) := by
        filter_upwards [hIoo0] with t ht
        exact (htime t x (hdiffΦ t ht)).deriv
      have hdiffD : DifferentiableAt ℝ (fderiv ℝ Φ) ((0 : ℝ), x) :=
        (hD1.contDiffAt (hO.mem_nhds (hjmaps hx))).differentiableAt (by simp)
      have hgd : HasFDerivAt (fun p ↦ fderiv ℝ Φ p ((1 : ℝ), (0 : Rn N)))
          ((fderiv ℝ (fderiv ℝ Φ) ((0 : ℝ), x)).flip ((1 : ℝ), (0 : Rn N))) ((0 : ℝ), x) := by
        simpa using hdiffD.hasFDerivAt.clm_apply
          (hasFDerivAt_const ((1 : ℝ), (0 : Rn N)) ((0 : ℝ), x))
      have hcomp := hgd.comp_hasDerivAt (0 : ℝ)
        ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const 0 x))
      unfold initialAcceleration
      rw [hEq.deriv_eq]
      exact hcomp.deriv
  refine ⟨fun N U K φ hφ ↦ ?_, fun N U K φ hφ ↦ ?_⟩
  · obtain ⟨hvan, hX, -⟩ := key N 2 U K φ hφ
    exact ⟨hX 1 (by norm_num), fun x hx ↦ (hvan x hx).1⟩
  · obtain ⟨hvan, hX, hZ⟩ := key N 3 U K φ hφ
    exact ⟨hX 2 (by norm_num), hZ 1 (by norm_num), hvan⟩
/-- **Local compactness of a Simon submanifold, closed-ball form.** If `M ⊆ ℝᴺ` is an
`n`-dimensional `C^r` Simon submanifold (Simon 4.1), `y ∈ M` and `O ∋ y` is open, then there is
`ρ > 0` with `B̄(y, ρ) ⊆ O` and `M ∩ B̄(y, ρ)` compact. Take a chart `(V, W, ψ)` with `y ∈ W` and
`ρ = ε/2` for an open ball `B(y, ε) ⊆ O ∩ W`. Since `B̄(y, ρ) ⊆ W` and `ψ(V) = W ∩ M`,
`M ∩ B̄(y, ρ) = ψ(V ∩ ψ⁻¹(B̄(y, ρ)))`; relative properness makes `V ∩ ψ⁻¹(B̄(y, ρ))` compact, and
`ψ` is continuous on `V`. -/
theorem Submission.simon_submanifold_exists_closedBall_isCompact_inter : ∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)), Chapter02.IsSimonSubmanifold (E := Rn n) r M → ∀ y ∈ M, ∀ O : Set (Rn N), IsOpen O → y ∈ O → ∃ ρ : ℝ, 0 < ρ ∧ closedBall y ρ ⊆ O ∧ IsCompact (M ∩ closedBall y ρ) := by
  intro n N r M hM y hy O hO hyO
  -- Step 1: a chart `(V, W, ψ)` of `M` with `y ∈ W` (second conjunct of `IsSimonSubmanifold`).
  obtain ⟨V, W, ψ, hyW, hψ⟩ := hM.2 y hy
  -- Step 2: `B̄(y, ε/2) ⊆ B(y, ε) ⊆ O ∩ W`.
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hO.inter hψ.isOpen_target) y ⟨hyO, hyW⟩
  have hsub : closedBall y (ε / 2) ⊆ O ∩ W :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
  refine ⟨ε / 2, half_pos hε, hsub.trans inter_subset_left, ?_⟩
  -- Step 3: `M ∩ B̄(y, ε/2) = ψ(V ∩ ψ⁻¹(B̄(y, ε/2)))`, as `B̄(y, ε/2) ⊆ W` and `ψ(V) = W ∩ M`.
  have himage : M ∩ closedBall y (ε / 2) = ψ '' (V ∩ ψ ⁻¹' closedBall y (ε / 2)) := by
    ext z
    constructor
    · rintro ⟨hzM, hzB⟩
      have hz : z ∈ ψ '' V := by
        rw [hψ.image_eq]
        exact ⟨(hsub hzB).2, hzM⟩
      obtain ⟨x, hxV, rfl⟩ := hz
      exact ⟨x, ⟨hxV, hzB⟩, rfl⟩
    · rintro ⟨x, ⟨hxV, hxB⟩, rfl⟩
      have hx : ψ x ∈ W ∩ M := by
        rw [← hψ.image_eq]
        exact mem_image_of_mem ψ hxV
      exact ⟨hx.2, hxB⟩
  -- Steps 4–5: `B̄(y, ε/2)` is a compact subset of `W`, so relative properness makes
  -- `V ∩ ψ⁻¹(B̄(y, ε/2))` compact; its image under `ψ`, continuous on `V`, is compact.
  rw [himage]
  exact (hψ.isCompact_source_inter_preimage _ (isCompact_closedBall y (ε / 2))
    (hsub.trans inter_subset_right)).image_of_continuousOn
    (hψ.contDiffOn.continuousOn.mono inter_subset_left)
/-- **Fundamental lemma for test vector fields.** Let `M ⊆ ℝᴺ` be measurable, `U` open and `F`
continuous on `M`. Assume (P) `μ(M ∩ O) > 0` for every open `O` meeting `M`, (L) each `y ∈ M` has
arbitrarily small closed balls `B̄(y, ρ)` with `M ∩ B̄(y, ρ)` compact, and (T) `∫_M ⟨Y, F⟩ dμ = 0`
(with `⟨Y, F⟩` integrable on `M`) for every `C²` field `Y` with compact support in `U` and
`M ∩ spt Y` compact. Then `F = 0` on `M ∩ U`. If `e = F(y₀) ≠ 0`, continuity and (L) give `ρ > 0`
with `B̄(y₀, ρ) ⊆ U`, `M ∩ B̄(y₀, ρ)` compact and `⟨e, F⟩ > ‖e‖²/2` on `M ∩ B̄(y₀, ρ)`. For the
smooth bump `ζ` (`ζ = 1` on `B̄(y₀, ρ/2)`, `spt ζ = B̄(y₀, ρ)`), the field `Y = ζ e` is admissible
in (T), and `⟨Y, F⟩ = ζ ⟨e, F⟩ ≥ 0` on `M` is positive on `M ∩ B(y₀, ρ/2)`, which has positive
measure by (P). So `∫_M ⟨Y, F⟩ dμ > 0`, a contradiction. -/
theorem Submission.vector_field_eq_zero_of_integral_inner_test_fields : ∀ (N : ℕ) (μ : Measure (Rn N)) (M U : Set (Rn N)) (F : Rn N → Rn N), MeasurableSet M → IsOpen U → ContinuousOn F M → (∀ y ∈ M, ∀ O : Set (Rn N), IsOpen O → y ∈ O → 0 < μ (M ∩ O)) → (∀ y ∈ M, ∀ O : Set (Rn N), IsOpen O → y ∈ O → ∃ ρ : ℝ, 0 < ρ ∧ closedBall y ρ ⊆ O ∧ IsCompact (M ∩ closedBall y ρ)) → (∀ Y : Rn N → Rn N, ContDiff ℝ 2 Y → HasCompactSupport Y → tsupport Y ⊆ U → IsCompact (M ∩ tsupport Y) → IntegrableOn (fun y ↦ inner ℝ (Y y) (F y)) M μ ∧ ∫ y in M, inner ℝ (Y y) (F y) ∂μ = 0) → ∀ y ∈ M ∩ U, F y = 0 := by
  intro N μ M U F hM hU hF hP hL hT y₀ hy₀
  -- Step 1: suppose `e = F y₀ ≠ 0`.
  by_contra hne
  have he : 0 < ‖F y₀‖ := norm_pos_iff.2 hne
  -- Step 2 (continuity): `‖F y - F y₀‖ < ‖F y₀‖ / 2` on `M ∩ B(y₀, δ)`.
  obtain ⟨δ, hδ, hδF⟩ := Metric.continuousOn_iff.1 hF y₀ hy₀.1 (‖F y₀‖ / 2) (half_pos he)
  -- Step 3 (localization): `B̄(y₀, ρ) ⊆ U ∩ B(y₀, δ)` with `M ∩ B̄(y₀, ρ)` compact.
  obtain ⟨ρ, hρ, hρU, hρK⟩ :=
    hL y₀ hy₀.1 (U ∩ ball y₀ δ) (hU.inter isOpen_ball) ⟨hy₀.2, mem_ball_self hδ⟩
  -- Step 4 (key estimate): `⟨e, F y⟩ > ‖e‖² / 2` on `M ∩ B̄(y₀, ρ)`, by Cauchy–Schwarz.
  have hkey : ∀ y ∈ M, dist y y₀ ≤ ρ → ‖F y₀‖ ^ 2 / 2 < inner ℝ (F y₀) (F y) := by
    intro y hyM hyρ
    have h1 : ‖F y - F y₀‖ < ‖F y₀‖ / 2 := by
      rw [← dist_eq_norm]
      exact hδF y hyM (mem_ball.1 (hρU (mem_closedBall.2 hyρ)).2)
    have h2 : inner ℝ (F y₀) (F y) = ‖F y₀‖ ^ 2 + inner ℝ (F y₀) (F y - F y₀) := by
      rw [inner_sub_right, real_inner_self_eq_norm_sq]
      ring
    have h3 : -(‖F y₀‖ * ‖F y - F y₀‖) ≤ inner ℝ (F y₀) (F y - F y₀) :=
      (abs_le.1 (abs_real_inner_le_norm (F y₀) (F y - F y₀))).1
    have h4 : ‖F y₀‖ * ‖F y - F y₀‖ < ‖F y₀‖ * (‖F y₀‖ / 2) := mul_lt_mul_of_pos_left h1 he
    nlinarith
  -- Step 5 (bump function): `ζ = 1` on `B̄(y₀, ρ/2)`, `ζ = 0` off `B(y₀, ρ)`, `0 ≤ ζ`.
  let ζ : ContDiffBump y₀ := ⟨ρ / 2, ρ, half_pos hρ, half_lt_self hρ⟩
  -- Step 6 (test field): `Y = ζ • e` is admissible in (T).
  let Y : Rn N → Rn N := fun x ↦ ζ x • F y₀
  have hYc : ContDiff ℝ 2 Y := ζ.contDiff.smul contDiff_const
  have hYs : HasCompactSupport Y := ζ.hasCompactSupport.smul_right
  have hYt : tsupport Y ⊆ closedBall y₀ ρ :=
    (tsupport_smul_subset_left (fun x ↦ ζ x) fun _ ↦ F y₀).trans ζ.tsupport_eq.subset
  have hYU : tsupport Y ⊆ U := fun x hx ↦ (hρU (hYt hx)).1
  have hYK : IsCompact (M ∩ tsupport Y) := by
    have h : M ∩ tsupport Y = M ∩ closedBall y₀ ρ ∩ tsupport Y := by
      ext x
      exact ⟨fun hx ↦ ⟨⟨hx.1, hYt hx.2⟩, hx.2⟩, fun hx ↦ ⟨hx.1.1, hx.2⟩⟩
    rw [h]
    exact hρK.inter_right (isClosed_tsupport Y)
  -- Step 7 (apply (T)): `f = ⟨Y, F⟩ = ζ ⟨e, F⟩` is integrable on `M` with `∫_M f dμ = 0`.
  obtain ⟨hint, hzero⟩ := hT Y hYc hYs hYU hYK
  have hf : ∀ y, inner ℝ (Y y) (F y) = ζ y * inner ℝ (F y₀) (F y) := fun y ↦
    real_inner_smul_left _ _ _
  -- Step 8: `f ≥ 0` on `M`.
  have hnn : 0 ≤ᵐ[μ.restrict M] fun y ↦ inner ℝ (Y y) (F y) := by
    refine ae_restrict_of_forall_mem hM fun y hyM ↦ ?_
    show 0 ≤ inner ℝ (Y y) (F y)
    rw [hf]
    by_cases hyρ : dist y y₀ ≤ ρ
    · exact mul_nonneg ζ.nonneg ((half_pos (pow_pos he 2)).le.trans (hkey y hyM hyρ).le)
    · rw [ζ.zero_of_le_dist (not_le.1 hyρ).le, zero_mul]
  -- Step 9: `f > 0` on `M ∩ B(y₀, ρ/2)`, which has positive measure by (P).
  have hpos : 0 < μ (Function.support (fun y ↦ inner ℝ (Y y) (F y)) ∩ M) := by
    have hsub : M ∩ ball y₀ (ρ / 2) ⊆ Function.support (fun y ↦ inner ℝ (Y y) (F y)) ∩ M := by
      rintro y ⟨hyM, hyB⟩
      refine ⟨?_, hyM⟩
      rw [Function.mem_support, hf, ζ.one_of_mem_closedBall (ball_subset_closedBall hyB), one_mul]
      have hyρ : dist y y₀ ≤ ρ := (mem_ball.1 hyB).le.trans (half_le_self hρ.le)
      exact ((half_pos (pow_pos he 2)).trans (hkey y hyM hyρ)).ne'
    exact (hP y₀ hy₀.1 (ball y₀ (ρ / 2)) isOpen_ball (mem_ball_self (half_pos hρ))).trans_le
      (measure_mono hsub)
  -- Step 10: then `∫_M f dμ > 0`, contradicting `∫_M f dμ = 0`.
  have hint_pos := (setIntegral_pos_iff_support_of_nonneg_ae hnn hint).2 hpos
  rw [hzero] at hint_pos
  exact lt_irrefl 0 hint_pos
/-- **Euclidean divergence theorem for a field vanishing off a compact set.** If `V ⊆ ℝⁿ` is open,
`Q ⊆ V` is compact and `w : ℝⁿ → ℝⁿ` is `C¹` on `V` with `w = 0` on `V \ Q`, then
`∫_V trace Dw(x) dLⁿ(x) = 0`. The extension `W` of `w` by `0` off `V` is `C¹` on `ℝⁿ` with support
in `Q`, and `DW = Dw` on `V`, `DW = 0` off `Q`. Writing `trace DW = ∑ᵢ ⟨eᵢ, DW eᵢ⟩` in the standard
orthonormal basis `(eᵢ)`, each coordinate integral `∫ ⟨eᵢ, DW(x) eᵢ⟩ dx` vanishes by Mathlib's
integration by parts `LipschitzWith.integral_lineDeriv_mul_eq` against the constant function `1`. -/
theorem Submission.euclidean_setIntegral_trace_fderiv_eq_zero : ∀ (n : ℕ) (V Q : Set (Rn n)) (w : Rn n → Rn n), IsOpen V → IsCompact Q → Q ⊆ V → ContDiffOn ℝ 1 w V → (∀ x ∈ V, x ∉ Q → w x = 0) → ∫ x in V, LinearMap.trace ℝ (Rn n) (fderiv ℝ w x).toLinearMap = 0 := by
  intro n V Q w hV hQ hQV hw hw0
  -- Step 2 (extension by zero): `W = w` near each point of the open set `V`, and `W = 0` near
  -- each point of the open set `Qᶜ` (on `V \ Q` by hypothesis, off `V` by definition).
  let W : Rn n → Rn n := V.indicator w
  have hWV : ∀ x ∈ V, W =ᶠ[𝓝 x] w := fun x hx ↦
    Filter.eventuallyEq_of_mem (hV.mem_nhds hx) fun y hy ↦ indicator_of_mem hy w
  have hWQ : ∀ x ∉ Q, W =ᶠ[𝓝 x] fun _ ↦ 0 := fun x hx ↦
    Filter.eventuallyEq_of_mem (hQ.isClosed.isOpen_compl.mem_nhds hx) fun y hy ↦ by
      by_cases hyV : y ∈ V
      · simp [W, hyV, hw0 y hyV hy]
      · simp [W, hyV]
  -- Steps 3–4: `W` is `C¹` on `ℝⁿ = V ∪ Qᶜ` and has compact support (contained in `Q`).
  have hWc : ContDiff ℝ 1 W := contDiff_iff_contDiffAt.2 fun x ↦ by
    by_cases hx : x ∈ V
    · exact (hw.contDiffAt (hV.mem_nhds hx)).congr_of_eventuallyEq (hWV x hx)
    · exact contDiffAt_const.congr_of_eventuallyEq (hWQ x fun hxQ ↦ hx (hQV hxQ))
  have hWs : HasCompactSupport W := HasCompactSupport.intro hQ fun x hx ↦ (hWQ x hx).self_of_nhds
  -- Step 5: `DW = Dw` on `V` and `DW = 0` off `Q`.
  have hDV : ∀ x ∈ V, fderiv ℝ W x = fderiv ℝ w x := fun x hx ↦ (hWV x hx).fderiv_eq
  have hDQ : ∀ x ∉ Q, fderiv ℝ W x = 0 := fun x hx ↦ by
    rw [(hWQ x hx).fderiv_eq]
    simp
  -- Step 6: `∫_V trace Dw = ∫_V trace DW = ∫_{ℝⁿ} trace DW`, as `trace DW = 0` off `V ⊇ Q`.
  have h6a : ∫ x in V, LinearMap.trace ℝ (Rn n) (fderiv ℝ w x).toLinearMap
      = ∫ x in V, LinearMap.trace ℝ (Rn n) (fderiv ℝ W x).toLinearMap :=
    setIntegral_congr_fun hV.measurableSet fun x hx ↦ by rw [hDV x hx]
  have h6b : ∫ x in V, LinearMap.trace ℝ (Rn n) (fderiv ℝ W x).toLinearMap
      = ∫ x, LinearMap.trace ℝ (Rn n) (fderiv ℝ W x).toLinearMap :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [hDQ x fun hxQ ↦ hx (hQV hxQ)]
      simp
  -- Steps 7–8: `trace DW(x) = ∑ᵢ ⟨eᵢ, DW(x) eᵢ⟩` in the standard orthonormal basis `(eᵢ)`.
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have h8 : ∀ x, LinearMap.trace ℝ (Rn n) (fderiv ℝ W x).toLinearMap
      = ∑ i, inner ℝ (b i) (fderiv ℝ W x (b i)) := fun x ↦ by
    rw [LinearMap.trace_eq_sum_inner _ b]
    rfl
  -- Step 9: each summand is continuous with compact support, hence integrable.
  have h9 : ∀ i, Integrable (fun x ↦ inner ℝ (b i) (fderiv ℝ W x (b i))) := fun i ↦
    Continuous.integrable_of_hasCompactSupport
      (continuous_const.inner ((hWc.continuous_fderiv one_ne_zero).clm_apply continuous_const))
      ((hWs.fderiv_apply ℝ (b i)).comp_left (g := fun y : Rn n ↦ inner ℝ (b i) y)
        (inner_zero_right _))
  -- Steps 10–11: the coordinate `gᵢ = ⟨eᵢ, W⟩` is `C¹` with compact support, hence Lipschitz, and
  -- `Dgᵢ(x) eᵢ = ⟨eᵢ, DW(x) eᵢ⟩`. Integration by parts against `1` (whose line derivative is `0`)
  -- gives `0 = ∫ Dgᵢ(x)(-eᵢ) dx = -∫ ⟨eᵢ, DW(x) eᵢ⟩ dx`.
  have h10 : ∀ i, ∫ x, inner ℝ (b i) (fderiv ℝ W x (b i)) = 0 := fun i ↦ by
    let g : Rn n → ℝ := fun y ↦ inner ℝ (b i) (W y)
    have hgc : ContDiff ℝ 1 g := (innerSL ℝ (b i)).contDiff.comp hWc
    have hgs : HasCompactSupport g :=
      hWs.comp_left (g := fun y : Rn n ↦ inner ℝ (b i) y) (inner_zero_right _)
    obtain ⟨L, hL⟩ := hgc.lipschitzWith_of_hasCompactSupport hgs one_ne_zero
    have hibp := (LipschitzWith.const (α := Rn n) (1 : ℝ)).integral_lineDeriv_mul_eq
      (μ := volume) hL hgs (b i)
    have hd : ∀ x, lineDeriv ℝ g x (-b i) = -inner ℝ (b i) (fderiv ℝ W x (b i)) := fun x ↦ by
      have hx : HasFDerivAt g ((innerSL ℝ (b i)).comp (fderiv ℝ W x)) x :=
        (innerSL ℝ (b i)).hasFDerivAt.comp x ((hWc.differentiable one_ne_zero) x).hasFDerivAt
      rw [hx.differentiableAt.lineDeriv_eq_fderiv, hx.fderiv]
      simp
    have h0 : ∀ x, lineDeriv ℝ (fun _ : Rn n ↦ (1 : ℝ)) x (b i) = 0 := fun x ↦ by
      simp [lineDeriv]
    simp only [h0, zero_mul, integral_zero, hd, mul_one, integral_neg] at hibp
    exact neg_eq_zero.1 hibp.symm
  rw [h6a, h6b]
  simp_rw [h8]
  rw [integral_finsetSum _ fun i _ ↦ h9 i]
  exact Finset.sum_eq_zero fun i _ ↦ h10 i

/-- **Chart localization for the divergence identity** (Simon Ch. 2, 4.22(2)(*) and 4.30, p. 59,
in one chart via the area formula 3.2/3.5). Let `(V, W, ψ)` be a Simon local representation of class
`r ≥ 1` of a measurable `M ⊆ ℝᴺ`, `K ⊆ W` compact and `g = 0` on `M \ K`. If `w : ℝⁿ → ℝⁿ` is `C¹`
on `V`, `w = 0` at the points of `V` that `ψ` maps outside `K`, and `trace Dw = Jψ · (g ∘ ψ)` on
`V`, then `∫_M g dHⁿ = 0`. Restrict `∫_M` to the chart image `ψ(V) = W ∩ M`, pull it back to
`∫_V Jψ · (g ∘ ψ) dLⁿ` by the area formula, and apply the Euclidean divergence theorem
`Submission.euclidean_setIntegral_trace_fderiv_eq_zero` to `V`, `Q = V ∩ ψ⁻¹(K)` and `w`. -/
theorem Submission.chart_setIntegral_eq_zero_of_trace_fderiv_eq : ∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)) (V : Set (Rn n)) (W K : Set (Rn N)) (ψ : Rn n → Rn N) (g : Rn N → ℝ) (w : Rn n → Rn n), 1 ≤ r → Chapter02.IsSimonLocalRepresentation r M V W ψ → MeasurableSet M → IsCompact K → K ⊆ W → (∀ y ∈ M, y ∉ K → g y = 0) → ContDiffOn ℝ 1 w V → (∀ x ∈ V, ψ x ∉ K → w x = 0) → (∀ x ∈ V, LinearMap.trace ℝ (Rn n) (fderiv ℝ w x).toLinearMap = Chapter02.areaJacobianAt ψ x * g (ψ x)) → ∫ y in M, g y ∂μHE[n] = 0 := by
  classical
  /- Simon (3.2)/(3.5) in Bochner form: for an injective `Φ` with injective derivative on a
  measurable `s` and an arbitrary real weight `h`, `∫_{Φ(s)} h dHⁿ = ∫_s JΦ · (h ∘ Φ) dLⁿ`, where
  `JΦ = normDet DΦ`. This is the pinned SimonGMT theorem
  `Chapter02.integral_area_formula_of_injective_derivative`, whose module `Chapter02/WeightedArea`
  is not imported here; its kernel-checked proof (SimonGMT `Chapter02/AreaApproximation`,
  `AreaDerivative`, `AreaFormula`, `WeightedArea`, the derivative-control step adapted from
  Mathlib's `MeasureTheory/Function/Jacobian.lean`) is replayed as a local step. The image-measure
  part is the same replay as in the accepted node `Submission.coarea_chart_area_pullback`. No
  integrability of `h` is needed: both sides integrate `h` against one measure, transported along
  a measurable embedding. -/
/-- **Simon Ch. 2, §6 (p. 66), toward Theorem 6.4.** `J*_f(x) = 0` precisely when `df_x` has rank
`< m`: with `L = Df(x) ∘ ι : T_x M → ℝᵐ`, `L L*` is positive semidefinite, so `√det(L L*) = 0` iff
`L L*` is singular, iff `ker L* = (range L)ᗮ ≠ 0`, iff `range L ≠ ℝᵐ`. No hypothesis on `M`, `f` or
`x` is needed. -/
theorem Submission.c1_sard_coarea_jacobian_eq_zero_iff : ∀ (N m : ℕ) (M : Set (Rn N)) (f : Rn N → Rn m) (x : Rn N), coareaJacobian M f x = 0 ↔ Module.finrank ℝ (LinearMap.range ((fderiv ℝ f x).toLinearMap ∘ₗ (tangentSpace M x).subtype)) < m := by
  intro N m M f x
  -- `L = Df(x) ∘ ι : T_x M → ℝᵐ`; by definition `J*_f(x) = √det(L L*)`.
  set L : tangentSpace M x →ₗ[ℝ] Rn m := (fderiv ℝ f x).toLinearMap ∘ₗ (tangentSpace M x).subtype
  have hJ : coareaJacobian M f x = Real.sqrt (L ∘ₗ L.adjoint).det := rfl
  -- Step 1: `det(L L*) = (normDet L*)² ≥ 0`, as `L** = L`.
  have hdet : 0 ≤ (L ∘ₗ L.adjoint).det := by
    have hsq : L.adjoint.normDet ^ 2 = (L ∘ₗ L.adjoint).det := by
      simpa using L.adjoint.normDet_sq
    exact hsq ▸ sq_nonneg _
  -- Steps 2–4: `√det(L L*) = 0 ↔ det(L L*) = 0 ↔ ker(L L*) ≠ 0`, and `ker(L L*) = ker L*`.
  rw [hJ, Real.sqrt_eq_zero hdet, LinearMap.det_eq_zero_iff_ker_ne_bot,
    LinearMap.ker_self_comp_adjoint]
  -- Step 5: `ker L* = (range L)ᗮ`, which is `0` iff `range L = ℝᵐ`.
  rw [← LinearMap.orthogonal_range, ne_eq, Submodule.orthogonal_eq_bot_iff]
  -- Step 6: a subspace of `ℝᵐ` is proper iff its dimension is `< m = dim ℝᵐ`.
  have hm : Module.finrank ℝ (Rn m) = m := finrank_euclideanSpace_fin
  refine ⟨fun h ↦ (Submodule.finrank_lt h).trans_eq hm, fun h htop ↦ ?_⟩
  rw [htop, finrank_top, hm] at h
  exact lt_irrefl m h

/-- **Simon Ch. 2, §6 (pp. 66–67), toward Theorem 6.4.** If `f` is `C¹` on an open `U ⊇ M` and
the tangent projection `x ↦ P_x` is continuous on `M`, then `J*_f` is continuous on `M`: the
adjoint of the inclusion `T_x M → ℝᴺ` is the orthogonal projection onto `T_x M`, so
`df_x ∘ df_x* = Df(x) ∘ P_x ∘ Df(x)*`. Hence for every `y` the critical part
`M ∩ f⁻¹{y} ∩ {J*_f = 0}` of the fiber is relatively closed in `M`. -/
theorem Submission.c1_sard_coarea_jacobian_continuousOn : ∀ (N m : ℕ) (M U : Set (Rn N)) (f : Rn N → Rn m), IsOpen U → M ⊆ U → ContDiffOn ℝ 1 f U → ContinuousOn (tangentProjection M) M → ContinuousOn (coareaJacobian M f) M ∧ ∀ y : Rn m, ∃ F : Set (Rn N), IsClosed F ∧ M ∩ f ⁻¹' {y} ∩ {x | coareaJacobian M f x = 0} = M ∩ F := by
  intro N m M U f hU hMU hf hP
  -- `(Df(x) ∘ ι)(Df(x) ∘ ι)* = Df(x) ∘ (ι ∘ π) ∘ Df(x)*`, as `ι* = π` and `ι ∘ π = P_x`.
  have key : ∀ x, coareaJacobian M f x = Real.sqrt ((fderiv ℝ f x ∘L
      (tangentProjection M x ∘L ContinuousLinearMap.adjoint (fderiv ℝ f x))).det) := by
    intro x
    simp only [coareaJacobian]
    congr 2
    rw [ContinuousLinearMap.adjoint_comp, Submodule.adjoint_subtypeL]
    rfl
  have hJ : ContinuousOn (coareaJacobian M f) M := by
    have hD : ContinuousOn (fderiv ℝ f) M := (hf.continuousOn_fderiv_of_isOpen hU le_rfl).mono hMU
    have hD' : ContinuousOn (fun x ↦ ContinuousLinearMap.adjoint (fderiv ℝ f x)) M :=
      (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Rn N) (F := Rn m)).continuous.comp_continuousOn hD
    refine ContinuousOn.congr ?_ fun x _ ↦ key x
    exact Real.continuous_sqrt.comp_continuousOn
      (ContinuousLinearMap.continuous_det.comp_continuousOn (hD.clm_comp (hP.clm_comp hD')))
  refine ⟨hJ, fun y ↦ ?_⟩
  -- `S = M ∩ f⁻¹{y} ∩ {J*_f = 0}` satisfies `S = M ∩ closure S`, as `f` and `J*_f` are continuous
  -- on `M ⊇ S`.
  set S := M ∩ f ⁻¹' {y} ∩ {x | coareaJacobian M f x = 0}
  refine ⟨closure S, isClosed_closure, Subset.antisymm (fun x hx ↦ ⟨hx.1.1, subset_closure hx⟩) ?_⟩
  rintro x ⟨hxM, hxS⟩
  have hSM : S ⊆ M := fun z hz ↦ hz.1.1
  have hfx : f x ∈ closure {y} :=
    (((hf.continuousOn.mono hMU) x hxM).mono hSM).mem_closure hxS fun z hz ↦ hz.1.2
  have hJx : coareaJacobian M f x ∈ closure {0} :=
    ((hJ x hxM).mono hSM).mem_closure hxS fun z hz ↦ hz.2
  rw [closure_singleton] at hfx hJx
  exact ⟨⟨hxM, hfx⟩, hJx⟩

/-- **Simon Ch. 2, §6 (p. 66), consequence of 6.3.** Given the co-area formula, the critical set
`C = {x ∈ M : J*_f(x) = 0}` meets `Lᵐ`-a.e. fiber `f⁻¹(y)` in an `Hᵏ`-null set: use 6.3 with
`g = 1_C`, for which the integrand `1_C J*_f` vanishes identically. `C` is measurable because `M`
is measurable and `J*_f` is continuous on `M`. -/
theorem Submission.c1_sard_critical_fibers_null : CoareaFormula → ∀ (N m k : ℕ) (M U : Set (Rn N)) (f : Rn N → Rn m), 0 < k → Chapter02.IsSimonSubmanifold (E := Rn (m + k)) 1 M → IsOpen U → M ⊆ U → ContDiffOn ℝ 1 f U → MeasurableSet M → ContinuousOn (coareaJacobian M f) M → ∀ᵐ y ∂(volume : Measure (Rn m)), μHE[k] (M ∩ f ⁻¹' {y} ∩ {x | coareaJacobian M f x = 0}) = 0 := by
  intro hco N m k M U f hk hM hU hMU hf hMmeas hJ
  -- `C = M ∩ {J*_f = 0}` is relatively closed in the measurable set `M`.
  obtain ⟨F₀, hF₀, h₀⟩ := continuousOn_iff_isClosed.mp hJ {0} isClosed_singleton
  set C : Set (Rn N) := M ∩ {x | coareaJacobian M f x = 0}
  have hC : C = M ∩ F₀ := by
    ext x; constructor
    · rintro ⟨hxM, hx⟩
      have : x ∈ F₀ ∩ M := h₀ ▸ ⟨hx, hxM⟩
      exact ⟨hxM, this.1⟩
    · rintro ⟨hxM, hx⟩
      have : x ∈ coareaJacobian M f ⁻¹' {0} ∩ M := h₀.symm ▸ ⟨hx, hxM⟩
      exact ⟨hxM, this.1⟩
  have hCmeas : MeasurableSet C := hC ▸ hMmeas.inter hF₀.measurableSet
  -- Co-area formula with `g = 1_C`: the left side is `0`, so the fiber integrals vanish a.e.
  set g : Rn N → ℝ≥0∞ := C.indicator 1
  have hgm : AEMeasurable g (μHE[m + k].restrict M) :=
    (measurable_one.indicator hCmeas).aemeasurable
  obtain ⟨hAEM, hEq⟩ := hco N m k M U f g hk hM hU hMU hf hgm
  have hLHS : (fun x => g x * ENNReal.ofReal (coareaJacobian M f x)) = 0 := by
    funext x
    by_cases hx : x ∈ C
    · have hx2 : coareaJacobian M f x = 0 := hx.2
      simp [hx2]
    · simp [g, hx]
  rw [hLHS] at hEq
  have hEq0 : ∫⁻ y, ∫⁻ x in M ∩ f ⁻¹' {y}, g x ∂μHE[k] ∂(volume : Measure (Rn m)) = 0 := by
    rw [← hEq]; exact lintegral_zero
  have hae := (lintegral_eq_zero_iff' hAEM).mp hEq0
  -- The fiber integral of `1_C` is the `Hᵏ`-measure of the critical part of the fiber.
  filter_upwards [hae] with y hy
  have hinner : ∫⁻ x in M ∩ f ⁻¹' {y}, g x ∂μHE[k] =
      μHE[k] (M ∩ f ⁻¹' {y} ∩ {x | coareaJacobian M f x = 0}) := by
    rw [lintegral_indicator_one hCmeas, Measure.restrict_apply hCmeas]
    congr 1
    ext x; constructor
    · rintro ⟨⟨hxM, hxZ⟩, hxM', hxy⟩; exact ⟨⟨hxM, hxy⟩, hxZ⟩
    · rintro ⟨⟨hxM, hxy⟩, hxZ⟩; exact ⟨⟨hxM, hxZ⟩, hxM, hxy⟩
  rw [← hinner]; exact hy

/-- **Simon Ch. 2, §6 (pp. 66–67), level sets of a submersion.** If `G` is `C¹` on the open set
`V ∋ x₀` and `DG(x₀)` is onto, then near `x₀` the level set `G⁻¹{G x₀}` has a `C¹` Simon local
representation (Simon 4.1) inside `V`. Let `π = e ∘ P_K`, where `P_K` is the orthogonal projection
onto `K = ker DG(x₀)` and `e : K ≃ ℝᵏ`. Then `Φ(x) = (G x, π(x - x₀))` has invertible derivative at
`x₀`, and by the inverse function theorem `l(z) = Φ⁻¹(G x₀, z)` on a small ball `D` is the chart. -/
theorem Submission.c1_sard_submersion_level_set_chart : ∀ (m k : ℕ) (V : Set (Rn (m + k))) (G : Rn (m + k) → Rn m) (x₀ : Rn (m + k)), IsOpen V → x₀ ∈ V → ContDiffOn ℝ 1 G V → Function.Surjective (fderiv ℝ G x₀) → ∃ (D : Set (Rn k)) (V₁ : Set (Rn (m + k))) (l : Rn k → Rn (m + k)), x₀ ∈ V₁ ∧ V₁ ⊆ V ∧ Chapter02.IsSimonLocalRepresentation 1 (G ⁻¹' {G x₀}) D V₁ l := by
  intro m k V G x₀ hV hx₀ hG hsurj
  -- `K = ker DG(x₀)` has dimension `k`; `π = e ∘ P_K` with `e : K ≃ ℝᵏ`.
  set A : Rn (m + k) →L[ℝ] Rn m := fderiv ℝ G x₀
  set K : Submodule ℝ (Rn (m + k)) := LinearMap.ker (A : Rn (m + k) →ₗ[ℝ] Rn m) with hK
  have hrange : LinearMap.range (A : Rn (m + k) →ₗ[ℝ] Rn m) = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hKdim : Module.finrank ℝ K = Module.finrank ℝ (Rn k) := by
    have h := LinearMap.finrank_range_add_finrank_ker (A : Rn (m + k) →ₗ[ℝ] Rn m)
    rw [hrange, finrank_top, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin, ← hK] at h
    rw [finrank_euclideanSpace_fin]
    omega
  let e : K ≃ₗ[ℝ] Rn k := LinearEquiv.ofFinrankEq K (Rn k) hKdim
  let π : Rn (m + k) →L[ℝ] Rn k :=
    (e.toContinuousLinearEquiv : K →L[ℝ] Rn k) ∘L K.orthogonalProjectionOnto
  have hπK : ∀ v : K, π v = e v := by
    intro v
    simp [π]
  -- `Φ(x) = (G x, π(x - x₀))` is `C¹` on `V` with `DΦ(x) = (DG(x), π)`.
  let Φ : Rn (m + k) → Rn m × Rn k := fun x => (G x, π (x - x₀))
  have hπaff : ContDiff ℝ 1 (fun x : Rn (m + k) => π (x - x₀)) :=
    π.contDiff.comp (contDiff_id.sub contDiff_const)
  have hΦC : ContDiffOn ℝ 1 Φ V := hG.prodMk hπaff.contDiffOn
  have hΦCA : ∀ x ∈ V, ContDiffAt ℝ 1 Φ x := fun x hx => hΦC.contDiffAt (hV.mem_nhds hx)
  have hπd : ∀ x, HasFDerivAt (fun x : Rn (m + k) => π (x - x₀)) π x := by
    intro x
    have h1 : HasFDerivAt (fun x : Rn (m + k) => x - x₀) (ContinuousLinearMap.id ℝ (Rn (m + k))) x :=
      (hasFDerivAt_id x).sub_const x₀
    have h2 := (π.hasFDerivAt (x := x - x₀)).comp x h1
    rw [ContinuousLinearMap.comp_id] at h2
    exact h2
  have hΦd : ∀ x ∈ V, HasFDerivAt Φ ((fderiv ℝ G x).prod π) x := by
    intro x hx
    have hGx : HasFDerivAt G (fderiv ℝ G x) x :=
      ((hG.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds hx)).hasFDerivAt
    exact hGx.prodMk (hπd x)
  -- `DΦ(x₀) = (A, π)` is injective, hence (equal dimensions) a linear isomorphism `Φ'`.
  have hinj : Function.Injective (A.prod π) := by
    intro v w hvw
    have h1 : A v = A w := congrArg Prod.fst hvw
    have h2 : π v = π w := congrArg Prod.snd hvw
    have hmem : v - w ∈ K := by
      show A (v - w) = 0
      rw [map_sub, h1, sub_self]
    have h3 : e ⟨v - w, hmem⟩ = e 0 := by
      rw [← hπK, map_zero]
      show π (v - w) = 0
      rw [map_sub, h2, sub_self]
    have := congrArg Subtype.val (e.injective h3)
    simpa [sub_eq_zero] using this
  have hdim : Module.finrank ℝ (Rn (m + k)) = Module.finrank ℝ (Rn m × Rn k) := by
    rw [Module.finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin,
      finrank_euclideanSpace_fin]
  have hsurjΦ : Function.Surjective (A.prod π) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  let Φ' : Rn (m + k) ≃L[ℝ] Rn m × Rn k :=
    (LinearEquiv.ofBijective ((A.prod π : Rn (m + k) →L[ℝ] Rn m × Rn k) :
      Rn (m + k) →ₗ[ℝ] Rn m × Rn k) ⟨hinj, hsurjΦ⟩).toContinuousLinearEquiv
  have hΦ'd : HasFDerivAt Φ (Φ' : Rn (m + k) →L[ℝ] Rn m × Rn k) x₀ := by
    have : (Φ' : Rn (m + k) →L[ℝ] Rn m × Rn k) = A.prod π := by ext1 v; rfl
    rw [this]; exact hΦd x₀ hx₀
  -- Inverse function theorem: a local homeomorphism `h = Φ` near `x₀`.
  have hΦs : HasStrictFDerivAt Φ (Φ' : Rn (m + k) →L[ℝ] Rn m × Rn k) x₀ :=
    (hΦCA x₀ hx₀).hasStrictFDerivAt' hΦ'd one_ne_zero
  let h := hΦs.toOpenPartialHomeomorph Φ
  -- Restrict `h` to the open set `Vinv ⊆ V` where `DΦ` is invertible.
  set Vinv : Set (Rn (m + k)) := V ∩ (fderiv ℝ Φ) ⁻¹'
    (range ((↑) : (Rn (m + k) ≃L[ℝ] Rn m × Rn k) → Rn (m + k) →L[ℝ] Rn m × Rn k))
  have hVinvo : IsOpen Vinv :=
    (hΦC.continuousOn_fderiv_of_isOpen hV le_rfl).isOpen_inter_preimage hV
      ContinuousLinearEquiv.isOpen
  have hx₀inv : x₀ ∈ Vinv := ⟨hx₀, Φ', (hΦ'd.fderiv).symm⟩
  let h' := h.restrOpen Vinv hVinvo
  have hh' : (h' : Rn (m + k) → Rn m × Rn k) = Φ := rfl
  have hx₀src : x₀ ∈ h'.source := ⟨hΦs.mem_toOpenPartialHomeomorph_source, hx₀inv⟩
  have hsrcV : h'.source ⊆ V := fun x hx => hx.2.1
  have hΦx₀ : Φ x₀ = (G x₀, 0) := by simp [Φ]
  have htgt : (G x₀, (0 : Rn k)) ∈ h'.target := by
    rw [← hΦx₀, ← hh']; exact h'.map_source hx₀src
  -- A box `O = B(G x₀, ε) × B(0, ε)` inside the target.
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp h'.open_target _ htgt
  set O : Set (Rn m × Rn k) := ball (G x₀) ε ×ˢ ball (0 : Rn k) ε with hO
  have hOt : O ⊆ h'.target := by rw [hO, ball_prod_same]; exact hball
  have hjO : ∀ z ∈ ball (0 : Rn k) ε, ((G x₀, z) : Rn m × Rn k) ∈ O :=
    fun z hz => ⟨mem_ball_self hε, hz⟩
  -- On the target, `h'⁻¹` is `C¹` with invertible derivative.
  have hsymm : ∀ ω ∈ h'.target, ∃ eqv : Rn (m + k) ≃L[ℝ] Rn m × Rn k,
      HasFDerivAt h'.symm (eqv.symm : Rn m × Rn k →L[ℝ] Rn (m + k)) ω ∧
        ContDiffAt ℝ 1 h'.symm ω := by
    intro ω hω
    have hxs : h'.symm ω ∈ h'.source := h'.map_target hω
    obtain ⟨eqv, heqv⟩ := hxs.2.2
    have hxV : h'.symm ω ∈ V := hxs.2.1
    have hd : HasFDerivAt h' (eqv : Rn (m + k) →L[ℝ] Rn m × Rn k) (h'.symm ω) := by
      rw [heqv]; exact ((hΦCA _ hxV).differentiableAt one_ne_zero).hasFDerivAt
    exact ⟨eqv, h'.hasFDerivAt_symm hω hd, h'.contDiffAt_symm hω hd (hΦCA _ hxV)⟩
  -- The chart: `D = B(0, ε)`, `V₁ = source ∩ Φ⁻¹ O`, `l(z) = h'⁻¹(G x₀, z)`.
  refine ⟨ball (0 : Rn k) ε, h'.source ∩ Φ ⁻¹' O, fun z => h'.symm (G x₀, z),
    ⟨hx₀src, ?_⟩, fun x hx => hsrcV hx.1, ?_⟩
  · rw [Set.mem_preimage, hΦx₀]; exact ⟨mem_ball_self hε, mem_ball_self hε⟩
  refine ⟨isOpen_ball, h'.isOpen_inter_preimage (isOpen_ball.prod isOpen_ball), ?_, ?_, ?_, ?_, ?_⟩
  · -- `l` is `C¹` on `D`
    intro z hz
    obtain ⟨eqv, -, hcd⟩ := hsymm _ (hOt (hjO z hz))
    exact (hcd.comp z (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt
  · -- `l` is injective on `D`
    intro z hz z' hz' hzz
    have h1 := h'.right_inv (hOt (hjO z hz))
    have h2 := h'.right_inv (hOt (hjO z' hz'))
    have := congrArg h' hzz
    simp only at this
    rw [h1, h2] at this
    exact (Prod.mk.inj this).2
  · -- `l(D) = V₁ ∩ G⁻¹{G x₀}`
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hω := hOt (hjO z hz)
      refine ⟨⟨h'.map_target hω, ?_⟩, ?_⟩
      · show Φ (h'.symm (G x₀, z)) ∈ O
        rw [← hh', h'.right_inv hω]; exact hjO z hz
      · show G (h'.symm (G x₀, z)) = G x₀
        exact congrArg Prod.fst (h'.right_inv hω)
    · rintro ⟨⟨hxs, hxO⟩, hxG⟩
      have hxG' : G x = G x₀ := hxG
      refine ⟨π (x - x₀), hxO.2, ?_⟩
      show h'.symm (G x₀, π (x - x₀)) = x
      have : ((G x₀, π (x - x₀)) : Rn m × Rn k) = h' x := by rw [hh']; simp [Φ, hxG']
      rw [this, h'.left_inv hxs]
  · -- properness: `D ∩ l⁻¹ Q` is a closed slice of the compact set `Φ(Q)`
    intro Q hQ hQV₁
    have hΦQ : IsCompact (Φ '' Q) :=
      hQ.image_of_continuousOn (hΦC.continuousOn.mono (fun x hx => hsrcV (hQV₁ hx).1))
    have heq : ball (0 : Rn k) ε ∩ (fun z => h'.symm (G x₀, z)) ⁻¹' Q =
        (fun z : Rn k => ((G x₀, z) : Rn m × Rn k)) ⁻¹' (Φ '' Q) := by
      ext z
      constructor
      · rintro ⟨hz, hzQ⟩
        refine ⟨_, hzQ, ?_⟩
        rw [← hh', h'.right_inv (hOt (hjO z hz))]
      · rintro ⟨q, hq, hqz⟩
        have hqz' : Φ q = (G x₀, z) := hqz
        have hqO : Φ q ∈ O := (hQV₁ hq).2
        rw [hqz'] at hqO
        refine ⟨hqO.2, ?_⟩
        show h'.symm (G x₀, z) ∈ Q
        rw [← hqz', ← hh', h'.left_inv (hQV₁ hq).1]; exact hq
    rw [heq]
    refine (hΦQ.image continuous_snd).of_isClosed_subset
      (hΦQ.isClosed.preimage (continuous_const.prodMk continuous_id)) ?_
    intro z hz
    exact ⟨_, hz, rfl⟩
  · -- `Dl(z) = (DΦ)⁻¹ ∘ (0, ·)` is injective
    intro z hz
    obtain ⟨eqv, hd, -⟩ := hsymm _ (hOt (hjO z hz))
    have hj : HasFDerivAt (fun z : Rn k => ((G x₀, z) : Rn m × Rn k))
        ((0 : Rn k →L[ℝ] Rn m).prod (ContinuousLinearMap.id ℝ (Rn k))) z :=
      (hasFDerivAt_const (G x₀) z).prodMk (hasFDerivAt_id z)
    have hcomp := hd.comp z hj
    rw [show (fun z => h'.symm (G x₀, z)) =
      h'.symm ∘ (fun z : Rn k => ((G x₀, z) : Rn m × Rn k)) from rfl, hcomp.fderiv,
      ContinuousLinearMap.coe_comp]
    refine eqv.symm.injective.comp ?_
    intro a b hab
    have := congrArg Prod.snd hab
    simpa using this

/-- **Simon Ch. 2, 4.1–4.2 (p. 55), composition of local representations.** If `(V, W, ψ)` is a
`C¹` local representation of `M`, `S ⊆ M`, and `(D, V₁, l)` is a `C¹` local representation of
`ψ⁻¹(S)` with `V₁ ⊆ V`, then `ψ(V₁) = W₁ ∩ M` for some open `W₁ ⊆ W` (4.2: by relative
properness, `ψ(V \ V₁)` is closed relative to `W`), and `(D, W₁, ψ ∘ l)` is a `C¹` local
representation of `S`. -/
theorem Submission.c1_sard_local_representation_comp : ∀ (n k N : ℕ) (M S : Set (Rn N)) (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N) (D : Set (Rn k)) (V₁ : Set (Rn n)) (l : Rn k → Rn n), Chapter02.IsSimonLocalRepresentation 1 M V W ψ → S ⊆ M → V₁ ⊆ V → Chapter02.IsSimonLocalRepresentation 1 (ψ ⁻¹' S) D V₁ l → ∃ W₁ : Set (Rn N), W₁ ⊆ W ∧ ψ '' V₁ = W₁ ∩ M ∧ Chapter02.IsSimonLocalRepresentation 1 S D W₁ (ψ ∘ l) := by
  intro n k N M S V W ψ D V₁ l hψ hSM hV₁V hl
  obtain ⟨hV, hW, hψC, hψinj, hψimg, hψprop, hψder⟩ := hψ
  obtain ⟨hD, hV₁, hlC, hlinj, hlimg, hlprop, hlder⟩ := hl
  -- Simon 4.2: `ψ(V \ V₁)` is closed relative to `W`. Near `y ∈ W` it lies in the image of the
  -- compact set `(V ∩ ψ⁻¹(B̄)) \ V₁`, where `B̄ ⊆ W` is a closed ball about `y`.
  have hrel : ∀ y ∈ W, y ∈ closure (ψ '' (V \ V₁)) → y ∈ ψ '' (V \ V₁) := by
    intro y hyW hycl
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hW y hyW
    have hQW : closedBall y (r / 2) ⊆ W := (closedBall_subset_ball (half_lt_self hr)).trans hball
    have hK : IsCompact (ψ '' (V ∩ ψ ⁻¹' closedBall y (r / 2) ∩ V₁ᶜ)) :=
      ((hψprop _ (isCompact_closedBall y (r / 2)) hQW).inter_right
        hV₁.isClosed_compl).image_of_continuousOn (hψC.continuousOn.mono fun x hx => hx.1.1)
    have hsub :
        ball y (r / 2) ∩ ψ '' (V \ V₁) ⊆ ψ '' (V ∩ ψ ⁻¹' closedBall y (r / 2) ∩ V₁ᶜ) := by
      rintro _ ⟨hyb, x, ⟨hxV, hxV₁⟩, rfl⟩
      exact ⟨x, ⟨⟨hxV, ball_subset_closedBall hyb⟩, hxV₁⟩, rfl⟩
    obtain ⟨x, ⟨⟨hxV, -⟩, hxV₁⟩, hxy⟩ := closure_minimal hsub hK.isClosed
      (isOpen_ball.inter_closure ⟨mem_ball_self (half_pos hr), hycl⟩)
    exact ⟨x, ⟨hxV, hxV₁⟩, hxy⟩
  obtain ⟨W₁, hW₁, hW₁W, hW₁img⟩ : ∃ W₁ : Set (Rn N), IsOpen W₁ ∧ W₁ ⊆ W ∧ ψ '' V₁ = W₁ ∩ M := by
    refine ⟨W \ closure (ψ '' (V \ V₁)), hW.sdiff isClosed_closure, sdiff_subset, ?_⟩
    ext y
    constructor
    · rintro ⟨x, hxV₁, rfl⟩
      have hxM : ψ x ∈ W ∩ M := by rw [← hψimg]; exact ⟨x, hV₁V hxV₁, rfl⟩
      refine ⟨⟨hxM.1, fun hcl => ?_⟩, hxM.2⟩
      obtain ⟨x', ⟨hx'V, hx'V₁⟩, hx'⟩ := hrel _ hxM.1 hcl
      rw [hψinj hx'V (hV₁V hxV₁) hx'] at hx'V₁
      exact hx'V₁ hxV₁
    · rintro ⟨⟨hyW, hycl⟩, hyM⟩
      obtain ⟨x, hxV, rfl⟩ : y ∈ ψ '' V := by rw [hψimg]; exact ⟨hyW, hyM⟩
      by_cases hx : x ∈ V₁
      · exact ⟨x, hx, rfl⟩
      · exact (hycl (subset_closure ⟨x, ⟨hxV, hx⟩, rfl⟩)).elim
  have hlD : MapsTo l D V₁ := fun z hz => by
    have : l z ∈ l '' D := ⟨z, hz, rfl⟩
    rw [hlimg] at this; exact this.1
  refine ⟨W₁, hW₁W, hW₁img, hD, hW₁, ?_, ?_, ?_, ?_, ?_⟩
  · exact hψC.comp hlC (hlD.mono_right hV₁V)
  · exact hψinj.comp hlinj (hlD.mono_right hV₁V)
  · rw [image_comp, hlimg, image_inter_preimage, hW₁img, inter_assoc, inter_eq_right.mpr hSM]
  · intro Q hQ hQW₁
    have hK := hψprop Q hQ (hQW₁.trans hW₁W)
    have hKV₁ : V ∩ ψ ⁻¹' Q ⊆ V₁ := by
      rintro x ⟨hxV, hxQ⟩
      have hxM : ψ x ∈ W ∩ M := by rw [← hψimg]; exact ⟨x, hxV, rfl⟩
      have : ψ x ∈ ψ '' V₁ := by rw [hW₁img]; exact ⟨hQW₁ hxQ, hxM.2⟩
      obtain ⟨x', hx'V₁, hx'⟩ := this
      rw [← hψinj (hV₁V hx'V₁) hxV hx']
      exact hx'V₁
    have heq : D ∩ (ψ ∘ l) ⁻¹' Q = D ∩ l ⁻¹' (V ∩ ψ ⁻¹' Q) := by
      ext z
      constructor
      · rintro ⟨hz, hzQ⟩; exact ⟨hz, hV₁V (hlD hz), hzQ⟩
      · rintro ⟨hz, _, hzQ⟩; exact ⟨hz, hzQ⟩
    rw [heq]
    exact hlprop _ hK hKV₁
  · intro z hz
    have hlz : l z ∈ V := hV₁V (hlD hz)
    have hdψ : DifferentiableAt ℝ ψ (l z) :=
      (hψC.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds hlz)
    have hdl : DifferentiableAt ℝ l z :=
      (hlC.differentiableOn one_ne_zero).differentiableAt (hD.mem_nhds hz)
    rw [fderiv_comp z hdψ hdl, ContinuousLinearMap.coe_comp]
    exact (hψder (l z) hlz).comp (hlder z hz)

/-- **Simon Ch. 2, Theorem 6.4 (p. 67), regular fibres** (steps 6, 7 and 11 of the `C1Sard`
proof). Fix `p ∈ Σ_y = (M ∩ f⁻¹{y}) \ {J*_f = 0}` and a Simon chart `(V, W, ψ)` of `M` with
`p = ψ(x_p)`. On the open set `V' = {x ∈ V : J*_f(ψ x) ≠ 0}` (continuity of `J*_f` on `M`) the
map `G = f ∘ ψ` is `C¹`, and `DG(x_p) = Df(p) ∘ Dψ(x_p)` is onto: `df_p` has rank `m`
(`c1_sard_coarea_jacobian_eq_zero_iff`) and `T_p M = range Dψ(x_p)`. The level-set chart
`(D, V₁, l)` of `G⁻¹{y}` at `x_p` (`c1_sard_submersion_level_set_chart`) is a chart of
`ψ⁻¹(Σ_y)` because the two sets agree on `V₁ ⊆ V'`, and `c1_sard_local_representation_comp`
turns it into the chart `(D, W₁, ψ ∘ l)` of `Σ_y` at `p`. -/
theorem Submission.c1_sard_regular_fiber_submanifold : ∀ (N m k : ℕ) (M U : Set (Rn N)) (f : Rn N → Rn m), Chapter02.IsSimonSubmanifold (E := Rn (m + k)) 1 M → IsOpen U → M ⊆ U → ContDiffOn ℝ 1 f U → (∀ (V : Set (Rn (m + k))) (W : Set (Rn N)) (ψ : Rn (m + k) → Rn N), Chapter02.IsSimonLocalRepresentation 1 M V W ψ → ∀ x ∈ V, tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap) → ContinuousOn (coareaJacobian M f) M → ∀ y : Rn m, Chapter02.IsSimonSubmanifold (E := Rn k) 1 ((M ∩ f ⁻¹' {y}) \ {x | coareaJacobian M f x = 0}) := by
  intro N m k M U f hM hU hMU hf htan hJ y
  refine ⟨le_rfl, ?_⟩
  rintro p ⟨⟨hpM, hpy⟩, hpZ⟩
  -- A Simon chart `(V, W, ψ)` of `M` with `p = ψ x_p`; then `y = f (ψ x_p)`.
  obtain ⟨V, W, ψ, hpW, hψ⟩ := hM.2 p hpM
  obtain ⟨xp, hxpV, rfl⟩ : p ∈ ψ '' V := by rw [hψ.image_eq]; exact ⟨hpW, hpM⟩
  obtain rfl : f (ψ xp) = y := hpy
  have hψM : MapsTo ψ V M := fun x hx ↦ (hψ.image_eq.subset (mem_image_of_mem ψ hx)).2
  -- The regular part `V'` of the chart is open and contains `x_p`.
  set V' : Set (Rn (m + k)) := V ∩ (coareaJacobian M f ∘ ψ) ⁻¹' {0}ᶜ
  have hV'open : IsOpen V' := (hJ.comp hψ.contDiffOn.continuousOn hψM).isOpen_inter_preimage
    hψ.isOpen_source isOpen_compl_singleton
  have hV'V : V' ⊆ V := inter_subset_left
  have hxpV' : xp ∈ V' := ⟨hxpV, hpZ⟩
  -- `G = f ∘ ψ` is `C¹` on `V'`, and `DG(x_p) = Df(p) ∘ Dψ(x_p)` is onto.
  have hG : ContDiffOn ℝ 1 (f ∘ ψ) V' :=
    hf.comp (hψ.contDiffOn.mono hV'V) fun x hx ↦ hMU (hψM (hV'V hx))
  have hdf : DifferentiableAt ℝ f (ψ xp) :=
    (hf.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds (hMU hpM))
  have hdψ : DifferentiableAt ℝ ψ xp :=
    (hψ.contDiffOn.differentiableOn one_ne_zero).differentiableAt (hψ.isOpen_source.mem_nhds hxpV)
  have hsurjL : LinearMap.range
      ((fderiv ℝ f (ψ xp)).toLinearMap ∘ₗ (tangentSpace M (ψ xp)).subtype) = ⊤ := by
    have h1 := (Submission.c1_sard_coarea_jacobian_eq_zero_iff N m M f (ψ xp)).not.mp hpZ
    apply Submodule.eq_top_of_finrank_eq
    have h2 := Submodule.finrank_le
      (LinearMap.range ((fderiv ℝ f (ψ xp)).toLinearMap ∘ₗ (tangentSpace M (ψ xp)).subtype))
    rw [finrank_euclideanSpace_fin] at h2 ⊢
    omega
  have hsurjG : Function.Surjective (fderiv ℝ (f ∘ ψ) xp) := by
    intro w
    have hw : w ∈ LinearMap.range
        ((fderiv ℝ f (ψ xp)).toLinearMap ∘ₗ (tangentSpace M (ψ xp)).subtype) := by
      rw [hsurjL]; trivial
    obtain ⟨t, ht⟩ := hw
    have htmem : (t : Rn N) ∈ LinearMap.range (fderiv ℝ ψ xp).toLinearMap := by
      rw [← htan V W ψ hψ xp hxpV]; exact t.2
    obtain ⟨v, hv⟩ := htmem
    refine ⟨v, ?_⟩
    rw [fderiv_comp xp hdf hdψ]
    have hv' : fderiv ℝ ψ xp v = t := hv
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, hv']
    simpa using ht
  -- The level-set chart of `G⁻¹{y}` at `x_p` is a chart of `ψ⁻¹(Σ_y)`.
  obtain ⟨D, V₁, l, hxpV₁, hV₁V', hl⟩ :=
    Submission.c1_sard_submersion_level_set_chart m k V' (f ∘ ψ) xp hV'open hxpV' hG hsurjG
  set S : Set (Rn N) := (M ∩ f ⁻¹' {f (ψ xp)}) \ {x | coareaJacobian M f x = 0}
  have hset : V₁ ∩ (f ∘ ψ) ⁻¹' {(f ∘ ψ) xp} = V₁ ∩ ψ ⁻¹' S := by
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩
      have hxV' := hV₁V' hx1
      exact ⟨hx1, ⟨hψM hxV'.1, hx2⟩, hxV'.2⟩
    · rintro ⟨hx1, ⟨_, hx2⟩, _⟩
      exact ⟨hx1, hx2⟩
  have hl' : Chapter02.IsSimonLocalRepresentation 1 (ψ ⁻¹' S) D V₁ l := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hl
    exact ⟨h1, h2, h3, h4, h5.trans hset, h6, h7⟩
  -- Composing with `ψ` gives the chart `(D, W₁, ψ ∘ l)` of `Σ_y`, and `p = ψ x_p ∈ W₁`.
  obtain ⟨W₁, -, hW₁img, hrep⟩ := Submission.c1_sard_local_representation_comp (m + k) k N M
    S V W ψ D V₁ l hψ (fun x hx ↦ hx.1.1) (hV₁V'.trans hV'V) hl'
  exact ⟨D, W₁, ψ ∘ l, (hW₁img.subset (mem_image_of_mem ψ hxpV₁)).1, hrep⟩

/-- **Local submersion (rectification) chart** (cf. Spivak, *Calculus on Manifolds*, Thm 2-13).
If `G` is `C¹` on the open set `V ∋ a` and `DG(a)` is onto, let `π = e ∘ P_K`, where `P_K` is the
orthogonal projection onto `K = ker DG(a)` and `e : K ≃ ℝᵏ`. Then `Φ(x) = (G x, π(x - a))` has
invertible derivative at `a`. By the inverse function theorem, `Λ = Φ⁻¹` on
`Ω = {p ∈ target : Λ p ∈ V₁}` is the chart, where `V₁ ∋ a` is an open subset of `V` on which
`DΦ` is invertible; `G ∘ Λ = WithLp.fst` because `Φ ∘ Λ = id` on `Ω`. -/
theorem Submission.coarea_straightening_submersion_chart : ∀ (m k : ℕ) (V : Set (Rn (m + k))) (G : Rn (m + k) → Rn m) (a : Rn (m + k)), IsOpen V → ContDiffOn ℝ 1 G V → a ∈ V → Function.Surjective (fderiv ℝ G a) → ∃ (Ω : Set (WithLp 2 (Rn m × Rn k))) (Λ : WithLp 2 (Rn m × Rn k) → Rn (m + k)), IsOpen Ω ∧ ContDiffOn ℝ 1 Λ Ω ∧ InjOn Λ Ω ∧ IsOpen (Λ '' Ω) ∧ a ∈ Λ '' Ω ∧ Λ '' Ω ⊆ V ∧ (∀ p ∈ Ω, Function.Bijective (fderiv ℝ Λ p)) ∧ ∀ p ∈ Ω, G (Λ p) = WithLp.fst p := by
  intro m k V G a hV hG ha hsurj
  -- `K = ker DG(a)` has dimension `k` (rank–nullity).
  set A : Rn (m + k) →L[ℝ] Rn m := fderiv ℝ G a
  set K : Submodule ℝ (Rn (m + k)) := LinearMap.ker (A : Rn (m + k) →ₗ[ℝ] Rn m) with hK
  have hrange : LinearMap.range (A : Rn (m + k) →ₗ[ℝ] Rn m) = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hKdim : Module.finrank ℝ K = Module.finrank ℝ (Rn k) := by
    have h := LinearMap.finrank_range_add_finrank_ker (A : Rn (m + k) →ₗ[ℝ] Rn m)
    rw [hrange, finrank_top, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin, ← hK] at h
    rw [finrank_euclideanSpace_fin]
    omega
  -- `π = e ∘ P_K : ℝ^{m+k} → ℝᵏ` agrees on `K` with an isomorphism `e : K ≃ ℝᵏ`.
  let e : K ≃ₗ[ℝ] Rn k := LinearEquiv.ofFinrankEq K (Rn k) hKdim
  let π : Rn (m + k) →L[ℝ] Rn k :=
    (e.toContinuousLinearEquiv : K →L[ℝ] Rn k) ∘L K.orthogonalProjectionOnto
  have hπK : ∀ v : K, π v = e v := by
    intro v
    simp [π]
  -- `Φ(x) = toLp (G x, π(x - a))` is `C¹` on `V` with `DΦ(x) = T ∘ (DG(x), π)`.
  let T : (Rn m × Rn k) ≃L[ℝ] WithLp 2 (Rn m × Rn k) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ (Rn m) (Rn k)).symm
  let Φ : Rn (m + k) → WithLp 2 (Rn m × Rn k) := fun x => T (G x, π (x - a))
  have hπaff : ContDiff ℝ 1 (fun x : Rn (m + k) => π (x - a)) :=
    π.contDiff.comp (contDiff_id.sub contDiff_const)
  have hΦC : ContDiffOn ℝ 1 Φ V := T.contDiff.comp_contDiffOn (hG.prodMk hπaff.contDiffOn)
  have hΦCA : ∀ x ∈ V, ContDiffAt ℝ 1 Φ x := fun x hx => hΦC.contDiffAt (hV.mem_nhds hx)
  have hπd : ∀ x, HasFDerivAt (fun x : Rn (m + k) => π (x - a)) π x := by
    intro x
    have h1 : HasFDerivAt (fun x : Rn (m + k) => x - a) (ContinuousLinearMap.id ℝ (Rn (m + k))) x :=
      (hasFDerivAt_id x).sub_const a
    have h2 := (π.hasFDerivAt (x := x - a)).comp x h1
    rw [ContinuousLinearMap.comp_id] at h2
    exact h2
  have hΦd : ∀ x ∈ V, HasFDerivAt Φ
      ((T : Rn m × Rn k →L[ℝ] WithLp 2 (Rn m × Rn k)).comp ((fderiv ℝ G x).prod π)) x := by
    intro x hx
    have hGx : HasFDerivAt G (fderiv ℝ G x) x :=
      ((hG.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds hx)).hasFDerivAt
    exact T.hasFDerivAt.comp x (hGx.prodMk (hπd x))
  -- `(DG(a), π)` is injective, hence (equal dimensions) bijective; so `DΦ(a)` is an isomorphism.
  have hinj : Function.Injective (A.prod π) := by
    intro v w hvw
    have h1 : A v = A w := congrArg Prod.fst hvw
    have h2 : π v = π w := congrArg Prod.snd hvw
    have hmem : v - w ∈ K := by
      show A (v - w) = 0
      rw [map_sub, h1, sub_self]
    have h3 : e ⟨v - w, hmem⟩ = e 0 := by
      rw [← hπK, map_zero]
      show π (v - w) = 0
      rw [map_sub, h2, sub_self]
    have := congrArg Subtype.val (e.injective h3)
    simpa [sub_eq_zero] using this
  have hdim : Module.finrank ℝ (Rn (m + k)) = Module.finrank ℝ (Rn m × Rn k) := by
    rw [Module.finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin,
      finrank_euclideanSpace_fin]
  have hsurjA : Function.Surjective (A.prod π) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  let Φ' : Rn (m + k) ≃L[ℝ] WithLp 2 (Rn m × Rn k) :=
    (LinearEquiv.ofBijective ((A.prod π : Rn (m + k) →L[ℝ] Rn m × Rn k) :
      Rn (m + k) →ₗ[ℝ] Rn m × Rn k) ⟨hinj, hsurjA⟩).toContinuousLinearEquiv.trans T
  have hΦ'd : HasFDerivAt Φ (Φ' : Rn (m + k) →L[ℝ] WithLp 2 (Rn m × Rn k)) a := by
    have : (Φ' : Rn (m + k) →L[ℝ] WithLp 2 (Rn m × Rn k)) =
        (T : Rn m × Rn k →L[ℝ] WithLp 2 (Rn m × Rn k)).comp (A.prod π) := by ext1 v; rfl
    rw [this]; exact hΦd a ha
  -- The set `V'` of points of `V` at which `DΦ` is invertible is open and contains `a`.
  set V' : Set (Rn (m + k)) := V ∩ (fderiv ℝ Φ) ⁻¹'
    (range ((↑) : (Rn (m + k) ≃L[ℝ] WithLp 2 (Rn m × Rn k)) →
      Rn (m + k) →L[ℝ] WithLp 2 (Rn m × Rn k)))
  have hV'o : IsOpen V' :=
    (hΦC.continuousOn_fderiv_of_isOpen hV le_rfl).isOpen_inter_preimage hV
      ContinuousLinearEquiv.isOpen
  have haV' : a ∈ V' := ⟨ha, Φ', hΦ'd.fderiv.symm⟩
  -- Inverse function theorem: an open partial homeomorphism `h` with `⇑h = Φ` and `a ∈ S`.
  have hΦs : HasStrictFDerivAt Φ (Φ' : Rn (m + k) →L[ℝ] WithLp 2 (Rn m × Rn k)) a :=
    (hΦCA a ha).hasStrictFDerivAt' hΦ'd one_ne_zero
  let h := hΦs.toOpenPartialHomeomorph Φ
  -- `V₁ = S ∩ V'`, `Ω = {p ∈ S' : h⁻¹ p ∈ V₁}` and `Λ = h⁻¹`; then `Λ(Ω) = V₁`.
  set V₁ : Set (Rn (m + k)) := h.source ∩ V'
  have hV₁o : IsOpen V₁ := h.open_source.inter hV'o
  have haV₁ : a ∈ V₁ := ⟨hΦs.mem_toOpenPartialHomeomorph_source, haV'⟩
  have hV₁V : V₁ ⊆ V := fun x hx => hx.2.1
  set Ω : Set (WithLp 2 (Rn m × Rn k)) := h.target ∩ h.symm ⁻¹' V₁
  have himage : h.symm '' Ω = V₁ := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact hp.2
    · intro hx
      refine ⟨h x, ⟨h.map_source hx.1, ?_⟩, h.left_inv hx.1⟩
      rw [Set.mem_preimage, h.left_inv hx.1]
      exact hx
  -- At `p ∈ Ω`, `Λ` is `C¹` with derivative `(DΦ(Λ p))⁻¹`.
  have hsymm : ∀ p ∈ Ω, ∃ φ : Rn (m + k) ≃L[ℝ] WithLp 2 (Rn m × Rn k),
      HasFDerivAt h.symm (φ.symm : WithLp 2 (Rn m × Rn k) →L[ℝ] Rn (m + k)) p ∧
        ContDiffAt ℝ 1 h.symm p := by
    intro p hp
    obtain ⟨φ, hφ⟩ := hp.2.2.2
    have hxV : h.symm p ∈ V := hp.2.2.1
    have hd : HasFDerivAt h (φ : Rn (m + k) →L[ℝ] WithLp 2 (Rn m × Rn k)) (h.symm p) := by
      rw [hφ]; exact ((hΦCA _ hxV).differentiableAt one_ne_zero).hasFDerivAt
    exact ⟨φ, h.hasFDerivAt_symm hp.1 hd, h.contDiffAt_symm hp.1 hd (hΦCA _ hxV)⟩
  refine ⟨Ω, h.symm, h.isOpen_inter_preimage_symm hV₁o, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `Λ` is `C¹` on `Ω`
    intro p hp
    obtain ⟨φ, -, hcd⟩ := hsymm p hp
    exact hcd.contDiffWithinAt
  · -- `Λ` is injective on `Ω ⊆ S'`
    exact h.symm.injOn.mono inter_subset_left
  · rw [himage]; exact hV₁o
  · rw [himage]; exact haV₁
  · rw [himage]; exact hV₁V
  · -- `DΛ(p) = (DΦ(Λ p))⁻¹` is bijective
    intro p hp
    obtain ⟨φ, hd, -⟩ := hsymm p hp
    rw [hd.fderiv]
    exact φ.symm.bijective
  · -- `G(Λ p) = (Φ(Λ p))₁ = p₁`
    intro p hp
    exact congrArg WithLp.fst (h.right_inv hp.1)
/-- **Simon Ch. 2, 4.1–4.2 (p. 55), reparametrizing a local representation.** Let `(V, W, ψ)` be
a `C¹` local representation of `M` with `T_{ψ(x)} M = range Dψ(x)` for `x ∈ V`, and let `Λ` be
`C¹` and injective on the open set `Ω`, with bijective derivative and `Λ(Ω) ⊆ V` open. Then
`ψ ∘ Λ` is `C¹` and injective on `Ω` with injective derivative, `(ψ ∘ Λ)(Ω) = O ∩ M` for an open
`O` (4.2: by relative properness, `ψ(V \ Λ(Ω))` is closed relative to `W`), and
`T_{ψ(Λ(p))} M = range D(ψ ∘ Λ)(p)` for `p ∈ Ω`. -/
theorem Submission.coarea_straightening_reparametrize_chart : ∀ (N m k : ℕ) (M : Set (Rn N)) (V : Set (Rn (m + k))) (W : Set (Rn N)) (ψ : Rn (m + k) → Rn N) (Ω : Set (WithLp 2 (Rn m × Rn k))) (Λ : WithLp 2 (Rn m × Rn k) → Rn (m + k)), Chapter02.IsSimonLocalRepresentation 1 M V W ψ → (∀ x ∈ V, tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap) → IsOpen Ω → ContDiffOn ℝ 1 Λ Ω → InjOn Λ Ω → IsOpen (Λ '' Ω) → Λ '' Ω ⊆ V → (∀ p ∈ Ω, Function.Bijective (fderiv ℝ Λ p)) → ∃ O : Set (Rn N), IsOpen O ∧ (ψ ∘ Λ) '' Ω = O ∩ M ∧ ContDiffOn ℝ 1 (ψ ∘ Λ) Ω ∧ InjOn (ψ ∘ Λ) Ω ∧ (∀ p ∈ Ω, Function.Injective (fderiv ℝ (ψ ∘ Λ) p)) ∧ ∀ p ∈ Ω, tangentSpace M ((ψ ∘ Λ) p) = LinearMap.range (fderiv ℝ (ψ ∘ Λ) p).toLinearMap := by
  intro N m k M V W ψ Ω Λ hψ hT hΩ hΛC hΛinj hV₁ hV₁V hΛbij
  obtain ⟨hV, hW, hψC, hψinj, hψimg, hψprop, hψder⟩ := hψ
  have hΛV : MapsTo Λ Ω V := fun p hp => hV₁V ⟨p, hp, rfl⟩
  -- Simon 4.2: `ψ(V \ Λ(Ω))` is closed relative to `W`. Near `y ∈ W` it lies in the image of the
  -- compact set `(V ∩ ψ⁻¹(B̄)) \ Λ(Ω)`, where `B̄ ⊆ W` is a closed ball about `y`.
  have hrel : ∀ y ∈ W, y ∈ closure (ψ '' (V \ Λ '' Ω)) → y ∈ ψ '' (V \ Λ '' Ω) := by
    intro y hyW hycl
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hW y hyW
    have hQW : closedBall y (r / 2) ⊆ W := (closedBall_subset_ball (half_lt_self hr)).trans hball
    have hK : IsCompact (ψ '' (V ∩ ψ ⁻¹' closedBall y (r / 2) ∩ (Λ '' Ω)ᶜ)) :=
      ((hψprop _ (isCompact_closedBall y (r / 2)) hQW).inter_right
        hV₁.isClosed_compl).image_of_continuousOn (hψC.continuousOn.mono fun x hx => hx.1.1)
    have hsub : ball y (r / 2) ∩ ψ '' (V \ Λ '' Ω) ⊆
        ψ '' (V ∩ ψ ⁻¹' closedBall y (r / 2) ∩ (Λ '' Ω)ᶜ) := by
      rintro _ ⟨hyb, x, ⟨hxV, hxV₁⟩, rfl⟩
      exact ⟨x, ⟨⟨hxV, ball_subset_closedBall hyb⟩, hxV₁⟩, rfl⟩
    obtain ⟨x, ⟨⟨hxV, -⟩, hxV₁⟩, hxy⟩ := closure_minimal hsub hK.isClosed
      (isOpen_ball.inter_closure ⟨mem_ball_self (half_pos hr), hycl⟩)
    exact ⟨x, ⟨hxV, hxV₁⟩, hxy⟩
  -- Chain rule: `D(ψ ∘ Λ)(p) = Dψ(Λ(p)) ∘ DΛ(p)`.
  have hD : ∀ p ∈ Ω, fderiv ℝ (ψ ∘ Λ) p = (fderiv ℝ ψ (Λ p)).comp (fderiv ℝ Λ p) := fun p hp =>
    fderiv_comp p ((hψC.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds (hΛV hp)))
      ((hΛC.differentiableOn one_ne_zero).differentiableAt (hΩ.mem_nhds hp))
  refine ⟨W \ closure (ψ '' (V \ Λ '' Ω)), hW.sdiff isClosed_closure, ?_, hψC.comp hΛC hΛV,
    hψinj.comp hΛinj hΛV, fun p hp => ?_, fun p hp => ?_⟩
  · rw [image_comp]
    ext y
    constructor
    · rintro ⟨x, hxV₁, rfl⟩
      have hxM : ψ x ∈ W ∩ M := by rw [← hψimg]; exact ⟨x, hV₁V hxV₁, rfl⟩
      refine ⟨⟨hxM.1, fun hcl => ?_⟩, hxM.2⟩
      obtain ⟨x', ⟨hx'V, hx'V₁⟩, hx'⟩ := hrel _ hxM.1 hcl
      rw [hψinj hx'V (hV₁V hxV₁) hx'] at hx'V₁
      exact hx'V₁ hxV₁
    · rintro ⟨⟨hyW, hycl⟩, hyM⟩
      obtain ⟨x, hxV, rfl⟩ : y ∈ ψ '' V := by rw [hψimg]; exact ⟨hyW, hyM⟩
      by_cases hx : x ∈ Λ '' Ω
      · exact ⟨x, hx, rfl⟩
      · exact (hycl (subset_closure ⟨x, ⟨hxV, hx⟩, rfl⟩)).elim
  · rw [hD p hp, ContinuousLinearMap.coe_comp]
    exact (hψder (Λ p) (hΛV hp)).comp (hΛbij p hp).1
  · -- `DΛ(p)` is onto, so `range D(ψ ∘ Λ)(p) = range Dψ(Λ(p)) = T_{ψ(Λ(p))} M`.
    rw [Function.comp_apply, hT (Λ p) (hΛV hp), hD p hp, ContinuousLinearMap.toLinearMap_comp,
      LinearMap.range_comp_of_range_eq_top]
    exact LinearMap.range_eq_top.mpr (hΛbij p hp).2
/-- **Simon Ch. 2, §6 (pp. 66–67), co-area formula on a straightening chart: area pull-back.**
Let `P = ℝᵐ × ℝᵏ` (Euclidean), `Ω ⊆ P` open, and `Ψ : P → ℝᴺ` an injective `C¹` immersion on `Ω`
with `f ∘ Ψ = fst` and `T_{Ψ p} M = range DΨ(p)` on `Ω`; let `j = toLp ∘ inr : ℝᵏ → P`. Given the
pointwise linear-algebra identity `J*_f(x) · normDet A = normDet B` (last hypothesis), the area
formula for `Ψ` (Simon 3.2/3.5) pulls `∫_S g J*_f dHᵐ⁺ᵏ` back to the chart:
`∫_{Ω ∩ Ψ⁻¹ S} normDet(DΨ(p) ∘ j) · g(Ψ p) dp`, for a Borel `S ⊆ Ψ(Ω)` and any weight `g`. -/
theorem Submission.coarea_chart_area_pullback : ∀ (N m k : ℕ) (M : Set (Rn N)) (f : Rn N → Rn m) (Ω : Set (WithLp 2 (Rn m × Rn k))) (Ψ : WithLp 2 (Rn m × Rn k) → Rn N) (S : Set (Rn N)) (g : Rn N → ℝ≥0∞), IsOpen Ω → ContDiffOn ℝ 1 Ψ Ω → InjOn Ψ Ω → (∀ p ∈ Ω, Function.Injective (fderiv ℝ Ψ p)) → (∀ p ∈ Ω, DifferentiableAt ℝ f (Ψ p)) → (∀ p ∈ Ω, f (Ψ p) = WithLp.fst p) → (∀ p ∈ Ω, tangentSpace M (Ψ p) = LinearMap.range (fderiv ℝ Ψ p).toLinearMap) → MeasurableSet S → S ⊆ Ψ '' Ω → (∀ (x : Rn N) (A : WithLp 2 (Rn m × Rn k) →L[ℝ] Rn N) (B : Rn k →L[ℝ] Rn N), Function.Injective A → tangentSpace M x = LinearMap.range A.toLinearMap → (∀ p, fderiv ℝ f x (A p) = WithLp.fst p) → (∀ b, B b = A (WithLp.toLp 2 (0, b))) → coareaJacobian M f x * A.toLinearMap.normDet = B.toLinearMap.normDet) → ∫⁻ x in S, g x * ENNReal.ofReal (coareaJacobian M f x) ∂μHE[m + k] = ∫⁻ p in Ω ∩ Ψ ⁻¹' S, ENNReal.ofReal (((fderiv ℝ Ψ p).comp ((WithLp.prodContinuousLinearEquiv 2 ℝ (Rn m) (Rn k)).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ (Rn m) (Rn k)))).toLinearMap.normDet) * g (Ψ p) := by
  intro N m k M f Ω Ψ S g hΩ hΨ hΨinj hreg hfd hfΨ hT hS hSΨ hLA
  classical
  /- Simon (3.2)/(3.5) for an injective regular parametrization in arbitrary codimension, with an
  arbitrary (possibly non-measurable) weight. This is the pinned SimonGMT theorem
  `Chapter02.weighted_area_formula_volume_of_injective_derivative`, whose module is not imported
  here; its kernel-checked proof (SimonGMT `Chapter02/AreaApproximation`, `AreaDerivative`,
  `AreaFormula`, `WeightedArea`, the derivative-control step adapted from Mathlib's
  `MeasureTheory/Function/Jacobian.lean`) is replayed as a local step. -/
  have area : ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F]
      [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
      (s : Set E) (Φ : E → F), MeasurableSet s → (∀ x ∈ s, DifferentiableAt ℝ Φ x) →
      (∀ x ∈ s, Function.Injective (fderiv ℝ Φ x)) → InjOn Φ s → ∀ h : F → ℝ,
      ∫ y in Φ '' s, h y ∂μHE[Module.finrank ℝ E] =
        ∫ x in s, (fderiv ℝ Φ x).toLinearMap.normDet * h (Φ x) := by
    intro E F _ _ _ _ _ _ _ _ _ _ s Φ hs hΦ hregΦ hinjΦ h
      (∀ x ∈ s, Function.Injective (fderiv ℝ Φ x)) → InjOn Φ s → ∀ w : F → ℝ≥0∞,
      ∫⁻ y in Φ '' s, w y ∂μHE[Module.finrank ℝ E] =
        ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ Φ x).toLinearMap.normDet * w (Φ x) := by
    intro E F _ _ _ _ _ _ _ _ _ _ s Φ hs hΦ hregΦ hinjΦ w
    -- The metric Jacobian `normDet` depends continuously on the linear map.
    have hcontJ : Continuous (fun L : E →L[ℝ] F ↦ L.toLinearMap.normDet) := by
      have heq : (fun L : E →L[ℝ] F ↦ L.toLinearMap.normDet) =
          fun L ↦ Real.sqrt ((L.adjoint ∘L L).det) := by
        funext L
        rw [← L.normDet_sq]
        simpa only [RCLike.ofReal_real_eq_id, id_eq] using
          (Real.sqrt_sq L.toLinearMap.normDet_nonneg).symm
      rw [heq]
      exact Real.continuous_sqrt.comp
        (ContinuousLinearMap.continuous_det.comp
          (Continuous.clm_comp ContinuousLinearMap.adjoint.continuous continuous_id))
    -- A comparison of pairwise distances gives a comparison of image measures.
    have himage_le : ∀ (φ γ : E → F) (t : Set E) (K : ℝ≥0), InjOn γ t →
        (∀ x ∈ t, ∀ y ∈ t, dist (φ x) (φ y) ≤ K * dist (γ x) (γ y)) →
        μHE[Module.finrank ℝ E] (φ '' t) ≤
          (K : ℝ≥0∞) ^ Module.finrank ℝ E * μHE[Module.finrank ℝ E] (γ '' t) := by
      intro φ γ t K hγ hφγ
      have hh : LipschitzOnWith K (φ ∘ Function.invFunOn γ t) (γ '' t) := by
        rw [lipschitzOnWith_iff_dist_le_mul]
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        simpa only [Function.comp_apply, hγ.leftInvOn_invFunOn hx,
          hγ.leftInvOn_invFunOn hy] using hφγ x hx y hy
      have himage : (φ ∘ Function.invFunOn γ t) '' (γ '' t) = φ '' t := by
        rw [image_comp, hγ.invFunOn_image Subset.rfl]
      simpa only [himage] using
        Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn (Module.finrank ℝ E) hh
    -- Upper and lower image estimates for a map approximating an injective linear map.
    have happrox_upper : ∀ (φ : E → F) (L : E →L[ℝ] F) (t : Set E) (δ K : ℝ≥0),
        ApproximatesLinearOn φ L t δ → AntilipschitzWith K L →
        μHE[Module.finrank ℝ E] (φ '' t) ≤ ((1 + δ * K : ℝ≥0) : ℝ≥0∞) ^ Module.finrank ℝ E *
          (ENNReal.ofReal L.toLinearMap.normDet * volume t) := by
      intro φ L t δ K hf hL
      rw [← L.toLinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume]
      apply himage_le φ L t _ hL.injective.injOn
      intro x hx y hy
      have hb : ‖x - y‖ ≤ K * ‖L x - L y‖ := by
        simpa only [dist_eq_norm] using hL.le_mul_dist x y
      have herror : ‖φ x - φ y - (L x - L y)‖ ≤ (δ : ℝ) * K * ‖L x - L y‖ := by
        calc
          _ ≤ δ * ‖x - y‖ := by simpa only [map_sub] using hf x hx y hy
          _ ≤ δ * (K * ‖L x - L y‖) := mul_le_mul_of_nonneg_left hb δ.2
          _ = _ := by ring
      simp only [dist_eq_norm, NNReal.coe_add, NNReal.coe_one, NNReal.coe_mul]
      calc
        ‖φ x - φ y‖ ≤ ‖φ x - φ y - (L x - L y)‖ + ‖L x - L y‖ := norm_le_norm_sub_add _ _
        _ ≤ (δ : ℝ) * K * ‖L x - L y‖ + ‖L x - L y‖ := add_le_add herror le_rfl
        _ = (1 + (δ : ℝ) * K) * ‖L x - L y‖ := by ring
    have happrox_lower : ∀ (φ : E → F) (L : E →L[ℝ] F) (t : Set E) (δ K : ℝ≥0),
        ApproximatesLinearOn φ L t δ → AntilipschitzWith K L → δ * K < 1 →
        ENNReal.ofReal L.toLinearMap.normDet * volume t ≤
          (((1 - δ * K)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ Module.finrank ℝ E *
            μHE[Module.finrank ℝ E] (φ '' t) := by
      intro φ L t δ K hf hL hδ
      have hδR : (δ : ℝ) * K < 1 := hδ
      have hdist : ∀ x ∈ t, ∀ y ∈ t, dist (L x) (L y) ≤
          ((1 - δ * K)⁻¹ : ℝ≥0) * dist (φ x) (φ y) := by
        intro x hx y hy
        have hb : ‖x - y‖ ≤ K * ‖L x - L y‖ := by
          simpa only [dist_eq_norm] using hL.le_mul_dist x y
        have herror : ‖φ x - φ y - (L x - L y)‖ ≤ (δ : ℝ) * K * ‖L x - L y‖ := by
          calc
            _ ≤ δ * ‖x - y‖ := by simpa only [map_sub] using hf x hx y hy
            _ ≤ δ * (K * ‖L x - L y‖) := mul_le_mul_of_nonneg_left hb δ.2
            _ = _ := by ring
        have htriangle : ‖L x - L y‖ ≤ ‖φ x - φ y‖ + ‖φ x - φ y - (L x - L y)‖ := by
          simpa only [norm_sub_rev, add_comm] using
            (norm_le_norm_sub_add (L x - L y) (φ x - φ y))
        simp only [dist_eq_norm, NNReal.coe_inv, NNReal.coe_sub hδ.le, NNReal.coe_one,
          NNReal.coe_mul, inv_mul_eq_div]
        apply (le_div_iff₀ (sub_pos.mpr hδR)).mpr
        nlinarith
      have hφinj : InjOn φ t := by
        intro x hx y hy hxy
        apply hL.injective
        apply dist_le_zero.mp
        simpa only [hxy, dist_self, mul_zero] using hdist x hx y hy
      rw [← L.toLinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume]
      exact himage_le L φ t _ hφinj hdist
    -- One approximation radius controls both the image measure and nearby Jacobians.
    have hradius : ∀ L : E →L[ℝ] F, Function.Injective L → ∀ q : ℝ≥0, 1 < q →
        ∃ δ : ℝ≥0, 0 < δ ∧
          (∀ B : E →L[ℝ] F, ‖B - L‖ ≤ δ →
            ENNReal.ofReal B.toLinearMap.normDet ≤ q * ENNReal.ofReal L.toLinearMap.normDet ∧
            ENNReal.ofReal L.toLinearMap.normDet ≤ q * ENNReal.ofReal B.toLinearMap.normDet) ∧
          (∀ (t : Set E) (φ : E → F), ApproximatesLinearOn φ L t δ →
            μHE[Module.finrank ℝ E] (φ '' t) ≤
                q * (ENNReal.ofReal L.toLinearMap.normDet * volume t) ∧
              ENNReal.ofReal L.toLinearMap.normDet * volume t ≤
                q * μHE[Module.finrank ℝ E] (φ '' t)) := by
      intro L hL q hq
      obtain ⟨δ₀, hδ₀, harea⟩ : ∃ δ : ℝ≥0, 0 < δ ∧ ∀ (t : Set E) (φ : E → F),
          ApproximatesLinearOn φ L t δ →
          μHE[Module.finrank ℝ E] (φ '' t) ≤
              q * (ENNReal.ofReal L.toLinearMap.normDet * volume t) ∧
            ENNReal.ofReal L.toLinearMap.normDet * volume t ≤
              q * μHE[Module.finrank ℝ E] (φ '' t) := by
        obtain ⟨K, _, hK⟩ :=
          L.toLinearMap.exists_antilipschitzWith (LinearMap.ker_eq_bot.mpr hL)
        have hsmall : ∀ᶠ δ : ℝ≥0 in 𝓝 0, δ * K < 1 :=
          (continuousAt_id.mul continuousAt_const).eventually_lt continuousAt_const (by simp)
        have hupper : ∀ᶠ δ : ℝ≥0 in 𝓝 0, (1 + δ * K) ^ Module.finrank ℝ E < q :=
          ((continuousAt_const.add (continuousAt_id.mul continuousAt_const)).pow _).eventually_lt
            continuousAt_const (by simpa using hq)
        have hlower : ∀ᶠ δ : ℝ≥0 in 𝓝 0, ((1 - δ * K)⁻¹) ^ Module.finrank ℝ E < q := by
          apply ContinuousAt.eventually_lt _ continuousAt_const (by simpa using hq)
          apply ContinuousAt.pow
          apply ContinuousAt.inv₀
          · exact continuousAt_const.sub (continuousAt_id.mul continuousAt_const)
          · simp
        have hevent : ∀ᶠ δ : ℝ≥0 in 𝓝[>] 0, 0 < δ ∧ δ * K < 1 ∧
            (1 + δ * K) ^ Module.finrank ℝ E < q ∧ ((1 - δ * K)⁻¹) ^ Module.finrank ℝ E < q := by
          filter_upwards [self_mem_nhdsWithin, hsmall.filter_mono nhdsWithin_le_nhds,
            hupper.filter_mono nhdsWithin_le_nhds, hlower.filter_mono nhdsWithin_le_nhds]
            with δ hδ hsmall hupper hlower
          exact ⟨hδ, hsmall, hupper, hlower⟩
        obtain ⟨δ, hδ, hδsmall, hδupper, hδlower⟩ := hevent.exists
        refine ⟨δ, hδ, fun t φ hf ↦ ⟨?_, ?_⟩⟩
        · refine (happrox_upper φ L t δ K hf hK).trans ?_
          gcongr
          exact_mod_cast hδupper.le
        · refine (happrox_lower φ L t δ K hf hK hδsmall).trans ?_
          gcongr
          exact_mod_cast hδlower.le
      have hJ : 0 < L.toLinearMap.normDet := by
        apply lt_of_le_of_ne L.toLinearMap.normDet_nonneg
        exact Ne.symm ((L.toLinearMap.normDet_ne_zero_tfae.out 5 1).mp hL)
      have hqR : (1 : ℝ) < q := hq
      have hmul : L.toLinearMap.normDet < (q : ℝ) * L.toLinearMap.normDet := by nlinarith
      have hnear : ∀ᶠ B : E →L[ℝ] F in 𝓝 L,
          B.toLinearMap.normDet < (q : ℝ) * L.toLinearMap.normDet ∧
            L.toLinearMap.normDet < (q : ℝ) * B.toLinearMap.normDet :=
        (hcontJ.continuousAt.eventually_lt continuousAt_const hmul).and
          (continuousAt_const.eventually_lt (continuousAt_const.mul hcontJ.continuousAt) hmul)
      obtain ⟨ε, hε, hnear⟩ := Metric.eventually_nhds_iff.mp hnear
      let δ₁ : ℝ≥0 := ⟨ε / 2, (half_pos hε).le⟩
      refine ⟨min δ₀ δ₁, lt_min hδ₀ (half_pos hε), ?_, ?_⟩
      · intro B hB
        have hdist : dist B L < ε := by
          rw [dist_eq_norm]
          exact hB.trans_lt (lt_of_le_of_lt (by exact_mod_cast min_le_right δ₀ δ₁)
            (half_lt_self hε))
        obtain ⟨hupper, hlower⟩ := hnear hdist
        constructor
        · simpa only [ENNReal.ofReal_mul (NNReal.coe_nonneg q), ENNReal.ofReal_coe_nnreal] using
            ENNReal.ofReal_le_ofReal hupper.le
        · simpa only [ENNReal.ofReal_mul (NNReal.coe_nonneg q), ENNReal.ofReal_coe_nnreal] using
            ENNReal.ofReal_le_ofReal hlower.le
      · intro t φ hf
        exact harea t φ (hf.mono_num (min_le_left _ _))
    -- At almost every point of a measurable approximation piece the derivative is within the
    -- approximation error of the approximating linear map (Lebesgue density points).
    have hderiv_ctrl : ∀ (t : Set E) (A : E →L[ℝ] F) (δ : ℝ≥0), ApproximatesLinearOn Φ A t δ →
        MeasurableSet t → (∀ x ∈ t, HasFDerivWithinAt Φ (fderiv ℝ Φ x) t x) →
        ∀ᵐ x ∂(volume : Measure E).restrict t, ‖fderiv ℝ Φ x - A‖₊ ≤ δ := by
      intro t A δ hf ht hf'
      open scoped Pointwise in
      filter_upwards [Besicovitch.ae_tendsto_measure_inter_div (volume : Measure E) t,
        ae_restrict_mem ht]
      intro x hx xt
      apply ContinuousLinearMap.opNorm_le_bound _ δ.2 fun z ↦ ?_
      suffices H : ∀ ε, 0 < ε →
          ‖(fderiv ℝ Φ x - A) z‖ ≤ (δ + ε) * (‖z‖ + ε) + ‖fderiv ℝ Φ x - A‖ * ε by
        have : Tendsto (fun ε : ℝ ↦ ((δ : ℝ) + ε) * (‖z‖ + ε) + ‖fderiv ℝ Φ x - A‖ * ε)
            (𝓝[>] 0) (𝓝 ((δ + 0) * (‖z‖ + 0) + ‖fderiv ℝ Φ x - A‖ * 0)) :=
          Tendsto.mono_left (Continuous.tendsto (by fun_prop) 0) nhdsWithin_le_nhds
        simp only [add_zero, mul_zero] at this
        apply le_of_tendsto_of_tendsto tendsto_const_nhds this
        filter_upwards [self_mem_nhdsWithin]
        exact H
      intro ε εpos
      have B₁ : ∀ᶠ r in 𝓝[>] (0 : ℝ), (t ∩ ({x} + r • closedBall z ε)).Nonempty :=
        Measure.eventually_nonempty_inter_smul_of_density_one volume t x hx _
          measurableSet_closedBall (measure_closedBall_pos volume z εpos).ne'
      obtain ⟨ρ, ρpos, hρ⟩ : ∃ ρ > 0,
          ball x ρ ∩ t ⊆ {y : E | ‖Φ y - Φ x - (fderiv ℝ Φ x) (y - x)‖ ≤ ε * ‖y - x‖} :=
        mem_nhdsWithin_iff.1 ((hf' x xt).isLittleO.bound εpos)
      have B₂ : ∀ᶠ r in 𝓝[>] (0 : ℝ), {x} + r • closedBall z ε ⊆ ball x ρ := by
        apply nhdsWithin_le_nhds
        exact eventually_singleton_add_smul_subset isBounded_closedBall (ball_mem_nhds x ρpos)
      obtain ⟨r, ⟨y, ⟨yt, hy⟩⟩, rρ, rpos⟩ : ∃ r : ℝ, (t ∩ ({x} + r • closedBall z ε)).Nonempty ∧
          {x} + r • closedBall z ε ⊆ ball x ρ ∧ 0 < r :=
        (B₁.and (B₂.and self_mem_nhdsWithin)).exists
      obtain ⟨a, az, ya⟩ : ∃ a, a ∈ closedBall z ε ∧ y = x + r • a := by
        simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hy
        rcases hy with ⟨a, az, ha⟩
        exact ⟨a, az, by simp only [ha, add_neg_cancel_left]⟩
      have norm_a : ‖a‖ ≤ ‖z‖ + ε :=
        calc
          ‖a‖ = ‖z + (a - z)‖ := by simp only [add_sub_cancel]
          _ ≤ ‖z‖ + ‖a - z‖ := norm_add_le _ _
          _ ≤ ‖z‖ + ε := by grw [mem_closedBall_iff_norm.1 az]
      have I : r * ‖(fderiv ℝ Φ x - A) a‖ ≤ r * (δ + ε) * (‖z‖ + ε) :=
        calc
          r * ‖(fderiv ℝ Φ x - A) a‖ = ‖(fderiv ℝ Φ x - A) (r • a)‖ := by
            simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
          _ = ‖Φ y - Φ x - A (y - x) - (Φ y - Φ x - (fderiv ℝ Φ x) (y - x))‖ := by
            simp only [ya, add_sub_cancel_left, sub_sub_sub_cancel_left, FunLike.coe_sub,
              Pi.sub_apply, map_smul, smul_sub]
          _ ≤ ‖Φ y - Φ x - A (y - x)‖ + ‖Φ y - Φ x - (fderiv ℝ Φ x) (y - x)‖ :=
            norm_sub_le _ _
          _ ≤ δ * ‖y - x‖ + ε * ‖y - x‖ := add_le_add (hf _ yt _ xt) (hρ ⟨rρ hy, yt⟩)
          _ = r * (δ + ε) * ‖a‖ := by
            simp only [ya, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
              abs_of_nonneg rpos.le]
            ring
          _ ≤ r * (δ + ε) * (‖z‖ + ε) := by gcongr
      calc
        ‖(fderiv ℝ Φ x - A) z‖ = ‖(fderiv ℝ Φ x - A) a + (fderiv ℝ Φ x - A) (z - a)‖ := by
          congr 1
          simp only [FunLike.coe_sub, map_sub, Pi.sub_apply]
          abel
        _ ≤ ‖(fderiv ℝ Φ x - A) a‖ + ‖(fderiv ℝ Φ x - A) (z - a)‖ := norm_add_le _ _
        _ ≤ (δ + ε) * (‖z‖ + ε) + ‖fderiv ℝ Φ x - A‖ * ‖z - a‖ := by
          apply add_le_add
          · rw [mul_assoc] at I
            exact (mul_le_mul_iff_right₀ rpos).1 I
          · apply ContinuousLinearMap.le_opNorm
        _ ≤ (δ + ε) * (‖z‖ + ε) + ‖fderiv ℝ Φ x - A‖ * ε := by
          rw [mem_closedBall_iff_norm'] at az
          gcongr
    -- The injective area formula (Simon 3.2) on measurable subsets of `s`.
    have hcore : ∀ B : Set E, MeasurableSet B → B ⊆ s →
        μHE[Module.finrank ℝ E] (Φ '' B) =
          ∫⁻ x in B, ENNReal.ofReal (fderiv ℝ Φ x).toLinearMap.normDet := by
      intro B hB hBs
      have hf' : ∀ x ∈ B, HasFDerivWithinAt Φ (fderiv ℝ Φ x) B x := fun x hx ↦
        (hΦ x (hBs hx)).hasFDerivAt.hasFDerivWithinAt
      have hinjB : InjOn Φ B := hinjΦ.mono hBs
      have hcomp : ∀ q : ℝ≥0, 1 < q →
          μHE[Module.finrank ℝ E] (Φ '' B) ≤
              (q : ℝ≥0∞) ^ 2 * ∫⁻ x in B, ENNReal.ofReal (fderiv ℝ Φ x).toLinearMap.normDet ∧
            (∫⁻ x in B, ENNReal.ofReal (fderiv ℝ Φ x).toLinearMap.normDet) ≤
              (q : ℝ≥0∞) ^ 2 * μHE[Module.finrank ℝ E] (Φ '' B) := by
        intro q hq
        rcases eq_empty_or_nonempty B with rfl | hBne
        · simp
        have hchoice : ∀ L : E →L[ℝ] F, ∃ δ : ℝ≥0, 0 < δ ∧ (Function.Injective L →
            (∀ C : E →L[ℝ] F, ‖C - L‖ ≤ δ →
              ENNReal.ofReal C.toLinearMap.normDet ≤ q * ENNReal.ofReal L.toLinearMap.normDet ∧
              ENNReal.ofReal L.toLinearMap.normDet ≤ q * ENNReal.ofReal C.toLinearMap.normDet) ∧
            (∀ (t : Set E) (φ : E → F), ApproximatesLinearOn φ L t δ →
              μHE[Module.finrank ℝ E] (φ '' t) ≤
                  q * (ENNReal.ofReal L.toLinearMap.normDet * volume t) ∧
                ENNReal.ofReal L.toLinearMap.normDet * volume t ≤
                  q * μHE[Module.finrank ℝ E] (φ '' t))) := by
          intro L
          by_cases hL : Function.Injective L
          · obtain ⟨δ, hδ, hJ, harea⟩ := hradius L hL q hq
            exact ⟨δ, hδ, fun _ ↦ ⟨hJ, harea⟩⟩
          · exact ⟨1, zero_lt_one, fun h ↦ (hL h).elim⟩
        choose δ hδpos hδ using hchoice
        obtain ⟨t, L, hdisj, ht, hcover, happrox, hactual⟩ :=
          exists_partition_approximatesLinearOn_of_hasFDerivWithinAt Φ B (fderiv ℝ Φ) hf' δ
            (fun L ↦ (hδpos L).ne')
        have hLreg (i : ℕ) : Function.Injective (L i) := by
          obtain ⟨x, hx, hL⟩ := hactual hBne i
          rw [hL]
          exact hregΦ x (hBs hx)
        have hseq : B = ⋃ i, B ∩ t i := by
          rw [← inter_iUnion]
          exact Subset.antisymm (subset_inter Subset.rfl hcover) inter_subset_left
        have hsumimage : μHE[Module.finrank ℝ E] (Φ '' B) =
            ∑' i, μHE[Module.finrank ℝ E] (Φ '' (B ∩ t i)) := by
          conv_lhs => rw [hseq, image_iUnion]
          apply measure_iUnion
          · intro i j hij
            exact Disjoint.image (Disjoint.mono inter_subset_right inter_subset_right (hdisj hij))
              hinjB inter_subset_left inter_subset_left
          · intro i
            apply (hB.inter (ht i)).image_of_continuousOn_injOn
            · exact fun x hx ↦ (hf' x hx.1).continuousWithinAt.mono inter_subset_left
            · exact hinjB.mono inter_subset_left
        have hsumintegral : (∫⁻ x in B, ENNReal.ofReal (fderiv ℝ Φ x).toLinearMap.normDet) =
            ∑' i, ∫⁻ x in B ∩ t i, ENNReal.ofReal (fderiv ℝ Φ x).toLinearMap.normDet := by
          conv_lhs => rw [hseq]
          exact lintegral_iUnion (fun i ↦ hB.inter (ht i))
            (pairwise_disjoint_mono hdisj (fun _ ↦ inter_subset_right)) _
        have hpiece (i : ℕ) :
            μHE[Module.finrank ℝ E] (Φ '' (B ∩ t i)) ≤ (q : ℝ≥0∞) ^ 2 *
                ∫⁻ x in B ∩ t i, ENNReal.ofReal (fderiv ℝ Φ x).toLinearMap.normDet ∧
              (∫⁻ x in B ∩ t i, ENNReal.ofReal (fderiv ℝ Φ x).toLinearMap.normDet) ≤
                (q : ℝ≥0∞) ^ 2 * μHE[Module.finrank ℝ E] (Φ '' (B ∩ t i)) := by
          have hJ := (hδ (L i) (hLreg i)).1
          obtain ⟨harea_upper, harea_lower⟩ := (hδ (L i) (hLreg i)).2 (B ∩ t i) Φ (happrox i)
          have hderiv := hderiv_ctrl (B ∩ t i) (L i) (δ (L i)) (happrox i) (hB.inter (ht i))
            (fun x hx ↦ (hf' x hx.1).mono inter_subset_left)
          have hJupper :
              (∫⁻ x in B ∩ t i, ENNReal.ofReal (fderiv ℝ Φ x).toLinearMap.normDet) ≤
                q * (ENNReal.ofReal (L i).toLinearMap.normDet * volume (B ∩ t i)) := by
            calc
              _ ≤ ∫⁻ _ in B ∩ t i, (q : ℝ≥0∞) * ENNReal.ofReal (L i).toLinearMap.normDet := by
                apply lintegral_mono_ae
                filter_upwards [hderiv] with x hx
                exact (hJ (fderiv ℝ Φ x) hx).1
              _ = _ := by rw [setLIntegral_const, mul_assoc]
          have hJlower : ENNReal.ofReal (L i).toLinearMap.normDet * volume (B ∩ t i) ≤
              q * ∫⁻ x in B ∩ t i, ENNReal.ofReal (fderiv ℝ Φ x).toLinearMap.normDet := by
            calc
              _ = ∫⁻ _ in B ∩ t i, ENNReal.ofReal (L i).toLinearMap.normDet :=
                (setLIntegral_const _ _).symm
              _ ≤ ∫⁻ x in B ∩ t i,
                  (q : ℝ≥0∞) * ENNReal.ofReal (fderiv ℝ Φ x).toLinearMap.normDet := by
                apply lintegral_mono_ae
                filter_upwards [hderiv] with x hx
                exact (hJ (fderiv ℝ Φ x) hx).2
              _ = _ := lintegral_const_mul' _ _ ENNReal.coe_ne_top
          constructor
          · calc
              _ ≤ q * (ENNReal.ofReal (L i).toLinearMap.normDet * volume (B ∩ t i)) :=
                harea_upper
              _ ≤ q * (q * ∫⁻ x in B ∩ t i,
                  ENNReal.ofReal (fderiv ℝ Φ x).toLinearMap.normDet) := by gcongr
              _ = _ := by rw [pow_two, mul_assoc]
          · calc
              _ ≤ q * (ENNReal.ofReal (L i).toLinearMap.normDet * volume (B ∩ t i)) := hJupper
              _ ≤ q * (q * μHE[Module.finrank ℝ E] (Φ '' (B ∩ t i))) := by gcongr
              _ = _ := by rw [pow_two, mul_assoc]
        rw [hsumimage, hsumintegral]
        constructor
        · calc
            _ ≤ ∑' i, (q : ℝ≥0∞) ^ 2 *
                ∫⁻ x in B ∩ t i, ENNReal.ofReal (fderiv ℝ Φ x).toLinearMap.normDet :=
              ENNReal.tsum_le_tsum (fun i ↦ (hpiece i).1)
            _ = _ := ENNReal.tsum_mul_left
        · calc
            _ ≤ ∑' i, (q : ℝ≥0∞) ^ 2 * μHE[Module.finrank ℝ E] (Φ '' (B ∩ t i)) :=
              ENNReal.tsum_le_tsum (fun i ↦ (hpiece i).2)
            _ = _ := ENNReal.tsum_mul_left
      have hlimit (a : ℝ≥0∞) :
          Tendsto (fun q : ℝ≥0 ↦ (q : ℝ≥0∞) ^ 2 * a) (𝓝[>] 1) (𝓝 a) := by
        have hcoe : Tendsto (fun q : ℝ≥0 ↦ (q : ℝ≥0∞)) (𝓝[>] 1) (𝓝 1) :=
          (ENNReal.tendsto_coe.2 tendsto_id).mono_left nhdsWithin_le_nhds
        simpa only [one_pow, one_mul] using
          ENNReal.Tendsto.mul_const (ENNReal.Tendsto.pow (n := 2) hcoe) (Or.inl (by simp))
      apply le_antisymm
      · apply ge_of_tendsto (hlimit _)
        filter_upwards [self_mem_nhdsWithin] with q hq
        exact (hcomp q hq).1
      · apply ge_of_tendsto (hlimit _)
        filter_upwards [self_mem_nhdsWithin] with q hq
        exact (hcomp q hq).2
    -- Measure-level transport, then the Bochner integral of an arbitrary real weight.
    have hcont : ContinuousOn Φ s := fun x hx ↦ (hΦ x hx).continuousAt.continuousWithinAt
    have hemb : MeasurableEmbedding (s.domRestrict Φ) := hcont.measurableEmbedding hs hinjΦ
    have hsub := MeasurableEmbedding.subtype_coe hs
    have hJmeas : Measurable (fun x : E ↦ (fderiv ℝ Φ x).toLinearMap.normDet) :=
      hcontJ.measurable.comp (measurable_fderiv ℝ Φ)
    -- Measure-level transport, then the weighted formula for an arbitrary weight.
    have hcont : ContinuousOn Φ s := fun x hx ↦ (hΦ x hx).continuousAt.continuousWithinAt
    have hemb : MeasurableEmbedding (s.domRestrict Φ) := hcont.measurableEmbedding hs hinjΦ
    have hsub := MeasurableEmbedding.subtype_coe hs
    have hJmeas : Measurable (fun x : E ↦ ENNReal.ofReal (fderiv ℝ Φ x).toLinearMap.normDet) :=
      (hcontJ.measurable.comp (measurable_fderiv ℝ Φ)).ennreal_ofReal
    have hmap : Measure.map (s.domRestrict Φ)
        (((volume : Measure E).withDensity
          (fun x ↦ ENNReal.ofReal (fderiv ℝ Φ x).toLinearMap.normDet)).comap
            (Subtype.val : s → E)) = (μHE[Module.finrank ℝ E] : Measure F).restrict (Φ '' s) := by
      ext u hu
      rw [Measure.map_apply hemb.measurable hu, hsub.comap_apply]
      have hBm : MeasurableSet (Subtype.val '' ((s.domRestrict Φ) ⁻¹' u)) :=
        hsub.measurableSet_image' (hemb.measurable hu)
      have hBs : Subtype.val '' ((s.domRestrict Φ) ⁻¹' u) ⊆ s := by
        rintro x ⟨v, _, rfl⟩
        exact v.property
      rw [withDensity_apply _ hBm, ← hcore _ hBm hBs, Measure.restrict_apply hu]
      congr 1
      ext y
      constructor
      · rintro ⟨x, ⟨v, hv, rfl⟩, rfl⟩
        exact ⟨hv, ⟨v, v.property, rfl⟩⟩
      · rintro ⟨hy, x, hx, rfl⟩
        exact ⟨x, ⟨⟨x, hx⟩, hy, rfl⟩, rfl⟩
    rw [← hmap, hemb.integral_map]
    change (∫ x : s, (fun x : E ↦ h (Φ x)) x ∂
      (((volume : Measure E).withDensity
        (fun x ↦ (((fderiv ℝ Φ x).toLinearMap.normDet.toNNReal : ℝ≥0) : ℝ≥0∞))).comap
          (Subtype.val : s → E))) = _
    rw [integral_subtype_comap hs (fun x : E ↦ h (Φ x)),
      setIntegral_withDensity_eq_setIntegral_smul₀ hJmeas.real_toNNReal.aemeasurable _ hs]
    refine setIntegral_congr_fun hs ?_
    intro x _
    show ((fderiv ℝ Φ x).toLinearMap.normDet.toNNReal : ℝ≥0) • h (Φ x) =
      (fderiv ℝ Φ x).toLinearMap.normDet * h (Φ x)
    rw [NNReal.smul_def, Real.coe_toNNReal _ (LinearMap.normDet_nonneg _), smul_eq_mul]
  intro n N r M V W K ψ g w hr hψ hM hK hKW hgK hw hwK htrace
  /- Step 1: the compact parameter set `Q = V ∩ ψ⁻¹(K)` (relative properness of the
  representation), with `w = 0` on `V \ Q`. -/
  have hV : IsOpen V := hψ.isOpen_source
  have hQ : IsCompact (V ∩ ψ ⁻¹' K) := hψ.isCompact_source_inter_preimage K hK hKW
  have hwQ : ∀ x ∈ V, x ∉ V ∩ ψ ⁻¹' K → w x = 0 := fun x hx hxQ ↦
    hwK x hx fun hxK ↦ hxQ ⟨hx, hxK⟩
  /- Step 2: `ψ(V) = W ∩ M ⊆ M`, and `g = 0` on `M \ ψ(V) = M \ W ⊆ M \ K`, so
  `∫_M g dHⁿ = ∫_{ψ(V)} g dHⁿ` (an identity of Bochner integrals; no integrability needed). -/
  have himage : ψ '' V = W ∩ M := hψ.image_eq
  have hrestrict : ∫ y in M, g y ∂μHE[n] = ∫ y in ψ '' V, g y ∂μHE[n] := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hM ?_ ?_
    · rw [himage]
      exact inter_subset_right
    · rintro y ⟨hyM, hyV⟩
      refine hgK y hyM fun hyK ↦ hyV ?_
      rw [himage]
      exact ⟨hKW hyK, hyM⟩
  /- Step 3: `ψ` is `C^r`, `r ≥ 1`, hence differentiable at every point of the open set `V`; its
  derivative is injective on `V` and `ψ` is injective on `V`. -/
  have hdiff : ∀ x ∈ V, DifferentiableAt ℝ ψ x := fun x hx ↦
    (hψ.contDiffOn.differentiableOn
      (by exact_mod_cast (ne_of_gt (lt_of_lt_of_le (show (0 : ℕ∞) < 1 by simp) hr))) x
      hx).differentiableAt (hV.mem_nhds hx)
  /- Step 4: the area formula for `ψ` on `V`, with `finrank ℝⁿ = n`. -/
  have key := area (Rn n) (Rn N) V ψ hV.measurableSet hdiff
    (fun x hx ↦ hψ.injective_fderiv hx) hψ.injOn g
  rw [finrank_euclideanSpace_fin] at key
  /- Steps 5–7: `Jψ · (g ∘ ψ) = trace Dw` on `V`, and the Euclidean divergence theorem for
  `(V, Q, w)`. -/
  rw [hrestrict, key]
  calc ∫ x in V, (fderiv ℝ ψ x).toLinearMap.normDet * g (ψ x)
      = ∫ x in V, LinearMap.trace ℝ (Rn n) (fderiv ℝ w x).toLinearMap := by
        refine setIntegral_congr_fun hV.measurableSet ?_
        intro x hx
        show (fderiv ℝ ψ x).toLinearMap.normDet * g (ψ x) =
          LinearMap.trace ℝ (Rn n) (fderiv ℝ w x).toLinearMap
        rw [htrace x hx, Chapter02.areaJacobianAt_eq_normDet]
    _ = 0 := Submission.euclidean_setIntegral_trace_fderiv_eq_zero n V (V ∩ ψ ⁻¹' K) w hV hQ
        inter_subset_left hw hwQ

/-- **Simon Ch. 2, (3.2) (p. 53), area formula: injective regular case.** Let `s ⊆ ℝⁿ` be Borel
and `Φ : ℝⁿ → ℝᴺ` differentiable at every point of `s`, with injective derivative `DΦ(x)` for
`x ∈ s`, and injective on `s`. Then `Hⁿ(Φ(s)) = ∫_s JΦ dHⁿ`, where `JΦ(x) = √det(DΦ(x)* ∘ DΦ(x))`
is `areaJacobian (DΦ(x))` and `Hⁿ = μHE[n]` (which is `Lⁿ` on `ℝⁿ`). The approximation argument
from the linear case 3.1 is carried out below. -/
theorem Submission.variation_injective_area_formula : ∀ (n N : ℕ) (s : Set (Rn n)) (Φ : Rn n → Rn N), MeasurableSet s → (∀ x ∈ s, DifferentiableAt ℝ Φ x) → (∀ x ∈ s, Function.Injective (fderiv ℝ Φ x)) → InjOn Φ s → μHE[n] (Φ '' s) = ∫⁻ x in s, ENNReal.ofReal (areaJacobian (fderiv ℝ Φ x)) ∂μHE[n] := by
  intro n N s Φ hs hΦ hreg hinj
  classical
  /- Simon (3.2) for an injective regular map in arbitrary codimension, with `normDet` for the
  Jacobian and Lebesgue measure on the source. This is the pinned SimonGMT theorem
  `Chapter02.injective_area_formula_of_injective_derivative` (stated there with
  `μHE[finrank ℝ E]` on the source, which equals Lebesgue measure), whose module is not imported
  here; its kernel-checked proof (SimonGMT `Chapter02/AreaApproximation`, `AreaDerivative`,
  `AreaFormula`, the derivative-control step adapted from Mathlib's
  `MeasureTheory/Function/Jacobian.lean`) is replayed as a local step. -/
  have area : ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F]
      [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
      (s : Set E) (Φ : E → F), MeasurableSet s → (∀ x ∈ s, DifferentiableAt ℝ Φ x) →
      (∀ x ∈ s, Function.Injective (fderiv ℝ Φ x)) → InjOn Φ s →
      μHE[Module.finrank ℝ E] (Φ '' s) =
        ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ Φ x).toLinearMap.normDet := by
    intro E F _ _ _ _ _ _ _ _ _ _ s Φ hs hΦ hregΦ hinjΦ
    -- The metric Jacobian `normDet` depends continuously on the linear map.
    have hcontJ : Continuous (fun L : E →L[ℝ] F ↦ L.toLinearMap.normDet) := by
      have heq : (fun L : E →L[ℝ] F ↦ L.toLinearMap.normDet) =
          fun L ↦ Real.sqrt ((L.adjoint ∘L L).det) := by
        funext L
        rw [← L.normDet_sq]
        simpa only [RCLike.ofReal_real_eq_id, id_eq] using
          (Real.sqrt_sq L.toLinearMap.normDet_nonneg).symm
      rw [heq]
      exact Real.continuous_sqrt.comp
        (ContinuousLinearMap.continuous_det.comp
          (Continuous.clm_comp ContinuousLinearMap.adjoint.continuous continuous_id))
    -- A comparison of pairwise distances gives a comparison of image measures.
    have himage_le : ∀ (φ γ : E → F) (t : Set E) (K : ℝ≥0), InjOn γ t →
        (∀ x ∈ t, ∀ y ∈ t, dist (φ x) (φ y) ≤ K * dist (γ x) (γ y)) →
        μHE[Module.finrank ℝ E] (φ '' t) ≤
          (K : ℝ≥0∞) ^ Module.finrank ℝ E * μHE[Module.finrank ℝ E] (γ '' t) := by
      intro φ γ t K hγ hφγ
      have hh : LipschitzOnWith K (φ ∘ Function.invFunOn γ t) (γ '' t) := by
        rw [lipschitzOnWith_iff_dist_le_mul]
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        simpa only [Function.comp_apply, hγ.leftInvOn_invFunOn hx,
          hγ.leftInvOn_invFunOn hy] using hφγ x hx y hy
      have himage : (φ ∘ Function.invFunOn γ t) '' (γ '' t) = φ '' t := by
        rw [image_comp, hγ.invFunOn_image Subset.rfl]
      simpa only [himage] using
        Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn (Module.finrank ℝ E) hh
    -- Upper and lower image estimates for a map approximating an injective linear map.
    have happrox_upper : ∀ (φ : E → F) (L : E →L[ℝ] F) (t : Set E) (δ K : ℝ≥0),
        ApproximatesLinearOn φ L t δ → AntilipschitzWith K L →
        μHE[Module.finrank ℝ E] (φ '' t) ≤ ((1 + δ * K : ℝ≥0) : ℝ≥0∞) ^ Module.finrank ℝ E *
          (ENNReal.ofReal L.toLinearMap.normDet * volume t) := by
      intro φ L t δ K hf hL
      rw [← L.toLinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume]
      apply himage_le φ L t _ hL.injective.injOn
      intro x hx y hy
      have hb : ‖x - y‖ ≤ K * ‖L x - L y‖ := by
        simpa only [dist_eq_norm] using hL.le_mul_dist x y
      have herror : ‖φ x - φ y - (L x - L y)‖ ≤ (δ : ℝ) * K * ‖L x - L y‖ := by
    rw [← hmap, hemb.lintegral_map]
    change (∫⁻ x : s, (fun x : E ↦ w (Φ x)) x ∂
      (((volume : Measure E).withDensity
        (fun x ↦ ENNReal.ofReal (fderiv ℝ Φ x).toLinearMap.normDet)).comap
          (Subtype.val : s → E))) = _
    rw [lintegral_subtype_comap hs (fun x : E ↦ w (Φ x)),
      setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀ _ _ _ hs]
    · rfl
    · simp only [eventually_true, ENNReal.ofReal_lt_top]
    · exact hJmeas.aemeasurable
  /- Step 1: `Ψ` is differentiable (hence continuous) at every point of the open set `Ω`. -/
  have hdiff : ∀ p ∈ Ω, DifferentiableAt ℝ Ψ p := fun p hp ↦
    (hΨ.differentiableOn one_ne_zero p hp).differentiableAt (hΩ.mem_nhds hp)
  /- Step 2: `S' = Ω ∩ Ψ⁻¹(S)` is Borel, via the measurable piecewise extension of `Ψ`. -/
  have hS'meas : MeasurableSet (Ω ∩ Ψ ⁻¹' S) := by
    have hm : Measurable (Ω.piecewise Ψ (fun _ ↦ (0 : Rn N))) :=
      hΨ.continuousOn.measurable_piecewise continuousOn_const hΩ.measurableSet
    have heq : Ω ∩ Ψ ⁻¹' S = Ω ∩ (Ω.piecewise Ψ (fun _ ↦ (0 : Rn N))) ⁻¹' S := by
      ext p
      simp only [mem_inter_iff, mem_preimage]
      constructor
      · rintro ⟨hp, h⟩
        exact ⟨hp, by rwa [Set.piecewise_eq_of_mem _ _ _ hp]⟩
      · rintro ⟨hp, h⟩
        exact ⟨hp, by rwa [Set.piecewise_eq_of_mem _ _ _ hp] at h⟩
    rw [heq]
    exact hΩ.measurableSet.inter (hm hS)
  /- Step 3: `Ψ(S') = S`. -/
  have himS : Ψ '' (Ω ∩ Ψ ⁻¹' S) = S := by
    ext x
    constructor
    · rintro ⟨p, ⟨_, hp⟩, rfl⟩
      exact hp
    · intro hx
      obtain ⟨p, hp, rfl⟩ := hSΨ hx
      exact ⟨p, ⟨hp, hx⟩, rfl⟩
  /- Step 4: `finrank P = m + k`. -/
  have hfin : Module.finrank ℝ (WithLp 2 (Rn m × Rn k)) = m + k := by
    rw [(WithLp.linearEquiv 2 ℝ (Rn m × Rn k)).finrank_eq, Module.finrank_prod,
      finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]
  /- Step 5: the weighted area formula for `Ψ` on `S'`, weight `g · J*f`. -/
  have key := area (WithLp 2 (Rn m × Rn k)) (Rn N) (Ω ∩ Ψ ⁻¹' S) Ψ hS'meas
    (fun p hp ↦ hdiff p hp.1) (fun p hp ↦ hreg p hp.1) (hΨinj.mono inter_subset_left)
    (fun x ↦ g x * ENNReal.ofReal (coareaJacobian M f x))
  rw [himS, hfin] at key
  rw [key]
  /- Step 6: chain rule. `f ∘ Ψ = fst` near each `p ∈ Ω`, so `Df(Ψ p) ∘ DΨ(p) = fst`. -/
  have hchain : ∀ p ∈ Ω, ∀ v, fderiv ℝ f (Ψ p) (fderiv ℝ Ψ p v) = WithLp.fst v := by
    intro p hp v
    have h1 : HasFDerivAt (f ∘ Ψ) ((fderiv ℝ f (Ψ p)).comp (fderiv ℝ Ψ p)) p :=
      (hfd p hp).hasFDerivAt.comp p (hdiff p hp).hasFDerivAt
    have h2 : HasFDerivAt (f ∘ Ψ) (WithLp.fstL 2 ℝ (Rn m) (Rn k)) p := by
      apply (WithLp.fstL 2 ℝ (Rn m) (Rn k)).hasFDerivAt.congr_of_eventuallyEq
      filter_upwards [hΩ.mem_nhds hp] with q hq
      exact hfΨ q hq
    have h3 := congrArg (fun T : WithLp 2 (Rn m × Rn k) →L[ℝ] Rn m ↦ T v) (h1.unique h2)
    simpa using h3
  /- Steps 7–9: the linear-algebra hypothesis at `x = Ψ p`, `A = DΨ(p)`, `B = DΨ(p) ∘ j`
  identifies the integrands on `S'`. -/
  apply setLIntegral_congr_fun hS'meas
  intro p hp
  have hjac := hLA (Ψ p) (fderiv ℝ Ψ p)
    ((fderiv ℝ Ψ p).comp
      ((WithLp.prodContinuousLinearEquiv 2 ℝ (Rn m) (Rn k)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.inr ℝ (Rn m) (Rn k))))
    (hreg p hp.1) (hT p hp.1) (hchain p hp.1) (fun _ ↦ rfl)
  have hnn : 0 ≤ coareaJacobian M f (Ψ p) := Real.sqrt_nonneg _
  simp only
  rw [← hjac, ENNReal.ofReal_mul hnn]
  ring

/-- **Simon Ch. 2, §6 (pp. 66–67), toward the co-area formula 6.6: fibrewise disintegration in a
chart.** Let `Ψ : ℝᵐ × ℝᵏ ⊇ Ω → ℝᴺ` be `C¹`, injective, with injective derivative, and straighten
`f` (`f ∘ Ψ = fst` on `Ω`). For Borel `S ⊆ Ψ(Ω)` and Borel `g ≥ 0`, the fibre integrals
`y ↦ ∫_{S ∩ f⁻¹y} g dHᵏ` are Borel and
`∫_{Ω ∩ Ψ⁻¹S} J_v Ψ · g ∘ Ψ = ∫_{ℝᵐ} ∫_{S ∩ f⁻¹y} g dHᵏ dLᵐ(y)`,
where `J_v Ψ(p) = normDet(DΨ(p) ∘ j)` is the area Jacobian of `Ψ` along the vertical directions
`j(b) = (0, b)`. Proof: the area formula (Simon 3.2, 3.5) for the fibre maps `b ↦ Ψ(a, b)` and
Tonelli. -/
theorem Submission.coarea_chart_fiber_disintegration : ∀ (N m k : ℕ) (f : Rn N → Rn m) (Ω : Set (WithLp 2 (Rn m × Rn k))) (Ψ : WithLp 2 (Rn m × Rn k) → Rn N) (S : Set (Rn N)) (g : Rn N → ℝ≥0∞), IsOpen Ω → ContDiffOn ℝ 1 Ψ Ω → InjOn Ψ Ω → (∀ p ∈ Ω, Function.Injective (fderiv ℝ Ψ p)) → (∀ p ∈ Ω, f (Ψ p) = WithLp.fst p) → MeasurableSet S → S ⊆ Ψ '' Ω → Measurable g → Measurable (fun y ↦ ∫⁻ x in S ∩ f ⁻¹' {y}, g x ∂μHE[k]) ∧ ∫⁻ p in Ω ∩ Ψ ⁻¹' S, ENNReal.ofReal (((fderiv ℝ Ψ p).comp ((WithLp.prodContinuousLinearEquiv 2 ℝ (Rn m) (Rn k)).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ (Rn m) (Rn k)))).toLinearMap.normDet) * g (Ψ p) = ∫⁻ y, ∫⁻ x in S ∩ f ⁻¹' {y}, g x ∂μHE[k] ∂volume := by
  intro N m k f Ω Ψ S g hΩ hΨ hinj hreg hfΨ hS hSΨ hg
  classical
  /- Part I: the area formula (Simon 3.2, 3.5) for an injective map `ℝᵏ → ℝᴺ` with injective
  derivative, proved as in SimonGMT `Chapter02.AreaFormula` (not among this file's imports): cut the
  source into pieces on which the map is close to a linear map, compare with the linear area formula
  on each piece, and let the relative error tend to `1`. -/
  -- Step 1: the metric Jacobian `normDet` depends continuously on the linear map.
  have hcont_nd : Continuous (fun L : Rn k →L[ℝ] Rn N ↦ L.toLinearMap.normDet) := by
    have heq : (fun L : Rn k →L[ℝ] Rn N ↦ L.toLinearMap.normDet) =
        fun L ↦ Real.sqrt ((ContinuousLinearMap.adjoint L ∘L L).det) := by
      funext L
      rw [← L.normDet_sq]
      simpa only [RCLike.ofReal_real_eq_id, id_eq] using
        (Real.sqrt_sq L.toLinearMap.normDet_nonneg).symm
    rw [heq]
    exact Real.continuous_sqrt.comp (ContinuousLinearMap.continuous_det.comp
      (Continuous.clm_comp ContinuousLinearMap.adjoint.continuous continuous_id))
  -- Step 2: the linear area formula (Simon 3.1), `Hᵏ(L(t)) = normDet L · Lᵏ(t)`.
  have hlin : ∀ (L : Rn k →L[ℝ] Rn N) (t : Set (Rn k)),
      μHE[k] (L '' t) = ENNReal.ofReal L.toLinearMap.normDet * volume t := by
    intro L t
    have h := L.toLinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume t
    rwa [finrank_euclideanSpace_fin, ContinuousLinearMap.coe_coe] at h
  -- Step 3: a pairwise distance comparison of two maps compares the measures of the images.
  have hdist : ∀ (φ₁ φ₂ : Rn k → Rn N) (t : Set (Rn k)) (K : ℝ≥0), InjOn φ₂ t →
      (∀ x ∈ t, ∀ y ∈ t, dist (φ₁ x) (φ₁ y) ≤ K * dist (φ₂ x) (φ₂ y)) →
      μHE[k] (φ₁ '' t) ≤ (K : ℝ≥0∞) ^ k * μHE[k] (φ₂ '' t) := by
    intro φ₁ φ₂ t K h₂ h₁₂
    have hh : LipschitzOnWith K (φ₁ ∘ Function.invFunOn φ₂ t) (φ₂ '' t) := by
      rw [lipschitzOnWith_iff_dist_le_mul]
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simpa only [Function.comp_apply, h₂.leftInvOn_invFunOn hx, h₂.leftInvOn_invFunOn hy] using
        h₁₂ x hx y hy
    have himage : (φ₁ ∘ Function.invFunOn φ₂ t) '' (φ₂ '' t) = φ₁ '' t := by
      rw [image_comp, h₂.invFunOn_image Subset.rfl]
    simpa only [himage] using Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn k hh
  -- Step 4: a map `δ`-close to an injective linear map `L` (`L` `K`-antilipschitz) multiplies
  -- `Hᵏ` by `normDet L` up to the factors `(1 + δK)ᵏ` and `(1 - δK)⁻ᵏ`.
  have hupper : ∀ (φ₁ : Rn k → Rn N) (L : Rn k →L[ℝ] Rn N) (t : Set (Rn k)) (δ K : ℝ≥0),
      ApproximatesLinearOn φ₁ L t δ → AntilipschitzWith K L →
      μHE[k] (φ₁ '' t) ≤
        ((1 + δ * K : ℝ≥0) : ℝ≥0∞) ^ k * (ENNReal.ofReal L.toLinearMap.normDet * volume t) := by
    intro φ₁ L t δ K hf hL
    rw [← hlin]
    apply hdist φ₁ L t _ hL.injective.injOn
    intro x hx y hy
    have hb : ‖x - y‖ ≤ K * ‖L x - L y‖ := by
      simpa only [dist_eq_norm] using hL.le_mul_dist x y
    have herror : ‖φ₁ x - φ₁ y - (L x - L y)‖ ≤ (δ : ℝ) * K * ‖L x - L y‖ := by
      calc
        _ ≤ δ * ‖x - y‖ := by simpa only [map_sub] using hf x hx y hy
        _ ≤ δ * (K * ‖L x - L y‖) := mul_le_mul_of_nonneg_left hb δ.2
        _ = _ := by ring
    simp only [dist_eq_norm, NNReal.coe_add, NNReal.coe_one, NNReal.coe_mul]
    calc
      ‖φ₁ x - φ₁ y‖ ≤ ‖φ₁ x - φ₁ y - (L x - L y)‖ + ‖L x - L y‖ := norm_le_norm_sub_add _ _
      _ ≤ (δ : ℝ) * K * ‖L x - L y‖ + ‖L x - L y‖ := add_le_add herror le_rfl
      _ = (1 + (δ : ℝ) * K) * ‖L x - L y‖ := by ring
  have hlower : ∀ (φ₁ : Rn k → Rn N) (L : Rn k →L[ℝ] Rn N) (t : Set (Rn k)) (δ K : ℝ≥0),
      ApproximatesLinearOn φ₁ L t δ → AntilipschitzWith K L → δ * K < 1 →
      ENNReal.ofReal L.toLinearMap.normDet * volume t ≤
        (((1 - δ * K)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ k * μHE[k] (φ₁ '' t) := by
    intro φ₁ L t δ K hf hL hδ
    have hδR : (δ : ℝ) * K < 1 := hδ
    have hd : ∀ x ∈ t, ∀ y ∈ t,
        dist (L x) (L y) ≤ ((1 - δ * K)⁻¹ : ℝ≥0) * dist (φ₁ x) (φ₁ y) := by
      intro x hx y hy
      have hb : ‖x - y‖ ≤ K * ‖L x - L y‖ := by
        simpa only [dist_eq_norm] using hL.le_mul_dist x y
      have herror : ‖φ₁ x - φ₁ y - (L x - L y)‖ ≤ (δ : ℝ) * K * ‖L x - L y‖ := by
        calc
          _ ≤ δ * ‖x - y‖ := by simpa only [map_sub] using hf x hx y hy
          _ ≤ δ * (K * ‖L x - L y‖) := mul_le_mul_of_nonneg_left hb δ.2
          _ = _ := by ring
      simp only [dist_eq_norm, NNReal.coe_add, NNReal.coe_one, NNReal.coe_mul]
      calc
        ‖φ x - φ y‖ ≤ ‖φ x - φ y - (L x - L y)‖ + ‖L x - L y‖ := norm_le_norm_sub_add _ _
        _ ≤ (δ : ℝ) * K * ‖L x - L y‖ + ‖L x - L y‖ := add_le_add herror le_rfl
        _ = (1 + (δ : ℝ) * K) * ‖L x - L y‖ := by ring
    have happrox_lower : ∀ (φ : E → F) (L : E →L[ℝ] F) (t : Set E) (δ K : ℝ≥0),
        ApproximatesLinearOn φ L t δ → AntilipschitzWith K L → δ * K < 1 →
        ENNReal.ofReal L.toLinearMap.normDet * volume t ≤
          (((1 - δ * K)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ Module.finrank ℝ E *
            μHE[Module.finrank ℝ E] (φ '' t) := by
      intro φ L t δ K hf hL hδ
      have hδR : (δ : ℝ) * K < 1 := hδ
      have hdist : ∀ x ∈ t, ∀ y ∈ t, dist (L x) (L y) ≤
          ((1 - δ * K)⁻¹ : ℝ≥0) * dist (φ x) (φ y) := by
        intro x hx y hy
        have hb : ‖x - y‖ ≤ K * ‖L x - L y‖ := by
          simpa only [dist_eq_norm] using hL.le_mul_dist x y
        have herror : ‖φ x - φ y - (L x - L y)‖ ≤ (δ : ℝ) * K * ‖L x - L y‖ := by
          calc
            _ ≤ δ * ‖x - y‖ := by simpa only [map_sub] using hf x hx y hy
            _ ≤ δ * (K * ‖L x - L y‖) := mul_le_mul_of_nonneg_left hb δ.2
            _ = _ := by ring
        have htriangle : ‖L x - L y‖ ≤ ‖φ x - φ y‖ + ‖φ x - φ y - (L x - L y)‖ := by
          simpa only [norm_sub_rev, add_comm] using
            (norm_le_norm_sub_add (L x - L y) (φ x - φ y))
        simp only [dist_eq_norm, NNReal.coe_inv, NNReal.coe_sub hδ.le, NNReal.coe_one,
          NNReal.coe_mul, inv_mul_eq_div]
        apply (le_div_iff₀ (sub_pos.mpr hδR)).mpr
        nlinarith
      have hφinj : InjOn φ t := by
        intro x hx y hy hxy
        apply hL.injective
        apply dist_le_zero.mp
        simpa only [hxy, dist_self, mul_zero] using hdist x hx y hy
      rw [← L.toLinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume]
      exact himage_le L φ t _ hφinj hdist
    -- One approximation radius controls both the image measure and nearby Jacobians.
    have hradius : ∀ L : E →L[ℝ] F, Function.Injective L → ∀ q : ℝ≥0, 1 < q →
        ∃ δ : ℝ≥0, 0 < δ ∧
          (∀ B : E →L[ℝ] F, ‖B - L‖ ≤ δ →
            ENNReal.ofReal B.toLinearMap.normDet ≤ q * ENNReal.ofReal L.toLinearMap.normDet ∧
            ENNReal.ofReal L.toLinearMap.normDet ≤ q * ENNReal.ofReal B.toLinearMap.normDet) ∧
          (∀ (t : Set E) (φ : E → F), ApproximatesLinearOn φ L t δ →
            μHE[Module.finrank ℝ E] (φ '' t) ≤
                q * (ENNReal.ofReal L.toLinearMap.normDet * volume t) ∧
              ENNReal.ofReal L.toLinearMap.normDet * volume t ≤
                q * μHE[Module.finrank ℝ E] (φ '' t)) := by
      intro L hL q hq
      obtain ⟨δ₀, hδ₀, harea⟩ : ∃ δ : ℝ≥0, 0 < δ ∧ ∀ (t : Set E) (φ : E → F),
          ApproximatesLinearOn φ L t δ →
          μHE[Module.finrank ℝ E] (φ '' t) ≤
              q * (ENNReal.ofReal L.toLinearMap.normDet * volume t) ∧
            ENNReal.ofReal L.toLinearMap.normDet * volume t ≤
              q * μHE[Module.finrank ℝ E] (φ '' t) := by
        obtain ⟨K, _, hK⟩ :=
          L.toLinearMap.exists_antilipschitzWith (LinearMap.ker_eq_bot.mpr hL)
        have hsmall : ∀ᶠ δ : ℝ≥0 in 𝓝 0, δ * K < 1 :=
          (continuousAt_id.mul continuousAt_const).eventually_lt continuousAt_const (by simp)
        have hupper : ∀ᶠ δ : ℝ≥0 in 𝓝 0, (1 + δ * K) ^ Module.finrank ℝ E < q :=
          ((continuousAt_const.add (continuousAt_id.mul continuousAt_const)).pow _).eventually_lt
            continuousAt_const (by simpa using hq)
        have hlower : ∀ᶠ δ : ℝ≥0 in 𝓝 0, ((1 - δ * K)⁻¹) ^ Module.finrank ℝ E < q := by
          apply ContinuousAt.eventually_lt _ continuousAt_const (by simpa using hq)
          apply ContinuousAt.pow
          apply ContinuousAt.inv₀
          · exact continuousAt_const.sub (continuousAt_id.mul continuousAt_const)
          · simp
        have hevent : ∀ᶠ δ : ℝ≥0 in 𝓝[>] 0, 0 < δ ∧ δ * K < 1 ∧
            (1 + δ * K) ^ Module.finrank ℝ E < q ∧ ((1 - δ * K)⁻¹) ^ Module.finrank ℝ E < q := by
          filter_upwards [self_mem_nhdsWithin, hsmall.filter_mono nhdsWithin_le_nhds,
            hupper.filter_mono nhdsWithin_le_nhds, hlower.filter_mono nhdsWithin_le_nhds]
            with δ hδ hsmall hupper hlower
          exact ⟨hδ, hsmall, hupper, hlower⟩
        obtain ⟨δ, hδ, hδsmall, hδupper, hδlower⟩ := hevent.exists
        refine ⟨δ, hδ, fun t φ hf ↦ ⟨?_, ?_⟩⟩
        · refine (happrox_upper φ L t δ K hf hK).trans ?_
          gcongr
          exact_mod_cast hδupper.le
        · refine (happrox_lower φ L t δ K hf hK hδsmall).trans ?_
          gcongr
          exact_mod_cast hδlower.le
      have hJ : 0 < L.toLinearMap.normDet := by
        apply lt_of_le_of_ne L.toLinearMap.normDet_nonneg
        exact Ne.symm ((L.toLinearMap.normDet_ne_zero_tfae.out 5 1).mp hL)
      have hqR : (1 : ℝ) < q := hq
      have hmul : L.toLinearMap.normDet < (q : ℝ) * L.toLinearMap.normDet := by nlinarith
      have hnear : ∀ᶠ B : E →L[ℝ] F in 𝓝 L,
          B.toLinearMap.normDet < (q : ℝ) * L.toLinearMap.normDet ∧
            L.toLinearMap.normDet < (q : ℝ) * B.toLinearMap.normDet :=
        (hcontJ.continuousAt.eventually_lt continuousAt_const hmul).and
          (continuousAt_const.eventually_lt (continuousAt_const.mul hcontJ.continuousAt) hmul)
      obtain ⟨ε, hε, hnear⟩ := Metric.eventually_nhds_iff.mp hnear
      let δ₁ : ℝ≥0 := ⟨ε / 2, (half_pos hε).le⟩
      refine ⟨min δ₀ δ₁, lt_min hδ₀ (half_pos hε), ?_, ?_⟩
      · intro B hB
        have hdist : dist B L < ε := by
          rw [dist_eq_norm]
          exact hB.trans_lt (lt_of_le_of_lt (by exact_mod_cast min_le_right δ₀ δ₁)
            (half_lt_self hε))
        obtain ⟨hupper, hlower⟩ := hnear hdist
        constructor
        · simpa only [ENNReal.ofReal_mul (NNReal.coe_nonneg q), ENNReal.ofReal_coe_nnreal] using
            ENNReal.ofReal_le_ofReal hupper.le
        · simpa only [ENNReal.ofReal_mul (NNReal.coe_nonneg q), ENNReal.ofReal_coe_nnreal] using
            ENNReal.ofReal_le_ofReal hlower.le
      · intro t φ hf
        exact harea t φ (hf.mono_num (min_le_left _ _))
    -- At almost every point of a measurable approximation piece the derivative is within the
    -- approximation error of the approximating linear map (Lebesgue density points).
    have hderiv_ctrl : ∀ (t : Set E) (A : E →L[ℝ] F) (δ : ℝ≥0), ApproximatesLinearOn Φ A t δ →
        MeasurableSet t → (∀ x ∈ t, HasFDerivWithinAt Φ (fderiv ℝ Φ x) t x) →
        ∀ᵐ x ∂(volume : Measure E).restrict t, ‖fderiv ℝ Φ x - A‖₊ ≤ δ := by
      intro t A δ hf ht hf'
      open scoped Pointwise in
      filter_upwards [Besicovitch.ae_tendsto_measure_inter_div (volume : Measure E) t,
        ae_restrict_mem ht]
      intro x hx xt
      apply ContinuousLinearMap.opNorm_le_bound _ δ.2 fun z ↦ ?_
      suffices H : ∀ ε, 0 < ε →
          ‖(fderiv ℝ Φ x - A) z‖ ≤ (δ + ε) * (‖z‖ + ε) + ‖fderiv ℝ Φ x - A‖ * ε by
        have : Tendsto (fun ε : ℝ ↦ ((δ : ℝ) + ε) * (‖z‖ + ε) + ‖fderiv ℝ Φ x - A‖ * ε)
            (𝓝[>] 0) (𝓝 ((δ + 0) * (‖z‖ + 0) + ‖fderiv ℝ Φ x - A‖ * 0)) :=
          Tendsto.mono_left (Continuous.tendsto (by fun_prop) 0) nhdsWithin_le_nhds
        simp only [add_zero, mul_zero] at this
        apply le_of_tendsto_of_tendsto tendsto_const_nhds this
        filter_upwards [self_mem_nhdsWithin]
        exact H
      intro ε εpos
      have B₁ : ∀ᶠ r in 𝓝[>] (0 : ℝ), (t ∩ ({x} + r • closedBall z ε)).Nonempty :=
        Measure.eventually_nonempty_inter_smul_of_density_one volume t x hx _
          measurableSet_closedBall (measure_closedBall_pos volume z εpos).ne'
      obtain ⟨ρ, ρpos, hρ⟩ : ∃ ρ > 0,
          ball x ρ ∩ t ⊆ {y : E | ‖Φ y - Φ x - (fderiv ℝ Φ x) (y - x)‖ ≤ ε * ‖y - x‖} :=
        mem_nhdsWithin_iff.1 ((hf' x xt).isLittleO.bound εpos)
      have B₂ : ∀ᶠ r in 𝓝[>] (0 : ℝ), {x} + r • closedBall z ε ⊆ ball x ρ := by
        apply nhdsWithin_le_nhds
        exact eventually_singleton_add_smul_subset isBounded_closedBall (ball_mem_nhds x ρpos)
      obtain ⟨r, ⟨y, ⟨yt, hy⟩⟩, rρ, rpos⟩ : ∃ r : ℝ, (t ∩ ({x} + r • closedBall z ε)).Nonempty ∧
          {x} + r • closedBall z ε ⊆ ball x ρ ∧ 0 < r :=
        (B₁.and (B₂.and self_mem_nhdsWithin)).exists
      obtain ⟨a, az, ya⟩ : ∃ a, a ∈ closedBall z ε ∧ y = x + r • a := by
        simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hy
        rcases hy with ⟨a, az, ha⟩
        exact ⟨a, az, by simp only [ha, add_neg_cancel_left]⟩
      have norm_a : ‖a‖ ≤ ‖z‖ + ε :=
        calc
          ‖a‖ = ‖z + (a - z)‖ := by simp only [add_sub_cancel]
          _ ≤ ‖z‖ + ‖a - z‖ := norm_add_le _ _
          _ ≤ ‖z‖ + ε := by grw [mem_closedBall_iff_norm.1 az]
      have I : r * ‖(fderiv ℝ Φ x - A) a‖ ≤ r * (δ + ε) * (‖z‖ + ε) :=
        calc
          r * ‖(fderiv ℝ Φ x - A) a‖ = ‖(fderiv ℝ Φ x - A) (r • a)‖ := by
            simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
          _ = ‖Φ y - Φ x - A (y - x) - (Φ y - Φ x - (fderiv ℝ Φ x) (y - x))‖ := by
            simp only [ya, add_sub_cancel_left, sub_sub_sub_cancel_left, FunLike.coe_sub,
              Pi.sub_apply, map_smul, smul_sub]
          _ ≤ ‖Φ y - Φ x - A (y - x)‖ + ‖Φ y - Φ x - (fderiv ℝ Φ x) (y - x)‖ :=
            norm_sub_le _ _
          _ ≤ δ * ‖y - x‖ + ε * ‖y - x‖ := add_le_add (hf _ yt _ xt) (hρ ⟨rρ hy, yt⟩)
          _ = r * (δ + ε) * ‖a‖ := by
            simp only [ya, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
              abs_of_nonneg rpos.le]
            ring
          _ ≤ r * (δ + ε) * (‖z‖ + ε) := by gcongr
      calc
        ‖(fderiv ℝ Φ x - A) z‖ = ‖(fderiv ℝ Φ x - A) a + (fderiv ℝ Φ x - A) (z - a)‖ := by
          congr 1
          simp only [FunLike.coe_sub, map_sub, Pi.sub_apply]
          abel
        _ ≤ ‖(fderiv ℝ Φ x - A) a‖ + ‖(fderiv ℝ Φ x - A) (z - a)‖ := norm_add_le _ _
        _ ≤ (δ + ε) * (‖z‖ + ε) + ‖fderiv ℝ Φ x - A‖ * ‖z - a‖ := by
          apply add_le_add
          · rw [mul_assoc] at I
            exact (mul_le_mul_iff_right₀ rpos).1 I
          · apply ContinuousLinearMap.le_opNorm
        _ ≤ (δ + ε) * (‖z‖ + ε) + ‖fderiv ℝ Φ x - A‖ * ε := by
          rw [mem_closedBall_iff_norm'] at az
          gcongr
    -- The injective area formula (Simon 3.2) on measurable subsets of `s`.
    have hcore : ∀ B : Set E, MeasurableSet B → B ⊆ s →
        μHE[Module.finrank ℝ E] (Φ '' B) =
          ∫⁻ x in B, ENNReal.ofReal (fderiv ℝ Φ x).toLinearMap.normDet := by
      intro B hB hBs
      have hf' : ∀ x ∈ B, HasFDerivWithinAt Φ (fderiv ℝ Φ x) B x := fun x hx ↦
        (hΦ x (hBs hx)).hasFDerivAt.hasFDerivWithinAt
      have hinjB : InjOn Φ B := hinjΦ.mono hBs
      have hcomp : ∀ q : ℝ≥0, 1 < q →
          μHE[Module.finrank ℝ E] (Φ '' B) ≤
              (q : ℝ≥0∞) ^ 2 * ∫⁻ x in B, ENNReal.ofReal (fderiv ℝ Φ x).toLinearMap.normDet ∧
            (∫⁻ x in B, ENNReal.ofReal (fderiv ℝ Φ x).toLinearMap.normDet) ≤
              (q : ℝ≥0∞) ^ 2 * μHE[Module.finrank ℝ E] (Φ '' B) := by
        intro q hq
        rcases eq_empty_or_nonempty B with rfl | hBne
        · simp
        have hchoice : ∀ L : E →L[ℝ] F, ∃ δ : ℝ≥0, 0 < δ ∧ (Function.Injective L →
            (∀ C : E →L[ℝ] F, ‖C - L‖ ≤ δ →
              ENNReal.ofReal C.toLinearMap.normDet ≤ q * ENNReal.ofReal L.toLinearMap.normDet ∧
              ENNReal.ofReal L.toLinearMap.normDet ≤ q * ENNReal.ofReal C.toLinearMap.normDet) ∧
            (∀ (t : Set E) (φ : E → F), ApproximatesLinearOn φ L t δ →
              μHE[Module.finrank ℝ E] (φ '' t) ≤
                  q * (ENNReal.ofReal L.toLinearMap.normDet * volume t) ∧
                ENNReal.ofReal L.toLinearMap.normDet * volume t ≤
                  q * μHE[Module.finrank ℝ E] (φ '' t))) := by
          intro L
          by_cases hL : Function.Injective L
          · obtain ⟨δ, hδ, hJ, harea⟩ := hradius L hL q hq
            exact ⟨δ, hδ, fun _ ↦ ⟨hJ, harea⟩⟩
          · exact ⟨1, zero_lt_one, fun h ↦ (hL h).elim⟩
        choose δ hδpos hδ using hchoice
        obtain ⟨t, L, hdisj, ht, hcover, happrox, hactual⟩ :=
          exists_partition_approximatesLinearOn_of_hasFDerivWithinAt Φ B (fderiv ℝ Φ) hf' δ
            (fun L ↦ (hδpos L).ne')
        have hLreg (i : ℕ) : Function.Injective (L i) := by
          obtain ⟨x, hx, hL⟩ := hactual hBne i
          rw [hL]
          exact hregΦ x (hBs hx)
        have hseq : B = ⋃ i, B ∩ t i := by
          rw [← inter_iUnion]
          exact Subset.antisymm (subset_inter Subset.rfl hcover) inter_subset_left
        have hsumimage : μHE[Module.finrank ℝ E] (Φ '' B) =
            ∑' i, μHE[Module.finrank ℝ E] (Φ '' (B ∩ t i)) := by
          conv_lhs => rw [hseq, image_iUnion]
          apply measure_iUnion
          · intro i j hij
            exact Disjoint.image (Disjoint.mono inter_subset_right inter_subset_right (hdisj hij))
              hinjB inter_subset_left inter_subset_left
          · intro i
            apply (hB.inter (ht i)).image_of_continuousOn_injOn
            · exact fun x hx ↦ (hf' x hx.1).continuousWithinAt.mono inter_subset_left
            · exact hinjB.mono inter_subset_left
        have hsumintegral : (∫⁻ x in B, ENNReal.ofReal (fderiv ℝ Φ x).toLinearMap.normDet) =
            ∑' i, ∫⁻ x in B ∩ t i, ENNReal.ofReal (fderiv ℝ Φ x).toLinearMap.normDet := by
          conv_lhs => rw [hseq]
          exact lintegral_iUnion (fun i ↦ hB.inter (ht i))
            (pairwise_disjoint_mono hdisj (fun _ ↦ inter_subset_right)) _
        have hpiece (i : ℕ) :
            μHE[Module.finrank ℝ E] (Φ '' (B ∩ t i)) ≤ (q : ℝ≥0∞) ^ 2 *
                ∫⁻ x in B ∩ t i, ENNReal.ofReal (fderiv ℝ Φ x).toLinearMap.normDet ∧
              (∫⁻ x in B ∩ t i, ENNReal.ofReal (fderiv ℝ Φ x).toLinearMap.normDet) ≤
                (q : ℝ≥0∞) ^ 2 * μHE[Module.finrank ℝ E] (Φ '' (B ∩ t i)) := by
          have hJ := (hδ (L i) (hLreg i)).1
          obtain ⟨harea_upper, harea_lower⟩ := (hδ (L i) (hLreg i)).2 (B ∩ t i) Φ (happrox i)
          have hderiv := hderiv_ctrl (B ∩ t i) (L i) (δ (L i)) (happrox i) (hB.inter (ht i))
            (fun x hx ↦ (hf' x hx.1).mono inter_subset_left)
          have hJupper :
              (∫⁻ x in B ∩ t i, ENNReal.ofReal (fderiv ℝ Φ x).toLinearMap.normDet) ≤
                q * (ENNReal.ofReal (L i).toLinearMap.normDet * volume (B ∩ t i)) := by
            calc
              _ ≤ ∫⁻ _ in B ∩ t i, (q : ℝ≥0∞) * ENNReal.ofReal (L i).toLinearMap.normDet := by
                apply lintegral_mono_ae
                filter_upwards [hderiv] with x hx
                exact (hJ (fderiv ℝ Φ x) hx).1
              _ = _ := by rw [setLIntegral_const, mul_assoc]
          have hJlower : ENNReal.ofReal (L i).toLinearMap.normDet * volume (B ∩ t i) ≤
              q * ∫⁻ x in B ∩ t i, ENNReal.ofReal (fderiv ℝ Φ x).toLinearMap.normDet := by
            calc
              _ = ∫⁻ _ in B ∩ t i, ENNReal.ofReal (L i).toLinearMap.normDet :=
                (setLIntegral_const _ _).symm
              _ ≤ ∫⁻ x in B ∩ t i,
                  (q : ℝ≥0∞) * ENNReal.ofReal (fderiv ℝ Φ x).toLinearMap.normDet := by
                apply lintegral_mono_ae
                filter_upwards [hderiv] with x hx
                exact (hJ (fderiv ℝ Φ x) hx).2
              _ = _ := lintegral_const_mul' _ _ ENNReal.coe_ne_top
          constructor
          · calc
              _ ≤ q * (ENNReal.ofReal (L i).toLinearMap.normDet * volume (B ∩ t i)) :=
                harea_upper
              _ ≤ q * (q * ∫⁻ x in B ∩ t i,
                  ENNReal.ofReal (fderiv ℝ Φ x).toLinearMap.normDet) := by gcongr
              _ = _ := by rw [pow_two, mul_assoc]
          · calc
              _ ≤ q * (ENNReal.ofReal (L i).toLinearMap.normDet * volume (B ∩ t i)) := hJupper
              _ ≤ q * (q * μHE[Module.finrank ℝ E] (Φ '' (B ∩ t i))) := by gcongr
              _ = _ := by rw [pow_two, mul_assoc]
        rw [hsumimage, hsumintegral]
        constructor
        · calc
            _ ≤ ∑' i, (q : ℝ≥0∞) ^ 2 *
                ∫⁻ x in B ∩ t i, ENNReal.ofReal (fderiv ℝ Φ x).toLinearMap.normDet :=
              ENNReal.tsum_le_tsum (fun i ↦ (hpiece i).1)
            _ = _ := ENNReal.tsum_mul_left
        · calc
            _ ≤ ∑' i, (q : ℝ≥0∞) ^ 2 * μHE[Module.finrank ℝ E] (Φ '' (B ∩ t i)) :=
              ENNReal.tsum_le_tsum (fun i ↦ (hpiece i).2)
            _ = _ := ENNReal.tsum_mul_left
      have hlimit (a : ℝ≥0∞) :
          Tendsto (fun q : ℝ≥0 ↦ (q : ℝ≥0∞) ^ 2 * a) (𝓝[>] 1) (𝓝 a) := by
        have hcoe : Tendsto (fun q : ℝ≥0 ↦ (q : ℝ≥0∞)) (𝓝[>] 1) (𝓝 1) :=
          (ENNReal.tendsto_coe.2 tendsto_id).mono_left nhdsWithin_le_nhds
        simpa only [one_pow, one_mul] using
          ENNReal.Tendsto.mul_const (ENNReal.Tendsto.pow (n := 2) hcoe) (Or.inl (by simp))
      apply le_antisymm
      · apply ge_of_tendsto (hlimit _)
        filter_upwards [self_mem_nhdsWithin] with q hq
        exact (hcomp q hq).1
      · apply ge_of_tendsto (hlimit _)
        filter_upwards [self_mem_nhdsWithin] with q hq
        exact (hcomp q hq).2
    exact hcore s hs subset_rfl
  /- Step 1: `areaJacobian L = √det(L* ∘ L) = √(normDet L ^ 2) = normDet L`, `finrank ℝⁿ = n`, and
  `μHE[n] = Lⁿ` on `ℝⁿ`. -/
  have hJ : ∀ L : Rn n →L[ℝ] Rn N, areaJacobian L = (L : Rn n →ₗ[ℝ] Rn N).normDet := by
    intro L
    have h := L.normDet_sq
    simp only [RCLike.ofReal_real_eq_id, id] at h
    rw [areaJacobian, ← h, Real.sqrt_sq (LinearMap.normDet_nonneg _)]
  have key := area (Rn n) (Rn N) s Φ hs hΦ hreg hinj
  rw [finrank_euclideanSpace_fin] at key
  rw [key, EuclideanSpace.euclideanHausdorffMeasure_eq_volume n]
  simp only [hJ]

/-- **Simon Ch. 2, divergence theorem on a submanifold (4.22(*), 4.29–4.30), proof steps 3a–3b:
a finite `C¹` partition of unity near a compact set.** If `C ⊆ ℝᴺ` is compact and every `y ∈ C`
lies in an open `U` with `P U`, there are finitely many `C¹` compactly supported `ζ_q` with
`tsupport ζ_q ⊆ U_q`, `P U_q`, and `∑_q ζ_q = 1` on an open `O ⊇ C`. Cover `C` by finitely many
open balls `ball c_q (ε_q / 4)` with `ball c_q ε_q ⊆ U_{c_q}`, take bumps `β_q` equal to `1` on
`closedBall c_q (ε_q / 4)` with `tsupport β_q = closedBall c_q (ε_q / 2)`, and set
`ζ_q = β_q ∏_{l<q} (1 - β_l)`; telescoping gives `∑_q ζ_q = 1 - ∏_q (1 - β_q)`, which is `1` on
`O = ⋃_q ball c_q (ε_q / 4)`. -/
theorem Submission.exists_finite_contDiff_partition_near_compact : ∀ (N : ℕ) (C : Set (Rn N)) (P : Set (Rn N) → Prop), IsCompact C → (∀ y ∈ C, ∃ U : Set (Rn N), IsOpen U ∧ y ∈ U ∧ P U) → ∃ (p : ℕ) (ζ : Fin p → Rn N → ℝ) (O : Set (Rn N)), IsOpen O ∧ C ⊆ O ∧ (∀ z ∈ O, ∑ q, ζ q z = 1) ∧ ∀ q, ContDiff ℝ 1 (ζ q) ∧ HasCompactSupport (ζ q) ∧ ∃ U : Set (Rn N), P U ∧ tsupport (ζ q) ⊆ U := by
  intro N C P hC hP
  -- Step 1: radii `ε_y > 0` with `ball y ε_y ⊆ U_y` and `P U_y`.
  have hrad : ∀ y ∈ C, ∃ ε > 0, ∃ U : Set (Rn N), P U ∧ ball y ε ⊆ U := fun y hy ↦ by
    obtain ⟨U, hUo, hyU, hPU⟩ := hP y hy
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hUo y hyU
    exact ⟨ε, hε, U, hPU, hεU⟩
  choose! ε hε U hPU hεU using hrad
  -- Step 2: a finite subcover of `C` by the balls `ball c_q (ε_q / 4)`, `q : Fin p`.
  obtain ⟨p, c, hcC, hCc⟩ : ∃ (p : ℕ) (c : Fin p → Rn N), (∀ q, c q ∈ C) ∧
      C ⊆ ⋃ q, ball (c q) (ε (c q) / 4) := by
    obtain ⟨T, hTC, hCT⟩ := hC.elim_nhds_subcover (fun y ↦ ball y (ε y / 4))
      fun y hy ↦ ball_mem_nhds y (by linarith [hε y hy])
    refine ⟨T.card, fun q ↦ T.equivFin.symm q, fun q ↦ hTC _ (T.equivFin.symm q).2, fun z hz ↦ ?_⟩
    obtain ⟨y, hyT, hzy⟩ := mem_iUnion₂.1 (hCT hz)
    exact mem_iUnion.2 ⟨T.equivFin ⟨y, hyT⟩, by simpa using hzy⟩
  have hεc : ∀ q, 0 < ε (c q) := fun q ↦ hε _ (hcC q)
  -- Step 3: bumps `β_q` at `c_q` with radii `ε_q / 4 < ε_q / 2`.
  let β : ∀ q, ContDiffBump (c q) := fun q ↦
    ⟨ε (c q) / 4, ε (c q) / 2, by linarith [hεc q], by linarith [hεc q]⟩
  -- Step 4: `ζ_q = β_q ∏_{l<q} (1 - β_l)` and `O = ⋃_q ball c_q (ε_q / 4)`.
  refine ⟨p, fun q x ↦ β q x * ∏ l ∈ Finset.univ with l < q, (1 - β l x),
    ⋃ q, ball (c q) (ε (c q) / 4), isOpen_iUnion fun q ↦ isOpen_ball, hCc, fun z hz ↦ ?_,
    fun q ↦ ⟨?_, ?_, U (c q), hPU _ (hcC q), ?_⟩⟩
  -- Steps 6–7: `∑_q ζ_q = 1 - ∏_q (1 - β_q)`, and some `β_q` equals `1` at each point of `O`.
  · obtain ⟨q₀, hzq₀⟩ := mem_iUnion.1 hz
    have h1 : β q₀ z = 1 := (β q₀).one_of_mem_closedBall (ball_subset_closedBall hzq₀)
    have h0 : ∏ q, (1 - β q z) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ q₀) (sub_eq_zero.2 h1.symm)
    have key := Finset.prod_one_sub_ordered Finset.univ fun q ↦ β q z
    rw [h0, eq_comm, sub_eq_zero] at key
    exact key.symm
  -- Step 5: `ζ_q` is `C¹` with compact support, and
  -- `tsupport ζ_q ⊆ closedBall c_q (ε_q / 2) ⊆ ball c_q ε_q ⊆ U_{c_q}`.
  · exact (β q).contDiff.mul (contDiff_prod fun l _ ↦ contDiff_const.sub (β l).contDiff)
  · exact (β q).hasCompactSupport.mul_right
  · calc tsupport (fun x ↦ β q x * ∏ l ∈ Finset.univ with l < q, (1 - β l x))
        ⊆ tsupport (β q) := tsupport_mul_subset_left
      _ = closedBall (c q) (ε (c q) / 2) := (β q).tsupport_eq
      _ ⊆ ball (c q) (ε (c q)) := closedBall_subset_ball (by linarith [hεc q])
      _ ⊆ U (c q) := hεU _ (hcC q)
/-- **Simon Ch. 2, 4.20, 4.27 and 4.30 (pp. 59–61), integrability for the divergence identity.**
Let `M ⊆ ℝᴺ` be measurable, with `y ↦ P_y` and `H` continuous on `M` and `Hⁿ` finite on compact
subsets of `M`, and let `Y` be `C¹` and vanish off a closed set `F` with `M ∩ F` compact. Then
`div_M Y` and `Y · H` are `Hⁿ`-integrable on `M`. As `P_y = ι ∘ π` (`ι` the inclusion of `T_y M`,
`π` the orthogonal projection onto it), cyclicity of the trace gives
`div_M Y(y) = trace(DY(y) ∘ P_y)`, so both functions are continuous on `M`. They vanish off `F`
(`DY = 0` on the open set `Fᶜ`), are bounded on the compact set `M ∩ F`, and `Hⁿ(M ∩ F) < ∞`. -/
theorem Submission.tangentialDivergence_meanCurvature_integrableOn : ∀ (n N : ℕ) (M F : Set (Rn N)) (Y : Rn N → Rn N), MeasurableSet M → ContinuousOn (tangentProjection M) M → ContinuousOn (meanCurvature M) M → (∀ C ⊆ M, IsCompact C → μHE[n] C < ⊤) → ContDiff ℝ 1 Y → IsClosed F → (∀ x ∉ F, Y x = 0) → IsCompact (M ∩ F) → IntegrableOn (tangentialDivergence M Y) M μHE[n] ∧ IntegrableOn (fun y ↦ inner ℝ (Y y) (meanCurvature M y)) M μHE[n] := by
  intro n N M F Y hM hP hH hfin hY hF hYF hMF
  -- Step 5: a function continuous on `M` and vanishing on `M \ F` is integrable on `M`: it is
  -- bounded on the compact set `M ∩ F`, which has finite measure.
  have key : ∀ f : Rn N → ℝ, ContinuousOn f M → (∀ y ∈ M, y ∉ F → f y = 0) →
      IntegrableOn f M μHE[n] := by
    intro f hf hf0
    have hfMF : ContinuousOn f (M ∩ F) := hf.mono inter_subset_left
    have hmeas : MeasurableSet (M ∩ F) := hM.inter hF.measurableSet
    obtain ⟨C, hC⟩ := hMF.exists_bound_of_continuousOn hfMF
    have hint : IntegrableOn f (M ∩ F) μHE[n] :=
      IntegrableOn.of_bound (hfin _ inter_subset_left hMF) (hfMF.aestronglyMeasurable hmeas) C
        ((ae_restrict_iff' hmeas).2 (Eventually.of_forall hC))
    exact hint.of_forall_sdiff_eq_zero hM fun y hy ↦ hf0 y hy.1 fun hyF ↦ hy.2 ⟨hy.1, hyF⟩
  -- Step 4: `DY(y) = 0` off `F`, since `Y` vanishes on the open set `Fᶜ`.
  have hD0 : ∀ y ∉ F, fderiv ℝ Y y = 0 := by
    intro y hy
    have hY0 : Y =ᶠ[𝓝 y] fun _ ↦ 0 :=
      eventually_of_mem (hF.isOpen_compl.mem_nhds hy) fun x hx ↦ hYF x hx
    rw [hY0.fderiv_eq]
    simp
  -- Step 1: `div_M Y(y) = trace(DY(y) ∘ P_y)`, as `P_y = ι ∘ π` and the trace is cyclic.
  have htr : ∀ y, tangentialDivergence M Y y = LinearMap.trace ℝ (Rn N)
      ((fderiv ℝ Y y ∘L tangentProjection M y : Rn N →L[ℝ] Rn N) : Rn N →ₗ[ℝ] Rn N) := by
    intro y
    set T := tangentSpace M y
    have hPT : ((fderiv ℝ Y y ∘L tangentProjection M y : Rn N →L[ℝ] Rn N) : Rn N →ₗ[ℝ] Rn N) =
        ((fderiv ℝ Y y : Rn N →ₗ[ℝ] Rn N) ∘ₗ T.subtype) ∘ₗ
          (T.orthogonalProjectionOnto : Rn N →ₗ[ℝ] T) := rfl
    rw [hPT, LinearMap.trace_comp_comm', LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ T)]
    simp [tangentialDivergence, tangentFrame, T]
  -- Step 2: `div_M Y` is continuous on `M`, the trace being continuous on `ℝᴺ →L[ℝ] ℝᴺ`.
  have hdiv : ContinuousOn (tangentialDivergence M Y) M := by
    have htrc : Continuous fun A : Rn N →L[ℝ] Rn N ↦
        LinearMap.trace ℝ (Rn N) (A : Rn N →ₗ[ℝ] Rn N) :=
      ((LinearMap.trace ℝ (Rn N)).comp
        (ContinuousLinearMap.coeLM ℝ)).continuous_of_finiteDimensional
    exact (htrc.comp_continuousOn
      ((hY.continuous_fderiv one_ne_zero).continuousOn.clm_comp hP)).congr fun y _ ↦ htr y
  -- Steps 3 and 6: `Y · H` is continuous on `M`, and both functions vanish off `F`.
  refine ⟨key _ hdiv fun y _ hy ↦ ?_, key _ (hY.continuous.continuousOn.inner hH) fun y _ hy ↦ ?_⟩
  · simp [tangentialDivergence, hD0 y hy]
  · simp [hYF y hy]
/-- **Simon Ch. 2, partition-of-unity step for 4.22(*) and 4.29–4.30 (pp. 59–61).** With `div_M`
as in 4.20 and `H` as in 4.27: let `Y` and `ζ_q` (`q < p`) be `C¹`, `Y = 0` off the closed set `S`,
and `∑_q ζ_q = 1` on an open `O ⊇ M ∩ S`. Then at every `y ∈ M`,
`div_M Y(y) + Y(y) · H(y) = ∑_q (div_M(ζ_q Y)(y) + ζ_q(y) Y(y) · H(y))`. Near `y`, `Y = ∑_q ζ_q Y`
(on `O` if `y ∈ S`, on `Sᶜ` otherwise), so `DY(y) = ∑_q D(ζ_q Y)(y)`; both terms are linear. -/
theorem Submission.tangentialDivergence_add_inner_eq_sum_partition : ∀ (N p : ℕ) (M S O : Set (Rn N)) (Y : Rn N → Rn N) (ζ : Fin p → Rn N → ℝ), ContDiff ℝ 1 Y → (∀ q, ContDiff ℝ 1 (ζ q)) → IsClosed S → (∀ x ∉ S, Y x = 0) → IsOpen O → M ∩ S ⊆ O → (∀ z ∈ O, ∑ q, ζ q z = 1) → ∀ y ∈ M, tangentialDivergence M Y y + inner ℝ (Y y) (meanCurvature M y) = ∑ q, (tangentialDivergence M (fun z ↦ ζ q z • Y z) y + inner ℝ (ζ q y • Y y) (meanCurvature M y)) := by
  intro N p M S O Y ζ hY hζ hS hYS hO hMSO hsum y hy
  -- Step 1: `Y = ∑_q ζ_q Y` near `y`: on `O` if `y ∈ S`, on `Sᶜ` (where `Y = 0`) otherwise.
  have hloc : Y =ᶠ[𝓝 y] fun z ↦ ∑ q, ζ q z • Y z := by
    by_cases hyS : y ∈ S
    · filter_upwards [hO.mem_nhds (hMSO ⟨hy, hyS⟩)] with z hz
      rw [← Finset.sum_smul, hsum z hz, one_smul]
    · filter_upwards [hS.isOpen_compl.mem_nhds hyS] with z hz
      simp [hYS z hz]
  -- Step 2: `DY(y) = ∑_q D(ζ_q Y)(y)`, each `ζ_q Y` being `C¹`.
  have hD : fderiv ℝ Y y = ∑ q, fderiv ℝ (fun z ↦ ζ q z • Y z) y := by
    rw [hloc.fderiv_eq, fderiv_fun_sum fun q _ ↦
      (((hζ q).fun_smul hY).differentiable one_ne_zero).differentiableAt]
  -- Step 3: the frame sum is linear in `DY(y)`; exchange the two finite sums.
  have hdiv : tangentialDivergence M Y y =
      ∑ q, tangentialDivergence M (fun z ↦ ζ q z • Y z) y := by
    simp only [tangentialDivergence, hD, _root_.sum_apply, inner_sum]
    exact Finset.sum_comm
  -- Step 4: `Y(y) = ∑_q ζ_q(y) Y(y)`, so the mean-curvature term splits the same way.
  have hval : Y y = ∑ q, ζ q y • Y y := hloc.eq_of_nhds
  have hinner : inner ℝ (Y y) (meanCurvature M y) =
      ∑ q, inner ℝ (ζ q y • Y y) (meanCurvature M y) := by
    rw [← sum_inner, ← hval]
  -- Step 5: add the two identities and regroup the sums.
  rw [Finset.sum_add_distrib, hdiv, hinner]
/-- **Simon Ch. 2, §5 (pp. 61–63), the hypothesis `Hⁿ(K ∩ M) < ∞`.** An `n`-dimensional `C^r`
submanifold `M ⊆ ℝᴺ` has locally finite and locally positive `Hⁿ`-measure.
(a) Compact `C ⊆ M`: near `y ∈ C` take a chart `ψ : V → W`; `C' = C ∩ B̄_{ρ/2}(y) ⊆ W` is `ψ(Q)` with
`Q = V ∩ ψ⁻¹(C')` compact (relative properness), and `ψ` is locally Lipschitz on `V`, so
`Hⁿ(C') < ∞`. (b) `y = ψ(x₀) ∈ O`: `V' = V ∩ ψ⁻¹(O ∩ W)` is an open neighbourhood of `x₀` with
`ψ(V') ⊆ M ∩ O`. A linear left inverse `P` of the injective `Dψ(x₀)` makes `P ∘ ψ` open at `x₀`
(inverse function theorem), so `0 < Lⁿ(P(ψ(V'))) ≤ ‖P‖ⁿ Hⁿ(ψ(V'))`. -/
theorem Submission.simon_submanifold_hausdorff_finite_pos : ∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)), Chapter02.IsSimonSubmanifold (E := Rn n) r M → (∀ C ⊆ M, IsCompact C → μHE[n] C < ⊤) ∧ ∀ y ∈ M, ∀ O : Set (Rn N), IsOpen O → y ∈ O → 0 < μHE[n] (M ∩ O) := by
  intro n N r M hM
  have hr : (1 : WithTop ℕ∞) ≤ r := by exact_mod_cast hM.1
  refine ⟨fun C hCM hC => ?_, fun y hyM O hO hyO => ?_⟩
  · -- (a) It suffices that every `y ∈ C` has a relative neighbourhood `C'` of finite measure.
    refine hC.measure_lt_top_of_nhdsWithin fun y hy => ?_
    obtain ⟨V, W, ψ, hyW, hψ⟩ := hM.2 y (hCM hy)
    obtain ⟨ρ, hρ, hρW⟩ := Metric.isOpen_iff.mp hψ.isOpen_target y hyW
    -- `C' = C ∩ B̄_{ρ/2}(y)` is a compact subset of `W`, so `Q = V ∩ ψ⁻¹(C')` is compact.
    have hC'W : C ∩ closedBall y (ρ / 2) ⊆ W := fun z hz =>
      hρW (closedBall_subset_ball (by linarith) hz.2)
    have hQ : IsCompact (V ∩ ψ ⁻¹' (C ∩ closedBall y (ρ / 2))) :=
      hψ.isCompact_source_inter_preimage _ (hC.inter_right isClosed_closedBall) hC'W
    -- `C' ⊆ M ∩ W = ψ(V)`, hence `C' = ψ(Q)`.
    have himg : C ∩ closedBall y (ρ / 2) ⊆ ψ '' (V ∩ ψ ⁻¹' (C ∩ closedBall y (ρ / 2))) := by
      intro z hz
      have hz' : z ∈ W ∩ M := ⟨hC'W hz, hCM hz.1⟩
      rw [← hψ.image_eq] at hz'
      obtain ⟨x, hxV, rfl⟩ := hz'
      exact ⟨x, ⟨hxV, hz⟩, rfl⟩
    refine ⟨C ∩ closedBall y (ρ / 2), inter_mem_nhdsWithin C (closedBall_mem_nhds y (by positivity)),
      (measure_mono himg).trans_lt ?_⟩
    -- `ψ` is locally Lipschitz on `V`, so the compact `Q` is covered by finitely many pieces
    -- with images of finite measure.
    refine hQ.induction_on (p := fun s => μHE[n] (ψ '' s) < ⊤) (by simp) ?_ ?_ ?_
    · intro s t hst ht
      exact (measure_mono (image_mono hst)).trans_lt ht
    · intro s t hs ht
      rw [image_union]
      exact (measure_union_le _ _).trans_lt (ENNReal.add_lt_top.2 ⟨hs, ht⟩)
    · intro x hx
      have hψx : ContDiffAt ℝ 1 ψ x :=
        (hψ.contDiffOn.contDiffAt (hψ.isOpen_source.mem_nhds hx.1)).of_le hr
      obtain ⟨K, t, ht, hK⟩ := hψx.exists_lipschitzOnWith
      refine ⟨t ∩ ball x 1, mem_nhdsWithin_of_mem_nhds (inter_mem ht (ball_mem_nhds x one_pos)), ?_⟩
      calc μHE[n] (ψ '' (t ∩ ball x 1)) ≤ (K : ℝ≥0∞) ^ n * μHE[n] (t ∩ ball x 1) :=
            Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n (hK.mono inter_subset_left)
        _ < ⊤ := by
            refine ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) ?_
            rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
            exact (measure_mono inter_subset_right).trans_lt measure_ball_lt_top
  · -- (b) Write `y = ψ(x₀)`; `V' = V ∩ ψ⁻¹(O ∩ W)` is an open neighbourhood of `x₀`.
    obtain ⟨V, W, ψ, hyW, hψ⟩ := hM.2 y hyM
    have hy : y ∈ ψ '' V := by rw [hψ.image_eq]; exact ⟨hyW, hyM⟩
    obtain ⟨x₀, hx₀V, rfl⟩ := hy
    have hV' : IsOpen (V ∩ ψ ⁻¹' (O ∩ W)) :=
      hψ.contDiffOn.continuousOn.isOpen_inter_preimage hψ.isOpen_source (hO.inter hψ.isOpen_target)
    have hx₀ : x₀ ∈ V ∩ ψ ⁻¹' (O ∩ W) := ⟨hx₀V, hyO, hyW⟩
    have himg : ψ '' (V ∩ ψ ⁻¹' (O ∩ W)) ⊆ M ∩ O := by
      rintro _ ⟨x, ⟨hxV, hxO, -⟩, rfl⟩
      have h : ψ x ∈ W ∩ M := hψ.image_eq ▸ mem_image_of_mem ψ hxV
      exact ⟨h.2, hxO⟩
    refine lt_of_lt_of_le ?_ (measure_mono himg)
    -- `Dψ(x₀)` is injective, so it has a linear left inverse `P : ℝᴺ → ℝⁿ`.
    obtain ⟨g, hg⟩ := (fderiv ℝ ψ x₀).toLinearMap.exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.2 (hψ.injective_fderiv hx₀V))
    set P : Rn N →L[ℝ] Rn n := LinearMap.toContinuousLinearMap g with hP
    have hPL : P.comp (fderiv ℝ ψ x₀) = ((ContinuousLinearEquiv.refl ℝ (Rn n) : Rn n ≃L[ℝ] Rn n) :
        Rn n →L[ℝ] Rn n) := by
      refine ContinuousLinearMap.ext fun v => ?_
      simpa [hP] using LinearMap.congr_fun hg v
    -- `P ∘ ψ` has derivative `id` at `x₀`, so it maps neighbourhoods of `x₀` onto neighbourhoods.
    have hPψ : HasStrictFDerivAt (fun x => P (ψ x))
        ((ContinuousLinearEquiv.refl ℝ (Rn n) : Rn n ≃L[ℝ] Rn n) : Rn n →L[ℝ] Rn n) x₀ := by
      rw [← hPL]
      exact P.hasStrictFDerivAt.comp x₀
        ((hψ.contDiffOn.contDiffAt (hψ.isOpen_source.mem_nhds hx₀V)).hasStrictFDerivAt
          (lt_of_lt_of_le zero_lt_one hr).ne')
    have hnhds : P '' (ψ '' (V ∩ ψ ⁻¹' (O ∩ W))) ∈ 𝓝 (P (ψ x₀)) := by
      rw [image_image, ← hPψ.map_nhds_eq_of_equiv]
      exact image_mem_map (hV'.mem_nhds hx₀)
    -- `0 < Lⁿ(P(ψ(V'))) = Hⁿ(P(ψ(V'))) ≤ ‖P‖ⁿ Hⁿ(ψ(V'))`.
    have hpos : 0 < μHE[n] (P '' (ψ '' (V ∩ ψ ⁻¹' (O ∩ W)))) := by
      rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
      exact Measure.measure_pos_of_mem_nhds _ hnhds
    have hle := Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
      (P.lipschitzWith.lipschitzOnWith (s := ψ '' (V ∩ ψ ⁻¹' (O ∩ W))))
    refine pos_iff_ne_zero.2 fun h0 => hpos.ne' ?_
    rw [h0, mul_zero] at hle
    exact nonpos_iff_eq_zero.mp hle
/-- **Scaled vector fields generate admissible deformations** (Simon Ch. 2, remark after 5.4).
For `U ⊆ ℝᴺ` open and `Y ∈ C²(ℝᴺ, ℝᴺ)` with compact support `tsupport Y ⊆ U`, there is `c > 0`
such that `φ_t(x) = x + c t Y(x)` is an admissible `C²` deformation of `U` fixing the outside of
`tsupport Y`, with initial velocity `c Y`. `Y` is `L`-Lipschitz (`C¹` with compact support) and
`c = 1/(L+1)`; for `|t| < 1` and any `L`-Lipschitz `g`, `x ↦ x + c t g(x)` approximates the identity
with constant `|c t| L < 1`, hence is a bijection of `ℝᴺ` (`ApproximatesLinearOn.injOn`,
`ApproximatesLinearOn.surjective`). Applied to `g = Y` this gives `φ_t` bijective; being the identity
off `K = tsupport Y ⊆ U`, it maps `U` onto `U`. Applied to `g = DY(x)` (of norm `≤ L`) it gives
`Dφ_t(x) = I + c t DY(x)` bijective. -/
theorem Submission.scaled_field_deformation_is_admissible : ∀ (N : ℕ) (U : Set (Rn N)) (Y : Rn N → Rn N), IsOpen U → ContDiff ℝ 2 Y → HasCompactSupport Y → tsupport Y ⊆ U → ∃ c : ℝ, 0 < c ∧ IsAdmissibleDeformation 2 U (tsupport Y) (fun t x ↦ x + (c * t) • Y x) ∧ ∀ x, initialVelocity (fun t x ↦ x + (c * t) • Y x) x = c • Y x := by
  intro N U Y hU hY hYc hYU
  -- `Y` is `C¹` with compact support, hence `L`-Lipschitz for some `L`; put `c = 1/(L+1)`.
  obtain ⟨L, hL⟩ := hY.lipschitzWith_of_hasCompactSupport hYc two_ne_zero
  set c : ℝ := 1 / ((L : ℝ) + 1) with hc_def
  have hc : 0 < c := by positivity
  have hcL : c * L < 1 := by
    rw [hc_def, div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
    linarith
  -- For `|s| < c` and `L`-Lipschitz `g`, `x ↦ x + s • g x` approximates the identity with constant
  -- `‖s‖ L < 1`, hence is a bijection of `ℝᴺ`.
  have key : ∀ s : ℝ, |s| < c → ∀ g : Rn N → Rn N, LipschitzWith L g →
      Function.Bijective (fun x ↦ x + s • g x) := by
    intro s hs g hg
    have hκ : ‖s‖₊ * L < 1 := by
      rw [← NNReal.coe_lt_coe, NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_one]
      calc |s| * L ≤ c * L := mul_le_mul_of_nonneg_right hs.le L.2
        _ < 1 := hcL
    have hA : ApproximatesLinearOn (fun x ↦ x + s • g x)
        ((ContinuousLinearEquiv.refl ℝ (Rn N) : Rn N ≃L[ℝ] Rn N) : Rn N →L[ℝ] Rn N) univ
        (‖s‖₊ * L) := by
      intro x _ y _
      have h1 : x + s • g x - (y + s • g y) -
          ((ContinuousLinearEquiv.refl ℝ (Rn N) : Rn N ≃L[ℝ] Rn N) : Rn N →L[ℝ] Rn N) (x - y) =
          s • (g x - g y) := by
        simp only [ContinuousLinearEquiv.coe_refl, ContinuousLinearMap.id_apply, smul_sub]
        abel
      rw [h1, norm_smul, NNReal.coe_mul, coe_nnnorm, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hg.norm_sub_le x y) (norm_nonneg s)
    have hA' : Subsingleton (Rn N) ∨ ‖s‖₊ * L <
        ‖(((ContinuousLinearEquiv.refl ℝ (Rn N) : Rn N ≃L[ℝ] Rn N).symm : Rn N ≃L[ℝ] Rn N) :
          Rn N →L[ℝ] Rn N)‖₊⁻¹ := by
      rcases subsingleton_or_nontrivial (Rn N) with h | h
      · exact Or.inl h
      · right
        rw [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl,
          ContinuousLinearMap.nnnorm_id, inv_one]
        exact hκ
    exact ⟨injOn_univ.mp (hA.injOn hA'), hA.surjective hA'⟩
  refine ⟨c, hc, ⟨hU, hYc, hYU, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- `(t, x) ↦ x + (c t) • Y x` is `C²` on `ℝ × ℝᴺ`.
    have h2 : ContDiff ℝ 2 (fun p : ℝ × Rn N ↦ p.2 + (c * p.1) • Y p.2) :=
      contDiff_snd.add ((contDiff_const.mul contDiff_fst).smul (hY.comp contDiff_snd))
    exact h2.contDiffOn
  · -- `φ₀ = id`.
    intro x _
    simp
  · -- `φ_t = id` off `tsupport Y`.
    intro t _ x hx
    simp [image_eq_zero_of_notMem_tsupport hx]
  · intro t ht
    have hs : |c * t| < c := by
      have ht' : |t| < 1 := abs_lt.mpr ⟨ht.1, ht.2⟩
      rw [abs_mul, abs_of_pos hc]
      calc c * |t| < c * 1 := mul_lt_mul_of_pos_left ht' hc
        _ = c := mul_one c
    have hbij := key (c * t) hs Y hL
    have hfix : ∀ x, x ∉ tsupport Y → x + (c * t) • Y x = x := fun x hx ↦ by
      simp [image_eq_zero_of_notMem_tsupport hx]
    refine ⟨⟨?_, hbij.1.injOn, ?_⟩, ?_⟩
    · -- `φ_t` maps `U` into `U`: either `φ_t x ∈ tsupport Y ⊆ U`, or `φ_t (φ_t x) = φ_t x`, whence
      -- `φ_t x = x` by injectivity.
      intro x hx
      by_cases h : x + (c * t) • Y x ∈ tsupport Y
      · exact hYU h
      · have hx' : x + (c * t) • Y x = x := hbij.1 (hfix _ h)
        show x + (c * t) • Y x ∈ U
        rw [hx']
        exact hx
    · -- `φ_t` maps `U` onto `U`: a preimage of `z ∈ U` lies in `tsupport Y ⊆ U` or equals `z`.
      intro z hz
      obtain ⟨x, rfl⟩ := hbij.2 z
      by_cases h : x ∈ tsupport Y
      · exact ⟨x, hYU h, rfl⟩
      · refine ⟨x, ?_, rfl⟩
        have hzx := hfix x h
        simp only at hz
        rw [hzx] at hz
        exact hz
    · -- `Dφ_t(x) = I + (c t) DY(x)` is bijective, since `DY(x)` is `L`-Lipschitz.
      intro x _
      have hd : HasFDerivAt (fun y ↦ y + (c * t) • Y y)
          (ContinuousLinearMap.id ℝ (Rn N) + (c * t) • fderiv ℝ Y x) x :=
        (hasFDerivAt_id x).add
          (((hY.differentiable two_ne_zero) x).hasFDerivAt.const_smul (c * t))
      have hDL : LipschitzWith L (fderiv ℝ Y x) :=
        (fderiv ℝ Y x).lipschitzWith.weaken (norm_fderiv_le_of_lipschitz ℝ hL)
      show Function.Bijective (fderiv ℝ (fun y ↦ y + (c * t) • Y y) x)
      rw [hd.fderiv]
      convert key (c * t) hs (fderiv ℝ Y x) hDL using 1
      ext v
      simp
  · -- Initial velocity: `t ↦ x + (c t) • Y x` has derivative `c • Y x`.
    intro x
    have h : HasDerivAt (fun t : ℝ ↦ x + (c * t) • Y x) (c • Y x) 0 := by
      simpa using (((hasDerivAt_id (0 : ℝ)).const_mul c).smul_const (Y x)).const_add x
    exact h.deriv
/-- **Symmetry of the second derivative (Schwarz)**, used for the symmetry `B_y(τ, η) = B_y(η, τ)`
of Simon Ch. 2, 4.26. If `f : ℝⁿ → ℝᴺ` is `C²` at `x`, then `L = D²f(x)` is symmetric. The Mathlib
statement (`ContDiffAt.isSymmSndFDerivAt`) is not imported, so this is the classical mean value
proof: `f` is differentiable near `x` and `Df` has derivative `L` at `x`, so
`‖Df(x + h) - Df(x) - L h‖ ≤ ε‖h‖` for `‖h‖ < δ`. The mean value inequality for
`g(s) = f(x + (t • u + (s * t) • v)) - f(x + (s * t) • v) - s • L (t • u) (t • v)` on `[0, 1]`
bounds the second difference `Δ = f(x + (t • u + t • v)) - f(x + t • v) - (f(x + t • u) - f(x))` by
`‖Δ - t² L u v‖ ≤ 2εt²(‖u‖ + ‖v‖)‖v‖`. Since `Δ` is symmetric in `u, v`, exchanging `a` and `b`
gives `‖L a b - L b a‖ ≤ 2ε(‖a‖ + ‖b‖)²` for every `ε > 0`. -/
theorem Submission.fderiv_fderiv_symm_of_contDiffAt : ∀ (n N : ℕ) (f : Rn n → Rn N) (x : Rn n), ContDiffAt ℝ 2 f x → ∀ a b : Rn n, fderiv ℝ (fderiv ℝ f) x a b = fderiv ℝ (fderiv ℝ f) x b a := by
  intro n N f x hf a b
  set L := fderiv ℝ (fderiv ℝ f) x
  -- Step 1: `f` is differentiable near `x`, and `Df` has derivative `L` at `x`.
  have hdiff : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y := by
    filter_upwards [hf.eventually (by simp)] with y hy
    exact hy.differentiableAt two_ne_zero
  have hDf : HasFDerivAt (fderiv ℝ f) L x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  -- Step 2: uniform first-order expansion of `Df` at `x`.
  have hexp : ∀ ε > 0, ∃ δ > 0, ∀ h : Rn n, ‖h‖ < δ → DifferentiableAt ℝ f (x + h) ∧
      ‖fderiv ℝ f (x + h) - fderiv ℝ f x - L h‖ ≤ ε * ‖h‖ := by
    intro ε hε
    have h1 := Asymptotics.isLittleO_iff.1 (hasFDerivAt_iff_isLittleO_nhds_zero.1 hDf) hε
    have h2 : ∀ᶠ h in 𝓝 (0 : Rn n), DifferentiableAt ℝ f (x + h) :=
      ((continuous_const.add continuous_id).tendsto' (0 : Rn n) x (by simp)).eventually hdiff
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (h2.and h1)
    exact ⟨δ, hδ, fun h hh ↦ hball (by simpa [dist_eq_norm] using hh)⟩
  -- Steps 3–5: the mean value inequality bounds the second difference.
  have hsec : ∀ ε > 0, ∀ δ > 0, (∀ h : Rn n, ‖h‖ < δ → DifferentiableAt ℝ f (x + h) ∧
      ‖fderiv ℝ f (x + h) - fderiv ℝ f x - L h‖ ≤ ε * ‖h‖) →
      ∀ u v : Rn n, ∀ t : ℝ, 0 < t → t * (‖u‖ + ‖v‖) < δ →
      ‖f (x + (t • u + t • v)) - f (x + t • v) - (f (x + t • u) - f x) - t ^ 2 • L u v‖ ≤
        2 * ε * t ^ 2 * (‖u‖ + ‖v‖) * ‖v‖ := by
    intro ε hε δ hδ hball u v t ht htδ
    have hnorm1 : ∀ s ∈ Icc (0 : ℝ) 1, ‖t • u + (s * t) • v‖ ≤ t * (‖u‖ + ‖v‖) := by
      intro s hs
      calc ‖t • u + (s * t) • v‖ ≤ ‖t • u‖ + ‖(s * t) • v‖ := norm_add_le _ _
        _ = t * ‖u‖ + s * t * ‖v‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ht.le,
            Real.norm_of_nonneg (mul_nonneg hs.1 ht.le)]
        _ ≤ t * (‖u‖ + ‖v‖) := by
          nlinarith [mul_nonneg (sub_nonneg.2 hs.2) (mul_nonneg ht.le (norm_nonneg v))]
    have hnorm2 : ∀ s ∈ Icc (0 : ℝ) 1, ‖(s * t) • v‖ ≤ t * (‖u‖ + ‖v‖) := by
      intro s hs
      rw [norm_smul, Real.norm_of_nonneg (mul_nonneg hs.1 ht.le)]
      nlinarith [mul_nonneg (sub_nonneg.2 hs.2) (mul_nonneg ht.le (norm_nonneg v)), norm_nonneg u]
    have hderiv : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt
        (fun s : ℝ ↦ f (x + (t • u + (s * t) • v)) - f (x + (s * t) • v) - s • L (t • u) (t • v))
        (fderiv ℝ f (x + (t • u + (s * t) • v)) (t • v) - fderiv ℝ f (x + (s * t) • v) (t • v) -
          L (t • u) (t • v)) (Icc 0 1) s := by
      intro s hs
      have hd1 : DifferentiableAt ℝ f (x + (t • u + (s * t) • v)) :=
        (hball _ ((hnorm1 s hs).trans_lt htδ)).1
      have hd2 : DifferentiableAt ℝ f (x + (s * t) • v) := (hball _ ((hnorm2 s hs).trans_lt htδ)).1
      have hc2 : HasDerivAt (fun s : ℝ ↦ x + (s * t) • v) (t • v) s := by
        simpa using ((hasDerivAt_mul_const t).smul_const v).const_add x
      have hc1 : HasDerivAt (fun s : ℝ ↦ x + (t • u + (s * t) • v)) (t • v) s := by
        simpa [add_assoc] using hc2.const_add (t • u)
      have hlin : HasDerivAt (fun s : ℝ ↦ s • L (t • u) (t • v)) (L (t • u) (t • v)) s := by
        simpa using (hasDerivAt_id s).smul_const (L (t • u) (t • v))
      exact (((hd1.hasFDerivAt.comp_hasDerivAt s hc1).sub
        (hd2.hasFDerivAt.comp_hasDerivAt s hc2)).sub hlin).hasDerivWithinAt
    have hbound : ∀ s ∈ Ico (0 : ℝ) 1,
        ‖fderiv ℝ f (x + (t • u + (s * t) • v)) (t • v) - fderiv ℝ f (x + (s * t) • v) (t • v) -
          L (t • u) (t • v)‖ ≤ 2 * ε * t ^ 2 * (‖u‖ + ‖v‖) * ‖v‖ := by
      intro s hs
      have hs' : s ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self hs
      have hR₁ := (hball _ ((hnorm1 s hs').trans_lt htδ)).2
      have hR₂ := (hball _ ((hnorm2 s hs').trans_lt htδ)).2
      have hgR : fderiv ℝ f (x + (t • u + (s * t) • v)) (t • v) -
          fderiv ℝ f (x + (s * t) • v) (t • v) - L (t • u) (t • v) =
          (fderiv ℝ f (x + (t • u + (s * t) • v)) - fderiv ℝ f x - L (t • u + (s * t) • v))
            (t • v) -
          (fderiv ℝ f (x + (s * t) • v) - fderiv ℝ f x - L ((s * t) • v)) (t • v) := by
        simp only [sub_apply, map_add, add_apply]
        abel
      have htv : ‖t • v‖ = t * ‖v‖ := by rw [norm_smul, Real.norm_of_nonneg ht.le]
      rw [hgR]
      calc _ ≤ ‖(fderiv ℝ f (x + (t • u + (s * t) • v)) - fderiv ℝ f x - L (t • u + (s * t) • v))
              (t • v)‖ +
            ‖(fderiv ℝ f (x + (s * t) • v) - fderiv ℝ f x - L ((s * t) • v)) (t • v)‖ :=
            norm_sub_le _ _
        _ ≤ ‖fderiv ℝ f (x + (t • u + (s * t) • v)) - fderiv ℝ f x - L (t • u + (s * t) • v)‖ *
              ‖t • v‖ + ‖fderiv ℝ f (x + (s * t) • v) - fderiv ℝ f x - L ((s * t) • v)‖ * ‖t • v‖ :=
            add_le_add (ContinuousLinearMap.le_opNorm _ _) (ContinuousLinearMap.le_opNorm _ _)
        _ ≤ ε * (t * (‖u‖ + ‖v‖)) * (t * ‖v‖) + ε * (t * (‖u‖ + ‖v‖)) * (t * ‖v‖) := by
            rw [htv]
            gcongr
            · exact hR₁.trans (mul_le_mul_of_nonneg_left (hnorm1 s hs') hε.le)
            · exact hR₂.trans (mul_le_mul_of_nonneg_left (hnorm2 s hs') hε.le)
        _ = 2 * ε * t ^ 2 * (‖u‖ + ‖v‖) * ‖v‖ := by ring
    have hmvt := norm_image_sub_le_of_norm_deriv_le_segment_01' hderiv hbound
    have hg : f (x + (t • u + (1 * t) • v)) - f (x + (1 * t) • v) - (1 : ℝ) • L (t • u) (t • v) -
        (f (x + (t • u + (0 * t) • v)) - f (x + (0 * t) • v) - (0 : ℝ) • L (t • u) (t • v)) =
        f (x + (t • u + t • v)) - f (x + t • v) - (f (x + t • u) - f x) - t ^ 2 • L u v := by
      simp only [one_mul, zero_mul, zero_smul, add_zero, sub_zero, map_smul, smul_apply, smul_smul,
        sq]
      abel
    rw [← hg]
    exact hmvt
  -- Steps 6–7: exchange `a` and `b`, divide by `t²` and let `ε → 0`.
  have hsymm : ∀ ε > 0, ‖L a b - L b a‖ ≤ 2 * ε * (‖a‖ + ‖b‖) ^ 2 := by
    intro ε hε
    obtain ⟨δ, hδ, hball⟩ := hexp ε hε
    have hpos : 0 < 2 * (‖a‖ + ‖b‖ + 1) := by positivity
    set t : ℝ := δ / (2 * (‖a‖ + ‖b‖ + 1)) with ht_def
    have ht : 0 < t := div_pos hδ hpos
    have htδ : t * (‖a‖ + ‖b‖) < δ := by
      rw [ht_def, div_mul_eq_mul_div, div_lt_iff₀ hpos]
      nlinarith [norm_nonneg a, norm_nonneg b]
    have htδ' : t * (‖b‖ + ‖a‖) < δ := by rwa [add_comm ‖b‖]
    have h1 := hsec ε hε δ hδ hball a b t ht htδ
    have h2 := hsec ε hε δ hδ hball b a t ht htδ'
    have hΔ : f (x + (t • b + t • a)) - f (x + t • a) - (f (x + t • b) - f x) =
        f (x + (t • a + t • b)) - f (x + t • b) - (f (x + t • a) - f x) := by
      rw [add_comm (t • b) (t • a)]
      abel
    rw [hΔ] at h2
    have hkey : t ^ 2 • (L a b - L b a) =
        (f (x + (t • a + t • b)) - f (x + t • b) - (f (x + t • a) - f x) - t ^ 2 • L b a) -
        (f (x + (t • a + t • b)) - f (x + t • b) - (f (x + t • a) - f x) - t ^ 2 • L a b) := by
      rw [smul_sub]
      abel
    have ht2 : 0 < t ^ 2 := by positivity
    have hmul : t ^ 2 * ‖L a b - L b a‖ ≤ t ^ 2 * (2 * ε * (‖a‖ + ‖b‖) ^ 2) := by
      calc t ^ 2 * ‖L a b - L b a‖ = ‖t ^ 2 • (L a b - L b a)‖ := by
            rw [norm_smul, Real.norm_of_nonneg ht2.le]
        _ ≤ 2 * ε * t ^ 2 * (‖b‖ + ‖a‖) * ‖a‖ + 2 * ε * t ^ 2 * (‖a‖ + ‖b‖) * ‖b‖ := by
            rw [hkey]
            exact (norm_sub_le _ _).trans (add_le_add h2 h1)
        _ = t ^ 2 * (2 * ε * (‖a‖ + ‖b‖) ^ 2) := by ring
    exact le_of_mul_le_mul_left hmul ht2
  -- Conclusion: the bound holds for every `ε > 0`.
  apply eq_of_forall_dist_le
  intro ε hε
  have hD : 0 < 2 * (‖a‖ + ‖b‖) ^ 2 + 1 := by positivity
  rw [dist_eq_norm]
  calc ‖L a b - L b a‖ ≤ 2 * (ε / (2 * (‖a‖ + ‖b‖) ^ 2 + 1)) * (‖a‖ + ‖b‖) ^ 2 :=
        hsymm _ (div_pos hε hD)
    _ = ε * (2 * (‖a‖ + ‖b‖) ^ 2 / (2 * (‖a‖ + ‖b‖) ^ 2 + 1)) := by ring
    _ ≤ ε * 1 := by
        gcongr
        rw [div_le_one hD]
        linarith
    _ = ε := mul_one ε
/-- **Invertibility of the Gram operator.** For an injective continuous linear map
`A : ℝⁿ → ℝᴺ`, the Gram operator `G = A* ∘ A` is a unit of the ring `ℝⁿ →L[ℝ] ℝⁿ`, whose
multiplication is composition. If `G w = 0` then `⟪A w, A w⟫ = ⟪w, A* (A w)⟫ = ⟪w, G w⟫ = 0`, so
`A w = 0` and `w = 0` by injectivity of `A`; thus `G` is an injective endomorphism of the
finite-dimensional `ℝⁿ`, i.e. a linear automorphism (`LinearEquiv.ofInjectiveEndo`), which is
continuous with continuous inverse (`LinearEquiv.toContinuousLinearEquiv`), and its unit
(`ContinuousLinearEquiv.toUnit`) has underlying map `G`. -/
theorem Submission.gram_operator_isUnit_of_injective : ∀ (n N : ℕ) (A : Rn n →L[ℝ] Rn N), Function.Injective A → IsUnit (ContinuousLinearMap.adjoint A ∘L A) := by
  intro n N A hA
  -- Step 1: `G` has trivial kernel, since `⟪A w, A w⟫ = ⟪w, A* (A w)⟫ = ⟪w, G w⟫`.
  have hker : ∀ w : Rn n, (ContinuousLinearMap.adjoint A ∘L A) w = 0 → w = 0 := by
    intro w hw
    have h : inner ℝ (A w) (A w) = 0 := by
      rw [← ContinuousLinearMap.adjoint_inner_right]
      exact (congrArg (inner ℝ w) hw).trans (inner_zero_right w)
    exact hA ((inner_self_eq_zero.mp h).trans (map_zero A).symm)
  -- Step 2: `G` is injective, by linearity.
  have hinj : Function.Injective (ContinuousLinearMap.adjoint A ∘L A) := fun u v huv ↦
    sub_eq_zero.mp (hker _ (by rw [map_sub, huv, sub_self]))
  -- Step 3: an injective endomorphism of the finite-dimensional `ℝⁿ` is a continuous linear
  -- automorphism `e`, with `e v = G v` by construction.
  let e : Rn n ≃L[ℝ] Rn n :=
    (LinearEquiv.ofInjectiveEndo (ContinuousLinearMap.adjoint A ∘L A : Rn n →ₗ[ℝ] Rn n)
      hinj).toContinuousLinearEquiv
  -- Step 4: the unit `e.toUnit` of `ℝⁿ →L[ℝ] ℝⁿ` has underlying map `G`.
  exact ⟨e.toUnit, ContinuousLinearMap.ext fun v ↦ rfl⟩

/-- **Simon Ch. 2, 4.26 (p. 60): `B_y` is a symmetric bilinear form with values in `(T_y M)^⊥`.**
Let `M` be an `n`-dimensional `C²` submanifold of `ℝᴺ`. Assume, for every `C²` local representation
`(V, W, ψ)` of `M` and `x ∈ V`, (R) `T_{ψ(x)} M = range Dψ(x)` and (C) the chart formula
`B_{ψ(x)}(Dψ(x)a, Dψ(x)b) = (D²ψ(x)[a, b])^⊥`. Then `B_y(τ, η) = B_y(η, τ)` and `B_y(τ, η) · v = 0`
for `y ∈ M` and `τ, η, v ∈ T_y M`. Take a chart with `y = ψ(x)`; by (R), `τ = Dψ(x)a` and
`η = Dψ(x)b`, so by (C) `B_y(τ, η)` and `B_y(η, τ)` are the normal parts of `D²ψ(x)[a, b]` and
`D²ψ(x)[b, a]`, which agree because `ψ` is `C²` at `x`
(`Submission.fderiv_fderiv_symm_of_contDiffAt`). A normal part `w - P_y w` is orthogonal to `T_y M`. -/
theorem Submission.second_fundamental_form_symm_normal_of_chart_formula : ∀ (n N : ℕ) (M : Set (Rn N)), Chapter02.IsSimonSubmanifold (E := Rn n) 2 M → (∀ (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N), Chapter02.IsSimonLocalRepresentation 2 M V W ψ → ∀ x ∈ V, tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap) → (∀ (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N), Chapter02.IsSimonLocalRepresentation 2 M V W ψ → ∀ x ∈ V, ∀ a b : Rn n, secondFundamentalForm M (ψ x) (fderiv ℝ ψ x a) (fderiv ℝ ψ x b) = normalPart M (ψ x) (fderiv ℝ (fderiv ℝ ψ) x a b)) → ∀ y ∈ M, ∀ τ ∈ tangentSpace M y, ∀ η ∈ tangentSpace M y, secondFundamentalForm M y τ η = secondFundamentalForm M y η τ ∧ ∀ v ∈ tangentSpace M y, inner ℝ (secondFundamentalForm M y τ η) v = 0 := by
  intro n N M hM hR hC y hy τ hτ η hη
  -- Step 1: a `C²` chart `(V, W, ψ)` of `M` with `y ∈ W`, and `x ∈ V` with `ψ x = y`.
  obtain ⟨V, W, ψ, hyW, hψ⟩ := hM.exists_localRepresentation hy
  obtain ⟨x, hx, rfl⟩ : y ∈ ψ '' V := by
    rw [hψ.image_eq]
    exact ⟨hyW, hy⟩
  -- Step 2: by (R), `τ = Dψ(x) a` and `η = Dψ(x) b`.
  rw [hR V W ψ hψ x hx] at hτ hη
  obtain ⟨a, rfl⟩ := hτ
  obtain ⟨b, rfl⟩ := hη
  simp only [ContinuousLinearMap.coe_coe]
  -- Step 3: `ψ` is `C²` at `x`, so `D²ψ(x)[a, b] = D²ψ(x)[b, a]`.
  have hψ2 : ContDiffAt ℝ 2 ψ x := hψ.contDiffOn.contDiffAt (hψ.isOpen_source.mem_nhds hx)
  have hS : fderiv ℝ (fderiv ℝ ψ) x a b = fderiv ℝ (fderiv ℝ ψ) x b a :=
    Submission.fderiv_fderiv_symm_of_contDiffAt n N ψ x hψ2 a b
  -- Step 4: by (C), `B_y(τ, η) = (D²ψ(x)[a, b])^⊥ = (D²ψ(x)[b, a])^⊥ = B_y(η, τ)`.
  rw [hC V W ψ hψ x hx a b, hC V W ψ hψ x hx b a, hS]
  -- Step 5: the normal part `w - P_y w` of `w = D²ψ(x)[b, a]` lies in `(T_y M)^⊥`.
  exact ⟨rfl, fun v hv ↦ Submodule.inner_left_of_mem_orthogonal hv
    (Submodule.sub_starProjection_mem_orthogonal _)⟩
/-- **Derivative of a field normal along `M`** (Simon 5.11 proof: `τᵢ · D_{τⱼ}X = -X · B(τᵢ, τⱼ)`
"by virtue of 4.24 and the fact that `X` is normal to `M`"). Let `M` be an `n`-dimensional `C²`
submanifold such that, on every class-2 chart `ψ`, (R) `T_{ψ(x)}M = range Dψ(x)` and
(C) `B_{ψ(x)}(Dψ(x)a, Dψ(x)b) = (D²ψ(x)[a, b])^⊥`. If `Y` is differentiable at `y ∈ M` and normal
along `M`, then `η · DY(y)τ = -Y(y) · B_y(τ, η)` for all `τ, η ∈ T_y M`. In a chart with `ψ(x) = y`,
`τ = Dψ(x)a` and `η = Dψ(x)b`, the function `x' ↦ Y(ψ(x')) · Dψ(x')b` vanishes on the open set
`V`, so its derivative at `x` in direction `a`, `Y(y) · D²ψ(x)[a, b] + DY(y)τ · η`, is `0`; and
`Y(y) · D²ψ(x)[a, b] = Y(y) · (D²ψ(x)[a, b])^⊥ = Y(y) · B_y(τ, η)` as `Y(y) ⊥ T_y M`. -/
theorem Submission.inner_fderiv_normal_field_eq_neg_second_fundamental_form : ∀ (n N : ℕ) (M : Set (Rn N)), Chapter02.IsSimonSubmanifold (E := Rn n) 2 M → (∀ (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N), Chapter02.IsSimonLocalRepresentation 2 M V W ψ → ∀ x ∈ V, tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap) → (∀ (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N), Chapter02.IsSimonLocalRepresentation 2 M V W ψ → ∀ x ∈ V, ∀ a b : Rn n, secondFundamentalForm M (ψ x) (fderiv ℝ ψ x a) (fderiv ℝ ψ x b) = normalPart M (ψ x) (fderiv ℝ (fderiv ℝ ψ) x a b)) → ∀ (Y : Rn N → Rn N) (y : Rn N), y ∈ M → DifferentiableAt ℝ Y y → (∀ z ∈ M, ∀ v ∈ tangentSpace M z, inner ℝ (Y z) v = 0) → ∀ τ ∈ tangentSpace M y, ∀ η ∈ tangentSpace M y, inner ℝ η (fderiv ℝ Y y τ) = -inner ℝ (Y y) (secondFundamentalForm M y τ η) := by
  intro n N M hM hR hC Y y hy hY hnorm τ hτ η hη
  -- Step 1: a class-2 chart `(V, W, ψ)` and `x ∈ V` with `ψ x = y`; by (R), `τ = Dψ(x) a` and
  -- `η = Dψ(x) b`.
  obtain ⟨V, W, ψ, hyW, hrep⟩ := hM.2 y hy
  obtain ⟨x, hxV, rfl⟩ : y ∈ ψ '' V := hrep.image_eq ▸ ⟨hyW, hy⟩
  rw [hR V W ψ hrep x hxV] at hτ hη
  obtain ⟨a, rfl⟩ := hτ
  obtain ⟨b, rfl⟩ := hη
  simp only [ContinuousLinearMap.coe_coe]
  -- Step 2: `ψ` and `Dψ` are differentiable at `x`; derivatives of `x' ↦ Dψ(x') b` and `Y ∘ ψ`.
  have hV : IsOpen V := hrep.isOpen_source
  have hψ2 : ContDiffAt ℝ 2 ψ x := hrep.contDiffOn.contDiffAt (hV.mem_nhds hxV)
  have hψ : HasFDerivAt ψ (fderiv ℝ ψ x) x := (hψ2.differentiableAt (by norm_num)).hasFDerivAt
  have hDψ : HasFDerivAt (fderiv ℝ ψ) (fderiv ℝ (fderiv ℝ ψ) x) x :=
    ((hψ2.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  have hg := hDψ.clm_apply (hasFDerivAt_const b x)
  have hYψ := hY.hasFDerivAt.comp x hψ
  -- Step 3: `f x' = ⟪Y (ψ x'), Dψ(x') b⟫` vanishes on the open set `V`, so `Df(x) = 0`.
  have hf0 : HasFDerivAt (fun x' => inner ℝ ((Y ∘ ψ) x') (fderiv ℝ ψ x' b))
      (0 : Rn n →L[ℝ] ℝ) x := by
    refine (hasFDerivAt_const (0 : ℝ) x).congr_of_eventuallyEq ?_
    filter_upwards [hV.mem_nhds hxV] with x' hx'
    have hmem : ψ x' ∈ M := (hrep.image_eq ▸ mem_image_of_mem ψ hx').2
    exact hnorm _ hmem _ (by rw [hR V W ψ hrep x' hx']; exact ⟨b, rfl⟩)
  -- Step 4: product rule and uniqueness of the derivative, evaluated at `a`.
  have h4 : inner ℝ (Y (ψ x)) (fderiv ℝ (fderiv ℝ ψ) x a b) +
      inner ℝ (fderiv ℝ Y (ψ x) (fderiv ℝ ψ x a)) (fderiv ℝ ψ x b) = 0 := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      fderivInnerCLM_apply, Function.comp_apply, ContinuousLinearMap.comp_zero, zero_add,
      ContinuousLinearMap.flip_apply, zero_apply] using
      DFunLike.congr_fun ((hYψ.inner ℝ hg).unique hf0) a
  -- Step 5: `Y (ψ x)` is normal, so it only sees the normal part of `D²ψ(x)[a, b]`, which is
  -- `B(τ, η)` by (C).
  have h5 : inner ℝ (Y (ψ x)) (tangentProjection M (ψ x) (fderiv ℝ (fderiv ℝ ψ) x a b)) = 0 :=
    hnorm _ hy _ (Submodule.starProjection_apply_mem _ _)
  rw [hC V W ψ hrep x hxV a b, normalPart, inner_sub_right, h5, sub_zero]
  -- Step 6: symmetry of the real inner product.
  have h6 := real_inner_comm (fderiv ℝ ψ x b) (fderiv ℝ Y (ψ x) (fderiv ℝ ψ x a))
  linarith
/-- **Mean curvature through the Gram operator of a chart** (Simon Ch. 2, 4.27, at one point). Let
`A : ℝⁿ → ℝᴺ` be injective with `T_y M = range A` and `S` bilinear with `B_y(A a, A b) = S(a, b)^⊥`.
With `G = A* ∘ A`, a unit by `Submission.gram_operator_isUnit_of_injective`, and `(eₖ)` the
standard basis of `ℝⁿ`, `H(y) = (∑ₖ,ₗ ⟨eₖ, G⁻¹ eₗ⟩ S(eₖ, eₗ))^⊥`. Choose `aᵢ` with `A aᵢ = τᵢ`;
then `H(y) = (∑ᵢ S(aᵢ, aᵢ))^⊥`, since `v ↦ v^⊥ = (I - P) v` is linear. The adjoint identity gives
`⟨eₖ, aᵢ⟩ = ⟨A G⁻¹ eₖ, τᵢ⟩`, so Parseval in `T_y M` gives
`∑ᵢ ⟨eₖ, aᵢ⟩⟨eₗ, aᵢ⟩ = ⟨A G⁻¹ eₖ, A G⁻¹ eₗ⟩ = ⟨eₖ, G⁻¹ eₗ⟩`; expanding each `aᵢ` in the standard
basis and using the bilinearity of `S` finishes the proof. -/
theorem Submission.mean_curvature_eq_normalPart_gram_trace : ∀ (n N : ℕ) (M : Set (Rn N)) (y : Rn N) (A : Rn n →L[ℝ] Rn N) (S : Rn n →L[ℝ] Rn n →L[ℝ] Rn N), Function.Injective A → tangentSpace M y = LinearMap.range A.toLinearMap → (∀ a b : Rn n, secondFundamentalForm M y (A a) (A b) = normalPart M y (S a b)) → meanCurvature M y = normalPart M y (∑ k : Fin n, ∑ l : Fin n, inner ℝ (EuclideanSpace.single k (1 : ℝ)) (Ring.inverse (ContinuousLinearMap.adjoint A ∘L A) (EuclideanSpace.single l (1 : ℝ))) • S (EuclideanSpace.single k (1 : ℝ)) (EuclideanSpace.single l (1 : ℝ))) := by
  intro n N M y A S hA hT hB
  set G : Rn n →L[ℝ] Rn n := ContinuousLinearMap.adjoint A ∘L A
  -- Step 1: `G` is a unit of `ℝⁿ →L[ℝ] ℝⁿ`, whose multiplication is composition, so
  -- `G (G⁻¹ v) = v`; by the adjoint identity, `⟨G u, w⟩ = ⟨A u, A w⟩`.
  have hGGi : ∀ v : Rn n, G (Ring.inverse G v) = v := fun v ↦ by
    rw [← mul_apply_eq_comp,
      Ring.mul_inverse_cancel _ (Submission.gram_operator_isUnit_of_injective n N A hA),
      one_apply_eq_self]
  have hGinner : ∀ u w : Rn n, inner ℝ (G u) w = inner ℝ (A u) (A w) := fun u w ↦
    ContinuousLinearMap.adjoint_inner_left A w (A u)
  -- Step 2: preimages `aᵢ` of the frame vectors `τᵢ ∈ T_y M = range A`.
  have hτ : ∀ i, ∃ a : Rn n, A a = tangentFrame M y i := fun i ↦ by
    have hi : tangentFrame M y i ∈ tangentSpace M y :=
      ((stdOrthonormalBasis ℝ (tangentSpace M y)) i).2
    rw [hT] at hi
    exact LinearMap.mem_range.mp hi
  choose a ha using hτ
  -- Step 3: `H(y) = ∑ᵢ B(A aᵢ, A aᵢ) = (∑ᵢ S(aᵢ, aᵢ))^⊥`, as `w ↦ w^⊥` is the linear map `I - P`.
  have hnp : ∀ v, normalPart M y v =
      (ContinuousLinearMap.id ℝ (Rn N) - tangentProjection M y) v := fun v ↦ rfl
  have hH : meanCurvature M y = normalPart M y (∑ i, S (a i) (a i)) := by
    rw [hnp, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← ha i, hB, hnp]
  rw [hH]
  congr 1
  -- Step 4: `⟨eₖ, aᵢ⟩ = ⟨G (G⁻¹ eₖ), aᵢ⟩ = ⟨A G⁻¹ eₖ, τᵢ⟩`.
  have hcoord : ∀ k i, inner ℝ (EuclideanSpace.single k (1 : ℝ)) (a i) =
      inner ℝ (A (Ring.inverse G (EuclideanSpace.single k (1 : ℝ)))) (tangentFrame M y i) := by
    intro k i
    rw [← ha i, ← hGinner, hGGi]
  -- Step 5: Parseval in `T_y M` for `uₖ = A G⁻¹ eₖ ∈ T_y M`:
  -- `∑ᵢ ⟨eₖ, aᵢ⟩⟨eₗ, aᵢ⟩ = ⟨uₖ, uₗ⟩ = ⟨G G⁻¹ eₖ, G⁻¹ eₗ⟩ = ⟨eₖ, G⁻¹ eₗ⟩`.
  have hmem : ∀ v, A v ∈ tangentSpace M y := fun v ↦ by
    rw [hT]
    exact LinearMap.mem_range_self _ v
  have hgram : ∀ k l, ∑ i, inner ℝ (EuclideanSpace.single k (1 : ℝ)) (a i) *
      inner ℝ (EuclideanSpace.single l (1 : ℝ)) (a i) =
      inner ℝ (EuclideanSpace.single k (1 : ℝ))
        (Ring.inverse G (EuclideanSpace.single l (1 : ℝ))) := by
    intro k l
    have hP := (stdOrthonormalBasis ℝ (tangentSpace M y)).sum_inner_mul_inner
      ⟨_, hmem (Ring.inverse G (EuclideanSpace.single k (1 : ℝ)))⟩
      ⟨_, hmem (Ring.inverse G (EuclideanSpace.single l (1 : ℝ)))⟩
    simp only [Submodule.coe_inner] at hP
    rw [← hGGi (EuclideanSpace.single k (1 : ℝ)), hGinner, ← hP]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hGGi, hcoord k i, hcoord l i,
      real_inner_comm (tangentFrame M y i) (A (Ring.inverse G (EuclideanSpace.single l (1 : ℝ))))]
    rfl
  -- Step 6: `v = ∑ₖ ⟨eₖ, v⟩ eₖ`, so by bilinearity `S(v, v) = ∑ₖ,ₗ ⟨eₖ, v⟩⟨eₗ, v⟩ S(eₖ, eₗ)`.
  have hexp : ∀ v : Rn n, S v v = ∑ k : Fin n, ∑ l : Fin n,
      (inner ℝ (EuclideanSpace.single k (1 : ℝ)) v *
        inner ℝ (EuclideanSpace.single l (1 : ℝ)) v) •
        S (EuclideanSpace.single k (1 : ℝ)) (EuclideanSpace.single l (1 : ℝ)) := by
    intro v
    have hv : ∑ k : Fin n, inner ℝ (EuclideanSpace.single k (1 : ℝ)) v •
        EuclideanSpace.single k (1 : ℝ) = v := by
      simpa only [EuclideanSpace.basisFun_apply] using
        (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr' v
    conv_lhs => rw [← hv]
    simp only [map_sum, map_smul, sum_apply, smul_apply, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ by rw [mul_comm]
  -- Summing over `i` and exchanging the finite sums, the coefficients are those of step 5.
  calc ∑ i, S (a i) (a i)
      = ∑ i, ∑ k : Fin n, ∑ l : Fin n, (inner ℝ (EuclideanSpace.single k (1 : ℝ)) (a i) *
          inner ℝ (EuclideanSpace.single l (1 : ℝ)) (a i)) •
            S (EuclideanSpace.single k (1 : ℝ)) (EuclideanSpace.single l (1 : ℝ)) :=
        Finset.sum_congr rfl fun i _ ↦ hexp (a i)
    _ = ∑ k : Fin n, ∑ l : Fin n, (∑ i, inner ℝ (EuclideanSpace.single k (1 : ℝ)) (a i) *
          inner ℝ (EuclideanSpace.single l (1 : ℝ)) (a i)) •
            S (EuclideanSpace.single k (1 : ℝ)) (EuclideanSpace.single l (1 : ℝ)) := by
        simp only [Finset.sum_smul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_comm
    _ = _ := by simp only [hgram]

/-- **Simon Ch. 2, 4.27 (p. 60): the mean curvature is continuous in a `C²` chart.** Let
`ψ : V → W` be a `C²` local representation of `M ⊆ ℝᴺ` with `T_{ψ(x)} M = range Dψ(x)` and
`B_{ψ(x)}(Dψ(x)a, Dψ(x)b) = (D²ψ(x)[a, b])^⊥`, and let `y ↦ P_y` be continuous on `M`. By the
Gram trace formula, `H(ψ(x)) = w(x) - P_{ψ(x)} w(x)` on `V`, where `G(x) = Dψ(x)* ∘ Dψ(x)` and
`w(x) = ∑ₖ ∑ₗ ⟪eₖ, G(x)⁻¹ eₗ⟫ D²ψ(x)[eₖ, eₗ]`. Here `Dψ` and `D²ψ` are continuous on the open `V`,
`G` is continuous and unit-valued, `Ring.inverse` is continuous at units, and `x ↦ P_{ψ(x)}` is
continuous because `ψ` maps `V` into `M`. -/
theorem Submission.mean_curvature_comp_chart_continuousOn : ∀ (n N : ℕ) (M : Set (Rn N)) (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N), Chapter02.IsSimonLocalRepresentation 2 M V W ψ → ContinuousOn (tangentProjection M) M → (∀ x ∈ V, tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap) → (∀ x ∈ V, ∀ a b : Rn n, secondFundamentalForm M (ψ x) (fderiv ℝ ψ x a) (fderiv ℝ ψ x b) = normalPart M (ψ x) (fderiv ℝ (fderiv ℝ ψ) x a b)) → ContinuousOn (fun x ↦ meanCurvature M (ψ x)) V := by
  intro n N M V W ψ hψ hP htan hsff
  have hV : IsOpen V := hψ.isOpen_source
  -- Step 1: `Dψ` and `D²ψ` are continuous on the open set `V`, as `ψ` is `C²` there.
  have hA : ContinuousOn (fderiv ℝ ψ) V :=
    hψ.contDiffOn.continuousOn_fderiv_of_isOpen hV (by norm_num)
  have hS : ContinuousOn (fderiv ℝ (fderiv ℝ ψ)) V :=
    (hψ.contDiffOn.fderiv_of_isOpen hV (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen hV
      le_rfl
  -- Step 2: the Gram operator `G(x) = Dψ(x)* ∘ Dψ(x)` is continuous on `V`; it is a unit at each
  -- `x ∈ V` (`Dψ(x)` is injective), and `Ring.inverse` is continuous at units, so `G⁻¹` is too.
  have hG : ContinuousOn (fun x ↦ ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x) V :=
    ((ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Rn n) (F := Rn N)).continuous.comp_continuousOn
      hA).clm_comp hA
  have hGinv : ContinuousOn
      (fun x ↦ Ring.inverse (ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x)) V := by
    intro x hx
    have hu := Submission.gram_operator_isUnit_of_injective n N (fderiv ℝ ψ x)
      (hψ.injective_fderiv hx)
    have hinv := NormedRing.inverse_continuousAt hu.unit
    rw [hu.unit_spec] at hinv
    exact ContinuousAt.comp_continuousWithinAt
      (f := fun x ↦ ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x) hinv (hG x hx)
  -- Step 3: `w(x) = ∑ₖ ∑ₗ ⟪eₖ, G(x)⁻¹ eₗ⟫ • D²ψ(x)[eₖ, eₗ]` is continuous on `V`.
  have hw : ContinuousOn (fun x ↦ ∑ k : Fin n, ∑ l : Fin n,
      inner ℝ (EuclideanSpace.single k (1 : ℝ))
          (Ring.inverse (ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x)
            (EuclideanSpace.single l (1 : ℝ))) •
        fderiv ℝ (fderiv ℝ ψ) x (EuclideanSpace.single k (1 : ℝ))
          (EuclideanSpace.single l (1 : ℝ))) V :=
    continuousOn_finsetSum _ fun k _ ↦ continuousOn_finsetSum _ fun l _ ↦
      (continuousOn_const.inner (hGinv.clm_apply continuousOn_const)).fun_smul
        ((hS.clm_apply continuousOn_const).clm_apply continuousOn_const)
  -- Step 4: `x ↦ P_{ψ(x)}` is continuous on `V`, since `ψ` maps `V` into `M`.
  have hmaps : MapsTo ψ V M := fun x hx ↦ (hψ.image_eq ▸ mem_image_of_mem ψ hx).2
  have hPψ : ContinuousOn (fun x ↦ tangentProjection M (ψ x)) V :=
    hP.comp hψ.contDiffOn.continuousOn hmaps
  -- Step 5: on `V`, `H(ψ(x)) = w(x)^⊥ = w(x) - P_{ψ(x)} w(x)` by the Gram trace formula.
  refine (hw.sub (hPψ.clm_apply hw)).congr fun x hx ↦ ?_
  exact Submission.mean_curvature_eq_normalPart_gram_trace n N M (ψ x) (fderiv ℝ ψ x)
    (fderiv ℝ (fderiv ℝ ψ) x) (hψ.injective_fderiv hx) (htan x hx) (hsff x hx)
/-- **Continuity on a Simon submanifold can be checked in charts.** If `M ⊆ ℝᴺ` is an
`n`-dimensional `C^r` Simon submanifold and `x ↦ F (ψ x)` is continuous on `V` for every chart
`(V, W, ψ)` of `M`, then `F` is continuous on `M`. At `y₀ = ψ x₀ ∈ M`, continuity of `F ∘ ψ` at
`x₀` gives an open `U₀ ∋ x₀` with `F (ψ x) ∈ O` for `x ∈ U₀`. If `closedBall y₀ ε ⊆ W`, relative
properness makes `K = V ∩ ψ⁻¹(closedBall y₀ ε)` compact, so `C = ψ (K \ U₀)` is compact, hence
closed, and `y₀ ∉ C` by injectivity of `ψ` on `V`. As `ψ V = W ∩ M`, every `z` in
`(ball y₀ ε \ C) ∩ M` is `ψ x` with `x ∈ K ∩ U₀`, so `F z ∈ O`. -/
theorem Submission.simon_submanifold_continuousOn_of_chart_continuousOn : ∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)) (X : Type) [TopologicalSpace X] (F : Rn N → X), Chapter02.IsSimonSubmanifold (E := Rn n) r M → (∀ (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N), Chapter02.IsSimonLocalRepresentation r M V W ψ → ContinuousOn (fun x ↦ F (ψ x)) V) → ContinuousOn F M := by
  intro n N r M X _ F hM hF y₀ hy₀
  -- Step 2: a chart `(V, W, ψ)` with `y₀ ∈ W`, and `x₀ ∈ V` with `ψ x₀ = y₀`.
  obtain ⟨V, W, ψ, hy₀W, hψ⟩ := hM.2 y₀ hy₀
  obtain ⟨x₀, hx₀V, rfl⟩ : y₀ ∈ ψ '' V := by
    rw [hψ.image_eq]
    exact ⟨hy₀W, hy₀⟩
  -- Step 1: it suffices that `F ⁻¹' O ∈ 𝓝[M] (ψ x₀)` for each neighbourhood `O` of `F (ψ x₀)`.
  rw [ContinuousWithinAt, Filter.tendsto_def]
  intro O hO
  -- Step 3: `F ∘ ψ` is continuous at `x₀ ∈ V` (`V` is open), so an open `U₀ ∋ x₀` maps into `O`.
  have hFψ : ContinuousAt (fun x ↦ F (ψ x)) x₀ :=
    (hF V W ψ hψ x₀ hx₀V).continuousAt (hψ.isOpen_source.mem_nhds hx₀V)
  obtain ⟨U₀, hU₀O, hU₀, hx₀U₀⟩ := _root_.mem_nhds_iff.mp (hFψ.preimage_mem_nhds hO)
  -- Step 4: `Q = closedBall (ψ x₀) ε ⊆ W`; `K = V ∩ ψ ⁻¹' Q` is compact by relative properness,
  -- so `C = ψ '' (K \ U₀)` is compact, hence closed.
  obtain ⟨ε, hε, hQW⟩ := nhds_basis_closedBall.mem_iff.mp (hψ.isOpen_target.mem_nhds hy₀W)
  have hK : IsCompact (V ∩ ψ ⁻¹' closedBall (ψ x₀) ε) :=
    hψ.isCompact_source_inter_preimage _ (isCompact_closedBall _ _) hQW
  have hC : IsClosed (ψ '' ((V ∩ ψ ⁻¹' closedBall (ψ x₀) ε) \ U₀)) :=
    ((hK.diff hU₀).image_of_continuousOn
      (hψ.contDiffOn.continuousOn.mono fun _ hx ↦ hx.1.1)).isClosed
  -- Step 5: `ψ x₀ ∉ C`, by injectivity of `ψ` on `V`.
  have hx₀C : ψ x₀ ∉ ψ '' ((V ∩ ψ ⁻¹' closedBall (ψ x₀) ε) \ U₀) := by
    rintro ⟨x, ⟨⟨hxV, -⟩, hxU₀⟩, hx⟩
    exact hxU₀ (hψ.injOn hxV hx₀V hx ▸ hx₀U₀)
  -- Steps 6–7: `W₀ = ball (ψ x₀) ε \ C` is open and contains `ψ x₀`; every `z ∈ W₀ ∩ M` is
  -- `ψ x` with `x ∈ K ∩ U₀`, so `F z ∈ O`.
  refine mem_nhdsWithin.mpr ⟨ball (ψ x₀) ε \ ψ '' ((V ∩ ψ ⁻¹' closedBall (ψ x₀) ε) \ U₀),
    isOpen_ball.sdiff hC, ⟨mem_ball_self hε, hx₀C⟩, ?_⟩
  rintro z ⟨⟨hzB, hzC⟩, hzM⟩
  obtain ⟨x, hxV, rfl⟩ : z ∈ ψ '' V := by
    rw [hψ.image_eq]
    exact ⟨hQW (ball_subset_closedBall hzB), hzM⟩
  have hxU₀ : x ∈ U₀ := by
    by_contra hxU₀
    exact hzC ⟨x, ⟨⟨hxV, ball_subset_closedBall hzB⟩, hxU₀⟩, rfl⟩
  exact hU₀O hxU₀
/-- **Derivative of the Gram map.** If `ψ : ℝⁿ → ℝᴺ` is `C²` on an open `V`, then
`G(x) = Dψ(x)* ∘ Dψ(x)` is `C¹` on `V` and `DG(x)[v] = Dψ(x)* ∘ D²ψ(x)[v] + (D²ψ(x)[v])* ∘ Dψ(x)`,
with `L*` the adjoint. Over `ℝ` the adjoint is a continuous linear map `adjR`, so
`x ↦ Dψ(x)* = adjR ∘ Dψ` is `C¹` on `V` with derivative `adjR ∘ D²ψ(x)` (chain rule). Both claims
then follow from the regularity (`ContDiffOn.clm_comp`) and the product rule
(`HasFDerivAt.clm_comp`) of the continuous bilinear composition `(B, C) ↦ B ∘L C`. -/
theorem Submission.adjoint_comp_fderiv_contDiffOn_fderiv_eq_add : ∀ (n N : ℕ) (V : Set (Rn n)) (ψ : Rn n → Rn N), IsOpen V → ContDiffOn ℝ 2 ψ V → ContDiffOn ℝ 1 (fun x ↦ ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x) V ∧ ∀ x ∈ V, ∀ v : Rn n, fderiv ℝ (fun x ↦ ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x) x v = ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ (fderiv ℝ ψ) x v + ContinuousLinearMap.adjoint (fderiv ℝ (fderiv ℝ ψ) x v) ∘L fderiv ℝ ψ x := by
  intro n N V ψ hV hψ
  -- Step 1: the adjoint over `ℝ` as a continuous `ℝ`-linear map `adjR`; `adjR L = L*` by `rfl`.
  let adjR : (Rn n →L[ℝ] Rn N) →L[ℝ] (Rn N →L[ℝ] Rn n) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Rn n) (F := Rn N)).toContinuousLinearEquiv.toContinuousLinearMap
  -- Step 2: `A = Dψ` is `C¹` on `V` (`1 + 1 ≤ 2`).
  have hA : ContDiffOn ℝ 1 (fderiv ℝ ψ) V := hψ.fderiv_of_isOpen hV (by norm_num)
  -- Step 3: `x ↦ A(x)* = adjR ∘ A` is `C¹` on `V`.
  have hAd : ContDiffOn ℝ 1 (fun x ↦ ContinuousLinearMap.adjoint (fderiv ℝ ψ x)) V :=
    adjR.contDiff.comp_contDiffOn hA
  -- Step 4 (first conjunct): `G = A* ∘L A` is `C¹` on `V`.
  refine ⟨hAd.clm_comp hA, fun x hx v ↦ ?_⟩
  -- Step 2 at `x ∈ V`: `A` has derivative `D²ψ(x)` at `x`, since `V` is a neighbourhood of `x`.
  have hAx : HasFDerivAt (fderiv ℝ ψ) (fderiv ℝ (fderiv ℝ ψ) x) x :=
    ((hA.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds hx)).hasFDerivAt
  -- Step 3 at `x` (chain rule): `x ↦ A(x)*` has derivative `adjR ∘L D²ψ(x)` at `x`.
  have hAdx : HasFDerivAt (fun x ↦ ContinuousLinearMap.adjoint (fderiv ℝ ψ x))
      (adjR ∘L fderiv ℝ (fderiv ℝ ψ) x) x :=
    adjR.hasFDerivAt.comp x hAx
  -- Step 5 (second conjunct): by the product rule and uniqueness of the derivative,
  -- `DG(x)[v] = A(x)* ∘L D²ψ(x)[v] + adjR (D²ψ(x)[v]) ∘L A(x)`, and `adjR L = L*` by `rfl`.
  rw [(hAdx.clm_comp hAx).fderiv]
  rfl
/-- **Trace swap under a symmetric weight.** For `A, S : ℝⁿ → ℝᴺ` and a symmetric `P : ℝⁿ → ℝⁿ`
(`⟨P v, w⟩ = ⟨v, P w⟩`), `tr(P ∘ S* ∘ A) = tr(P ∘ A* ∘ S)`, with `L*` the adjoint. By cyclicity,
`tr(P ∘ A* ∘ S) = tr((A* ∘ S) ∘ P)`. Both traces are then expanded in the standard orthonormal
basis `(e_l)` of `ℝⁿ`, and the terms agree:
`⟨e, P S* A e⟩ = ⟨P e, S* A e⟩ = ⟨S P e, A e⟩ = ⟨A* S P e, e⟩ = ⟨e, A* S P e⟩`. -/
theorem Submission.trace_comp_adjoint_comp_swap_of_symm : ∀ (n N : ℕ) (A S : Rn n →L[ℝ] Rn N) (P : Rn n →L[ℝ] Rn n), (∀ v w : Rn n, inner ℝ (P v) w = inner ℝ v (P w)) → LinearMap.trace ℝ (Rn n) (P ∘L ContinuousLinearMap.adjoint S ∘L A).toLinearMap = LinearMap.trace ℝ (Rn n) (P ∘L ContinuousLinearMap.adjoint A ∘L S).toLinearMap := by
  intro n N A S P hP
  -- Step 1 (cyclicity): `tr(P ∘ A* ∘ S) = tr((A* ∘ S) ∘ P)`.
  have hcyc : LinearMap.trace ℝ (Rn n) (P ∘L ContinuousLinearMap.adjoint A ∘L S).toLinearMap =
      LinearMap.trace ℝ (Rn n)
        ((ContinuousLinearMap.adjoint A ∘L S).toLinearMap ∘ₗ P.toLinearMap) :=
    LinearMap.trace_comp_comm' (ContinuousLinearMap.adjoint A ∘L S).toLinearMap P.toLinearMap
  -- Step 2: expand both traces in the standard orthonormal basis `(e_l)` and compare termwise.
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  rw [hcyc, LinearMap.trace_eq_sum_inner _ e, LinearMap.trace_eq_sum_inner _ e]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  -- Step 3: `⟨e, P S* A e⟩ = ⟨P e, S* A e⟩ = ⟨S P e, A e⟩ = ⟨A* S P e, e⟩ = ⟨e, A* S P e⟩`.
  calc inner ℝ (e l) ((P ∘L ContinuousLinearMap.adjoint S ∘L A).toLinearMap (e l))
      = inner ℝ (e l) (P (ContinuousLinearMap.adjoint S (A (e l)))) := rfl
    _ = inner ℝ (P (e l)) (ContinuousLinearMap.adjoint S (A (e l))) := (hP _ _).symm
    _ = inner ℝ (S (P (e l))) (A (e l)) := ContinuousLinearMap.adjoint_inner_right S _ _
    _ = inner ℝ (ContinuousLinearMap.adjoint A (S (P (e l)))) (e l) :=
      (ContinuousLinearMap.adjoint_inner_left A _ _).symm
    _ = inner ℝ (e l) (ContinuousLinearMap.adjoint A (S (P (e l)))) := real_inner_comm _ _
    _ = inner ℝ (e l)
        (((ContinuousLinearMap.adjoint A ∘L S).toLinearMap ∘ₗ P.toLinearMap) (e l)) := rfl
/-- **Gram operator of an injective linear map and the range projection.** For an injective
`A : ℝⁿ →L[ℝ] ℝᴺ` with `K = range A`, the Gram operator `G = A* ∘L A` is a unit of `ℝⁿ →L[ℝ] ℝⁿ`,
its ring inverse `G⁻¹` is symmetric, and `K.starProjection = A ∘L G⁻¹ ∘L A*`. `G` is injective
because `ker (A* ∘L A) = ker A` (`ContinuousLinearMap.adjoint_comp_self_injective_iff`), so in
finite dimension it is a continuous linear automorphism. Then
`⟪G⁻¹v, w⟫ = ⟪G⁻¹v, G G⁻¹w⟫ = ⟪A G⁻¹v, A G⁻¹w⟫ = ⟪G G⁻¹v, G⁻¹w⟫ = ⟪v, G⁻¹w⟫`, and
`A G⁻¹ A* z ∈ range A` with `⟪z - A G⁻¹ A* z, A c⟫ = ⟪A* z - G G⁻¹ A* z, c⟫ = 0`, which
characterizes the orthogonal projection (`Submodule.eq_starProjection_of_mem_of_inner_eq_zero`). -/
theorem Submission.gram_inverse_range_starProjection : ∀ (n N : ℕ) (K : Submodule ℝ (Rn N)) (A : Rn n →L[ℝ] Rn N), Function.Injective A → K = LinearMap.range A.toLinearMap → IsUnit (ContinuousLinearMap.adjoint A ∘L A) ∧ (∀ v w : Rn n, inner ℝ (Ring.inverse (ContinuousLinearMap.adjoint A ∘L A) v) w = inner ℝ v (Ring.inverse (ContinuousLinearMap.adjoint A ∘L A) w)) ∧ K.starProjection = A ∘L Ring.inverse (ContinuousLinearMap.adjoint A ∘L A) ∘L ContinuousLinearMap.adjoint A := by
  intro n N K A hA hK
  subst hK
  set G := ContinuousLinearMap.adjoint A ∘L A
  -- Step 2: `G` is injective, since `ker (A* ∘L A) = ker A = ⊥`.
  have hGinj : Function.Injective G := (ContinuousLinearMap.adjoint_comp_self_injective_iff A).2 hA
  -- Step 3: an injective endomorphism of `ℝⁿ` is a continuous linear automorphism, so `G` is a unit.
  have hunit : IsUnit G := by
    let e : Rn n ≃L[ℝ] Rn n :=
      (LinearEquiv.ofInjectiveEndo (G : Rn n →ₗ[ℝ] Rn n) hGinj).toContinuousLinearEquiv
    exact ⟨e.toUnit, by ext x; rfl⟩
  have hGG : ∀ x, G (Ring.inverse G x) = x := fun x => by
    rw [← mul_apply_eq_comp, Ring.mul_inverse_cancel G hunit, one_apply_eq_self]
  -- Step 1: `⟪G x, y⟫ = ⟪A x, A y⟫ = ⟪x, G y⟫`.
  have hl : ∀ x y, inner ℝ (G x) y = inner ℝ (A x) (A y) := fun x y =>
    ContinuousLinearMap.adjoint_inner_left A y (A x)
  have hr : ∀ x y, inner ℝ x (G y) = inner ℝ (A x) (A y) := fun x y =>
    ContinuousLinearMap.adjoint_inner_right A x (A y)
  refine ⟨hunit, fun v w => ?_, ?_⟩
  -- Step 4: `G⁻¹` is symmetric.
  · calc inner ℝ (Ring.inverse G v) w = inner ℝ (Ring.inverse G v) (G (Ring.inverse G w)) := by
          rw [hGG]
      _ = inner ℝ (G (Ring.inverse G v)) (Ring.inverse G w) := by rw [hl, hr]
      _ = inner ℝ v (Ring.inverse G w) := by rw [hGG]
  -- Step 7: `A G⁻¹ A* z ∈ range A` and `z - A G⁻¹ A* z` is orthogonal to `range A`.
  · ext1 z
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (LinearMap.mem_range_self _ _) ?_
    rintro _ ⟨c, rfl⟩
    rw [ContinuousLinearMap.coe_coe, ← ContinuousLinearMap.adjoint_inner_left, map_sub]
    have h : ContinuousLinearMap.adjoint A ((A ∘L Ring.inverse G ∘L ContinuousLinearMap.adjoint A) z) =
        ContinuousLinearMap.adjoint A z := hGG _
    rw [h, sub_self, inner_zero_left]

/-- **Tangential divergence in a chart.** If `T_y M = range A` for an injective `A : ℝⁿ → ℝᴺ`, then
`div_M Y(y) = tr(G⁻¹ A* L A)`, a trace on `ℝⁿ`, where `L = DY(y)`, `A*` is the adjoint and `G = A* A`;
no differentiability of `Y` is needed. Write `T = T_y M`, `q : ℝᴺ → T` for the orthogonal projection
and `ι : T → ℝᴺ` for the inclusion. In the orthonormal basis `τᵢ` of `T` defining the frame,
`tr_T(q L ι) = ∑ᵢ ⟨τᵢ, q L τᵢ⟩ = ∑ᵢ ⟨τᵢ, L τᵢ⟩ = div_M Y(y)`, and cyclicity turns this into
`tr_{ℝᴺ}(L P_T)` with `P_T = ι q`. The Gram projection formula `P_T = A G⁻¹ A*` and cyclicity once
more give `tr_{ℝᴺ}((L A)(G⁻¹ A*)) = tr_{ℝⁿ}((G⁻¹ A*)(L A))`. -/
theorem Submission.chart_tangentialDivergence_eq_gram_trace : ∀ (n N : ℕ) (M : Set (Rn N)) (y : Rn N) (A : Rn n →L[ℝ] Rn N) (Y : Rn N → Rn N), Function.Injective A → tangentSpace M y = LinearMap.range A.toLinearMap → tangentialDivergence M Y y = LinearMap.trace ℝ (Rn n) (Ring.inverse (ContinuousLinearMap.adjoint A ∘L A) ∘L ContinuousLinearMap.adjoint A ∘L fderiv ℝ Y y ∘L A).toLinearMap := by
  intro n N M y A Y hA hT
  -- Steps 1–3: `div_M Y(y) = tr_{ℝᴺ}(L ∘ P_T)` with `T = T_y M`, `L = DY(y)` and `P_T = ι ∘ q`.
  have hdiv : tangentialDivergence M Y y = LinearMap.trace ℝ (Rn N)
      (fderiv ℝ Y y ∘L (tangentSpace M y).starProjection).toLinearMap := by
    -- Steps 1–2: expand `tr_T(q ∘ L ∘ ι)` in the orthonormal basis `b` of `T` that defines the
    -- frame `τᵢ = b i`; since `b i ∈ T`, `⟨b i, q (L (b i))⟩_T = ⟨b i, L (b i)⟩`.
    have hsum : LinearMap.trace ℝ (tangentSpace M y)
        ((tangentSpace M y).orthogonalProjectionOnto.toLinearMap ∘ₗ
          ((fderiv ℝ Y y).toLinearMap ∘ₗ (tangentSpace M y).subtype)) =
        tangentialDivergence M Y y := by
      unfold tangentialDivergence
      rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ (tangentSpace M y))]
      exact Finset.sum_congr rfl fun i _ ↦
        Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left _ _
    -- Step 3 (cyclicity): `tr_T(q ∘ (L ∘ ι)) = tr_{ℝᴺ}((L ∘ ι) ∘ q)`, and `ι ∘ q = P_T` by the
    -- definition of `starProjection`.
    rw [← hsum]
    exact LinearMap.trace_comp_comm' _ _
  -- Step 4: `P_T = A G⁻¹ A*` by the Gram projection formula (`T = range A`, `A` injective).
  rw [hdiv, (Submission.gram_inverse_range_starProjection n N _ A hA hT).2.2]
  -- Step 5 (cyclicity): `tr_{ℝᴺ}((L ∘ A) ∘ (G⁻¹ ∘ A*)) = tr_{ℝⁿ}((G⁻¹ ∘ A*) ∘ (L ∘ A))`.
  exact LinearMap.trace_comp_comm'
    (Ring.inverse (ContinuousLinearMap.adjoint A ∘L A) ∘L ContinuousLinearMap.adjoint A).toLinearMap
    (fderiv ℝ Y y ∘L A).toLinearMap
/-- **Mean curvature through an injective parametrization differential** (Simon 4.27 in a chart).
Let `A : ℝⁿ → ℝᴺ` be injective with `T_y M = range A`, and let `S` be bilinear (not necessarily
symmetric) with `B_y(Aa, Ab) = S(a, b)^⊥`. With `G = A*A` and `eₗ` the standard basis of `ℝⁿ`,
`H(y) = (∑ₗ S(eₗ, G⁻¹eₗ))^⊥`. Choose `aᵢ` with `Aaᵢ = τᵢ` for the frame `τᵢ` of `T_y M`, so
`H(y) = (∑ᵢ S(aᵢ, aᵢ))^⊥`. Expanding `Ac ∈ T_y M` in the frame and using injectivity of `A` gives
`c = ∑ᵢ ⟨Aaᵢ, Ac⟩ aᵢ`; for `c = G⁻¹eₗ`, `GG⁻¹ = 1` (`gram_inverse_range_starProjection`) turns this
into `G⁻¹eₗ = ∑ᵢ ⟨aᵢ, eₗ⟩ aᵢ`. Bilinearity and `∑ₗ ⟨aᵢ, eₗ⟩ eₗ = aᵢ` give
`∑ₗ S(eₗ, G⁻¹eₗ) = ∑ᵢ S(aᵢ, aᵢ)`. -/
theorem Submission.chart_meanCurvature_eq_normalPart_gram_sum : ∀ (n N : ℕ) (M : Set (Rn N)) (y : Rn N) (A : Rn n →L[ℝ] Rn N) (S : Rn n →L[ℝ] Rn n →L[ℝ] Rn N), Function.Injective A → tangentSpace M y = LinearMap.range A.toLinearMap → (∀ a b : Rn n, secondFundamentalForm M y (A a) (A b) = normalPart M y (S a b)) → meanCurvature M y = normalPart M y (∑ l : Fin n, S (EuclideanSpace.single l 1) (Ring.inverse (ContinuousLinearMap.adjoint A ∘L A) (EuclideanSpace.single l 1))) := by
  intro n N M y A S hA hT hB
  -- Step 1: `G = A*A` is a unit (sibling `gram_projection`), so `A*(A(G⁻¹w)) = G(G⁻¹w) = w`.
  have hG := (Submission.gram_inverse_range_starProjection n N (tangentSpace M y) A hA hT).1
  have hGG : ∀ w : Rn n, ContinuousLinearMap.adjoint A
      (A (Ring.inverse (ContinuousLinearMap.adjoint A ∘L A) w)) = w :=
    fun w ↦ DFunLike.congr_fun (Ring.mul_inverse_cancel _ hG) w
  -- Steps 2–3: every frame vector `τᵢ` of `T_y M = range A` has a preimage `aᵢ`.
  have hpre : ∀ i, ∃ a : Rn n, A a = tangentFrame M y i := fun i ↦ by
    have hi : tangentFrame M y i ∈ tangentSpace M y :=
      (stdOrthonormalBasis ℝ (tangentSpace M y) i).2
    rw [hT] at hi
    exact LinearMap.mem_range.1 hi
  choose a ha using hpre
  -- Step 4: `H(y) = ∑ᵢ B(Aaᵢ, Aaᵢ) = ∑ᵢ S(aᵢ, aᵢ)^⊥ = (∑ᵢ S(aᵢ, aᵢ))^⊥`.
  have hH : meanCurvature M y = normalPart M y (∑ i, S (a i) (a i)) := by
    have hnp : normalPart M y (∑ i, S (a i) (a i)) = ∑ i, normalPart M y (S (a i) (a i)) := by
      simp only [normalPart, map_sum, Finset.sum_sub_distrib]
    rw [hnp, meanCurvature]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← ha i, hB]
  -- Step 5: reproducing formula `c = ∑ᵢ ⟨Aaᵢ, Ac⟩ aᵢ`, from the frame expansion of `Ac ∈ T_y M`.
  have hrep : ∀ c : Rn n, ∑ i, inner ℝ (A (a i)) (A c) • a i = c := by
    intro c
    apply hA
    have hc : A c ∈ tangentSpace M y := by
      rw [hT]
      exact LinearMap.mem_range_self A.toLinearMap c
    have h := congrArg Subtype.val
      ((stdOrthonormalBasis ℝ (tangentSpace M y)).sum_repr' ⟨A c, hc⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at h
    rw [map_sum]
    simp only [map_smul, ha]
    exact h
  -- Step 6: `G⁻¹eₗ = ∑ᵢ ⟨aᵢ, eₗ⟩ aᵢ`, since `⟨Aaᵢ, A(G⁻¹eₗ)⟩ = ⟨aᵢ, A*A(G⁻¹eₗ)⟩ = ⟨aᵢ, eₗ⟩`.
  have hGinv : ∀ l : Fin n, Ring.inverse (ContinuousLinearMap.adjoint A ∘L A)
      (EuclideanSpace.single l 1) = ∑ i, inner ℝ (a i) (EuclideanSpace.single l 1) • a i := by
    intro l
    refine (hrep _).symm.trans (Finset.sum_congr rfl fun i _ ↦ ?_)
    rw [← ContinuousLinearMap.adjoint_inner_right A (a i), hGG]
  -- `∑ₗ ⟨v, eₗ⟩ eₗ = v`: the expansion in the standard orthonormal basis of `ℝⁿ`.
  have hexp : ∀ v : Rn n,
      ∑ l : Fin n, inner ℝ v (EuclideanSpace.single l 1) • EuclideanSpace.single l (1 : ℝ) = v := by
    intro v
    conv_rhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr' v]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [EuclideanSpace.basisFun_apply, real_inner_comm]
  -- Step 7: `∑ₗ S(eₗ, G⁻¹eₗ) = ∑ᵢ ∑ₗ ⟨aᵢ, eₗ⟩ S(eₗ, aᵢ) = ∑ᵢ S(∑ₗ ⟨aᵢ, eₗ⟩ eₗ, aᵢ) = ∑ᵢ S(aᵢ, aᵢ)`.
  have hS : ∑ l : Fin n, S (EuclideanSpace.single l 1)
      (Ring.inverse (ContinuousLinearMap.adjoint A ∘L A) (EuclideanSpace.single l 1)) =
      ∑ i, S (a i) (a i) := by
    simp only [hGinv, map_sum, map_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    calc ∑ l : Fin n, inner ℝ (a i) (EuclideanSpace.single l 1) • S (EuclideanSpace.single l 1) (a i)
        = S (∑ l : Fin n, inner ℝ (a i) (EuclideanSpace.single l 1) •
            EuclideanSpace.single l (1 : ℝ)) (a i) := by
          simp only [map_sum, map_smul, sum_apply, smul_apply]
      _ = S (a i) (a i) := by rw [hexp]
  -- Step 8: combine Steps 4 and 7.
  rw [hH, hS]
/-- **Smoothness of the determinant on `L(ℝⁿ)`.** For every `n` and every order `k : WithTop ℕ∞`
(finite, `∞` or analytic), `T ↦ T.det` is `C^k` on `ℝⁿ →L[ℝ] ℝⁿ`. In the standard basis `eᵢ` the
Leibniz formula gives `T.det = ∑_σ sign σ * ∏ᵢ (T eᵢ)_{σ i}` (`LinearMap.det_toMatrix`,
`Matrix.det_apply`). Each entry `T ↦ (T eᵢ)_l` is continuous linear, and finite sums and products of
`C^k` functions are `C^k` (`ContDiff.sum`, `contDiff_prod`). -/
theorem Submission.contDiff_rn_continuousLinearMap_det : ∀ (n : ℕ) (k : WithTop ℕ∞), ContDiff ℝ k (fun T : Rn n →L[ℝ] Rn n ↦ T.det) := by
  intro n k
  -- Steps 1–2: the Leibniz formula in the standard basis, whose matrix entries are `(T eᵢ)_l`.
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have h : (fun T : Rn n →L[ℝ] Rn n ↦ T.det) = fun T ↦ ∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, (T (EuclideanSpace.single i (1 : ℝ))).ofLp (σ i) := by
    funext T
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b, Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ ↦ ?_
    rw [Units.smul_def, zsmul_eq_mul]
    congr 1
  rw [h]
  -- Steps 3–4: each entry is a continuous linear functional of `T`; close under `∏` and `∑`.
  refine ContDiff.sum fun σ _ ↦ contDiff_const.mul (contDiff_prod fun i _ ↦ ?_)
  exact ((EuclideanSpace.proj (σ i)).comp
    (ContinuousLinearMap.apply ℝ (Rn n) (EuclideanSpace.single i (1 : ℝ)))).contDiff
/-- **Jacobi's formula at the identity.** For `K ∈ L(ℝⁿ)`, `t ↦ det(1 + t • K)` has derivative
`trace K` at `t = 0`. With `b` the standard basis of `ℝⁿ` and `A = [K]_b`, the matrix of `1 + t • K` is
`1 + t • A`, so `det(1 + t • K) = det(1 + t • A) = 1 + trace A · t + p(t) t²` for every `t`, with the
fixed polynomial `p = (det(1 + X • A)).divX.divX` (`LinearMap.det_toMatrix`,
`Matrix.det_one_add_smul`). The right side has derivative `trace A` at `0`, and `trace A = trace K`
(`LinearMap.trace_eq_matrix_trace`). -/
theorem Submission.hasDerivAt_rn_det_one_add_smul_trace : ∀ (n : ℕ) (K : Rn n →L[ℝ] Rn n), HasDerivAt (fun t : ℝ ↦ (1 + t • K).det) (LinearMap.trace ℝ (Rn n) K.toLinearMap) 0 := by
  intro n K
  -- Step 1: the standard basis `b` of `ℝⁿ`, the matrix `A` of `K` and the fixed polynomial `p`.
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin n) (Fin n) ℝ, LinearMap.toMatrix b b K.toLinearMap = A :=
    ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : Polynomial ℝ,
      (1 + (Polynomial.X : Polynomial ℝ) • A.map Polynomial.C).det.divX.divX = p := ⟨_, rfl⟩
  -- Steps 2–3: `[1 + t • K]_b = 1 + t • A`, so `det(1 + t • K) = 1 + trace A * t + p(t) * t ^ 2`.
  have hexp : ∀ t : ℝ, (1 + t • K).det = 1 + A.trace * t + p.eval t * t ^ 2 := fun t ↦ by
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b, ContinuousLinearMap.toLinearMap_add,
      ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.toLinearMap_one, map_add, map_smul,
      LinearMap.toMatrix_one, hA, Matrix.det_one_add_smul, hp]
  -- Step 5: `t ↦ 1 + trace A * t + p(t) * t ^ 2` has derivative `trace A + 0` at `0`.
  have hlin : HasDerivAt (fun t : ℝ ↦ A.trace * t) A.trace 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul A.trace
  have hquad : HasDerivAt (fun t : ℝ ↦ p.eval t * t ^ 2) 0 0 := by
    simpa using (Polynomial.hasDerivAt p 0).fun_mul (hasDerivAt_pow 2 (0 : ℝ))
  have hg := (hlin.const_add 1).fun_add hquad
  rw [add_zero] at hg
  -- Steps 4 and 6: `trace K = trace A`, and `det(1 + t • K)` agrees with the polynomial everywhere.
  rw [LinearMap.trace_eq_matrix_trace ℝ b, hA]
  exact hg.congr_of_eventuallyEq (Filter.Eventually.of_forall hexp)

/-- **Jacobi's formula on `L(ℝⁿ)`.** `det : L(ℝⁿ) → ℝ` is `C¹`, and at a unit `T` of the ring
`L(ℝⁿ)` (multiplication is composition), `D det(T)[H] = det T · trace(T⁻¹ ∘ H)` with
`T⁻¹ = Ring.inverse T`. The first conjunct is `Submission.contDiff_rn_continuousLinearMap_det` at
order `1`. For the second, put `K = T⁻¹ ∘ H`: then `T + t • H = T ∘ (1 + t • K)`
(`Ring.mul_inverse_cancel`), so `det(T + t • H) = det T · det(1 + t • K)` (`LinearMap.det_comp`), which
has derivative `det T · trace K` at `t = 0` by `Submission.hasDerivAt_rn_det_one_add_smul_trace`. The
chain rule along `t ↦ T + t • H` and uniqueness of derivatives identify it with `D det(T)[H]`. -/
theorem Submission.continuousLinearMap_det_contDiff_fderiv_eq_mul_trace : ∀ n : ℕ, ContDiff ℝ 1 (fun T : Rn n →L[ℝ] Rn n ↦ T.det) ∧ ∀ T H : Rn n →L[ℝ] Rn n, IsUnit T → fderiv ℝ (fun T : Rn n →L[ℝ] Rn n ↦ T.det) T H = T.det * LinearMap.trace ℝ (Rn n) (Ring.inverse T ∘L H).toLinearMap := by
  intro n
  -- Step 2: `det` is `C¹`, hence differentiable at every `T`.
  have hC1 : ContDiff ℝ 1 (fun T : Rn n →L[ℝ] Rn n ↦ T.det) :=
    Submission.contDiff_rn_continuousLinearMap_det n 1
  refine ⟨hC1, fun T H hT ↦ ?_⟩
  -- Step 3: `T ∘ (1 + t • K) = T + t • H` for `K = T⁻¹ ∘ H`, since `T ∘ T⁻¹ = 1`.
  have hTK : T * (Ring.inverse T ∘L H) = H := by
    rw [← ContinuousLinearMap.mul_def, ← mul_assoc, Ring.mul_inverse_cancel T hT, one_mul]
  have hfac : ∀ t : ℝ, T * (1 + t • (Ring.inverse T ∘L H)) = T + t • H := fun t ↦ by
    rw [mul_add, mul_one, ContinuousLinearMap.mul_def T, ContinuousLinearMap.comp_smul,
      ← ContinuousLinearMap.mul_def, hTK]
  -- Steps 3–5: `det(T + t • H) = det T · det(1 + t • K)` has derivative `det T · trace K` at `0`.
  have hline : HasDerivAt (fun t : ℝ ↦ (T + t • H).det)
      (T.det * LinearMap.trace ℝ (Rn n) (Ring.inverse T ∘L H).toLinearMap) 0 := by
    have hmul : (fun t : ℝ ↦ (T + t • H).det) =
        fun t ↦ T.det * (1 + t • (Ring.inverse T ∘L H)).det :=
      funext fun t ↦ by rw [← hfac t]; exact LinearMap.det_comp _ _
    rw [hmul]
    exact (Submission.hasDerivAt_rn_det_one_add_smul_trace n (Ring.inverse T ∘L H)).const_mul T.det
  -- Step 6: chain rule along `γ t = T + t • H` (`γ 0 = T`, `γ' 0 = H`) and uniqueness.
  have hγ : HasDerivAt (fun t : ℝ ↦ T + t • H) H 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const H).const_add T
  have hchain := ((hC1.differentiable one_ne_zero) T).hasFDerivAt.comp_hasDerivAt_of_eq 0 hγ
    (show T = T + (0 : ℝ) • H by rw [zero_smul ℝ H, add_zero])
  exact hchain.unique hline

/-- **Simon Ch. 2, §5, derivative of the area Jacobian of a `C²` immersion.** Let `V ⊆ ℝⁿ` be open
and `ψ : ℝⁿ → ℝᴺ` be `C²` on `V` with injective `A(x) = Dψ(x)`, and let `G(x) = A(x)* A(x)`. Then
`J = areaJacobianAt ψ = √(det ∘ G)` is `C¹` on `V` and `DJ(x)[v] = J(x) tr(G(x)⁻¹ A(x)* S_v)`, where
`S_v = D²ψ(x)[v]`. Indeed `G` is `C¹` with `DG(x)[v] = A* S_v + S_v* A`, Jacobi's formula gives
`D(det ∘ G)(x)[v] = det G · tr(G⁻¹ DG(x)[v])`, the symmetry of `G⁻¹` turns `tr(G⁻¹ S_v* A)` into
`tr(G⁻¹ A* S_v)`, and `det G = J² > 0` because `A(x)` is injective. -/
theorem Submission.areaJacobianAt_contDiffOn_fderiv_eq_gram_trace : ∀ (n N : ℕ) (V : Set (Rn n)) (ψ : Rn n → Rn N), IsOpen V → ContDiffOn ℝ 2 ψ V → (∀ x ∈ V, Function.Injective (fderiv ℝ ψ x)) → ContDiffOn ℝ 1 (Chapter02.areaJacobianAt ψ) V ∧ ∀ x ∈ V, ∀ v : Rn n, fderiv ℝ (Chapter02.areaJacobianAt ψ) x v = Chapter02.areaJacobianAt ψ x * LinearMap.trace ℝ (Rn n) (Ring.inverse (ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x) ∘L ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ (fderiv ℝ ψ) x v).toLinearMap := by
  intro n N V ψ hV hψ hinj
  -- `G = A* A` is `C¹` on `V` with `DG(x)[v] = A* S_v + S_v* A`, and `det` is `C¹` with
  -- `D det(T)[H] = det T · tr(T⁻¹ H)` at every unit `T` (Jacobi's formula).
  obtain ⟨hGC, hGD⟩ := Submission.adjoint_comp_fderiv_contDiffOn_fderiv_eq_add n N V ψ hV hψ
  obtain ⟨hdetC, hdetD⟩ := Submission.continuousLinearMap_det_contDiff_fderiv_eq_mul_trace n
  -- Step 1: `J = √(det ∘ G)`.
  have hJ : Chapter02.areaJacobianAt ψ = fun x ↦
      Real.sqrt (ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x).det :=
    funext fun x ↦ Chapter02.areaJacobianAt_eq_sqrt_det_adjoint_comp ψ x
  -- Step 2: on `V`, `A(x)` is injective, so `J x = normDet A(x) ≠ 0` and `det G(x) = (J x)² ≠ 0`.
  have hJ0 : ∀ x ∈ V, Chapter02.areaJacobianAt ψ x ≠ 0 := fun x hx ↦ by
    rw [Chapter02.areaJacobianAt_eq_normDet]
    exact ((fderiv ℝ ψ x).toLinearMap.normDet_ne_zero_tfae.out 1 5).2 (hinj x hx)
  have hd0 : ∀ x ∈ V, (ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x).det ≠ 0 :=
    fun x hx ↦ Chapter02.areaJacobianAt_sq_eq_det_adjoint_comp ψ x ▸ pow_ne_zero 2 (hJ0 x hx)
  refine ⟨?_, fun x hx v ↦ ?_⟩
  · -- Step 6: `√(det ∘ G)` is `C¹` on `V`, as `det ∘ G` is `C¹` and nonvanishing there.
    rw [hJ]
    exact (hdetC.comp_contDiffOn hGC).sqrt hd0
  · -- Steps 4 and 7: the chain rule for `√(det ∘ G)` at `x`.
    have hGx := ((hGC.differentiableOn one_ne_zero x hx).differentiableAt
      (hV.mem_nhds hx)).hasFDerivAt
    have hdetx := ((hdetC.differentiable one_ne_zero)
      (ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x)).hasFDerivAt
    have hc := hdetx.comp x hGx
    have hJx : HasFDerivAt (fun y ↦
        Real.sqrt (ContinuousLinearMap.adjoint (fderiv ℝ ψ y) ∘L fderiv ℝ ψ y).det) _ x :=
      hc.sqrt (hd0 x hx)
    rw [← hJ] at hJx
    -- Step 5: `G(x)` is a unit with symmetric inverse (`gram_projection`), so the two traces in
    -- `tr(G⁻¹ (A* S_v + S_v* A))` agree (`trace_swap`).
    obtain ⟨hunit, hsymm, -⟩ := Submission.gram_inverse_range_starProjection n N
      (LinearMap.range (fderiv ℝ ψ x).toLinearMap) (fderiv ℝ ψ x) (hinj x hx) rfl
    rw [hJx.fderiv, smul_apply, ContinuousLinearMap.comp_apply, hGD x hx v, hdetD _ _ hunit,
      ContinuousLinearMap.comp_add, ContinuousLinearMap.toLinearMap_add, map_add,
      Submission.trace_comp_adjoint_comp_swap_of_symm n N (fderiv ℝ ψ x)
        (fderiv ℝ (fderiv ℝ ψ) x v) _ hsymm, Function.comp_apply,
      ← Chapter02.areaJacobianAt_eq_sqrt_det_adjoint_comp ψ x,
      ← Chapter02.areaJacobianAt_sq_eq_det_adjoint_comp ψ x, smul_eq_mul]
    field_simp [hJ0 x hx]
    ring
/-- **`C¹` regularity of the tangential coefficient field.** Let `V ⊆ ℝⁿ` be open, `ψ : ℝⁿ → ℝᴺ`
`C²` on `V` with `A(x) = Dψ(x)` injective for `x ∈ V`, and `u : ℝⁿ → ℝᴺ` `C¹` on `V`. Then
`a(x) = G(x)⁻¹ (A(x)* u(x))`, `G = A* ∘ A`, is `C¹` on `V`. `A` is `C¹` because `ψ` is `C²` on the
open set `V`. Over `ℝ` the adjoint is a continuous linear map, so `A*` is `C¹`, and `G` is `C¹`
because composition is continuous bilinear. Each `G(x)` is a unit
(`gram_inverse_range_starProjection` with `K = range A(x)`) and `Ring.inverse` is smooth at units,
so `G⁻¹` is `C¹`. Evaluation is continuous bilinear, which gives `a`. -/
theorem Submission.chart_tangential_coefficient_contDiffOn : ∀ (n N : ℕ) (V : Set (Rn n)) (ψ : Rn n → Rn N) (u : Rn n → Rn N), IsOpen V → ContDiffOn ℝ 2 ψ V → (∀ x ∈ V, Function.Injective (fderiv ℝ ψ x)) → ContDiffOn ℝ 1 u V → ContDiffOn ℝ 1 (fun x ↦ Ring.inverse (ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x) (ContinuousLinearMap.adjoint (fderiv ℝ ψ x) (u x))) V := by
  intro n N V ψ u hV hψ hinj hu
  -- Step 1: `A = Dψ` is `C¹` on `V`.
  have hA : ContDiffOn ℝ 1 (fderiv ℝ ψ) V := hψ.fderiv_of_isOpen hV (by norm_num)
  -- Step 2: `x ↦ A(x)*` is `C¹` on `V`; over `ℝ` the adjoint is a continuous linear map `adjR`.
  have hAs : ContDiffOn ℝ 1 (fun x ↦ ContinuousLinearMap.adjoint (fderiv ℝ ψ x)) V := by
    let adjR : (Rn n →L[ℝ] Rn N) →L[ℝ] Rn N →L[ℝ] Rn n :=
      (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Rn n) (F := Rn N)).toContinuousLinearEquiv
        |>.toContinuousLinearMap
    exact adjR.contDiff.comp_contDiffOn hA
  -- Step 3: `G = A* ∘ A` is `C¹` on `V`.
  have hG : ContDiffOn ℝ 1 (fun x ↦ ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x) V :=
    hAs.clm_comp hA
  -- Steps 4-5: each `G(x)`, `x ∈ V`, is a unit and `Ring.inverse` is smooth at units.
  have hGi : ContDiffOn ℝ 1
      (fun x ↦ Ring.inverse (ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x)) V := by
    intro x hx
    obtain ⟨U, hU⟩ := (Submission.gram_inverse_range_starProjection n N
      (LinearMap.range (fderiv ℝ ψ x).toLinearMap) (fderiv ℝ ψ x) (hinj x hx) rfl).1
    have hinv : ContDiffAt ℝ 1 Ring.inverse
        (ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x) :=
      hU ▸ contDiffAt_ringInverse ℝ U
    exact (hinv.comp x (hG.contDiffAt (hV.mem_nhds hx))).contDiffWithinAt
  -- Step 6: `a = G⁻¹ (A* u)` is `C¹` on `V`.
  exact hGi.clm_apply (hAs.clm_apply hu)
/-- **Symmetry of the second derivative (Schwarz).** If `ψ : ℝⁿ → ℝᴺ` is `C²` on an open set `V`,
then `D²ψ(x)[v, w] = D²ψ(x)[w, v]` for `x ∈ V`. Mathlib's `ContDiffAt.isSymmSndFDerivAt` is in
`Mathlib.Analysis.Calculus.FDeriv.Symmetric`, which the frozen header does not import, so this is
the classical second-difference proof. For `ε > 0` take `δ` with `B_δ(x) ⊆ V` and
`‖D²ψ(z) - D²ψ(x)‖ < ε` on `B_δ(x)`. For `‖a‖ + ‖b‖ < δ`, two applications of the mean value
inequality on `[0, 1]` give
`‖ψ(x + a + b) - ψ(x + a) - ψ(x + b) + ψ(x) - D²ψ(x)[a, b]‖ ≤ ε ‖a‖ ‖b‖`. The second difference
is symmetric in `(a, b)`. With `a = t v`, `b = t w` this gives
`‖D²ψ(x)[v, w] - D²ψ(x)[w, v]‖ ≤ 2 ε ‖v‖ ‖w‖` for every `ε > 0`. -/
theorem Submission.fderiv_fderiv_symm_of_contDiffOn_two : ∀ (n N : ℕ) (V : Set (Rn n)) (ψ : Rn n → Rn N), IsOpen V → ContDiffOn ℝ 2 ψ V → ∀ x ∈ V, ∀ v w : Rn n, fderiv ℝ (fderiv ℝ ψ) x v w = fderiv ℝ (fderiv ℝ ψ) x w v := by
  intro n N V ψ hV hψ x hx v w
  -- Step 1: `Dψ` is `C¹` on `V`, `D²ψ` is continuous on `V`, and `ψ`, `Dψ` are differentiable at
  -- every point of `V`.
  have hD : ContDiffOn ℝ 1 (fderiv ℝ ψ) V := hψ.fderiv_of_isOpen hV (by norm_num)
  have hD2 : ContinuousOn (fderiv ℝ (fderiv ℝ ψ)) V := hD.continuousOn_fderiv_of_isOpen hV le_rfl
  have hψd : ∀ z ∈ V, HasFDerivAt ψ (fderiv ℝ ψ z) z := fun z hz ↦
    ((hψ.differentiableOn (by norm_num)) z hz).differentiableAt (hV.mem_nhds hz) |>.hasFDerivAt
  have hDd : ∀ z ∈ V, HasFDerivAt (fderiv ℝ ψ) (fderiv ℝ (fderiv ℝ ψ) z) z := fun z hz ↦
    ((hD.differentiableOn (by norm_num)) z hz).differentiableAt (hV.mem_nhds hz) |>.hasFDerivAt
  -- Steps 2-5: `‖D²ψ(x)[v, w] - D²ψ(x)[w, v]‖ ≤ 2 ε ‖v‖ ‖w‖` for every `ε > 0`.
  have hbound : ∀ ε : ℝ, 0 < ε → ‖fderiv ℝ (fderiv ℝ ψ) x v w - fderiv ℝ (fderiv ℝ ψ) x w v‖ ≤
      2 * ε * ‖v‖ * ‖w‖ := by
    intro ε hε
    -- Step 2: `B_δ(x) ⊆ V` and `‖D²ψ(z) - D²ψ(x)‖ < ε` for `z ∈ B_δ(x)`.
    have hnhds : V ∩ fderiv ℝ (fderiv ℝ ψ) ⁻¹' ball (fderiv ℝ (fderiv ℝ ψ) x) ε ∈ 𝓝 x :=
      inter_mem (hV.mem_nhds hx)
        ((hD2.continuousAt (hV.mem_nhds hx)).preimage_mem_nhds
          (ball_mem_nhds (fderiv ℝ (fderiv ℝ ψ) x) hε))
    obtain ⟨δ, hδ, hδV⟩ := Metric.mem_nhds_iff.mp hnhds
    -- Steps 3-4: for `‖a‖ + ‖b‖ < δ`, the second difference is `D²ψ(x)[a, b]` up to `ε ‖a‖ ‖b‖`.
    have key : ∀ a b : Rn n, ‖a‖ + ‖b‖ < δ →
        ‖ψ (x + a + b) - ψ (x + a) - ψ (x + b) + ψ x - fderiv ℝ (fderiv ℝ ψ) x a b‖ ≤
          ε * ‖a‖ * ‖b‖ := by
      intro a b hab
      have hmem : ∀ r s : ℝ, r ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
          x + r • a + s • b ∈ ball x δ := by
        intro r s hr hs
        rw [mem_ball, dist_eq_norm, add_assoc, add_sub_cancel_left]
        calc ‖r • a + s • b‖ ≤ ‖r • a‖ + ‖s • b‖ := norm_add_le _ _
          _ = r * ‖a‖ + s * ‖b‖ := by
            rw [norm_smul, norm_smul, Real.norm_of_nonneg hr.1, Real.norm_of_nonneg hs.1]
          _ ≤ ‖a‖ + ‖b‖ := add_le_add (mul_le_of_le_one_left (norm_nonneg a) hr.2)
            (mul_le_of_le_one_left (norm_nonneg b) hs.2)
          _ < δ := hab
      have hV' : ∀ r s : ℝ, r ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → x + r • a + s • b ∈ V :=
        fun r s hr hs ↦ (hδV (hmem r s hr hs)).1
      have hclose : ∀ r s : ℝ, r ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
          ‖fderiv ℝ (fderiv ℝ ψ) (x + r • a + s • b) - fderiv ℝ (fderiv ℝ ψ) x‖ < ε := by
        intro r s hr hs
        have h := (hδV (hmem r s hr hs)).2
        rw [mem_preimage, mem_ball] at h
        exact (dist_eq_norm (fderiv ℝ (fderiv ℝ ψ) (x + r • a + s • b))
          (fderiv ℝ (fderiv ℝ ψ) x)).symm.trans_lt h
      -- Step 3 (inner estimate): mean value inequality for
      -- `k(r) = Dψ(x + r a + s b) b - r D²ψ(x)[a, b]`. Its derivative is
      -- `k'(r) = (D²ψ(x + r a + s b) - D²ψ(x))[a, b]`.
      have inner : ∀ s ∈ Icc (0 : ℝ) 1, ‖fderiv ℝ ψ (x + a + s • b) b - fderiv ℝ ψ (x + s • b) b -
          fderiv ℝ (fderiv ℝ ψ) x a b‖ ≤ ε * ‖a‖ * ‖b‖ := by
        intro s hs
        have hk : ∀ r ∈ Icc (0 : ℝ) 1, HasDerivWithinAt
            (fun r : ℝ ↦ fderiv ℝ ψ (x + r • a + s • b) b - r • fderiv ℝ (fderiv ℝ ψ) x a b)
            (fderiv ℝ (fderiv ℝ ψ) (x + r • a + s • b) a b - fderiv ℝ (fderiv ℝ ψ) x a b)
            (Icc (0 : ℝ) 1) r := by
          intro r hr
          have hγ : HasDerivAt (fun r : ℝ ↦ x + r • a + s • b) a r := by
            simpa using (((hasDerivAt_id r).smul_const a).const_add x).add_const (s • b)
          have h1 : HasDerivAt (fun r : ℝ ↦ fderiv ℝ ψ (x + r • a + s • b))
              (fderiv ℝ (fderiv ℝ ψ) (x + r • a + s • b) a) r :=
            (hDd _ (hV' r s hr hs)).comp_hasDerivAt r hγ
          have h2 := (h1.clm_apply (hasDerivAt_const r b)).sub
            ((hasDerivAt_id r).smul_const (fderiv ℝ (fderiv ℝ ψ) x a b))
          simp only [id_eq, map_zero, add_zero, one_smul] at h2
          exact h2.hasDerivWithinAt
        have hb : ∀ r ∈ Ico (0 : ℝ) 1, ‖fderiv ℝ (fderiv ℝ ψ) (x + r • a + s • b) a b -
            fderiv ℝ (fderiv ℝ ψ) x a b‖ ≤ ε * ‖a‖ * ‖b‖ := by
          intro r hr
          calc ‖fderiv ℝ (fderiv ℝ ψ) (x + r • a + s • b) a b - fderiv ℝ (fderiv ℝ ψ) x a b‖
              = ‖(fderiv ℝ (fderiv ℝ ψ) (x + r • a + s • b) - fderiv ℝ (fderiv ℝ ψ) x) a b‖ := by
                rw [sub_apply, sub_apply]
            _ ≤ ‖fderiv ℝ (fderiv ℝ ψ) (x + r • a + s • b) - fderiv ℝ (fderiv ℝ ψ) x‖ * ‖a‖ * ‖b‖ :=
                ContinuousLinearMap.le_opNorm₂ _ _ _
            _ ≤ ε * ‖a‖ * ‖b‖ := by
                gcongr
                exact (hclose r s (Ico_subset_Icc_self hr) hs).le
        have hfin := norm_image_sub_le_of_norm_deriv_le_segment_01' hk hb
        simp only [one_smul, zero_smul, add_zero, sub_zero] at hfin
        calc ‖fderiv ℝ ψ (x + a + s • b) b - fderiv ℝ ψ (x + s • b) b - fderiv ℝ (fderiv ℝ ψ) x a b‖
            = ‖fderiv ℝ ψ (x + a + s • b) b - fderiv ℝ (fderiv ℝ ψ) x a b -
                fderiv ℝ ψ (x + s • b) b‖ := by rw [sub_right_comm]
          _ ≤ ε * ‖a‖ * ‖b‖ := hfin
      -- Step 4 (outer estimate): mean value inequality for
      -- `g(s) = ψ(x + a + s b) - ψ(x + s b) - s D²ψ(x)[a, b]`. `inner` bounds its derivative.
      have hg : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt
          (fun s : ℝ ↦ ψ (x + a + s • b) - ψ (x + s • b) - s • fderiv ℝ (fderiv ℝ ψ) x a b)
          (fderiv ℝ ψ (x + a + s • b) b - fderiv ℝ ψ (x + s • b) b - fderiv ℝ (fderiv ℝ ψ) x a b)
          (Icc (0 : ℝ) 1) s := by
        intro s hs
        have hγ1 : HasDerivAt (fun s : ℝ ↦ x + a + s • b) b s := by
          simpa using ((hasDerivAt_id s).smul_const b).const_add (x + a)
        have hγ0 : HasDerivAt (fun s : ℝ ↦ x + s • b) b s := by
          simpa using ((hasDerivAt_id s).smul_const b).const_add x
        have hm1 : x + a + s • b ∈ V := by
          simpa using hV' 1 s (right_mem_Icc.2 zero_le_one) hs
        have hm0 : x + s • b ∈ V := by
          simpa using hV' 0 s (left_mem_Icc.2 zero_le_one) hs
        have h1 : HasDerivAt (fun s : ℝ ↦ ψ (x + a + s • b)) (fderiv ℝ ψ (x + a + s • b) b) s :=
          (hψd _ hm1).comp_hasDerivAt s hγ1
        have h0 : HasDerivAt (fun s : ℝ ↦ ψ (x + s • b)) (fderiv ℝ ψ (x + s • b) b) s :=
          (hψd _ hm0).comp_hasDerivAt s hγ0
        have h2 := (h1.sub h0).sub ((hasDerivAt_id s).smul_const (fderiv ℝ (fderiv ℝ ψ) x a b))
        simp only [id_eq, one_smul] at h2
        exact h2.hasDerivWithinAt
      have hfin := norm_image_sub_le_of_norm_deriv_le_segment_01' hg
        (fun s hs ↦ inner s (Ico_subset_Icc_self hs))
      simp only [one_smul, zero_smul, add_zero, sub_zero] at hfin
      calc ‖ψ (x + a + b) - ψ (x + a) - ψ (x + b) + ψ x - fderiv ℝ (fderiv ℝ ψ) x a b‖
          = ‖ψ (x + a + b) - ψ (x + b) - fderiv ℝ (fderiv ℝ ψ) x a b - (ψ (x + a) - ψ x)‖ := by
            congr 1
            abel
        _ ≤ ε * ‖a‖ * ‖b‖ := hfin
    -- Step 5: apply `key` to `(t v, t w)` and `(t w, t v)` with `t = δ / (‖v‖ + ‖w‖ + 1)`.
    obtain ⟨t, ht0, hsum⟩ : ∃ t : ℝ, 0 < t ∧ ‖t • v‖ + ‖t • w‖ < δ := by
      have hS : 0 < ‖v‖ + ‖w‖ + 1 := by positivity
      refine ⟨δ / (‖v‖ + ‖w‖ + 1), div_pos hδ hS, ?_⟩
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (div_pos hδ hS).le, ← mul_add,
        div_mul_eq_mul_div, div_lt_iff₀ hS]
      nlinarith [norm_nonneg v, norm_nonneg w]
    have k1 := key (t • v) (t • w) hsum
    have k2 := key (t • w) (t • v) (by rw [add_comm]; exact hsum)
    have hsmul : ∀ a b : Rn n, fderiv ℝ (fderiv ℝ ψ) x (t • a) (t • b) =
        (t * t) • fderiv ℝ (fderiv ℝ ψ) x a b := by
      intro a b
      rw [map_smul, map_smul, smul_apply, smul_smul]
    rw [hsmul, norm_smul, norm_smul, Real.norm_of_nonneg ht0.le] at k1 k2
    rw [add_right_comm x (t • w) (t • v)] at k2
    -- Step 6: the second difference is symmetric; cancel `t² > 0`.
    have h3 : t * t * ‖fderiv ℝ (fderiv ℝ ψ) x v w - fderiv ℝ (fderiv ℝ ψ) x w v‖ ≤
        t * t * (2 * ε * ‖v‖ * ‖w‖) := by
      calc t * t * ‖fderiv ℝ (fderiv ℝ ψ) x v w - fderiv ℝ (fderiv ℝ ψ) x w v‖
          = ‖(t * t) • (fderiv ℝ (fderiv ℝ ψ) x v w - fderiv ℝ (fderiv ℝ ψ) x w v)‖ := by
            rw [norm_smul, Real.norm_of_nonneg (mul_self_nonneg t)]
        _ = ‖(ψ (x + t • v + t • w) - ψ (x + t • w) - ψ (x + t • v) + ψ x -
              (t * t) • fderiv ℝ (fderiv ℝ ψ) x w v) -
            (ψ (x + t • v + t • w) - ψ (x + t • v) - ψ (x + t • w) + ψ x -
              (t * t) • fderiv ℝ (fderiv ℝ ψ) x v w)‖ := by
            rw [smul_sub]
            congr 1
            abel
        _ ≤ ‖ψ (x + t • v + t • w) - ψ (x + t • w) - ψ (x + t • v) + ψ x -
              (t * t) • fderiv ℝ (fderiv ℝ ψ) x w v‖ +
            ‖ψ (x + t • v + t • w) - ψ (x + t • v) - ψ (x + t • w) + ψ x -
              (t * t) • fderiv ℝ (fderiv ℝ ψ) x v w‖ := norm_sub_le _ _
        _ ≤ ε * (t * ‖w‖) * (t * ‖v‖) + ε * (t * ‖v‖) * (t * ‖w‖) := add_le_add k2 k1
        _ = t * t * (2 * ε * ‖v‖ * ‖w‖) := by ring
    exact le_of_mul_le_mul_left h3 (mul_pos ht0 ht0)
  -- Conclusion: `‖D²ψ(x)[v, w] - D²ψ(x)[w, v]‖ ≤ ε` for every `ε > 0`, so it vanishes.
  have hzero : ‖fderiv ℝ (fderiv ℝ ψ) x v w - fderiv ℝ (fderiv ℝ ψ) x w v‖ ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    have hK : 0 < 2 * ‖v‖ * ‖w‖ + 1 := by positivity
    calc ‖fderiv ℝ (fderiv ℝ ψ) x v w - fderiv ℝ (fderiv ℝ ψ) x w v‖
        ≤ 2 * (ε / (2 * ‖v‖ * ‖w‖ + 1)) * ‖v‖ * ‖w‖ := hbound _ (div_pos hε hK)
      _ = ε * (2 * ‖v‖ * ‖w‖ / (2 * ‖v‖ * ‖w‖ + 1)) := by ring
      _ ≤ ε * 1 := by
          gcongr
          rw [div_le_one hK]
          linarith
      _ = 0 + ε := by ring
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hzero)

/-- **Trace identity for the tangential coefficient field** (product-rule core of the chart
divergence formula). Put `A(y) = Dψ(y)`, `G(y) = A(y)* A(y)` and `a = G⁻¹ A* u`; fix `x ∈ V` and
write `A = A(x)`, `S = D²ψ(x)` and `p = u(x) - A a(x)`. By `gram_inverse_range_starProjection`
each `G(y)`, `y ∈ V`, is a unit, so `A(y)* (u(y) - A(y) a(y)) = 0` on `V`. Hence for every `c` the
function `y ↦ ⟪A(y) c, u(y) - A(y) a(y)⟫ = ⟪c, A(y)* (u(y) - A(y) a(y))⟫` vanishes near `x`, and
the product rule at `x` (`a` is `C¹` by `chart_tangential_coefficient_contDiffOn`) gives
`⟪A c, Du(x) v - A Da(x) v - S v a(x)⟫ + ⟪S v c, p⟫ = 0` for all `c, v`. For any `e` take
`c = G⁻¹ e`, so `A* A c = e`; with the symmetry of `G⁻¹` (`gram_inverse_range_starProjection`)
and `S v a(x) = S a(x) v` (`fderiv_fderiv_symm_of_contDiffOn_two`) this becomes
`⟪e, Da(x) e⟫ + ⟪e, G⁻¹ A* S(a(x)) e⟫ = ⟪e, G⁻¹ A* Du(x) e⟫ + ⟪p, S e (G⁻¹ e)⟫`. Summing over the
standard orthonormal basis `e_l` (`LinearMap.trace_eq_sum_inner`) gives the identity. -/
theorem Submission.chart_tangential_coefficient_trace_identity : ∀ (n N : ℕ) (V : Set (Rn n)) (ψ : Rn n → Rn N) (u : Rn n → Rn N), IsOpen V → ContDiffOn ℝ 2 ψ V → (∀ x ∈ V, Function.Injective (fderiv ℝ ψ x)) → ContDiffOn ℝ 1 u V → let a : Rn n → Rn n := fun x ↦ Ring.inverse (ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x) (ContinuousLinearMap.adjoint (fderiv ℝ ψ x) (u x)); ∀ x ∈ V, LinearMap.trace ℝ (Rn n) (fderiv ℝ a x).toLinearMap + LinearMap.trace ℝ (Rn n) (Ring.inverse (ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x) ∘L ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ (fderiv ℝ ψ) x (a x)).toLinearMap = LinearMap.trace ℝ (Rn n) (Ring.inverse (ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x) ∘L ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ u x).toLinearMap + inner ℝ (u x - fderiv ℝ ψ x (a x)) (∑ l : Fin n, fderiv ℝ (fderiv ℝ ψ) x (EuclideanSpace.single l 1) (Ring.inverse (ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x) (EuclideanSpace.single l 1))) := by
  intro n N V ψ u hV hψ hinj hu a x hx
  -- Step 1: `Dψ`, `u` and `a` are differentiable at `x`, and `S = D²ψ(x)` is symmetric.
  have hxV : V ∈ 𝓝 x := hV.mem_nhds hx
  have hA : HasFDerivAt (fderiv ℝ ψ) (fderiv ℝ (fderiv ℝ ψ) x) x :=
    (((hψ.fderiv_of_isOpen hV (m := 1) (by norm_num)).contDiffAt hxV).differentiableAt
      one_ne_zero).hasFDerivAt
  have hu' : HasFDerivAt u (fderiv ℝ u x) x :=
    ((hu.contDiffAt hxV).differentiableAt one_ne_zero).hasFDerivAt
  have ha' : HasFDerivAt a (fderiv ℝ a x) x :=
    (((Submission.chart_tangential_coefficient_contDiffOn n N V ψ u hV hψ hinj hu).contDiffAt
      hxV).differentiableAt one_ne_zero).hasFDerivAt
  have hS := Submission.fderiv_fderiv_symm_of_contDiffOn_two n N V ψ hV hψ x hx
  -- Step 2: `G(y) G(y)⁻¹ = 1` for `y ∈ V`, so `A(y)* (A(y) a(y)) = A(y)* u(y)` there.
  have hGG : ∀ y ∈ V, ∀ w : Rn n, ContinuousLinearMap.adjoint (fderiv ℝ ψ y) (fderiv ℝ ψ y
      (Ring.inverse (ContinuousLinearMap.adjoint (fderiv ℝ ψ y) ∘L fderiv ℝ ψ y) w)) = w :=
    fun y hy w ↦ congrArg (fun T : Rn n →L[ℝ] Rn n ↦ T w) (Ring.mul_inverse_cancel _
      (Submission.gram_inverse_range_starProjection n N _ (fderiv ℝ ψ y) (hinj y hy) rfl).1)
  have hGa : ∀ y ∈ V, ContinuousLinearMap.adjoint (fderiv ℝ ψ y) (fderiv ℝ ψ y (a y)) =
      ContinuousLinearMap.adjoint (fderiv ℝ ψ y) (u y) := fun y hy ↦ hGG y hy _
  -- Step 3: `y ↦ ⟪A(y) c, u y - A(y) (a y)⟫` vanishes on `V`; its derivative at `x` in direction
  -- `v` is `⟪A c, Du v - (A Da v + S v a)⟫ + ⟪S v c, u - A a⟫`, which is therefore `0`.
  have hkey : ∀ c v : Rn n, inner ℝ (fderiv ℝ ψ x c) (fderiv ℝ u x v -
      (fderiv ℝ ψ x (fderiv ℝ a x v) + fderiv ℝ (fderiv ℝ ψ) x v (a x))) +
      inner ℝ (fderiv ℝ (fderiv ℝ ψ) x v c) (u x - fderiv ℝ ψ x (a x)) = 0 := by
    intro c v
    have hF := (hA.clm_apply (hasFDerivAt_const c x)).inner ℝ (hu'.sub (hA.clm_apply ha'))
    have hF0 : HasFDerivAt (fun y ↦ inner ℝ (fderiv ℝ ψ y c) (u y - fderiv ℝ ψ y (a y)))
        (0 : Rn n →L[ℝ] ℝ) x := by
      refine (hasFDerivAt_const (0 : ℝ) x).congr_of_eventuallyEq ?_
      filter_upwards [hxV] with y hy
      rw [← ContinuousLinearMap.adjoint_inner_right, map_sub, hGa y hy, sub_self,
        inner_zero_right]
    have h := congrArg (fun L : Rn n →L[ℝ] ℝ ↦ L v) (hF.unique hF0)
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      fderivInnerCLM_apply, add_apply, sub_apply, Pi.sub_apply, ContinuousLinearMap.flip_apply,
      zero_apply, map_zero, zero_add] using h
  -- Step 4: for every `e`, with `c = G⁻¹ e` (so `A* A c = e`) and `G⁻¹` symmetric,
  -- `⟪e, Da e⟫ + ⟪e, G⁻¹ A* S(a) e⟫ = ⟪e, G⁻¹ A* Du e⟫ + ⟪u - A a, S e c⟫`.
  obtain ⟨-, hsym, -⟩ :=
    Submission.gram_inverse_range_starProjection n N _ (fderiv ℝ ψ x) (hinj x hx) rfl
  have hterm : ∀ e : Rn n, inner ℝ e (fderiv ℝ a x e) + inner ℝ e ((Ring.inverse
      (ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x) ∘L
      ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ (fderiv ℝ ψ) x (a x)) e) =
      inner ℝ e ((Ring.inverse (ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x) ∘L
        ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ u x) e) +
      inner ℝ (u x - fderiv ℝ ψ x (a x)) (fderiv ℝ (fderiv ℝ ψ) x e (Ring.inverse
        (ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x) e)) := by
    intro e
    have hk :=
      hkey (Ring.inverse (ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x) e) e
    rw [inner_sub_right (fderiv ℝ ψ x _), inner_add_right (fderiv ℝ ψ x _), hS e (a x),
      ← ContinuousLinearMap.adjoint_inner_left (fderiv ℝ ψ x) (fderiv ℝ a x e), hGG x hx,
      real_inner_comm (u x - fderiv ℝ ψ x (a x))] at hk
    simp only [ContinuousLinearMap.comp_apply]
    rw [← hsym e, ← hsym e, ContinuousLinearMap.adjoint_inner_right,
      ContinuousLinearMap.adjoint_inner_right]
    linarith
  -- Step 5: compute the three traces in the standard orthonormal basis `e_l` and sum.
  have htr : ∀ T : Rn n →L[ℝ] Rn n, LinearMap.trace ℝ (Rn n) T.toLinearMap =
      ∑ l : Fin n, inner ℝ (EuclideanSpace.single l (1 : ℝ) : Rn n)
        (T (EuclideanSpace.single l 1)) := by
    intro T
    rw [LinearMap.trace_eq_sum_inner T.toLinearMap (EuclideanSpace.basisFun (Fin n) ℝ)]
    simp only [EuclideanSpace.basisFun_apply, ContinuousLinearMap.coe_coe]
  rw [htr, htr, htr, inner_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun l _ ↦ hterm _
/-- **Differentiability of the projection onto the range.** For an injective `A : ℝⁿ →L[ℝ] ℝᴺ`,
the map `B ↦ (range B).starProjection` (the orthogonal projection of `ℝᴺ` onto the range of `B`) is
Fréchet differentiable at `A`. The Gram operator `G(B) = B† ∘ B` is injective at `A`
(`adjoint_comp_self_injective_iff`), hence a unit (finite dimension), hence a unit near `A`
(`Units.isOpen`). There the projection equals `B ∘ G(B)⁻¹ ∘ B†`
(`eq_starProjection_of_mem_of_inner_eq_zero`), and that map is differentiable at `A`
(`DifferentiableAt.clm_comp`, `DifferentiableAt.inverse`). -/
theorem Submission.sff_range_starProjection_differentiableAt : ∀ (n N : ℕ) (A : Rn n →L[ℝ] Rn N), Function.Injective A → DifferentiableAt ℝ (fun B : Rn n →L[ℝ] Rn N ↦ (LinearMap.range B.toLinearMap).starProjection) A := by
  intro n N A hA
  -- Step 1: the adjoint `B ↦ B†` as a continuous `ℝ`-linear map (Mathlib bundles `adjoint` as a
  -- conjugate-linear isometry, and conjugation is trivial on `ℝ`).
  let adj : (Rn n →L[ℝ] Rn N) →L[ℝ] (Rn N →L[ℝ] Rn n) :=
    { toFun := fun B ↦ ContinuousLinearMap.adjoint B
      map_add' := fun B C ↦ by simp
      map_smul' := fun c B ↦ by simp
      cont := ContinuousLinearMap.adjoint.continuous }
  have hadj : ∀ B, adj B = ContinuousLinearMap.adjoint B := fun _ ↦ rfl
  -- The Gram operator `G(B) = B† ∘ B`.
  let G : (Rn n →L[ℝ] Rn N) → (Rn n →L[ℝ] Rn n) := fun B ↦ (adj B).comp B
  -- Step 2: `G(A)` is injective, hence bijective in finite dimension, hence a unit.
  have hGA : IsUnit (G A) := by
    have hinj : Function.Injective (G A) :=
      (ContinuousLinearMap.adjoint_comp_self_injective_iff A).2 hA
    exact ContinuousLinearMap.isUnit_iff_bijective.2
      ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩
  -- Step 3: `G(B)` stays a unit for `B` near `A`.
  have hS : ∀ᶠ B in 𝓝 A, IsUnit (G B) :=
    (adj.continuous.clm_comp continuous_id).continuousAt.eventually (Units.isOpen.mem_nhds hGA)
  -- Step 4: where `G(B)` is a unit, the projection onto `range B` is `B ∘ G(B)⁻¹ ∘ B†`.
  have hformula : ∀ B : Rn n →L[ℝ] Rn N, IsUnit (G B) →
      (LinearMap.range B.toLinearMap).starProjection =
        B.comp ((Ring.inverse (G B)).comp (adj B)) := by
    intro B hB
    -- `B† (B (G(B)⁻¹ (B† w))) = B† w`, from `G(B) * G(B)⁻¹ = 1`.
    have hcancel : ∀ w, adj B (B (Ring.inverse (G B) (adj B w))) = adj B w := fun w ↦ by
      simpa [G] using
        congrArg (fun T : Rn n →L[ℝ] Rn n ↦ T (adj B w)) (Ring.mul_inverse_cancel _ hB)
    ext1 w
    -- `p = B (G(B)⁻¹ (B† w))` lies in `range B`, and `w - p ⊥ B v` because `B† (w - p) = 0`.
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (LinearMap.mem_range_self _ _) ?_
    rintro u ⟨v, rfl⟩
    rw [ContinuousLinearMap.coe_coe, ← ContinuousLinearMap.adjoint_inner_left]
    simp only [ContinuousLinearMap.comp_apply, map_sub]
    rw [← hadj, hcancel, sub_self, inner_zero_left]
  -- Step 5: `B ↦ B ∘ G(B)⁻¹ ∘ B†` is differentiable at `A`.
  have hdiff : DifferentiableAt ℝ
      (fun B : Rn n →L[ℝ] Rn N ↦ B.comp ((Ring.inverse (G B)).comp (adj B))) A :=
    differentiableAt_id.clm_comp
      (((adj.differentiableAt.clm_comp differentiableAt_id).inverse hGA).clm_comp
        adj.differentiableAt)
  -- Step 6: the two maps agree near `A`.
  exact hdiff.congr_of_eventuallyEq (hS.mono fun B hB ↦ hformula B hB)
/-- **Local left inverse of an immersion.** If `ψ : ℝⁿ → ℝᴺ` is `C¹` at `x₀` and `Dψ(x₀)` is
injective, then some `g : ℝᴺ → ℝⁿ` is differentiable at `ψ(x₀)` and satisfies `g(ψ(x)) = x` near
`x₀`. `Dψ(x₀)` has a linear left inverse `L`, which is continuous because `ℝᴺ` is
finite-dimensional. So `L ∘ ψ` has strict derivative `L ∘ Dψ(x₀) = id` at `x₀`. The inverse function
theorem gives a local inverse `k` of `L ∘ ψ` that is differentiable at `L(ψ(x₀))`, and
`g = k ∘ L` works. -/
theorem Submission.sff_immersion_local_left_inverse : ∀ (n N : ℕ) (ψ : Rn n → Rn N) (x₀ : Rn n), ContDiffAt ℝ 1 ψ x₀ → Function.Injective (fderiv ℝ ψ x₀) → ∃ g : Rn N → Rn n, DifferentiableAt ℝ g (ψ x₀) ∧ ∀ᶠ x in 𝓝 x₀, g (ψ x) = x := by
  intro n N ψ x₀ hψ hinj
  -- Step 1: a continuous linear left inverse `L` of `Dψ(x₀)`.
  obtain ⟨L₀, hL₀⟩ := (fderiv ℝ ψ x₀).toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hinj)
  let L : Rn N →L[ℝ] Rn n := LinearMap.toContinuousLinearMap L₀
  have hLA : L.comp (fderiv ℝ ψ x₀) = (ContinuousLinearEquiv.refl ℝ (Rn n) : Rn n →L[ℝ] Rn n) := by
    ext1 v
    exact LinearMap.congr_fun hL₀ v
  -- Step 2: `h = L ∘ ψ` has strict derivative `L ∘ Dψ(x₀) = id` at `x₀`.
  have hh : HasStrictFDerivAt (fun x ↦ L (ψ x))
      ((ContinuousLinearEquiv.refl ℝ (Rn n) : Rn n ≃L[ℝ] Rn n) : Rn n →L[ℝ] Rn n) x₀ := by
    rw [← hLA]
    exact L.hasStrictFDerivAt.comp x₀ (hψ.hasStrictFDerivAt one_ne_zero)
  -- Step 3: the inverse function theorem gives the local inverse `k = hh.localInverse` of `h`.
  refine ⟨fun y ↦ hh.localInverse _ _ _ (L y), ?_, ?_⟩
  · -- Step 4: `g = k ∘ L` is differentiable at `ψ(x₀)`, since `k` is at `L(ψ(x₀)) = h(x₀)`.
    exact hh.to_localInverse.differentiableAt.comp (ψ x₀) L.differentiableAt
  · -- Step 5: `g(ψ(x)) = k(h(x)) = x` near `x₀`.
    exact hh.eventually_left_inverse

/-- **Local differentiable extension of the tangent projection.** Let `ψ` be a `C²` Simon local
representation `V → W` of `M` with `T_{ψ x} M = range Dψ(x)` for `x ∈ V`, and let `x₀ ∈ V`. Write
`Π(B) = (range B).starProjection`. There is `Q` differentiable at `ψ x₀` with `P_z = Q(z)` for
`z ∈ M` near `ψ x₀` and `Q(ψ x) = Π(Dψ x)` for `x` near `x₀`. Take a left inverse `g` of `ψ` near
`x₀` that is differentiable at `ψ x₀` (`Submission.sff_immersion_local_left_inverse`) and
`Q = Π ∘ Dψ ∘ g`. `Q` is differentiable at `ψ x₀` by the chain rule
(`Submission.sff_range_starProjection_differentiableAt`, `ContDiffAt.fderiv_right`). By Simon 4.2
(from the relative properness of `ψ`), the points of `M` near `ψ x₀` are the `ψ x` with
`g (ψ x) = x`, where `Q (ψ x) = Π(Dψ x) = P_{ψ x}`. -/
theorem Submission.sff_tangentProjection_local_extension : ∀ (n N : ℕ) (M : Set (Rn N)) (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N), Chapter02.IsSimonLocalRepresentation 2 M V W ψ → (∀ x ∈ V, tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap) → ∀ x₀ ∈ V, ∃ Q : Rn N → (Rn N →L[ℝ] Rn N), DifferentiableAt ℝ Q (ψ x₀) ∧ tangentProjection M =ᶠ[𝓝[M] ψ x₀] Q ∧ ∀ᶠ x in 𝓝 x₀, Q (ψ x) = (LinearMap.range (fderiv ℝ ψ x).toLinearMap).starProjection := by
  intro n N M V W ψ hrep hT x₀ hx₀
  -- Step 1: `ψ` is `C²` at `x₀`, so `ψ` is `C¹` there and `Dψ` is differentiable at `x₀`.
  have h2 : ContDiffAt ℝ 2 ψ x₀ := hrep.contDiffOn.contDiffAt (hrep.isOpen_source.mem_nhds hx₀)
  have h1 : ContDiffAt ℝ 1 ψ x₀ := h2.of_le (by norm_num)
  have hA : DifferentiableAt ℝ (fderiv ℝ ψ) x₀ :=
    (h2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hinj : Function.Injective (fderiv ℝ ψ x₀) := hrep.injective_fderiv hx₀
  -- Step 2: a left inverse `g` of `ψ` on an open `U ∋ x₀`, differentiable at `ψ x₀`.
  obtain ⟨g, hg, hgψ⟩ := Submission.sff_immersion_local_left_inverse n N ψ x₀ h1 hinj
  obtain ⟨U, hUg, hUo, hxU⟩ := _root_.eventually_nhds_iff.mp hgψ
  have hgx₀ : g (ψ x₀) = x₀ := hUg x₀ hxU
  -- Step 3 (Simon 4.2): near `ψ x₀`, every point of `M` is `ψ x` with `x ∈ U ∩ V`. Take a compact
  -- neighbourhood `K ⊆ W` of `ψ x₀`. By relative properness `V ∩ ψ⁻¹ K` is compact, so
  -- `ψ ((V ∩ ψ⁻¹ K) \ U)` is compact, hence closed, and it misses `ψ x₀` since `ψ` is injective on `V`.
  have hy₀W : ψ x₀ ∈ W := by
    have h : ψ x₀ ∈ ψ '' V := ⟨x₀, hx₀, rfl⟩
    rw [hrep.image_eq] at h
    exact h.1
  obtain ⟨K, hKn, hKW, hK⟩ := local_compact_nhds (hrep.isOpen_target.mem_nhds hy₀W)
  have hcl : IsClosed (ψ '' ((V ∩ ψ ⁻¹' K) \ U)) :=
    (((hrep.isCompact_source_inter_preimage K hK hKW).diff hUo).image_of_continuousOn
      (hrep.contDiffOn.continuousOn.mono fun x hx ↦ hx.1.1)).isClosed
  have hy₀C : ψ x₀ ∉ ψ '' ((V ∩ ψ ⁻¹' K) \ U) := by
    rintro ⟨x, ⟨⟨hxV, -⟩, hxU'⟩, hx⟩
    rw [hrep.injOn hxV hx₀ hx] at hxU'
    exact hxU' hxU
  have hloc : ∀ᶠ z in 𝓝 (ψ x₀), z ∈ M → ∃ x ∈ U ∩ V, ψ x = z := by
    filter_upwards [hKn, hcl.isOpen_compl.mem_nhds hy₀C] with z hzK hzC hzM
    have hz : z ∈ ψ '' V := by rw [hrep.image_eq]; exact ⟨hKW hzK, hzM⟩
    obtain ⟨x, hxV, rfl⟩ := hz
    refine ⟨x, ⟨?_, hxV⟩, rfl⟩
    by_contra hxU'
    exact hzC ⟨x, ⟨⟨hxV, hzK⟩, hxU'⟩, rfl⟩
  -- Step 4: `Q = Π ∘ Dψ ∘ g` is differentiable at `ψ x₀` by the chain rule.
  let Pr : (Rn n →L[ℝ] Rn N) → (Rn N →L[ℝ] Rn N) :=
    fun B ↦ (LinearMap.range B.toLinearMap).starProjection
  refine ⟨fun z ↦ Pr (fderiv ℝ ψ (g z)), ?_, ?_, ?_⟩
  · have hPr : DifferentiableAt ℝ Pr (fderiv ℝ ψ (g (ψ x₀))) := by
      rw [hgx₀]; exact Submission.sff_range_starProjection_differentiableAt n N _ hinj
    have hAg : DifferentiableAt ℝ (fderiv ℝ ψ) (g (ψ x₀)) := by rw [hgx₀]; exact hA
    exact hPr.comp (ψ x₀) (hAg.comp (ψ x₀) hg)
  -- Step 5: each `z ∈ M` near `ψ x₀` is `ψ x` with `x ∈ U ∩ V`, so `Q z = Π(Dψ x) = P_z` by (T).
  · -- Equal subspaces have equal projections (`HasOrthogonalProjection` is a `Prop`).
    have key : ∀ K K' : Submodule ℝ (Rn N), K = K' → K.starProjection = K'.starProjection := by
      rintro K K' rfl; rfl
    rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
    filter_upwards [hloc] with z hz hzM
    obtain ⟨x, ⟨hxU', hxV⟩, rfl⟩ := hz hzM
    show (tangentSpace M (ψ x)).starProjection = Pr (fderiv ℝ ψ (g (ψ x)))
    rw [hUg x hxU']
    exact key _ _ (hT x hxV)
  -- Step 6: for `x ∈ U`, `Q (ψ x) = Π(Dψ (g (ψ x))) = Π(Dψ x)`.
  · filter_upwards [hUo.mem_nhds hxU] with x hx
    show Pr (fderiv ℝ ψ (g (ψ x))) = _
    rw [hUg x hx]
/-- **Derivative of an operator field that fixes the chart tangent vectors** (Simon 4.23–4.26, the
computation `B = (D²ψ)^⊥` in a chart). Let `ψ : ℝⁿ → ℝᴺ` and its derivative `Dψ` be differentiable
at `x₀`, and let `Q : ℝᴺ → L(ℝᴺ, ℝᴺ)` be differentiable at `ψ(x₀)` with
`Q(ψ(x))(Dψ(x)v) = Dψ(x)v` for all `v` and all `x` near `x₀`. Then
`DQ(ψ(x₀))(Dψ(x₀)a)(Dψ(x₀)b) = D²ψ(x₀)[a, b] - Q(ψ(x₀))(D²ψ(x₀)[a, b])`. The map
`G(x) = Q(ψ(x))(Dψ(x)b)` has derivative `a ↦ Q(ψ(x₀))(D²ψ(x₀)[a, b]) + DQ(ψ(x₀))(Dψ(x₀)a)(Dψ(x₀)b)`
by the chain rule and the product rule `HasFDerivAt.clm_apply`. Since `G(x) = Dψ(x)b` near `x₀`,
it also has derivative `a ↦ D²ψ(x₀)[a, b]`; uniqueness of the derivative gives the identity. -/
theorem Submission.sff_projection_field_fderiv_identity : ∀ (n N : ℕ) (ψ : Rn n → Rn N) (Q : Rn N → (Rn N →L[ℝ] Rn N)) (x₀ : Rn n), DifferentiableAt ℝ ψ x₀ → DifferentiableAt ℝ (fderiv ℝ ψ) x₀ → DifferentiableAt ℝ Q (ψ x₀) → (∀ᶠ x in 𝓝 x₀, ∀ v : Rn n, Q (ψ x) (fderiv ℝ ψ x v) = fderiv ℝ ψ x v) → ∀ a b : Rn n, fderiv ℝ Q (ψ x₀) (fderiv ℝ ψ x₀ a) (fderiv ℝ ψ x₀ b) = fderiv ℝ (fderiv ℝ ψ) x₀ a b - Q (ψ x₀) (fderiv ℝ (fderiv ℝ ψ) x₀ a b) := by
  intro n N ψ Q x₀ hψ hDψ hQ hfix a b
  -- Step 1 (chain rule): `c(x) = Q(ψ(x))` has derivative `DQ(ψ(x₀)) ∘ Dψ(x₀)` at `x₀`.
  have hc : HasFDerivAt (fun x ↦ Q (ψ x)) ((fderiv ℝ Q (ψ x₀)).comp (fderiv ℝ ψ x₀)) x₀ :=
    hQ.hasFDerivAt.comp x₀ hψ.hasFDerivAt
  -- Step 2: `u(x) = Dψ(x)b` has derivative `a' ↦ D²ψ(x₀)[a', b]` at `x₀`.
  have hu : HasFDerivAt (fun x ↦ fderiv ℝ ψ x b)
      ((fderiv ℝ ψ x₀).comp (0 : Rn n →L[ℝ] Rn n) + (fderiv ℝ (fderiv ℝ ψ) x₀).flip b) x₀ :=
    hDψ.hasFDerivAt.clm_apply (hasFDerivAt_const b x₀)
  -- Step 3 (product rule): the derivative of `G(x) = c(x)(u(x))` at `x₀`.
  have hG := hc.clm_apply hu
  -- Step 4: `G = u` near `x₀`, so the two derivatives of `G` at `x₀` agree.
  have hGu : (fun x ↦ Q (ψ x) (fderiv ℝ ψ x b)) =ᶠ[𝓝 x₀] fun x ↦ fderiv ℝ ψ x b :=
    hfix.mono fun x hx ↦ hx b
  have h := congrArg (fun L ↦ L a) (hG.unique (hu.congr_of_eventuallyEq hGu))
  simp only [add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply, zero_apply, map_zero,
    ContinuousLinearMap.flip_apply, zero_add] at h
  -- Step 5: rearrange `Q(ψ(x₀))(D²ψ(x₀)[a, b]) + DQ(ψ(x₀))(Dψ(x₀)a)(Dψ(x₀)b) = D²ψ(x₀)[a, b]`.
  rw [eq_sub_iff_add_eq, add_comm]
  exact h
/-- **Simon Ch. 2, 4.23–4.26 (pp. 59–60), derivative within `M` along chart directions.** Let `V`
be a neighbourhood of `x₀` with `ψ(V) ⊆ M`, `ψ` differentiable at `x₀`, `g` differentiable at
`y₀ = ψ(x₀)` and `f = g` on `M` near `y₀`. Then the derivative of `f` within `M` at `y₀` agrees with
`Dg(y₀)` in every chart direction `Dψ(x₀)a`. Both are derivatives of `f` within `M` at `y₀`, so they
agree on the tangent cone of `M` at `y₀`; this cone contains `Dψ(x₀)a`, the image of `a` in the
tangent cone `ℝⁿ` of `V` at `x₀`. `M` need not have unique differentiability at `y₀`. -/
theorem Submission.sff_fderivWithin_chart_direction : ∀ (n N : ℕ) (M : Set (Rn N)) (V : Set (Rn n)) (ψ : Rn n → Rn N) (f g : Rn N → (Rn N →L[ℝ] Rn N)) (x₀ : Rn n), V ∈ 𝓝 x₀ → ψ '' V ⊆ M → DifferentiableAt ℝ ψ x₀ → DifferentiableAt ℝ g (ψ x₀) → f =ᶠ[𝓝[M] ψ x₀] g → ∀ a : Rn n, fderivWithin ℝ f M (ψ x₀) (fderiv ℝ ψ x₀ a) = fderiv ℝ g (ψ x₀) (fderiv ℝ ψ x₀ a) := by
  intro n N M V ψ f g x₀ hV hψV hψ hg hfg a
  -- `ψ x₀ ∈ ψ '' V ⊆ M`, so `f (ψ x₀) = g (ψ x₀)` and `Dg(ψ x₀)` is a derivative of `f` within `M`.
  have hmem : ψ x₀ ∈ M := hψV (mem_image_of_mem ψ (mem_of_mem_nhds hV))
  have hf : HasFDerivWithinAt f (fderiv ℝ g (ψ x₀)) M (ψ x₀) :=
    hg.hasFDerivAt.hasFDerivWithinAt.congr_of_eventuallyEq hfg (hfg.eq_of_nhdsWithin hmem)
  -- The tangent cone of `V` at `x₀` is everything, and `Dψ(x₀)` maps it into the tangent cone of
  -- `ψ '' V ⊆ M` at `ψ x₀`.
  have hcone : fderiv ℝ ψ x₀ a ∈ tangentConeAt ℝ M (ψ x₀) := by
    refine tangentConeAt_mono hψV
      ((hψ.hasFDerivAt.hasFDerivWithinAt (s := V)).mapsTo_tangent_cone ?_)
    rw [tangentConeAt_of_mem_nhds hV]
    exact mem_univ a
  -- Two derivatives of `f` within `M` at `ψ x₀` agree on the tangent cone.
  exact hf.differentiableWithinAt.hasFDerivWithinAt.unique_on hf hcone

/-- **Simon Ch. 2, 4.26 (p. 60), the second fundamental form in a chart.** Assume (TH), the frozen
statement of `Submission.simon_submanifold_tangent_basics`; only its first part, the chart
description `T_{ψ(x)} M = range Dψ(x)` of the tangent space, is used. Then for a `C²` local
representation `(V, W, ψ)` of `M`, `x ∈ V` and `a, b ∈ ℝⁿ`,
`B_{ψ(x)}(Dψ(x)a, Dψ(x)b) = (D²ψ(x)[a, b])^⊥`. On `M` near `ψ(x)` the tangent projection `P` agrees
with a field `Q` that is differentiable at `ψ(x)` and fixes the chart tangent vectors
(`sff_tangentProjection_local_extension`). So `B_{ψ(x)}(Dψ(x)a, ·) = DQ(ψ(x))(Dψ(x)a)`
(`sff_fderivWithin_chart_direction`), and differentiating `Q(ψ(x'))(Dψ(x')b) = Dψ(x')b` gives
`DQ(ψ(x))(Dψ(x)a)(Dψ(x)b) = D²ψ(x)[a, b] - Q(ψ(x))(D²ψ(x)[a, b])`
(`sff_projection_field_fderiv_identity`), where `Q(ψ(x)) = P_{ψ(x)}`. -/
theorem Submission.second_fundamental_form_chart_formula : ((∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)) (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N), 1 ≤ r → Chapter02.IsSimonLocalRepresentation r M V W ψ → ∀ x ∈ V, tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap) ∧ ∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)), Chapter02.IsSimonSubmanifold (E := Rn n) r M → MeasurableSet M ∧ ContinuousOn (tangentProjection M) M) → ∀ (n N : ℕ) (M : Set (Rn N)) (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N), Chapter02.IsSimonLocalRepresentation 2 M V W ψ → ∀ x ∈ V, ∀ a b : Rn n, secondFundamentalForm M (ψ x) (fderiv ℝ ψ x a) (fderiv ℝ ψ x b) = normalPart M (ψ x) (fderiv ℝ (fderiv ℝ ψ) x a b) := by
  intro hTH n N M V W ψ hψ x₀ hx₀ a b
  -- Step 1: the chart instance of (TH1) (class `2 ≥ 1`): `T_{ψ(x)} M = range Dψ(x)` for `x ∈ V`.
  have hT : ∀ x ∈ V, tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap :=
    hTH.1 n N 2 M V W ψ (by norm_num) hψ
  -- Step 2: an extension `Q` of the tangent projection near `ψ(x₀)`, differentiable at `ψ(x₀)`.
  obtain ⟨Q, hQ, hPQ, hQψ⟩ :=
    Submission.sff_tangentProjection_local_extension n N M V W ψ hψ hT x₀ hx₀
  -- Step 3: `ψ` is `C²` at `x₀`, so `ψ` and `Dψ` are differentiable at `x₀`.
  have hV : V ∈ 𝓝 x₀ := hψ.isOpen_source.mem_nhds hx₀
  have hψ2 := hψ.contDiffOn.contDiffAt hV
  have hψ1 : DifferentiableAt ℝ ψ x₀ := hψ2.differentiableAt (by norm_num)
  have hDψ : DifferentiableAt ℝ (fderiv ℝ ψ) x₀ :=
    (hψ2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  -- Step 4: `ψ '' V = W ∩ M ⊆ M`; in particular `ψ(x₀) ∈ M`, so `P_{ψ(x₀)} = Q(ψ(x₀))`.
  have hψV : ψ '' V ⊆ M := hψ.image_eq ▸ inter_subset_right
  have hP₀ : tangentProjection M (ψ x₀) = Q (ψ x₀) :=
    hPQ.eq_of_nhdsWithin (hψV (mem_image_of_mem ψ hx₀))
  -- Step 5: near `x₀`, `Q(ψ(x))` is the projection onto `range Dψ(x)`, so it fixes `Dψ(x)v`.
  have hfix : ∀ᶠ x in 𝓝 x₀, ∀ v : Rn n, Q (ψ x) (fderiv ℝ ψ x v) = fderiv ℝ ψ x v :=
    hQψ.mono fun x hx v ↦ by
      rw [hx]
      exact Submodule.starProjection_eq_self_iff.2 (LinearMap.mem_range_self _ v)
  -- Step 6: `B_{ψ(x₀)}(Dψ(x₀)a, ·) = DQ(ψ(x₀))(Dψ(x₀)a)`; then the derivative identity for `Q`.
  rw [secondFundamentalForm, normalPart,
    Submission.sff_fderivWithin_chart_direction n N M V ψ (tangentProjection M) Q x₀ hV hψV hψ1
      hQ hPQ a,
    Submission.sff_projection_field_fderiv_identity n N ψ Q x₀ hψ1 hDψ hQ hfix a b, hP₀]

/-- **Simon Ch. 2, 4.26–4.27 (p. 60) and the identity in the proof of 5.11 (p. 65): properties of
`B` and `H`.** Assume (TH), the frozen statement of `Submission.simon_submanifold_tangent_basics`,
and let `M` be an `n`-dimensional `C²` submanifold of `ℝᴺ`. Then (i) `B_y(τ, η) = B_y(η, τ)` lies in
`(T_y M)^⊥` for `y ∈ M` and `τ, η ∈ T_y M`; (ii) `y ↦ H(y)` is continuous on `M`; (iii) if `Y` is
differentiable at `y ∈ M` and normal along `M`, then `⟨η, DY(y)τ⟩ = -⟨Y(y), B_y(τ, η)⟩` for
`τ, η ∈ T_y M`. In every `C²` chart `(V, W, ψ)` of `M`, (TH1) gives `T_{ψ(x)} M = range Dψ(x)`, and
`B_{ψ(x)}(Dψ(x)a, Dψ(x)b) = (D²ψ(x)[a, b])^⊥` (`Submission.second_fundamental_form_chart_formula`).
From these two chart facts, (i) is `Submission.second_fundamental_form_symm_normal_of_chart_formula`
and (iii) is `Submission.inner_fderiv_normal_field_eq_neg_second_fundamental_form`. For (ii), with
`G(x) = Dψ(x)* ∘ Dψ(x)`, the map `x ↦ H(ψ(x)) = (∑_{k,l} ⟨e_k, G(x)⁻¹ e_l⟩ D²ψ(x)[e_k, e_l])^⊥` is
continuous on `V` because `z ↦ P_z` is continuous on `M` by (TH2)
(`Submission.mean_curvature_comp_chart_continuousOn`); continuity on `M` can be checked in charts
(`Submission.simon_submanifold_continuousOn_of_chart_continuousOn`). -/
theorem Submission.second_fundamental_form_symm_normal_continuity : ((∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)) (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N), 1 ≤ r → Chapter02.IsSimonLocalRepresentation r M V W ψ → ∀ x ∈ V, tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap) ∧ ∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)), Chapter02.IsSimonSubmanifold (E := Rn n) r M → MeasurableSet M ∧ ContinuousOn (tangentProjection M) M) → ∀ (n N : ℕ) (M : Set (Rn N)), Chapter02.IsSimonSubmanifold (E := Rn n) 2 M → (∀ y ∈ M, ∀ τ ∈ tangentSpace M y, ∀ η ∈ tangentSpace M y, secondFundamentalForm M y τ η = secondFundamentalForm M y η τ ∧ ∀ v ∈ tangentSpace M y, inner ℝ (secondFundamentalForm M y τ η) v = 0) ∧ ContinuousOn (meanCurvature M) M ∧ ∀ (Y : Rn N → Rn N) (y : Rn N), y ∈ M → DifferentiableAt ℝ Y y → (∀ z ∈ M, ∀ v ∈ tangentSpace M z, inner ℝ (Y z) v = 0) → ∀ τ ∈ tangentSpace M y, ∀ η ∈ tangentSpace M y, inner ℝ η (fderiv ℝ Y y τ) = -inner ℝ (Y y) (secondFundamentalForm M y τ η) := by
  intro hTH n N M hM
  -- Step 1 (TH1, class `2 ≥ 1`): `T_{ψ(x)} M = range Dψ(x)` in every `C²` chart of `M`.
  have hR : ∀ (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N),
      Chapter02.IsSimonLocalRepresentation 2 M V W ψ →
        ∀ x ∈ V, tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap :=
    fun V W ψ hψ ↦ hTH.1 n N 2 M V W ψ (by norm_num) hψ
  -- Step 2: `B_{ψ(x)}(Dψ(x)a, Dψ(x)b) = (D²ψ(x)[a, b])^⊥` in every `C²` chart of `M`.
  have hC : ∀ (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N),
      Chapter02.IsSimonLocalRepresentation 2 M V W ψ → ∀ x ∈ V, ∀ a b : Rn n,
        secondFundamentalForm M (ψ x) (fderiv ℝ ψ x a) (fderiv ℝ ψ x b) =
          normalPart M (ψ x) (fderiv ℝ (fderiv ℝ ψ) x a b) :=
    fun V W ψ hψ ↦ Submission.second_fundamental_form_chart_formula hTH n N M V W ψ hψ
  -- Step 3: (i) symmetry and normality of `B` and (iii) the normal-field identity, from Steps 1–2.
  refine ⟨Submission.second_fundamental_form_symm_normal_of_chart_formula n N M hM hR hC, ?_,
    Submission.inner_fderiv_normal_field_eq_neg_second_fundamental_form n N M hM hR hC⟩
  -- Step 4: (ii) `H ∘ ψ` is continuous on `V` for every `C²` chart (TH2: `z ↦ P_z` is continuous on
  -- `M`), and continuity on `M` is checked in charts.
  exact Submission.simon_submanifold_continuousOn_of_chart_continuousOn n N 2 M (Rn N)
    (meanCurvature M) hM fun V W ψ hψ ↦
      Submission.mean_curvature_comp_chart_continuousOn n N M V W ψ hψ (hTH.2 n N 2 M hM).2
        (hR V W ψ hψ) (hC V W ψ hψ)
/-- **Simon Ch. 2, 4.21–4.30 (pp. 59–61) in a chart: the divergence density.** Assume `(TH)`, the
frozen statement of `simon_submanifold_tangent_basics`. Let `(V, W, ψ)` be a class-`2` local
representation of `M`, `Y` a `C¹` field, and put `A = Dψ`, `G = A*A`, `J = areaJacobianAt ψ`,
`u = Y ∘ ψ`, `a = G⁻¹A*u`. Then `w = J • a` is `C¹` on `V` and vanishes where `u` does. By the
product rule and Jacobi's formula, `trace Dw = J (trace Da + trace(G⁻¹A* D²ψ[a]))`, and the
coefficient trace identity rewrites the bracket as `trace(G⁻¹A* Du) + ⟨u - Aa, ∑ₗ D²ψ[eₗ, G⁻¹eₗ]⟩`.
The first term is `div_M Y ∘ ψ` (chain rule and the chart formula for `div_M`). Since `Aa = Pu` with
`P = AG⁻¹A*` self-adjoint, the chart formulas for `H` and `B` make the second term `⟨u, H ∘ ψ⟩`. -/
theorem Submission.chart_divergence_density_formula : ((∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)) (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N), 1 ≤ r → Chapter02.IsSimonLocalRepresentation r M V W ψ → ∀ x ∈ V, tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap) ∧ ∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)), Chapter02.IsSimonSubmanifold (E := Rn n) r M → MeasurableSet M ∧ ContinuousOn (tangentProjection M) M) → ∀ (n N : ℕ) (M : Set (Rn N)) (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N) (Y : Rn N → Rn N), Chapter02.IsSimonLocalRepresentation 2 M V W ψ → ContDiff ℝ 1 Y → ∃ w : Rn n → Rn n, ContDiffOn ℝ 1 w V ∧ (∀ x ∈ V, Y (ψ x) = 0 → w x = 0) ∧ ∀ x ∈ V, LinearMap.trace ℝ (Rn n) (fderiv ℝ w x).toLinearMap = Chapter02.areaJacobianAt ψ x * (tangentialDivergence M Y (ψ x) + inner ℝ (Y (ψ x)) (meanCurvature M (ψ x))) := by
  intro hTH n N M V W ψ Y hψ hY
  have hV : IsOpen V := hψ.isOpen_source
  have hψ2 : ContDiffOn ℝ 2 ψ V := hψ.contDiffOn
  have hinj : ∀ x ∈ V, Function.Injective (fderiv ℝ ψ x) := fun x hx ↦ hψ.injective_fderiv hx
  have hu : ContDiffOn ℝ 1 (fun x ↦ Y (ψ x)) V := hY.comp_contDiffOn (hψ2.of_le (by norm_num))
  obtain ⟨hJ, hDJ⟩ :=
    Submission.areaJacobianAt_contDiffOn_fderiv_eq_gram_trace n N V ψ hV hψ2 hinj
  have ha := Submission.chart_tangential_coefficient_contDiffOn n N V ψ _ hV hψ2 hinj hu
  -- `w = J • a` with `a = G⁻¹A*(Y ∘ ψ)`.
  refine ⟨fun x ↦ Chapter02.areaJacobianAt ψ x • Ring.inverse
      (ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x)
      (ContinuousLinearMap.adjoint (fderiv ℝ ψ x) (Y (ψ x))), hJ.smul ha,
    fun x _ h0 ↦ by simp only [h0, map_zero, smul_zero], fun x hx ↦ ?_⟩
  have hxV : V ∈ 𝓝 x := hV.mem_nhds hx
  have hT : tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap :=
    hTH.1 n N 2 M V W ψ (by norm_num) hψ x hx
  -- Product rule and Jacobi's formula: `trace Dw = J trace Da + J trace(G⁻¹A* D²ψ[a])`.
  have hsr (f : Rn n →L[ℝ] ℝ) (v : Rn n) :
      LinearMap.trace ℝ (Rn n) (f.smulRight v).toLinearMap = f v :=
    LinearMap.trace_smulRight f.toLinearMap v
  rw [fderiv_fun_smul (hJ.contDiffAt hxV).differentiableAt_one
      (ha.contDiffAt hxV).differentiableAt_one, ContinuousLinearMap.toLinearMap_add,
    ContinuousLinearMap.toLinearMap_smul, map_add, map_smul, smul_eq_mul, hsr, hDJ x hx]
  -- The coefficient trace identity, with `Du(x) = DY(ψ x) ∘ A` (chain rule).
  have hcore :=
    Submission.chart_tangential_coefficient_trace_identity n N V ψ _ hV hψ2 hinj hu x hx
  dsimp only at hcore
  rw [fderiv_fun_comp x (hY.differentiable one_ne_zero _)
    ((hψ2.contDiffAt hxV).differentiableAt (by norm_num)), inner_sub_left] at hcore
  -- The chart formulas for `div_M Y` and `H`; `P = AG⁻¹A*` is self-adjoint.
  have hP := (Submission.gram_inverse_range_starProjection n N (tangentSpace M (ψ x))
    (fderiv ℝ ψ x) (hinj x hx) hT).2.2
  rw [Submission.chart_tangentialDivergence_eq_gram_trace n N M (ψ x) (fderiv ℝ ψ x) Y
      (hinj x hx) hT,
    Submission.chart_meanCurvature_eq_normalPart_gram_sum n N M (ψ x) (fderiv ℝ ψ x)
      (fderiv ℝ (fderiv ℝ ψ) x) (hinj x hx) hT
      (Submission.second_fundamental_form_chart_formula hTH n N M V W ψ hψ x hx),
    normalPart, tangentProjection, inner_sub_right,
    ← Submodule.inner_starProjection_left_eq_right, hP, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]
  linear_combination Chapter02.areaJacobianAt ψ x * hcore

/-- **Simon Ch. 2, 4.22(*) and 4.30 (pp. 59–61), divergence identity for compact support.**
Assume (TH), the statement of `Submission.simon_submanifold_tangent_basics`. Let `M ⊆ ℝᴺ` be an
`n`-dimensional `C²` submanifold and `Y` a `C¹` field vanishing off a closed `S` with `M ∩ S`
compact. Then `div_M Y` and `⟨Y, H⟩` are `Hⁿ`-integrable on `M` and
`∫_M div_M Y dHⁿ = -∫_M ⟨Y, H⟩ dHⁿ`. A finite `C¹` partition of unity `ζ_q` near `M ∩ S`, each
`tsupport ζ_q` inside a chart target, gives `div_M Y + ⟨Y, H⟩ = ∑_q (div_M (ζ_q Y) + ⟨ζ_q Y, H⟩)`
on `M`. In the chart, `Jψ · (div_M (ζ_q Y) + ⟨ζ_q Y, H⟩) ∘ ψ` is the divergence of a field
vanishing off the compact `V ∩ ψ⁻¹(tsupport ζ_q)`, so each summand has integral `0`. -/
theorem Submission.submanifold_divergence_identity_compact : ((∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)) (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N), 1 ≤ r → Chapter02.IsSimonLocalRepresentation r M V W ψ → ∀ x ∈ V, tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap) ∧ ∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)), Chapter02.IsSimonSubmanifold (E := Rn n) r M → MeasurableSet M ∧ ContinuousOn (tangentProjection M) M) → ∀ (n N : ℕ) (M S : Set (Rn N)) (Y : Rn N → Rn N), Chapter02.IsSimonSubmanifold (E := Rn n) 2 M → ContDiff ℝ 1 Y → IsClosed S → (∀ x ∉ S, Y x = 0) → IsCompact (M ∩ S) → IntegrableOn (tangentialDivergence M Y) M μHE[n] ∧ IntegrableOn (fun y ↦ inner ℝ (Y y) (meanCurvature M y)) M μHE[n] ∧ ∫ y in M, tangentialDivergence M Y y ∂μHE[n] = -∫ y in M, inner ℝ (Y y) (meanCurvature M y) ∂μHE[n] := by
  intro hTH n N M S Y hM hY hS hYS hMS
  -- `M` is measurable, `P` and `H` are continuous on `M`, and compact subsets of `M` have finite
  -- `Hⁿ`-measure.
  obtain ⟨hMmeas, hP⟩ := hTH.2 n N 2 M hM
  have hH : ContinuousOn (meanCurvature M) M :=
    (Submission.second_fundamental_form_symm_normal_continuity hTH n N M hM).2.1
  have hfin : ∀ C ⊆ M, IsCompact C → μHE[n] C < ⊤ :=
    (Submission.simon_submanifold_hausdorff_finite_pos n N 2 M hM).1
  -- The two integrability conjuncts.
  obtain ⟨hdiv, hinner⟩ := Submission.tangentialDivergence_meanCurvature_integrableOn n N M S Y
    hMmeas hP hH hfin hY hS hYS hMS
  refine ⟨hdiv, hinner, ?_⟩
  -- A finite `C¹` partition of unity near `M ∩ S`, each `tsupport ζ_q` inside a chart target.
  obtain ⟨p, ζ, O, hO, hMSO, hζsum, hζ⟩ := Submission.exists_finite_contDiff_partition_near_compact
    N (M ∩ S) (fun U ↦ ∃ (V : Set (Rn n)) (ψ : Rn n → Rn N),
      Chapter02.IsSimonLocalRepresentation 2 M V U ψ) hMS fun y hy ↦ by
    obtain ⟨V, W, ψ, hyW, hψ⟩ := hM.2 y hy.1
    exact ⟨W, hψ.isOpen_target, hyW, V, ψ, hψ⟩
  -- Each localized integrand `div_M (ζ_q Y) + ⟨ζ_q Y, H⟩` is integrable on `M` with integral `0`.
  have hloc : ∀ q, IntegrableOn (fun y ↦ tangentialDivergence M (fun z ↦ ζ q z • Y z) y +
        inner ℝ (ζ q y • Y y) (meanCurvature M y)) M μHE[n] ∧
      ∫ y in M, (tangentialDivergence M (fun z ↦ ζ q z • Y z) y +
        inner ℝ (ζ q y • Y y) (meanCurvature M y)) ∂μHE[n] = 0 := by
    intro q
    obtain ⟨hζq, hζK, U, ⟨V, ψ, hψ⟩, hKU⟩ := hζ q
    have hK : IsCompact (tsupport (ζ q)) := hζK.isCompact
    have hYq : ContDiff ℝ 1 (fun z ↦ ζ q z • Y z) := hζq.smul hY
    -- `ζ_q Y` vanishes on a neighbourhood of every point outside `tsupport ζ_q`.
    have hvan : ∀ y ∉ tsupport (ζ q), (fun z ↦ ζ q z • Y z) =ᶠ[𝓝 y] 0 := fun y hy ↦ by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
      simp only [hz, Pi.zero_apply, zero_smul]
    have hYq0 : ∀ y ∉ tsupport (ζ q), ζ q y • Y y = 0 := fun y hy ↦ (hvan y hy).eq_of_nhds
    -- `M ∩ tsupport ζ_q = ψ(V ∩ ψ⁻¹(tsupport ζ_q))` is compact by relative properness.
    have hMK : IsCompact (M ∩ tsupport (ζ q)) := by
      have himg : ψ '' (V ∩ ψ ⁻¹' tsupport (ζ q)) = M ∩ tsupport (ζ q) := by
        ext z
        constructor
        · rintro ⟨x, ⟨hxV, hxK⟩, rfl⟩
          have h : ψ x ∈ U ∩ M := hψ.image_eq ▸ mem_image_of_mem ψ hxV
          exact ⟨h.2, hxK⟩
        · rintro ⟨hzM, hzK⟩
          have h : z ∈ ψ '' V := by
            rw [hψ.image_eq]
            exact ⟨hKU hzK, hzM⟩
          obtain ⟨x, hxV, rfl⟩ := h
          exact ⟨x, ⟨hxV, hzK⟩, rfl⟩
      rw [← himg]
      exact (hψ.isCompact_source_inter_preimage _ hK hKU).image_of_continuousOn
        (hψ.contDiffOn.continuousOn.mono inter_subset_left)
    obtain ⟨hdq, hiq⟩ := Submission.tangentialDivergence_meanCurvature_integrableOn n N M
      (tsupport (ζ q)) (fun z ↦ ζ q z • Y z) hMmeas hP hH hfin hYq (isClosed_tsupport _) hYq0 hMK
    refine ⟨hdq.add hiq, ?_⟩
    -- The chart field `w` with `trace Dw = Jψ · (div_M (ζ_q Y) + ⟨ζ_q Y, H⟩) ∘ ψ` on `V`.
    obtain ⟨w, hw, hw0, htr⟩ := Submission.chart_divergence_density_formula hTH n N M V U ψ
      (fun z ↦ ζ q z • Y z) hψ hYq
    refine Submission.chart_setIntegral_eq_zero_of_trace_fderiv_eq n N 2 M V U (tsupport (ζ q)) ψ
      (fun y ↦ tangentialDivergence M (fun z ↦ ζ q z • Y z) y +
        inner ℝ (ζ q y • Y y) (meanCurvature M y)) w one_le_two hψ hMmeas hK hKU
      (fun y _ hy ↦ ?_) hw (fun x hx hxK ↦ hw0 x hx (hYq0 _ hxK)) htr
    -- Off `tsupport ζ_q` both `D(ζ_q Y)` and `ζ_q Y` vanish.
    have hD : fderiv ℝ (fun z ↦ ζ q z • Y z) y = 0 := by
      rw [(hvan y hy).fderiv_eq, fderiv_zero, Pi.zero_apply]
    simp only [tangentialDivergence, hD, zero_apply, inner_zero_right,
      Finset.sum_const_zero, hYq0 y hy, inner_zero_left, add_zero]
  -- Sum the localized identities over the partition.
  have hsum := Submission.tangentialDivergence_add_inner_eq_sum_partition N p M S O Y ζ hY
    (fun q ↦ (hζ q).1) hS hYS hO hMSO hζsum
  rw [eq_neg_iff_add_eq_zero, ← integral_add hdiv hinner, setIntegral_congr_fun hMmeas hsum,
    integral_finsetSum _ fun q _ ↦ (hloc q).1]
  exact Finset.sum_eq_zero fun q _ ↦ (hloc q).2

/-- **Simon Ch. 2, Lemma 5.5(2) (p. 63), stationary `⇒ H ≡ 0`.** Assume (TH) and the first
variation formula 5.3. If the `n`-dimensional `C²` submanifold `M ⊆ ℝ^{n+ℓ}` is stationary in the
open set `U`, then `H = 0` on `M ∩ U`; no compactness of `Ū ∩ M` is needed. By the fundamental
lemma for test fields (`μ = Hⁿ`, `F = H`: `M` is measurable by (TH2), `H` is continuous on `M`,
`Hⁿ` is positive on relatively open pieces of `M`, and `M` is locally compact in closed-ball form)
it suffices that `∫_M ⟨Y, H⟩ dHⁿ = 0` for every `C²` field `Y` with compact support in `U` and
`M ∩ spt Y` compact. For such `Y`, `φ_t(x) = x + c t Y(x)` is admissible with initial velocity
`c Y` (`c > 0`), so stationarity, 5.3 and uniqueness of derivatives give `∫_M div_M (c Y) dHⁿ = 0`,
while the divergence identity gives `∫_M div_M (c Y) dHⁿ = -c ∫_M ⟨Y, H⟩ dHⁿ`. -/
theorem Submission.stationary_imp_mean_curvature_zero : ((∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)) (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N), 1 ≤ r → Chapter02.IsSimonLocalRepresentation r M V W ψ → ∀ x ∈ V, tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap) ∧ ∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)), Chapter02.IsSimonSubmanifold (E := Rn n) r M → MeasurableSet M ∧ ContinuousOn (tangentProjection M) M) → FirstVariation → ∀ (n ℓ : ℕ) (M U : Set (Rn (n + ℓ))), Chapter02.IsSimonSubmanifold (E := Rn n) 2 M → IsOpen U → IsStationaryIn n M U → ∀ y ∈ M ∩ U, meanCurvature M y = 0 := by
  intro hTH hFV n ℓ M U hM hU hS y hy
  -- `M` is also a `C¹` Simon submanifold: each class-2 chart is a class-1 chart.
  have hM1 : Chapter02.IsSimonSubmanifold (E := Rn n) 1 M := by
    refine ⟨le_rfl, fun z hz ↦ ?_⟩
    obtain ⟨V, W, ψ, hzW, hψ⟩ := hM.2 z hz
    exact ⟨V, W, ψ, hzW, hψ.1, hψ.2.1, hψ.2.2.1.of_le (by norm_num), hψ.2.2.2⟩
  -- Fundamental lemma with `μ = Hⁿ`, `F = H`: `M` is measurable (TH2), `H` is continuous on `M`
  -- (sff_properties), `Hⁿ` is positive near points of `M` (measure_bounds (b)), and `M` is locally
  -- compact (local_compact_ball).
  refine Submission.vector_field_eq_zero_of_integral_inner_test_fields (n + ℓ) μHE[n] M U
    (meanCurvature M) (hTH.2 n (n + ℓ) 2 M hM).1 hU
    (Submission.second_fundamental_form_symm_normal_continuity hTH n (n + ℓ) M hM).2.1
    (Submission.simon_submanifold_hausdorff_finite_pos n (n + ℓ) 2 M hM).2
    (Submission.simon_submanifold_exists_closedBall_isCompact_inter n (n + ℓ) 2 M hM) ?_ y hy
  -- It remains to show `∫_M ⟨Y, H⟩ dHⁿ = 0` for every admissible test field `Y`.
  intro Y hY hYc hYU hYK
  -- scaled_deformation: `φ_t(x) = x + (c t) Y(x)` is admissible, with initial velocity `c Y`.
  obtain ⟨c, hc, hφ, hvel⟩ :=
    Submission.scaled_field_deformation_is_admissible (n + ℓ) U Y hU hY hYc hYU
  -- Stationarity, the first variation formula and uniqueness of derivatives:
  -- `∫_M div_M (c Y) dHⁿ = 0`.
  have hdiv0 : ∫ z in M, tangentialDivergence M (fun x ↦ c • Y x) z ∂μHE[n] = 0 := by
    have hfv := hFV n ℓ M U (tsupport Y) (fun t x ↦ x + (c * t) • Y x) hM1 hU ⟨y, hy.2, hy.1⟩
      (fun K' hK' hK'U ↦ by rw [inter_comm]; exact hS.1 K' hK' hK'U) hφ
    rw [show initialVelocity (fun t x ↦ x + (c * t) • Y x) = fun x ↦ c • Y x from funext hvel]
      at hfv
    exact hfv.unique (hS.2 _ _ hφ)
  -- divergence_identity for the `C¹` field `c Y`, which vanishes off the closed set `tsupport Y`:
  -- `⟨c Y, H⟩` is integrable on `M` and `∫_M div_M (c Y) dHⁿ = -∫_M ⟨c Y, H⟩ dHⁿ`.
  obtain ⟨-, hint, hdiv⟩ := Submission.submanifold_divergence_identity_compact hTH n (n + ℓ) M
    (tsupport Y) (fun x ↦ c • Y x) hM ((hY.of_le (by norm_num)).const_smul c)
    (isClosed_tsupport Y) (fun x hx ↦ by simp [image_eq_zero_of_notMem_tsupport hx]) hYK
  -- `⟨c Y, H⟩ = c ⟨Y, H⟩` and `c ≠ 0`.
  have hcY : ∀ z, inner ℝ (c • Y z) (meanCurvature M z) = c * inner ℝ (Y z) (meanCurvature M z) :=
    fun z ↦ real_inner_smul_left _ _ _
  simp only [hcY] at hint hdiv
  rw [hdiv0, integral_const_mul] at hdiv
  refine ⟨?_, ?_⟩
  · have h : IntegrableOn (fun z ↦ c⁻¹ * (c * inner ℝ (Y z) (meanCurvature M z))) M μHE[n] :=
      hint.const_mul c⁻¹
    simpa only [inv_mul_cancel_left₀ hc.ne'] using h
  · exact (mul_eq_zero.1 (neg_eq_zero.1 hdiv.symm)).resolve_left hc.ne'
/-- **Simon Ch. 2, Lemma 5.5(2) (p. 63), `H ≡ 0` implies stationary.** Assume (TH), the frozen
statement of `Submission.simon_submanifold_tangent_basics`, and the first variation formula 5.3.
Let `M ⊆ ℝ^{n+ℓ}` be an `n`-dimensional `C²` submanifold and `U` open with `closure U ∩ M`
compact. If `H ≡ 0` on `M ∩ U`, then `M` is stationary in `U`. For compact `K ⊆ U` the set
`M ∩ K = (closure U ∩ M) ∩ K` is compact, so `Hⁿ(M ∩ K) < ∞`. By 5.3 the first variation equals
`∫_M div_M X dHⁿ`. The initial velocity `X` is `C¹` and vanishes off `K`, so by 4.30 this
integral is `-∫_M X · H dHⁿ`. That integral is `0` because `H = 0` on `M ∩ U` and `X = 0` off
`K ⊆ U`. -/
theorem Submission.mean_curvature_zero_imp_stationary : ((∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)) (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N), 1 ≤ r → Chapter02.IsSimonLocalRepresentation r M V W ψ → ∀ x ∈ V, tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap) ∧ ∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)), Chapter02.IsSimonSubmanifold (E := Rn n) r M → MeasurableSet M ∧ ContinuousOn (tangentProjection M) M) → FirstVariation → ∀ (n ℓ : ℕ) (M U : Set (Rn (n + ℓ))), Chapter02.IsSimonSubmanifold (E := Rn n) 2 M → IsOpen U → IsCompact (closure U ∩ M) → (∀ y ∈ M ∩ U, meanCurvature M y = 0) → IsStationaryIn n M U := by
  intro hTH hFV n ℓ M U hM hU hcpt hH
  -- Step 1: for compact `K ⊆ U`, `M ∩ K = (closure U ∩ M) ∩ K` is compact, so `Hⁿ(M ∩ K) < ∞`.
  have hMK : ∀ K, IsCompact K → K ⊆ U → IsCompact (M ∩ K) := by
    intro K hK hKU
    have hEq : M ∩ K = (closure U ∩ M) ∩ K :=
      Subset.antisymm (fun y hy ↦ ⟨⟨subset_closure (hKU hy.2), hy.1⟩, hy.2⟩)
        fun y hy ↦ ⟨hy.1.2, hy.2⟩
    rw [hEq]
    exact hcpt.inter_right hK.isClosed
  have hfin : ∀ K, IsCompact K → K ⊆ U → μHE[n] (M ∩ K) < ⊤ := fun K hK hKU ↦
    (Submission.simon_submanifold_hausdorff_finite_pos n (n + ℓ) 2 M hM).1 _ inter_subset_left
      (hMK K hK hKU)
  -- Step 2: zero first variation for every admissible `C²` deformation `φ` (so `K ⊆ U` compact).
  refine ⟨hfin, fun K φ hφ ↦ ?_⟩
  have hK : IsCompact K := hφ.2.1
  have hKU : K ⊆ U := hφ.2.2.1
  rcases (U ∩ M).eq_empty_or_nonempty with hUM₀ | hUMne
  · -- Step 3: if `U ∩ M = ∅`, then `M ∩ K = ∅` and the deformed area is identically `0`.
    have hMK₀ : M ∩ K = ∅ := eq_empty_iff_forall_notMem.2 fun y hy ↦
      eq_empty_iff_forall_notMem.1 hUM₀ y ⟨hKU hy.2, hy.1⟩
    have hconst : deformedArea n M K φ = fun _ ↦ 0 := funext fun t ↦ by
      simp [deformedArea, hMK₀]
    rw [hconst]
    exact hasDerivAt_const _ _
  · -- Step 4: each `C²` chart is a `C¹` chart, so `M` is a `C¹` submanifold and 5.3 applies.
    have hM₁ : Chapter02.IsSimonSubmanifold (E := Rn n) 1 M := by
      refine ⟨le_rfl, fun y hy ↦ ?_⟩
      obtain ⟨V, W, ψ, hyW, hV, hW, hψ, hrest⟩ := hM.2 y hy
      exact ⟨V, W, ψ, hyW, hV, hW, hψ.of_le (by norm_num), hrest⟩
    have hderiv := hFV n ℓ M U K φ hM₁ hU hUMne
      (fun K' hK' hK'U ↦ by rw [inter_comm]; exact hfin K' hK' hK'U) hφ
    -- Step 5: `X` is `C¹` and vanishes off the closed set `K`, and `M ∩ K` is compact, so
    -- `∫_M div_M X dHⁿ = -∫_M X · H dHⁿ` (4.30).
    obtain ⟨hX, hX₀⟩ :=
      Submission.deformation_velocity_acceleration_regularity.1 (n + ℓ) U K φ hφ
    obtain ⟨-, -, hdiv⟩ := Submission.submanifold_divergence_identity_compact hTH n (n + ℓ) M K
      (initialVelocity φ) hM hX hK.isClosed hX₀ (hMK K hK hKU)
    -- Step 6: `X · H = 0` on `M`, since `H = 0` on `M ∩ U` and `X = 0` off `K ⊆ U`.
    have hXH : ∫ y in M, inner ℝ (initialVelocity φ y) (meanCurvature M y) ∂μHE[n] = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun y hy ↦ ?_
      by_cases hyU : y ∈ U
      · rw [hH y ⟨hy, hyU⟩, inner_zero_right]
      · rw [hX₀ y fun hyK ↦ hyU (hKU hyK), inner_zero_left]
    rwa [hdiv, hXH, neg_zero] at hderiv

/-- **Simon Ch. 2, Lemma 5.11 (p. 65), second variation of a stationary submanifold**, from the
tangent-space facts (TH), the first variation formula 5.3 and the second variation formula 5.4
(`C³` correction). Let `M` be `C²` and stationary in the open set `U` with `(M̄ \ M) ∩ U = ∅`, and
let `φ` be admissible of class `C³` for `(U, K)` with initial velocity `X` normal to `M`. Then
`M ∩ K = K ∩ M̄` is compact with `Hⁿ(M ∩ K) < ∞`, and `H = 0` on `M ∩ U` (5.5(2)), so
`∫_M div_M Z dHⁿ = -∫_M Z · H dHⁿ = 0` and `X · H = 0` on `M`. By 4.24 for the normal field `X` and
the symmetry of `B`, the 5.4 integrand is `div_M Z` plus the 5.11 integrand on `M`, and the latter
is integrable; so 5.4 gives the claim if `U ∩ M ≠ ∅`. If `U ∩ M = ∅`, then `M ∩ K = ∅`, so
`t ↦ Hⁿ(M_t)` vanishes identically and the 5.11 integrand vanishes on `M`. -/
theorem Submission.second_variation_stationary_of_variations : ((∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)) (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N), 1 ≤ r → Chapter02.IsSimonLocalRepresentation r M V W ψ → ∀ x ∈ V, tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap) ∧ ∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)), Chapter02.IsSimonSubmanifold (E := Rn n) r M → MeasurableSet M ∧ ContinuousOn (tangentProjection M) M) → FirstVariation → SecondVariation → SecondVariationStationary := by
  intro hTH hFV hSV n ℓ M U K φ hM hU hMU hstat hφ hXn
  have hKc : IsCompact K := hφ.2.1
  have hKU : K ⊆ U := hφ.2.2.1
  -- Step 1: `X` is `C²`, `Z` is `C¹`, and both vanish off `K`.
  obtain ⟨hX, hZ, hXZ⟩ :=
    Submission.deformation_velocity_acceleration_regularity.2 (n + ℓ) U K φ hφ
  -- Step 2: `M ∩ K = K ∩ M̄` is compact, as `(M̄ \ M) ∩ U = ∅` and `K ⊆ U`; `Hⁿ(M ∩ K) < ∞`.
  have hMK : IsCompact (M ∩ K) := by
    have hEq : M ∩ K = K ∩ closure M := by
      ext y
      refine ⟨fun hy ↦ ⟨hy.2, subset_closure hy.1⟩, fun hy ↦ ⟨?_, hy.1⟩⟩
      by_contra hyM
      have hy' : y ∈ (closure M \ M) ∩ U := ⟨⟨hy.2, hyM⟩, hKU hy.1⟩
      rw [hMU] at hy'
      exact hy'
    rw [hEq]
    exact hKc.inter_right isClosed_closure
  have hfin : μHE[n] (M ∩ K) < ⊤ := hstat.1 K hKc hKU
  -- Step 3: `H = 0` on `M ∩ U` (5.5(2)); off `U` we are off `K`, where `X = Z = 0`.
  have hH := Submission.stationary_imp_mean_curvature_zero hTH hFV n ℓ M U hM hU hstat
  have hcases : ∀ y ∈ M, meanCurvature M y = 0 ∨
      (initialVelocity φ y = 0 ∧ initialAcceleration φ y = 0) := fun y hy ↦
    (em (y ∈ U)).imp (fun hyU ↦ hH y ⟨hy, hyU⟩) fun hyU ↦ hXZ y fun hyK ↦ hyU (hKU hyK)
  -- Symmetry of `B` (4.26) and `η · D_τ X = -X · B(τ, η)` on `M` for the normal field `X` (4.24).
  obtain ⟨hB, -, hnormal⟩ :=
    Submission.second_fundamental_form_symm_normal_continuity hTH n (n + ℓ) M hM
  have hN : ∀ y ∈ M, ∀ τ ∈ tangentSpace M y, ∀ η ∈ tangentSpace M y,
      inner ℝ η (fderiv ℝ (initialVelocity φ) y τ) =
        -inner ℝ (initialVelocity φ y) (secondFundamentalForm M y τ η) := fun y hy ↦
    hnormal (initialVelocity φ) y hy (hX.differentiable (by norm_num) y) hXn
  -- Step 4: `∫_M div_M Z dHⁿ = -∫_M Z · H dHⁿ = 0`, since `Z · H = 0` on `M`.
  obtain ⟨hdivZ, -, hdivZ_eq⟩ := Submission.submanifold_divergence_identity_compact hTH n
    (n + ℓ) M K (initialAcceleration φ) hM hZ hKc.isClosed (fun x hx ↦ (hXZ x hx).2) hMK
  have hZH : ∀ y ∈ M, inner ℝ (initialAcceleration φ y) (meanCurvature M y) = 0 := by
    intro y hy
    rcases hcases y hy with h | h
    · rw [h, inner_zero_right]
    · rw [h.2, inner_zero_left]
  have hdivZ0 : ∫ y in M, tangentialDivergence M (initialAcceleration φ) y ∂μHE[n] = 0 := by
    rw [hdivZ_eq, setIntegral_eq_zero_of_forall_eq_zero hZH, neg_zero]
  -- Step 5: on `M`, the 5.4 integrand is `div_M Z` plus the 5.11 integrand, as `X · H = 0`.
  have hXH : ∀ y ∈ M, inner ℝ (initialVelocity φ y) (meanCurvature M y) = 0 := by
    intro y hy
    rcases hcases y hy with h | h
    · rw [h, inner_zero_right]
    · rw [h.1, inner_zero_left]
  have hpt : ∀ y ∈ M, secondVariationIntegrand M φ y =
      tangentialDivergence M (initialAcceleration φ) y + stableSecondVariationIntegrand M φ y :=
    fun y hy ↦ Submission.second_variation_integrand_eq_div_accel_add_stable (n + ℓ) M φ y
      (fun τ hτ η hη ↦ (hB y hy τ hτ η hη).1) (hN y hy) (hXH y hy)
  -- Step 6: the 5.11 integrand vanishes on `M \ K` and is integrable on `M`.
  obtain ⟨hMm, hP⟩ := hTH.2 n (n + ℓ) 2 M hM
  obtain ⟨hS0, hS⟩ := Submission.stable_second_variation_integrand_integrableOn n (n + ℓ) M K φ
    hMm hP (hX.of_le (by norm_num)) hKc.isClosed (fun x hx ↦ (hXZ x hx).1) hMK hfin hN
  -- Step 7: the 5.4 and 5.11 integrals over `M` agree.
  have hint : ∫ y in M, secondVariationIntegrand M φ y ∂μHE[n] =
      ∫ y in M, stableSecondVariationIntegrand M φ y ∂μHE[n] := by
    rw [setIntegral_congr_fun hMm hpt, integral_add hdivZ hS, hdivZ0, zero_add]
  by_cases hUM : (U ∩ M).Nonempty
  · -- Step 8: `U ∩ M ≠ ∅`, so 5.4 applies to `M`, which is also a `C¹` submanifold.
    have hM1 : Chapter02.IsSimonSubmanifold (E := Rn n) 1 M := by
      refine ⟨le_rfl, fun y hy ↦ ?_⟩
      obtain ⟨V, W, ψ, hyW, hV, hW, hψ, hinj, himg, hprop, hD⟩ := hM.2 y hy
      exact ⟨V, W, ψ, hyW, hV, hW, hψ.of_le (by norm_num), hinj, himg, hprop, hD⟩
    have hfin' : ∀ K', IsCompact K' → K' ⊆ U → μHE[n] (K' ∩ M) < ⊤ := by
      intro K' hK' hK'U
      rw [inter_comm]
      exact hstat.1 K' hK' hK'U
    obtain ⟨hdiff, hderiv⟩ := hSV n ℓ M U K φ hM1 hU hUM hfin' hφ
    rw [← hint]
    exact ⟨hdiff, hderiv⟩
  · -- Step 9: `U ∩ M = ∅`, so `M ∩ K = ∅`, `Hⁿ(M_t) = 0` and the 5.11 integrand is `0` on `M`.
    have hMK0 : M ∩ K = ∅ := eq_empty_of_subset_empty fun y hy ↦ hUM ⟨y, hKU hy.2, hy.1⟩
    have hA : deformedArea n M K φ = fun _ ↦ 0 := by
      funext t
      simp [deformedArea, hMK0]
    have hS00 : ∫ y in M, stableSecondVariationIntegrand M φ y ∂μHE[n] = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero fun y hy ↦ hS0 y hy fun hyK ↦ hUM ⟨y, hKU hyK, hy⟩
    rw [hA, hS00, deriv_const']
    exact ⟨Eventually.of_forall fun t ↦ differentiableAt_const _, hasDerivAt_const _ _⟩

/-- **Simon Ch. 2, 3.5 (p. 54), injective regular case: weighted area formula.** Let `s ⊆ ℝⁿ` be
Borel and `Φ : ℝⁿ → ℝᴺ` differentiable with injective derivative at every point of `s` and injective
on `s`. For an arbitrary (not necessarily measurable) `g : ℝᴺ → [0, ∞]`,
`∫_{Φ(s)} g dHⁿ = ∫_s JΦ · g ∘ Φ dHⁿ`, `JΦ(x) = areaJacobian (DΦ(x))`. The Jacobian-weighted measure
`JΦ · Hⁿ`, pulled back to the subtype `s`, is pushed forward by `Φ|_s` to `Hⁿ ⌊ Φ(s)`: on a Borel
`t ⊆ ℝᴺ` this is `variation_injective_area_formula` (Simon 3.2) applied to the Borel set
`s ∩ Φ⁻¹(t)`. As `Φ|_s` and the inclusion of `s` are measurable embeddings (Lusin–Souslin) and `JΦ`
is a finite Borel density, the weight `g` transports with no measurability assumption. -/
theorem Submission.variation_injective_weighted_area_formula : ∀ (n N : ℕ) (s : Set (Rn n)) (Φ : Rn n → Rn N) (g : Rn N → ℝ≥0∞), MeasurableSet s → (∀ x ∈ s, DifferentiableAt ℝ Φ x) → (∀ x ∈ s, Function.Injective (fderiv ℝ Φ x)) → InjOn Φ s → ∫⁻ y in Φ '' s, g y ∂μHE[n] = ∫⁻ x in s, ENNReal.ofReal (areaJacobian (fderiv ℝ Φ x)) * g (Φ x) ∂μHE[n] := by
  intro n N s Φ g hs hΦ hreg hinj
  -- Step 1: the density `J x = ofReal (areaJacobian (DΦ x))` is Borel (and finite everywhere):
  -- `x ↦ DΦ x` is Borel and `L ↦ √det(L* ∘ L)` is continuous.
  have hJmeas : Measurable (fun x : Rn n ↦ ENNReal.ofReal (areaJacobian (fderiv ℝ Φ x))) := by
    have hc : Continuous (fun L : Rn n →L[ℝ] Rn N ↦ areaJacobian L) :=
      Real.continuous_sqrt.comp (ContinuousLinearMap.continuous_det.comp
        (Continuous.clm_comp ContinuousLinearMap.adjoint.continuous continuous_id))
    exact (hc.measurable.comp (measurable_fderiv ℝ Φ)).ennreal_ofReal
  -- Step 2: `Φ|_s` (continuous and injective on the Borel set `s`) and the inclusion of `s` are
  -- measurable embeddings.
  have hcont : ContinuousOn Φ s := fun x hx ↦ (hΦ x hx).continuousAt.continuousWithinAt
  have hemb : MeasurableEmbedding (s.domRestrict Φ) := hcont.measurableEmbedding hs hinj
  have hsub := MeasurableEmbedding.subtype_coe hs
  -- Step 3: `(Φ|_s)_* ι^*(J · Hⁿ) = Hⁿ ⌊ Φ(s)`. On a Borel `t`, both sides are computed on the Borel
  -- set `C = ι((Φ|_s)⁻¹ t) = s ∩ Φ⁻¹(t) ⊆ s`, where the area formula gives `∫_C J dHⁿ = Hⁿ(Φ(C))`,
  -- and `Φ(C) = Φ(s) ∩ t`.
  have hmap : Measure.map (s.domRestrict Φ)
      (((μHE[n] : Measure (Rn n)).withDensity
        (fun x ↦ ENNReal.ofReal (areaJacobian (fderiv ℝ Φ x)))).comap (Subtype.val : s → Rn n)) =
        (μHE[n] : Measure (Rn N)).restrict (Φ '' s) := by
    ext t ht
    rw [Measure.map_apply hemb.measurable ht, hsub.comap_apply]
    have hCm : MeasurableSet (Subtype.val '' ((s.domRestrict Φ) ⁻¹' t)) :=
      hsub.measurableSet_image' (hemb.measurable ht)
    have hCs : Subtype.val '' ((s.domRestrict Φ) ⁻¹' t) ⊆ s := by
      rintro x ⟨v, _, rfl⟩
      exact v.property
    rw [withDensity_apply _ hCm,
      ← Submission.variation_injective_area_formula n N _ Φ hCm (fun x hx ↦ hΦ x (hCs hx))
        (fun x hx ↦ hreg x (hCs hx)) (hinj.mono hCs), Measure.restrict_apply ht]
    congr 1
    ext y
    constructor
    · rintro ⟨x, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨hv, ⟨v, v.property, rfl⟩⟩
    · rintro ⟨hy, x, hx, rfl⟩
      exact ⟨x, ⟨⟨x, hx⟩, hy, rfl⟩, rfl⟩
  -- Step 4: transport the arbitrary weight `g`: `lintegral_map` along the embedding `Φ|_s`, then
  -- back from the subtype `s`, then through the finite Borel density `J`.
  rw [← hmap, hemb.lintegral_map]
  change (∫⁻ x : s, (fun x : Rn n ↦ g (Φ x)) x ∂
    (((μHE[n] : Measure (Rn n)).withDensity
      (fun x ↦ ENNReal.ofReal (areaJacobian (fderiv ℝ Φ x)))).comap (Subtype.val : s → Rn n))) = _
  rw [lintegral_subtype_comap hs (fun x : Rn n ↦ g (Φ x)),
    setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀ _ _ _ hs]
  · rfl
  · simp only [eventually_true, ENNReal.ofReal_lt_top]
  · exact hJmeas.aemeasurable
/-- **Simon Ch. 2, 4.11 (p. 58), linear form of `J_{f∘ψ} = J_ψ · J^M_f`.** For continuous linear
`L : ℝⁿ → ℝᴺ`, `A : ℝᴺ → ℝ^{N'}` and `T = range L ⊆ ℝᴺ` (with the induced inner product and the
inclusion `ι_T`), `J(A ∘ L) = J(A ∘ ι_T) · J(L)`. Each area Jacobian `√det(K* ∘ K)` equals Mathlib's
`LinearMap.normDet K` (`ContinuousLinearMap.normDet_sq`, `LinearMap.normDet_nonneg`), and
`LinearMap.normDet_comp` factors `normDet (A ∘ₗ L)` through `range L`. `L` need not be injective. -/
theorem Submission.variation_areaJacobian_chain_rule : ∀ (n N N' : ℕ) (L : Rn n →L[ℝ] Rn N) (A : Rn N →L[ℝ] Rn N') (T : Submodule ℝ (Rn N)), T = LinearMap.range L.toLinearMap → areaJacobian (A.comp L) = areaJacobian (A.comp T.subtypeL) * areaJacobian L := by
  intro n N N' L A T hT
  -- Step 2: replace `T` by `range L`.
  subst hT
  -- Step 1: `areaJacobian K = √(normDet K ^ 2) = normDet K` for `K` with finite-dimensional source.
  have hJ : ∀ {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (K : E →L[ℝ] F), areaJacobian K = (K : E →ₗ[ℝ] F).normDet := by
    intro E F _ _ _ _ _ _ _ K
    have h := K.normDet_sq
    simp only [RCLike.ofReal_real_eq_id, id] at h
    rw [areaJacobian, ← h, Real.sqrt_sq (LinearMap.normDet_nonneg _)]
  -- Steps 3–5: `normDet (A ∘ₗ L) = normDet (A.domRestrict (range L)) * normDet L`, and
  -- `A.domRestrict (range L)` is by definition the linear map underlying `A ∘ ι_T`.
  rw [hJ, hJ, hJ]
  exact LinearMap.normDet_comp (L : Rn n →ₗ[ℝ] Rn N) (A : Rn N →ₗ[ℝ] Rn N')

/-- **Simon Ch. 2, after 4.12 (p. 58), area formula for `f` on one chart of `M`.** Let
`(V, W, ψ)` be a `C¹` local representation of `M` with `T_{ψ(x)} M = range Dψ(x)` for `x ∈ V`, and
let `B ⊆ W ∩ M` be Borel. If `f` is differentiable at every point of `B`, with injective
derivative, and `f` is injective on `B`, then `Hⁿ(f(B)) = ∫_B J^M_f dHⁿ`, where
`J^M_f(y) = J(Df(y) ∘ ι_y)`. Proof: pull `B` back to the Borel set `B' = V ∩ ψ⁻¹(B)`, apply the area
formula 3.2 to `f ∘ ψ` on `B'`, factor `J_{f∘ψ} = J_ψ · (J^M_f ∘ ψ)` by 4.11, and push the integral
forward to `ψ(B') = B` by the weighted area formula 3.5 for `ψ`. -/
theorem Submission.variation_chart_image_area : ∀ (n N N' : ℕ) (M : Set (Rn N)) (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N) (f : Rn N → Rn N') (B : Set (Rn N)), Chapter02.IsSimonLocalRepresentation 1 M V W ψ → (∀ x ∈ V, tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap) → MeasurableSet B → B ⊆ W ∩ M → (∀ y ∈ B, DifferentiableAt ℝ f y) → (∀ y ∈ B, Function.Injective (fderiv ℝ f y)) → InjOn f B → μHE[n] (f '' B) = ∫⁻ y in B, ENNReal.ofReal (areaJacobian ((fderiv ℝ f y).comp (tangentSpace M y).subtypeL)) ∂μHE[n] := by
  intro n N N' M V W ψ f B hrep hT hB hBWM hfd hfinj hfB
  -- Step 1: `V` is open and `ψ` is `C¹` on `V`, so `ψ` is differentiable at every point of `V`.
  have hV : IsOpen V := hrep.isOpen_source
  have hψd : ∀ x ∈ V, DifferentiableAt ℝ ψ x := fun x hx ↦
    (hrep.contDiffOn.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hx)
  -- Step 2: `B' = V ∩ ψ⁻¹(B)` is Borel: it is the image under the inclusion of the open set `V`
  -- of the preimage of `B` under the continuous restriction `ψ|_V`.
  have hB' : MeasurableSet (V ∩ ψ ⁻¹' B) := by
    rw [← Subtype.image_preimage_coe]
    exact (MeasurableEmbedding.subtype_coe hV.measurableSet).measurableSet_image'
      ((continuousOn_iff_continuous_domRestrict.mp hrep.contDiffOn.continuousOn).measurable hB)
  -- Step 3: `ψ(B') = ψ(V) ∩ B = B`, since `B ⊆ W ∩ M = ψ(V)`.
  have hψB : ψ '' (V ∩ ψ ⁻¹' B) = B := by
    rw [image_inter_preimage, hrep.image_eq, inter_eq_right.mpr hBWM]
  -- Step 4: `F = f ∘ ψ` is differentiable on `B'` with injective derivative
  -- `DF(x) = Df(ψ x) ∘ Dψ(x)`, and `F` is injective on `B'`.
  have hF : ∀ x ∈ V ∩ ψ ⁻¹' B, fderiv ℝ (f ∘ ψ) x = (fderiv ℝ f (ψ x)).comp (fderiv ℝ ψ x) :=
    fun x hx ↦ fderiv_comp x (hfd (ψ x) hx.2) (hψd x hx.1)
  have hFd : ∀ x ∈ V ∩ ψ ⁻¹' B, DifferentiableAt ℝ (f ∘ ψ) x :=
    fun x hx ↦ (hfd (ψ x) hx.2).comp x (hψd x hx.1)
  have hFreg : ∀ x ∈ V ∩ ψ ⁻¹' B, Function.Injective (fderiv ℝ (f ∘ ψ) x) := by
    intro x hx
    rw [hF x hx, ContinuousLinearMap.coe_comp]
    exact (hfinj (ψ x) hx.2).comp (hrep.injective_fderiv hx.1)
  have hFinj : InjOn (f ∘ ψ) (V ∩ ψ ⁻¹' B) := by
    intro x hx x' hx' h
    have hψx : ψ x ∈ B := hx.2
    have hψx' : ψ x' ∈ B := hx'.2
    exact hrep.injOn hx.1 hx'.1 (hfB hψx hψx' h)
  -- Step 5: the area formula 3.2 for `F` on `B'`, with `F(B') = f(ψ(B')) = f(B)`.
  have h5 := Submission.variation_injective_area_formula n N' (V ∩ ψ ⁻¹' B) (f ∘ ψ) hB' hFd
    hFreg hFinj
  rw [image_comp, hψB] at h5
  -- Step 6: 4.11 with `T = T_{ψ(x)} M = range Dψ(x)` gives `J_F(x) = J^M_f(ψ x) · J_ψ(x)` on `B'`.
  have h6 : ∫⁻ x in V ∩ ψ ⁻¹' B, ENNReal.ofReal (areaJacobian (fderiv ℝ (f ∘ ψ) x)) ∂μHE[n] =
      ∫⁻ x in V ∩ ψ ⁻¹' B, ENNReal.ofReal (areaJacobian (fderiv ℝ ψ x)) *
        ENNReal.ofReal (areaJacobian ((fderiv ℝ f (ψ x)).comp (tangentSpace M (ψ x)).subtypeL))
        ∂μHE[n] := by
    refine setLIntegral_congr_fun hB' fun x hx ↦ ?_
    have h0 : 0 ≤ areaJacobian ((fderiv ℝ f (ψ x)).comp (tangentSpace M (ψ x)).subtypeL) :=
      Real.sqrt_nonneg _
    show ENNReal.ofReal (areaJacobian (fderiv ℝ (f ∘ ψ) x)) = _
    rw [hF x hx, Submission.variation_areaJacobian_chain_rule n N N' _ _ _ (hT x hx.1),
      ENNReal.ofReal_mul h0, mul_comm]
  -- Step 7: the weighted area formula 3.5 for `ψ` on `B'` with weight `J^M_f`, and `ψ(B') = B`.
  have h7 := Submission.variation_injective_weighted_area_formula n N (V ∩ ψ ⁻¹' B) ψ
    (fun y ↦ ENNReal.ofReal (areaJacobian ((fderiv ℝ f y).comp (tangentSpace M y).subtypeL)))
    hB' (fun x hx ↦ hψd x hx.1) (fun x hx ↦ hrep.injective_fderiv hx.1)
    (hrep.injOn.mono inter_subset_left)
  rw [hψB] at h7
  -- Step 8: combine steps 5–7.
  exact h5.trans (h6.trans h7.symm)

/-- **Area formula for an injective image of a Borel subset of a `C¹` submanifold** (Simon Ch. 2,
p. 58, after 4.12; used on p. 62 for `Hⁿ(φ_t(M ∩ K))`): `Hⁿ(f(S)) = ∫_S J dHⁿ` with
`J(y) = √det(L_y* L_y)` and `L_y = Df(y)|_{T_y M}`. The charts of `M` have a countable subcover
`W (e k)` (Lindelöf), and the disjoint Borel pieces `B k = disjointed (S ∩ W (e k))` exhaust `S`.
`variation_chart_image_area` gives the formula on each `B k`. Lusin–Souslin makes the images
`f(B k)` Borel and injectivity of `f` on `S` makes them disjoint, so countable additivity of `Hⁿ`
and of the set integral gives the formula on `S`. -/
theorem Submission.variation_submanifold_image_area : ∀ (n N N' : ℕ) (M S : Set (Rn N)) (f : Rn N → Rn N'), Chapter02.IsSimonSubmanifold (E := Rn n) 1 M → (∀ (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N), Chapter02.IsSimonLocalRepresentation 1 M V W ψ → ∀ x ∈ V, tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap) → MeasurableSet S → S ⊆ M → (∀ y ∈ S, DifferentiableAt ℝ f y) → (∀ y ∈ S, Function.Injective (fderiv ℝ f y)) → InjOn f S → μHE[n] (f '' S) = ∫⁻ y in S, ENNReal.ofReal (areaJacobian ((fderiv ℝ f y).comp (tangentSpace M y).subtypeL)) ∂μHE[n] := by
  intro n N N' M S f hM hT hS hSM hfd hfi hinj
  -- Step 2: for `S = ∅` both sides vanish.
  rcases S.eq_empty_or_nonempty with rfl | ⟨y₀, hy₀⟩
  · simp
  -- Step 3: a chart `(V z, W z, ψ z)` around every `z ∈ M`; countably many `W (e k)` cover `S`.
  choose V W ψ hzW hrep using fun z : M ↦ hM.exists_localRepresentation z.2
  obtain ⟨T, hTc, hTW⟩ :=
    TopologicalSpace.isOpen_iUnion_countable W fun z ↦ (hrep z).isOpen_target
  have hcov : ∀ y ∈ S, ∃ z ∈ T, y ∈ W z := by
    intro y hy
    have hy' : y ∈ ⋃ z ∈ T, W z := hTW ▸ mem_iUnion.2 ⟨⟨y, hSM hy⟩, hzW _⟩
    simpa only [mem_iUnion, exists_prop] using hy'
  obtain ⟨z₀, hz₀, -⟩ := hcov y₀ hy₀
  obtain ⟨e, rfl⟩ := hTc.exists_eq_range ⟨z₀, hz₀⟩
  -- Step 4: disjoint Borel pieces `B k ⊆ S ∩ W (e k)` with union `S`.
  set B : ℕ → Set (Rn N) := disjointed fun k ↦ S ∩ W (e k) with hB
  have hBm : ∀ k, MeasurableSet (B k) :=
    MeasurableSet.disjointed fun k ↦ hS.inter (hrep (e k)).isOpen_target.measurableSet
  have hBsub : ∀ k, B k ⊆ S ∩ W (e k) := disjointed_subset _
  have hBS : ∀ k, B k ⊆ S := fun k y hy ↦ (hBsub k hy).1
  have hBd : Pairwise (Function.onFun Disjoint B) := disjoint_disjointed _
  have hBU : ⋃ k, B k = S := by
    rw [hB, iUnion_disjointed, ← inter_iUnion, inter_eq_left]
    intro y hy
    obtain ⟨_, ⟨k, rfl⟩, hk⟩ := hcov y hy
    exact mem_iUnion.2 ⟨k, hk⟩
  -- Steps 5–8: the area formula on each piece, inside the single chart `e k`.
  have hpiece : ∀ k, μHE[n] (f '' B k) = ∫⁻ y in B k,
      ENNReal.ofReal (areaJacobian ((fderiv ℝ f y).comp (tangentSpace M y).subtypeL)) ∂μHE[n] :=
    fun k ↦ Submission.variation_chart_image_area n N N' M (V (e k)) (W (e k)) (ψ (e k)) f (B k)
      (hrep (e k)) (hT _ _ _ (hrep (e k))) (hBm k)
      (fun y hy ↦ ⟨(hBsub k hy).2, hSM (hBsub k hy).1⟩) (fun y hy ↦ hfd y (hBS k hy))
      (fun y hy ↦ hfi y (hBS k hy)) (hinj.mono (hBS k))
  -- Step 9: the images `f(B k)` are Borel (Lusin–Souslin) and pairwise disjoint; sum over `k`.
  have hfBm : ∀ k, MeasurableSet (f '' B k) := fun k ↦
    (hBm k).image_of_continuousOn_injOn
      (fun y hy ↦ (hfd y (hBS k hy)).continuousAt.continuousWithinAt) (hinj.mono (hBS k))
  have hfBd : Pairwise (Function.onFun Disjoint fun k ↦ f '' B k) := fun i j hij ↦
    (hBd hij).image hinj (hBS i) (hBS j)
  rw [← hBU, image_iUnion, measure_iUnion hfBd hfBm, lintegral_iUnion hBm hBd]
  exact tsum_congr hpiece
/-- **Leibniz-form derivative of `t ↦ det G(t)`.** If every entry `s ↦ G(s)ᵢₖ` has derivative `Hᵢₖ`
at `x`, then `t ↦ det G(t)` has derivative
`∑_σ sgn σ ∑_m (∏_{j ≠ m} G(x)_{σ(j) j}) H_{σ(m) m}` at `x`. Expand `det G(t)` by the Leibniz
formula (`Matrix.det_apply'`), then apply the finite product rule (`HasDerivAt.fun_finsetProd`) to
each `∏ᵢ G(t)_{σ(i) i}`, the constant-multiple rule for `sgn σ` and the finite sum rule over
`Perm ι`. -/
theorem Submission.variation_matrix_det_hasDerivAt_leibniz : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : ℝ → Matrix ι ι ℝ) (H : Matrix ι ι ℝ) (x : ℝ), (∀ i k, HasDerivAt (fun s ↦ G s i k) (H i k) x) → HasDerivAt (fun t ↦ (G t).det) (∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∑ m : ι, (∏ j ∈ Finset.univ.erase m, G x (σ j) j) * H (σ m) m) x := by
  intro ι _ _ G H x hG
  -- Step 1: Leibniz expansion `det G(t) = ∑_σ sgn σ ∏ᵢ G(t)_{σ(i) i}`.
  simp_rw [Matrix.det_apply']
  -- Steps 4 and 3: sum rule over `Perm ι`, then the constant factor `sgn σ`.
  refine HasDerivAt.fun_sum fun σ _ ↦ HasDerivAt.const_mul _ ?_
  -- Step 2: finite product rule for `t ↦ ∏ᵢ G(t)_{σ(i) i}`; on `ℝ`, `•` is multiplication.
  simpa only [smul_eq_mul] using HasDerivAt.fun_finsetProd (u := Finset.univ)
    (f := fun i s ↦ G s (σ i) i) (f' := fun i ↦ H (σ i) i) fun i _ ↦ hG (σ i) i
/-- **First-order Leibniz sum at the identity matrix is the trace** (Simon Ch. 2, p. 62: the
first-order term `tr A` of `det(I + A)`). For a real `ι × ι` matrix `H`,
`∑_σ sgn σ · ∑_m (∏_{j ≠ m} I_{σ j, j}) · H_{σ m, m} = tr H`. A permutation `σ ≠ 1` moves some
`j ≠ m` (a moved `y` if `y ≠ m`, else `σ m`, by injectivity), so the factor `I_{σ j, j} = 0` kills
every product and the `σ`-summand vanishes (`Finset.sum_eq_single`). The `σ = 1` summand is
`1 · ∑_m 1 · H_{m m} = tr H`. -/
theorem Submission.variation_matrix_det_leibniz_first_order_at_one : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℝ), ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∑ m : ι, (∏ j ∈ Finset.univ.erase m, (1 : Matrix ι ι ℝ) (σ j) j) * H (σ m) m = H.trace := by
  intro ι _ _ H
  -- Step 3: only the `σ = 1` summand survives.
  rw [Finset.sum_eq_single (1 : Equiv.Perm ι)]
  · -- Step 4: `sgn 1 = 1`, every `I_{j j} = 1`, and `∑_m H_{m m} = tr H`.
    have hprod : ∀ m : ι,
        ∏ j ∈ Finset.univ.erase m, (1 : Matrix ι ι ℝ) ((1 : Equiv.Perm ι) j) j = 1 :=
      fun m ↦ Finset.prod_eq_one fun j _ ↦ Matrix.one_apply_eq j
    simp [hprod, Matrix.trace]
  · intro σ _ hσ
    -- Step 1: `σ ≠ 1` moves some `y`.
    obtain ⟨y, hy⟩ : ∃ y, σ y ≠ y := not_forall.1 fun h ↦ hσ (Equiv.ext h)
    -- Step 2: for each `m`, a moved `j ≠ m` gives the zero factor `I_{σ j, j}`.
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun m _ ↦ ?_)
    obtain ⟨j, hjm, hj⟩ : ∃ j, j ≠ m ∧ σ j ≠ j := by
      by_cases hym : y = m
      · rw [hym] at hy
        exact ⟨σ m, hy, fun h ↦ hy (σ.injective h)⟩
      · exact ⟨y, hym, hy⟩
    have hzero : ∏ j ∈ Finset.univ.erase m, (1 : Matrix ι ι ℝ) (σ j) j = 0 :=
      Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hjm, Finset.mem_univ j⟩) (Matrix.one_apply_ne hj)
    rw [hzero, zero_mul]
  · exact fun h ↦ absurd (Finset.mem_univ _) h
/-- **Simon Ch. 2, §5 (p. 62), second-order term of `det (I + A)`.** The second-order Leibniz sum
at the identity matrix: for `m ≠ l` the product `∏_{j ∉ {m, l}} I_{σ j, j}` vanishes unless `σ` is
`1` or the transposition `(m l)`, so the sum is `∑_{m ≠ l} (B_ll B_mm - B_ml B_lm)`, which equals
`(tr B)² - tr (B B)`, twice the coefficient `½ (tr A)² - ½ tr (A²)` of Simon's formula. -/
theorem Submission.variation_matrix_det_leibniz_second_order_at_one : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℝ), ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∑ m : ι, (∑ l ∈ Finset.univ.erase m, (∏ j ∈ (Finset.univ.erase m).erase l, (1 : Matrix ι ι ℝ) (σ j) j) * B (σ l) l) * B (σ m) m = B.trace ^ 2 - (B * B).trace := by
  intro ι _ _ B
  -- Step 2: for `m ≠ l`, a permutation fixing every `j ∉ {m, l}` is `1` or `swap m l`.
  have hclass : ∀ (m l : ι) (σ : Equiv.Perm ι), m ≠ l → (∀ j, j ≠ m → j ≠ l → σ j = j) →
      σ = 1 ∨ σ = Equiv.swap m l := by
    intro m l σ hml h
    -- `σ` sends every point it moves into `{m, l}`, since it also moves the image.
    have hmoved : ∀ y, σ y ≠ y → σ y = m ∨ σ y = l := by
      intro y hy
      by_contra hc
      exact hy (σ.injective (h (σ y) (fun e => hc (Or.inl e)) (fun e => hc (Or.inr e))))
    by_cases hm : σ m = m
    · have hl : σ l = l := by
        by_contra hl
        rcases hmoved l hl with h1 | h1
        · exact hml (σ.injective (hm.trans h1.symm))
        · exact hl h1
      left
      ext j
      by_cases hjm : j = m
      · subst hjm; simpa using hm
      by_cases hjl : j = l
      · subst hjl; simpa using hl
      simpa using h j hjm hjl
    · have hm' : σ m = l := (hmoved m hm).resolve_left hm
      have hl' : σ l = m := by
        have hl : σ l ≠ l := fun hl => hml (σ.injective (hm'.trans hl.symm))
        exact (hmoved l hl).resolve_right hl
      right
      ext j
      by_cases hjm : j = m
      · subst hjm; simp [hm']
      by_cases hjl : j = l
      · subst hjl; simp [hl']
      rw [h j hjm hjl, Equiv.swap_apply_of_ne_of_ne hjm hjl]
  -- Steps 3–4: for `m ≠ l` only `σ = 1` and `σ = swap m l` contribute to the `σ`-sum.
  have hS : ∀ m l : ι, m ≠ l →
      ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ((∏ j ∈ (Finset.univ.erase m).erase l, (1 : Matrix ι ι ℝ) (σ j) j) * B (σ l) l * B (σ m) m)
        = B l l * B m m - B m l * B l m := by
    intro m l hml
    have hne : (1 : Equiv.Perm ι) ≠ Equiv.swap m l := by
      intro h
      have h' := congrArg (fun τ : Equiv.Perm ι => τ m) h
      simp only [Equiv.Perm.coe_one, id_eq, Equiv.swap_apply_left] at h'
      exact hml h'
    rw [← Finset.sum_subset (Finset.subset_univ {1, Equiv.swap m l}) ?_]
    · rw [Finset.sum_pair hne]
      have hP1 :
          ∏ j ∈ (Finset.univ.erase m).erase l, (1 : Matrix ι ι ℝ) ((1 : Equiv.Perm ι) j) j = 1 :=
        Finset.prod_eq_one fun j _ => Matrix.one_apply_eq j
      have hP2 :
          ∏ j ∈ (Finset.univ.erase m).erase l, (1 : Matrix ι ι ℝ) (Equiv.swap m l j) j = 1 := by
        refine Finset.prod_eq_one fun j hj => ?_
        rw [Finset.mem_erase, Finset.mem_erase] at hj
        rw [Equiv.swap_apply_of_ne_of_ne hj.2.1 hj.1, Matrix.one_apply_eq]
      rw [hP1, hP2, Equiv.Perm.sign_swap hml, Equiv.Perm.sign_one, Equiv.swap_apply_left,
        Equiv.swap_apply_right]
      simp only [Equiv.Perm.coe_one, id_eq, Units.val_one, Units.val_neg, Int.cast_one,
        Int.cast_neg]
      ring
    · intro σ _ hσ
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hσ
      have hP : ∏ j ∈ (Finset.univ.erase m).erase l, (1 : Matrix ι ι ℝ) (σ j) j = 0 := by
        by_contra hP
        have hfix : ∀ j, j ≠ m → j ≠ l → σ j = j := by
          intro j hjm hjl
          by_contra hj
          exact hP (Finset.prod_eq_zero
            (Finset.mem_erase.2 ⟨hjl, Finset.mem_erase.2 ⟨hjm, Finset.mem_univ j⟩⟩)
            (Matrix.one_apply_ne hj))
        rcases hclass m l σ hml hfix with h | h
        · exact hσ.1 h
        · exact hσ.2 h
      rw [hP]
      ring
  -- Step 1: distribute the products and move the `σ`-sum inside the `m`- and `l`-sums.
  calc ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∑ m : ι, (∑ l ∈ Finset.univ.erase m,
          (∏ j ∈ (Finset.univ.erase m).erase l, (1 : Matrix ι ι ℝ) (σ j) j) * B (σ l) l) * B (σ m) m
      = ∑ m : ι, ∑ l ∈ Finset.univ.erase m, ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ((∏ j ∈ (Finset.univ.erase m).erase l, (1 : Matrix ι ι ℝ) (σ j) j) * B (σ l) l *
            B (σ m) m) := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.sum_comm]
    -- Step 4: each inner `σ`-sum is `B_ll B_mm - B_ml B_lm`.
    _ = ∑ m : ι, ∑ l ∈ Finset.univ.erase m, (B l l * B m m - B m l * B l m) :=
        Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l hl =>
          hS m l (Finset.ne_of_mem_erase hl).symm
    -- Step 5: the omitted `l = m` term `B_mm B_mm - B_mm B_mm` is zero.
    _ = ∑ m : ι, ∑ l : ι, (B l l * B m m - B m l * B l m) :=
        Finset.sum_congr rfl fun m _ => Finset.sum_erase _ (sub_self _)
    -- Step 6: `∑∑ B_ll B_mm = (tr B)²` and `∑∑ B_ml B_lm = tr (B B)`.
    _ = B.trace ^ 2 - (B * B).trace := by
        simp only [Finset.sum_sub_distrib, Matrix.trace, Matrix.diag, Matrix.mul_apply, sq,
          Finset.sum_mul_sum]
        rw [Finset.sum_comm (f := fun m l => B l l * B m m)]

/-- **Derivatives of `det G(t)` where `G = I`** (derivative form of Simon's expansion
`det(I + A) = 1 + tr A + ½(tr A)² - ½ tr(A²) + O(|A|³)`, Ch. 2, p. 62). Let `G(0) = I` and
`h(t) = det G(t)`. (1) If the entries of `G` have derivatives `G₁` at `0`, then `h'(0) = tr G₁`.
(2) If near `0` the entries of `G` have derivatives `G'(t)` at `t` and those of `G'` have
derivatives `G₂` at `0`, then `h` is differentiable near `0` and
`(deriv h)'(0) = tr G₂ + (tr G'(0))² - tr(G'(0) G'(0))`. The Leibniz expansion gives, near `0`,
`h'(t) = φ(t) := ∑_σ sgn σ ∑_m (∏_{j ≠ m} G(t)_{σ(j) j}) G'(t)_{σ(m) m}`. The product and sum
rules give `φ'(0)`. At `G(0) = I` its two parts are `tr G₂` and `(tr B)² - tr(B B)`, `B = G'(0)`. -/
theorem Submission.variation_matrix_det_derivatives_at_one : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : ℝ → Matrix ι ι ℝ), G 0 = 1 → (∀ G₁ : Matrix ι ι ℝ, (∀ i k, HasDerivAt (fun t ↦ G t i k) (G₁ i k) 0) → HasDerivAt (fun t ↦ (G t).det) G₁.trace 0) ∧ ∀ (G' : ℝ → Matrix ι ι ℝ) (G₂ : Matrix ι ι ℝ), (∀ᶠ t in 𝓝 0, ∀ i k, HasDerivAt (fun s ↦ G s i k) (G' t i k) t) → (∀ i k, HasDerivAt (fun t ↦ G' t i k) (G₂ i k) 0) → (∀ᶠ t in 𝓝 0, DifferentiableAt ℝ (fun s ↦ (G s).det) t) ∧ HasDerivAt (deriv (fun t ↦ (G t).det)) (G₂.trace + (G' 0).trace ^ 2 - (G' 0 * G' 0).trace) 0 := by
  intro ι _ _ G hG0
  refine ⟨fun G₁ hG₁ ↦ ?_, fun G' G₂ hG' hG₂ ↦ ?_⟩
  · -- Step 5: the Leibniz derivative at `0` with `H = G₁` is the first-order sum at `G 0 = 1`,
    -- which is `tr G₁`.
    have h := Submission.variation_matrix_det_hasDerivAt_leibniz ι G G₁ 0 hG₁
    rwa [hG0, Submission.variation_matrix_det_leibniz_first_order_at_one] at h
  · -- Step 6: near `0`, `h` has derivative `φ t` at `t`, so `h` is differentiable there.
    have hdet : ∀ᶠ t in 𝓝 0, HasDerivAt (fun s ↦ (G s).det)
        (∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∑ m : ι, (∏ j ∈ Finset.univ.erase m, G t (σ j) j) * G' t (σ m) m) t :=
      hG'.mono fun t ht ↦ Submission.variation_matrix_det_hasDerivAt_leibniz ι G (G' t) t ht
    refine ⟨hdet.mono fun t ht ↦ ht.differentiableAt, ?_⟩
    -- Step 7: as `0` lies in the neighbourhood, the entries of `G` have derivatives `G' 0` at `0`.
    -- The finite product, product, constant-multiple and sum rules give `φ'(0)`.
    have hG'0 : ∀ i k, HasDerivAt (fun s ↦ G s i k) (G' 0 i k) 0 := hG'.self_of_nhds
    have hφ : HasDerivAt (fun t ↦ ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∑ m : ι, (∏ j ∈ Finset.univ.erase m, G t (σ j) j) * G' t (σ m) m)
        (∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∑ m : ι,
          ((∑ l ∈ Finset.univ.erase m, (∏ j ∈ (Finset.univ.erase m).erase l, G 0 (σ j) j) *
              G' 0 (σ l) l) * G' 0 (σ m) m +
            (∏ j ∈ Finset.univ.erase m, G 0 (σ j) j) * G₂ (σ m) m)) 0 := by
      refine HasDerivAt.fun_sum fun σ _ ↦ (HasDerivAt.fun_sum fun m _ ↦ ?_).const_mul _
      refine HasDerivAt.fun_mul ?_ (hG₂ (σ m) m)
      simpa only [smul_eq_mul] using
        HasDerivAt.fun_finsetProd (u := Finset.univ.erase m) fun j _ ↦ hG'0 (σ j) j
    -- Step 8: with `G 0 = 1`, `φ'(0) = V₁ + V₂`, where the second-order sum `V₁` is
    -- `(tr B)² - tr (B B)` for `B = G' 0` and the first-order sum `V₂` is `tr G₂`.
    rw [hG0] at hφ
    simp only [mul_add, Finset.sum_add_distrib,
      Submission.variation_matrix_det_leibniz_second_order_at_one,
      Submission.variation_matrix_det_leibniz_first_order_at_one] at hφ
    -- Step 9: `deriv h` agrees with `φ` near `0`.
    exact (hφ.congr_deriv (by ring)).congr_of_eventuallyEq (hdet.mono fun t ht ↦ ht.deriv)
/-- **Simon Ch. 2, 5.2–5.4 (p. 63), derivatives of `√h` at a point where `h = 1`.** Let `h : ℝ → ℝ`
have `h(0) = 1` and derivative `h₁` at `0`. Then `t ↦ √h(t)` has derivative `h₁/2` at `0`. If
moreover `h` is differentiable near `0` and `deriv h` has derivative `h₂` at `0`, then
`deriv (t ↦ √h(t))` has derivative `h₂/2 - h₁²/4` at `0`. This is the derivative form of
`√(1 + x) = 1 + x/2 - x²/8 + O(x³)`, which Simon quotes without proof: near `0`,
`deriv (t ↦ √h(t)) = deriv h / (2√h)`, and the quotient rule applies at `0`. -/
theorem Submission.variation_sqrt_derivatives_at_one : ∀ (h : ℝ → ℝ) (h₁ : ℝ), h 0 = 1 → HasDerivAt h h₁ 0 → HasDerivAt (fun t ↦ Real.sqrt (h t)) (h₁ / 2) 0 ∧ ∀ h₂ : ℝ, (∀ᶠ t in 𝓝 0, DifferentiableAt ℝ h t) → HasDerivAt (deriv h) h₂ 0 → HasDerivAt (deriv (fun t ↦ Real.sqrt (h t))) (h₂ / 2 - h₁ ^ 2 / 4) 0 := by
  intro h h₁ h0 hd
  -- (1) Chain rule at `h 0 = 1`: the derivative is `h₁ / (2 * √1) = h₁ / 2`.
  have hsqrt : HasDerivAt (fun t ↦ Real.sqrt (h t)) (h₁ / 2) 0 := by
    simpa [h0] using hd.sqrt (by rw [h0]; exact one_ne_zero)
  refine ⟨hsqrt, fun h₂ hdiff hdd ↦ ?_⟩
  -- `h` is continuous at `0` and `h 0 = 1 > 0`, so `h > 0` near `0`.
  have hpos : ∀ᶠ t in 𝓝 0, 0 < h t :=
    hd.continuousAt.eventually (lt_mem_nhds (by rw [h0]; exact one_pos))
  -- Near `0`, the chain rule at `t` gives `deriv (√ ∘ h) t = deriv h t / (2 * √(h t))`.
  have heq : deriv (fun t ↦ Real.sqrt (h t)) =ᶠ[𝓝 0]
      fun t ↦ deriv h t / (2 * Real.sqrt (h t)) := by
    filter_upwards [hpos, hdiff] with t ht hdt
    exact (hdt.hasDerivAt.sqrt ht.ne').deriv
  -- Quotient rule at `0`: the numerator `deriv h` has value `h₁` and derivative `h₂`, the
  -- denominator `2 * √h` has value `2` and derivative `2 * (h₁ / 2)`.
  have hq := hdd.fun_div (hsqrt.const_mul 2) (by rw [h0, Real.sqrt_one]; norm_num)
  rw [hd.deriv, h0, Real.sqrt_one] at hq
  convert hq.congr_of_eventuallyEq heq using 1
  ring
/-- **Tangential Jacobian as an ambient Gram determinant** (Simon Ch. 2, §5, p. 62: basis-free
form of the Jacobian `J_t = √det(b_ij)` behind the variation formulas 5.3–5.4). Let `T ⊆ ℝᴺ` be
a subspace with orthogonal projection `P` and inclusion `ι_T`, and let `A : ℝᴺ → ℝ^{N'}` be
linear. Then `areaJacobian (A ∘ ι_T) = √det(I - P + P A* A P)`. With `L = A ∘ ι_T` we have
`L* = π_T ∘ A*`. In the orthogonal splitting `T × Tᗮ ≃ ℝᴺ`, `(u, w) ↦ u + w`, the operator
`Σ = I - P + P A* A P` is block diagonal, acting as `L* L` on `T` and as the identity on `Tᗮ`.
Hence `det Σ = det (L* L) · det I = det (L* L)`, also when `T = 0`. -/
theorem Submission.variation_gram_det_identity : ∀ (N N' : ℕ) (T : Submodule ℝ (Rn N)) (A : Rn N →L[ℝ] Rn N'), areaJacobian (A.comp T.subtypeL) = Real.sqrt ((1 - T.starProjection + T.starProjection ∘L ContinuousLinearMap.adjoint A ∘L A ∘L T.starProjection).det) := by
  intro N N' T A
  -- Step 1: for `L = A ∘ ι_T`, the adjoint of `ι_T` is `π_T`, so `L* = π_T ∘ A*`.
  have hadj : ContinuousLinearMap.adjoint (A.comp T.subtypeL) =
      T.orthogonalProjectionOnto ∘L ContinuousLinearMap.adjoint A := by
    rw [ContinuousLinearMap.adjoint_comp, T.adjoint_subtypeL]
  -- Step 2: the orthogonal splitting `T × Tᗮ ≃ ℝᴺ`, `(u, w) ↦ u + w`.
  let e : (T × Tᗮ) ≃ₗ[ℝ] Rn N := Submodule.prodEquivOfIsCompl T Tᗮ T.isCompl_orthogonal
  -- Step 3: block structure. Since `P u = u` for `u ∈ T` and `P w = 0` for `w ∈ Tᗮ`,
  -- `Σ (u + w) = P A* A u + w = L* L u + w`, i.e. `Σ = e ∘ (L* L × I) ∘ e⁻¹`.
  have hblock : ((1 - T.starProjection + T.starProjection ∘L ContinuousLinearMap.adjoint A ∘L
        A ∘L T.starProjection : Rn N →L[ℝ] Rn N) : Rn N →ₗ[ℝ] Rn N) =
      (e : (T × Tᗮ) →ₗ[ℝ] Rn N) ∘ₗ
        (LinearMap.prodMap ((ContinuousLinearMap.adjoint (A.comp T.subtypeL) ∘L
          A.comp T.subtypeL : T →L[ℝ] T) : T →ₗ[ℝ] T) LinearMap.id) ∘ₗ
        (e.symm : Rn N →ₗ[ℝ] (T × Tᗮ)) := by
    rw [← LinearMap.comp_assoc, LinearEquiv.eq_comp_toLinearMap_symm]
    refine LinearMap.ext fun ⟨u, w⟩ => ?_
    have hu : T.starProjection (u : Rn N) = u := T.starProjection_mem_subspace_eq_self u
    have hw : T.starProjection (w : Rn N) = 0 := T.starProjection_apply_eq_zero_iff.mpr w.2
    simp [e, hadj, hu, hw, add_comm]
  -- Steps 4-5: a block-diagonal determinant is the product of the block determinants, so
  -- `det Σ = det (L* L) · det I = det (L* L)` (also when `T = 0`); take square roots.
  unfold areaJacobian
  rw [ContinuousLinearMap.det, ContinuousLinearMap.det, hblock, LinearMap.det_conj,
    LinearMap.det_prodMap, LinearMap.det_id, mul_one]

/-- **Derivatives of the Jacobian of a linear family on a subspace** (Simon Ch. 2, §5,
pp. 62–63: the expansion of `J_t = √det(b_ij)` behind the variation formulas 5.3–5.4). Let
`T ⊆ ℝᴺ` be a subspace with orthogonal projection `P` and orthonormal basis `b`, let `A(0) = I`
and `j(t) = √det(I - P + P A(t)* A(t) P)`. (1) If `A'(0) = A₁`, then `j'(0) = ∑ᵢ ⟨bᵢ, A₁ bᵢ⟩`.
(2) If moreover `A` is differentiable near `0` and `(deriv A)'(0) = A₂`, then `deriv j` has
derivative `∑ᵢ ⟨bᵢ, A₂ bᵢ⟩ + (∑ᵢ ⟨bᵢ, A₁ bᵢ⟩)² + ∑ᵢ ‖(A₁ bᵢ)^⊥‖² - ∑ᵢ ∑ₖ ⟨bᵢ, A₁ bₖ⟩⟨bₖ, A₁ bᵢ⟩`
at `0`. By the Gram identity, `j = √det G` with `G(t)_{ik} = ⟨A(t) bᵢ, A(t) bₖ⟩` and `G(0) = I`.
The derivatives of `det G` at `I` (Jacobi's formula to second order) and of `√` at `1` give the
result; Parseval and Pythagoras in `T` turn `∑ᵢ ‖A₁ bᵢ‖² - ∑ᵢ ∑ₖ ⟨bᵢ, A₁ bₖ⟩²` into the normal
parts. -/
theorem Submission.variation_gram_det_derivatives : ∀ (N : ℕ) (T : Submodule ℝ (Rn N)) (ι : Type) [Fintype ι] (b : OrthonormalBasis ι ℝ T) (A : ℝ → Rn N →L[ℝ] Rn N), A 0 = 1 → let j : ℝ → ℝ := fun t ↦ Real.sqrt ((1 - T.starProjection + T.starProjection ∘L ContinuousLinearMap.adjoint (A t) ∘L A t ∘L T.starProjection).det); (∀ A₁ : Rn N →L[ℝ] Rn N, HasDerivAt A A₁ 0 → HasDerivAt j (∑ i, inner ℝ (b i : Rn N) (A₁ (b i : Rn N))) 0) ∧ ∀ A₁ A₂ : Rn N →L[ℝ] Rn N, (∀ᶠ t in 𝓝 0, DifferentiableAt ℝ A t) → HasDerivAt A A₁ 0 → HasDerivAt (deriv A) A₂ 0 → HasDerivAt (deriv j) (∑ i, inner ℝ (b i : Rn N) (A₂ (b i : Rn N)) + (∑ i, inner ℝ (b i : Rn N) (A₁ (b i : Rn N))) ^ 2 + ∑ i, ‖A₁ (b i : Rn N) - T.starProjection (A₁ (b i : Rn N))‖ ^ 2 - ∑ i, ∑ k, inner ℝ (b i : Rn N) (A₁ (b k : Rn N)) * inner ℝ (b k : Rn N) (A₁ (b i : Rn N))) 0 := by
  intro N T ι _ b A hA0 j
  classical
  -- Step 1: the Gram matrix `G(t)_{ik} = ⟨A(t) b_i, A(t) b_k⟩` (Simon's `b_ij`) and `j = √det G`:
  -- `j(t) = areaJacobian (A(t) ∘ ι_T)` by the Gram identity, and `(L* L).det = normDet L ^ 2`
  -- is the Gram determinant of `L b_i` for `L = A(t) ∘ ι_T`.
  let G : ℝ → Matrix ι ι ℝ := fun t ↦
    Matrix.of fun i k ↦ inner ℝ (A t (b i : Rn N)) (A t (b k : Rn N))
  have hj : j = fun t ↦ Real.sqrt (G t).det := by
    funext t
    dsimp only [j]
    rw [← Submission.variation_gram_det_identity N N T (A t), areaJacobian,
      ← ContinuousLinearMap.normDet_sq, LinearMap.normDet_sq_eq_det_gram _ b]
    rfl
  -- Step 2: `G(0) = I`, since `A(0) = I` and `b` is orthonormal.
  have hG0 : G 0 = 1 := by
    ext i k
    simp [G, hA0, Matrix.one_apply, ← Submodule.coe_inner, orthonormal_iff_ite.mp b.orthonormal]
  have hh0 : (G 0).det = 1 := by rw [hG0, Matrix.det_one]
  -- `s ↦ B(s) v` has derivative `B' v` wherever `B` has derivative `B'`.
  have happ : ∀ {B : ℝ → Rn N →L[ℝ] Rn N} {B' : Rn N →L[ℝ] Rn N} {t : ℝ} (v : Rn N),
      HasDerivAt B B' t → HasDerivAt (fun s ↦ B s v) (B' v) t := by
    intro B B' t v hB
    simpa using hB.clm_apply (hasDerivAt_const t v)
  obtain ⟨hdet1, hdet2⟩ := Submission.variation_matrix_det_derivatives_at_one ι G hG0
  refine ⟨fun A₁ hA₁ ↦ ?_, fun A₁ A₂ hdiff hA₁ hA₂ ↦ ?_⟩
  · -- Step 3(a): `Ġ(0)_{ik} = ⟨b_i, A₁ b_k⟩ + ⟨A₁ b_i, b_k⟩`.
    let G₁ : Matrix ι ι ℝ := Matrix.of fun i k ↦
      inner ℝ (b i : Rn N) (A₁ (b k : Rn N)) + inner ℝ (A₁ (b i : Rn N)) (b k : Rn N)
    have hG₁ : ∀ i k, HasDerivAt (fun t ↦ G t i k) (G₁ i k) 0 := by
      intro i k
      have h := (happ (b i : Rn N) hA₁).inner ℝ (happ (b k : Rn N) hA₁)
      rw [hA0, one_apply_eq_self, one_apply_eq_self] at h
      exact h
    -- Step 5: `h'(0) = tr Ġ(0) = 2 D` and `j'(0) = h'(0) / 2 = D`.
    have h := (Submission.variation_sqrt_derivatives_at_one (fun t ↦ (G t).det) _ hh0
      (hdet1 G₁ hG₁)).1
    rw [hj]
    convert h using 1
    simp only [G₁, Matrix.trace, Matrix.diag_apply, Matrix.of_apply, real_inner_comm (b _ : Rn N)
      (A₁ _), ← two_mul, ← Finset.mul_sum]
    ring
  · -- Step 3(b): near `0`, `Ġ(t)_{ik} = ⟨A(t) b_i, A'(t) b_k⟩ + ⟨A'(t) b_i, A(t) b_k⟩`.
    have hd0 : deriv A 0 = A₁ := hA₁.deriv
    let G' : ℝ → Matrix ι ι ℝ := fun t ↦ Matrix.of fun i k ↦
      inner ℝ (A t (b i : Rn N)) (deriv A t (b k : Rn N)) +
        inner ℝ (deriv A t (b i : Rn N)) (A t (b k : Rn N))
    have hG' : ∀ᶠ t in 𝓝 0, ∀ i k, HasDerivAt (fun s ↦ G s i k) (G' t i k) t := by
      filter_upwards [hdiff] with t ht i k
      exact (happ (b i : Rn N) ht.hasDerivAt).inner ℝ (happ (b k : Rn N) ht.hasDerivAt)
    -- `G̈(0)_{ik} = ⟨b_i, A₂ b_k⟩ + 2 ⟨A₁ b_i, A₁ b_k⟩ + ⟨A₂ b_i, b_k⟩`.
    let G₂ : Matrix ι ι ℝ := Matrix.of fun i k ↦
      (inner ℝ (b i : Rn N) (A₂ (b k : Rn N)) + inner ℝ (A₁ (b i : Rn N)) (A₁ (b k : Rn N))) +
        (inner ℝ (A₁ (b i : Rn N)) (A₁ (b k : Rn N)) + inner ℝ (A₂ (b i : Rn N)) (b k : Rn N))
    have hG₂ : ∀ i k, HasDerivAt (fun t ↦ G' t i k) (G₂ i k) 0 := by
      intro i k
      have h := ((happ (b i : Rn N) hA₁).inner ℝ (happ (b k : Rn N) hA₂)).add
        ((happ (b i : Rn N) hA₂).inner ℝ (happ (b k : Rn N) hA₁))
      rw [hA0, hd0, one_apply_eq_self, one_apply_eq_self] at h
      exact h
    -- Step 6: `h = det G` is differentiable near `0` and `h''(0) = tr G̈ + (tr Ġ)² - tr (Ġ²)`.
    obtain ⟨hhdiff, hh2⟩ := hdet2 G' G₂ hG' hG₂
    -- Step 7: `deriv j` has derivative `h''(0) / 2 - h'(0)² / 4` at `0`.
    have h := (Submission.variation_sqrt_derivatives_at_one (fun t ↦ (G t).det) _ hh0
      (hdet1 (G' 0) hG'.self_of_nhds)).2 _ hhdiff hh2
    rw [hj]
    convert h using 1
    -- Step 8: evaluate the traces at `G(0) = I`, with `a_{ik} = ⟨b_i, A₁ b_k⟩`.
    have hG'0 : ∀ i k, G' 0 i k = inner ℝ (b i : Rn N) (A₁ (b k : Rn N)) +
        inner ℝ (b k : Rn N) (A₁ (b i : Rn N)) := by
      intro i k
      simp only [G', Matrix.of_apply, hA0, hd0, one_apply_eq_self, real_inner_comm (b k : Rn N)]
    have htr1 : (G' 0).trace = 2 * ∑ i, inner ℝ (b i : Rn N) (A₁ (b i : Rn N)) := by
      simp only [Matrix.trace, Matrix.diag_apply, hG'0, ← two_mul, ← Finset.mul_sum]
    have htr2 : G₂.trace = 2 * ∑ i, inner ℝ (b i : Rn N) (A₂ (b i : Rn N)) +
        2 * ∑ i, ‖A₁ (b i : Rn N)‖ ^ 2 := by
      simp only [G₂, Matrix.trace, Matrix.diag_apply, Matrix.of_apply, real_inner_self_eq_norm_sq,
        real_inner_comm (b _ : Rn N) (A₂ _), Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      ring
    have hsq : ∀ a : ι → ι → ℝ, ∑ i, ∑ k, (a i k + a k i) * (a k i + a i k) =
        2 * ∑ i, ∑ k, a i k ^ 2 + 2 * ∑ i, ∑ k, a i k * a k i := by
      intro a
      have hc : ∑ i, ∑ k, a k i ^ 2 = ∑ i, ∑ k, a i k ^ 2 := Finset.sum_comm
      calc ∑ i, ∑ k, (a i k + a k i) * (a k i + a i k)
          = ∑ i, ∑ k, a i k ^ 2 + ∑ i, ∑ k, a k i ^ 2 + 2 * ∑ i, ∑ k, a i k * a k i := by
            simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
            ring
        _ = 2 * ∑ i, ∑ k, a i k ^ 2 + 2 * ∑ i, ∑ k, a i k * a k i := by rw [hc]; ring
    have htr3 : (G' 0 * G' 0).trace =
        2 * ∑ i, ∑ k, inner ℝ (b i : Rn N) (A₁ (b k : Rn N)) ^ 2 +
          2 * ∑ i, ∑ k, inner ℝ (b i : Rn N) (A₁ (b k : Rn N)) *
            inner ℝ (b k : Rn N) (A₁ (b i : Rn N)) := by
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, hG'0]
      exact hsq fun i k ↦ inner ℝ (b i : Rn N) (A₁ (b k : Rn N))
    -- Step 9: Parseval in `T` and Pythagoras give `‖v - P v‖² = ‖v‖² - ∑_k ⟨b_k, v⟩²`.
    have hnormal : ∀ v : Rn N,
        ‖v - T.starProjection v‖ ^ 2 = ‖v‖ ^ 2 - ∑ k, inner ℝ (b k : Rn N) v ^ 2 := by
      intro v
      have hpars : ∑ k, inner ℝ (b k : Rn N) v ^ 2 = ‖T.starProjection v‖ ^ 2 := by
        rw [Submodule.starProjection_apply, Submodule.norm_coe, ← b.sum_sq_inner_right]
        simp only [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
      have horth : inner ℝ (v - T.starProjection v) (T.starProjection v) = 0 :=
        Submodule.starProjection_inner_eq_zero v _ (T.starProjection_apply_mem v)
      have hpyth := norm_add_sq_real (v - T.starProjection v) (T.starProjection v)
      rw [sub_add_cancel, horth] at hpyth
      rw [hpars]
      linarith
    have hnsum : ∑ i, ‖A₁ (b i : Rn N) - T.starProjection (A₁ (b i : Rn N))‖ ^ 2 =
        ∑ i, ‖A₁ (b i : Rn N)‖ ^ 2 - ∑ i, ∑ k, inner ℝ (b i : Rn N) (A₁ (b k : Rn N)) ^ 2 := by
      simp only [hnormal, Finset.sum_sub_distrib]
      rw [Finset.sum_comm (f := fun i k ↦ inner ℝ (b k : Rn N) (A₁ (b i : Rn N)) ^ 2)]
    rw [htr1, htr2, htr3, hnsum]
    ring
/-- **Initial velocity, acceleration and their spatial derivatives vanish off a closed set fixed by
the family** (Simon 5.1–5.2). If `K ⊆ ℝᴺ` is closed and `φ t x = x` for `t ∈ (-1,1)` and `x ∉ K`,
then `X = initialVelocity φ` and `Z = initialAcceleration φ` vanish at every `x ∉ K`, and so do
`DX(x)` and `DZ(x)`. For `y ∉ K`, `s ↦ φ s y` is constant on the open interval `(-1,1)`, so its
derivative vanishes there (`Filter.EventuallyEq.deriv_eq`, `deriv_const`); at `t = 0` this is
`X(y) = 0`, and since `t ↦ ∂ₜφ(t,y)` vanishes near `0`, also `Z(y) = 0`. As `Kᶜ` is open, `X` and
`Z` vanish near each `x ∉ K`, so `DX(x) = DZ(x) = 0` (`Filter.EventuallyEq.fderiv_eq`,
`fderiv_const_apply`). -/
theorem Submission.variation_deformation_vanish_off_closed : ∀ (N : ℕ) (K : Set (Rn N)) (φ : ℝ → Rn N → Rn N), IsClosed K → (∀ t ∈ Ioo (-1 : ℝ) 1, ∀ x, x ∉ K → φ t x = x) → ∀ x, x ∉ K → initialVelocity φ x = 0 ∧ initialAcceleration φ x = 0 ∧ fderiv ℝ (initialVelocity φ) x = 0 ∧ fderiv ℝ (initialAcceleration φ) x = 0 := by
  intro N K φ hK hfix
  -- Steps 1–2: for `y ∉ K`, `s ↦ φ s y` equals `y` near each `t ∈ (-1,1)`, so its derivative
  -- vanishes there.
  have hderiv : ∀ y, y ∉ K → ∀ t ∈ Ioo (-1 : ℝ) 1, deriv (fun s ↦ φ s y) t = 0 := by
    intro y hy t ht
    have hconst : (fun s ↦ φ s y) =ᶠ[𝓝 t] fun _ ↦ y := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact hfix s hs y hy
    rw [hconst.deriv_eq, deriv_const]
  have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  -- Step 3: `X(y) = 0` for `y ∉ K` (step 2 at `t = 0`).
  have hX : ∀ y, y ∉ K → initialVelocity φ y = 0 := fun y hy ↦ hderiv y hy 0 h0
  -- Step 4: `Z(y) = 0` for `y ∉ K`, as `t ↦ deriv (s ↦ φ s y) t` vanishes near `0`.
  have hZ : ∀ y, y ∉ K → initialAcceleration φ y = 0 := by
    intro y hy
    have hzero : (fun t ↦ deriv (fun s ↦ φ s y) t) =ᶠ[𝓝 0] fun _ ↦ (0 : Rn N) := by
      filter_upwards [isOpen_Ioo.mem_nhds h0] with t ht
      exact hderiv y hy t ht
    change deriv (fun t ↦ deriv (fun s ↦ φ s y) t) 0 = 0
    rw [hzero.deriv_eq, deriv_const]
  -- Step 5: `Kᶜ` is an open neighbourhood of `x` on which `X` and `Z` vanish.
  intro x hx
  have hnhds : Kᶜ ∈ 𝓝 x := hK.isOpen_compl.mem_nhds hx
  have hXloc : initialVelocity φ =ᶠ[𝓝 x] fun _ ↦ (0 : Rn N) := by
    filter_upwards [hnhds] with y hy
    exact hX y hy
  have hZloc : initialAcceleration φ =ᶠ[𝓝 x] fun _ ↦ (0 : Rn N) := by
    filter_upwards [hnhds] with y hy
    exact hZ y hy
  -- Step 6: combine.
  refine ⟨hX x hx, hZ x hx, ?_, ?_⟩
  · rw [hXloc.fderiv_eq, fderiv_const_apply]
  · rw [hZloc.fderiv_eq, fderiv_const_apply]
/-- **Partial derivatives of a jointly `C^n` family.** Let `O ⊆ ℝ × ℝᴺ` be open, let
`F(t, x) = Φ t x` be `C^n` on `O`, and let `m + 1 ≤ n`. Then the spatial derivative
`(t, x) ↦ fderiv ℝ (Φ t) x` and the time derivative `(t, x) ↦ deriv (s ↦ Φ s x) t` are `C^m` on
`O`. On `O` they equal `DF(t, x) ∘ inr` and `DF(t, x) (1, 0)` (chain rule along `x' ↦ (t, x')` and
`s ↦ (s, x)`), and `p ↦ DF(p)` is `C^m` on `O` (`ContDiffOn.fderiv_of_isOpen`). -/
theorem Submission.variation_deformation_partials_contDiffOn : ∀ (N : ℕ) (Φ : ℝ → Rn N → Rn N) (O : Set (ℝ × Rn N)) (m n : WithTop ℕ∞), IsOpen O → ContDiffOn ℝ n (fun p : ℝ × Rn N ↦ Φ p.1 p.2) O → m + 1 ≤ n → ContDiffOn ℝ m (fun p : ℝ × Rn N ↦ fderiv ℝ (Φ p.1) p.2) O ∧ ContDiffOn ℝ m (fun p : ℝ × Rn N ↦ deriv (fun s ↦ Φ s p.2) p.1) O := by
  intro N Φ O m n hO hF hmn
  -- Step 1: `0 < 1 ≤ m + 1 ≤ n`, so `F` is differentiable at every point of the open set `O`.
  have hn : n ≠ 0 := (zero_lt_one.trans_le (le_add_self.trans hmn)).ne'
  have hdiff : ∀ p ∈ O, DifferentiableAt ℝ (fun p : ℝ × Rn N ↦ Φ p.1 p.2) p := fun p hp ↦
    (hF.contDiffAt (hO.mem_nhds hp)).differentiableAt hn
  -- Step 2: `p ↦ DF(p)` is `C^m` on `O`.
  have hDF : ContDiffOn ℝ m (fderiv ℝ fun p : ℝ × Rn N ↦ Φ p.1 p.2) O :=
    hF.fderiv_of_isOpen hO hmn
  constructor
  · -- Steps 3–4: `fderiv ℝ (Φ t) x = DF(t, x) ∘ inr` on `O`, by the chain rule along `x' ↦ (t, x')`.
    refine (hDF.clm_comp (contDiffOn_const (c := ContinuousLinearMap.inr ℝ ℝ (Rn N)))).congr ?_
    rintro ⟨t, x⟩ hp
    exact ((hdiff (t, x) hp).hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)).fderiv
  · -- Steps 5–6: `deriv (s ↦ Φ s x) t = DF(t, x) (1, 0)` on `O`, by the chain rule along `s ↦ (s, x)`.
    refine (hDF.clm_apply (contDiffOn_const (c := ((1 : ℝ), (0 : Rn N))))).congr ?_
    rintro ⟨t, x⟩ hp
    exact ((hdiff (t, x) hp).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))).deriv
/-- **Simon Ch. 2, §5 (p. 62), mixed partials of a deformation.** The expansion
`D_τ φ_t = τ + t D_τ X + (t²/2) D_τ Z + O(t³)` "by 5.2" interchanges `∂_t` and `D_x`. Here, for
`F(s, x) = Φ s x` that is `C²` at `(t, y)`, `s ↦ DΦ_s(y)` has derivative `D(x ↦ ∂_s Φ(t, x))(y)` at
`t`. Both sides equal `M(t, y) = D²F(t, y)(1, 0) ∘ inr`. For the left side this is the chain rule.
For the right side, `x ↦ ∂_s Φ(t, x)` is the pointwise limit of the quotients
`h⁻¹ (Φ (t + h) - Φ t)` as `h → 0`. Their spatial derivatives `h⁻¹ (D_x F(t + h, ·) - D_x F(t, ·))`
converge to `M(t, ·)` uniformly near `y`, by the mean value theorem and the continuity of `D²F` at
`(t, y)`. The uniform limit theorem for derivatives then applies. -/
theorem Submission.variation_deformation_mixed_partial : ∀ (N : ℕ) (Φ : ℝ → Rn N → Rn N) (t : ℝ) (y : Rn N), ContDiffAt ℝ 2 (fun p : ℝ × Rn N ↦ Φ p.1 p.2) (t, y) → HasDerivAt (fun s ↦ fderiv ℝ (Φ s) y) (fderiv ℝ (fun x ↦ deriv (fun s ↦ Φ s x) t) y) t := by
  intro N Φ t y hF
  -- `F(s, x) = Φ s x`, `e₀ = (1, 0)`, `L = inr`, and `M p = D²F(p) e₀ ∘ L`, the time derivative of
  -- the spatial derivative `D_x F = DF ∘ L`.
  set F : ℝ × Rn N → Rn N := fun p ↦ Φ p.1 p.2
  set e₀ : ℝ × Rn N := (1, 0)
  set L : Rn N →L[ℝ] ℝ × Rn N := ContinuousLinearMap.inr ℝ ℝ (Rn N)
  set M : ℝ × Rn N → (Rn N →L[ℝ] Rn N) := fun p ↦ (fderiv ℝ (fderiv ℝ F) p e₀).comp L
  -- Step 1: `F` is `C²` on a ball `B = B_r(t, y)`. On `B`, `F` and `DF` are differentiable and
  -- `D²F` is continuous.
  obtain ⟨u, hu, hFu⟩ := hF.contDiffOn le_rfl (by simp)
  obtain ⟨r, hr, hru⟩ := Metric.mem_nhds_iff.mp hu
  have hB : IsOpen (ball (t, y) r) := isOpen_ball
  have hFB : ContDiffOn ℝ 2 F (ball (t, y) r) := hFu.mono hru
  have hDF : ContDiffOn ℝ 1 (fderiv ℝ F) (ball (t, y) r) :=
    hFB.fderiv_of_isOpen hB (by norm_num)
  have hD2 : ContDiffOn ℝ 0 (fderiv ℝ (fderiv ℝ F)) (ball (t, y) r) :=
    hDF.fderiv_of_isOpen hB (by norm_num)
  have hF1 : ∀ p ∈ ball (t, y) r, HasFDerivAt F (fderiv ℝ F p) p := fun p hp ↦
    ((hFB.differentiableOn (by norm_num)) p hp).differentiableAt (hB.mem_nhds hp) |>.hasFDerivAt
  have hF2 : ∀ p ∈ ball (t, y) r, HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) p) p :=
    fun p hp ↦
      ((hDF.differentiableOn (by norm_num)) p hp).differentiableAt (hB.mem_nhds hp) |>.hasFDerivAt
  have hmem : ∀ s x, |s - t| < r → dist x y < r → (s, x) ∈ ball (t, y) r := by
    intro s x hs hx
    rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq]
    exact ⟨hs, hx⟩
  have hpath : ∀ (s : ℝ) (x : Rn N), HasDerivAt (fun σ : ℝ ↦ (σ, x)) e₀ s := fun s x ↦
    (hasDerivAt_id s).prodMk (hasDerivAt_const s x)
  -- Step 2 (chain rule at points `(s, x)` of `B`): `D(Φ s)(x) = DF(s, x) ∘ L`,
  -- `∂_s Φ(s, x) = DF(s, x) e₀`, and `σ ↦ DF(σ, x) ∘ L` has derivative `M(s, x)` at `s`.
  have ha : ∀ s x, (s, x) ∈ ball (t, y) r → HasFDerivAt (Φ s) ((fderiv ℝ F (s, x)).comp L) x :=
    fun s x hp ↦ (hF1 (s, x) hp).comp x (hasFDerivAt_prodMk_right s x)
  have hb : ∀ s x, (s, x) ∈ ball (t, y) r →
      HasDerivAt (fun σ ↦ Φ σ x) (fderiv ℝ F (s, x) e₀) s :=
    fun s x hp ↦ by
      have h := (hF1 (s, x) hp).comp_hasDerivAt s (hpath s x)
      exact h
  have hc : ∀ s x, (s, x) ∈ ball (t, y) r →
      HasDerivAt (fun σ ↦ (fderiv ℝ F (σ, x)).comp L) (M (s, x)) s := by
    intro s x hp
    have h1 : HasDerivAt (fun σ ↦ fderiv ℝ F (σ, x)) (fderiv ℝ (fderiv ℝ F) (s, x) e₀) s :=
      (hF2 (s, x) hp).comp_hasDerivAt s (hpath s x)
    simpa using h1.clm_comp (hasDerivAt_const s L)
  -- Step 3: `x ↦ ∂_s Φ(t, x)` has derivative `M(t, y)` at `y`. It is the pointwise limit of
  -- `f h = h⁻¹ (Φ (t + h) - Φ t)` as `h → 0`, `h ≠ 0`, and the derivatives
  -- `f' h = h⁻¹ (D_x F(t + h, ·) - D_x F(t, ·))` converge to `M(t, ·)` uniformly near `y`.
  have key : HasFDerivAt (fun x ↦ deriv (fun s ↦ Φ s x) t) (M (t, y)) y := by
    refine hasFDerivAt_of_tendstoUniformlyOnFilter (l := 𝓝[≠] (0 : ℝ))
      (f := fun h x ↦ h⁻¹ • (Φ (t + h) x - Φ t x))
      (f' := fun h x ↦ h⁻¹ • ((fderiv ℝ F (t + h, x)).comp L - (fderiv ℝ F (t, x)).comp L))
      (g' := fun x ↦ M (t, x)) ?_ ?_ ?_
    · -- Uniform convergence of `f'`: given `ε`, take `δ` from the continuity of `M` at `(t, y)`.
      rw [Metric.tendstoUniformlyOnFilter_iff]
      intro ε hε
      have hMc : ContinuousAt M (t, y) :=
        ((hD2.continuousOn.continuousAt (hB.mem_nhds (mem_ball_self hr))).clm_apply
          continuousAt_const).clm_comp continuousAt_const
      obtain ⟨δ, hδ, hδM⟩ := Metric.continuousAt_iff.mp hMc (ε / 2) (half_pos hε)
      have hδ' : 0 < min δ r := lt_min hδ hr
      have hev1 : ∀ᶠ h in 𝓝[≠] (0 : ℝ), |h| < min δ r ∧ h ≠ 0 := by
        filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds (0 : ℝ) hδ'), self_mem_nhdsWithin]
          with h h1 h2
        refine ⟨?_, h2⟩
        rwa [mem_ball, Real.dist_eq, sub_zero] at h1
      have hev2 : ∀ᶠ x in 𝓝 y, dist x y < min δ r := ball_mem_nhds y hδ'
      filter_upwards [hev1.prod_mk hev2]
      rintro ⟨h, x⟩ ⟨⟨hh, hh0⟩, hx⟩
      dsimp only
      have hxδ : dist x y < δ := lt_of_lt_of_le hx (min_le_left _ _)
      have hxr : dist x y < r := lt_of_lt_of_le hx (min_le_right _ _)
      have hclose : ∀ σ, |σ - t| < min δ r → dist (M (σ, x)) (M (t, y)) < ε / 2 := by
        intro σ hσ
        apply hδM
        rw [Prod.dist_eq, max_lt_iff, Real.dist_eq]
        exact ⟨lt_of_lt_of_le hσ (min_le_left _ _), hxδ⟩
      -- Mean value theorem in time for `σ ↦ D_x F(σ, x) - σ • M(t, y)`, whose derivative
      -- `M(σ, x) - M(t, y)` has norm `≤ ε / 2` for `|σ - t| < min δ r`.
      have hmvt : ‖(fderiv ℝ F (t + h, x)).comp L - (fderiv ℝ F (t, x)).comp L - h • M (t, y)‖
          ≤ ε / 2 * |h| := by
        have hderiv : ∀ σ ∈ ball t (min δ r), HasDerivWithinAt
            (fun σ ↦ (fderiv ℝ F (σ, x)).comp L - σ • M (t, y)) (M (σ, x) - M (t, y))
            (ball t (min δ r)) σ := by
          intro σ hσ
          rw [mem_ball, Real.dist_eq] at hσ
          have h1 := hc σ x (hmem σ x (lt_of_lt_of_le hσ (min_le_right _ _)) hxr)
          have h2 := (hasDerivAt_id' σ).smul_const (M (t, y))
          have h3 := (h1.sub h2).hasDerivWithinAt (s := ball t (min δ r))
          rw [one_smul] at h3
          exact h3
        have hbound : ∀ σ ∈ ball t (min δ r), ‖M (σ, x) - M (t, y)‖ ≤ ε / 2 := by
          intro σ hσ
          rw [mem_ball, Real.dist_eq] at hσ
          rw [← dist_eq_norm]
          exact (hclose σ hσ).le
        have hth : t + h ∈ ball t (min δ r) := by
          rw [mem_ball, Real.dist_eq, add_sub_cancel_left]
          exact hh
        have hlip := (convex_ball t (min δ r)).norm_image_sub_le_of_norm_hasDerivWithin_le
          hderiv hbound (mem_ball_self hδ') hth
        simp only [add_sub_cancel_left, Real.norm_eq_abs] at hlip
        calc _ = ‖(fderiv ℝ F (t + h, x)).comp L - (t + h) • M (t, y)
              - ((fderiv ℝ F (t, x)).comp L - t • M (t, y))‖ := by
              congr 1
              rw [show (t + h) • M (t, y) = t • M (t, y) + h • M (t, y) from add_smul t h (M (t, y))]
              abel
          _ ≤ ε / 2 * |h| := hlip
      -- Hence `‖M(t, y) - f' h x‖ ≤ ε / 2`, and `‖M(t, x) - M(t, y)‖ < ε / 2`.
      have hfinal : dist (M (t, y))
          (h⁻¹ • ((fderiv ℝ F (t + h, x)).comp L - (fderiv ℝ F (t, x)).comp L)) ≤ ε / 2 := by
        rw [dist_eq_norm]
        have e2 : M (t, y) - h⁻¹ • ((fderiv ℝ F (t + h, x)).comp L - (fderiv ℝ F (t, x)).comp L)
            = -(h⁻¹ • ((fderiv ℝ F (t + h, x)).comp L - (fderiv ℝ F (t, x)).comp L
              - h • M (t, y))) := by
          rw [smul_sub (h⁻¹) _ (h • M (t, y)), smul_smul, inv_mul_cancel₀ hh0, one_smul]; abel
        rw [e2, norm_neg, norm_smul, norm_inv, Real.norm_eq_abs]
        have habs : 0 < |h| := abs_pos.mpr hh0
        calc |h|⁻¹ * ‖_‖ ≤ |h|⁻¹ * (ε / 2 * |h|) := by gcongr
          _ = ε / 2 := by field_simp
      calc dist (M (t, x)) (h⁻¹ • ((fderiv ℝ F (t + h, x)).comp L - (fderiv ℝ F (t, x)).comp L))
          ≤ dist (M (t, x)) (M (t, y)) + dist (M (t, y))
              (h⁻¹ • ((fderiv ℝ F (t + h, x)).comp L - (fderiv ℝ F (t, x)).comp L)) :=
            dist_triangle _ _ _
        _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le (hclose t (by simpa using hδ')) hfinal
        _ = ε := add_halves ε
    · -- `f' h` is the derivative of `f h` near `y`, for small `h`.
      have h1 : ∀ᶠ h in 𝓝[≠] (0 : ℝ), |h| < r := by
        filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds (0 : ℝ) hr)] with h h1
        rwa [mem_ball, Real.dist_eq, sub_zero] at h1
      have h2 : ∀ᶠ x in 𝓝 y, dist x y < r := ball_mem_nhds y hr
      filter_upwards [h1.prod_mk h2]
      rintro ⟨h, x⟩ ⟨hh, hx⟩
      have p1 := ha (t + h) x (hmem (t + h) x (by simpa using hh) hx)
      have p2 := ha t x (hmem t x (by simpa using hr) hx)
      exact (p1.sub p2).const_smul h⁻¹
    · -- `f h x → ∂_s Φ(t, x)` for `x` near `y`: the slopes converge to the derivative.
      filter_upwards [ball_mem_nhds y hr] with x hx
      have hbx := hb t x (hmem t x (by simpa using hr) hx)
      show Tendsto (fun h ↦ h⁻¹ • (Φ (t + h) x - Φ t x)) (𝓝[≠] 0) (𝓝 (deriv (fun s ↦ Φ s x) t))
      rw [hbx.deriv]
      exact hbx.tendsto_slope_zero
  -- Step 4: near `t`, `D(Φ s)(y) = D_x F(s, y)`, whose time derivative at `t` is `M(t, y)`.
  rw [key.fderiv]
  refine (hc t y (mem_ball_self hr)).congr_of_eventuallyEq ?_
  filter_upwards [ball_mem_nhds t hr] with s hs
  rw [mem_ball, Real.dist_eq] at hs
  exact (ha s y (hmem s y hs (by simpa using hr))).fderiv

/-- **Calculus of an admissible deformation** (Simon Ch. 2, 5.1–5.4). Write `X`, `Z` for the
initial velocity and acceleration, `A(t,x) = fderiv ℝ (φ t) x` and `O = (-1,1) × U` (open).
(V) `X`, `Z`, `DX`, `DZ` vanish off `K`: `K` is compact, hence closed, and `φ t = id` off `K`.
(C2) `A` is `C¹` on `O` (`m = 1`, `n = 2` in `partials_contDiffOn`); `A(0,y) = I` since
`φ 0 = id` near `y ∈ U`; and the interchange `mixed_partial` at `(0,y)` gives `∂ₜA(0,y) = DX(y)`,
because `x ↦ deriv (s ↦ φ s x) 0` is `X` by definition.
(C3) (Erratum: `C³`, not `C²`.) `A` and `Ψ(t,x) = deriv (s ↦ φ s x) t` are `C²` on `O`.
`mixed_partial` at every `(t,y)`, `|t| < 1`, makes `s ↦ A(s,y)` differentiable near `0` with
`∂ₜA(t,y) = D(Ψ t)(y)`; `mixed_partial` for `Ψ` at `(0,y)` differentiates this at `0`, and
`x ↦ deriv (s ↦ Ψ s x) 0` is `Z` by definition. -/
theorem Submission.variation_deformation_calculus : ∀ (N : ℕ) (U K : Set (Rn N)) (φ : ℝ → Rn N → Rn N), (∀ r : ℕ∞, IsAdmissibleDeformation r U K φ → ∀ x, x ∉ K → initialVelocity φ x = 0 ∧ initialAcceleration φ x = 0 ∧ fderiv ℝ (initialVelocity φ) x = 0 ∧ fderiv ℝ (initialAcceleration φ) x = 0) ∧ (IsAdmissibleDeformation 2 U K φ → (∀ t ∈ Ioo (-1 : ℝ) 1, ∀ x ∈ U, ContDiffAt ℝ 1 (fun p : ℝ × Rn N ↦ fderiv ℝ (φ p.1) p.2) (t, x)) ∧ ∀ y ∈ U, fderiv ℝ (φ 0) y = 1 ∧ HasDerivAt (fun t ↦ fderiv ℝ (φ t) y) (fderiv ℝ (initialVelocity φ) y) 0) ∧ (IsAdmissibleDeformation 3 U K φ → (∀ t ∈ Ioo (-1 : ℝ) 1, ∀ x ∈ U, ContDiffAt ℝ 2 (fun p : ℝ × Rn N ↦ fderiv ℝ (φ p.1) p.2) (t, x)) ∧ ∀ y ∈ U, (∀ᶠ t in 𝓝 0, DifferentiableAt ℝ (fun s ↦ fderiv ℝ (φ s) y) t) ∧ HasDerivAt (deriv (fun s ↦ fderiv ℝ (φ s) y)) (fderiv ℝ (initialAcceleration φ) y) 0) := by
  intro N U K φ
  have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by norm_num
  have hI : Ioo (-1 : ℝ) 1 ∈ 𝓝 0 := isOpen_Ioo.mem_nhds h0
  refine ⟨?_, ?_, ?_⟩
  · -- (V), items 1–2.
    rintro r ⟨-, hK, -, -, -, hfix, -⟩
    exact Submission.variation_deformation_vanish_off_closed N K φ hK.isClosed hfix
  · -- (C2).
    rintro ⟨hU, -, -, hC, hid, -, -⟩
    have hO : IsOpen (Ioo (-1 : ℝ) 1 ×ˢ U) := isOpen_Ioo.prod hU
    -- Items 3–4: `A` is `C¹` on `O`.
    have hA := (Submission.variation_deformation_partials_contDiffOn N φ _ 1 _ hO hC
      (by norm_num)).1
    refine ⟨fun t ht x hx ↦ hA.contDiffAt (hO.mem_nhds ⟨ht, hx⟩), fun y hy ↦ ⟨?_, ?_⟩⟩
    · -- Item 5: `φ 0 = id` on the neighbourhood `U` of `y`.
      have hid' : φ 0 =ᶠ[𝓝 y] id := Filter.eventually_of_mem (hU.mem_nhds hy) hid
      rw [hid'.fderiv_eq, fderiv_id]
      rfl
    · -- Items 6–7: interchange at `(0,y)`.
      exact Submission.variation_deformation_mixed_partial N φ 0 y
        (hC.contDiffAt (hO.mem_nhds ⟨h0, hy⟩))
  · -- (C3).
    rintro ⟨hU, -, -, hC, -, -, -⟩
    have hO : IsOpen (Ioo (-1 : ℝ) 1 ×ˢ U) := isOpen_Ioo.prod hU
    -- Items 8–10: `A` and `Ψ` are `C²` on `O`.
    obtain ⟨hA, hΨ⟩ := Submission.variation_deformation_partials_contDiffOn N φ _ 2 _ hO hC
      (by norm_num)
    refine ⟨fun t ht x hx ↦ hA.contDiffAt (hO.mem_nhds ⟨ht, hx⟩), fun y hy ↦ ?_⟩
    -- Item 9: interchange at every `(t,y)` with `|t| < 1`.
    have hM : ∀ t ∈ Ioo (-1 : ℝ) 1, HasDerivAt (fun s ↦ fderiv ℝ (φ s) y)
        (fderiv ℝ (fun x ↦ deriv (fun s ↦ φ s x) t) y) t := fun t ht ↦
      Submission.variation_deformation_mixed_partial N φ t y
        ((hC.contDiffAt (hO.mem_nhds ⟨ht, hy⟩)).of_le (by norm_num))
    refine ⟨Filter.eventually_of_mem hI fun t ht ↦ (hM t ht).differentiableAt, ?_⟩
    -- Item 11: interchange for `Ψ` at `(0,y)`, transported along `∂ₜA(t,y) = D(Ψ t)(y)` near `0`.
    exact (Submission.variation_deformation_mixed_partial N (fun t x ↦ deriv (fun s ↦ φ s x) t)
      0 y (hΨ.contDiffAt (hO.mem_nhds ⟨h0, hy⟩))).congr_of_eventuallyEq
      (Filter.eventually_of_mem hI fun t ht ↦ (hM t ht).deriv)

/-- **Simon Ch. 2, 5.2–5.4 (pp. 62–63), the Jacobian of a deformation family.** With
`A(t, x) = Dφ_t(x)`, put `g(t, (x, P)) = √det(I - P + P A(t, x)* A(t, x) P)`. If `φ` is admissible
of class `r ∈ {2, 3}`, then `g` is `C^{r-1}` at `(0, (x, P))` for `x ∈ U` and every idempotent
`P`: `det`, the adjoint and composition are smooth on `L(ℝᴺ)`, `A` is `C^{r-1}` at `(0, x)` with
`A(0, x) = I` (`variation_deformation_calculus`), and so the radicand is `det(I - P + P ∘ P) = 1`
there. At `P = P_y`, `t ↦ g(t, (y, P_y))` is the function of `variation_gram_det_derivatives` for
the frame `τᵢ` of `T_y M`; its first two derivatives at `0` are `div_M X(y)` and the
second-variation integrand. Both integrands vanish off `K`, where `DX = DZ = 0`. -/
theorem Submission.variation_jacobian_family : ∀ (N : ℕ) (U K : Set (Rn N)) (φ : ℝ → Rn N → Rn N), let g : ℝ × (Rn N × (Rn N →L[ℝ] Rn N)) → ℝ := fun p ↦ Real.sqrt ((1 - p.2.2 + p.2.2 ∘L ContinuousLinearMap.adjoint (fderiv ℝ (φ p.1) p.2.1) ∘L fderiv ℝ (φ p.1) p.2.1 ∘L p.2.2).det); (IsAdmissibleDeformation 2 U K φ → (∀ x ∈ U, ∀ P : Rn N →L[ℝ] Rn N, P ∘L P = P → ContDiffAt ℝ 1 g (0, (x, P))) ∧ ∀ (M : Set (Rn N)) (y : Rn N), y ∈ U → HasDerivAt (fun t ↦ g (t, (y, tangentProjection M y))) (tangentialDivergence M (initialVelocity φ) y) 0) ∧ (IsAdmissibleDeformation 3 U K φ → (∀ x ∈ U, ∀ P : Rn N →L[ℝ] Rn N, P ∘L P = P → ContDiffAt ℝ 2 g (0, (x, P))) ∧ ∀ (M : Set (Rn N)) (y : Rn N), y ∈ U → HasDerivAt (fun t ↦ deriv (fun s ↦ g (s, (y, tangentProjection M y))) t) (secondVariationIntegrand M φ y) 0) ∧ ∀ r : ℕ∞, IsAdmissibleDeformation r U K φ → ∀ (M : Set (Rn N)) (y : Rn N), y ∉ K → tangentialDivergence M (initialVelocity φ) y = 0 ∧ secondVariationIntegrand M φ y = 0 := by
  intro N U K φ g
  have hG := Submission.variation_gram_det_derivatives
  have hD := Submission.variation_deformation_calculus N U K φ
  -- Class `3` implies class `2`: only the `C^r` clause depends on `r`.
  have h32 : IsAdmissibleDeformation 3 U K φ → IsAdmissibleDeformation 2 U K φ := by
    rintro ⟨hU, hK, hKU, hφ, hφ0, hfix, hbij⟩
    exact ⟨hU, hK, hKU, hφ.of_le (by exact_mod_cast (by norm_num : (2 : ℕ∞) ≤ 3)), hφ0, hfix, hbij⟩
  -- `B ↦ det B` is smooth: in the standard basis `e` it is the Leibniz polynomial in the
  -- continuous linear coordinates `B ↦ ⟪e (σ i), B (e i)⟫`.
  have hdet : ∀ {k : WithTop ℕ∞}, ContDiff ℝ k (fun B : Rn N →L[ℝ] Rn N ↦ B.det) := by
    intro k
    classical
    let e := EuclideanSpace.basisFun (Fin N) ℝ
    have h : (fun B : Rn N →L[ℝ] Rn N ↦ B.det) = fun B ↦
        ∑ σ : Equiv.Perm (Fin N), Equiv.Perm.sign σ • ∏ i, inner ℝ (e (σ i)) (B (e i)) := by
      funext B
      change LinearMap.det (B : Rn N →ₗ[ℝ] Rn N) = _
      rw [← LinearMap.det_toMatrix e.toBasis, Matrix.det_apply]
      simp [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.repr_apply_apply]
    rw [h]
    refine ContDiff.sum fun σ _ ↦ ContDiff.const_smul _ (contDiff_prod fun i _ ↦ ?_)
    exact contDiff_const.inner ℝ (ContinuousLinearMap.apply ℝ (Rn N) (e i)).contDiff
  -- `B ↦ B*` is additive and commutes with real scalars, so it is continuous linear.
  have hadj : ∀ {k : WithTop ℕ∞}, ContDiff ℝ k
      (fun B : Rn N →L[ℝ] Rn N ↦ ContinuousLinearMap.adjoint B) := by
    intro k
    let L : (Rn N →L[ℝ] Rn N) →L[ℝ] (Rn N →L[ℝ] Rn N) :=
      { toFun := fun B ↦ ContinuousLinearMap.adjoint B
        map_add' := fun B C ↦ map_add _ B C
        map_smul' := fun c B ↦ by simp
        cont := ContinuousLinearMap.adjoint.continuous }
    exact L.contDiff
  -- Smoothness of `g` at `(0, (x, P))` once `A` is `C^k` at `(0, x)` with `A(0, x) = I`.
  have hsmooth : ∀ {k : WithTop ℕ∞} (x : Rn N) (P : Rn N →L[ℝ] Rn N), P ∘L P = P →
      ContDiffAt ℝ k (fun p : ℝ × Rn N ↦ fderiv ℝ (φ p.1) p.2) (0, x) →
      fderiv ℝ (φ 0) x = 1 → ContDiffAt ℝ k g (0, (x, P)) := by
    intro k x P hP hA hA0
    have hA' : ContDiffAt ℝ k
        (fun p : ℝ × (Rn N × (Rn N →L[ℝ] Rn N)) ↦ fderiv ℝ (φ p.1) p.2.1) (0, (x, P)) :=
      hA.comp (f := fun p : ℝ × (Rn N × (Rn N →L[ℝ] Rn N)) ↦ (p.1, p.2.1)) (0, (x, P))
        (contDiffAt_fst.prodMk contDiffAt_snd.fst)
    have hP' : ContDiffAt ℝ k (fun p : ℝ × (Rn N × (Rn N →L[ℝ] Rn N)) ↦ p.2.2) (0, (x, P)) :=
      contDiffAt_snd.snd
    have hΓ : ContDiffAt ℝ k (fun p : ℝ × (Rn N × (Rn N →L[ℝ] Rn N)) ↦ 1 - p.2.2 +
        p.2.2 ∘L ContinuousLinearMap.adjoint (fderiv ℝ (φ p.1) p.2.1) ∘L fderiv ℝ (φ p.1) p.2.1 ∘L
          p.2.2) (0, (x, P)) :=
      (contDiffAt_const.sub hP').add
        (hP'.clm_comp ((hadj.contDiffAt.comp _ hA').clm_comp (hA'.clm_comp hP')))
    -- At `(0, (x, P))` the operator is `I - P + P ∘ P = I`, whose determinant is `1 ≠ 0`.
    have h1 : 1 - P + P ∘L ContinuousLinearMap.adjoint (fderiv ℝ (φ 0) x) ∘L fderiv ℝ (φ 0) x ∘L
        P = 1 := by
      rw [hA0, ContinuousLinearMap.adjoint_one, ContinuousLinearMap.one_def,
        ContinuousLinearMap.id_comp, ContinuousLinearMap.id_comp, hP, sub_add_cancel]
    refine (hdet.contDiffAt.comp _ hΓ).sqrt ?_
    change (1 - P + P ∘L ContinuousLinearMap.adjoint (fderiv ℝ (φ 0) x) ∘L fderiv ℝ (φ 0) x ∘L
      P).det ≠ 0
    rw [h1, ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_one, map_one]
    exact one_ne_zero
  have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  refine ⟨fun h2 ↦ ⟨fun x hx P hP ↦ ?_, fun M y hy ↦ ?_⟩,
    fun h3 ↦ ⟨fun x hx P hP ↦ ?_, fun M y hy ↦ ?_⟩, fun r hr M y hy ↦ ?_⟩
  · -- (F2), smoothness.
    exact hsmooth x P hP ((hD.2.1 h2).1 0 h0 x hx) ((hD.2.1 h2).2 x hx).1
  · -- (F2), first variation: `P_y = T.starProjection` and `τᵢ` is the frame `b` of `T = T_y M`.
    obtain ⟨hA0, hA1⟩ := (hD.2.1 h2).2 y hy
    exact (hG N (tangentSpace M y) _ (stdOrthonormalBasis ℝ (tangentSpace M y))
      (fun t ↦ fderiv ℝ (φ t) y) hA0).1 _ hA1
  · -- (F3), smoothness.
    exact hsmooth x P hP ((hD.2.2 h3).1 0 h0 x hx) ((hD.2.1 (h32 h3)).2 x hx).1
  · -- (F3), second variation: `A₁ = DX(y)`, `A₂ = DZ(y)`, and `v - P_y v = normalPart M y v`.
    obtain ⟨hA0, hA1⟩ := (hD.2.1 (h32 h3)).2 y hy
    obtain ⟨hev, hA2⟩ := (hD.2.2 h3).2 y hy
    exact (hG N (tangentSpace M y) _ (stdOrthonormalBasis ℝ (tangentSpace M y))
      (fun t ↦ fderiv ℝ (φ t) y) hA0).2 _ _ hev hA1 hA2
  · -- (FV): off `K`, `DX(y) = DZ(y) = 0`, so every term of both integrands vanishes.
    obtain ⟨-, -, hX, hZ⟩ := hD.1 r hr y hy
    simp [secondVariationIntegrand, tangentialDivergence, normalPart, hX, hZ]
/-- **Differentiation under the integral sign for `g (t, e z)` with `e(S)` in a compact set**
(Simon Ch. 2, §5, p. 62: differentiating `t ↦ Hⁿ(M_t)` once and twice in 5.3–5.4). Let `S` be
measurable with `μ S < ∞`, let `C` be compact, and let `e` be a.e. strongly measurable for `μ⌊S`
with `e(S) ⊆ C`. If `g` is `C¹` at every `(0, x)`, `x ∈ C`, then `z ↦ g (t, e z)` is integrable on
`S` for `t` near `0`, and `d/dt ∫_S g (t, e z) dμ = ∫_S ∂_t g (0, e z) dμ` at `t = 0`. If `g` is
`C²` there, the same formula holds at every `t` near `0`, and differentiating it once more at `0`
gives `∫_S ∂²_t g (0, e z) dμ`. By compactness `g` is `C^k` on `(-2r, 2r) × C` for some `r > 0`, so
`g`, `∂_t g` and `∂²_t g` are bounded on `[-r, r] × C`. Composition with `e` is a.e. strongly
measurable (approximate `e` by simple functions). The constant bound is `μ⌊S`-integrable, so
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` applies. -/
theorem Submission.variation_param_integral_deriv : ∀ (α X : Type) [MeasurableSpace α] [NormedAddCommGroup X] [NormedSpace ℝ X] (μ : Measure α) (S : Set α) (C : Set X) (e : α → X) (g : ℝ × X → ℝ), MeasurableSet S → μ S < ⊤ → IsCompact C → (∀ z ∈ S, e z ∈ C) → AEStronglyMeasurable e (μ.restrict S) → ((∀ x ∈ C, ContDiffAt ℝ 1 g (0, x)) → (∀ᶠ t in 𝓝 0, Integrable (fun z ↦ g (t, e z)) (μ.restrict S)) ∧ HasDerivAt (fun t ↦ ∫ z in S, g (t, e z) ∂μ) (∫ z in S, deriv (fun t ↦ g (t, e z)) 0 ∂μ) 0) ∧ ((∀ x ∈ C, ContDiffAt ℝ 2 g (0, x)) → (∀ᶠ t in 𝓝 0, HasDerivAt (fun s ↦ ∫ z in S, g (s, e z) ∂μ) (∫ z in S, deriv (fun s ↦ g (s, e z)) t ∂μ) t) ∧ HasDerivAt (fun t ↦ ∫ z in S, deriv (fun s ↦ g (s, e z)) t ∂μ) (∫ z in S, deriv (fun t ↦ deriv (fun s ↦ g (s, e z)) t) 0 ∂μ) 0) := by
  intro α X _ _ _ μ S C e g hS hμS hC heC he
  have : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.mpr hμS.ne
  -- Step 4: if `h` is continuous at every point of `C`, then `z ↦ h (e z)` is a.e. strongly
  -- measurable for `μ⌊S`: approximate a strongly measurable version `e'` of `e` by simple
  -- functions `s_m`; `h ∘ s_m` is simple and `h (s_m z) → h (e' z)` whenever `e' z = e z ∈ C`.
  have hmeas : ∀ h : X → ℝ, (∀ x ∈ C, ContinuousAt h x) →
      AEStronglyMeasurable (fun z ↦ h (e z)) (μ.restrict S) := by
    intro h hh
    obtain ⟨e', he'm, hee'⟩ := he
    have h' : AEStronglyMeasurable (fun z ↦ h (e' z)) (μ.restrict S) := by
      refine aestronglyMeasurable_of_tendsto_ae atTop
        (f := fun n z ↦ h (he'm.approx n z)) (fun n ↦ ?_) ?_
      · exact ((he'm.approx n).map h).stronglyMeasurable.aestronglyMeasurable
      · filter_upwards [hee', ae_restrict_mem hS] with z hz hzS
        exact (hh (e' z) (hz ▸ heC z hzS)).tendsto.comp (he'm.tendsto_approx z)
    exact h'.congr (hee'.fun_comp h).symm
  -- Step 1: if `G` is `C¹` at `(t, x)`, then `G` and `∂_t G = DG(·)(1, 0)` are continuous at
  -- `(t, x)`, and `s ↦ G (s, x)` has derivative `∂_t G (t, x)` at `t` (chain rule).
  have facts : ∀ (G : ℝ × X → ℝ) (t : ℝ) (x : X), ContDiffAt ℝ 1 G (t, x) →
      ContinuousAt G (t, x) ∧ ContinuousAt (fun q ↦ fderiv ℝ G q (1, 0)) (t, x) ∧
        HasDerivAt (fun s ↦ G (s, x)) (fderiv ℝ G (t, x) (1, 0)) t := by
    intro G t x hG
    refine ⟨hG.continuousAt, ?_, ?_⟩
    · exact (hG.fderiv_right (m := 0) (by norm_num)).continuousAt.clm_apply continuousAt_const
    · exact (hG.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_id' t).prodMk (hasDerivAt_const t x))
  -- Step 2: tube lemma. If `g` is `C^n` (`n` finite) at every `(0, x)`, `x ∈ C`, then `g` is
  -- `C^n` on `(-2r, 2r) × C` for some `r > 0`.
  have tube : ∀ n : WithTop ℕ∞, n ≠ ((⊤ : ℕ∞) : WithTop ℕ∞) →
      (∀ x ∈ C, ContDiffAt ℝ n g (0, x)) →
        ∃ r > 0, ∀ t : ℝ, |t| < 2 * r → ∀ x ∈ C, ContDiffAt ℝ n g (t, x) := by
    intro n hn hg
    have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ x ∈ C, ContDiffAt ℝ n g (t, x) :=
      hC.eventually_forall_of_forall_eventually (P := fun t x ↦ ContDiffAt ℝ n g (t, x))
        fun x hx ↦ (hg x hx).eventually hn
    obtain ⟨ε, hε, hεball⟩ := Metric.eventually_nhds_iff.mp hev
    refine ⟨ε / 2, half_pos hε, fun t ht x hx ↦ hεball ?_ x hx⟩
    rw [Real.dist_eq, sub_zero]
    linarith
  -- Steps 3, 5 and 6: let `G` have `t`-derivative `G'` on `(-2r, 2r) × C`, with `G` and `G'`
  -- continuous there. For `|t₀| < r`, `z ↦ G (t₀, e z)` is `μ⌊S`-integrable, and dominated
  -- differentiation on `ball t₀ (r - |t₀|) ⊆ (-r, r)` gives the derivative of the integral at `t₀`.
  have core : ∀ (G G' : ℝ × X → ℝ) (r : ℝ), 0 < r →
      (∀ t : ℝ, |t| < 2 * r → ∀ x ∈ C, ContinuousAt G (t, x) ∧ ContinuousAt G' (t, x) ∧
        HasDerivAt (fun s ↦ G (s, x)) (G' (t, x)) t) →
      ∀ t₀ : ℝ, |t₀| < r → Integrable (fun z ↦ G (t₀, e z)) (μ.restrict S) ∧
        HasDerivAt (fun t ↦ ∫ z in S, G (t, e z) ∂μ) (∫ z in S, G' (t₀, e z) ∂μ) t₀ := by
    intro G G' r hr hG t₀ ht₀
    have hmG : ∀ t : ℝ, |t| < 2 * r → AEStronglyMeasurable (fun z ↦ G (t, e z)) (μ.restrict S) :=
      fun t ht ↦ hmeas (fun x ↦ G (t, x)) fun x hx ↦
        (hG t ht x hx).1.comp (continuous_const.prodMk continuous_id).continuousAt
    have hmG' : ∀ t : ℝ, |t| < 2 * r → AEStronglyMeasurable (fun z ↦ G' (t, e z)) (μ.restrict S) :=
      fun t ht ↦ hmeas (fun x ↦ G' (t, x)) fun x hx ↦
        (hG t ht x hx).2.1.comp (continuous_const.prodMk continuous_id).continuousAt
    -- Uniform bounds `B`, `B'` for `G`, `G'` on the compact set `[-r, r] × C`.
    have hQ : IsCompact (closedBall (0 : ℝ) r ×ˢ C) := (isCompact_closedBall 0 r).prod hC
    have hQmem : ∀ p ∈ closedBall (0 : ℝ) r ×ˢ C, |p.1| < 2 * r ∧ p.2 ∈ C := by
      intro p hp
      refine ⟨?_, hp.2⟩
      have := hp.1
      rw [mem_closedBall, Real.dist_eq, sub_zero] at this
      linarith
    obtain ⟨B, hB⟩ := hQ.exists_bound_of_continuousOn (f := G)
      (continuousOn_of_forall_continuousAt fun p hp ↦ (hG p.1 (hQmem p hp).1 p.2 (hQmem p hp).2).1)
    obtain ⟨B', hB'⟩ := hQ.exists_bound_of_continuousOn (f := G')
      (continuousOn_of_forall_continuousAt fun p hp ↦
        (hG p.1 (hQmem p hp).1 p.2 (hQmem p hp).2).2.1)
    have hint : Integrable (fun z ↦ G (t₀, e z)) (μ.restrict S) := by
      refine (integrable_const B).mono' (hmG t₀ (by linarith [abs_nonneg t₀])) ?_
      filter_upwards [ae_restrict_mem hS] with z hz
      refine hB (t₀, e z) ⟨?_, heC z hz⟩
      rw [mem_closedBall, Real.dist_eq, sub_zero]
      exact ht₀.le
    refine ⟨hint, ?_⟩
    have hpos : 0 < r - |t₀| := by linarith
    have hball : ∀ t ∈ ball t₀ (r - |t₀|), |t| < r := by
      intro t ht
      rw [mem_ball, Real.dist_eq] at ht
      linarith [abs_sub_abs_le_abs_sub t t₀]
    have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict S)
      (F := fun t z ↦ G (t, e z)) (F' := fun t z ↦ G' (t, e z)) (x₀ := t₀)
      (bound := fun _ ↦ B') (s := ball t₀ (r - |t₀|))
      (ball_mem_nhds t₀ hpos)
      (eventually_of_mem (ball_mem_nhds t₀ hpos) fun t ht ↦
        hmG t (by linarith [hball t ht]))
      hint (hmG' t₀ (by linarith [abs_nonneg t₀]))
      (by
        filter_upwards [ae_restrict_mem hS] with z hz t ht
        refine hB' (t, e z) ⟨?_, heC z hz⟩
        rw [mem_closedBall, Real.dist_eq, sub_zero]
        exact (hball t ht).le)
      (integrable_const B')
      (by
        filter_upwards [ae_restrict_mem hS] with z hz t ht
        exact (hG t (by linarith [hball t ht]) (e z) (heC z hz)).2.2)
    exact hd.2
  refine ⟨fun h1 ↦ ?_, fun h2 ↦ ?_⟩
  · -- (I1): apply `core` to `g` and `∂_t g`; by Step 1, `∂_t g (0, e z)` is the `deriv` integrand.
    obtain ⟨r, hr, hgr⟩ := tube 1 (by simp) h1
    have hG : ∀ t : ℝ, |t| < 2 * r → ∀ x ∈ C, ContinuousAt g (t, x) ∧
        ContinuousAt (fun q ↦ fderiv ℝ g q (1, 0)) (t, x) ∧
          HasDerivAt (fun s ↦ g (s, x)) (fderiv ℝ g (t, x) (1, 0)) t :=
      fun t ht x hx ↦ facts g t x (hgr t ht x hx)
    refine ⟨?_, ?_⟩
    · filter_upwards [ball_mem_nhds (0 : ℝ) hr] with t ht
      rw [mem_ball, Real.dist_eq, sub_zero] at ht
      exact (core g _ r hr hG t ht).1
    · refine (core g _ r hr hG 0 (by simpa using hr)).2.congr_deriv ?_
      refine setIntegral_congr_fun hS fun z hz ↦ ?_
      exact ((hG 0 (by simpa using hr) (e z) (heC z hz)).2.2.deriv).symm
  · -- (I2): `g` is `C²` on `(-2r, 2r) × C`, so `g` and `g₁ = ∂_t g` are `C¹` there.
    obtain ⟨r, hr, hgr⟩ := tube 2 (by simp) h2
    have hG : ∀ t : ℝ, |t| < 2 * r → ∀ x ∈ C, ContinuousAt g (t, x) ∧
        ContinuousAt (fun q ↦ fderiv ℝ g q (1, 0)) (t, x) ∧
          HasDerivAt (fun s ↦ g (s, x)) (fderiv ℝ g (t, x) (1, 0)) t :=
      fun t ht x hx ↦ facts g t x ((hgr t ht x hx).of_le (by norm_num))
    have hG1 : ∀ t : ℝ, |t| < 2 * r → ∀ x ∈ C,
        ContinuousAt (fun q ↦ fderiv ℝ g q (1, 0)) (t, x) ∧
        ContinuousAt (fun q ↦ fderiv ℝ (fun q ↦ fderiv ℝ g q (1, 0)) q (1, 0)) (t, x) ∧
          HasDerivAt (fun s ↦ fderiv ℝ g (s, x) (1, 0))
            (fderiv ℝ (fun q ↦ fderiv ℝ g q (1, 0)) (t, x) (1, 0)) t :=
      fun t ht x hx ↦ facts (fun q ↦ fderiv ℝ g q (1, 0)) t x
        (((hgr t ht x hx).fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const)
    have h2r : (0 : ℝ) < 2 * r := by linarith
    refine ⟨?_, ?_⟩
    · -- Step 6: `core` for `g` at every `|t| < r`.
      filter_upwards [ball_mem_nhds (0 : ℝ) hr] with t ht
      rw [mem_ball, Real.dist_eq, sub_zero] at ht
      refine (core g _ r hr hG t ht).2.congr_deriv ?_
      refine setIntegral_congr_fun hS fun z hz ↦ ?_
      exact ((hG t (by linarith) (e z) (heC z hz)).2.2.deriv).symm
    · -- Step 7: `core` for `g₁` at `0`. On `(-2r, 2r)` the `deriv` integrand equals `g₁ (t, e z)`,
      -- both inside the integral and before differentiating once more at `0`.
      refine ((core _ _ r hr hG1 0 (by simpa using hr)).2.congr_deriv ?_).congr_of_eventuallyEq ?_
      · refine setIntegral_congr_fun hS fun z hz ↦ ?_
        have hev : (fun t ↦ deriv (fun s ↦ g (s, e z)) t) =ᶠ[𝓝 0]
            fun t ↦ fderiv ℝ g (t, e z) (1, 0) := by
          filter_upwards [ball_mem_nhds (0 : ℝ) h2r] with t ht
          rw [mem_ball, Real.dist_eq, sub_zero] at ht
          exact (hG t ht (e z) (heC z hz)).2.2.deriv
        exact (hev.deriv_eq.trans (hG1 0 (by simpa using h2r) (e z) (heC z hz)).2.2.deriv).symm
      · filter_upwards [ball_mem_nhds (0 : ℝ) h2r] with t ht
        rw [mem_ball, Real.dist_eq, sub_zero] at ht
        exact setIntegral_congr_fun hS fun z hz ↦ (hG t ht (e z) (heC z hz)).2.2.deriv
      have htriangle : ‖L x - L y‖ ≤ ‖φ₁ x - φ₁ y‖ + ‖φ₁ x - φ₁ y - (L x - L y)‖ := by
        simpa only [norm_sub_rev, add_comm] using
          norm_le_norm_sub_add (L x - L y) (φ₁ x - φ₁ y)
      simp only [dist_eq_norm, NNReal.coe_inv, NNReal.coe_sub hδ.le, NNReal.coe_one,
        NNReal.coe_mul, inv_mul_eq_div]
      apply (le_div_iff₀ (sub_pos.mpr hδR)).mpr
      nlinarith
    have hfinj : InjOn φ₁ t := by
      intro x hx y hy hxy
      apply hL.injective
      apply dist_le_zero.mp
      simpa only [hxy, dist_self, mul_zero] using hd x hx y hy
    rw [← hlin]
    exact hdist L φ₁ t _ hfinj hd
  -- Step 5: near an injective linear map `L`, one radius `δ` controls both the image measures of
  -- `δ`-approximations of `L` and the metric Jacobians of `δ`-close linear maps, up to a factor
  -- `q`.
  have hradius : ∀ (L : Rn k →L[ℝ] Rn N), Function.Injective L → ∀ q : ℝ≥0, 1 < q →
      ∃ δ : ℝ≥0, 0 < δ ∧
        (∀ B : Rn k →L[ℝ] Rn N, ‖B - L‖ ≤ δ →
          ENNReal.ofReal B.toLinearMap.normDet ≤ q * ENNReal.ofReal L.toLinearMap.normDet ∧
          ENNReal.ofReal L.toLinearMap.normDet ≤ q * ENNReal.ofReal B.toLinearMap.normDet) ∧
        (∀ (t : Set (Rn k)) (φ₁ : Rn k → Rn N), ApproximatesLinearOn φ₁ L t δ →
          μHE[k] (φ₁ '' t) ≤ q * (ENNReal.ofReal L.toLinearMap.normDet * volume t) ∧
          ENNReal.ofReal L.toLinearMap.normDet * volume t ≤ q * μHE[k] (φ₁ '' t)) := by
    intro L hL q hq
    obtain ⟨K, _, hK⟩ := L.toLinearMap.exists_antilipschitzWith (LinearMap.ker_eq_bot.mpr hL)
    have hJ : 0 < L.toLinearMap.normDet := by
      apply lt_of_le_of_ne L.toLinearMap.normDet_nonneg
      exact Ne.symm ((L.toLinearMap.normDet_ne_zero_tfae.out 5 1).mp hL)
    have hqR : (1 : ℝ) < q := hq
    have hmul : L.toLinearMap.normDet < (q : ℝ) * L.toLinearMap.normDet := by nlinarith
    have hnear : ∀ᶠ B : Rn k →L[ℝ] Rn N in 𝓝 L,
        B.toLinearMap.normDet < (q : ℝ) * L.toLinearMap.normDet ∧
          L.toLinearMap.normDet < (q : ℝ) * B.toLinearMap.normDet :=
      (hcont_nd.continuousAt.eventually_lt continuousAt_const hmul).and
        (continuousAt_const.eventually_lt (continuousAt_const.mul hcont_nd.continuousAt) hmul)
    obtain ⟨ε, hε, hnear⟩ := Metric.eventually_nhds_iff.mp hnear
    have hsmall : ∀ᶠ δ : ℝ≥0 in 𝓝 0, δ * K < 1 :=
      (continuousAt_id.mul continuousAt_const).eventually_lt continuousAt_const (by simp)
    have hup : ∀ᶠ δ : ℝ≥0 in 𝓝 0, (1 + δ * K) ^ k < q :=
      ((continuousAt_const.add (continuousAt_id.mul continuousAt_const)).pow _).eventually_lt
        continuousAt_const (by simpa using hq)
    have hlow : ∀ᶠ δ : ℝ≥0 in 𝓝 0, ((1 - δ * K)⁻¹) ^ k < q := by
      apply ContinuousAt.eventually_lt _ continuousAt_const (by simpa using hq)
      apply ContinuousAt.pow
      apply ContinuousAt.inv₀
      · exact continuousAt_const.sub (continuousAt_id.mul continuousAt_const)
      · simp
    have hεδ : ∀ᶠ δ : ℝ≥0 in 𝓝 0, (δ : ℝ) < ε :=
      NNReal.continuous_coe.continuousAt.eventually_lt continuousAt_const (by simpa using hε)
    have hevent : ∀ᶠ δ : ℝ≥0 in 𝓝[>] 0, 0 < δ ∧ δ * K < 1 ∧ (1 + δ * K) ^ k < q ∧
        ((1 - δ * K)⁻¹) ^ k < q ∧ (δ : ℝ) < ε := by
      filter_upwards [self_mem_nhdsWithin, hsmall.filter_mono nhdsWithin_le_nhds,
        hup.filter_mono nhdsWithin_le_nhds, hlow.filter_mono nhdsWithin_le_nhds,
        hεδ.filter_mono nhdsWithin_le_nhds] with δ hδ h1 h2 h3 h4
      exact ⟨hδ, h1, h2, h3, h4⟩
    obtain ⟨δ, hδ, hδsmall, hδup, hδlow, hδε⟩ := hevent.exists
    refine ⟨δ, hδ, fun B hB ↦ ?_, fun t φ₁ hf ↦ ⟨?_, ?_⟩⟩
    · have hBL : dist B L < ε := by
        rw [dist_eq_norm]
        exact hB.trans_lt hδε
      obtain ⟨h1, h2⟩ := hnear hBL
      constructor
      · simpa only [ENNReal.ofReal_mul (NNReal.coe_nonneg q), ENNReal.ofReal_coe_nnreal] using
          ENNReal.ofReal_le_ofReal h1.le
      · simpa only [ENNReal.ofReal_mul (NNReal.coe_nonneg q), ENNReal.ofReal_coe_nnreal] using
          ENNReal.ofReal_le_ofReal h2.le
    · refine (hupper φ₁ L t δ K hf hK).trans ?_
      gcongr
      exact_mod_cast hδup.le
    · refine (hlower φ₁ L t δ K hf hK hδsmall).trans ?_
      gcongr
      exact_mod_cast hδlow.le
  -- Step 6: at almost every point of a piece on which `φ₁` is `δ`-close to `A`, the derivative is
  -- `δ`-close to `A` (the density-point argument of Mathlib's
  -- `ApproximatesLinearOn.norm_fderiv_sub_le`, here for rectangular derivatives).
  have hderiv : ∀ (φ₁ : Rn k → Rn N) (t : Set (Rn k)) (A : Rn k →L[ℝ] Rn N) (δ : ℝ≥0),
      ApproximatesLinearOn φ₁ A t δ → MeasurableSet t → ∀ φ₁' : Rn k → Rn k →L[ℝ] Rn N,
      (∀ x ∈ t, HasFDerivWithinAt φ₁ (φ₁' x) t x) →
      ∀ᵐ x ∂(volume.restrict t), ‖φ₁' x - A‖₊ ≤ δ := by
    intro φ₁ t A δ hf ht φ₁' hf'
    filter_upwards [Besicovitch.ae_tendsto_measure_inter_div (volume : Measure (Rn k)) t,
      ae_restrict_mem ht]
    intro x hx xt
    apply ContinuousLinearMap.opNorm_le_bound _ δ.2 fun z ↦ ?_
    suffices Hε : ∀ ε, 0 < ε → ‖(φ₁' x - A) z‖ ≤ (δ + ε) * (‖z‖ + ε) + ‖φ₁' x - A‖ * ε by
      have : Tendsto (fun ε : ℝ ↦ ((δ : ℝ) + ε) * (‖z‖ + ε) + ‖φ₁' x - A‖ * ε) (𝓝[>] 0)
          (𝓝 ((δ + 0) * (‖z‖ + 0) + ‖φ₁' x - A‖ * 0)) :=
        Tendsto.mono_left (Continuous.tendsto (by fun_prop) 0) nhdsWithin_le_nhds
      simp only [add_zero, mul_zero] at this
      apply le_of_tendsto_of_tendsto tendsto_const_nhds this
      filter_upwards [self_mem_nhdsWithin]
      exact Hε
    intro ε εpos
    open scoped Pointwise in
    have B₁ : ∀ᶠ r in 𝓝[>] (0 : ℝ), (t ∩ ({x} + r • closedBall z ε)).Nonempty :=
      Measure.eventually_nonempty_inter_smul_of_density_one volume t x hx _
        measurableSet_closedBall (measure_closedBall_pos volume z εpos).ne'
    obtain ⟨ρ, ρpos, hρ⟩ :
        ∃ ρ > 0, ball x ρ ∩ t ⊆ {y : Rn k | ‖φ₁ y - φ₁ x - (φ₁' x) (y - x)‖ ≤ ε * ‖y - x‖} :=
      Metric.mem_nhdsWithin_iff.1 ((hf' x xt).isLittleO.bound εpos)
    open scoped Pointwise in
    have B₂ : ∀ᶠ r in 𝓝[>] (0 : ℝ), {x} + r • closedBall z ε ⊆ ball x ρ := by
      apply nhdsWithin_le_nhds
      exact eventually_singleton_add_smul_subset isBounded_closedBall (ball_mem_nhds x ρpos)
    open scoped Pointwise in
    obtain ⟨r, ⟨y, ⟨yt, hy⟩⟩, rρ, rpos⟩ : ∃ r : ℝ, (t ∩ ({x} + r • closedBall z ε)).Nonempty ∧
        {x} + r • closedBall z ε ⊆ ball x ρ ∧ 0 < r :=
      (B₁.and (B₂.and self_mem_nhdsWithin)).exists
    obtain ⟨a, az, ya⟩ : ∃ a, a ∈ closedBall z ε ∧ y = x + r • a := by
      simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hy
      rcases hy with ⟨a, az, ha⟩
      exact ⟨a, az, by simp only [ha, add_neg_cancel_left]⟩
    have norm_a : ‖a‖ ≤ ‖z‖ + ε :=
      calc
        ‖a‖ = ‖z + (a - z)‖ := by simp only [add_sub_cancel]
        _ ≤ ‖z‖ + ‖a - z‖ := norm_add_le _ _
        _ ≤ ‖z‖ + ε := by grw [mem_closedBall_iff_norm.1 az]
    have I : r * ‖(φ₁' x - A) a‖ ≤ r * (δ + ε) * (‖z‖ + ε) :=
      calc
        r * ‖(φ₁' x - A) a‖ = ‖(φ₁' x - A) (r • a)‖ := by
          simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
        _ = ‖φ₁ y - φ₁ x - A (y - x) - (φ₁ y - φ₁ x - (φ₁' x) (y - x))‖ := by
          simp only [ya, add_sub_cancel_left, sub_sub_sub_cancel_left, FunLike.coe_sub,
            Pi.sub_apply, map_smul, smul_sub]
        _ ≤ ‖φ₁ y - φ₁ x - A (y - x)‖ + ‖φ₁ y - φ₁ x - (φ₁' x) (y - x)‖ := norm_sub_le _ _
        _ ≤ δ * ‖y - x‖ + ε * ‖y - x‖ := add_le_add (hf _ yt _ xt) (hρ ⟨rρ hy, yt⟩)
        _ = r * (δ + ε) * ‖a‖ := by
          simp only [ya, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
          ring
        _ ≤ r * (δ + ε) * (‖z‖ + ε) := by gcongr
    calc
      ‖(φ₁' x - A) z‖ = ‖(φ₁' x - A) a + (φ₁' x - A) (z - a)‖ := by
        congr 1
        simp only [FunLike.coe_sub, map_sub, Pi.sub_apply]
        abel
      _ ≤ ‖(φ₁' x - A) a‖ + ‖(φ₁' x - A) (z - a)‖ := norm_add_le _ _
      _ ≤ (δ + ε) * (‖z‖ + ε) + ‖φ₁' x - A‖ * ‖z - a‖ := by
        apply add_le_add
        · rw [mul_assoc] at I
          exact (mul_le_mul_iff_right₀ rpos).1 I
        · apply ContinuousLinearMap.le_opNorm
      _ ≤ (δ + ε) * (‖z‖ + ε) + ‖φ₁' x - A‖ * ε := by
        rw [mem_closedBall_iff_norm'] at az
        gcongr
  -- Step 7: comparison up to the factor `q²` on a measurable partition into approximation pieces.
  have hcmp : ∀ (s : Set (Rn k)) (φ : Rn k → Rn N) (φ' : Rn k → Rn k →L[ℝ] Rn N),
      MeasurableSet s → (∀ x ∈ s, HasFDerivWithinAt φ (φ' x) s x) →
      (∀ x ∈ s, Function.Injective (φ' x)) → InjOn φ s → ∀ q : ℝ≥0, 1 < q →
      μHE[k] (φ '' s) ≤
          (q : ℝ≥0∞) ^ 2 * ∫⁻ x in s, ENNReal.ofReal (φ' x).toLinearMap.normDet ∂volume ∧
        (∫⁻ x in s, ENNReal.ofReal (φ' x).toLinearMap.normDet ∂volume) ≤
          (q : ℝ≥0∞) ^ 2 * μHE[k] (φ '' s) := by
    intro s φ φ' hs hφ' hreg' hinj' q hq
    rcases eq_empty_or_nonempty s with rfl | hsne
    · simp
    have hchoice : ∀ L : Rn k →L[ℝ] Rn N, ∃ δ : ℝ≥0, 0 < δ ∧ (Function.Injective L →
        (∀ B : Rn k →L[ℝ] Rn N, ‖B - L‖ ≤ δ →
          ENNReal.ofReal B.toLinearMap.normDet ≤ q * ENNReal.ofReal L.toLinearMap.normDet ∧
          ENNReal.ofReal L.toLinearMap.normDet ≤ q * ENNReal.ofReal B.toLinearMap.normDet) ∧
        (∀ (t : Set (Rn k)) (φ₁ : Rn k → Rn N), ApproximatesLinearOn φ₁ L t δ →
          μHE[k] (φ₁ '' t) ≤ q * (ENNReal.ofReal L.toLinearMap.normDet * volume t) ∧
          ENNReal.ofReal L.toLinearMap.normDet * volume t ≤ q * μHE[k] (φ₁ '' t))) := by
      intro L
      by_cases hL : Function.Injective L
      · obtain ⟨δ, hδ, hJ, harea⟩ := hradius L hL q hq
        exact ⟨δ, hδ, fun _ ↦ ⟨hJ, harea⟩⟩
      · exact ⟨1, zero_lt_one, fun h ↦ (hL h).elim⟩
    choose δ hδpos hδ using hchoice
    obtain ⟨t, L, hdisj, ht, hcover, happrox, hactual⟩ :=
      exists_partition_approximatesLinearOn_of_hasFDerivWithinAt φ s φ' hφ' δ
        (fun L ↦ (hδpos L).ne')
    have hLreg : ∀ i, Function.Injective (L i) := by
      intro i
      obtain ⟨x, hx, hL⟩ := hactual hsne i
      rw [hL]
      exact hreg' x hx
    have hseq : s = ⋃ i, s ∩ t i := by
      rw [← inter_iUnion]
      exact Subset.antisymm (subset_inter Subset.rfl hcover) inter_subset_left
    have hsumimage : μHE[k] (φ '' s) = ∑' i, μHE[k] (φ '' (s ∩ t i)) := by
      conv_lhs => rw [hseq, image_iUnion]
      apply measure_iUnion
      · intro i j hij
        exact Disjoint.image (Disjoint.mono inter_subset_right inter_subset_right (hdisj hij))
          hinj' inter_subset_left inter_subset_left
      · intro i
        apply (hs.inter (ht i)).image_of_continuousOn_injOn
        · exact fun x hx ↦ (hφ' x hx.1).continuousWithinAt.mono inter_subset_left
        · exact hinj'.mono inter_subset_left
    have hsumintegral : (∫⁻ x in s, ENNReal.ofReal (φ' x).toLinearMap.normDet ∂volume) =
        ∑' i, ∫⁻ x in s ∩ t i, ENNReal.ofReal (φ' x).toLinearMap.normDet ∂volume := by
      conv_lhs => rw [hseq]
      exact lintegral_iUnion (fun i ↦ hs.inter (ht i))
        (pairwise_disjoint_mono hdisj (fun _ ↦ inter_subset_right)) _
    have hpiece : ∀ i, μHE[k] (φ '' (s ∩ t i)) ≤ (q : ℝ≥0∞) ^ 2 *
          ∫⁻ x in s ∩ t i, ENNReal.ofReal (φ' x).toLinearMap.normDet ∂volume ∧
        (∫⁻ x in s ∩ t i, ENNReal.ofReal (φ' x).toLinearMap.normDet ∂volume) ≤
          (q : ℝ≥0∞) ^ 2 * μHE[k] (φ '' (s ∩ t i)) := by
      intro i
      have hJ := (hδ (L i) (hLreg i)).1
      obtain ⟨harea_upper, harea_lower⟩ := (hδ (L i) (hLreg i)).2 (s ∩ t i) φ (happrox i)
      have hder := hderiv φ (s ∩ t i) (L i) (δ (L i)) (happrox i) (hs.inter (ht i)) φ'
        (fun x hx ↦ (hφ' x hx.1).mono inter_subset_left)
      have hJupper : (∫⁻ x in s ∩ t i, ENNReal.ofReal (φ' x).toLinearMap.normDet ∂volume) ≤
          q * (ENNReal.ofReal (L i).toLinearMap.normDet * volume (s ∩ t i)) := by
        calc
          _ ≤ ∫⁻ _ in s ∩ t i, (q : ℝ≥0∞) * ENNReal.ofReal (L i).toLinearMap.normDet ∂volume := by
            apply lintegral_mono_ae
            filter_upwards [hder] with x hx
            exact (hJ (φ' x) hx).1
          _ = _ := by rw [setLIntegral_const, mul_assoc]
      have hJlower : ENNReal.ofReal (L i).toLinearMap.normDet * volume (s ∩ t i) ≤
          q * ∫⁻ x in s ∩ t i, ENNReal.ofReal (φ' x).toLinearMap.normDet ∂volume := by
        calc
          _ = ∫⁻ _ in s ∩ t i, ENNReal.ofReal (L i).toLinearMap.normDet ∂volume :=
            (setLIntegral_const _ _).symm
          _ ≤ ∫⁻ x in s ∩ t i, (q : ℝ≥0∞) * ENNReal.ofReal (φ' x).toLinearMap.normDet ∂volume := by
            apply lintegral_mono_ae
            filter_upwards [hder] with x hx
            exact (hJ (φ' x) hx).2
          _ = _ := lintegral_const_mul' _ _ ENNReal.coe_ne_top
      constructor
      · calc
          _ ≤ q * (ENNReal.ofReal (L i).toLinearMap.normDet * volume (s ∩ t i)) := harea_upper
          _ ≤ q * (q * ∫⁻ x in s ∩ t i, ENNReal.ofReal (φ' x).toLinearMap.normDet ∂volume) := by
            gcongr
          _ = _ := by rw [pow_two, mul_assoc]
      · calc
          _ ≤ q * (ENNReal.ofReal (L i).toLinearMap.normDet * volume (s ∩ t i)) := hJupper
          _ ≤ q * (q * μHE[k] (φ '' (s ∩ t i))) := by gcongr
          _ = _ := by rw [pow_two, mul_assoc]
    rw [hsumimage, hsumintegral]
    constructor
    · calc
        _ ≤ ∑' i, (q : ℝ≥0∞) ^ 2 *
            ∫⁻ x in s ∩ t i, ENNReal.ofReal (φ' x).toLinearMap.normDet ∂volume :=
          ENNReal.tsum_le_tsum (fun i ↦ (hpiece i).1)
        _ = _ := ENNReal.tsum_mul_left
    · calc
        _ ≤ ∑' i, (q : ℝ≥0∞) ^ 2 * μHE[k] (φ '' (s ∩ t i)) :=
          ENNReal.tsum_le_tsum (fun i ↦ (hpiece i).2)
        _ = _ := ENNReal.tsum_mul_left
  -- Step 8: the area formula (Simon 3.2), letting `q → 1`.
  have hAF : ∀ (s : Set (Rn k)) (φ : Rn k → Rn N) (φ' : Rn k → Rn k →L[ℝ] Rn N),
      MeasurableSet s → (∀ x ∈ s, HasFDerivWithinAt φ (φ' x) s x) →
      (∀ x ∈ s, Function.Injective (φ' x)) → InjOn φ s →
      μHE[k] (φ '' s) = ∫⁻ x in s, ENNReal.ofReal (φ' x).toLinearMap.normDet ∂volume := by
    intro s φ φ' hs hφ' hreg' hinj'
    have hlimit : ∀ c : ℝ≥0∞, Tendsto (fun q : ℝ≥0 ↦ (q : ℝ≥0∞) ^ 2 * c) (𝓝[>] 1) (𝓝 c) := by
      intro c
      have hcoe : Tendsto (fun q : ℝ≥0 ↦ (q : ℝ≥0∞)) (𝓝[>] 1) (𝓝 1) :=
        (ENNReal.tendsto_coe.2 tendsto_id).mono_left nhdsWithin_le_nhds
      simpa only [one_pow, one_mul] using
        ENNReal.Tendsto.mul_const (ENNReal.Tendsto.pow (n := 2) hcoe) (Or.inl (by simp))
    apply le_antisymm
    · apply ge_of_tendsto (hlimit _)
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact (hcmp s φ φ' hs hφ' hreg' hinj' q hq).1
    · apply ge_of_tendsto (hlimit _)
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact (hcmp s φ φ' hs hφ' hreg' hinj' q hq).2
  -- Step 9: the weighted area formula (Simon 3.5) for the Borel weight `g`, by transporting the
  -- Jacobian-weighted source measure to `Hᵏ` on the image.
  have hWAF : ∀ (s : Set (Rn k)) (φ : Rn k → Rn N) (φ' : Rn k → Rn k →L[ℝ] Rn N),
      MeasurableSet s → (∀ x ∈ s, HasFDerivAt φ (φ' x) x) →
      (∀ x ∈ s, Function.Injective (φ' x)) → InjOn φ s →
      Measurable (fun x ↦ ENNReal.ofReal (φ' x).toLinearMap.normDet) →
      ∫⁻ y in φ '' s, g y ∂μHE[k] =
        ∫⁻ x in s, ENNReal.ofReal (φ' x).toLinearMap.normDet * g (φ x) ∂volume := by
    intro s φ φ' hs hφ' hreg' hinj' hD
    have hcont : ContinuousOn φ s := fun x hx ↦ (hφ' x hx).continuousAt.continuousWithinAt
    have hφt_meas : Measurable (s.piecewise φ (fun _ ↦ 0)) :=
      hcont.measurable_piecewise continuousOn_const hs
    have hφt_eq : ∀ x ∈ s, s.piecewise φ (fun _ ↦ 0) x = φ x :=
      fun x hx ↦ Set.piecewise_eq_of_mem _ _ _ hx
    have hmeas_eq : μHE[k].restrict (φ '' s) = Measure.map (s.piecewise φ (fun _ ↦ 0))
        ((volume.restrict s).withDensity fun x ↦ ENNReal.ofReal (φ' x).toLinearMap.normDet) := by
      ext T hT
      have hpre : s.piecewise φ (fun _ ↦ 0) ⁻¹' T ∩ s = s ∩ φ ⁻¹' T := by
        ext x
        constructor
        · rintro ⟨hxT, hxs⟩
          exact ⟨hxs, by simpa only [mem_preimage, hφt_eq x hxs] using hxT⟩
        · rintro ⟨hxs, hxT⟩
          exact ⟨by simpa only [mem_preimage, hφt_eq x hxs] using hxT, hxs⟩
      have hsub : MeasurableSet (s ∩ φ ⁻¹' T) := by
        rw [← hpre]
        exact (hφt_meas hT).inter hs
      rw [Measure.restrict_apply hT, Measure.map_apply hφt_meas hT,
        withDensity_apply _ (hφt_meas hT), Measure.restrict_restrict (hφt_meas hT), hpre,
        inter_comm, ← image_inter_preimage]
      exact hAF (s ∩ φ ⁻¹' T) φ φ' hsub (fun x hx ↦ (hφ' x hx.1).hasFDerivWithinAt)
        (fun x hx ↦ hreg' x hx.1) (hinj'.mono inter_subset_left)
    calc ∫⁻ y in φ '' s, g y ∂μHE[k]
        = ∫⁻ y, g y ∂(Measure.map (s.piecewise φ (fun _ ↦ 0))
            ((volume.restrict s).withDensity fun x ↦
              ENNReal.ofReal (φ' x).toLinearMap.normDet)) := by
          rw [hmeas_eq]
      _ = ∫⁻ x, g (s.piecewise φ (fun _ ↦ 0) x) ∂((volume.restrict s).withDensity fun x ↦
              ENNReal.ofReal (φ' x).toLinearMap.normDet) := lintegral_map hg hφt_meas
      _ = ∫⁻ x in s, ENNReal.ofReal (φ' x).toLinearMap.normDet *
              g (s.piecewise φ (fun _ ↦ 0) x) ∂volume :=
          lintegral_withDensity_eq_lintegral_mul _ hD (hg.comp hφt_meas)
      _ = ∫⁻ x in s, ENNReal.ofReal (φ' x).toLinearMap.normDet * g (φ x) ∂volume :=
          setLIntegral_congr_fun hs (fun x hx ↦ by simp only [hφt_eq x hx])
  /- Part II: the chart. `j b = (0, b)` is the vertical inclusion; the fibre map over `a` is
  `b ↦ Ψ(a, b)`, with derivative `DΨ(a, b) ∘ j`. -/
  set j : Rn k →L[ℝ] WithLp 2 (Rn m × Rn k) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ (Rn m) (Rn k)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inr ℝ (Rn m) (Rn k))
  have hj_inj : Function.Injective j := by
    intro b b' h
    exact congrArg WithLp.snd h
  have hdiff : ∀ p ∈ Ω, DifferentiableAt ℝ Ψ p := fun p hp ↦
    (hΨ.differentiableOn one_ne_zero p hp).differentiableAt (hΩ.mem_nhds hp)
  -- `S' = Ω ∩ Ψ⁻¹ S` is Borel, via the Borel extension of `Ψ` by `0` off `Ω`.
  have hΨt_meas : Measurable (Ω.piecewise Ψ (fun _ ↦ 0)) :=
    hΨ.continuousOn.measurable_piecewise continuousOn_const hΩ.measurableSet
  have hΨt_eq : ∀ p ∈ Ω, Ω.piecewise Ψ (fun _ ↦ 0) p = Ψ p :=
    fun p hp ↦ Set.piecewise_eq_of_mem _ _ _ hp
  have hS'_meas : MeasurableSet (Ω ∩ Ψ ⁻¹' S) := by
    have hS'_eq : Ω ∩ Ψ ⁻¹' S = Ω ∩ Ω.piecewise Ψ (fun _ ↦ 0) ⁻¹' S := by
      ext p
      constructor
      · rintro ⟨hp, hpS⟩
        exact ⟨hp, by simpa only [mem_preimage, hΨt_eq p hp] using hpS⟩
      · rintro ⟨hp, hpS⟩
        exact ⟨hp, by simpa only [mem_preimage, hΨt_eq p hp] using hpS⟩
    rw [hS'_eq]
    exact hΩ.measurableSet.inter (hΨt_meas hS)
  -- The vertical Jacobian `J_v` is Borel on all of `P`.
  have hJ_meas : Measurable (fun p ↦ ENNReal.ofReal ((fderiv ℝ Ψ p).comp j).toLinearMap.normDet) :=
    ((hcont_nd.comp (continuous_id.clm_comp continuous_const)).measurable.comp
      (measurable_fderiv ℝ Ψ)).ennreal_ofReal
  -- The integrand `H = 1_{S'} · J_v · g ∘ Ψ` is Borel.
  set H : WithLp 2 (Rn m × Rn k) → ℝ≥0∞ := (Ω ∩ Ψ ⁻¹' S).indicator
    (fun p ↦ ENNReal.ofReal ((fderiv ℝ Ψ p).comp j).toLinearMap.normDet * g (Ψ p)) with hH_def
  have hH_meas : Measurable H := by
    have hH_eq : H = (Ω ∩ Ψ ⁻¹' S).indicator (fun p ↦
        ENNReal.ofReal ((fderiv ℝ Ψ p).comp j).toLinearMap.normDet *
          g (Ω.piecewise Ψ (fun _ ↦ 0) p)) := by
      apply Set.indicator_congr
      intro p hp
      simp only [hΨt_eq p hp.1]
    rw [hH_eq]
    exact (hJ_meas.mul (hg.comp hΨt_meas)).indicator hS'_meas
  -- Tonelli through the measure-preserving `toLp : ℝᵐ × ℝᵏ → P`.
  have hHT_meas : Measurable (fun q : Rn m × Rn k ↦ H (WithLp.toLp 2 q)) :=
    hH_meas.comp (WithLp.measurable_toLp 2 _)
  have hTonelli : ∫⁻ p in Ω ∩ Ψ ⁻¹' S,
      ENNReal.ofReal ((fderiv ℝ Ψ p).comp j).toLinearMap.normDet * g (Ψ p) =
        ∫⁻ a, ∫⁻ b, H (WithLp.toLp 2 (a, b)) := by
    rw [← lintegral_indicator hS'_meas, ← hH_def,
      ← (WithLp.volume_preserving_toLp (Rn m) (Rn k)).lintegral_comp hH_meas,
      Measure.volume_eq_prod, lintegral_prod _ hHT_meas.aemeasurable]
  -- The fibre over `a`: the area formula for `b ↦ Ψ(a, b)` on `S'_a = {b | (a, b) ∈ S'}`, whose
  -- image is `S ∩ f⁻¹{a}` because `f ∘ Ψ = fst` on `Ω` and `S ⊆ Ψ(Ω)`.
  have hfiber : ∀ a : Rn m,
      ∫⁻ x in S ∩ f ⁻¹' {a}, g x ∂μHE[k] = ∫⁻ b, H (WithLp.toLp 2 (a, b)) := by
    intro a
    have hι_cont : Continuous (fun b : Rn k ↦ WithLp.toLp 2 (a, b)) :=
      (WithLp.prod_continuous_toLp 2 (Rn m) (Rn k)).comp (continuous_const.prodMk continuous_id)
    have hSa_meas : MeasurableSet ((fun b : Rn k ↦ WithLp.toLp 2 (a, b)) ⁻¹' (Ω ∩ Ψ ⁻¹' S)) :=
      hS'_meas.preimage hι_cont.measurable
    have hψ_deriv : ∀ b ∈ (fun b : Rn k ↦ WithLp.toLp 2 (a, b)) ⁻¹' (Ω ∩ Ψ ⁻¹' S),
        HasFDerivAt (fun b : Rn k ↦ Ψ (WithLp.toLp 2 (a, b)))
          ((fderiv ℝ Ψ (WithLp.toLp 2 (a, b))).comp j) b := by
      intro b hb
      have hι : HasFDerivAt (fun b : Rn k ↦ WithLp.toLp 2 (a, b)) j b :=
        (WithLp.prodContinuousLinearEquiv 2 ℝ (Rn m) (Rn k)).symm.hasFDerivAt.comp b
          (hasFDerivAt_prodMk_right a b)
      exact (hdiff _ hb.1).hasFDerivAt.comp b hι
    have hψ_reg : ∀ b ∈ (fun b : Rn k ↦ WithLp.toLp 2 (a, b)) ⁻¹' (Ω ∩ Ψ ⁻¹' S),
        Function.Injective ((fderiv ℝ Ψ (WithLp.toLp 2 (a, b))).comp j) :=
      fun b hb ↦ (hreg _ hb.1).comp hj_inj
    have hψ_inj : InjOn (fun b : Rn k ↦ Ψ (WithLp.toLp 2 (a, b)))
        ((fun b : Rn k ↦ WithLp.toLp 2 (a, b)) ⁻¹' (Ω ∩ Ψ ⁻¹' S)) := by
      intro b hb b' hb' h
      exact congrArg WithLp.snd (hinj hb.1 hb'.1 h)
    have hψ_image : (fun b : Rn k ↦ Ψ (WithLp.toLp 2 (a, b))) ''
        ((fun b : Rn k ↦ WithLp.toLp 2 (a, b)) ⁻¹' (Ω ∩ Ψ ⁻¹' S)) = S ∩ f ⁻¹' {a} := by
      ext x
      constructor
      · rintro ⟨b, hb, rfl⟩
        exact ⟨hb.2, (hfΨ _ hb.1).trans rfl⟩
      · rintro ⟨hxS, hxa⟩
        obtain ⟨p, hp, rfl⟩ := hSΨ hxS
        have hpa : WithLp.fst p = a := (hfΨ p hp).symm.trans hxa
        have hp_eq : WithLp.toLp 2 (a, WithLp.snd p) = p := by
          rw [← hpa]
          rfl
        refine ⟨WithLp.snd p, ?_, ?_⟩
        · show WithLp.toLp 2 (a, WithLp.snd p) ∈ Ω ∩ Ψ ⁻¹' S
          rw [hp_eq]
          exact ⟨hp, hxS⟩
        · show Ψ (WithLp.toLp 2 (a, WithLp.snd p)) = Ψ p
          rw [hp_eq]
    rw [← hψ_image, hWAF _ _ _ hSa_meas hψ_deriv hψ_reg hψ_inj
      (hJ_meas.comp hι_cont.measurable), ← lintegral_indicator hSa_meas]
    exact lintegral_congr fun b ↦ Set.indicator_comp_right (fun b : Rn k ↦ WithLp.toLp 2 (a, b))
      (s := Ω ∩ Ψ ⁻¹' S)
      (g := fun p ↦ ENNReal.ofReal ((fderiv ℝ Ψ p).comp j).toLinearMap.normDet * g (Ψ p))
  -- Conclusion.
  have hfun : (fun y ↦ ∫⁻ x in S ∩ f ⁻¹' {y}, g x ∂μHE[k]) =
      fun a ↦ ∫⁻ b, H (WithLp.toLp 2 (a, b)) := funext hfiber
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact hHT_meas.lintegral_prod_right'
  · rw [hTonelli, hfun]

/-- **The co-area Jacobian as a norm determinant** (Simon Ch. 2, §6, p. 66). Let `T = T_x M`, let
`L = Df(x) ∘ ι_T : T → ℝᵐ` with `ι_T` the inclusion of `T` in `ℝᴺ`, and let `L*` be the adjoint
of `L`. Then `J*_f(x) = √det(L ∘ L*) = normDet(L*)`. For `g = L*` we have `g* = L`, so
`(normDet g)² = det(g* ∘ g) = det(L ∘ L*)`, and `normDet g ≥ 0`. -/
theorem Submission.coareaJacobian_eq_normDet_adjoint : ∀ (N m : ℕ) (M : Set (Rn N)) (f : Rn N → Rn m) (x : Rn N), coareaJacobian M f x = (LinearMap.adjoint ((fderiv ℝ f x).comp (tangentSpace M x).subtypeL).toLinearMap).normDet := by
  intro N m M f x
  -- Step 3: for `g = L*`, `(normDet g)² = det(g* ∘ₗ g) = det(L ∘ₗ L*)`, as `g* = L`.
  have hsq :=
    (LinearMap.adjoint ((fderiv ℝ f x).comp (tangentSpace M x).subtypeL).toLinearMap).normDet_sq
  rw [LinearMap.adjoint_adjoint] at hsq
  -- Step 4: `normDet g ≥ 0`, so `normDet g = √((normDet g)²)`.
  rw [← Real.sqrt_sq (LinearMap.normDet_nonneg _)]
  -- Steps 1-2 and 5: by unfolding, `coareaJacobian M f x = √det(L ∘ₗ L*)`, since
  -- `ContinuousLinearMap.det` is `LinearMap.det` of the underlying map and the underlying map of
  -- the continuous adjoint is `LinearMap.adjoint`.
  exact congrArg Real.sqrt hsq.symm
/-- **Norm determinant of a block lower-triangular map** (Simon Ch. 2, §6, p. 66: the block
computation behind the co-area Jacobian `J*_f`). Let `E₁, E₂, F₁, F₂` be finite-dimensional real
inner product spaces with `dim E₁ = dim F₁` and `dim E₂ = dim F₂`, and let
`G : E₁ × E₂ → F₁ × F₂` be linear between the `L²` products, with `(G (0, b))₁ = 0` for all `b`.
If `G₁₁ a = (G (a, 0))₁` and `G₂₂ b = (G (0, b))₂`, then `normDet G = normDet G₁₁ · normDet G₂₂`.
In product orthonormal bases the matrix of `G` is block lower-triangular, `[[G₁₁, 0], [*, G₂₂]]`,
and its determinant is the product of the determinants of the diagonal blocks. -/
theorem Submission.coarea_normDet_block_triangular : ∀ (E₁ E₂ F₁ F₂ : Type) [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁] [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂] [NormedAddCommGroup F₁] [InnerProductSpace ℝ F₁] [FiniteDimensional ℝ F₁] [NormedAddCommGroup F₂] [InnerProductSpace ℝ F₂] [FiniteDimensional ℝ F₂] (G : WithLp 2 (E₁ × E₂) →ₗ[ℝ] WithLp 2 (F₁ × F₂)) (G₁₁ : E₁ →ₗ[ℝ] F₁) (G₂₂ : E₂ →ₗ[ℝ] F₂), Module.finrank ℝ E₁ = Module.finrank ℝ F₁ → Module.finrank ℝ E₂ = Module.finrank ℝ F₂ → (∀ b : E₂, WithLp.fst (G (WithLp.toLp 2 (0, b))) = 0) → (∀ a : E₁, G₁₁ a = WithLp.fst (G (WithLp.toLp 2 (a, 0)))) → (∀ b : E₂, G₂₂ b = WithLp.snd (G (WithLp.toLp 2 (0, b)))) → G.normDet = G₁₁.normDet * G₂₂.normDet := by
  intro E₁ E₂ F₁ F₂ _ _ _ _ _ _ _ _ _ _ _ _ G G₁₁ G₂₂ h₁ h₂ h0 hG₁₁ hG₂₂
  classical
  -- Step 1: orthonormal bases indexed by `Fin d₁` (`E₁`, `F₁`) and `Fin d₂` (`E₂`, `F₂`).
  let bE₁ := stdOrthonormalBasis ℝ E₁
  let bE₂ := stdOrthonormalBasis ℝ E₂
  let bF₁ := (stdOrthonormalBasis ℝ F₁).reindex (finCongr h₁.symm)
  let bF₂ := (stdOrthonormalBasis ℝ F₂).reindex (finCongr h₂.symm)
  -- Step 2: the product orthonormal bases of the `L²` products, indexed by `Fin d₁ ⊕ Fin d₂`.
  let bE := bE₁.prod bE₂
  let bF := bF₁.prod bF₂
  -- Step 3: the `bF`-coordinates of `w` are the `bF₁`-coordinates of `w₁` and the
  -- `bF₂`-coordinates of `w₂`.
  have hrepr₁ : ∀ (v : WithLp 2 (F₁ × F₂)) i, bF.repr v (Sum.inl i) = bF₁.repr (WithLp.fst v) i := by
    intro v i
    simp [bF, OrthonormalBasis.repr_apply_apply]
  have hrepr₂ : ∀ (v : WithLp 2 (F₁ × F₂)) i, bF.repr v (Sum.inr i) = bF₂.repr (WithLp.snd v) i := by
    intro v i
    simp [bF, OrthonormalBasis.repr_apply_apply]
  -- Step 4: the matrix of `G` is block lower-triangular, with the matrices of `G₁₁` and `G₂₂` on
  -- the diagonal and a zero upper-right block.
  have hmat : LinearMap.toMatrix bE.toBasis bF.toBasis G =
      Matrix.fromBlocks (LinearMap.toMatrix bE₁.toBasis bF₁.toBasis G₁₁) 0
        (Matrix.of fun i j => bF₂.repr (WithLp.snd (G (WithLp.toLp 2 (bE₁ j, 0)))) i)
        (LinearMap.toMatrix bE₂.toBasis bF₂.toBasis G₂₂) := by
    ext (i | i) (j | j)
    · simp [LinearMap.toMatrix_apply, hrepr₁, bE, hG₁₁]
    · simp [LinearMap.toMatrix_apply, hrepr₁, bE, h0]
    · simp [LinearMap.toMatrix_apply, hrepr₂, bE]
    · simp [LinearMap.toMatrix_apply, hrepr₂, bE, hG₂₂]
  -- Steps 5–6: `normDet` is `‖det‖` of the matrix in orthonormal bases with a common index type,
  -- and `det (fromBlocks A 0 C D) = det A * det D`.
  rw [G.normDet_eq_norm_det_toMatrix bE bF, G₁₁.normDet_eq_norm_det_toMatrix bE₁ bF₁,
    G₂₂.normDet_eq_norm_det_toMatrix bE₂ bF₂, hmat, Matrix.det_fromBlocks_zero₁₂, norm_mul]

/-- **Chart identity for the coarea Jacobian** (Simon Ch. 2, §6, 6.2). If the linear bijection
`Φ : ℝᵐ × ℝᵏ → T` straightens `L : T → ℝᵐ` (`L ∘ Φ = WithLp.fst`) and `Ψ = Φ ∘ (0, ·)`, then
`normDet L* · normDet Φ = normDet Ψ`. In the orthogonal coordinates `C = (π_{Qᗮ}, π_Q)`,
`Q = ker L`, the map `C ∘ Φ` is block lower triangular with diagonal blocks
`α = π_{Qᗮ} ∘ Φ ∘ (·, 0)` and `Ψ` (corestricted to `Q`). Moreover `λ ∘ α = id` for
`λ = L|_{Qᗮ}`, and `normDet λ = normDet L*` because `L*` corestricted to `Qᗮ` is `λ*`. -/
theorem Submission.coarea_normDet_adjoint_mul_normDet_chart : ∀ (m k : ℕ) (T : Type) [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T] (L : T →ₗ[ℝ] Rn m) (Φ : WithLp 2 (Rn m × Rn k) →ₗ[ℝ] T) (Ψ : Rn k →ₗ[ℝ] T), Function.Bijective Φ → (∀ p, L (Φ p) = WithLp.fst p) → (∀ b, Ψ b = Φ (WithLp.toLp 2 (0, b))) → (LinearMap.adjoint L).normDet * Φ.normDet = Ψ.normDet := by
  intro m k T _ _ _ L Φ Ψ hΦ hL hΨ
  -- Step 1: `L` is onto.
  have hsurj : Function.Surjective L := fun a => ⟨Φ (WithLp.toLp 2 (a, 0)), by rw [hL]; rfl⟩
  -- Step 2: `dim P = dim T = m + k`, `dim Q = k` and `dim Qᗮ = m`, where `Q = ker L`.
  have hP : Module.finrank ℝ (WithLp 2 (Rn m × Rn k)) = m + k := by
    rw [(WithLp.linearEquiv 2 ℝ (Rn m × Rn k)).finrank_eq, Module.finrank_prod]
    simp
  have hT : Module.finrank ℝ T = m + k := by
    rw [← (LinearEquiv.ofBijective Φ hΦ).finrank_eq, hP]
  have hQ : Module.finrank ℝ (LinearMap.ker L) = k := by
    have h := L.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hT, finrank_euclideanSpace_fin] at h
    omega
  have hQperp : Module.finrank ℝ (LinearMap.ker L)ᗮ = m := by
    have := (LinearMap.ker L).finrank_add_finrank_orthogonal
    omega
  -- Step 3: the isometric coordinates `C t = (π_{Qᗮ} t, π_Q t)`.
  let C : T ≃ₗᵢ[ℝ] WithLp 2 ((LinearMap.ker L)ᗮ × LinearMap.ker L) :=
    (LinearMap.ker L).orthogonalDecomposition.trans (LinearIsometryEquiv.withLpProdComm 2 ℝ _ _)
  have hC : ∀ t, C t = WithLp.toLp 2 ((LinearMap.ker L)ᗮ.orthogonalProjectionOnto t,
      (LinearMap.ker L).orthogonalProjectionOnto t) := by
    intro t
    simp [C, Submodule.orthogonalDecomposition_apply, LinearIsometryEquiv.withLpProdComm_apply]
  -- Step 4: `G = C ∘ Φ` has `normDet G = normDet C · normDet Φ = normDet Φ`.
  let G : WithLp 2 (Rn m × Rn k) →ₗ[ℝ] WithLp 2 ((LinearMap.ker L)ᗮ × LinearMap.ker L) :=
    C.toLinearEquiv.toLinearMap ∘ₗ Φ
  have hGΦ : G.normDet = Φ.normDet := by
    rw [LinearMap.normDet_comp_of_finrank_eq _ _ (by rw [hP, hT])]
    have : (C.toLinearEquiv.toLinearMap).normDet = 1 := C.toLinearIsometry.normDet_eq_one
    rw [this, one_mul]
  -- Step 5: `Ψ` maps into `Q`, so the upper-right block of `G` vanishes.
  have hΨmem : ∀ b, Ψ b ∈ LinearMap.ker L := by
    intro b; rw [LinearMap.mem_ker, hΨ, hL]; rfl
  have h0 : ∀ b, WithLp.fst (G (WithLp.toLp 2 (0, b))) = 0 := by
    intro b
    simp only [G, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]
    rw [← hΨ, hC]
    simp [Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal
      ((LinearMap.ker L).le_orthogonal_orthogonal (hΨmem b))]
  -- Step 6: the diagonal blocks `α = G₁₁` and `Θ = G₂₂`, where `Θ` is `Ψ` corestricted to `Q`.
  let inl : Rn m →ₗ[ℝ] WithLp 2 (Rn m × Rn k) :=
    (WithLp.linearEquiv 2 ℝ (Rn m × Rn k)).symm.toLinearMap ∘ₗ LinearMap.inl ℝ (Rn m) (Rn k)
  let inr : Rn k →ₗ[ℝ] WithLp 2 (Rn m × Rn k) :=
    (WithLp.linearEquiv 2 ℝ (Rn m × Rn k)).symm.toLinearMap ∘ₗ LinearMap.inr ℝ (Rn m) (Rn k)
  let G₁₁ : Rn m →ₗ[ℝ] (LinearMap.ker L)ᗮ := (WithLp.fstL 2 ℝ _ _).toLinearMap ∘ₗ G ∘ₗ inl
  let G₂₂ : Rn k →ₗ[ℝ] LinearMap.ker L := (WithLp.sndL 2 ℝ _ _).toLinearMap ∘ₗ G ∘ₗ inr
  have hG₂₂ : G₂₂ = Ψ.codRestrict (LinearMap.ker L) hΨmem := by
    refine LinearMap.ext fun b => ?_
    apply Subtype.ext
    simp only [G₂₂, G, inr, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv, LinearMap.codRestrict_apply]
    have : (WithLp.linearEquiv 2 ℝ (Rn m × Rn k)).symm (LinearMap.inr ℝ (Rn m) (Rn k) b) =
        WithLp.toLp 2 (0, b) := rfl
    rw [this, ← hΨ, hC]
    simp [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨Ψ b, hΨmem b⟩]
  -- Step 7: the block lemma gives `normDet G = normDet α · normDet Θ`.
  have hG := Submission.coarea_normDet_block_triangular (Rn m) (Rn k) _ _ G G₁₁ G₂₂
    (by simp [hQperp]) (by simp [hQ]) h0 (fun a => rfl) (fun b => rfl)
  -- Step 8: `λ = L|_{Qᗮ}` satisfies `λ ∘ α = id`, since `L (π_{Qᗮ} t) = L (t - π_Q t) = L t`.
  let lam : (LinearMap.ker L)ᗮ →ₗ[ℝ] Rn m := L.domRestrict (LinearMap.ker L)ᗮ
  have hproj : ∀ t, L ((LinearMap.ker L)ᗮ.orthogonalProjectionOnto t) = L t := by
    intro t
    rw [Submodule.coe_orthogonalProjectionOnto_apply, Submodule.starProjection_orthogonal_val,
      map_sub, LinearMap.mem_ker.mp ((LinearMap.ker L).starProjection_apply_mem t), sub_zero]
  have hlam : lam ∘ₗ G₁₁ = LinearMap.id := by
    refine LinearMap.ext fun a => ?_
    have hα : G₁₁ a = WithLp.fst (C (Φ (WithLp.toLp 2 (a, 0)))) := rfl
    show L (G₁₁ a : T) = a
    rw [hα, hC]
    show L ((LinearMap.ker L)ᗮ.orthogonalProjectionOnto (Φ (WithLp.toLp 2 (a, 0))) : T) = a
    rw [hproj, hL]
    rfl
  have h1 : lam.normDet * G₁₁.normDet = 1 := by
    rw [← LinearMap.normDet_comp_of_finrank_eq _ _ (by simp [hQperp]), hlam, LinearMap.normDet_id]
  -- Step 9: `L*` maps onto `range L* = Qᗮ`, and corestricted to `Qᗮ` it is `λ*`. In orthonormal
  -- bases indexed by `Fin m` the matrix of `λ*` is the transpose of that of `λ`, so
  -- `normDet L* = normDet λ* = normDet λ`.
  have hm : ∀ y, (LinearMap.adjoint L) y ∈ (LinearMap.ker L)ᗮ := by
    intro y
    rw [LinearMap.orthogonal_ker]
    exact LinearMap.mem_range_self _ y
  have ha : (LinearMap.adjoint L).codRestrict (LinearMap.ker L)ᗮ hm = LinearMap.adjoint lam := by
    refine (LinearMap.eq_adjoint_iff _ _).mpr fun y q => ?_
    exact LinearMap.adjoint_inner_left L q y
  have hlamJ : lam.normDet = (LinearMap.adjoint L).normDet := by
    let bQ := (stdOrthonormalBasis ℝ (LinearMap.ker L)ᗮ).reindex (finCongr hQperp)
    let bR := EuclideanSpace.basisFun (Fin m) ℝ
    rw [← LinearMap.normDet_codRestrict hm, ha,
      (LinearMap.adjoint lam).normDet_eq_norm_det_toMatrix bR bQ,
      lam.normDet_eq_norm_det_toMatrix bQ bR, LinearMap.toMatrix_adjoint, Matrix.det_conjTranspose]
    simp
  -- Step 10: `normDet L* · normDet Φ = (normDet λ · normDet α) · normDet Ψ = normDet Ψ`.
  rw [← hGΦ, hG, hG₂₂, LinearMap.normDet_codRestrict, ← hlamJ, ← mul_assoc, h1, one_mul]

/-- **Chart identity for the co-area Jacobian** (part (2) of `coarea_jacobian_linear_algebra`).
Let `A : ℝᵐ × ℝᵏ → ℝᴺ` be injective with `range A = T_x M` and `Df(x) (A p) = p₁`, and let
`B b = A (0, b)`. Then `J*_f(x) · normDet A = normDet B`. Indeed `A` and `B` take values in
`T = T_x M`, and for `L = Df(x)|_T` the codomain restrictions `Φ = A|^T` (bijective) and
`Ψ = B|^T` satisfy `L (Φ p) = p₁` and `Ψ b = Φ (0, b)`, so
`coarea_normDet_adjoint_mul_normDet_chart` gives `normDet L* · normDet Φ = normDet Ψ`. Finally
`J*_f(x) = normDet L*` (`coareaJacobian_eq_normDet_adjoint`), and following a map by the isometric
inclusion `T ⊆ ℝᴺ` does not change `normDet` (`LinearMap.normDet_codRestrict`). -/
theorem Submission.coareaJacobian_mul_normDet_chart : ∀ (N m k : ℕ) (M : Set (Rn N))
    (f : Rn N → Rn m) (x : Rn N) (A : WithLp 2 (Rn m × Rn k) →L[ℝ] Rn N) (B : Rn k →L[ℝ] Rn N),
    Function.Injective A → tangentSpace M x = LinearMap.range A.toLinearMap →
    (∀ p, fderiv ℝ f x (A p) = WithLp.fst p) → (∀ b, B b = A (WithLp.toLp 2 (0, b))) →
    coareaJacobian M f x * A.toLinearMap.normDet = B.toLinearMap.normDet := by
  intro N m k M f x A B hA hT hD hB
  -- Step 1: `A` and `B` take values in `T = T_x M = range A`.
  have hAT : ∀ p, A.toLinearMap p ∈ tangentSpace M x := fun p ↦
    hT ▸ LinearMap.mem_range_self A.toLinearMap p
  have hBT : ∀ b, B.toLinearMap b ∈ tangentSpace M x := fun b ↦ by
    simpa only [ContinuousLinearMap.coe_coe, hB] using hAT (WithLp.toLp 2 (0, b))
  -- Step 2: the codomain restrictions `Φ = A|^T` and `Ψ = B|^T`.
  let Φ := A.toLinearMap.codRestrict (tangentSpace M x) hAT
  let Ψ := B.toLinearMap.codRestrict (tangentSpace M x) hBT
  -- Step 3: `Φ` is bijective, as `A` is injective and `T = range A`.
  have hΦ : Function.Bijective Φ := by
    refine ⟨fun p q hpq ↦ hA (congrArg Subtype.val hpq), fun t ↦ ?_⟩
    obtain ⟨p, hp⟩ : (t : Rn N) ∈ LinearMap.range A.toLinearMap := hT ▸ t.2
    exact ⟨p, Subtype.ext hp⟩
  -- Steps 4–6: for `L = Df(x)|_T`, `L (Φ p) = p₁` (by `hD`) and `Ψ b = Φ (toLp (0, b))` (by `hB`),
  -- so the abstract chart identity applies to `L`, `Φ` and `Ψ`.
  have key := Submission.coarea_normDet_adjoint_mul_normDet_chart m k (tangentSpace M x)
    ((fderiv ℝ f x).comp (tangentSpace M x).subtypeL).toLinearMap Φ Ψ hΦ hD
    fun b ↦ Subtype.ext (hB b)
  -- Steps 7–9: `J*_f(x) = normDet L*`, `normDet Φ = normDet A` and `normDet Ψ = normDet B`.
  rw [Submission.coareaJacobian_eq_normDet_adjoint, ← LinearMap.normDet_codRestrict hAT,
    ← LinearMap.normDet_codRestrict hBT]
  exact key
/-- **Simon Ch. 2, §6 (pp. 66–67), co-area formula: critical fibres.** Volume of a thin slab in a
closed ball: if `‖e‖ = 1`, `ε ≥ 0` and `R ≥ 0`, then
`Lᵐ{v : ‖v - c‖ ≤ R, |⟨e, v - c⟩| ≤ ε} ≤ 2ε (2R)^{m-1}`. Extend `e` to an orthonormal basis `b` with
`b₀ = e`; the coordinates `v ↦ (⟨bᵢ, v - c⟩)ᵢ` preserve Lebesgue measure and map the set into the box
`[-ε, ε] × [-R, R]^{m-1}`. (`m ≥ 1`, as `ℝ⁰` contains no unit vector.) -/
theorem Submission.euclidean_slab_inter_closedBall_volume_le : ∀ (m : ℕ) (e c : Rn m) (ε R : ℝ), ‖e‖ = 1 → 0 ≤ ε → 0 ≤ R → volume {v : Rn m | ‖v - c‖ ≤ R ∧ |inner ℝ e (v - c)| ≤ ε} ≤ ENNReal.ofReal (2 * ε * (2 * R) ^ (m - 1)) := by
  intro m e c ε R he hε hR
  -- Step 1: `m = n + 1`, since `ℝ⁰ = {0}` contains no unit vector.
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := by
    rcases m with _ | n
    · rw [Subsingleton.elim e 0, norm_zero] at he
      exact absurd he zero_ne_one
    · exact ⟨n, rfl⟩
  rw [Nat.add_sub_cancel]
  -- Step 2: an orthonormal basis `b` of `ℝⁿ⁺¹` with `b₀ = e`.
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℝ)
    (E := Rn (n + 1)) (ι := Fin (n + 1)) (by simp) (v := fun _ ↦ e) (s := {0})
    ⟨fun _ ↦ he, fun i j hij ↦ absurd (Subsingleton.elim i j) hij⟩
  have hb0 : b 0 = e := hb 0 rfl
  -- Step 3: the coordinates `Φ v = (⟨bᵢ, v - c⟩)ᵢ` preserve Lebesgue measure.
  set Φ : Rn (n + 1) → Fin (n + 1) → ℝ := fun v ↦ (b.repr (v - c)).ofLp
  have hΦ : MeasurePreserving Φ volume volume :=
    (PiLp.volume_preserving_ofLp _).comp
      (b.measurePreserving_repr.comp (measurePreserving_sub_right volume c))
  -- Step 4: `Φ` maps the set into the box `∏ᵢ [-aᵢ, aᵢ]`, `a₀ = ε`, `aᵢ = R` for `i ≠ 0`.
  set a : Fin (n + 1) → ℝ := Fin.cons ε fun _ ↦ R with ha
  have hsub : {v : Rn (n + 1) | ‖v - c‖ ≤ R ∧ |inner ℝ e (v - c)| ≤ ε} ⊆ Φ ⁻¹' Icc (-a) a := by
    rintro v ⟨hvR, hvε⟩
    have hcoord : ∀ i, |Φ v i| ≤ a i := by
      intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · show |(b.repr (v - c)).ofLp 0| ≤ a 0
        rw [OrthonormalBasis.repr_apply_apply, hb0, ha, Fin.cons_zero]
        exact hvε
      · rw [ha, Fin.cons_succ, ← Real.norm_eq_abs]
        calc ‖(b.repr (v - c)).ofLp j.succ‖ ≤ ‖b.repr (v - c)‖ := PiLp.norm_apply_le _ _
          _ = ‖v - c‖ := b.repr.norm_map _
          _ ≤ R := hvR
    exact ⟨fun i ↦ neg_le_of_abs_le (hcoord i), fun i ↦ le_of_abs_le (hcoord i)⟩
  -- Step 5: the box has volume `2ε (2R)ⁿ`.
  calc volume {v : Rn (n + 1) | ‖v - c‖ ≤ R ∧ |inner ℝ e (v - c)| ≤ ε}
      ≤ volume (Φ ⁻¹' Icc (-a) a) := measure_mono hsub
    _ = volume (Icc (-a) a) := hΦ.measure_preimage measurableSet_Icc.nullMeasurableSet
    _ = ∏ i, ENNReal.ofReal (a i - (-a) i) := Real.volume_Icc_pi
    _ = ENNReal.ofReal (2 * ε * (2 * R) ^ n) := by
      rw [Fin.prod_univ_succ, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity)]
      simp only [ha, Pi.neg_apply, Fin.cons_zero, Fin.cons_succ, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]
      rw [show ε - -ε = 2 * ε by ring, show R - -R = 2 * R by ring]
/-- **Toward Simon Ch. 2, 6.3 and 6.6 (co-area formula).** Volume packing bound: for bounded
`K ⊆ ℝⁿ` there is `C` such that every finite `F ⊆ K` that is `r`-separated, `0 < r ≤ 1`, has
`card F · rⁿ ≤ C`. The open balls `ball x (r/2)`, `x ∈ F`, are pairwise disjoint and lie in
`U = thickening 1 K`, so `card F · (r/2)ⁿ · Lⁿ(ball 0 1) ≤ Lⁿ(U)`; take
`C = 2ⁿ Lⁿ(U) / Lⁿ(ball 0 1)`. -/
theorem Submission.bounded_set_separated_finset_card_mul_pow_le : ∀ (n : ℕ) (K : Set (Rn n)), Bornology.IsBounded K → ∃ C : ℝ, ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ F : Finset (Rn n), (↑F : Set (Rn n)) ⊆ K → (∀ x ∈ F, ∀ y ∈ F, x ≠ y → r < dist x y) → (F.card : ℝ) * r ^ n ≤ C := by
  intro n K hK
  -- Step 1: `U = thickening 1 K` has finite volume `A`; `ball 0 1` has volume `b > 0`.
  set U : Set (Rn n) := Metric.thickening 1 K
  have hUfin : volume U ≠ ⊤ := hK.thickening.measure_lt_top.ne
  set A : ℝ := (volume U).toReal
  set b : ℝ := (volume (Metric.ball (0 : Rn n) 1)).toReal
  have hb : 0 < b := ENNReal.toReal_pos
    (Metric.measure_ball_pos volume (0 : Rn n) one_pos).ne' measure_ball_lt_top.ne
  refine ⟨2 ^ n * A / b, fun r hr hr1 F hFK hsep ↦ ?_⟩
  have hr2 : 0 < r / 2 := by positivity
  -- Step 2: `Lⁿ(ball z (r/2)) = (r/2)ⁿ · Lⁿ(ball 0 1)`.
  have hball : ∀ z : Rn n, volume (Metric.ball z (r / 2)) =
      ENNReal.ofReal ((r / 2) ^ n) * volume (Metric.ball (0 : Rn n) 1) := by
    intro z
    rw [Measure.addHaar_ball_of_pos volume z hr2, finrank_euclideanSpace_fin]
  -- Step 3: the balls `ball x (r/2)`, `x ∈ F`, are pairwise disjoint.
  have hdisj : (↑F : Set (Rn n)).PairwiseDisjoint (fun x ↦ Metric.ball x (r / 2)) := by
    intro x hx y hy hxy
    refine Set.disjoint_left.2 fun z hzx hzy ↦ ?_
    rw [Metric.mem_ball] at hzx hzy
    have h1 := hsep x hx y hy hxy
    have h2 := dist_triangle_left x y z
    linarith
  -- Step 4: they lie in `U`, since `r/2 < 1`.
  have hsub : (⋃ x ∈ F, Metric.ball x (r / 2)) ⊆ U := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨x, hxF, hzx⟩ := hz
    rw [Metric.mem_ball] at hzx
    exact Metric.mem_thickening_iff.2 ⟨x, hFK hxF, by linarith⟩
  -- Step 5: `card F · (r/2)ⁿ · Lⁿ(ball 0 1) = ∑ Lⁿ(ball x (r/2)) = Lⁿ(⋃ ball x (r/2)) ≤ Lⁿ(U)`.
  have hle : (F.card : ℝ≥0∞) * (ENNReal.ofReal ((r / 2) ^ n) * volume (Metric.ball (0 : Rn n) 1))
      ≤ volume U := by
    calc (F.card : ℝ≥0∞) * (ENNReal.ofReal ((r / 2) ^ n) * volume (Metric.ball (0 : Rn n) 1))
        = ∑ x ∈ F, volume (Metric.ball x (r / 2)) := by
          rw [Finset.sum_congr rfl fun x _ ↦ hball x, Finset.sum_const, nsmul_eq_mul]
      _ = volume (⋃ x ∈ F, Metric.ball x (r / 2)) :=
          (measure_biUnion_finset hdisj fun x _ ↦ Metric.isOpen_ball.measurableSet).symm
      _ ≤ volume U := measure_mono hsub
  -- Step 6: real form `card F · ((r/2)ⁿ · b) ≤ A`, as `Lⁿ(U) < ∞`.
  have hreal : (F.card : ℝ) * ((r / 2) ^ n * b) ≤ A := by
    have h := ENNReal.toReal_mono hUfin hle
    rwa [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (by positivity)] at h
  -- Step 7: `card F · rⁿ · b = 2ⁿ · (card F · ((r/2)ⁿ · b)) ≤ 2ⁿ · A`.
  have hpow : (2 : ℝ) ^ n * (r / 2) ^ n = r ^ n := by
    rw [← mul_pow, mul_div_cancel₀ r two_ne_zero]
  rw [le_div_iff₀ hb]
  calc (F.card : ℝ) * r ^ n * b = 2 ^ n * ((F.card : ℝ) * ((r / 2) ^ n * b)) := by
        rw [← hpow]; ring
    _ ≤ 2 ^ n * A := mul_le_mul_of_nonneg_left hreal (by positivity)
/-- **A maximal separated set covers.** Let `K` be a subset of a pseudometric space `X`, `0 ≤ r`, and
suppose every finite `r`-separated `F ⊆ K` (`r < dist x y` for distinct `x, y ∈ F`) has at most `N`
points. Then some finite `r`-separated `F ⊆ K` has `K ⊆ ⋃_{x ∈ F} B̄(x, r)`. Take `F` of the greatest
attained cardinality `Nat.findGreatest P N`, where `P c` says that such an `F` with `c` points exists.
A point `a ∈ K` outside every `B̄(x, r)`, `x ∈ F`, is not in `F` (as `dist a a = 0 ≤ r`), so
`insert a F` would be an `r`-separated subset of `K` with one more point. -/
theorem Submission.exists_separated_finset_subset_cover_closedBall : ∀ (X : Type) [PseudoMetricSpace X] (K : Set X) (r : ℝ) (N : ℕ), 0 ≤ r → (∀ F : Finset X, (↑F : Set X) ⊆ K → (∀ x ∈ F, ∀ y ∈ F, x ≠ y → r < dist x y) → F.card ≤ N) → ∃ F : Finset X, (↑F : Set X) ⊆ K ∧ (∀ x ∈ F, ∀ y ∈ F, x ≠ y → r < dist x y) ∧ K ⊆ ⋃ x ∈ F, closedBall x r := by
  intro X _ K r N hr hN
  classical
  -- Step 1: `P c` says that some finite `r`-separated `F ⊆ K` has `c` points; then `c ≤ N`.
  let P : ℕ → Prop := fun c ↦ ∃ F : Finset X, (↑F : Set X) ⊆ K ∧
    (∀ x ∈ F, ∀ y ∈ F, x ≠ y → r < dist x y) ∧ F.card = c
  have hPN : ∀ c, P c → c ≤ N := fun c ⟨F, hFK, hFr, hFc⟩ ↦ hFc ▸ hN F hFK hFr
  -- Step 2: `P 0` holds with `F = ∅`, so `P (Nat.findGreatest P N)`; fix a witness `F`.
  obtain ⟨F, hFK, hFr, hFc⟩ : P (Nat.findGreatest P N) :=
    Nat.findGreatest_spec (Nat.zero_le N) ⟨∅, by simp, by simp, rfl⟩
  -- Step 3: no finite `r`-separated subset of `K` has `Nat.findGreatest P N + 1` points.
  have hsucc : ¬ P (Nat.findGreatest P N + 1) := fun h ↦
    Nat.findGreatest_is_greatest (Nat.lt_add_one _) (hPN _ h) h
  refine ⟨F, hFK, hFr, fun a ha ↦ ?_⟩
  -- Step 4: otherwise some `a ∈ K` has `r < dist a x` for every `x ∈ F`.
  by_contra hcov
  have haF : ∀ x ∈ F, r < dist a x := fun x hx ↦
    lt_of_not_ge fun h ↦ hcov (mem_iUnion₂.2 ⟨x, hx, mem_closedBall.2 h⟩)
  -- Step 5: `a ∉ F`, as `dist a a = 0 ≤ r`.
  have ha' : a ∉ F := fun h ↦ (haF a h).not_ge (by rw [dist_self]; exact hr)
  -- Steps 6–7: `insert a F` has `Nat.findGreatest P N + 1` points, contradicting step 3.
  refine hsucc ⟨insert a F, ?_, ?_, ?_⟩
  · rw [Finset.coe_insert]
    exact Set.insert_subset ha hFK
  · intro x hx y hy hxy
    rcases Finset.mem_insert.1 hx with rfl | hxF <;> rcases Finset.mem_insert.1 hy with rfl | hyF
    · exact (hxy rfl).elim
    · exact haF y hyF
    · rw [dist_comm]
      exact haF x hxF
    · exact hFr x hxF y hyF hxy
  · rw [Finset.card_insert_of_notMem ha', hFc]
/-- **Simon Ch. 2, §6 (pp. 66–67), critical fibres: covering and Fatou step.** If for all
`ε, δ > 0` the set `K` is covered by finitely many closed balls `closedBall x r` with `2 r ≤ δ`
and `∑ₓ (2 r) ^ k ν (G '' closedBall x r) ≤ ε`, then `μH[k] (K ∩ G ⁻¹' {y}) = 0` for
`ν`-a.e. `y`. -/
theorem Submission.ae_hausdorffMeasure_fiber_eq_zero_of_small_ball_covers : ∀ (X Y : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] (ν : Measure Y) (k : ℕ) (K : Set X) (G : X → Y), (∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → ∃ (s : Finset X) (r : ℝ), 0 < r ∧ 2 * r ≤ δ ∧ K ⊆ ⋃ x ∈ s, closedBall x r ∧ ∑ x ∈ s, ENNReal.ofReal ((2 * r) ^ k) * ν (G '' closedBall x r) ≤ ENNReal.ofReal ε) → ∀ᵐ y ∂ν, μH[k] (K ∩ G ⁻¹' {y}) = 0 := by
  intro X Y _ _ _ _ ν k K G h
  classical
  -- Step 1: covers `(s j, r j)` for `ε = δ = 1 / (j + 1)`; these scales tend to `0`.
  choose s r hr hrd hcov hsum using fun j : ℕ ↦
    h (1 / ((j : ℝ) + 1)) Nat.one_div_pos_of_nat (1 / ((j : ℝ) + 1)) Nat.one_div_pos_of_nat
  have hd : Tendsto (fun j : ℕ ↦ ENNReal.ofReal (1 / ((j : ℝ) + 1))) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    rwa [ENNReal.ofReal_zero] at this
  -- `ediam (closedBall x (r j)) ≤ 2 r j`, hence `ediam (closedBall x (r j)) ^ k ≤ (2 r j) ^ k`.
  have hdiam : ∀ j (x : X), ediam (closedBall x (r j)) ≤ ENNReal.ofReal (2 * r j) := fun j x ↦
    ediam_le_of_forall_dist_le fun a ha b hb ↦ by
      linarith [dist_triangle_right a b x, mem_closedBall.1 ha, mem_closedBall.1 hb]
  have hpow : ∀ j (x : X),
      ediam (closedBall x (r j)) ^ (k : ℝ) ≤ ENNReal.ofReal ((2 * r j) ^ k) := by
    intro j x
    rw [ENNReal.rpow_natCast, ENNReal.ofReal_pow (mul_pos two_pos (hr j)).le]
    exact pow_le_pow_left₀ zero_le (hdiam j x) k
  -- Step 2: measurable majorants `S j = ∑_{x ∈ s j} (2 r j)^k 1_{T j x}`, where
  -- `T j x = toMeasurable ν (G '' closedBall x (r j))` has the same measure as the image.
  obtain ⟨S, hSm, hSi, hSy⟩ : ∃ S : ℕ → Y → ℝ≥0∞, (∀ j, Measurable (S j)) ∧
      (∀ j, ∫⁻ y, S j y ∂ν ≤ ENNReal.ofReal (1 / ((j : ℝ) + 1))) ∧
      ∀ j y, ∑ x ∈ s j with y ∈ G '' closedBall x (r j), ENNReal.ofReal ((2 * r j) ^ k) ≤
        S j y := by
    have hm : ∀ j x, Measurable ((toMeasurable ν (G '' closedBall x (r j))).indicator
        fun _ : Y ↦ ENNReal.ofReal ((2 * r j) ^ k)) := fun j x ↦
      measurable_const.indicator (measurableSet_toMeasurable _ _)
    refine ⟨fun j y ↦ ∑ x ∈ s j, (toMeasurable ν (G '' closedBall x (r j))).indicator
      (fun _ ↦ ENNReal.ofReal ((2 * r j) ^ k)) y, fun j ↦ Finset.measurable_sum _ fun x _ ↦ hm j x,
      fun j ↦ ?_, fun j y ↦ ?_⟩
    · rw [lintegral_finsetSum _ fun x _ ↦ hm j x]
      simp_rw [lintegral_indicator_const (measurableSet_toMeasurable _ _), measure_toMeasurable]
      exact hsum j
    · rw [Finset.sum_filter]
      refine Finset.sum_le_sum fun x _ ↦ ?_
      split_ifs with hy
      · rw [indicator_of_mem (subset_toMeasurable _ _ hy)]
      · exact zero_le
  -- Step 3: Fatou's lemma gives `liminf_j S j y = 0` for `ν`-a.e. `y`.
  have hae : ∀ᵐ y ∂ν, liminf (fun j ↦ S j y) atTop = 0 := by
    refine (lintegral_eq_zero_iff (Measurable.liminf hSm)).1 (le_antisymm ?_ zero_le)
    calc ∫⁻ y, liminf (fun j ↦ S j y) atTop ∂ν
        ≤ liminf (fun j ↦ ∫⁻ y, S j y ∂ν) atTop := lintegral_liminf_le hSm
      _ ≤ liminf (fun j : ℕ ↦ ENNReal.ofReal (1 / ((j : ℝ) + 1))) atTop :=
          liminf_le_liminf (Eventually.of_forall hSi)
      _ = 0 := hd.liminf_eq
  -- Steps 4–6: for such `y`, the balls `closedBall x (r j)`, `x ∈ s j`, whose image contains `y`
  -- cover the fibre; bound `μH[k]` of the fibre by `liminf_j S j y = 0`.
  filter_upwards [hae] with y hy
  set F : ℕ → Finset X := fun j ↦ {x ∈ s j | y ∈ G '' closedBall x (r j)}
  refine le_antisymm ?_ zero_le
  calc μH[k] (K ∩ G ⁻¹' {y})
      ≤ liminf (fun j ↦ ∑ i : F j, ediam (closedBall (i : X) (r j)) ^ (k : ℝ)) atTop :=
        Measure.hausdorffMeasure_le_liminf_sum (ι := fun j ↦ ↥(F j)) _ _ _ hd
          (fun j i ↦ closedBall (i : X) (r j))
          (Eventually.of_forall fun j i ↦ (hdiam j i).trans (ENNReal.ofReal_le_ofReal (hrd j)))
          (Eventually.of_forall fun j a ha ↦ by
            obtain ⟨x, hx, hax⟩ := mem_iUnion₂.1 (hcov j ha.1)
            exact mem_iUnion.2 ⟨⟨x, Finset.mem_filter.2 ⟨hx, a, hax, ha.2⟩⟩, hax⟩)
    _ ≤ liminf (fun j ↦ S j y) atTop := by
        refine liminf_le_liminf (Eventually.of_forall fun j ↦ ?_)
        calc ∑ i : F j, ediam (closedBall (i : X) (r j)) ^ (k : ℝ)
            ≤ ∑ _i : F j, ENNReal.ofReal ((2 * r j) ^ k) := Finset.sum_le_sum fun i _ ↦ hpow j i
          _ = ∑ _x ∈ F j, ENNReal.ofReal ((2 * r j) ^ k) :=
            Finset.sum_coe_sort (s := F j) (f := fun _ ↦ ENNReal.ofReal ((2 * r j) ^ k))
          _ ≤ S j y := hSy j y
    _ = 0 := hy

/-- **`J*_f(x) = 0` iff `Df(x) ∘ A` is not onto** (Simon Ch. 2, §6, p. 66: `J*_f(x) ≠ 0`
precisely when `df_x` has rank `m`), for `A : ℝⁿ → ℝᴺ` with `T_x M = range A`. With
`L = df_x = Df(x)|_{T_x M}`, `J*_f(x) = normDet(L*)` (`coareaJacobian_eq_normDet_adjoint`), which
vanishes iff `ker L* = (range L)ᗮ ≠ 0`, i.e. iff `L` is not onto; and `L` is onto iff `Df(x) ∘ A`
is, since both have range `Df(x)(T_x M)`. -/
theorem Submission.coareaJacobian_eq_zero_iff_not_surjective : ∀ (N m n : ℕ) (M : Set (Rn N))
    (f : Rn N → Rn m) (x : Rn N) (A : Rn n →L[ℝ] Rn N),
    tangentSpace M x = LinearMap.range A.toLinearMap →
    (coareaJacobian M f x = 0 ↔ ¬ Function.Surjective ((fderiv ℝ f x).comp A)) := by
  intro N m n M f x A hT
  -- Steps 1–3: `J*_f(x) = normDet(L*)` vanishes iff `(range L)ᗮ = ker L* ≠ 0` iff `L` is not onto.
  rw [Submission.coareaJacobian_eq_normDet_adjoint, LinearMap.normDet_eq_zero_iff_ker_ne_bot,
    ← LinearMap.orthogonal_range, ne_eq, Submodule.orthogonal_eq_bot_iff, LinearMap.range_eq_top]
  -- Step 4: since `T_x M = range A`, `L` is onto iff `Df(x) ∘ A` is.
  refine not_congr ⟨fun hs y ↦ ?_, fun hs y ↦ ?_⟩
  · obtain ⟨t, rfl⟩ := hs y
    obtain ⟨z, hz⟩ : (t : Rn N) ∈ LinearMap.range A.toLinearMap := hT ▸ t.2
    exact ⟨z, congrArg (fderiv ℝ f x) hz⟩
  · obtain ⟨z, rfl⟩ := hs y
    exact ⟨⟨A z, hT ▸ LinearMap.mem_range_self A.toLinearMap z⟩, rfl⟩

/-- **Linear algebra of the co-area Jacobian** (Simon Ch. 2, §6, 6.2, p. 66). Let `T = T_x M`,
`D = Df(x)` and `L = D|_T : T → ℝᵐ`, so that `J*_f(x) = √det(L L*)`.
(1) If `A : ℝⁿ → ℝᴺ` is linear with `T = range A`, then `J*_f(x) = 0` iff `D ∘ A` is not onto.
(2) Let `A : ℝᵐ × ℝᵏ → ℝᴺ` (Euclidean product) be injective and linear with `T = range A` and
`D (A p) = p₁`, and let `B b = A (0, b)`. Then `J*_f(x) · normDet A = normDet B`.
Part (1) is `coareaJacobian_eq_zero_iff_not_surjective` and part (2) is
`coareaJacobian_mul_normDet_chart`. -/
theorem Submission.coarea_jacobian_linear_algebra : (∀ (N m n : ℕ) (M : Set (Rn N)) (f : Rn N → Rn m) (x : Rn N) (A : Rn n →L[ℝ] Rn N), tangentSpace M x = LinearMap.range A.toLinearMap → (coareaJacobian M f x = 0 ↔ ¬ Function.Surjective ((fderiv ℝ f x).comp A))) ∧ ∀ (N m k : ℕ) (M : Set (Rn N)) (f : Rn N → Rn m) (x : Rn N) (A : WithLp 2 (Rn m × Rn k) →L[ℝ] Rn N) (B : Rn k →L[ℝ] Rn N), Function.Injective A → tangentSpace M x = LinearMap.range A.toLinearMap → (∀ p, fderiv ℝ f x (A p) = WithLp.fst p) → (∀ b, B b = A (WithLp.toLp 2 (0, b))) → coareaJacobian M f x * A.toLinearMap.normDet = B.toLinearMap.normDet :=
  -- Part (1), Steps 1–3: `J*_f(x) = 0` iff `L` is not onto, and `range L = range (D ∘ A)`.
  -- Part (2), Steps 4–9: corestrict `A` and `B` to `T` and compute in block-triangular form.
  ⟨Submission.coareaJacobian_eq_zero_iff_not_surjective,
    Submission.coareaJacobian_mul_normDet_chart⟩
/-- **Image of a ball under a map whose derivative is not surjective.** Let `G : ℝⁿ → ℝᵐ` be
differentiable on `B̄(x, r)`, with `‖DG(z) - DG(x)‖ ≤ η` there, `‖DG(x)‖ ≤ L` and `DG(x)` not
surjective. Then `Lᵐ(G(B̄(x, r))) ≤ 2(ηr)(2(L + η)r)^{m-1}`. This bounds the images of small balls
centred at critical points, for the critical fibres in Simon Ch. 2, 6.4 (the same slab argument
proves Sard's theorem for `C¹` maps between spaces of equal dimension; Spivak, *Calculus on
Manifolds*, 3-14). The range of `A = DG(x)` is proper, so it has a unit normal `e`
(`Submodule.orthogonal_eq_bot_iff`). By the mean value inequality,
`‖G(z) - G(x) - A(z - x)‖ ≤ ηr` on the ball, so `G(B̄(x, r))` lies in the slab
`{w : ‖w - G(x)‖ ≤ (L + η)r, |⟨e, w - G(x)⟩| ≤ ηr}`, whose volume is bounded by
`euclidean_slab_inter_closedBall_volume_le`. -/
theorem Submission.volume_image_closedBall_le_of_fderiv_not_surjective : ∀ (n m : ℕ) (G : Rn n → Rn m) (x : Rn n) (r η L : ℝ), 0 ≤ r → (∀ z ∈ closedBall x r, DifferentiableAt ℝ G z) → (∀ z ∈ closedBall x r, ‖fderiv ℝ G z - fderiv ℝ G x‖ ≤ η) → ‖fderiv ℝ G x‖ ≤ L → ¬ Function.Surjective (fderiv ℝ G x) → volume (G '' closedBall x r) ≤ ENNReal.ofReal (2 * (η * r) * (2 * ((L + η) * r)) ^ (m - 1)) := by
  intro n m G x r η L hr hdiff hbound hL hns
  set A := fderiv ℝ G x
  -- Step 1 (signs): `x ∈ B̄(x, r)`, so `η ≥ ‖A - A‖ ≥ 0`; and `L ≥ ‖A‖ ≥ 0`.
  have hx : x ∈ closedBall x r := mem_closedBall_self hr
  have hη : 0 ≤ η := (norm_nonneg _).trans (hbound x hx)
  have hL0 : 0 ≤ L := (norm_nonneg A).trans hL
  -- Step 2 (unit normal): `range A ≠ ⊤`, so `(range A)ᗮ ≠ ⊥` contains some `u ≠ 0`, and
  -- `e = ‖u‖⁻¹ • u` is a unit vector with `⟨e, A w⟩ = 0` for every `w`.
  obtain ⟨e, he, hAe⟩ : ∃ e : Rn m, ‖e‖ = 1 ∧ ∀ w, inner ℝ e (A w) = 0 := by
    have hW : (LinearMap.range (A : Rn n →ₗ[ℝ] Rn m))ᗮ ≠ ⊥ := by
      rw [Ne, Submodule.orthogonal_eq_bot_iff, LinearMap.range_eq_top]
      exact hns
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    refine ⟨‖u‖⁻¹ • u, ?_, fun w ↦ ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hu0)]
    · rw [real_inner_smul_left,
        (Submodule.mem_orthogonal' _ u).1 hu (A w) (LinearMap.mem_range_self _ w), mul_zero]
  -- Steps 3–4 (mean value inequality, slab containment): for `z ∈ B̄(x, r)` the remainder
  -- `d = G z - G x - A (z - x)` has `‖d‖ ≤ η‖z - x‖ ≤ ηr`. Hence
  -- `‖G z - G x‖ ≤ ‖A‖‖z - x‖ + ηr ≤ (L + η)r` and `|⟨e, G z - G x⟩| = |⟨e, d⟩| ≤ ‖d‖ ≤ ηr`.
  have hsub : G '' closedBall x r ⊆
      {v : Rn m | ‖v - G x‖ ≤ (L + η) * r ∧ |inner ℝ e (v - G x)| ≤ η * r} := by
    rintro _ ⟨z, hz, rfl⟩
    have hzx : ‖z - x‖ ≤ r := mem_closedBall_iff_norm.1 hz
    have hd : ‖G z - G x - A (z - x)‖ ≤ η * r :=
      ((convex_closedBall x r).norm_image_sub_le_of_norm_fderiv_le' hdiff hbound hx hz).trans
        (mul_le_mul_of_nonneg_left hzx hη)
    constructor
    · calc ‖G z - G x‖ = ‖A (z - x) + (G z - G x - A (z - x))‖ := by rw [add_sub_cancel]
        _ ≤ ‖A‖ * ‖z - x‖ + η * r := (norm_add_le _ _).trans (add_le_add (A.le_opNorm _) hd)
        _ ≤ L * r + η * r := add_le_add (mul_le_mul hL hzx (norm_nonneg _) hL0) le_rfl
        _ = (L + η) * r := (add_mul L η r).symm
    · calc |inner ℝ e (G z - G x)| = |inner ℝ e (G z - G x - A (z - x))| := by
            rw [inner_sub_right e (G z - G x), hAe, sub_zero]
        _ ≤ ‖e‖ * ‖G z - G x - A (z - x)‖ := abs_real_inner_le_norm _ _
        _ ≤ η * r := by rw [he, one_mul]; exact hd
  -- Step 5 (volume): monotonicity, then the slab bound with `ε = ηr` and `R = (L + η)r`.
  exact (measure_mono hsub).trans
    (Submission.euclidean_slab_inter_closedBall_volume_le m e (G x) (η * r) ((L + η) * r) he
      (mul_nonneg hη hr) (mul_nonneg (add_nonneg hL0 hη) hr))
/-- **Closed-ball covers of a bounded set in `ℝⁿ`.** Let `K ⊆ ℝⁿ` be bounded. There is `C` such that
for every `0 < r ≤ 1` some finite `s ⊆ K` has `K ⊆ ⋃_{x ∈ s} B̄(x, r)` and `card(s)·rⁿ ≤ C`. Take `C`
from the packing bound: `card(F)·rⁿ ≤ C` for every finite `r`-separated `F ⊆ K`. As `0 < rⁿ`, every
such `F` has at most `⌊C / rⁿ⌋₊` points, so a maximal `r`-separated `F ⊆ K` covers `K` by closed
`r`-balls, and the packing bound applies to this `F` as well. -/
theorem Submission.bounded_set_closedBall_cover_card_mul_pow_le : ∀ (n : ℕ) (K : Set (Rn n)), Bornology.IsBounded K → ∃ C : ℝ, ∀ r : ℝ, 0 < r → r ≤ 1 → ∃ s : Finset (Rn n), (↑s : Set (Rn n)) ⊆ K ∧ K ⊆ ⋃ x ∈ s, closedBall x r ∧ (s.card : ℝ) * r ^ n ≤ C := by
  intro n K hK
  -- Step 1: the packing bound gives `C`, fixed before `r` is chosen.
  obtain ⟨C, hC⟩ := Submission.bounded_set_separated_finset_card_mul_pow_le n K hK
  refine ⟨C, fun r hr hr1 ↦ ?_⟩
  -- Step 2: as `0 < rⁿ`, every finite `r`-separated `F ⊆ K` has at most `⌊C / rⁿ⌋₊` points.
  have hN : ∀ F : Finset (Rn n), (↑F : Set (Rn n)) ⊆ K →
      (∀ x ∈ F, ∀ y ∈ F, x ≠ y → r < dist x y) → F.card ≤ ⌊C / r ^ n⌋₊ :=
    fun F hFK hFr ↦ Nat.le_floor ((le_div_iff₀ (pow_pos hr n)).2 (hC r hr hr1 F hFK hFr))
  -- Step 3: hence some finite `r`-separated `F ⊆ K` covers `K` by closed `r`-balls.
  obtain ⟨F, hFK, hFr, hcov⟩ :=
    Submission.exists_separated_finset_subset_cover_closedBall (Rn n) K r ⌊C / r ^ n⌋₊ hr.le hN
  -- Step 4: take `s := F`; the packing bound gives `card(F)·rⁿ ≤ C`.
  exact ⟨F, hFK, hcov, hC r hr hr1 F hFK hFr⟩

/-- **Simon Ch. 2, §6 (pp. 66–67), toward `Hᵏ(C ∩ f⁻¹(y)) = 0` for `Lᵐ`-a.e. `y` (6.3, 6.4):
small ball covers of the critical set on a compact set.** Let `n = m + k`, `G : ℝⁿ → ℝᵐ` be `C¹`
on the open `V`, `Q ⊆ V` compact and `K = {x ∈ Q : DG(x) not surjective}`. For `ε, δ > 0` there
are closed balls `B̄(x, r)`, `x ∈ s`, `2r ≤ δ`, covering `K` with `∑ₓ (2r)ᵏ Lᵐ(G(B̄(x, r))) ≤ ε`.
If `m = 0` then `K = ∅`. Otherwise `DG` is bounded by `L ≥ 0` and uniformly continuous on a compact
thickening `K₁ ⊆ V` of `Q`. Cover `K` by balls of a small radius `r` centred in `K`, with
`card s · rⁿ ≤ C'` (`bounded_set_closedBall_cover_card_mul_pow_le`). On each ball `DG` stays
within `η` of the non-surjective `DG(x)`, so `Lᵐ(G(B̄(x, r))) ≤ 2ηr (2(L + η)r)^{m-1}`
(`volume_image_closedBall_le_of_fderiv_not_surjective`). As `n = m + k`, the sum is at most
`2^{k+m} η (L + 1)^{m-1} C'`, which is `≤ ε` for small `η`. -/
theorem Submission.critical_set_small_ball_covers_of_isCompact : ∀ (m k : ℕ) (V Q : Set (Rn (m + k))) (G : Rn (m + k) → Rn m), IsOpen V → ContDiffOn ℝ 1 G V → IsCompact Q → Q ⊆ V → ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → ∃ (s : Finset (Rn (m + k))) (r : ℝ), 0 < r ∧ 2 * r ≤ δ ∧ {x | x ∈ Q ∧ ¬ Function.Surjective (fderiv ℝ G x)} ⊆ ⋃ x ∈ s, closedBall x r ∧ ∑ x ∈ s, ENNReal.ofReal ((2 * r) ^ k) * volume (G '' closedBall x r) ≤ ENNReal.ofReal ε := by
  intro m k V Q G hV hG hQ hQV ε hε δ hδ
  -- Step 1: if `m = 0`, every linear map into `ℝ⁰ = {0}` is surjective, so `K = ∅`.
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨∅, δ / 4, by positivity, by linarith, ?_, by simp⟩
    rintro x ⟨-, hx⟩
    exact (hx fun y ↦ ⟨0, Subsingleton.elim _ y⟩).elim
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  -- Step 2: a compact thickening `K₁ = cthickening ρ₀ Q ⊆ V` of `Q`.
  obtain ⟨ρ₀, hρ₀, hK₁V⟩ := hQ.exists_cthickening_subset_open hV hQV
  have hK₁ : IsCompact (cthickening ρ₀ Q) := hQ.cthickening
  -- Step 3: `G` is differentiable on `V`; `DG` is continuous on `V`, hence bounded by some `L ≥ 0`
  -- and uniformly continuous on `K₁`.
  have hdiff : ∀ z ∈ V, DifferentiableAt ℝ G z := fun z hz ↦
    (hG.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds hz)
  have hcont : ContinuousOn (fderiv ℝ G) (cthickening ρ₀ Q) :=
    (hG.continuousOn_fderiv_of_isOpen hV le_rfl).mono hK₁V
  obtain ⟨L, hL0, hL⟩ : ∃ L : ℝ, 0 ≤ L ∧ ∀ z ∈ cthickening ρ₀ Q, ‖fderiv ℝ G z‖ ≤ L := by
    obtain ⟨L, hL⟩ := hK₁.exists_bound_of_continuousOn hcont
    exact ⟨max L 0, le_max_right _ _, fun z hz ↦ (hL z hz).trans (le_max_left _ _)⟩
  have hUC := Metric.uniformContinuousOn_iff.1 (hK₁.uniformContinuousOn_of_continuous hcont)
  -- Step 4: the covering constant of the bounded set `K ⊆ Q`, made nonnegative.
  have hKb : Bornology.IsBounded {x | x ∈ Q ∧ ¬ Function.Surjective (fderiv ℝ G x)} :=
    hQ.isBounded.subset fun x hx ↦ hx.1
  obtain ⟨C, hC⟩ := Submission.bounded_set_closedBall_cover_card_mul_pow_le (m' + 1 + k) _ hKb
  obtain ⟨C', hC'0, hCC'⟩ : ∃ C' : ℝ, 0 ≤ C' ∧ C ≤ C' :=
    ⟨max C 0, le_max_right _ _, le_max_left _ _⟩
  -- Step 5: `η = min 1 (ε / (D + 1))` with `D = 2^{k+m} (L + 1)^{m'} C'`, then `ρ` from uniform
  -- continuity for `η`, and `r = min (min ρ₀ (δ / 2)) (min (ρ / 2) 1)`.
  obtain ⟨η, hη, hη1, hDη⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧
      2 ^ (k + (m' + 1)) * (L + 1) ^ m' * C' * η ≤ ε := by
    have hD : 0 ≤ 2 ^ (k + (m' + 1)) * (L + 1) ^ m' * C' := by positivity
    generalize 2 ^ (k + (m' + 1)) * (L + 1) ^ m' * C' = D at hD ⊢
    refine ⟨min 1 (ε / (D + 1)), lt_min one_pos (div_pos hε (by linarith)), min_le_left _ _, ?_⟩
    calc D * min 1 (ε / (D + 1)) ≤ D * (ε / (D + 1)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hD
      _ ≤ ε := by
          rw [mul_div_assoc', div_le_iff₀ (by linarith)]
          nlinarith
  obtain ⟨ρ, hρ, hρUC⟩ := hUC η hη
  obtain ⟨r, hr, hrρ₀, hrδ, hrρ, hr1⟩ :
      ∃ r : ℝ, 0 < r ∧ r ≤ ρ₀ ∧ 2 * r ≤ δ ∧ r < ρ ∧ r ≤ 1 :=
    ⟨min (min ρ₀ (δ / 2)) (min (ρ / 2) 1),
      lt_min (lt_min hρ₀ (by linarith)) (lt_min (by linarith) one_pos),
      (min_le_left _ _).trans (min_le_left _ _),
      by linarith [min_le_left (min ρ₀ (δ / 2)) (min (ρ / 2) 1), min_le_right ρ₀ (δ / 2)],
      ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (half_lt_self hρ),
      (min_le_right _ _).trans (min_le_right _ _)⟩
  -- Step 6: the cover of `K` by the balls `B̄(x, r)`, `x ∈ s ⊆ K`, with `card s · rⁿ ≤ C ≤ C'`.
  obtain ⟨s, hsK, hKs, hcard⟩ := hC r hr hr1
  refine ⟨s, r, hr, hrδ, hKs, ?_⟩
  -- Step 7: one ball. `B̄(x, r) ⊆ K₁ ⊆ V`, `‖DG(z) - DG(x)‖ ≤ η` on it and `‖DG(x)‖ ≤ L`.
  have hball : ∀ x ∈ s, volume (G '' closedBall x r) ≤
      ENNReal.ofReal (2 * (η * r) * (2 * ((L + η) * r)) ^ m') := by
    intro x hx
    obtain ⟨hxQ, hxs⟩ := hsK (Finset.mem_coe.2 hx)
    have hxK₁ : x ∈ cthickening ρ₀ Q := self_subset_cthickening Q hxQ
    have hsub : closedBall x r ⊆ cthickening ρ₀ Q := fun z hz ↦
      mem_cthickening_of_dist_le z x ρ₀ Q hxQ ((mem_closedBall.1 hz).trans hrρ₀)
    have h := Submission.volume_image_closedBall_le_of_fderiv_not_surjective (m' + 1 + k) (m' + 1)
      G x r η L hr.le (fun z hz ↦ hdiff z (hK₁V (hsub hz)))
      (fun z hz ↦ by
        rw [← dist_eq_norm]
        exact (hρUC z (hsub hz) x hxK₁ ((mem_closedBall.1 hz).trans_lt hrρ)).le)
      (hL x hxK₁) hxs
    rwa [Nat.add_sub_cancel] at h
  -- Step 8: summation, using `n = m' + 1 + k`.
  have hk : 0 ≤ (2 * r) ^ k := by positivity
  calc ∑ x ∈ s, ENNReal.ofReal ((2 * r) ^ k) * volume (G '' closedBall x r)
      ≤ ∑ x ∈ s, ENNReal.ofReal ((2 * r) ^ k) *
          ENNReal.ofReal (2 * (η * r) * (2 * ((L + η) * r)) ^ m') :=
        Finset.sum_le_sum fun x hx ↦ by gcongr; exact hball x hx
    _ = ENNReal.ofReal ((s.card : ℝ) *
          ((2 * r) ^ k * (2 * (η * r) * (2 * ((L + η) * r)) ^ m'))) := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_mul hk, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    _ = ENNReal.ofReal (2 ^ (k + (m' + 1)) * η * (L + η) ^ m' *
          ((s.card : ℝ) * r ^ (m' + 1 + k))) := by
        congr 1
        simp only [mul_pow]
        ring
    _ ≤ ENNReal.ofReal (2 ^ (k + (m' + 1)) * η * (L + 1) ^ m' * C') := by
        gcongr
        exact hcard.trans hCC'
    _ ≤ ENNReal.ofReal ε := by
        apply ENNReal.ofReal_le_ofReal
        calc 2 ^ (k + (m' + 1)) * η * (L + 1) ^ m' * C'
            = 2 ^ (k + (m' + 1)) * (L + 1) ^ m' * C' * η := by ring
          _ ≤ ε := hDη

/-- **Simon Ch. 2, §6 (p. 67), critical fibres of a `C¹` map on an open set of `ℝ^{m+k}`.** Let
`V ⊆ ℝ^{m+k}` be open and `G : ℝ^{m+k} → ℝᵐ` of class `C¹` on `V`. Then for `Lᵐ`-a.e. `y`, the set
`{x ∈ V : DG(x) not surjective} ∩ G⁻¹{y}` is `Hᵏ`-null. The open set `V` is σ-compact. On each
compact piece `Q ⊆ V`, the small ball covers of the critical set
(`critical_set_small_ball_covers_of_isCompact`) are exactly the hypothesis of the Fatou argument
(`ae_hausdorffMeasure_fiber_eq_zero_of_small_ball_covers`). A countable union of `μH[k]`-null sets
and `μHE[k] = c_k • μH[k]` then give the claim. -/
theorem Submission.coarea_critical_fibers_null_euclidean : ∀ (m k : ℕ) (V : Set (Rn (m + k))) (G : Rn (m + k) → Rn m), IsOpen V → ContDiffOn ℝ 1 G V → ∀ᵐ y ∂(volume : Measure (Rn m)), μHE[k] ({x | x ∈ V ∧ ¬ Function.Surjective (fderiv ℝ G x)} ∩ G ⁻¹' {y}) = 0 := by
  intro m k V G hV hG
  -- An open subset of `ℝ^{m+k}` is σ-compact: `V = ⋃ n, Q n` with every `Q n` compact.
  obtain ⟨Q, hQc, hQV⟩ : IsSigmaCompact V := by
    have := hV.locallyCompactSpace
    exact isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
  -- On each compact piece `Q n ⊆ V`, the small covers of `Q n ∩ C_G` give `Hᵏ`-null fibres a.e.
  have hpiece : ∀ n, ∀ᵐ y ∂(volume : Measure (Rn m)),
      μH[k] ({x | x ∈ Q n ∧ ¬ Function.Surjective (fderiv ℝ G x)} ∩ G ⁻¹' {y}) = 0 := fun n ↦
    Submission.ae_hausdorffMeasure_fiber_eq_zero_of_small_ball_covers (Rn (m + k)) (Rn m) volume k
      _ G (Submission.critical_set_small_ball_covers_of_isCompact m k V (Q n) G hV hG (hQc n)
        (hQV ▸ subset_iUnion Q n))
  filter_upwards [ae_all_iff.2 hpiece] with y hy
  -- `C_G ∩ G⁻¹{y} ⊆ ⋃ n, (Q n ∩ C_G ∩ G⁻¹{y})`, a countable union of `μH[k]`-null sets.
  have hH : μH[k] ({x | x ∈ V ∧ ¬ Function.Surjective (fderiv ℝ G x)} ∩ G ⁻¹' {y}) = 0 := by
    refine measure_mono_null ?_ (measure_iUnion_null hy)
    rintro x ⟨⟨hxV, hxs⟩, hxy⟩
    obtain ⟨n, hn⟩ := mem_iUnion.1 (hQV.symm ▸ hxV : x ∈ ⋃ n, Q n)
    exact mem_iUnion.2 ⟨n, ⟨hn, hxs⟩, hxy⟩
  -- `μHE[k] = c_k • μH[k]`.
  rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, hH, smul_zero]

/-- **Simon Ch. 2, §6 (pp. 66–67), critical fibres.** For `Lᵐ`-a.e. `y`,
`Hᵏ(M ∩ f⁻¹{y} ∩ {J*_f = 0}) = 0` (the first assertion of Theorem 6.4). Countably many Simon charts
`ψ` cover `M`; in a chart, critical points of `f` are images of critical points of `f ∘ ψ`, whose
fibres are null by the Euclidean case, and `ψ` is Lipschitz near each point. -/
theorem Submission.coarea_critical_fibers_null : ∀ (N m k : ℕ) (M U : Set (Rn N))
    (f : Rn N → Rn m), Chapter02.IsSimonSubmanifold (E := Rn (m + k)) 1 M → IsOpen U → M ⊆ U →
    ContDiffOn ℝ 1 f U → (∀ (V : Set (Rn (m + k))) (W : Set (Rn N)) (ψ : Rn (m + k) → Rn N),
      Chapter02.IsSimonLocalRepresentation 1 M V W ψ → ∀ x ∈ V,
        tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap) →
    ∀ᵐ y ∂(volume : Measure (Rn m)),
      μHE[k] (M ∩ f ⁻¹' {y} ∩ {x | coareaJacobian M f x = 0}) = 0 := by
  intro N m k M U f hM hU hMU hf hT
  -- One chart: the critical part of the fibre inside `W` is null for a.e. `y`.
  have hchart : ∀ (V : Set (Rn (m + k))) (W : Set (Rn N)) (ψ : Rn (m + k) → Rn N),
      Chapter02.IsSimonLocalRepresentation 1 M V W ψ → ∀ᵐ y ∂(volume : Measure (Rn m)),
        μHE[k] (W ∩ (M ∩ f ⁻¹' {y} ∩ {x | coareaJacobian M f x = 0})) = 0 := by
    intro V W ψ hrep
    have hV : IsOpen V := hrep.isOpen_source
    have hψ : ContDiffOn ℝ 1 ψ V := hrep.contDiffOn
    have hψU : MapsTo ψ V U := fun x hx ↦ hMU (hrep.image_eq.subset (mem_image_of_mem ψ hx)).2
    -- `ψ` is Lipschitz on a neighbourhood of each point of `V`; countably many cover `V`.
    choose! K t ht hKt using fun x (hx : x ∈ V) ↦
      (hψ.contDiffAt (hV.mem_nhds hx)).exists_lipschitzOnWith
    obtain ⟨T, hTV, hTc, hVT⟩ := TopologicalSpace.countable_cover_nhdsWithin (f := t) (s := V)
      fun x hx ↦ mem_nhdsWithin_of_mem_nhds (ht x hx)
    filter_upwards [Submission.coarea_critical_fibers_null_euclidean m k V (f ∘ ψ) hV
      (hf.comp hψ hψU)] with y hy
    refine measure_mono_null (t := ⋃ x ∈ T, ψ '' (t x ∩
      ({x | x ∈ V ∧ ¬ Function.Surjective (fderiv ℝ (f ∘ ψ) x)} ∩ (f ∘ ψ) ⁻¹' {y}))) ?_ ?_
    · rintro p ⟨hpW, ⟨hpM, hpy⟩, hpC⟩
      have hpV : p ∈ ψ '' V := by rw [hrep.image_eq]; exact ⟨hpW, hpM⟩
      obtain ⟨x, hx, rfl⟩ := hpV
      obtain ⟨x₀, hx₀, hxt⟩ := mem_iUnion₂.1 (hVT hx)
      refine mem_iUnion₂.2 ⟨x₀, hx₀, x, ⟨hxt, ⟨hx, ?_⟩, hpy⟩, rfl⟩
      -- `D(f ∘ ψ)(x) = Df(ψ x) ∘ Dψ(x)` is not surjective because `J*_f(ψ x) = 0`.
      rw [fderiv_comp x ((hf.differentiableOn one_ne_zero).differentiableAt
        (hU.mem_nhds (hψU hx))) ((hψ.differentiableOn one_ne_zero).differentiableAt
          (hV.mem_nhds hx))]
      exact (Submission.coarea_jacobian_linear_algebra.1 N m (m + k) M f (ψ x) (fderiv ℝ ψ x)
        (hT V W ψ hrep x hx)).1 hpC
    · refine (measure_biUnion_null_iff hTc).2 fun x hx ↦ nonpos_iff_eq_zero.1 ?_
      calc μHE[k] (ψ '' (t x ∩
            ({x | x ∈ V ∧ ¬ Function.Surjective (fderiv ℝ (f ∘ ψ) x)} ∩ (f ∘ ψ) ⁻¹' {y})))
          ≤ (K x : ℝ≥0∞) ^ k * μHE[k] (t x ∩
            ({x | x ∈ V ∧ ¬ Function.Surjective (fderiv ℝ (f ∘ ψ) x)} ∩ (f ∘ ψ) ⁻¹' {y})) :=
            Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn k
              ((hKt x (hTV hx)).mono inter_subset_left)
        _ = 0 := by rw [measure_mono_null inter_subset_right hy, mul_zero]
  -- Countably many charts cover `M`.
  choose! V W ψ hzW hrep using fun z (hz : z ∈ M) ↦ hM.exists_localRepresentation hz
  obtain ⟨I, hIM, hIc, hMI⟩ := TopologicalSpace.countable_cover_nhdsWithin (f := W) (s := M)
    fun z hz ↦ mem_nhdsWithin_of_mem_nhds ((hrep z hz).isOpen_target.mem_nhds (hzW z hz))
  have hae : ∀ᵐ y ∂(volume : Measure (Rn m)), ∀ z ∈ I,
      μHE[k] (W z ∩ (M ∩ f ⁻¹' {y} ∩ {x | coareaJacobian M f x = 0})) = 0 :=
    (ae_ball_iff hIc).2 fun z hz ↦ hchart _ _ _ (hrep z (hIM hz))
  filter_upwards [hae] with y hy
  refine measure_mono_null ?_ ((measure_biUnion_null_iff hIc).2 hy)
  intro p hp
  obtain ⟨z, hz, hpz⟩ := mem_iUnion₂.1 (hMI hp.1.1)
  exact mem_iUnion₂.2 ⟨z, hz, hpz, hp⟩

/-- **Simon Ch. 2, §6 (pp. 66–67), straightening charts at regular points of `f` on `M`.** Let `M`
be an `(m+k)`-dimensional `C¹` submanifold whose local representations `ψ` satisfy
`T_{ψ(x)} M = range Dψ(x)`, `f` `C¹` on an open `U ⊇ M` and `J*_f(x₀) ≠ 0`. Take a chart `ψ` with
`ψ(a) = x₀`. Then `D(f ∘ ψ)(a) = Df(x₀) ∘ Dψ(a)` is onto, the local submersion theorem gives `Λ`
with `f ∘ ψ ∘ Λ = fst`, and `Ψ = ψ ∘ Λ` is the required chart. -/
theorem Submission.coarea_exists_straightening_chart : ∀ (N m k : ℕ) (M U : Set (Rn N)) (f : Rn N → Rn m) (x₀ : Rn N), Chapter02.IsSimonSubmanifold (E := Rn (m + k)) 1 M → IsOpen U → M ⊆ U → ContDiffOn ℝ 1 f U → (∀ (V : Set (Rn (m + k))) (W : Set (Rn N)) (ψ : Rn (m + k) → Rn N), Chapter02.IsSimonLocalRepresentation 1 M V W ψ → ∀ x ∈ V, tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap) → x₀ ∈ M → coareaJacobian M f x₀ ≠ 0 → ∃ (Ω : Set (WithLp 2 (Rn m × Rn k))) (O : Set (Rn N)) (Ψ : WithLp 2 (Rn m × Rn k) → Rn N), IsOpen Ω ∧ IsOpen O ∧ x₀ ∈ O ∧ ContDiffOn ℝ 1 Ψ Ω ∧ InjOn Ψ Ω ∧ Ψ '' Ω = O ∩ M ∧ (∀ p ∈ Ω, Function.Injective (fderiv ℝ Ψ p)) ∧ (∀ p ∈ Ω, f (Ψ p) = WithLp.fst p) ∧ ∀ p ∈ Ω, tangentSpace M (Ψ p) = LinearMap.range (fderiv ℝ Ψ p).toLinearMap := by
  intro N m k M U f x₀ hM hU hMU hf hT hx₀ hJ
  -- A chart `(V, W, ψ)` of `M` at `x₀ = ψ a`.
  obtain ⟨V, W, ψ, hx₀W, hψ⟩ := hM.exists_localRepresentation hx₀
  obtain ⟨a, haV, rfl⟩ : x₀ ∈ ψ '' V := by rw [hψ.image_eq]; exact ⟨hx₀W, hx₀⟩
  have hψVU : MapsTo ψ V U := fun x hx => by
    have hx' : ψ x ∈ W ∩ M := by rw [← hψ.image_eq]; exact mem_image_of_mem ψ hx
    exact hMU hx'.2
  -- `G = f ∘ ψ` is `C¹` on `V`, and `DG(a) = Df(ψ a) ∘ Dψ(a)` is onto because `J*_f(ψ a) ≠ 0`.
  have hGC : ContDiffOn ℝ 1 (f ∘ ψ) V := hf.comp hψ.contDiffOn hψVU
  have hDG : fderiv ℝ (f ∘ ψ) a = (fderiv ℝ f (ψ a)).comp (fderiv ℝ ψ a) :=
    fderiv_comp a ((hf.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds (hψVU haV)))
      ((hψ.contDiffOn.differentiableOn one_ne_zero).differentiableAt
        (hψ.isOpen_source.mem_nhds haV))
  have hsurj : Function.Surjective (fderiv ℝ (f ∘ ψ) a) := by
    rw [hDG]
    by_contra hns
    exact hJ (((Submission.coarea_jacobian_linear_algebra).1 N m (m + k) M f (ψ a)
      (fderiv ℝ ψ a) (hT V W ψ hψ a haV)).2 hns)
  -- The submersion chart `Λ` of `G` at `a`; then `Ψ = ψ ∘ Λ` is a chart of `M` near `x₀`.
  obtain ⟨Ω, Λ, hΩ, hΛC, hΛinj, hΛΩ, haΛ, hΛV, hΛder, hGΛ⟩ :=
    Submission.coarea_straightening_submersion_chart m k V (f ∘ ψ) a hψ.isOpen_source hGC haV
      hsurj
  obtain ⟨O, hO, hΨΩ, hΨC, hΨinj, hΨder, hΨT⟩ :=
    Submission.coarea_straightening_reparametrize_chart N m k M V W ψ Ω Λ hψ (hT V W ψ hψ) hΩ
      hΛC hΛinj hΛΩ hΛV hΛder
  refine ⟨Ω, O, ψ ∘ Λ, hΩ, hO, ?_, hΨC, hΨinj, hΨΩ, hΨder, hGΛ, hΨT⟩
  -- `x₀ = ψ a = Ψ p` for the `p ∈ Ω` with `Λ p = a`, so `x₀ ∈ Ψ(Ω) = O ∩ M`.
  obtain ⟨p, hp, hpa⟩ := haΛ
  have hpO : ψ (Λ p) ∈ O ∩ M := by rw [← hΨΩ]; exact ⟨p, hp, rfl⟩
  rw [hpa] at hpO
  exact hpO.1

/-- **Co-area formula on one straightening chart** (Step 3 of the supplied proof of 6.6).
`Ψ` is an injective `C¹` immersion of the open set `Ω ⊆ ℝᵐ × ℝᵏ` with `f ∘ Ψ = WithLp.fst` and
`T_{Ψ p} M = range DΨ(p)`; `S ⊆ Ψ(Ω)` and `g` are Borel. Write `j b = toLp(0, b)` and
`J_v(p) = normDet(DΨ(p) ∘ j)`. The area formula for `Ψ`, together with the pointwise identity
`J*_f(Ψ p) · normDet DΨ(p) = J_v(p)` (part (2) of `coarea_jacobian_linear_algebra`), gives
`∫_S g J*_f dHᵐ⁺ᵏ = ∫_{Ω ∩ Ψ⁻¹S} J_v · g ∘ Ψ` (`coarea_chart_area_pullback`). Tonelli and the
area formula for the fibre maps `b ↦ Ψ(toLp(a, b))` identify the right side with
`∫_{ℝᵐ} ∫_{S ∩ f⁻¹{y}} g dHᵏ dLᵐ(y)` and show that the inner integral is Borel in `y`
(`coarea_chart_fiber_disintegration`). -/
theorem Submission.coarea_formula_on_straightening_chart : ∀ (N m k : ℕ) (M : Set (Rn N))
    (f : Rn N → Rn m) (Ω : Set (WithLp 2 (Rn m × Rn k))) (Ψ : WithLp 2 (Rn m × Rn k) → Rn N)
    (S : Set (Rn N)) (g : Rn N → ℝ≥0∞), IsOpen Ω → ContDiffOn ℝ 1 Ψ Ω → InjOn Ψ Ω →
    (∀ p ∈ Ω, Function.Injective (fderiv ℝ Ψ p)) → (∀ p ∈ Ω, DifferentiableAt ℝ f (Ψ p)) →
    (∀ p ∈ Ω, f (Ψ p) = WithLp.fst p) →
    (∀ p ∈ Ω, tangentSpace M (Ψ p) = LinearMap.range (fderiv ℝ Ψ p).toLinearMap) →
    MeasurableSet S → S ⊆ Ψ '' Ω → Measurable g →
    Measurable (fun y ↦ ∫⁻ x in S ∩ f ⁻¹' {y}, g x ∂μHE[k]) ∧
      ∫⁻ x in S, g x * ENNReal.ofReal (coareaJacobian M f x) ∂μHE[m + k] =
        ∫⁻ y, ∫⁻ x in S ∩ f ⁻¹' {y}, g x ∂μHE[k] ∂volume := by
  intro N m k M f Ω Ψ S g hΩ hΨ hΨi hΨd hfd hfΨ hT hS hSΨ hg
  -- Steps 1–3: pull the left side back to `Ω ∩ Ψ⁻¹S`, using the pointwise Jacobian identity.
  have hpull := Submission.coarea_chart_area_pullback N m k M f Ω Ψ S g hΩ hΨ hΨi hΨd hfd hfΨ hT
    hS hSΨ (Submission.coarea_jacobian_linear_algebra.2 N m k M f)
  -- Steps 4–7: Tonelli and the area formula on the fibres `{toLp(a, ·)} ∩ Ω`.
  obtain ⟨hmeas, hfib⟩ := Submission.coarea_chart_fiber_disintegration N m k f Ω Ψ S g hΩ hΨ hΨi
    hΨd hfΨ hS hSΨ hg
  exact ⟨hmeas, hpull.trans hfib⟩

/-- **Simon Ch. 2, 6.6 (p. 67), co-area formula for Borel `g` on a Borel submanifold `M`.**
Countably many straightening charts (`coarea_exists_straightening_chart`) cover the regular set
`{J*_f ≠ 0}`. Their disjointed Borel pieces `S n` satisfy the one-chart formula
(`coarea_formula_on_straightening_chart`) and sum by countable additivity. On the rest of `M`,
`J*_f = 0`, so it adds nothing to the left side, and its fibres are `Hᵏ`-null for `Lᵐ`-a.e. `y`
(`coarea_critical_fibers_null`). -/
theorem Submission.coarea_formula_of_measurable : ∀ (N m k : ℕ) (M U : Set (Rn N)) (f : Rn N → Rn m) (g : Rn N → ℝ≥0∞), Chapter02.IsSimonSubmanifold (E := Rn (m + k)) 1 M → IsOpen U → M ⊆ U → ContDiffOn ℝ 1 f U → (∀ (V : Set (Rn (m + k))) (W : Set (Rn N)) (ψ : Rn (m + k) → Rn N), Chapter02.IsSimonLocalRepresentation 1 M V W ψ → ∀ x ∈ V, tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap) → MeasurableSet M → Measurable g → AEMeasurable (fun y ↦ ∫⁻ x in M ∩ f ⁻¹' {y}, g x ∂μHE[k]) volume ∧ ∫⁻ x in M, g x * ENNReal.ofReal (coareaJacobian M f x) ∂μHE[m + k] = ∫⁻ y, ∫⁻ x in M ∩ f ⁻¹' {y}, g x ∂μHE[k] ∂volume := by
  intro N m k M U f g hM hU hMU hf hT hMm hg
  -- Step 1. `f` is differentiable on `U`, and fibres of Borel subsets of `U` are Borel.
  have hfd : ∀ x ∈ U, DifferentiableAt ℝ f x := fun x hx ↦
    (hf.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hx)
  have hfib : ∀ X ⊆ U, MeasurableSet X → ∀ y, MeasurableSet (X ∩ f ⁻¹' {y}) := by
    intro X hXU hX y
    have hopen : IsOpen (U ∩ f ⁻¹' {y}ᶜ) :=
      hf.continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton
    have heq : X ∩ f ⁻¹' {y} = X \ (U ∩ f ⁻¹' {y}ᶜ) := by
      ext x
      have hxU : x ∈ X → x ∈ U := fun hx ↦ hXU hx
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, Set.mem_sdiff, mem_compl_iff]
      tauto
    rw [heq]
    exact hX.diff hopen.measurableSet
  -- Step 2. Straightening charts at the regular points; countably many of them cover the regular
  -- set, and padding with empty charts turns them into a sequence.
  let R : Set (Rn N) := {x | x ∈ M ∧ coareaJacobian M f x ≠ 0}
  choose Ω O Ψ hΩo hOo hxO hΨc hΨi hΨim hΨd hΨf hΨt using fun x : R ↦
    Submission.coarea_exists_straightening_chart N m k M U f x hM hU hMU hf hT x.2.1 x.2.2
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable (fun x : R ↦ O x) hOo
  have : Countable T := hTc.to_subtype
  obtain ⟨e, he⟩ := exists_surjective_nat (Option T)
  let Ω' : ℕ → Set (WithLp 2 (Rn m × Rn k)) := fun n ↦ (e n).elim ∅ (fun x ↦ Ω x)
  let O' : ℕ → Set (Rn N) := fun n ↦ (e n).elim ∅ (fun x ↦ O x)
  let Ψ' : ℕ → WithLp 2 (Rn m × Rn k) → Rn N := fun n ↦ (e n).elim 0 (fun x ↦ Ψ x)
  have hchart : ∀ n, IsOpen (Ω' n) ∧ IsOpen (O' n) ∧ ContDiffOn ℝ 1 (Ψ' n) (Ω' n) ∧
      InjOn (Ψ' n) (Ω' n) ∧ Ψ' n '' Ω' n = O' n ∩ M ∧
      (∀ p ∈ Ω' n, Function.Injective (fderiv ℝ (Ψ' n) p)) ∧
      (∀ p ∈ Ω' n, f (Ψ' n p) = WithLp.fst p) ∧
      ∀ p ∈ Ω' n,
        tangentSpace M (Ψ' n p) = LinearMap.range (fderiv ℝ (Ψ' n) p).toLinearMap := by
    intro n
    simp only [Ω', O', Ψ']
    cases e n with
    | none => simp
    | some x => exact ⟨hΩo x, hOo x, hΨc x, hΨi x, hΨim x, hΨd x, hΨf x, hΨt x⟩
  have hcover : ∀ x ∈ M, coareaJacobian M f x ≠ 0 → ∃ n, x ∈ O' n := by
    intro x hxM hxJ
    have hx : x ∈ ⋃ i : R, O i := mem_iUnion.2 ⟨⟨x, hxM, hxJ⟩, hxO _⟩
    rw [← hTU] at hx
    obtain ⟨i, hiT, hxi⟩ := mem_iUnion₂.1 hx
    obtain ⟨n, hn⟩ := he (some ⟨i, hiT⟩)
    refine ⟨n, ?_⟩
    simp only [O', hn, Option.elim_some]
    exact hxi
  -- Step 3. Disjoint Borel pieces `S n ⊆ Ψ' n '' Ω' n` whose union `R'` contains every regular
  -- point of `M`, so that `J*_f = 0` on `M \ R'`.
  let A : ℕ → Set (Rn N) := fun n ↦ O' n ∩ M
  have hAm : ∀ n, MeasurableSet (A n) := fun n ↦ (hchart n).2.1.measurableSet.inter hMm
  let S : ℕ → Set (Rn N) := disjointed A
  have hSm : ∀ n, MeasurableSet (S n) := MeasurableSet.disjointed hAm
  have hSd : Pairwise (Function.onFun Disjoint S) := disjoint_disjointed A
  have hSA : ∀ n, S n ⊆ A n := disjointed_subset A
  have hSM : ∀ n, S n ⊆ M := fun n ↦ (hSA n).trans inter_subset_right
  let R' : Set (Rn N) := ⋃ n, S n
  have hR'eq : R' = ⋃ n, A n := iUnion_disjointed
  have hR'm : MeasurableSet R' := MeasurableSet.iUnion hSm
  have hR'M : R' ⊆ M := iUnion_subset hSM
  have hC : ∀ x ∈ M \ R', coareaJacobian M f x = 0 := by
    rintro x ⟨hxM, hxR'⟩
    by_contra hJ
    obtain ⟨n, hn⟩ := hcover x hxM hJ
    exact hxR' (hR'eq ▸ mem_iUnion.2 ⟨n, hn, hxM⟩)
  -- Step 4. The one-chart formula on every piece.
  have hloc : ∀ n, Measurable (fun y ↦ ∫⁻ x in S n ∩ f ⁻¹' {y}, g x ∂μHE[k]) ∧
      ∫⁻ x in S n, g x * ENNReal.ofReal (coareaJacobian M f x) ∂μHE[m + k] =
        ∫⁻ y, ∫⁻ x in S n ∩ f ⁻¹' {y}, g x ∂μHE[k] ∂volume := by
    intro n
    obtain ⟨hΩn, -, hΨcn, hΨin, hΨimn, hΨdn, hΨfn, hΨtn⟩ := hchart n
    refine Submission.coarea_formula_on_straightening_chart N m k M f (Ω' n) (Ψ' n) (S n) g
      hΩn hΨcn hΨin hΨdn ?_ hΨfn hΨtn (hSm n) ?_ hg
    · intro p hp
      have hmem : Ψ' n p ∈ O' n ∩ M := hΨimn ▸ mem_image_of_mem _ hp
      exact hfd _ (hMU hmem.2)
    · rw [hΨimn]
      exact hSA n
  -- Step 5. The left side: `R'` is the disjoint union of the `S n`, and `M \ R'` adds nothing.
  have hLHS : ∫⁻ x in M, g x * ENNReal.ofReal (coareaJacobian M f x) ∂μHE[m + k] =
      ∫⁻ y, ∑' n, ∫⁻ x in S n ∩ f ⁻¹' {y}, g x ∂μHE[k] ∂volume := by
    have hzero :
        ∫⁻ x in M \ R', g x * ENNReal.ofReal (coareaJacobian M f x) ∂μHE[m + k] = 0 := by
      rw [setLIntegral_congr_fun (hMm.diff hR'm) (g := fun _ ↦ 0)
        (fun x hx ↦ by simp [hC x hx])]
      simp
    rw [← lintegral_inter_add_sdiff _ M hR'm, inter_eq_right.2 hR'M, hzero, add_zero,
      lintegral_iUnion hSm hSd, lintegral_tsum (fun n ↦ (hloc n).1.aemeasurable)]
    exact tsum_congr (fun n ↦ (hloc n).2)
  -- Step 6. The regular part of every fibre is the disjoint union of the fibres of the `S n`.
  have hreg : ∀ y, ∫⁻ x in R' ∩ f ⁻¹' {y}, g x ∂μHE[k] =
      ∑' n, ∫⁻ x in S n ∩ f ⁻¹' {y}, g x ∂μHE[k] := by
    intro y
    rw [show R' ∩ f ⁻¹' {y} = ⋃ n, S n ∩ f ⁻¹' {y} from iUnion_inter _ _]
    exact lintegral_iUnion (fun n ↦ hfib _ ((hSM n).trans hMU) (hSm n) y)
      (fun i j hij ↦ (hSd hij).mono inter_subset_left inter_subset_left) _
  -- Step 7. For `Lᵐ`-a.e. `y`, the critical part `(M \ R') ∩ f⁻¹{y}` of the fibre is null.
  have hae : ∀ᵐ y ∂(volume : Measure (Rn m)), ∫⁻ x in M ∩ f ⁻¹' {y}, g x ∂μHE[k] =
      ∑' n, ∫⁻ x in S n ∩ f ⁻¹' {y}, g x ∂μHE[k] := by
    filter_upwards [Submission.coarea_critical_fibers_null N m k M U f hM hU hMU hf hT] with y hy
    have hsub :
        (M \ R') ∩ f ⁻¹' {y} ⊆ M ∩ f ⁻¹' {y} ∩ {x | coareaJacobian M f x = 0} :=
      fun x hx ↦ ⟨⟨hx.1.1, hx.2⟩, hC x hx.1⟩
    have hnull : μHE[k] ((M \ R') ∩ f ⁻¹' {y}) = 0 := measure_mono_null hsub hy
    have hsplit : M ∩ f ⁻¹' {y} = (R' ∩ f ⁻¹' {y}) ∪ ((M \ R') ∩ f ⁻¹' {y}) := by
      rw [← union_inter_distrib_right, union_sdiff_cancel hR'M]
    rw [hsplit, lintegral_union (hfib _ (sdiff_subset.trans hMU) (hMm.diff hR'm) y)
      (disjoint_sdiff_right.mono inter_subset_left inter_subset_left),
      setLIntegral_measure_zero _ _ hnull, add_zero, hreg y]
  -- Step 8. The fibre integral agrees `Lᵐ`-a.e. with the Borel sum over the pieces.
  have hmeas : Measurable (fun y ↦ ∑' n, ∫⁻ x in S n ∩ f ⁻¹' {y}, g x ∂μHE[k]) :=
    Measurable.tsum fun n ↦ (hloc n).1
  exact ⟨hmeas.aemeasurable.congr (hae.mono fun y hy ↦ hy.symm),
    hLHS.trans (lintegral_congr_ae hae).symm⟩
/-- **Simon Ch. 2, 4.3 (p. 55): chart velocities are tangent vectors.** If `V ⊆ ℝⁿ` is open,
`ψ : ℝⁿ → ℝᴺ` is `C¹` on `V` and maps `V` into `M`, then `range Dψ(x) ⊆ T_{ψ(x)} M` for `x ∈ V`.
For `w ≠ 0` choose `B(x, ρ) ⊆ V` and `κ = ρ/(2|w|)`; the curve `γ(t) = ψ(x + κ t w)` is `C¹` on
`(-1,1)`, maps `(-1,1)` into `M`, has `γ(0) = ψ(x)` and, by the chain rule, `γ'(0) = κ Dψ(x) w`.
So `κ Dψ(x) w` is a generator of `T_{ψ(x)} M` and `Dψ(x) w = κ⁻¹ (κ Dψ(x) w)` lies in the span. -/
theorem Submission.simon_chart_range_fderiv_le_tangentSpace : ∀ (n N : ℕ) (M : Set (Rn N)) (V : Set (Rn n)) (ψ : Rn n → Rn N), IsOpen V → ContDiffOn ℝ 1 ψ V → MapsTo ψ V M → ∀ x ∈ V, LinearMap.range (fderiv ℝ ψ x).toLinearMap ≤ tangentSpace M (ψ x) := by
  intro n N M V ψ hV hψ hMaps x₀ hx₀
  -- Step 1: `ψ` is differentiable at `x₀`, with derivative `A = fderiv ℝ ψ x₀`.
  have hA : HasFDerivAt ψ (fderiv ℝ ψ x₀) x₀ :=
    (hψ.contDiffAt (hV.mem_nhds hx₀)).differentiableAt_one.hasFDerivAt
  rintro _ ⟨w, rfl⟩
  -- Step 2: `A 0 = 0` lies in the subspace; for `w ≠ 0` fix `B(x₀, ρ) ⊆ V` and `κ = ρ/(2|w|)`.
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hV x₀ hx₀
  have hw' : 0 < ‖w‖ := norm_pos_iff.mpr hw
  set κ : ℝ := ρ / (2 * ‖w‖) with hκ
  have hκ0 : 0 < κ := div_pos hρ (by positivity)
  set ℓ : ℝ → Rn n := fun t ↦ x₀ + (κ * t) • w with hℓ
  -- Step 3: `ℓ` maps `(-1,1)` into `B(x₀, ρ) ⊆ V`, so `γ = ψ ∘ ℓ` is a `C¹` curve in `M`.
  have hℓV : MapsTo ℓ (Ioo (-1) 1) V := by
    intro t ht
    apply hball
    have ht' : |t| < 1 := abs_lt.mpr ht
    have hκw : κ * ‖w‖ = ρ / 2 := by rw [hκ]; field_simp
    rw [Metric.mem_ball, dist_eq_norm, hℓ, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_mul, abs_of_pos hκ0, mul_right_comm, hκw]
    nlinarith
  have hℓC : ContDiff ℝ 1 ℓ :=
    contDiff_const.add ((contDiff_const.mul contDiff_id).smul contDiff_const)
  have hγC : ContDiffOn ℝ 1 (ψ ∘ ℓ) (Ioo (-1) 1) := hψ.comp hℓC.contDiffOn hℓV
  have hγM : MapsTo (ψ ∘ ℓ) (Ioo (-1) 1) M := hMaps.comp hℓV
  have hℓ0 : ℓ 0 = x₀ := by simp [hℓ]
  have hγ0 : (ψ ∘ ℓ) 0 = ψ x₀ := by simp [Function.comp, hℓ0]
  -- Step 4: chain rule, `γ'(0) = A (κ • w)`, so `κ • A w` is a generator of the span.
  have hℓd : HasDerivAt ℓ (κ • w) 0 := by
    have h := (((hasDerivAt_id (0 : ℝ)).const_mul κ).smul_const w).const_add x₀
    rwa [mul_one] at h
  have hγd : HasDerivAt (ψ ∘ ℓ) (fderiv ℝ ψ x₀ (κ • w)) 0 :=
    hA.comp_hasDerivAt_of_eq (0 : ℝ) hℓd hℓ0.symm
  have hmem : fderiv ℝ ψ x₀ (κ • w) ∈ tangentSpace M (ψ x₀) :=
    Submodule.subset_span ⟨ψ ∘ ℓ, hγC, hγM, hγ0, hγd⟩
  rw [map_smul] at hmem
  have h := (tangentSpace M (ψ x₀)).smul_mem κ⁻¹ hmem
  rwa [smul_smul, inv_mul_cancel₀ hκ0.ne', one_smul] at h
/-- **Simon Ch. 2, 4.3 (p. 55), velocity of a lifted curve.** If `ψ` is differentiable at `x₀`
with injective derivative `A = Dψ(x₀)`, `c(t) → x₀` as `t → 0`, `γ = ψ ∘ c` near `0` and
`γ'(0) = v`, then `v ∈ range A` (`c` need not be differentiable). Injectivity gives
`|ζ| ≤ K |Aζ|`, so the remainder `e(t) = ψ(c(t)) - ψ(x₀) - A(c(t) - x₀) = o(|c(t) - x₀|)` forces
`c(t) - x₀ = O(t)` and `e(t) = o(t)`; then `A(t⁻¹(c(t) - x₀)) = t⁻¹(γ(t) - γ(0)) - t⁻¹e(t) → v`,
and `range A` is closed. -/
theorem Submission.simon_lift_velocity_mem_range_fderiv : ∀ (n N : ℕ) (ψ : Rn n → Rn N) (x₀ : Rn n) (c : ℝ → Rn n) (γ : ℝ → Rn N) (v : Rn N), DifferentiableAt ℝ ψ x₀ → Function.Injective (fderiv ℝ ψ x₀) → Tendsto c (𝓝 (0 : ℝ)) (𝓝 x₀) → (∀ᶠ t in 𝓝 (0 : ℝ), γ t = ψ (c t)) → HasDerivAt γ v 0 → v ∈ LinearMap.range (fderiv ℝ ψ x₀).toLinearMap := by
  intro n N ψ x₀ c γ v hψ hinj hc hγψ hγ
  set A := fderiv ℝ ψ x₀
  -- The unpunctured limit gives `c 0 = x₀`, hence `γ 0 = ψ x₀`.
  have hc0 : c 0 = x₀ :=
    tendsto_nhds_unique (tendsto_pure_nhds c 0) (hc.mono_left (pure_le_nhds 0))
  have hγ0 : γ 0 = ψ x₀ := by rw [hγψ.self_of_nhds, hc0]
  -- The remainder `e(t) = ψ(c t) - ψ x₀ - A (c t - x₀)` is `o(c t - x₀)`.
  have he : (fun t => ψ (c t) - ψ x₀ - A (c t - x₀)) =o[𝓝 0] (fun t => c t - x₀) :=
    hψ.hasFDerivAt.isLittleO.comp_tendsto hc
  -- Injectivity in finite dimension: `‖ζ‖ ≤ K ‖A ζ‖`.
  obtain ⟨K, -, hK⟩ := A.toLinearMap.exists_antilipschitzWith (LinearMap.ker_eq_bot.mpr hinj)
  have hu : (fun t => c t - x₀) =O[𝓝 0] (fun t => A (c t - x₀)) :=
    Asymptotics.IsBigO.of_bound (K : ℝ)
      (Eventually.of_forall fun t => A.bound_of_antilipschitz hK _)
  -- Hence `A (c t - x₀) = O(γ t - γ 0) = O(t)`, so `c t - x₀ = O(t)` and `e(t) = o(t)`.
  have hAu : (fun t => A (c t - x₀)) =O[𝓝 0] (fun t => γ t - γ 0) := by
    refine (he.trans_isBigO hu).right_isBigO_add.congr' EventuallyEq.rfl ?_
    filter_upwards [hγψ] with t ht
    rw [ht, hγ0, sub_add_cancel]
  have hγO : (fun t => γ t - γ 0) =O[𝓝 0] (fun t : ℝ => t) := by
    simpa only [sub_zero] using hγ.isBigO_sub
  have het : (fun t => ψ (c t) - ψ x₀ - A (c t - x₀)) =o[𝓝 0] (fun t : ℝ => t) :=
    he.trans_isBigO (hu.trans (hAu.trans hγO))
  -- `A (t⁻¹ (c t - x₀)) = t⁻¹ (γ t - γ 0) - t⁻¹ e(t) → v` as `t → 0`, `t ≠ 0`.
  have hslope : Tendsto (fun t : ℝ => t⁻¹ • (γ t - γ 0)) (𝓝[≠] 0) (𝓝 v) := by
    simpa only [zero_add] using hγ.tendsto_slope_zero
  have hlim : Tendsto (fun t : ℝ => t⁻¹ • (γ t - γ 0) - t⁻¹ • (ψ (c t) - ψ x₀ - A (c t - x₀)))
      (𝓝[≠] 0) (𝓝 (v - 0)) :=
    hslope.sub (het.tendsto_inv_smul_nhds_zero.mono_left nhdsWithin_le_nhds)
  rw [sub_zero] at hlim
  -- Every term lies in `range A`, a closed subspace.
  refine SetLike.mem_coe.mp <|
    (LinearMap.range A.toLinearMap).closed_of_finiteDimensional.mem_of_tendsto hlim ?_
  filter_upwards [hγψ.filter_mono nhdsWithin_le_nhds] with t ht
  have hAt : t⁻¹ • (γ t - γ 0) - t⁻¹ • (ψ (c t) - ψ x₀ - A (c t - x₀)) =
      A (t⁻¹ • (c t - x₀)) := by
    rw [ht, hγ0, ← smul_sub, map_smul, sub_sub_cancel]
  rw [hAt]
  exact LinearMap.mem_range_self A.toLinearMap _
/-- **Simon Ch. 2, 4.2 (p. 55).** The inverse `g = invFunOn ψ V` of a local representation is
continuous on `W ∩ M = ψ(V)`. For `y ∈ W ∩ M`, a closed ball `Q ⊆ W` about `y` has compact preimage
`K = V ∩ ψ⁻¹(Q)` (relative properness), and `g` maps `W ∩ M ∩ Q` into `K`. Every cluster point `x'`
of `g` at `y` lies in `K ⊆ V` and has `ψ x' = y` by continuity of `ψ`, so `x' = g y` by
injectivity; a map eventually in a compact set with a unique cluster point converges to it. The
injectivity of `Dψ` is not needed. -/
theorem Submission.simon_submanifold_chart_inverse_continuousOn : ∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)) (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N), Chapter02.IsSimonLocalRepresentation r M V W ψ → ContinuousOn (Function.invFunOn ψ V) (W ∩ M) := by
  intro n N r M V W ψ h
  obtain ⟨hV, hW, hψ, hinj, himg, hprop, -⟩ := h
  -- Step 2: on `W ∩ M = ψ(V)`, `g` takes values in `V` and is a right inverse of `ψ`.
  have hg : ∀ y ∈ W ∩ M, Function.invFunOn ψ V y ∈ V ∧ ψ (Function.invFunOn ψ V y) = y := by
    intro y hy
    rw [← himg] at hy
    exact ⟨Function.invFunOn_mem hy, Function.invFunOn_eq hy⟩
  intro y hy
  obtain ⟨hgyV, hψgy⟩ := hg y hy
  -- Step 4, with a compact ball `Q = closedBall y ε ⊆ W` in place of `{y_j} ∪ {y}`:
  -- `K = V ∩ ψ⁻¹(Q)` is compact, and `g z ∈ K` for every `z ∈ W ∩ M` close to `y`.
  obtain ⟨ε, hε, hQW⟩ := nhds_basis_closedBall.mem_iff.1 (hW.mem_nhds hy.1)
  have hK : IsCompact (V ∩ ψ ⁻¹' closedBall y ε) := hprop _ (isCompact_closedBall y ε) hQW
  have hev : ∀ᶠ z in 𝓝[W ∩ M] y, Function.invFunOn ψ V z ∈ V ∩ ψ ⁻¹' closedBall y ε := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (closedBall_mem_nhds y hε)]
      with z hz hzQ
    obtain ⟨hgzV, hψgz⟩ := hg z hz
    exact ⟨hgzV, by rwa [mem_preimage, hψgz]⟩
  -- Steps 5–6, with cluster points in place of subsequential limits: a cluster point `x' ∈ K`
  -- of `g` at `y` has `ψ x' = y` (Step 1: `ψ` is continuous at `x' ∈ V`), hence `x' = g y`.
  refine hK.tendsto_nhds_of_unique_mapClusterPt hev fun x' hx' hcl ↦ ?_
  have hψx' : ContinuousAt ψ x' := hψ.continuousOn.continuousAt (hV.mem_nhds hx'.1)
  have hcl' : MapClusterPt (ψ x') (𝓝[W ∩ M] y) id := by
    refine (hcl.continuousAt_comp hψx').congrFun ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (hg z hz).2
  have hψx'y : ψ x' = y :=
    eq_of_nhds_neBot (mapClusterPt_id_iff.1 hcl' |>.mono nhdsWithin_le_nhds).neBot
  exact hinj hx'.1 hgyV (hψx'y.trans hψgy.symm)
/-- **Simon Ch. 2, §4 (p. 55), projection onto the range of an injective map.** The orthogonal
projection `P_{range A}` depends continuously on `A` on the set of injective `A ∈ L(ℝⁿ, ℝᴺ)`.
For injective `A`, the endomorphism `A* A` of `ℝⁿ` is injective, hence invertible. Moreover
`A (A* A)⁻¹ A*` is the orthogonal projection onto `range A`, since its values lie in `range A` and
`v - A (A* A)⁻¹ A* v ⊥ range A`. The map `A ↦ A ∘ Ring.inverse (A* A) ∘ A*` is continuous at every
injective `A`: the adjoint is a linear isometry, composition is jointly continuous, and
`Ring.inverse` is continuous at units. -/
theorem Submission.simon_submanifold_range_starProjection_continuousOn : ∀ (n N : ℕ), ContinuousOn (fun A : Rn n →L[ℝ] Rn N ↦ (LinearMap.range A.toLinearMap).starProjection) {A : Rn n →L[ℝ] Rn N | Function.Injective A} := by
  intro n N
  -- Step 1: `A* A` is a unit of `L(ℝⁿ, ℝⁿ)` for injective `A`.
  have hunit : ∀ A : Rn n →L[ℝ] Rn N, Function.Injective A →
      IsUnit (ContinuousLinearMap.adjoint A ∘L A) := by
    intro A hA
    have hinj : Function.Injective (ContinuousLinearMap.adjoint A ∘L A) := by
      rw [ContinuousLinearMap.coe_comp]
      exact (ContinuousLinearMap.adjoint_comp_self_injective_iff A).2 hA
    exact ContinuousLinearMap.isUnit_iff_bijective.2
      ⟨hinj, LinearMap.surjective_of_injective
        (f := (ContinuousLinearMap.adjoint A ∘L A : Rn n →ₗ[ℝ] Rn n)) hinj⟩
  -- Steps 2–3: for injective `A`, `A (A* A)⁻¹ A*` is the orthogonal projection onto `range A`.
  have hF : ∀ A : Rn n →L[ℝ] Rn N, Function.Injective A →
      A ∘L (Ring.inverse (ContinuousLinearMap.adjoint A ∘L A) ∘L ContinuousLinearMap.adjoint A) =
        (LinearMap.range A.toLinearMap).starProjection := by
    intro A hA
    ext1 v
    symm
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (LinearMap.mem_range_self _ _) ?_
    rintro _ ⟨w, rfl⟩
    -- `A* (A (A* A)⁻¹ A* v) = A* v`, because `(A* A) (A* A)⁻¹ = 1`.
    have hfix : ContinuousLinearMap.adjoint A
        ((A ∘L (Ring.inverse (ContinuousLinearMap.adjoint A ∘L A) ∘L
          ContinuousLinearMap.adjoint A)) v) = ContinuousLinearMap.adjoint A v := by
      simpa using congrArg (fun T : Rn n →L[ℝ] Rn n ↦ T (ContinuousLinearMap.adjoint A v))
        (Ring.mul_inverse_cancel _ (hunit A hA))
    rw [ContinuousLinearMap.coe_coe, ← ContinuousLinearMap.adjoint_inner_left, map_sub, hfix,
      sub_self, inner_zero_left]
  -- Steps 4–5: `A ↦ A (A* A)⁻¹ A*` is continuous at each injective `A₀`, and it agrees with
  -- `A ↦ P_{range A}` on the injective maps.
  intro A₀ hA₀
  have hadj : Continuous fun A : Rn n →L[ℝ] Rn N ↦ ContinuousLinearMap.adjoint A :=
    ContinuousLinearMap.adjoint.continuous
  have hinv : ContinuousAt (fun A : Rn n →L[ℝ] Rn N ↦
      Ring.inverse (ContinuousLinearMap.adjoint A ∘L A)) A₀ :=
    (NormedRing.inverse_continuousAt (hunit A₀ hA₀).unit).comp_of_eq
      (hadj.clm_comp continuous_id).continuousAt (hunit A₀ hA₀).unit_spec.symm
  have hcont : ContinuousAt (fun A : Rn n →L[ℝ] Rn N ↦
      A ∘L (Ring.inverse (ContinuousLinearMap.adjoint A ∘L A) ∘L
        ContinuousLinearMap.adjoint A)) A₀ :=
    continuousAt_id.clm_comp (hinv.clm_comp hadj.continuousAt)
  exact hcont.continuousWithinAt.congr (fun A hA ↦ (hF A hA).symm) (hF A₀ hA₀).symm
/-- **Simon Ch. 2, §4 (p. 55).** A `C^r` submanifold `M ⊆ ℝᴺ` in the sense of 4.1 is a Borel set.
If `(V, W, ψ)` is a local representation, relative properness and continuity of `ψ` on `V` give
`W ∩ closure (W ∩ M) ⊆ M`, so `W ∩ M = W ∩ closure (W ∩ M)` is the intersection of an open set and a
closed set. By second countability, countably many chart sets `W_y` (`y ∈ M`) cover `M`. Hence `M`
is a countable union of such intersections. -/
theorem Submission.simon_submanifold_measurableSet : ∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)), Chapter02.IsSimonSubmanifold (E := Rn n) r M → MeasurableSet M := by
  intro n N r M hM
  -- Step 1: local closedness. For every local representation `(V, W, ψ)`,
  -- `W ∩ closure (W ∩ M) ⊆ M`.
  have hloc : ∀ (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N),
      Chapter02.IsSimonLocalRepresentation r M V W ψ → W ∩ closure (W ∩ M) ⊆ M := by
    rintro V W ψ ⟨hV, -, hψ, -, himg, hprop, -⟩ z ⟨hzW, hz⟩
    obtain ⟨u, huWM, hu⟩ := mem_closure_iff_seq_limit.1 hz
    -- `Q = {u j : j ∈ ℕ} ∪ {z} ⊆ W` is compact, so relative properness makes `V ∩ ψ⁻¹(Q)` compact.
    have hK : IsCompact (V ∩ ψ ⁻¹' insert z (range u)) :=
      hprop _ hu.isCompact_insert_range (insert_subset hzW (range_subset_iff.2 fun j ↦ (huWM j).1))
    -- Since `u j ∈ W ∩ M = ψ(V)`, choose `x j ∈ V` with `ψ (x j) = u j`.
    have hpre : ∀ j, ∃ x ∈ V, ψ x = u j := fun j ↦ (mem_image ψ V (u j)).1 (himg ▸ huWM j)
    choose x hxV hψx using hpre
    obtain ⟨a, ⟨haV, -⟩, φ, hφ, hxa⟩ := hK.tendsto_subseq (x := x) fun j ↦
      ⟨hxV j, mem_insert_of_mem _ ⟨j, (hψx j).symm⟩⟩
    -- `ψ` is continuous at `a ∈ V`, so `ψ a = lim ψ (x (φ k)) = lim u (φ k) = z`.
    have hψa : Tendsto (ψ ∘ x ∘ φ) atTop (𝓝 (ψ a)) :=
      (hψ.continuousOn.continuousAt (hV.mem_nhds haV)).tendsto.comp hxa
    have hz' : Tendsto (ψ ∘ x ∘ φ) atTop (𝓝 z) := by
      have hcomp : ψ ∘ x ∘ φ = u ∘ φ := funext fun k ↦ hψx (φ k)
      rw [hcomp]
      exact hu.comp hφ.tendsto_atTop
    have hzimg : z ∈ ψ '' V := ⟨a, haV, tendsto_nhds_unique hψa hz'⟩
    exact (himg ▸ hzimg).2
  -- Step 3: Lindelöf. Choose a local representation `(V y, W y, ψ y)` with `y ∈ W y` for every
  -- `y ∈ M`; the union of the open sets `W y`, `y ∈ M`, is a union over a countable `T ⊆ M`.
  choose! V W ψ hyW hrep using hM.2
  obtain ⟨T, hTM, hTc, hTU⟩ :=
    TopologicalSpace.isOpen_biUnion_countable M W fun y hy ↦ (hrep y hy).2.1
  -- Steps 2 and 4: `M = ⋃ y ∈ T, (W y ∩ closure (W y ∩ M))`; `⊆` uses
  -- `W y ∩ M ⊆ closure (W y ∩ M)`, and `⊇` is Step 1.
  have hMeq : M = ⋃ y ∈ T, (W y ∩ closure (W y ∩ M)) := by
    refine Subset.antisymm (fun z hz ↦ ?_) (iUnion₂_subset fun y hy ↦ hloc _ _ _ (hrep y (hTM hy)))
    have hzT : z ∈ ⋃ y ∈ T, W y := hTU ▸ mem_biUnion hz (hyW z hz)
    obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.1 hzT
    exact mem_biUnion hy ⟨hzy, subset_closure ⟨hzy, hz⟩⟩
  -- Step 5: each `W y ∩ closure (W y ∩ M)` is Borel, and `T` is countable.
  rw [hMeq]
  exact .biUnion hTc fun y hy ↦
    (hrep y (hTM hy)).2.1.measurableSet.inter isClosed_closure.measurableSet

/-- The frozen Chapter 2 contract: the conjunction of all headline results. -/
theorem main_theorem : LipschitzExtension ∧ Rademacher ∧ C1Approximation ∧ WhitneyExtension ∧ LipschitzImageHausdorff ∧ EilenbergInequality ∧ BVCompactness ∧ BVPoincare ∧ BVExtensionEstimate ∧ AreaFormula ∧ FirstVariation ∧ SecondVariation ∧ StationaryIffMeanCurvatureZero ∧ SecondVariationStationary ∧ CoareaFormula ∧ C1Sard := by sorry

/-- **Simon Ch. 2, proof of Theorem 1.9 (pp. 45–46), covering majorant**, with a Borel majorant
`G` in place of the upper integral of Remark 1.10. Put `s = m + k`, `M = μH[s](E)` (finite, as
`𝓗^s = (ω_s/2^s) μH[s]`) and `a = ω_m ω_k K^m / 2^s`. At the scales `δ i = (i + 1)⁻¹`,
`eilenberg_covering_fixed_scale_majorant` gives Borel `g i` dominating `(ω_k/2^k)` times the
size-`δ i` Hausdorff premeasure of `E ∩ f⁻¹{y}`, with `∫ g i ≤ a (M + δ i)`;
`eilenberg_covering_liminf_majorant` turns them into `G ≥ (ω_k/2^k) μH[k](E ∩ f⁻¹{·}) = 𝓗^k(…)`
with `∫ G ≤ a M = (ω_m ω_k / ω_s) K^m 𝓗^s(E)`. -/
theorem Submission.eilenberg_covering_majorant : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (m : ℕ) (k : ℝ) (E : Set X) (f : X → Rn m) (K : ℝ≥0), 0 < k → Chapter01.simonHausdorffMeasureReal (m + k) E < ⊤ → LipschitzOnWith K f E → ∃ G : Rn m → ℝ≥0∞, Measurable G ∧ (∀ y, Chapter01.simonHausdorffMeasureReal k (E ∩ f ⁻¹' {y}) ≤ G y) ∧ ∫⁻ y, G y ∂volume ≤ Chapter01.realUnitBallVolume (m : ℝ) * Chapter01.realUnitBallVolume k / Chapter01.realUnitBallVolume (m + k) * (K : ℝ≥0∞) ^ m * Chapter01.simonHausdorffMeasureReal (m + k) E := by
  intro X _ _ _ m k E f K hk hE hf
  have hnorm (s : ℝ) (S : Set X) : Chapter01.simonHausdorffMeasureReal s S =
      Chapter01.realUnitBallVolume s / 2 ^ s * μH[s] S := by
    rw [Chapter01.simonHausdorffMeasureReal, Measure.smul_apply, smul_eq_mul]
  have hs : (0 : ℝ) ≤ m + k := add_nonneg (Nat.cast_nonneg m) hk.le
  have hω₀ : Chapter01.realUnitBallVolume (m + k) ≠ 0 := (Chapter01.realUnitBallVolume_pos hs).ne'
  have hω : Chapter01.realUnitBallVolume (m + k) ≠ ⊤ := Chapter01.realUnitBallVolume_ne_top _
  have h2₀ : (2 : ℝ≥0∞) ^ ((m : ℝ) + k) ≠ 0 := (ENNReal.rpow_pos (by norm_num) (by norm_num)).ne'
  have h2 : (2 : ℝ≥0∞) ^ ((m : ℝ) + k) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hs (by norm_num)
  have hM : μH[(m : ℝ) + k] E < ⊤ := by
    rw [hnorm] at hE
    exact ENNReal.lt_top_of_mul_ne_top_right hE.ne (ENNReal.div_pos hω₀ h2).ne'
  -- Scales and slacks `δ i = (i + 1)⁻¹ → 0`, and the fixed-scale majorants `g i`.
  set δ : ℕ → ℝ≥0∞ := fun i ↦ ((i : ℝ≥0∞) + 1)⁻¹ with hδ_def
  have hδ₀ (i : ℕ) : 0 < δ i :=
    ENNReal.inv_pos.2 (ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top i, ENNReal.one_ne_top⟩)
  have hδ : Tendsto δ atTop (𝓝 0) := by
    rw [hδ_def]
    simpa using (tendsto_add_atTop_iff_nat 1).2 ENNReal.tendsto_inv_nat_nhds_zero
  choose g hg hgle hgint using fun i ↦ Submission.eilenberg_covering_fixed_scale_majorant X m k E
    f K (δ i) (δ i) hk hM hf (hδ₀ i) (hδ₀ i)
  set a := Chapter01.realUnitBallVolume (m : ℝ) * Chapter01.realUnitBallVolume k * (K : ℝ≥0∞) ^ m /
    (2 : ℝ≥0∞) ^ ((m : ℝ) + k) with ha_def
  have ha : a ≠ ⊤ := ENNReal.div_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
    (Chapter01.realUnitBallVolume_ne_top _) (Chapter01.realUnitBallVolume_ne_top _))
    (ENNReal.pow_ne_top ENNReal.coe_ne_top)) h2₀
  have hb : Tendsto (fun i ↦ a * (μH[(m : ℝ) + k] E + δ i)) atTop
      (𝓝 (a * μH[(m : ℝ) + k] E)) := by
    simpa using ENNReal.Tendsto.const_mul (hδ.const_add (μH[(m : ℝ) + k] E)) (Or.inr ha)
  obtain ⟨G, hG, hGle, hGint⟩ := Submission.eilenberg_covering_liminf_majorant X (Rn m) volume k
    (Chapter01.realUnitBallVolume k / 2 ^ k) (fun y ↦ E ∩ f ⁻¹' {y}) δ g
    (fun i ↦ a * (μH[(m : ℝ) + k] E + δ i)) (a * μH[(m : ℝ) + k] E) hδ hg hgle hgint hb
  refine ⟨G, hG, fun y ↦ (hnorm k _).trans_le (hGle y), hGint.trans_eq ?_⟩
  -- `a M = (ω_m ω_k / ω_s) K^m (ω_s / 2^s) M`: the factor `ω_s` cancels.
  rw [hnorm, ha_def]
  calc _ = Chapter01.realUnitBallVolume (m : ℝ) * Chapter01.realUnitBallVolume k *
        (K : ℝ≥0∞) ^ m / (2 : ℝ≥0∞) ^ ((m : ℝ) + k) * μH[(m : ℝ) + k] E *
        ((Chapter01.realUnitBallVolume (m + k))⁻¹ * Chapter01.realUnitBallVolume (m + k)) := by
        rw [ENNReal.inv_mul_cancel hω₀ hω, mul_one]
    _ = _ := by
        simp only [div_eq_mul_inv]
        ring

/-- **Simon Ch. 2, Theorem 1.9 (pp. 45–46), Eilenberg inequality**, assembled from its three
children. `eilenberg_compact_exhaustion` gives increasing compact `Q j ⊆ A` with
`𝓗^{m+k}(N) = 0`, `N = A \ ⋃ j, Q j`. The `eilenberg_covering_majorant` of `N` has integral `0`,
so `𝓗^k(N ∩ f⁻¹{y}) = 0` for a.e. `y`. Hence, a.e., `𝓗^k(A ∩ f⁻¹{y}) = 𝓗^k((⋃ j, Q j) ∩ f⁻¹{y})
= ⨆ j, 𝓗^k(Q j ∩ f⁻¹{y})`, a supremum of Borel functions (`eilenberg_compact_fiber_measurable`).
The inequality is the `eilenberg_covering_majorant` of `A` itself. -/
theorem Submission.eilenberg_inequality_theorem : EilenbergInequality := by
  intro X _ _ _ _ m k A f K _ hk hA hAfin hf
  obtain ⟨Q, hQc, hQA, hQmono, hN⟩ := Submission.eilenberg_compact_exhaustion X
    (Chapter01.simonHausdorffMeasureReal (m + k)) A hA hAfin
  -- The majorant of the null remainder `N` vanishes a.e., hence so do the fibre measures of `N`.
  obtain ⟨G₀, hG₀, hG₀le, hG₀int⟩ := Submission.eilenberg_covering_majorant X m k
    (A \ ⋃ j, Q j) f K hk (hN.trans_lt ENNReal.zero_lt_top) (hf.mono sdiff_subset)
  rw [hN, mul_zero, nonpos_iff_eq_zero, lintegral_eq_zero_iff hG₀] at hG₀int
  -- Continuity from below along the increasing fibres `Q j ∩ f⁻¹{y}`.
  have hmeas : Measurable fun y ↦
      Chapter01.simonHausdorffMeasureReal k ((⋃ j, Q j) ∩ f ⁻¹' {y}) := by
    have hsup : (fun y ↦ Chapter01.simonHausdorffMeasureReal k ((⋃ j, Q j) ∩ f ⁻¹' {y})) =
        fun y ↦ ⨆ j, Chapter01.simonHausdorffMeasureReal k (Q j ∩ f ⁻¹' {y}) := by
      funext y
      rw [iUnion_inter]
      exact Monotone.measure_iUnion fun i j hij ↦ inter_subset_inter_left _ (hQmono hij)
    rw [hsup]
    exact Measurable.iSup fun j ↦ Submission.eilenberg_compact_fiber_measurable X m k (Q j) f hk
      (hQc j) (hf.mono (hQA j)).continuousOn
  have hae : (fun y ↦ Chapter01.simonHausdorffMeasureReal k ((⋃ j, Q j) ∩ f ⁻¹' {y})) =ᵐ[volume]
      fun y ↦ Chapter01.simonHausdorffMeasureReal k (A ∩ f ⁻¹' {y}) := by
    filter_upwards [hG₀int] with y hy
    refine le_antisymm (measure_mono (inter_subset_inter_left _ (iUnion_subset hQA))) ?_
    calc Chapter01.simonHausdorffMeasureReal k (A ∩ f ⁻¹' {y})
        ≤ Chapter01.simonHausdorffMeasureReal k ((⋃ j, Q j) ∩ f ⁻¹' {y}) +
            Chapter01.simonHausdorffMeasureReal k ((A \ ⋃ j, Q j) ∩ f ⁻¹' {y}) := by
          refine (measure_mono fun x hx ↦ ?_).trans (measure_union_le _ _)
          by_cases hxQ : x ∈ ⋃ j, Q j
          exacts [Or.inl ⟨hxQ, hx.2⟩, Or.inr ⟨⟨hx.1, hxQ⟩, hx.2⟩]
      _ = Chapter01.simonHausdorffMeasureReal k ((⋃ j, Q j) ∩ f ⁻¹' {y}) := by
          rw [nonpos_iff_eq_zero.1 ((hG₀le y).trans_eq hy), add_zero]
  obtain ⟨G, -, hGle, hGint⟩ := Submission.eilenberg_covering_majorant X m k A f K hk hAfin hf
  exact ⟨hmeas.aemeasurable.congr hae, (lintegral_mono hGle).trans hGint⟩
/-- **The distance gradient points into `U` near `∂U`** (Simon 2.8, proof, C2, inequality (1)).
Let `U ⊆ ℝⁿ` be open and convex with `Uᶜ ≠ ∅`, `r > 0`, `closedBall ξ r ⊆ U`, and
`d(y) = infDist y Uᶜ`. Take `η > 0` to be the minimum of `d` over the compact ball
`closedBall ξ r ⊆ U`. Fix `x ∈ U` with `d(x) < η` at which `d` is differentiable, and put
`L = Dd(x)`. Then `‖L‖ = 1` (`Submission.bv_ext_norm_fderiv_infDist_eq_one`), so the Riesz
vector `ν` of `L` is a unit vector with `L ν = 1`. The point `w = ξ - r • ν` lies in the ball,
so `d(x) < η ≤ d(w)`. Since `d` is concave on `U` (`Submission.bv_ext_infDist_compl_concaveOn`),
its restriction to the segment from `x` to `w` gives `d(w) - d(x) ≤ L (w - x) = -L (x - ξ) - r`
(`ConcaveOn.slope_le_of_hasDerivAt`). -/
theorem Submission.bv_ext_infDist_compl_fderiv_lt : ∀ (n : ℕ) (U : Set (Rn n)) (ξ : Rn n) (r : ℝ), IsOpen U → Convex ℝ U → Uᶜ.Nonempty → 0 < r → closedBall ξ r ⊆ U → ∃ η : ℝ, 0 < η ∧ ∀ x ∈ U, infDist x Uᶜ < η → DifferentiableAt ℝ (fun y ↦ infDist y Uᶜ) x → r < -fderiv ℝ (fun y ↦ infDist y Uᶜ) x (x - ξ) := by
  intro n U ξ r hUo hUc hne hr hball
  -- Step 1: `Uᶜ` is closed and nonempty, so `d > 0` on `U`.
  have hcl : IsClosed Uᶜ := hUo.isClosed_compl
  have hpos : ∀ y ∈ U, 0 < infDist y Uᶜ := fun y hy ↦
    (hcl.notMem_iff_infDist_pos hne).1 (Set.notMem_compl_iff.2 hy)
  -- Step 2: `η = d(y₀)` is the minimum of `d` over the compact ball `closedBall ξ r ⊆ U`.
  obtain ⟨y₀, hy₀, hmin⟩ := (isCompact_closedBall ξ r).exists_isMinOn
    (nonempty_closedBall.2 hr.le) (continuous_infDist_pt Uᶜ).continuousOn
  refine ⟨infDist y₀ Uᶜ, hpos y₀ (hball hy₀), fun x hx hxη hdiff ↦ ?_⟩
  -- Step 3: `L = Dd(x)` has norm `1`.
  generalize hL : fderiv ℝ (fun y ↦ infDist y Uᶜ) x = L
  have hfd : HasFDerivAt (fun y ↦ infDist y Uᶜ) L x := hL ▸ hdiff.hasFDerivAt
  have hLnorm : ‖L‖ = 1 := hL ▸ Submission.bv_ext_norm_fderiv_infDist_eq_one n Uᶜ x hcl hne
    (Set.notMem_compl_iff.2 hx) hdiff
  -- Step 4: the Riesz vector `ν` of `L` is a unit vector with `L ν = 1`.
  obtain ⟨ν, hν, hLν⟩ : ∃ ν : Rn n, ‖ν‖ = 1 ∧ L ν = 1 := by
    set e := InnerProductSpace.toDual ℝ (Rn n)
    refine ⟨e.symm L, by rw [LinearIsometryEquiv.norm_map, hLnorm], ?_⟩
    rw [← InnerProductSpace.toDual_symm_apply (x := e.symm L) (y := L),
      real_inner_self_eq_norm_sq, LinearIsometryEquiv.norm_map, hLnorm, one_pow]
  -- Step 5: `w = ξ - r • ν` lies in `closedBall ξ r ⊆ U`, so `d(x) < η ≤ d(w)`.
  obtain ⟨w, hw⟩ : ∃ w : Rn n, w = ξ - r • ν := ⟨_, rfl⟩
  have hwball : w ∈ closedBall ξ r := by
    rw [mem_closedBall, dist_eq_norm, hw, sub_sub_cancel_left, norm_neg, norm_smul, hν, mul_one,
      Real.norm_of_nonneg hr.le]
  have hdw : infDist x Uᶜ < infDist w Uᶜ := hxη.trans_le (isMinOn_iff.1 hmin w hwball)
  -- Step 6: concavity of `d` along the segment from `x` to `w` gives `d(w) - d(x) ≤ L (w - x)`.
  have hsuper : infDist w Uᶜ - infDist x Uᶜ ≤ L (w - x) := by
    have hcv := (Submission.bv_ext_infDist_compl_concaveOn n U hUc).comp_affineMap
      (AffineMap.lineMap x w)
    have hder := hfd.comp_hasDerivAt_of_eq 0 (AffineMap.hasDerivAt_lineMap (a := x) (b := w))
      (AffineMap.lineMap_apply_zero x w).symm
    simpa [slope_def_field] using
      hcv.slope_le_of_hasDerivAt (by simpa using hx) (by simpa using hball hwball) zero_lt_one hder
  -- Step 7: `L (w - x) = -L (x - ξ) - r`.
  have hcomp : L (w - x) = -L (x - ξ) - r := by
    rw [show w - x = -(x - ξ) - r • ν by rw [hw]; abel, map_sub, map_neg, map_smul, hLν,
      smul_eq_mul, mul_one]
  -- Step 8: `0 < d(w) - d(x) ≤ -L (x - ξ) - r`.
  linarith

/-- **Cut-offs for the BV extension estimate** (Simon Ch. 2, proof of Lemma 2.8, (2)–(3), p. 52).
Let `U ⊂ ℝⁿ` be bounded, open and convex, and `B_r(ξ) ⊂ U` with `r > 0`. Then there are Lipschitz
`φ_j : ℝⁿ → [0, 1]` with compact support in `U` such that `φ_j → 1_U` pointwise and
`r |Dφ_j| ≤ -Dφ_j(x)[x - ξ]` for `Lⁿ`-a.e. `x`. Take `φ_j = γ_j ∘ d`, where `d = dist(·, ℝⁿ \ U)` and
`γ_j(t) = min(1, max(0, 2t/ε_j - 1))`. The level `ε_j < min(η, 1/(j+1))` is chosen so that
`{d = ε_j}` and `{d = ε_j/2}` are `Lⁿ`-null. Here `η` is given by
`Submission.bv_ext_infDist_compl_fderiv_lt`: `r < -Dd(x)[x - ξ]` at every `x ∈ U` with `d(x) < η`
at which `d` is differentiable. -/
theorem Submission.bv_ext_exists_cutoffs : ∀ (n : ℕ) (U : Set (Rn n)) (ξ : Rn n) (r : ℝ), IsOpen U → Bornology.IsBounded U → Convex ℝ U → 0 < r → closedBall ξ r ⊆ U → ∃ φ : ℕ → Rn n → ℝ, (∀ j, ∃ K, LipschitzWith K (φ j)) ∧ (∀ j x, 0 ≤ φ j x ∧ φ j x ≤ 1) ∧ (∀ j, HasCompactSupport (φ j)) ∧ (∀ j, tsupport (φ j) ⊆ U) ∧ (∀ x, Tendsto (fun j ↦ φ j x) atTop (𝓝 (U.indicator (fun _ ↦ (1 : ℝ)) x))) ∧ ∀ j, ∀ᵐ x ∂volume, r * ‖fderiv ℝ (φ j) x‖ ≤ -fderiv ℝ (φ j) x (x - ξ) := by
  intro n U ξ r hUo hUb hUc hr hball
  rcases Uᶜ.eq_empty_or_nonempty with hUe | hne
  · -- Step 1: `Uᶜ = ∅`, so `U = univ` is compact and `φ_j ≡ 1` works.
    have hU : U = univ := compl_empty_iff.1 hUe
    have hcpt : IsCompact (univ : Set (Rn n)) :=
      Metric.isCompact_of_isClosed_isBounded isClosed_univ (hU ▸ hUb)
    refine ⟨fun _ _ ↦ 1, fun _ ↦ ⟨0, LipschitzWith.const 1⟩,
      fun _ _ ↦ ⟨zero_le_one, le_rfl⟩, fun _ ↦ ?_, fun _ ↦ ?_, fun x ↦ ?_, fun _ ↦ ?_⟩
    · exact hcpt.of_isClosed_subset (isClosed_tsupport _) (subset_univ _)
    · rw [hU]; exact subset_univ _
    · rw [hU, indicator_univ]; exact tendsto_const_nhds
    · exact Filter.Eventually.of_forall fun x ↦ by simp
  -- Step 2: `d = infDist · Uᶜ` is 1-Lipschitz, `0` off `U`, positive on `U`, `‖Dd‖ ≤ 1`, and
  -- differentiable a.e. (Rademacher).
  set d : Rn n → ℝ := fun y ↦ infDist y Uᶜ with hd_def
  have hdlip : LipschitzWith 1 d := lipschitz_infDist_pt Uᶜ
  have hdcont : Continuous d := hdlip.continuous
  have hd0 : ∀ x, x ∉ U → d x = 0 := fun x hx ↦ infDist_zero_of_mem hx
  have hdpos : ∀ x ∈ U, 0 < d x := fun x hx ↦
    (hUo.isClosed_compl.notMem_iff_infDist_pos hne).1 (not_not.2 hx)
  have hDd : ∀ x, ‖fderiv ℝ d x‖ ≤ 1 := fun x ↦ by
    simpa using norm_fderiv_le_of_lipschitz ℝ (x₀ := x) hdlip
  have hdiff : ∀ᵐ x ∂(volume : Measure (Rn n)), DifferentiableAt ℝ d x :=
    hdlip.ae_differentiableAt
  -- Step 3: the boundary-direction inequality near `∂U`.
  obtain ⟨η, hη, hkey⟩ :=
    Submission.bv_ext_infDist_compl_fderiv_lt n U ξ r hUo hUc hne hr hball
  -- Step 4: only countably many levels of `d` have positive measure, so we can pick `ε_j` with
  -- `{d = ε_j}` and `{d = ε_j / 2}` null.
  have hB : {t : ℝ | 0 < (volume : Measure (Rn n)) {y | d y = t}}.Countable :=
    Measure.countable_meas_level_set_pos hdcont.measurable
  have hB' : ({t : ℝ | 0 < (volume : Measure (Rn n)) {y | d y = t}} ∪
      (fun t ↦ 2 * t) '' {t : ℝ | 0 < (volume : Measure (Rn n)) {y | d y = t}}).Countable :=
    hB.union (hB.image _)
  have hε : ∀ j : ℕ, ∃ ε : ℝ, 0 < ε ∧ ε < η ∧ ε < 1 / ((j : ℝ) + 1) ∧
      (volume : Measure (Rn n)) {y | d y = ε} = 0 ∧
      (volume : Measure (Rn n)) {y | d y = ε / 2} = 0 := by
    intro j
    have hpos : 0 < min η (1 / ((j : ℝ) + 1)) := lt_min hη (by positivity)
    have hns : ¬ Ioo 0 (min η (1 / ((j : ℝ) + 1))) ⊆
        {t : ℝ | 0 < (volume : Measure (Rn n)) {y | d y = t}} ∪
        (fun t ↦ 2 * t) '' {t : ℝ | 0 < (volume : Measure (Rn n)) {y | d y = t}} := by
      intro hsub
      have h0 := measure_mono_null hsub (hB'.measure_zero volume)
      rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at h0
      linarith
    obtain ⟨ε, hεI, hεB⟩ := not_subset.1 hns
    refine ⟨ε, hεI.1, hεI.2.trans_le (min_le_left _ _), hεI.2.trans_le (min_le_right _ _), ?_, ?_⟩
    · by_contra h
      exact hεB (Or.inl (pos_iff_ne_zero.2 h))
    · by_contra h
      exact hεB (Or.inr ⟨ε / 2, pos_iff_ne_zero.2 h, by beta_reduce; ring⟩)
  choose ε hε0 hεη hεj hεnull hεnull2 using hε
  -- Step 5: the cut-offs `φ_j = min 1 (max 0 (2 d / ε_j - 1))`.
  set φ : ℕ → Rn n → ℝ := fun j x ↦ min 1 (max 0 (2 * d x / ε j - 1)) with hφ_def
  have hφ0 : ∀ j x, d x ≤ ε j / 2 → φ j x = 0 := by
    intro j x hx
    have h1 : 2 * d x / ε j - 1 ≤ 0 := by
      rw [sub_nonpos, div_le_one (hε0 j)]; linarith
    simp only [hφ_def, max_eq_left h1, min_eq_right zero_le_one]
  have hφ1 : ∀ j x, ε j ≤ d x → φ j x = 1 := by
    intro j x hx
    have h1 : 1 ≤ 2 * d x / ε j - 1 := by
      rw [le_sub_iff_add_le, le_div_iff₀ (hε0 j)]; linarith
    simp only [hφ_def, max_eq_right (zero_le_one.trans h1), min_eq_left h1]
  have hφlin : ∀ j x, ε j / 2 ≤ d x → d x ≤ ε j → φ j x = 2 * d x / ε j - 1 := by
    intro j x h1 h2
    have a1 : 0 ≤ 2 * d x / ε j - 1 := by
      rw [sub_nonneg, one_le_div (hε0 j)]; linarith
    have a2 : 2 * d x / ε j - 1 ≤ 1 := by
      rw [sub_le_iff_le_add, div_le_iff₀ (hε0 j)]; linarith
    simp only [hφ_def, max_eq_right a1, min_eq_right a2]
  -- Step 7: `tsupport φ_j ⊆ {ε_j / 2 ≤ d} ⊆ U`.
  have htsupp : ∀ j, tsupport (φ j) ⊆ {x | ε j / 2 ≤ d x} := by
    intro j
    refine closure_minimal ?_ (isClosed_le continuous_const hdcont)
    intro x hx
    by_contra h
    exact hx (hφ0 j x (le_of_lt (not_le.1 h)))
  have hFU : ∀ j, {x | ε j / 2 ≤ d x} ⊆ U := by
    intro j x hx
    by_contra h
    have h1 := hd0 x h
    have h2 := hε0 j
    simp only [mem_ofPred_eq] at hx
    linarith
  refine ⟨φ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Step 6: `φ_j` is `(2 / ε_j)`-Lipschitz.
    intro j
    have he := hε0 j
    have hlin : LipschitzWith (Real.toNNReal (2 / ε j)) (fun x ↦ 2 * d x / ε j - 1) := by
      refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
      rw [Real.coe_toNNReal _ (by positivity), Real.dist_eq]
      have hxy : |d x - d y| ≤ dist x y := by
        simpa [Real.dist_eq] using hdlip.dist_le_mul x y
      calc |2 * d x / ε j - 1 - (2 * d y / ε j - 1)| = 2 / ε j * |d x - d y| := by
            rw [show 2 * d x / ε j - 1 - (2 * d y / ε j - 1) = 2 / ε j * (d x - d y) by ring,
              abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / ε j)]
        _ ≤ 2 / ε j * dist x y := by gcongr
    exact ⟨_, (hlin.const_max 0).const_min 1⟩
  · -- Step 6: `0 ≤ φ_j ≤ 1`.
    intro j x
    exact ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩
  · -- Step 7: `{ε_j / 2 ≤ d}` is closed and bounded, hence compact.
    intro j
    have hF : IsCompact {x | ε j / 2 ≤ d x} :=
      Metric.isCompact_of_isClosed_isBounded (isClosed_le continuous_const hdcont)
        (hUb.subset (hFU j))
    exact hF.of_isClosed_subset (isClosed_tsupport _) (htsupp j)
  · intro j
    exact (htsupp j).trans (hFU j)
  · -- Step 8: `φ_j(x)` is eventually `1_U(x)`.
    intro x
    by_cases hx : x ∈ U
    · rw [indicator_of_mem hx]
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt (hdpos x hx)
      refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun j hj ↦ ?_⟩)
      symm
      apply hφ1
      have : 1 / ((j : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
        gcongr
      linarith [hεj j]
    · rw [indicator_of_notMem hx]
      refine tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun j ↦ ?_)
      symm
      apply hφ0
      rw [hd0 x hx]
      have := hε0 j
      linarith
  · -- Step 9: off `{d = ε_j} ∪ {d = ε_j / 2}` and the non-differentiability set of `d`, either
    -- `Dφ_j(x) = 0` or `Dφ_j(x) = (2 / ε_j) Dd(x)` with `0 < d(x) < ε_j < η`.
    intro j
    have he := hε0 j
    have hn1 : ∀ᵐ x ∂(volume : Measure (Rn n)), d x ≠ ε j := by
      rw [ae_iff]; simpa using hεnull j
    have hn2 : ∀ᵐ x ∂(volume : Measure (Rn n)), d x ≠ ε j / 2 := by
      rw [ae_iff]; simpa using hεnull2 j
    filter_upwards [hdiff, hn1, hn2] with x hxd hx1 hx2
    rcases lt_or_gt_of_ne hx2 with hlt | hgt
    · -- (a) `d x < ε_j / 2`: `φ_j = 0` near `x`.
      have hloc : φ j =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := by
        filter_upwards [(isOpen_lt hdcont continuous_const).mem_nhds hlt] with y hy
        exact hφ0 j y (le_of_lt hy)
      rw [hloc.fderiv_eq]
      simp
    rcases lt_or_gt_of_ne hx1 with hlt' | hgt'
    · -- (c) `ε_j / 2 < d x < ε_j`: `φ_j = 2 d / ε_j - 1` near `x`.
      have hloc : φ j =ᶠ[𝓝 x] fun y ↦ 2 * d y / ε j - 1 := by
        filter_upwards [(isOpen_lt continuous_const hdcont).mem_nhds hgt,
          (isOpen_lt hdcont continuous_const).mem_nhds hlt'] with y hy1 hy2
        exact hφlin j y (le_of_lt hy1) (le_of_lt hy2)
      have hderiv : fderiv ℝ (φ j) x = (2 / ε j) • fderiv ℝ d x := by
        rw [hloc.fderiv_eq]
        have hfun : (fun y ↦ 2 * d y / ε j - 1) = (fun y ↦ 2 / ε j * d y - 1) := by
          funext y; ring
        rw [hfun]
        exact ((hxd.hasFDerivAt.const_mul (2 / ε j)).sub_const 1).fderiv
      have hxU : x ∈ U := by
        by_contra h
        rw [hd0 x h] at hgt
        linarith
      have hk : r < -fderiv ℝ d x (x - ξ) := hkey x hxU (by linarith [hεη j]) hxd
      have h2e : (0 : ℝ) < 2 / ε j := by positivity
      rw [hderiv, norm_smul, smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_of_pos h2e]
      calc r * (2 / ε j * ‖fderiv ℝ d x‖) ≤ r * (2 / ε j * 1) := by
            gcongr
            exact hDd x
        _ = 2 / ε j * r := by ring
        _ ≤ 2 / ε j * (-fderiv ℝ d x (x - ξ)) := mul_le_mul_of_nonneg_left hk.le h2e.le
        _ = -(2 / ε j * fderiv ℝ d x (x - ξ)) := by ring
    · -- (b) `d x > ε_j`: `φ_j = 1` near `x`.
      have hloc : φ j =ᶠ[𝓝 x] fun _ ↦ (1 : ℝ) := by
        filter_upwards [(isOpen_lt continuous_const hdcont).mem_nhds hgt'] with y hy
        exact hφ1 j y (le_of_lt hy)
      rw [hloc.fderiv_eq]
      simp

/-- **Simon Ch. 2, Lemma 2.8 (p. 51), BV extension estimate**, with `C = max (1 + δ⁻¹) (n δ⁻¹)`.
The first conjunct is `bv_ext_variation_eq_zero_of_ae_eq_zero` on the open set `(closure U)ᶜ`.
For the second, take the cut-offs `φ_j` of `bv_ext_exists_cutoffs` with `r = δR`. By
`bv_ext_lintegral_enorm_mul_fderiv_le` and `bv_abs_variation_le`,
`∫ |u| |Dφ_j| ≤ δ⁻¹ |Du|(U) + n δ⁻¹ R⁻¹ ∫_U |u|`. For an admissible field `g` on `ℝⁿ`,
`bv_ext_ofReal_integral_cutoff_le` bounds `∫ φ_j u div g` by `|Du|(U) + ∫ |u| |Dφ_j|`, hence by
`C (|Du|(U) + R⁻¹ ∫_U |u|)`. Since `φ_j → 1_U` and `1_U u = u` a.e. (`u = 0` a.e. off `Ū`, and the
frontier of the convex set `U` is null), dominated convergence gives `∫ φ_j u div g → ∫ u div g`;
the supremum over `g` is the claim. -/
theorem Submission.bv_extension_estimate_theorem : BVExtensionEstimate := by
  intro n δ hδ _hδ1
  -- Step 1: the constant `C = max (1 + δ⁻¹) (n δ⁻¹)`.
  set C : ℝ := max (1 + δ⁻¹) (n * δ⁻¹)
  refine ⟨C, le_max_of_le_left (by positivity), ?_⟩
  intro U R ξ u hUo hUb hUc hR _hξ hball hUR hu hsupp
  have hu_int : Integrable u volume := integrableOn_univ.1 hu.2.1
  -- Step 2 (C0): `u = 0` a.e. on the open set `(closure U)ᶜ`, so its variation there vanishes.
  refine ⟨Submission.bv_ext_variation_eq_zero_of_ae_eq_zero n _ u
    isClosed_closure.isOpen_compl.measurableSet hsupp, ?_⟩
  -- Step 3 (C3): the cut-offs `φ_j`, with `r = δR`.
  have hδR : 0 < δ * R := mul_pos hδ hR
  obtain ⟨φ, hφL, hφ01, hφc, hφs, hφlim, hφae⟩ :=
    Submission.bv_ext_exists_cutoffs n U ξ (δ * R) hUo hUb hUc hδR hball
  set A := Chapter02.bvVariationOn u U
  set B := ∫⁻ x in U, ‖u x‖ₑ
  -- Step 4 (C4): `∫ |u| |Dφ_j| ≤ δ⁻¹ |Du|(U) + n δ⁻¹ R⁻¹ ∫_U |u|`.
  have habs : Chapter02.bvVariationOn (fun x ↦ |u x|) U ≤ A :=
    Submission.bv_abs_variation_le n U u hUo hu_int.integrableOn.locallyIntegrableOn
  have hgrad : ∀ j, ∫⁻ x, ‖u x‖ₑ * ‖fderiv ℝ (φ j) x‖ₑ ≤
      ENNReal.ofReal δ⁻¹ * A + ENNReal.ofReal (n * δ⁻¹) * (ENNReal.ofReal R⁻¹ * B) := by
    intro j
    have hw := Submission.bv_ext_lintegral_enorm_mul_fderiv_le n U ξ R (δ * R) u (φ j) hUo hR hUR
      hu_int (hφL j) (hφ01 j) (hφc j) (hφs j) (hφae j)
    have hinv : ENNReal.ofReal (δ * R)⁻¹ * ENNReal.ofReal (δ * R) = 1 := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.2 hδR.le), inv_mul_cancel₀ hδR.ne', ENNReal.ofReal_one]
    have e1 : ENNReal.ofReal (δ * R)⁻¹ * ENNReal.ofReal R = ENNReal.ofReal δ⁻¹ := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.2 hδR.le)]
      congr 1
      field_simp
    have e2 : ENNReal.ofReal (δ * R)⁻¹ * (n : ℝ≥0∞) =
        ENNReal.ofReal (n * δ⁻¹) * ENNReal.ofReal R⁻¹ := by
      rw [← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_mul (inv_nonneg.2 hδR.le),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    calc ∫⁻ x, ‖u x‖ₑ * ‖fderiv ℝ (φ j) x‖ₑ
        = ENNReal.ofReal (δ * R)⁻¹ *
            (ENNReal.ofReal (δ * R) * ∫⁻ x, ‖u x‖ₑ * ‖fderiv ℝ (φ j) x‖ₑ) := by
          rw [← mul_assoc, hinv, one_mul]
      _ ≤ ENNReal.ofReal (δ * R)⁻¹ * (ENNReal.ofReal R * A + n * B) := by
          gcongr
          exact hw.trans (by gcongr)
      _ = ENNReal.ofReal δ⁻¹ * A + ENNReal.ofReal (n * δ⁻¹) * (ENNReal.ofReal R⁻¹ * B) := by
          rw [mul_add, ← mul_assoc, e1, ← mul_assoc, e2, mul_assoc]
  -- Step 5: `A + (δ⁻¹ A + n δ⁻¹ R⁻¹ B) ≤ C (A + R⁻¹ B)`.
  have hfin : A + (ENNReal.ofReal δ⁻¹ * A + ENNReal.ofReal (n * δ⁻¹) * (ENNReal.ofReal R⁻¹ * B)) ≤
      ENNReal.ofReal C * (A + ENNReal.ofReal R⁻¹ * B) := by
    have h1 : 1 + ENNReal.ofReal δ⁻¹ ≤ ENNReal.ofReal C := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (inv_nonneg.2 hδ.le)]
      exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
    have h2 : ENNReal.ofReal (n * δ⁻¹) ≤ ENNReal.ofReal C :=
      ENNReal.ofReal_le_ofReal (le_max_right _ _)
    calc A + (ENNReal.ofReal δ⁻¹ * A + ENNReal.ofReal (n * δ⁻¹) * (ENNReal.ofReal R⁻¹ * B))
        = (1 + ENNReal.ofReal δ⁻¹) * A + ENNReal.ofReal (n * δ⁻¹) * (ENNReal.ofReal R⁻¹ * B) := by
          ring
      _ ≤ ENNReal.ofReal C * A + ENNReal.ofReal C * (ENNReal.ofReal R⁻¹ * B) := by gcongr
      _ = ENNReal.ofReal C * (A + ENNReal.ofReal R⁻¹ * B) := by ring
  -- Step 6 (C5): fix an admissible test field `g` on `ℝⁿ`, `K`-Lipschitz.
  refine iSup_le fun g ↦ iSup_le fun hg ↦ iSup_le fun _ ↦ iSup_le fun hn ↦ ?_
  obtain ⟨K, hK⟩ := hg
  rw [setIntegral_univ]
  -- Step 7: a.e. `x ∈ U` or `u x = 0`, since `u = 0` a.e. off `closure U` and the frontier of the
  -- convex set `U` is null.
  have hae : ∀ᵐ x ∂(volume : Measure (Rn n)), x ∈ U ∨ u x = 0 := by
    filter_upwards [hsupp, measure_eq_zero_iff_ae_notMem.1 (hUc.addHaar_frontier volume)]
      with x hx hxf
    by_cases hxU : x ∈ U
    · exact Or.inl hxU
    · refine Or.inr (hx fun hxc ↦ hxf ?_)
      rw [hUo.frontier_eq]
      exact ⟨hxc, hxU⟩
  -- Step 8: dominated convergence, `∫ φ_j u div g → ∫ u div g`, dominated by `n K |u|`.
  have hlim : Tendsto (fun j ↦ ∫ x, φ j x * u x * Chapter02.euclideanDivergence (g : Rn n → Rn n) x)
      atTop (𝓝 (∫ x, u x * Chapter02.euclideanDivergence (g : Rn n → Rn n) x)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x ↦ ‖u x‖ * ((Module.finrank ℝ (Rn n) : ℝ) * K)) (fun j ↦ ?_)
      (hu_int.norm.mul_const _) (fun j ↦ ae_of_all _ fun x ↦ ?_) ?_
    · obtain ⟨Kj, hKj⟩ := hφL j
      exact (hKj.continuous.aestronglyMeasurable.mul hu_int.aestronglyMeasurable).mul
        (Chapter02.measurable_euclideanDivergence _).aestronglyMeasurable
    · have h1 : ‖φ j x‖ ≤ 1 := by
        rw [Real.norm_of_nonneg (hφ01 j x).1]
        exact (hφ01 j x).2
      rw [norm_mul, norm_mul]
      calc ‖φ j x‖ * ‖u x‖ * ‖Chapter02.euclideanDivergence (g : Rn n → Rn n) x‖
          ≤ 1 * ‖u x‖ * ((Module.finrank ℝ (Rn n) : ℝ) * K) := by
            gcongr
            exact Chapter02.norm_euclideanDivergence_le_of_lipschitz hK x
        _ = ‖u x‖ * ((Module.finrank ℝ (Rn n) : ℝ) * K) := by rw [one_mul]
    · filter_upwards [hae] with x hx
      convert ((hφlim x).mul_const (u x)).mul_const
        (Chapter02.euclideanDivergence (g : Rn n → Rn n) x) using 2
      rcases hx with hx | hx <;> simp [hx]
  -- Step 9: each `∫ φ_j u div g` is at most `C (|Du|(U) + R⁻¹ ∫_U |u|)`; pass to the limit.
  refine le_of_tendsto' ((ENNReal.continuous_ofReal.tendsto _).comp hlim) fun j ↦ ?_
  calc ENNReal.ofReal (∫ x, φ j x * u x * Chapter02.euclideanDivergence (g : Rn n → Rn n) x)
      ≤ A + ∫⁻ x, ‖u x‖ₑ * ‖fderiv ℝ (φ j) x‖ₑ :=
        Submission.bv_ext_ofReal_integral_cutoff_le n U u (φ j) g hUo hu_int (hφL j) (hφ01 j)
          (hφc j) (hφs j) ⟨K, hK⟩ hn
    _ ≤ A + (ENNReal.ofReal δ⁻¹ * A + ENNReal.ofReal (n * δ⁻¹) * (ENNReal.ofReal R⁻¹ * B)) := by
        gcongr
        exact hgrad j
    _ ≤ ENNReal.ofReal C * (A + ENNReal.ofReal R⁻¹ * B) := hfin

/-- **Simon Ch. 2, Theorem 2.6, Lemma 2.7 and Lemma 2.8.** Compactness for `BV_loc`, the BV
Poincaré inequality on convex sets and the BV extension estimate. -/
theorem Submission.bv_compactness_poincare_extension : BVCompactness ∧ BVPoincare ∧ BVExtensionEstimate :=
  ⟨Submission.bv_compactness_theorem, Submission.bv_poincare_theorem,
    Submission.bv_extension_estimate_theorem⟩
/-- **Simon Ch. 2, 4.3 (p. 55), `T_{ψ(x)} M ⊆ range Dψ(x)`.** If `(V, W, ψ)` is a `C^r` local
representation of `M`, `r ≥ 1`, and `ψ⁻¹ = invFunOn ψ V` is continuous on `W ∩ M`, then
`T_{ψ(x)} M ⊆ range Dψ(x)` for `x ∈ V`. A `C¹` curve `γ` in `M` through `ψ(x)` stays in `W ∩ M`
near `0`, so `γ = ψ ∘ c` there with `c = ψ⁻¹ ∘ γ → x`, and `simon_lift_velocity_mem_range_fderiv`
puts `γ'(0)` in `range Dψ(x)`. -/
theorem Submission.simon_chart_tangentSpace_le_range_fderiv : ∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)) (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N), 1 ≤ r → Chapter02.IsSimonLocalRepresentation r M V W ψ → ContinuousOn (Function.invFunOn ψ V) (W ∩ M) → ∀ x ∈ V, tangentSpace M (ψ x) ≤ LinearMap.range (fderiv ℝ ψ x).toLinearMap := by
  intro n N r M V W ψ hr hψ hcont x₀ hx₀
  obtain ⟨hV, hW, hψC, hψinj, hψimg, -, hψder⟩ := hψ
  have hdiff : DifferentiableAt ℝ ψ x₀ :=
    ((hψC.of_le (by exact_mod_cast hr)).differentiableOn_one x₀ hx₀).differentiableAt
      (hV.mem_nhds hx₀)
  have hy₀ : ψ x₀ ∈ W ∩ M := by rw [← hψimg]; exact mem_image_of_mem ψ hx₀
  -- It suffices to treat a generator `v = γ'(0)` of `T_{ψ(x₀)} M`.
  rw [tangentSpace, Submodule.span_le]
  rintro v ⟨γ, -, hγM, hγ0, hγv⟩
  -- `γ(t) ∈ W ∩ M` for `t` near `0`.
  have hγWM : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ W ∩ M := by
    have hγ0W : γ 0 ∈ W := by rw [hγ0]; exact hy₀.1
    filter_upwards [hγv.continuousAt.preimage_mem_nhds (hW.mem_nhds hγ0W),
      Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num) one_pos] with t htW htI
    exact ⟨htW, hγM htI⟩
  -- The lift `c = ψ⁻¹ ∘ γ` satisfies `γ = ψ ∘ c` near `0` and `c(t) → ψ⁻¹(ψ x₀) = x₀`.
  have hfac : ∀ᶠ t in 𝓝 (0 : ℝ), γ t = ψ (Function.invFunOn ψ V (γ t)) := by
    filter_upwards [hγWM] with t ht
    rw [← hψimg] at ht
    exact (Function.invFunOn_eq ht).symm
  have hc : Tendsto (fun t ↦ Function.invFunOn ψ V (γ t)) (𝓝 (0 : ℝ)) (𝓝 x₀) := by
    have hγt : Tendsto γ (𝓝 (0 : ℝ)) (𝓝[W ∩ M] (ψ x₀)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, hγWM⟩
      rw [← hγ0]
      exact hγv.continuousAt.tendsto
    have hg := (hcont (ψ x₀) hy₀).tendsto
    rw [hψinj.leftInvOn_invFunOn hx₀] at hg
    exact hg.comp hγt
  exact Submission.simon_lift_velocity_mem_range_fderiv n N ψ x₀
    (fun t ↦ Function.invFunOn ψ V (γ t)) γ v hdiff (hψder x₀ hx₀) hc hfac hγv

/-- **Simon Ch. 2, 4.3 (p. 55).** If `(V, W, ψ)` is a `C^r` local representation of `M`, `r ≥ 1`,
then `T_{ψ(x)} M = range Dψ(x)` for `x ∈ V`. `range Dψ(x) ⊆ T_{ψ(x)} M` holds for any `C¹` map of
the open set `V` into `M` (here `ψ(V) = W ∩ M`). Conversely, every generating velocity of
`T_{ψ(x)} M` lies in `range Dψ(x)`, since its curve lifts through `ψ⁻¹ = invFunOn ψ V`, which is
continuous on `W ∩ M` by 4.2. -/
theorem Submission.simon_submanifold_tangentSpace_eq_range : ∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)) (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N), 1 ≤ r → Chapter02.IsSimonLocalRepresentation r M V W ψ → ∀ x ∈ V, tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap := by
  intro n N r M V W ψ hr h x hx
  -- Part A: `ψ` is a `C¹` map of the open set `V` into `ψ(V) = W ∩ M ⊆ M`.
  have hA : LinearMap.range (fderiv ℝ ψ x).toLinearMap ≤ tangentSpace M (ψ x) :=
    Submission.simon_chart_range_fderiv_le_tangentSpace n N M V ψ h.isOpen_source
      (h.contDiffOn.of_le (by exact_mod_cast hr))
      ((mapsTo_image ψ V).mono_right (h.image_eq.subset.trans inter_subset_right)) x hx
  -- Part B: generating curves lift through `invFunOn ψ V`, continuous on `W ∩ M` (Simon 4.2).
  have hB : tangentSpace M (ψ x) ≤ LinearMap.range (fderiv ℝ ψ x).toLinearMap :=
    Submission.simon_chart_tangentSpace_le_range_fderiv n N r M V W ψ hr h
      (Submission.simon_submanifold_chart_inverse_continuousOn n N r M V W ψ h) x hx
  exact le_antisymm hB hA

/-- **Simon Ch. 2, §4 (p. 55), from 4.1–4.3: the tangent projection `y ↦ P_y` is continuous on
`M`.** Near `y₀ ∈ M` take a local representation `(V, W, ψ)` with `y₀ ∈ W` and let
`g = invFunOn ψ V : W ∩ M → V`. As `T_{ψ(x)} M = range Dψ(x)` (4.3,
`simon_submanifold_tangentSpace_eq_range`), `P_y = P_{range Dψ(g(y))}` for `y ∈ W ∩ M`. The right
side is continuous on `W ∩ M`: it composes `g` (`simon_submanifold_chart_inverse_continuousOn`),
`x ↦ Dψ(x)` (continuous on the open `V`, with injective values) and `A ↦ P_{range A}`
(`simon_submanifold_range_starProjection_continuousOn`). As `W` is a neighbourhood of `y₀`,
continuity within `W ∩ M` at `y₀` is continuity within `M`. -/
theorem Submission.simon_submanifold_tangentProjection_continuousOn : ∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)), Chapter02.IsSimonSubmanifold (E := Rn n) r M → ContinuousOn (tangentProjection M) M := by
  intro n N r M hM y₀ hy₀
  -- Step 1: a local representation `(V, W, ψ)` with `y₀ ∈ W`; `g = invFunOn ψ V`.
  obtain ⟨V, W, ψ, hy₀W, hψ⟩ := hM.exists_localRepresentation hy₀
  set g := Function.invFunOn ψ V
  -- Step 2: `W ∩ M = ψ(V)`, so `g` maps `W ∩ M` into `V` and `ψ (g y) = y` there.
  have hsurj : SurjOn ψ V (W ∩ M) := hψ.image_eq.symm.subset
  have hgV : MapsTo g (W ∩ M) V := hsurj.mapsTo_invFunOn
  have hψg : RightInvOn g ψ (W ∩ M) := hsurj.rightInvOn_invFunOn
  -- Step 3: `P_y = P_{range Dψ(g(y))}` on `W ∩ M`, as `T_y M = T_{ψ(g(y))} M = range Dψ(g(y))`.
  have hP : EqOn (tangentProjection M)
      (fun y ↦ (LinearMap.range (fderiv ℝ ψ (g y)).toLinearMap).starProjection) (W ∩ M) := by
    intro y hy
    have hT := Submission.simon_submanifold_tangentSpace_eq_range n N r M V W ψ hM.1 hψ (g y)
      (hgV hy)
    rw [hψg hy] at hT
    simp only [tangentProjection, hT]
  -- Step 4: the right side is continuous on `W ∩ M`, as the composite of `g`, `x ↦ Dψ(x)` (which
  -- maps `V` into the injective maps) and `A ↦ P_{range A}`.
  have hDψ : ContinuousOn (fderiv ℝ ψ) V :=
    hψ.contDiffOn.continuousOn_fderiv_of_isOpen hψ.isOpen_source (by exact_mod_cast hM.1)
  have hcont : ContinuousOn
      (fun y ↦ (LinearMap.range (fderiv ℝ ψ (g y)).toLinearMap).starProjection) (W ∩ M) :=
    (Submission.simon_submanifold_range_starProjection_continuousOn n N).comp
      (hDψ.comp (Submission.simon_submanifold_chart_inverse_continuousOn n N r M V W ψ hψ) hgV)
      fun _ hy ↦ hψ.injective_fderiv (hgV hy)
  -- Steps 5–6: so `P` is continuous within `W ∩ M` at `y₀`, and `W ∩ M ∈ 𝓝[M] y₀` as `W` is open.
  exact (hcont.congr hP y₀ ⟨hy₀W, hy₀⟩).mono_of_mem_nhdsWithin
    (mem_nhdsWithin.2 ⟨W, hψ.isOpen_target, hy₀W, subset_rfl⟩)

/-- **Simon Ch. 2, 4.1–4.3 (p. 55).** (1) If `ψ : V → W` is a local representation of `M` of class
`C^r`, `r ≥ 1`, then `T_{ψ(x)} M = range Dψ(x)` for every `x ∈ V`. (2) An `n`-dimensional `C^r`
submanifold `M` is a Borel set and `y ↦ P_y` is continuous on `M`. Part (1) is
`simon_submanifold_tangentSpace_eq_range`. In part (2), `M` is Borel because properness makes it
locally closed and countably many charts cover it (`simon_submanifold_measurableSet`). On a chart,
`P_y` is the projection onto `range Dψ(ψ⁻¹ y)`, which depends continuously on `y` because `Dψ` and
`ψ⁻¹` are continuous (`simon_submanifold_tangentProjection_continuousOn`). -/
theorem Submission.simon_submanifold_tangent_basics : (∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)) (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N), 1 ≤ r → Chapter02.IsSimonLocalRepresentation r M V W ψ → ∀ x ∈ V, tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap) ∧ ∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)), Chapter02.IsSimonSubmanifold (E := Rn n) r M → MeasurableSet M ∧ ContinuousOn (tangentProjection M) M :=
  ⟨Submission.simon_submanifold_tangentSpace_eq_range, fun n N r M hM ↦
    ⟨Submission.simon_submanifold_measurableSet n N r M hM,
      Submission.simon_submanifold_tangentProjection_continuousOn n N r M hM⟩⟩

/-- **Simon Ch. 2, 5.3 and 5.4 (pp. 61–63), first and second variation formulas** (5.4 with the
`C³` correction). Put `S = M ∩ K`, `e y = (y, P_y)` with `P_y = tangentProjection M y`, and
`g (t, (x, P)) = √det(I - P + P (Dφ_t x)* (Dφ_t x) P)`. For `|t| < 1` the map `φ_t` is
differentiable and injective on `S` with injective derivative, so the area formula on `M`
(`variation_submanifold_image_area`) and the Gram identity (`variation_gram_det_identity`) give
`Hⁿ(φ_t(S)) = ∫_S g(t, e y) dHⁿ(y)`. `S` is Borel with `Hⁿ(S) < ∞`, and `e` is continuous on `S`
(`simon_submanifold_tangent_basics`) with values in the compact set
`C = K × {P : ‖P‖ ≤ 1, P ∘ P = P}`, where `g` is `C¹` (`C²` in class `C³`) at `t = 0`
(`variation_jacobian_family`). Differentiating under the integral sign
(`variation_param_integral_deriv`) and identifying the `t`-derivatives of `g(t, e y)` at `0` with
`div_M X y` and `secondVariationIntegrand M φ y` (`variation_jacobian_family`) gives both
formulas. Both integrands vanish off `K`, so `∫_S = ∫_M`. -/
theorem Submission.first_and_second_variation : FirstVariation ∧ SecondVariation := by
  have hImage := Submission.variation_submanifold_image_area
  have hGram := Submission.variation_gram_det_identity
  have hFamily := Submission.variation_jacobian_family
  have hParam := Submission.variation_param_integral_deriv
  have hTangent := Submission.simon_submanifold_tangent_basics
  -- Both formulas follow from one statement for a deformation of class `C²`; class `C³` adds the
  -- second variation.
  suffices H : ∀ (n ℓ : ℕ) (M U K : Set (Rn (n + ℓ))) (φ : ℝ → Rn (n + ℓ) → Rn (n + ℓ)),
      Chapter02.IsSimonSubmanifold (E := Rn n) 1 M →
      (∀ K', IsCompact K' → K' ⊆ U → μHE[n] (K' ∩ M) < ⊤) → IsAdmissibleDeformation 2 U K φ →
      HasDerivAt (deformedArea n M K φ)
          (∫ y in M, tangentialDivergence M (initialVelocity φ) y ∂μHE[n]) 0 ∧
        (IsAdmissibleDeformation 3 U K φ →
          (∀ᶠ t in 𝓝 0, DifferentiableAt ℝ (deformedArea n M K φ) t) ∧
            HasDerivAt (deriv (deformedArea n M K φ))
              (∫ y in M, secondVariationIntegrand M φ y ∂μHE[n]) 0) by
    refine ⟨fun n ℓ M U K φ hM _ _ hfin hφ ↦ (H n ℓ M U K φ hM hfin hφ).1,
      fun n ℓ M U K φ hM _ _ hfin hφ ↦ (H n ℓ M U K φ hM hfin ?_).2 hφ⟩
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := hφ
    exact ⟨h₁, h₂, h₃, h₄.of_le (by norm_num), h₅, h₆, h₇⟩
  intro n ℓ M U K φ hM hfin hφ
  obtain ⟨hUo, hKc, hKU, hΦ, -, -, hφbij⟩ := id hφ
  obtain ⟨hF2, hF3, hFV⟩ := hFamily (n + ℓ) U K φ
  obtain ⟨hMmeas, hPcont⟩ := hTangent.2 n (n + ℓ) 1 M hM
  -- Step 1: `S = M ∩ K` is a Borel set of finite measure.
  have hS : MeasurableSet (M ∩ K) := hMmeas.inter hKc.measurableSet
  have hμS : μHE[n] (M ∩ K) < ⊤ := by
    rw [inter_comm]
    exact hfin K hKc hKU
  -- Step 2: the family Jacobian `g` and `e y = (y, P_y)`, which maps `S` into the compact set
  -- `C = K × {P : ‖P‖ ≤ 1, P ∘ P = P}`.
  set g : ℝ × (Rn (n + ℓ) × (Rn (n + ℓ) →L[ℝ] Rn (n + ℓ))) → ℝ := fun p ↦
    Real.sqrt ((1 - p.2.2 + p.2.2 ∘L ContinuousLinearMap.adjoint (fderiv ℝ (φ p.1) p.2.1) ∘L
      fderiv ℝ (φ p.1) p.2.1 ∘L p.2.2).det)
  set e : Rn (n + ℓ) → Rn (n + ℓ) × (Rn (n + ℓ) →L[ℝ] Rn (n + ℓ)) :=
    fun y ↦ (y, tangentProjection M y)
  set C : Set (Rn (n + ℓ) × (Rn (n + ℓ) →L[ℝ] Rn (n + ℓ))) :=
    K ×ˢ (closedBall 0 1 ∩ {P | P ∘L P = P})
  have hC : IsCompact C :=
    hKc.prod ((isCompact_closedBall 0 1).inter_right
      (isClosed_eq (continuous_id.clm_comp continuous_id) continuous_id))
  have heC : ∀ z ∈ M ∩ K, e z ∈ C := fun z hz ↦
    ⟨hz.2, mem_closedBall_zero_iff.mpr (Submodule.starProjection_norm_le _),
      (Submodule.isIdempotentElem_starProjection _).eq⟩
  have hem : AEStronglyMeasurable e (μHE[n].restrict (M ∩ K)) :=
    (continuousOn_id.prodMk (hPcont.mono inter_subset_left)).aestronglyMeasurable hS
  have hP := hParam (Rn (n + ℓ)) (Rn (n + ℓ) × (Rn (n + ℓ) →L[ℝ] Rn (n + ℓ))) μHE[n] (M ∩ K) C e g
    hS hμS hC heC hem
  have hg1 : ∀ x ∈ C, ContDiffAt ℝ 1 g (0, x) := fun x hx ↦
    (hF2 hφ).1 x.1 (hKU hx.1) x.2 hx.2.2
  obtain ⟨hint, hderiv⟩ := hP.1 hg1
  -- Step 3: area formula, `Hⁿ(φ_t(S)) = ∫_S g(t, e y) dHⁿ(y)` for `|t| < 1`.
  have harea : ∀ t ∈ Ioo (-1 : ℝ) 1,
      μHE[n] (φ t '' (M ∩ K)) = ∫⁻ y in M ∩ K, ENNReal.ofReal (g (t, e y)) ∂μHE[n] := by
    intro t ht
    have hT : ∀ (V : Set (Rn n)) (W : Set (Rn (n + ℓ))) (ψ : Rn n → Rn (n + ℓ)),
        Chapter02.IsSimonLocalRepresentation 1 M V W ψ →
          ∀ x ∈ V, tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap :=
      fun V W ψ hψ ↦ hTangent.1 n (n + ℓ) 1 M V W ψ le_rfl hψ
    have hdiff : ∀ y ∈ M ∩ K, DifferentiableAt ℝ (φ t) y := by
      intro y hy
      have hΦy : DifferentiableAt ℝ (fun p : ℝ × Rn (n + ℓ) ↦ φ p.1 p.2) (t, y) :=
        (hΦ.contDiffAt ((isOpen_Ioo.prod hUo).mem_nhds ⟨ht, hKU hy.2⟩)).differentiableAt
          (by norm_num)
      exact hΦy.comp y ((differentiableAt_const t).prodMk differentiableAt_id)
    rw [hImage n (n + ℓ) (n + ℓ) M (M ∩ K) (φ t) hM hT hS inter_subset_left hdiff
      (fun y hy ↦ ((hφbij t ht).2 y (hKU hy.2)).1)
      (InjOn.mono (fun y hy ↦ hKU hy.2) (hφbij t ht).1.injOn)]
    refine lintegral_congr fun y ↦ ?_
    rw [hGram]
    rfl
  -- Hence `t ↦ Hⁿ(φ_t(S))` agrees near `0` with `t ↦ ∫_S g(t, e y) dHⁿ(y)`.
  have heq : deformedArea n M K φ =ᶠ[𝓝 0] fun t ↦ ∫ z in M ∩ K, g (t, e z) ∂μHE[n] := by
    filter_upwards [hint, Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) one_pos] with t hti ht
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun z ↦ Real.sqrt_nonneg _)
      hti.aestronglyMeasurable, ← harea t ht]
    rfl
  -- Step 4: first variation; the integrand vanishes off `K`, so `∫_S = ∫_M`.
  have hval : ∫ z in M ∩ K, deriv (fun t ↦ g (t, e z)) 0 ∂μHE[n] =
      ∫ y in M, tangentialDivergence M (initialVelocity φ) y ∂μHE[n] := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hMmeas inter_subset_left
      fun y hy ↦ (hFV 2 hφ M y fun hyK ↦ hy.2 ⟨hy.1, hyK⟩).1]
    exact setIntegral_congr_fun hS fun z hz ↦ ((hF2 hφ).2 M z (hKU hz.2)).deriv
  refine ⟨hval ▸ hderiv.congr_of_eventuallyEq heq, fun hφ3 ↦ ?_⟩
  -- Step 5: second variation (class `C³`).
  have hg2 : ∀ x ∈ C, ContDiffAt ℝ 2 g (0, x) := fun x hx ↦
    (hF3 hφ3).1 x.1 (hKU hx.1) x.2 hx.2.2
  obtain ⟨hderivs, hderiv2⟩ := hP.2 hg2
  have hev : ∀ᶠ t in 𝓝 0, HasDerivAt (deformedArea n M K φ)
      (∫ z in M ∩ K, deriv (fun s ↦ g (s, e z)) t ∂μHE[n]) t := by
    filter_upwards [hderivs, heq.eventuallyEq_nhds] with t ht hteq
    exact ht.congr_of_eventuallyEq hteq
  have hval2 : ∫ z in M ∩ K, deriv (fun t ↦ deriv (fun s ↦ g (s, e z)) t) 0 ∂μHE[n] =
      ∫ y in M, secondVariationIntegrand M φ y ∂μHE[n] := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hMmeas inter_subset_left
      fun y hy ↦ (hFV 3 hφ3 M y fun hyK ↦ hy.2 ⟨hy.1, hyK⟩).2]
    exact setIntegral_congr_fun hS fun z hz ↦ ((hF3 hφ3).2 M z (hKU hz.2)).deriv
  exact ⟨hev.mono fun t ht ↦ ht.differentiableAt,
    hval2 ▸ hderiv2.congr_of_eventuallyEq (hev.mono fun t ht ↦ ht.deriv)⟩

/-- **Simon Ch. 2, Lemma 5.5(2) and Lemma 5.11 (pp. 63–65).** If `Ū ∩ M` is compact, a `C²`
submanifold `M` is stationary in the open set `U` iff `H ≡ 0` on `M ∩ U`. If `M` is stationary in
`U`, `(M̄ \ M) ∩ U = ∅` and a `C³` deformation has initial velocity `X` normal to `M`, the second
variation is `∫_M (∑ᵢ |(D_{τᵢ}X)^⊥|² - ∑_{i,j} (X · B(τᵢ, τⱼ))²) dHⁿ`. The two directions of
5.5(2) are `stationary_imp_mean_curvature_zero` and `mean_curvature_zero_imp_stationary`, and
Lemma 5.11 is `second_variation_stationary_of_variations`. These take as hypotheses the
tangent-space facts 4.1–4.3 (`simon_submanifold_tangent_basics`) and the first (5.3) and, for
5.11, second (5.4) variation formulas (`first_and_second_variation`). -/
theorem Submission.stationary_mean_curvature_and_stable_variation :
    StationaryIffMeanCurvatureZero ∧ SecondVariationStationary :=
  ⟨fun n ℓ M U hM hU hUM ↦
      ⟨Submission.stationary_imp_mean_curvature_zero Submission.simon_submanifold_tangent_basics
          Submission.first_and_second_variation.1 n ℓ M U hM hU,
        Submission.mean_curvature_zero_imp_stationary Submission.simon_submanifold_tangent_basics
          Submission.first_and_second_variation.1 n ℓ M U hM hU hUM⟩,
    Submission.second_variation_stationary_of_variations Submission.simon_submanifold_tangent_basics
      Submission.first_and_second_variation.1 Submission.first_and_second_variation.2⟩
/-- **Simon Ch. 2, 6.3 and 6.6 (pp. 66–67), co-area formula** (Step 5 of the supplied proof).
`Submission.coarea_formula_of_measurable` is the formula for Borel `g`. For `g` a.e.-measurable
for `Hⁿ⌊M`, take a Borel `g₀` with `g = g₀` `Hⁿ⌊M`-a.e. and a Borel `Hⁿ⌊M`-null set
`Z ⊇ {g ≠ g₀}`. The formula for `1_Z` has left side `0`, so `Hᵏ(M ∩ f⁻¹{y} ∩ Z) = 0` for
`Lᵐ`-a.e. `y`; for such `y` the fibre integrals of `g` and `g₀` agree, and both conclusions
transfer from `g₀` to `g`. -/
theorem Submission.coarea_formula_theorem : CoareaFormula := by
  intro N m k M U f g _ hM hU hMU hf hg
  -- Tangent spaces of Simon charts and Borel measurability of `M` (sibling `submanifold_tangent`).
  have hT : ∀ (V : Set (Rn (m + k))) (W : Set (Rn N)) (ψ : Rn (m + k) → Rn N),
      Chapter02.IsSimonLocalRepresentation 1 M V W ψ → ∀ x ∈ V,
        tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap :=
    fun V W ψ ↦ Submission.simon_submanifold_tangent_basics.1 (m + k) N 1 M V W ψ le_rfl
  have hMmeas : MeasurableSet M :=
    (Submission.simon_submanifold_tangent_basics.2 (m + k) N 1 M hM).1
  -- A Borel representative `g₀` of `g` and a Borel `Hⁿ⌊M`-null set `Z ⊇ {g ≠ g₀}`.
  obtain ⟨g₀, hg₀, hgg₀⟩ := hg
  obtain ⟨Z, hgZ, hZ, hZnull⟩ := exists_measurable_superset_of_null (ae_iff.1 hgg₀)
  -- The formula for `1_Z` has left side `0`, so a.e. fibre meets `Z` in an `Hᵏ`-null set.
  obtain ⟨hZae, hZform⟩ := Submission.coarea_formula_of_measurable N m k M U f (Z.indicator 1)
    hM hU hMU hf hT hMmeas (measurable_one.indicator hZ)
  have hZlhs :
      ∫⁻ x in M, Z.indicator 1 x * ENNReal.ofReal (coareaJacobian M f x) ∂μHE[m + k] = 0 := by
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hZnull] with x hx
    simp [hx]
  rw [hZlhs, eq_comm, lintegral_eq_zero_iff' hZae] at hZform
  have hfib : ∀ᵐ y ∂volume,
      ∫⁻ x in M ∩ f ⁻¹' {y}, g₀ x ∂μHE[k] = ∫⁻ x in M ∩ f ⁻¹' {y}, g x ∂μHE[k] := by
    filter_upwards [hZform] with y hy
    have hyZ : μHE[k].restrict (M ∩ f ⁻¹' {y}) Z = 0 := by
      rw [← lintegral_indicator_one hZ]
      exact hy
    exact lintegral_congr_ae (ae_iff.2 (measure_mono_null (fun x hx ↦ hgZ (Ne.symm hx)) hyZ))
  -- Both conclusions for the Borel representative `g₀` transfer to `g`.
  obtain ⟨hmeas₀, hform₀⟩ := Submission.coarea_formula_of_measurable N m k M U f g₀
    hM hU hMU hf hT hMmeas hg₀
  refine ⟨hmeas₀.congr hfib, ?_⟩
  calc ∫⁻ x in M, g x * ENNReal.ofReal (coareaJacobian M f x) ∂μHE[m + k]
      = ∫⁻ x in M, g₀ x * ENNReal.ofReal (coareaJacobian M f x) ∂μHE[m + k] :=
        lintegral_congr_ae (hgg₀.mono fun x hx ↦ by simp only [hx])
    _ = ∫⁻ y, ∫⁻ x in M ∩ f ⁻¹' {y}, g₀ x ∂μHE[k] ∂volume := hform₀
    _ = ∫⁻ y, ∫⁻ x in M ∩ f ⁻¹' {y}, g x ∂μHE[k] ∂volume := lintegral_congr_ae hfib

/-- **Simon Ch. 2, Theorem 6.4 (p. 67), `C¹` Sard-type theorem**, assembled from its children.
`simon_submanifold_tangent_basics` makes `M` Borel with `x ↦ P_x` continuous on `M` and identifies
`T_{ψ x} M` with the range of `Dψ(x)` in every chart `ψ`. Then `J*f` is continuous on `M` and the
critical part of each fiber is relatively closed (`c1_sard_coarea_jacobian_continuousOn`);
`J*f(x) = 0` iff `rank df_x < m` (`c1_sard_coarea_jacobian_eq_zero_iff`); the co-area formula with
`g = 1_{M ∩ {J*f = 0}}` makes almost every critical fiber `Hᵏ`-null
(`c1_sard_critical_fibers_null`); and the implicit function theorem in charts makes the regular part
of every fiber a `k`-dimensional `C¹` submanifold (`c1_sard_regular_fiber_submanifold`). -/
theorem Submission.c1_sard_theorem : C1Sard := by
  intro N m k M U f hk hM hU hMU hf
  obtain ⟨htan, hbasic⟩ := Submission.simon_submanifold_tangent_basics
  obtain ⟨hMmeas, hP⟩ := hbasic (m + k) N 1 M hM
  obtain ⟨hJ, hclosed⟩ :=
    Submission.c1_sard_coarea_jacobian_continuousOn N m M U f hU hMU hf hP
  refine ⟨?_, ?_, fun y ↦ ⟨hclosed y, ?_⟩⟩
  · exact sep_ext_iff.mpr fun x _ ↦ Submission.c1_sard_coarea_jacobian_eq_zero_iff N m M f x
  · exact Submission.c1_sard_critical_fibers_null Submission.coarea_formula_theorem N m k M U f
      hk hM hU hMU hf hMmeas hJ
  · exact Submission.c1_sard_regular_fiber_submanifold N m k M U f hM hU hMU hf
      (fun V W ψ hψ x hx ↦ htan (m + k) N 1 M V W ψ le_rfl hψ x hx) hJ y

end GMT.Ch02
