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

/-- The frozen Chapter 2 contract: the conjunction of all headline results. -/
theorem main_theorem : LipschitzExtension ∧ Rademacher ∧ C1Approximation ∧ WhitneyExtension ∧ LipschitzImageHausdorff ∧ EilenbergInequality ∧ BVCompactness ∧ BVPoincare ∧ BVExtensionEstimate ∧ AreaFormula ∧ FirstVariation ∧ SecondVariation ∧ StationaryIffMeanCurvatureZero ∧ SecondVariationStationary ∧ CoareaFormula ∧ C1Sard := by sorry

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

end GMT.Ch02
