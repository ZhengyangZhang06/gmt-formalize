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

/-- The frozen Chapter 2 contract: the conjunction of all headline results. -/
theorem main_theorem : LipschitzExtension ∧ Rademacher ∧ C1Approximation ∧ WhitneyExtension ∧ LipschitzImageHausdorff ∧ EilenbergInequality ∧ BVCompactness ∧ BVPoincare ∧ BVExtensionEstimate ∧ AreaFormula ∧ FirstVariation ∧ SecondVariation ∧ StationaryIffMeanCurvatureZero ∧ SecondVariationStationary ∧ CoareaFormula ∧ C1Sard := by sorry

end GMT.Ch02
