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

/-- The frozen Chapter 2 contract: the conjunction of all headline results. -/
theorem main_theorem : LipschitzExtension ∧ Rademacher ∧ C1Approximation ∧ WhitneyExtension ∧ LipschitzImageHausdorff ∧ EilenbergInequality ∧ BVCompactness ∧ BVPoincare ∧ BVExtensionEstimate ∧ AreaFormula ∧ FirstVariation ∧ SecondVariation ∧ StationaryIffMeanCurvatureZero ∧ SecondVariationStationary ∧ CoareaFormula ∧ C1Sard := by sorry

end GMT.Ch02
