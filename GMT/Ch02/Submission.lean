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

/-- The frozen Chapter 2 contract: the conjunction of all headline results. -/
theorem main_theorem : LipschitzExtension ∧ Rademacher ∧ C1Approximation ∧ WhitneyExtension ∧ LipschitzImageHausdorff ∧ EilenbergInequality ∧ BVCompactness ∧ BVPoincare ∧ BVExtensionEstimate ∧ AreaFormula ∧ FirstVariation ∧ SecondVariation ∧ StationaryIffMeanCurvatureZero ∧ SecondVariationStationary ∧ CoareaFormula ∧ C1Sard := by sorry

end GMT.Ch02


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
