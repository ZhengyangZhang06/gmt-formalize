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

/-- The frozen Chapter 2 contract: the conjunction of all headline results. -/
theorem main_theorem : LipschitzExtension ∧ Rademacher ∧ C1Approximation ∧ WhitneyExtension ∧ LipschitzImageHausdorff ∧ EilenbergInequality ∧ BVCompactness ∧ BVPoincare ∧ BVExtensionEstimate ∧ AreaFormula ∧ FirstVariation ∧ SecondVariation ∧ StationaryIffMeanCurvatureZero ∧ SecondVariationStationary ∧ CoareaFormula ∧ C1Sard := by sorry

end GMT.Ch02
