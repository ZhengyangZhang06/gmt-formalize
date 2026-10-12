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

/-- The frozen Chapter 2 contract: the conjunction of all headline results. -/
theorem main_theorem : LipschitzExtension ∧ Rademacher ∧ C1Approximation ∧ WhitneyExtension ∧ LipschitzImageHausdorff ∧ EilenbergInequality ∧ BVCompactness ∧ BVPoincare ∧ BVExtensionEstimate ∧ AreaFormula ∧ FirstVariation ∧ SecondVariation ∧ StationaryIffMeanCurvatureZero ∧ SecondVariationStationary ∧ CoareaFormula ∧ C1Sard := by sorry

end GMT.Ch02
