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

/-- The frozen Chapter 2 contract: the conjunction of all headline results. -/
theorem main_theorem : LipschitzExtension ∧ Rademacher ∧ C1Approximation ∧ WhitneyExtension ∧ LipschitzImageHausdorff ∧ EilenbergInequality ∧ BVCompactness ∧ BVPoincare ∧ BVExtensionEstimate ∧ AreaFormula ∧ FirstVariation ∧ SecondVariation ∧ StationaryIffMeanCurvatureZero ∧ SecondVariationStationary ∧ CoareaFormula ∧ C1Sard := by sorry

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

end GMT.Ch02
