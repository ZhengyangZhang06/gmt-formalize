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

/-- The frozen Chapter 2 contract: the conjunction of all headline results. -/
theorem main_theorem : LipschitzExtension ∧ Rademacher ∧ C1Approximation ∧ WhitneyExtension ∧ LipschitzImageHausdorff ∧ EilenbergInequality ∧ BVCompactness ∧ BVPoincare ∧ BVExtensionEstimate ∧ AreaFormula ∧ FirstVariation ∧ SecondVariation ∧ StationaryIffMeanCurvatureZero ∧ SecondVariationStationary ∧ CoareaFormula ∧ C1Sard := by sorry

end GMT.Ch02
