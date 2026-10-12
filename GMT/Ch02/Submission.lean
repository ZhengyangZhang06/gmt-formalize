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

/-- The frozen Chapter 2 contract: the conjunction of all headline results. -/
theorem main_theorem : LipschitzExtension ∧ Rademacher ∧ C1Approximation ∧ WhitneyExtension ∧ LipschitzImageHausdorff ∧ EilenbergInequality ∧ BVCompactness ∧ BVPoincare ∧ BVExtensionEstimate ∧ AreaFormula ∧ FirstVariation ∧ SecondVariation ∧ StationaryIffMeanCurvatureZero ∧ SecondVariationStationary ∧ CoareaFormula ∧ C1Sard := by sorry

end GMT.Ch02
