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

/-- The frozen Chapter 2 contract: the conjunction of all headline results. -/
theorem main_theorem : LipschitzExtension ∧ Rademacher ∧ C1Approximation ∧ WhitneyExtension ∧ LipschitzImageHausdorff ∧ EilenbergInequality ∧ BVCompactness ∧ BVPoincare ∧ BVExtensionEstimate ∧ AreaFormula ∧ FirstVariation ∧ SecondVariation ∧ StationaryIffMeanCurvatureZero ∧ SecondVariationStationary ∧ CoareaFormula ∧ C1Sard := by sorry

end GMT.Ch02
