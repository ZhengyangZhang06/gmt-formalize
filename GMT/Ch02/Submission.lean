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

/-- The frozen Chapter 2 contract: the conjunction of all headline results. -/
theorem main_theorem : LipschitzExtension ∧ Rademacher ∧ C1Approximation ∧ WhitneyExtension ∧ LipschitzImageHausdorff ∧ EilenbergInequality ∧ BVCompactness ∧ BVPoincare ∧ BVExtensionEstimate ∧ AreaFormula ∧ FirstVariation ∧ SecondVariation ∧ StationaryIffMeanCurvatureZero ∧ SecondVariationStationary ∧ CoareaFormula ∧ C1Sard := by sorry

end GMT.Ch02
