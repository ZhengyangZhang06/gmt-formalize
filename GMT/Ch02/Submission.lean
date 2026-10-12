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

/-- **Derivative of the Gram map.** If `ψ : ℝⁿ → ℝᴺ` is `C²` on an open `V`, then
`G(x) = Dψ(x)* ∘ Dψ(x)` is `C¹` on `V` and `DG(x)[v] = Dψ(x)* ∘ D²ψ(x)[v] + (D²ψ(x)[v])* ∘ Dψ(x)`,
with `L*` the adjoint. Over `ℝ` the adjoint is a continuous linear map `adjR`, so
`x ↦ Dψ(x)* = adjR ∘ Dψ` is `C¹` on `V` with derivative `adjR ∘ D²ψ(x)` (chain rule). Both claims
then follow from the regularity (`ContDiffOn.clm_comp`) and the product rule
(`HasFDerivAt.clm_comp`) of the continuous bilinear composition `(B, C) ↦ B ∘L C`. -/
theorem Submission.adjoint_comp_fderiv_contDiffOn_fderiv_eq_add : ∀ (n N : ℕ) (V : Set (Rn n)) (ψ : Rn n → Rn N), IsOpen V → ContDiffOn ℝ 2 ψ V → ContDiffOn ℝ 1 (fun x ↦ ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x) V ∧ ∀ x ∈ V, ∀ v : Rn n, fderiv ℝ (fun x ↦ ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x) x v = ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ (fderiv ℝ ψ) x v + ContinuousLinearMap.adjoint (fderiv ℝ (fderiv ℝ ψ) x v) ∘L fderiv ℝ ψ x := by
  intro n N V ψ hV hψ
  -- Step 1: the adjoint over `ℝ` as a continuous `ℝ`-linear map `adjR`; `adjR L = L*` by `rfl`.
  let adjR : (Rn n →L[ℝ] Rn N) →L[ℝ] (Rn N →L[ℝ] Rn n) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Rn n) (F := Rn N)).toContinuousLinearEquiv.toContinuousLinearMap
  -- Step 2: `A = Dψ` is `C¹` on `V` (`1 + 1 ≤ 2`).
  have hA : ContDiffOn ℝ 1 (fderiv ℝ ψ) V := hψ.fderiv_of_isOpen hV (by norm_num)
  -- Step 3: `x ↦ A(x)* = adjR ∘ A` is `C¹` on `V`.
  have hAd : ContDiffOn ℝ 1 (fun x ↦ ContinuousLinearMap.adjoint (fderiv ℝ ψ x)) V :=
    adjR.contDiff.comp_contDiffOn hA
  -- Step 4 (first conjunct): `G = A* ∘L A` is `C¹` on `V`.
  refine ⟨hAd.clm_comp hA, fun x hx v ↦ ?_⟩
  -- Step 2 at `x ∈ V`: `A` has derivative `D²ψ(x)` at `x`, since `V` is a neighbourhood of `x`.
  have hAx : HasFDerivAt (fderiv ℝ ψ) (fderiv ℝ (fderiv ℝ ψ) x) x :=
    ((hA.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds hx)).hasFDerivAt
  -- Step 3 at `x` (chain rule): `x ↦ A(x)*` has derivative `adjR ∘L D²ψ(x)` at `x`.
  have hAdx : HasFDerivAt (fun x ↦ ContinuousLinearMap.adjoint (fderiv ℝ ψ x))
      (adjR ∘L fderiv ℝ (fderiv ℝ ψ) x) x :=
    adjR.hasFDerivAt.comp x hAx
  -- Step 5 (second conjunct): by the product rule and uniqueness of the derivative,
  -- `DG(x)[v] = A(x)* ∘L D²ψ(x)[v] + adjR (D²ψ(x)[v]) ∘L A(x)`, and `adjR L = L*` by `rfl`.
  rw [(hAdx.clm_comp hAx).fderiv]
  rfl
/-- **Trace swap under a symmetric weight.** For `A, S : ℝⁿ → ℝᴺ` and a symmetric `P : ℝⁿ → ℝⁿ`
(`⟨P v, w⟩ = ⟨v, P w⟩`), `tr(P ∘ S* ∘ A) = tr(P ∘ A* ∘ S)`, with `L*` the adjoint. By cyclicity,
`tr(P ∘ A* ∘ S) = tr((A* ∘ S) ∘ P)`. Both traces are then expanded in the standard orthonormal
basis `(e_l)` of `ℝⁿ`, and the terms agree:
`⟨e, P S* A e⟩ = ⟨P e, S* A e⟩ = ⟨S P e, A e⟩ = ⟨A* S P e, e⟩ = ⟨e, A* S P e⟩`. -/
theorem Submission.trace_comp_adjoint_comp_swap_of_symm : ∀ (n N : ℕ) (A S : Rn n →L[ℝ] Rn N) (P : Rn n →L[ℝ] Rn n), (∀ v w : Rn n, inner ℝ (P v) w = inner ℝ v (P w)) → LinearMap.trace ℝ (Rn n) (P ∘L ContinuousLinearMap.adjoint S ∘L A).toLinearMap = LinearMap.trace ℝ (Rn n) (P ∘L ContinuousLinearMap.adjoint A ∘L S).toLinearMap := by
  intro n N A S P hP
  -- Step 1 (cyclicity): `tr(P ∘ A* ∘ S) = tr((A* ∘ S) ∘ P)`.
  have hcyc : LinearMap.trace ℝ (Rn n) (P ∘L ContinuousLinearMap.adjoint A ∘L S).toLinearMap =
      LinearMap.trace ℝ (Rn n)
        ((ContinuousLinearMap.adjoint A ∘L S).toLinearMap ∘ₗ P.toLinearMap) :=
    LinearMap.trace_comp_comm' (ContinuousLinearMap.adjoint A ∘L S).toLinearMap P.toLinearMap
  -- Step 2: expand both traces in the standard orthonormal basis `(e_l)` and compare termwise.
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  rw [hcyc, LinearMap.trace_eq_sum_inner _ e, LinearMap.trace_eq_sum_inner _ e]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  -- Step 3: `⟨e, P S* A e⟩ = ⟨P e, S* A e⟩ = ⟨S P e, A e⟩ = ⟨A* S P e, e⟩ = ⟨e, A* S P e⟩`.
  calc inner ℝ (e l) ((P ∘L ContinuousLinearMap.adjoint S ∘L A).toLinearMap (e l))
      = inner ℝ (e l) (P (ContinuousLinearMap.adjoint S (A (e l)))) := rfl
    _ = inner ℝ (P (e l)) (ContinuousLinearMap.adjoint S (A (e l))) := (hP _ _).symm
    _ = inner ℝ (S (P (e l))) (A (e l)) := ContinuousLinearMap.adjoint_inner_right S _ _
    _ = inner ℝ (ContinuousLinearMap.adjoint A (S (P (e l)))) (e l) :=
      (ContinuousLinearMap.adjoint_inner_left A _ _).symm
    _ = inner ℝ (e l) (ContinuousLinearMap.adjoint A (S (P (e l)))) := real_inner_comm _ _
    _ = inner ℝ (e l)
        (((ContinuousLinearMap.adjoint A ∘L S).toLinearMap ∘ₗ P.toLinearMap) (e l)) := rfl
/-- **Gram operator of an injective linear map and the range projection.** For an injective
`A : ℝⁿ →L[ℝ] ℝᴺ` with `K = range A`, the Gram operator `G = A* ∘L A` is a unit of `ℝⁿ →L[ℝ] ℝⁿ`,
its ring inverse `G⁻¹` is symmetric, and `K.starProjection = A ∘L G⁻¹ ∘L A*`. `G` is injective
because `ker (A* ∘L A) = ker A` (`ContinuousLinearMap.adjoint_comp_self_injective_iff`), so in
finite dimension it is a continuous linear automorphism. Then
`⟪G⁻¹v, w⟫ = ⟪G⁻¹v, G G⁻¹w⟫ = ⟪A G⁻¹v, A G⁻¹w⟫ = ⟪G G⁻¹v, G⁻¹w⟫ = ⟪v, G⁻¹w⟫`, and
`A G⁻¹ A* z ∈ range A` with `⟪z - A G⁻¹ A* z, A c⟫ = ⟪A* z - G G⁻¹ A* z, c⟫ = 0`, which
characterizes the orthogonal projection (`Submodule.eq_starProjection_of_mem_of_inner_eq_zero`). -/
theorem Submission.gram_inverse_range_starProjection : ∀ (n N : ℕ) (K : Submodule ℝ (Rn N)) (A : Rn n →L[ℝ] Rn N), Function.Injective A → K = LinearMap.range A.toLinearMap → IsUnit (ContinuousLinearMap.adjoint A ∘L A) ∧ (∀ v w : Rn n, inner ℝ (Ring.inverse (ContinuousLinearMap.adjoint A ∘L A) v) w = inner ℝ v (Ring.inverse (ContinuousLinearMap.adjoint A ∘L A) w)) ∧ K.starProjection = A ∘L Ring.inverse (ContinuousLinearMap.adjoint A ∘L A) ∘L ContinuousLinearMap.adjoint A := by
  intro n N K A hA hK
  subst hK
  set G := ContinuousLinearMap.adjoint A ∘L A
  -- Step 2: `G` is injective, since `ker (A* ∘L A) = ker A = ⊥`.
  have hGinj : Function.Injective G := (ContinuousLinearMap.adjoint_comp_self_injective_iff A).2 hA
  -- Step 3: an injective endomorphism of `ℝⁿ` is a continuous linear automorphism, so `G` is a unit.
  have hunit : IsUnit G := by
    let e : Rn n ≃L[ℝ] Rn n :=
      (LinearEquiv.ofInjectiveEndo (G : Rn n →ₗ[ℝ] Rn n) hGinj).toContinuousLinearEquiv
    exact ⟨e.toUnit, by ext x; rfl⟩
  have hGG : ∀ x, G (Ring.inverse G x) = x := fun x => by
    rw [← mul_apply_eq_comp, Ring.mul_inverse_cancel G hunit, one_apply_eq_self]
  -- Step 1: `⟪G x, y⟫ = ⟪A x, A y⟫ = ⟪x, G y⟫`.
  have hl : ∀ x y, inner ℝ (G x) y = inner ℝ (A x) (A y) := fun x y =>
    ContinuousLinearMap.adjoint_inner_left A y (A x)
  have hr : ∀ x y, inner ℝ x (G y) = inner ℝ (A x) (A y) := fun x y =>
    ContinuousLinearMap.adjoint_inner_right A x (A y)
  refine ⟨hunit, fun v w => ?_, ?_⟩
  -- Step 4: `G⁻¹` is symmetric.
  · calc inner ℝ (Ring.inverse G v) w = inner ℝ (Ring.inverse G v) (G (Ring.inverse G w)) := by
          rw [hGG]
      _ = inner ℝ (G (Ring.inverse G v)) (Ring.inverse G w) := by rw [hl, hr]
      _ = inner ℝ v (Ring.inverse G w) := by rw [hGG]
  -- Step 7: `A G⁻¹ A* z ∈ range A` and `z - A G⁻¹ A* z` is orthogonal to `range A`.
  · ext1 z
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (LinearMap.mem_range_self _ _) ?_
    rintro _ ⟨c, rfl⟩
    rw [ContinuousLinearMap.coe_coe, ← ContinuousLinearMap.adjoint_inner_left, map_sub]
    have h : ContinuousLinearMap.adjoint A ((A ∘L Ring.inverse G ∘L ContinuousLinearMap.adjoint A) z) =
        ContinuousLinearMap.adjoint A z := hGG _
    rw [h, sub_self, inner_zero_left]

/-- **Tangential divergence in a chart.** If `T_y M = range A` for an injective `A : ℝⁿ → ℝᴺ`, then
`div_M Y(y) = tr(G⁻¹ A* L A)`, a trace on `ℝⁿ`, where `L = DY(y)`, `A*` is the adjoint and `G = A* A`;
no differentiability of `Y` is needed. Write `T = T_y M`, `q : ℝᴺ → T` for the orthogonal projection
and `ι : T → ℝᴺ` for the inclusion. In the orthonormal basis `τᵢ` of `T` defining the frame,
`tr_T(q L ι) = ∑ᵢ ⟨τᵢ, q L τᵢ⟩ = ∑ᵢ ⟨τᵢ, L τᵢ⟩ = div_M Y(y)`, and cyclicity turns this into
`tr_{ℝᴺ}(L P_T)` with `P_T = ι q`. The Gram projection formula `P_T = A G⁻¹ A*` and cyclicity once
more give `tr_{ℝᴺ}((L A)(G⁻¹ A*)) = tr_{ℝⁿ}((G⁻¹ A*)(L A))`. -/
theorem Submission.chart_tangentialDivergence_eq_gram_trace : ∀ (n N : ℕ) (M : Set (Rn N)) (y : Rn N) (A : Rn n →L[ℝ] Rn N) (Y : Rn N → Rn N), Function.Injective A → tangentSpace M y = LinearMap.range A.toLinearMap → tangentialDivergence M Y y = LinearMap.trace ℝ (Rn n) (Ring.inverse (ContinuousLinearMap.adjoint A ∘L A) ∘L ContinuousLinearMap.adjoint A ∘L fderiv ℝ Y y ∘L A).toLinearMap := by
  intro n N M y A Y hA hT
  -- Steps 1–3: `div_M Y(y) = tr_{ℝᴺ}(L ∘ P_T)` with `T = T_y M`, `L = DY(y)` and `P_T = ι ∘ q`.
  have hdiv : tangentialDivergence M Y y = LinearMap.trace ℝ (Rn N)
      (fderiv ℝ Y y ∘L (tangentSpace M y).starProjection).toLinearMap := by
    -- Steps 1–2: expand `tr_T(q ∘ L ∘ ι)` in the orthonormal basis `b` of `T` that defines the
    -- frame `τᵢ = b i`; since `b i ∈ T`, `⟨b i, q (L (b i))⟩_T = ⟨b i, L (b i)⟩`.
    have hsum : LinearMap.trace ℝ (tangentSpace M y)
        ((tangentSpace M y).orthogonalProjectionOnto.toLinearMap ∘ₗ
          ((fderiv ℝ Y y).toLinearMap ∘ₗ (tangentSpace M y).subtype)) =
        tangentialDivergence M Y y := by
      unfold tangentialDivergence
      rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ (tangentSpace M y))]
      exact Finset.sum_congr rfl fun i _ ↦
        Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left _ _
    -- Step 3 (cyclicity): `tr_T(q ∘ (L ∘ ι)) = tr_{ℝᴺ}((L ∘ ι) ∘ q)`, and `ι ∘ q = P_T` by the
    -- definition of `starProjection`.
    rw [← hsum]
    exact LinearMap.trace_comp_comm' _ _
  -- Step 4: `P_T = A G⁻¹ A*` by the Gram projection formula (`T = range A`, `A` injective).
  rw [hdiv, (Submission.gram_inverse_range_starProjection n N _ A hA hT).2.2]
  -- Step 5 (cyclicity): `tr_{ℝᴺ}((L ∘ A) ∘ (G⁻¹ ∘ A*)) = tr_{ℝⁿ}((G⁻¹ ∘ A*) ∘ (L ∘ A))`.
  exact LinearMap.trace_comp_comm'
    (Ring.inverse (ContinuousLinearMap.adjoint A ∘L A) ∘L ContinuousLinearMap.adjoint A).toLinearMap
    (fderiv ℝ Y y ∘L A).toLinearMap
/-- **Mean curvature through an injective parametrization differential** (Simon 4.27 in a chart).
Let `A : ℝⁿ → ℝᴺ` be injective with `T_y M = range A`, and let `S` be bilinear (not necessarily
symmetric) with `B_y(Aa, Ab) = S(a, b)^⊥`. With `G = A*A` and `eₗ` the standard basis of `ℝⁿ`,
`H(y) = (∑ₗ S(eₗ, G⁻¹eₗ))^⊥`. Choose `aᵢ` with `Aaᵢ = τᵢ` for the frame `τᵢ` of `T_y M`, so
`H(y) = (∑ᵢ S(aᵢ, aᵢ))^⊥`. Expanding `Ac ∈ T_y M` in the frame and using injectivity of `A` gives
`c = ∑ᵢ ⟨Aaᵢ, Ac⟩ aᵢ`; for `c = G⁻¹eₗ`, `GG⁻¹ = 1` (`gram_inverse_range_starProjection`) turns this
into `G⁻¹eₗ = ∑ᵢ ⟨aᵢ, eₗ⟩ aᵢ`. Bilinearity and `∑ₗ ⟨aᵢ, eₗ⟩ eₗ = aᵢ` give
`∑ₗ S(eₗ, G⁻¹eₗ) = ∑ᵢ S(aᵢ, aᵢ)`. -/
theorem Submission.chart_meanCurvature_eq_normalPart_gram_sum : ∀ (n N : ℕ) (M : Set (Rn N)) (y : Rn N) (A : Rn n →L[ℝ] Rn N) (S : Rn n →L[ℝ] Rn n →L[ℝ] Rn N), Function.Injective A → tangentSpace M y = LinearMap.range A.toLinearMap → (∀ a b : Rn n, secondFundamentalForm M y (A a) (A b) = normalPart M y (S a b)) → meanCurvature M y = normalPart M y (∑ l : Fin n, S (EuclideanSpace.single l 1) (Ring.inverse (ContinuousLinearMap.adjoint A ∘L A) (EuclideanSpace.single l 1))) := by
  intro n N M y A S hA hT hB
  -- Step 1: `G = A*A` is a unit (sibling `gram_projection`), so `A*(A(G⁻¹w)) = G(G⁻¹w) = w`.
  have hG := (Submission.gram_inverse_range_starProjection n N (tangentSpace M y) A hA hT).1
  have hGG : ∀ w : Rn n, ContinuousLinearMap.adjoint A
      (A (Ring.inverse (ContinuousLinearMap.adjoint A ∘L A) w)) = w :=
    fun w ↦ DFunLike.congr_fun (Ring.mul_inverse_cancel _ hG) w
  -- Steps 2–3: every frame vector `τᵢ` of `T_y M = range A` has a preimage `aᵢ`.
  have hpre : ∀ i, ∃ a : Rn n, A a = tangentFrame M y i := fun i ↦ by
    have hi : tangentFrame M y i ∈ tangentSpace M y :=
      (stdOrthonormalBasis ℝ (tangentSpace M y) i).2
    rw [hT] at hi
    exact LinearMap.mem_range.1 hi
  choose a ha using hpre
  -- Step 4: `H(y) = ∑ᵢ B(Aaᵢ, Aaᵢ) = ∑ᵢ S(aᵢ, aᵢ)^⊥ = (∑ᵢ S(aᵢ, aᵢ))^⊥`.
  have hH : meanCurvature M y = normalPart M y (∑ i, S (a i) (a i)) := by
    have hnp : normalPart M y (∑ i, S (a i) (a i)) = ∑ i, normalPart M y (S (a i) (a i)) := by
      simp only [normalPart, map_sum, Finset.sum_sub_distrib]
    rw [hnp, meanCurvature]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← ha i, hB]
  -- Step 5: reproducing formula `c = ∑ᵢ ⟨Aaᵢ, Ac⟩ aᵢ`, from the frame expansion of `Ac ∈ T_y M`.
  have hrep : ∀ c : Rn n, ∑ i, inner ℝ (A (a i)) (A c) • a i = c := by
    intro c
    apply hA
    have hc : A c ∈ tangentSpace M y := by
      rw [hT]
      exact LinearMap.mem_range_self A.toLinearMap c
    have h := congrArg Subtype.val
      ((stdOrthonormalBasis ℝ (tangentSpace M y)).sum_repr' ⟨A c, hc⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at h
    rw [map_sum]
    simp only [map_smul, ha]
    exact h
  -- Step 6: `G⁻¹eₗ = ∑ᵢ ⟨aᵢ, eₗ⟩ aᵢ`, since `⟨Aaᵢ, A(G⁻¹eₗ)⟩ = ⟨aᵢ, A*A(G⁻¹eₗ)⟩ = ⟨aᵢ, eₗ⟩`.
  have hGinv : ∀ l : Fin n, Ring.inverse (ContinuousLinearMap.adjoint A ∘L A)
      (EuclideanSpace.single l 1) = ∑ i, inner ℝ (a i) (EuclideanSpace.single l 1) • a i := by
    intro l
    refine (hrep _).symm.trans (Finset.sum_congr rfl fun i _ ↦ ?_)
    rw [← ContinuousLinearMap.adjoint_inner_right A (a i), hGG]
  -- `∑ₗ ⟨v, eₗ⟩ eₗ = v`: the expansion in the standard orthonormal basis of `ℝⁿ`.
  have hexp : ∀ v : Rn n,
      ∑ l : Fin n, inner ℝ v (EuclideanSpace.single l 1) • EuclideanSpace.single l (1 : ℝ) = v := by
    intro v
    conv_rhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr' v]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [EuclideanSpace.basisFun_apply, real_inner_comm]
  -- Step 7: `∑ₗ S(eₗ, G⁻¹eₗ) = ∑ᵢ ∑ₗ ⟨aᵢ, eₗ⟩ S(eₗ, aᵢ) = ∑ᵢ S(∑ₗ ⟨aᵢ, eₗ⟩ eₗ, aᵢ) = ∑ᵢ S(aᵢ, aᵢ)`.
  have hS : ∑ l : Fin n, S (EuclideanSpace.single l 1)
      (Ring.inverse (ContinuousLinearMap.adjoint A ∘L A) (EuclideanSpace.single l 1)) =
      ∑ i, S (a i) (a i) := by
    simp only [hGinv, map_sum, map_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    calc ∑ l : Fin n, inner ℝ (a i) (EuclideanSpace.single l 1) • S (EuclideanSpace.single l 1) (a i)
        = S (∑ l : Fin n, inner ℝ (a i) (EuclideanSpace.single l 1) •
            EuclideanSpace.single l (1 : ℝ)) (a i) := by
          simp only [map_sum, map_smul, sum_apply, smul_apply]
      _ = S (a i) (a i) := by rw [hexp]
  -- Step 8: combine Steps 4 and 7.
  rw [hH, hS]
/-- **Smoothness of the determinant on `L(ℝⁿ)`.** For every `n` and every order `k : WithTop ℕ∞`
(finite, `∞` or analytic), `T ↦ T.det` is `C^k` on `ℝⁿ →L[ℝ] ℝⁿ`. In the standard basis `eᵢ` the
Leibniz formula gives `T.det = ∑_σ sign σ * ∏ᵢ (T eᵢ)_{σ i}` (`LinearMap.det_toMatrix`,
`Matrix.det_apply`). Each entry `T ↦ (T eᵢ)_l` is continuous linear, and finite sums and products of
`C^k` functions are `C^k` (`ContDiff.sum`, `contDiff_prod`). -/
theorem Submission.contDiff_rn_continuousLinearMap_det : ∀ (n : ℕ) (k : WithTop ℕ∞), ContDiff ℝ k (fun T : Rn n →L[ℝ] Rn n ↦ T.det) := by
  intro n k
  -- Steps 1–2: the Leibniz formula in the standard basis, whose matrix entries are `(T eᵢ)_l`.
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have h : (fun T : Rn n →L[ℝ] Rn n ↦ T.det) = fun T ↦ ∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, (T (EuclideanSpace.single i (1 : ℝ))).ofLp (σ i) := by
    funext T
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b, Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ ↦ ?_
    rw [Units.smul_def, zsmul_eq_mul]
    congr 1
  rw [h]
  -- Steps 3–4: each entry is a continuous linear functional of `T`; close under `∏` and `∑`.
  refine ContDiff.sum fun σ _ ↦ contDiff_const.mul (contDiff_prod fun i _ ↦ ?_)
  exact ((EuclideanSpace.proj (σ i)).comp
    (ContinuousLinearMap.apply ℝ (Rn n) (EuclideanSpace.single i (1 : ℝ)))).contDiff
/-- **Jacobi's formula at the identity.** For `K ∈ L(ℝⁿ)`, `t ↦ det(1 + t • K)` has derivative
`trace K` at `t = 0`. With `b` the standard basis of `ℝⁿ` and `A = [K]_b`, the matrix of `1 + t • K` is
`1 + t • A`, so `det(1 + t • K) = det(1 + t • A) = 1 + trace A · t + p(t) t²` for every `t`, with the
fixed polynomial `p = (det(1 + X • A)).divX.divX` (`LinearMap.det_toMatrix`,
`Matrix.det_one_add_smul`). The right side has derivative `trace A` at `0`, and `trace A = trace K`
(`LinearMap.trace_eq_matrix_trace`). -/
theorem Submission.hasDerivAt_rn_det_one_add_smul_trace : ∀ (n : ℕ) (K : Rn n →L[ℝ] Rn n), HasDerivAt (fun t : ℝ ↦ (1 + t • K).det) (LinearMap.trace ℝ (Rn n) K.toLinearMap) 0 := by
  intro n K
  -- Step 1: the standard basis `b` of `ℝⁿ`, the matrix `A` of `K` and the fixed polynomial `p`.
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin n) (Fin n) ℝ, LinearMap.toMatrix b b K.toLinearMap = A :=
    ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : Polynomial ℝ,
      (1 + (Polynomial.X : Polynomial ℝ) • A.map Polynomial.C).det.divX.divX = p := ⟨_, rfl⟩
  -- Steps 2–3: `[1 + t • K]_b = 1 + t • A`, so `det(1 + t • K) = 1 + trace A * t + p(t) * t ^ 2`.
  have hexp : ∀ t : ℝ, (1 + t • K).det = 1 + A.trace * t + p.eval t * t ^ 2 := fun t ↦ by
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b, ContinuousLinearMap.toLinearMap_add,
      ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.toLinearMap_one, map_add, map_smul,
      LinearMap.toMatrix_one, hA, Matrix.det_one_add_smul, hp]
  -- Step 5: `t ↦ 1 + trace A * t + p(t) * t ^ 2` has derivative `trace A + 0` at `0`.
  have hlin : HasDerivAt (fun t : ℝ ↦ A.trace * t) A.trace 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul A.trace
  have hquad : HasDerivAt (fun t : ℝ ↦ p.eval t * t ^ 2) 0 0 := by
    simpa using (Polynomial.hasDerivAt p 0).fun_mul (hasDerivAt_pow 2 (0 : ℝ))
  have hg := (hlin.const_add 1).fun_add hquad
  rw [add_zero] at hg
  -- Steps 4 and 6: `trace K = trace A`, and `det(1 + t • K)` agrees with the polynomial everywhere.
  rw [LinearMap.trace_eq_matrix_trace ℝ b, hA]
  exact hg.congr_of_eventuallyEq (Filter.Eventually.of_forall hexp)

/-- **Jacobi's formula on `L(ℝⁿ)`.** `det : L(ℝⁿ) → ℝ` is `C¹`, and at a unit `T` of the ring
`L(ℝⁿ)` (multiplication is composition), `D det(T)[H] = det T · trace(T⁻¹ ∘ H)` with
`T⁻¹ = Ring.inverse T`. The first conjunct is `Submission.contDiff_rn_continuousLinearMap_det` at
order `1`. For the second, put `K = T⁻¹ ∘ H`: then `T + t • H = T ∘ (1 + t • K)`
(`Ring.mul_inverse_cancel`), so `det(T + t • H) = det T · det(1 + t • K)` (`LinearMap.det_comp`), which
has derivative `det T · trace K` at `t = 0` by `Submission.hasDerivAt_rn_det_one_add_smul_trace`. The
chain rule along `t ↦ T + t • H` and uniqueness of derivatives identify it with `D det(T)[H]`. -/
theorem Submission.continuousLinearMap_det_contDiff_fderiv_eq_mul_trace : ∀ n : ℕ, ContDiff ℝ 1 (fun T : Rn n →L[ℝ] Rn n ↦ T.det) ∧ ∀ T H : Rn n →L[ℝ] Rn n, IsUnit T → fderiv ℝ (fun T : Rn n →L[ℝ] Rn n ↦ T.det) T H = T.det * LinearMap.trace ℝ (Rn n) (Ring.inverse T ∘L H).toLinearMap := by
  intro n
  -- Step 2: `det` is `C¹`, hence differentiable at every `T`.
  have hC1 : ContDiff ℝ 1 (fun T : Rn n →L[ℝ] Rn n ↦ T.det) :=
    Submission.contDiff_rn_continuousLinearMap_det n 1
  refine ⟨hC1, fun T H hT ↦ ?_⟩
  -- Step 3: `T ∘ (1 + t • K) = T + t • H` for `K = T⁻¹ ∘ H`, since `T ∘ T⁻¹ = 1`.
  have hTK : T * (Ring.inverse T ∘L H) = H := by
    rw [← ContinuousLinearMap.mul_def, ← mul_assoc, Ring.mul_inverse_cancel T hT, one_mul]
  have hfac : ∀ t : ℝ, T * (1 + t • (Ring.inverse T ∘L H)) = T + t • H := fun t ↦ by
    rw [mul_add, mul_one, ContinuousLinearMap.mul_def T, ContinuousLinearMap.comp_smul,
      ← ContinuousLinearMap.mul_def, hTK]
  -- Steps 3–5: `det(T + t • H) = det T · det(1 + t • K)` has derivative `det T · trace K` at `0`.
  have hline : HasDerivAt (fun t : ℝ ↦ (T + t • H).det)
      (T.det * LinearMap.trace ℝ (Rn n) (Ring.inverse T ∘L H).toLinearMap) 0 := by
    have hmul : (fun t : ℝ ↦ (T + t • H).det) =
        fun t ↦ T.det * (1 + t • (Ring.inverse T ∘L H)).det :=
      funext fun t ↦ by rw [← hfac t]; exact LinearMap.det_comp _ _
    rw [hmul]
    exact (Submission.hasDerivAt_rn_det_one_add_smul_trace n (Ring.inverse T ∘L H)).const_mul T.det
  -- Step 6: chain rule along `γ t = T + t • H` (`γ 0 = T`, `γ' 0 = H`) and uniqueness.
  have hγ : HasDerivAt (fun t : ℝ ↦ T + t • H) H 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const H).const_add T
  have hchain := ((hC1.differentiable one_ne_zero) T).hasFDerivAt.comp_hasDerivAt_of_eq 0 hγ
    (show T = T + (0 : ℝ) • H by rw [zero_smul ℝ H, add_zero])
  exact hchain.unique hline

/-- **Simon Ch. 2, §5, derivative of the area Jacobian of a `C²` immersion.** Let `V ⊆ ℝⁿ` be open
and `ψ : ℝⁿ → ℝᴺ` be `C²` on `V` with injective `A(x) = Dψ(x)`, and let `G(x) = A(x)* A(x)`. Then
`J = areaJacobianAt ψ = √(det ∘ G)` is `C¹` on `V` and `DJ(x)[v] = J(x) tr(G(x)⁻¹ A(x)* S_v)`, where
`S_v = D²ψ(x)[v]`. Indeed `G` is `C¹` with `DG(x)[v] = A* S_v + S_v* A`, Jacobi's formula gives
`D(det ∘ G)(x)[v] = det G · tr(G⁻¹ DG(x)[v])`, the symmetry of `G⁻¹` turns `tr(G⁻¹ S_v* A)` into
`tr(G⁻¹ A* S_v)`, and `det G = J² > 0` because `A(x)` is injective. -/
theorem Submission.areaJacobianAt_contDiffOn_fderiv_eq_gram_trace : ∀ (n N : ℕ) (V : Set (Rn n)) (ψ : Rn n → Rn N), IsOpen V → ContDiffOn ℝ 2 ψ V → (∀ x ∈ V, Function.Injective (fderiv ℝ ψ x)) → ContDiffOn ℝ 1 (Chapter02.areaJacobianAt ψ) V ∧ ∀ x ∈ V, ∀ v : Rn n, fderiv ℝ (Chapter02.areaJacobianAt ψ) x v = Chapter02.areaJacobianAt ψ x * LinearMap.trace ℝ (Rn n) (Ring.inverse (ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x) ∘L ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ (fderiv ℝ ψ) x v).toLinearMap := by
  intro n N V ψ hV hψ hinj
  -- `G = A* A` is `C¹` on `V` with `DG(x)[v] = A* S_v + S_v* A`, and `det` is `C¹` with
  -- `D det(T)[H] = det T · tr(T⁻¹ H)` at every unit `T` (Jacobi's formula).
  obtain ⟨hGC, hGD⟩ := Submission.adjoint_comp_fderiv_contDiffOn_fderiv_eq_add n N V ψ hV hψ
  obtain ⟨hdetC, hdetD⟩ := Submission.continuousLinearMap_det_contDiff_fderiv_eq_mul_trace n
  -- Step 1: `J = √(det ∘ G)`.
  have hJ : Chapter02.areaJacobianAt ψ = fun x ↦
      Real.sqrt (ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x).det :=
    funext fun x ↦ Chapter02.areaJacobianAt_eq_sqrt_det_adjoint_comp ψ x
  -- Step 2: on `V`, `A(x)` is injective, so `J x = normDet A(x) ≠ 0` and `det G(x) = (J x)² ≠ 0`.
  have hJ0 : ∀ x ∈ V, Chapter02.areaJacobianAt ψ x ≠ 0 := fun x hx ↦ by
    rw [Chapter02.areaJacobianAt_eq_normDet]
    exact ((fderiv ℝ ψ x).toLinearMap.normDet_ne_zero_tfae.out 1 5).2 (hinj x hx)
  have hd0 : ∀ x ∈ V, (ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x).det ≠ 0 :=
    fun x hx ↦ Chapter02.areaJacobianAt_sq_eq_det_adjoint_comp ψ x ▸ pow_ne_zero 2 (hJ0 x hx)
  refine ⟨?_, fun x hx v ↦ ?_⟩
  · -- Step 6: `√(det ∘ G)` is `C¹` on `V`, as `det ∘ G` is `C¹` and nonvanishing there.
    rw [hJ]
    exact (hdetC.comp_contDiffOn hGC).sqrt hd0
  · -- Steps 4 and 7: the chain rule for `√(det ∘ G)` at `x`.
    have hGx := ((hGC.differentiableOn one_ne_zero x hx).differentiableAt
      (hV.mem_nhds hx)).hasFDerivAt
    have hdetx := ((hdetC.differentiable one_ne_zero)
      (ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x)).hasFDerivAt
    have hc := hdetx.comp x hGx
    have hJx : HasFDerivAt (fun y ↦
        Real.sqrt (ContinuousLinearMap.adjoint (fderiv ℝ ψ y) ∘L fderiv ℝ ψ y).det) _ x :=
      hc.sqrt (hd0 x hx)
    rw [← hJ] at hJx
    -- Step 5: `G(x)` is a unit with symmetric inverse (`gram_projection`), so the two traces in
    -- `tr(G⁻¹ (A* S_v + S_v* A))` agree (`trace_swap`).
    obtain ⟨hunit, hsymm, -⟩ := Submission.gram_inverse_range_starProjection n N
      (LinearMap.range (fderiv ℝ ψ x).toLinearMap) (fderiv ℝ ψ x) (hinj x hx) rfl
    rw [hJx.fderiv, smul_apply, ContinuousLinearMap.comp_apply, hGD x hx v, hdetD _ _ hunit,
      ContinuousLinearMap.comp_add, ContinuousLinearMap.toLinearMap_add, map_add,
      Submission.trace_comp_adjoint_comp_swap_of_symm n N (fderiv ℝ ψ x)
        (fderiv ℝ (fderiv ℝ ψ) x v) _ hsymm, Function.comp_apply,
      ← Chapter02.areaJacobianAt_eq_sqrt_det_adjoint_comp ψ x,
      ← Chapter02.areaJacobianAt_sq_eq_det_adjoint_comp ψ x, smul_eq_mul]
    field_simp [hJ0 x hx]
    ring
/-- **`C¹` regularity of the tangential coefficient field.** Let `V ⊆ ℝⁿ` be open, `ψ : ℝⁿ → ℝᴺ`
`C²` on `V` with `A(x) = Dψ(x)` injective for `x ∈ V`, and `u : ℝⁿ → ℝᴺ` `C¹` on `V`. Then
`a(x) = G(x)⁻¹ (A(x)* u(x))`, `G = A* ∘ A`, is `C¹` on `V`. `A` is `C¹` because `ψ` is `C²` on the
open set `V`. Over `ℝ` the adjoint is a continuous linear map, so `A*` is `C¹`, and `G` is `C¹`
because composition is continuous bilinear. Each `G(x)` is a unit
(`gram_inverse_range_starProjection` with `K = range A(x)`) and `Ring.inverse` is smooth at units,
so `G⁻¹` is `C¹`. Evaluation is continuous bilinear, which gives `a`. -/
theorem Submission.chart_tangential_coefficient_contDiffOn : ∀ (n N : ℕ) (V : Set (Rn n)) (ψ : Rn n → Rn N) (u : Rn n → Rn N), IsOpen V → ContDiffOn ℝ 2 ψ V → (∀ x ∈ V, Function.Injective (fderiv ℝ ψ x)) → ContDiffOn ℝ 1 u V → ContDiffOn ℝ 1 (fun x ↦ Ring.inverse (ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x) (ContinuousLinearMap.adjoint (fderiv ℝ ψ x) (u x))) V := by
  intro n N V ψ u hV hψ hinj hu
  -- Step 1: `A = Dψ` is `C¹` on `V`.
  have hA : ContDiffOn ℝ 1 (fderiv ℝ ψ) V := hψ.fderiv_of_isOpen hV (by norm_num)
  -- Step 2: `x ↦ A(x)*` is `C¹` on `V`; over `ℝ` the adjoint is a continuous linear map `adjR`.
  have hAs : ContDiffOn ℝ 1 (fun x ↦ ContinuousLinearMap.adjoint (fderiv ℝ ψ x)) V := by
    let adjR : (Rn n →L[ℝ] Rn N) →L[ℝ] Rn N →L[ℝ] Rn n :=
      (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Rn n) (F := Rn N)).toContinuousLinearEquiv
        |>.toContinuousLinearMap
    exact adjR.contDiff.comp_contDiffOn hA
  -- Step 3: `G = A* ∘ A` is `C¹` on `V`.
  have hG : ContDiffOn ℝ 1 (fun x ↦ ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x) V :=
    hAs.clm_comp hA
  -- Steps 4-5: each `G(x)`, `x ∈ V`, is a unit and `Ring.inverse` is smooth at units.
  have hGi : ContDiffOn ℝ 1
      (fun x ↦ Ring.inverse (ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x)) V := by
    intro x hx
    obtain ⟨U, hU⟩ := (Submission.gram_inverse_range_starProjection n N
      (LinearMap.range (fderiv ℝ ψ x).toLinearMap) (fderiv ℝ ψ x) (hinj x hx) rfl).1
    have hinv : ContDiffAt ℝ 1 Ring.inverse
        (ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x) :=
      hU ▸ contDiffAt_ringInverse ℝ U
    exact (hinv.comp x (hG.contDiffAt (hV.mem_nhds hx))).contDiffWithinAt
  -- Step 6: `a = G⁻¹ (A* u)` is `C¹` on `V`.
  exact hGi.clm_apply (hAs.clm_apply hu)
/-- **Symmetry of the second derivative (Schwarz).** If `ψ : ℝⁿ → ℝᴺ` is `C²` on an open set `V`,
then `D²ψ(x)[v, w] = D²ψ(x)[w, v]` for `x ∈ V`. Mathlib's `ContDiffAt.isSymmSndFDerivAt` is in
`Mathlib.Analysis.Calculus.FDeriv.Symmetric`, which the frozen header does not import, so this is
the classical second-difference proof. For `ε > 0` take `δ` with `B_δ(x) ⊆ V` and
`‖D²ψ(z) - D²ψ(x)‖ < ε` on `B_δ(x)`. For `‖a‖ + ‖b‖ < δ`, two applications of the mean value
inequality on `[0, 1]` give
`‖ψ(x + a + b) - ψ(x + a) - ψ(x + b) + ψ(x) - D²ψ(x)[a, b]‖ ≤ ε ‖a‖ ‖b‖`. The second difference
is symmetric in `(a, b)`. With `a = t v`, `b = t w` this gives
`‖D²ψ(x)[v, w] - D²ψ(x)[w, v]‖ ≤ 2 ε ‖v‖ ‖w‖` for every `ε > 0`. -/
theorem Submission.fderiv_fderiv_symm_of_contDiffOn_two : ∀ (n N : ℕ) (V : Set (Rn n)) (ψ : Rn n → Rn N), IsOpen V → ContDiffOn ℝ 2 ψ V → ∀ x ∈ V, ∀ v w : Rn n, fderiv ℝ (fderiv ℝ ψ) x v w = fderiv ℝ (fderiv ℝ ψ) x w v := by
  intro n N V ψ hV hψ x hx v w
  -- Step 1: `Dψ` is `C¹` on `V`, `D²ψ` is continuous on `V`, and `ψ`, `Dψ` are differentiable at
  -- every point of `V`.
  have hD : ContDiffOn ℝ 1 (fderiv ℝ ψ) V := hψ.fderiv_of_isOpen hV (by norm_num)
  have hD2 : ContinuousOn (fderiv ℝ (fderiv ℝ ψ)) V := hD.continuousOn_fderiv_of_isOpen hV le_rfl
  have hψd : ∀ z ∈ V, HasFDerivAt ψ (fderiv ℝ ψ z) z := fun z hz ↦
    ((hψ.differentiableOn (by norm_num)) z hz).differentiableAt (hV.mem_nhds hz) |>.hasFDerivAt
  have hDd : ∀ z ∈ V, HasFDerivAt (fderiv ℝ ψ) (fderiv ℝ (fderiv ℝ ψ) z) z := fun z hz ↦
    ((hD.differentiableOn (by norm_num)) z hz).differentiableAt (hV.mem_nhds hz) |>.hasFDerivAt
  -- Steps 2-5: `‖D²ψ(x)[v, w] - D²ψ(x)[w, v]‖ ≤ 2 ε ‖v‖ ‖w‖` for every `ε > 0`.
  have hbound : ∀ ε : ℝ, 0 < ε → ‖fderiv ℝ (fderiv ℝ ψ) x v w - fderiv ℝ (fderiv ℝ ψ) x w v‖ ≤
      2 * ε * ‖v‖ * ‖w‖ := by
    intro ε hε
    -- Step 2: `B_δ(x) ⊆ V` and `‖D²ψ(z) - D²ψ(x)‖ < ε` for `z ∈ B_δ(x)`.
    have hnhds : V ∩ fderiv ℝ (fderiv ℝ ψ) ⁻¹' ball (fderiv ℝ (fderiv ℝ ψ) x) ε ∈ 𝓝 x :=
      inter_mem (hV.mem_nhds hx)
        ((hD2.continuousAt (hV.mem_nhds hx)).preimage_mem_nhds
          (ball_mem_nhds (fderiv ℝ (fderiv ℝ ψ) x) hε))
    obtain ⟨δ, hδ, hδV⟩ := Metric.mem_nhds_iff.mp hnhds
    -- Steps 3-4: for `‖a‖ + ‖b‖ < δ`, the second difference is `D²ψ(x)[a, b]` up to `ε ‖a‖ ‖b‖`.
    have key : ∀ a b : Rn n, ‖a‖ + ‖b‖ < δ →
        ‖ψ (x + a + b) - ψ (x + a) - ψ (x + b) + ψ x - fderiv ℝ (fderiv ℝ ψ) x a b‖ ≤
          ε * ‖a‖ * ‖b‖ := by
      intro a b hab
      have hmem : ∀ r s : ℝ, r ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
          x + r • a + s • b ∈ ball x δ := by
        intro r s hr hs
        rw [mem_ball, dist_eq_norm, add_assoc, add_sub_cancel_left]
        calc ‖r • a + s • b‖ ≤ ‖r • a‖ + ‖s • b‖ := norm_add_le _ _
          _ = r * ‖a‖ + s * ‖b‖ := by
            rw [norm_smul, norm_smul, Real.norm_of_nonneg hr.1, Real.norm_of_nonneg hs.1]
          _ ≤ ‖a‖ + ‖b‖ := add_le_add (mul_le_of_le_one_left (norm_nonneg a) hr.2)
            (mul_le_of_le_one_left (norm_nonneg b) hs.2)
          _ < δ := hab
      have hV' : ∀ r s : ℝ, r ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → x + r • a + s • b ∈ V :=
        fun r s hr hs ↦ (hδV (hmem r s hr hs)).1
      have hclose : ∀ r s : ℝ, r ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
          ‖fderiv ℝ (fderiv ℝ ψ) (x + r • a + s • b) - fderiv ℝ (fderiv ℝ ψ) x‖ < ε := by
        intro r s hr hs
        have h := (hδV (hmem r s hr hs)).2
        rw [mem_preimage, mem_ball] at h
        exact (dist_eq_norm (fderiv ℝ (fderiv ℝ ψ) (x + r • a + s • b))
          (fderiv ℝ (fderiv ℝ ψ) x)).symm.trans_lt h
      -- Step 3 (inner estimate): mean value inequality for
      -- `k(r) = Dψ(x + r a + s b) b - r D²ψ(x)[a, b]`. Its derivative is
      -- `k'(r) = (D²ψ(x + r a + s b) - D²ψ(x))[a, b]`.
      have inner : ∀ s ∈ Icc (0 : ℝ) 1, ‖fderiv ℝ ψ (x + a + s • b) b - fderiv ℝ ψ (x + s • b) b -
          fderiv ℝ (fderiv ℝ ψ) x a b‖ ≤ ε * ‖a‖ * ‖b‖ := by
        intro s hs
        have hk : ∀ r ∈ Icc (0 : ℝ) 1, HasDerivWithinAt
            (fun r : ℝ ↦ fderiv ℝ ψ (x + r • a + s • b) b - r • fderiv ℝ (fderiv ℝ ψ) x a b)
            (fderiv ℝ (fderiv ℝ ψ) (x + r • a + s • b) a b - fderiv ℝ (fderiv ℝ ψ) x a b)
            (Icc (0 : ℝ) 1) r := by
          intro r hr
          have hγ : HasDerivAt (fun r : ℝ ↦ x + r • a + s • b) a r := by
            simpa using (((hasDerivAt_id r).smul_const a).const_add x).add_const (s • b)
          have h1 : HasDerivAt (fun r : ℝ ↦ fderiv ℝ ψ (x + r • a + s • b))
              (fderiv ℝ (fderiv ℝ ψ) (x + r • a + s • b) a) r :=
            (hDd _ (hV' r s hr hs)).comp_hasDerivAt r hγ
          have h2 := (h1.clm_apply (hasDerivAt_const r b)).sub
            ((hasDerivAt_id r).smul_const (fderiv ℝ (fderiv ℝ ψ) x a b))
          simp only [id_eq, map_zero, add_zero, one_smul] at h2
          exact h2.hasDerivWithinAt
        have hb : ∀ r ∈ Ico (0 : ℝ) 1, ‖fderiv ℝ (fderiv ℝ ψ) (x + r • a + s • b) a b -
            fderiv ℝ (fderiv ℝ ψ) x a b‖ ≤ ε * ‖a‖ * ‖b‖ := by
          intro r hr
          calc ‖fderiv ℝ (fderiv ℝ ψ) (x + r • a + s • b) a b - fderiv ℝ (fderiv ℝ ψ) x a b‖
              = ‖(fderiv ℝ (fderiv ℝ ψ) (x + r • a + s • b) - fderiv ℝ (fderiv ℝ ψ) x) a b‖ := by
                rw [sub_apply, sub_apply]
            _ ≤ ‖fderiv ℝ (fderiv ℝ ψ) (x + r • a + s • b) - fderiv ℝ (fderiv ℝ ψ) x‖ * ‖a‖ * ‖b‖ :=
                ContinuousLinearMap.le_opNorm₂ _ _ _
            _ ≤ ε * ‖a‖ * ‖b‖ := by
                gcongr
                exact (hclose r s (Ico_subset_Icc_self hr) hs).le
        have hfin := norm_image_sub_le_of_norm_deriv_le_segment_01' hk hb
        simp only [one_smul, zero_smul, add_zero, sub_zero] at hfin
        calc ‖fderiv ℝ ψ (x + a + s • b) b - fderiv ℝ ψ (x + s • b) b - fderiv ℝ (fderiv ℝ ψ) x a b‖
            = ‖fderiv ℝ ψ (x + a + s • b) b - fderiv ℝ (fderiv ℝ ψ) x a b -
                fderiv ℝ ψ (x + s • b) b‖ := by rw [sub_right_comm]
          _ ≤ ε * ‖a‖ * ‖b‖ := hfin
      -- Step 4 (outer estimate): mean value inequality for
      -- `g(s) = ψ(x + a + s b) - ψ(x + s b) - s D²ψ(x)[a, b]`. `inner` bounds its derivative.
      have hg : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt
          (fun s : ℝ ↦ ψ (x + a + s • b) - ψ (x + s • b) - s • fderiv ℝ (fderiv ℝ ψ) x a b)
          (fderiv ℝ ψ (x + a + s • b) b - fderiv ℝ ψ (x + s • b) b - fderiv ℝ (fderiv ℝ ψ) x a b)
          (Icc (0 : ℝ) 1) s := by
        intro s hs
        have hγ1 : HasDerivAt (fun s : ℝ ↦ x + a + s • b) b s := by
          simpa using ((hasDerivAt_id s).smul_const b).const_add (x + a)
        have hγ0 : HasDerivAt (fun s : ℝ ↦ x + s • b) b s := by
          simpa using ((hasDerivAt_id s).smul_const b).const_add x
        have hm1 : x + a + s • b ∈ V := by
          simpa using hV' 1 s (right_mem_Icc.2 zero_le_one) hs
        have hm0 : x + s • b ∈ V := by
          simpa using hV' 0 s (left_mem_Icc.2 zero_le_one) hs
        have h1 : HasDerivAt (fun s : ℝ ↦ ψ (x + a + s • b)) (fderiv ℝ ψ (x + a + s • b) b) s :=
          (hψd _ hm1).comp_hasDerivAt s hγ1
        have h0 : HasDerivAt (fun s : ℝ ↦ ψ (x + s • b)) (fderiv ℝ ψ (x + s • b) b) s :=
          (hψd _ hm0).comp_hasDerivAt s hγ0
        have h2 := (h1.sub h0).sub ((hasDerivAt_id s).smul_const (fderiv ℝ (fderiv ℝ ψ) x a b))
        simp only [id_eq, one_smul] at h2
        exact h2.hasDerivWithinAt
      have hfin := norm_image_sub_le_of_norm_deriv_le_segment_01' hg
        (fun s hs ↦ inner s (Ico_subset_Icc_self hs))
      simp only [one_smul, zero_smul, add_zero, sub_zero] at hfin
      calc ‖ψ (x + a + b) - ψ (x + a) - ψ (x + b) + ψ x - fderiv ℝ (fderiv ℝ ψ) x a b‖
          = ‖ψ (x + a + b) - ψ (x + b) - fderiv ℝ (fderiv ℝ ψ) x a b - (ψ (x + a) - ψ x)‖ := by
            congr 1
            abel
        _ ≤ ε * ‖a‖ * ‖b‖ := hfin
    -- Step 5: apply `key` to `(t v, t w)` and `(t w, t v)` with `t = δ / (‖v‖ + ‖w‖ + 1)`.
    obtain ⟨t, ht0, hsum⟩ : ∃ t : ℝ, 0 < t ∧ ‖t • v‖ + ‖t • w‖ < δ := by
      have hS : 0 < ‖v‖ + ‖w‖ + 1 := by positivity
      refine ⟨δ / (‖v‖ + ‖w‖ + 1), div_pos hδ hS, ?_⟩
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (div_pos hδ hS).le, ← mul_add,
        div_mul_eq_mul_div, div_lt_iff₀ hS]
      nlinarith [norm_nonneg v, norm_nonneg w]
    have k1 := key (t • v) (t • w) hsum
    have k2 := key (t • w) (t • v) (by rw [add_comm]; exact hsum)
    have hsmul : ∀ a b : Rn n, fderiv ℝ (fderiv ℝ ψ) x (t • a) (t • b) =
        (t * t) • fderiv ℝ (fderiv ℝ ψ) x a b := by
      intro a b
      rw [map_smul, map_smul, smul_apply, smul_smul]
    rw [hsmul, norm_smul, norm_smul, Real.norm_of_nonneg ht0.le] at k1 k2
    rw [add_right_comm x (t • w) (t • v)] at k2
    -- Step 6: the second difference is symmetric; cancel `t² > 0`.
    have h3 : t * t * ‖fderiv ℝ (fderiv ℝ ψ) x v w - fderiv ℝ (fderiv ℝ ψ) x w v‖ ≤
        t * t * (2 * ε * ‖v‖ * ‖w‖) := by
      calc t * t * ‖fderiv ℝ (fderiv ℝ ψ) x v w - fderiv ℝ (fderiv ℝ ψ) x w v‖
          = ‖(t * t) • (fderiv ℝ (fderiv ℝ ψ) x v w - fderiv ℝ (fderiv ℝ ψ) x w v)‖ := by
            rw [norm_smul, Real.norm_of_nonneg (mul_self_nonneg t)]
        _ = ‖(ψ (x + t • v + t • w) - ψ (x + t • w) - ψ (x + t • v) + ψ x -
              (t * t) • fderiv ℝ (fderiv ℝ ψ) x w v) -
            (ψ (x + t • v + t • w) - ψ (x + t • v) - ψ (x + t • w) + ψ x -
              (t * t) • fderiv ℝ (fderiv ℝ ψ) x v w)‖ := by
            rw [smul_sub]
            congr 1
            abel
        _ ≤ ‖ψ (x + t • v + t • w) - ψ (x + t • w) - ψ (x + t • v) + ψ x -
              (t * t) • fderiv ℝ (fderiv ℝ ψ) x w v‖ +
            ‖ψ (x + t • v + t • w) - ψ (x + t • v) - ψ (x + t • w) + ψ x -
              (t * t) • fderiv ℝ (fderiv ℝ ψ) x v w‖ := norm_sub_le _ _
        _ ≤ ε * (t * ‖w‖) * (t * ‖v‖) + ε * (t * ‖v‖) * (t * ‖w‖) := add_le_add k2 k1
        _ = t * t * (2 * ε * ‖v‖ * ‖w‖) := by ring
    exact le_of_mul_le_mul_left h3 (mul_pos ht0 ht0)
  -- Conclusion: `‖D²ψ(x)[v, w] - D²ψ(x)[w, v]‖ ≤ ε` for every `ε > 0`, so it vanishes.
  have hzero : ‖fderiv ℝ (fderiv ℝ ψ) x v w - fderiv ℝ (fderiv ℝ ψ) x w v‖ ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    have hK : 0 < 2 * ‖v‖ * ‖w‖ + 1 := by positivity
    calc ‖fderiv ℝ (fderiv ℝ ψ) x v w - fderiv ℝ (fderiv ℝ ψ) x w v‖
        ≤ 2 * (ε / (2 * ‖v‖ * ‖w‖ + 1)) * ‖v‖ * ‖w‖ := hbound _ (div_pos hε hK)
      _ = ε * (2 * ‖v‖ * ‖w‖ / (2 * ‖v‖ * ‖w‖ + 1)) := by ring
      _ ≤ ε * 1 := by
          gcongr
          rw [div_le_one hK]
          linarith
      _ = 0 + ε := by ring
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hzero)

/-- **Trace identity for the tangential coefficient field** (product-rule core of the chart
divergence formula). Put `A(y) = Dψ(y)`, `G(y) = A(y)* A(y)` and `a = G⁻¹ A* u`; fix `x ∈ V` and
write `A = A(x)`, `S = D²ψ(x)` and `p = u(x) - A a(x)`. By `gram_inverse_range_starProjection`
each `G(y)`, `y ∈ V`, is a unit, so `A(y)* (u(y) - A(y) a(y)) = 0` on `V`. Hence for every `c` the
function `y ↦ ⟪A(y) c, u(y) - A(y) a(y)⟫ = ⟪c, A(y)* (u(y) - A(y) a(y))⟫` vanishes near `x`, and
the product rule at `x` (`a` is `C¹` by `chart_tangential_coefficient_contDiffOn`) gives
`⟪A c, Du(x) v - A Da(x) v - S v a(x)⟫ + ⟪S v c, p⟫ = 0` for all `c, v`. For any `e` take
`c = G⁻¹ e`, so `A* A c = e`; with the symmetry of `G⁻¹` (`gram_inverse_range_starProjection`)
and `S v a(x) = S a(x) v` (`fderiv_fderiv_symm_of_contDiffOn_two`) this becomes
`⟪e, Da(x) e⟫ + ⟪e, G⁻¹ A* S(a(x)) e⟫ = ⟪e, G⁻¹ A* Du(x) e⟫ + ⟪p, S e (G⁻¹ e)⟫`. Summing over the
standard orthonormal basis `e_l` (`LinearMap.trace_eq_sum_inner`) gives the identity. -/
theorem Submission.chart_tangential_coefficient_trace_identity : ∀ (n N : ℕ) (V : Set (Rn n)) (ψ : Rn n → Rn N) (u : Rn n → Rn N), IsOpen V → ContDiffOn ℝ 2 ψ V → (∀ x ∈ V, Function.Injective (fderiv ℝ ψ x)) → ContDiffOn ℝ 1 u V → let a : Rn n → Rn n := fun x ↦ Ring.inverse (ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x) (ContinuousLinearMap.adjoint (fderiv ℝ ψ x) (u x)); ∀ x ∈ V, LinearMap.trace ℝ (Rn n) (fderiv ℝ a x).toLinearMap + LinearMap.trace ℝ (Rn n) (Ring.inverse (ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x) ∘L ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ (fderiv ℝ ψ) x (a x)).toLinearMap = LinearMap.trace ℝ (Rn n) (Ring.inverse (ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x) ∘L ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ u x).toLinearMap + inner ℝ (u x - fderiv ℝ ψ x (a x)) (∑ l : Fin n, fderiv ℝ (fderiv ℝ ψ) x (EuclideanSpace.single l 1) (Ring.inverse (ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x) (EuclideanSpace.single l 1))) := by
  intro n N V ψ u hV hψ hinj hu a x hx
  -- Step 1: `Dψ`, `u` and `a` are differentiable at `x`, and `S = D²ψ(x)` is symmetric.
  have hxV : V ∈ 𝓝 x := hV.mem_nhds hx
  have hA : HasFDerivAt (fderiv ℝ ψ) (fderiv ℝ (fderiv ℝ ψ) x) x :=
    (((hψ.fderiv_of_isOpen hV (m := 1) (by norm_num)).contDiffAt hxV).differentiableAt
      one_ne_zero).hasFDerivAt
  have hu' : HasFDerivAt u (fderiv ℝ u x) x :=
    ((hu.contDiffAt hxV).differentiableAt one_ne_zero).hasFDerivAt
  have ha' : HasFDerivAt a (fderiv ℝ a x) x :=
    (((Submission.chart_tangential_coefficient_contDiffOn n N V ψ u hV hψ hinj hu).contDiffAt
      hxV).differentiableAt one_ne_zero).hasFDerivAt
  have hS := Submission.fderiv_fderiv_symm_of_contDiffOn_two n N V ψ hV hψ x hx
  -- Step 2: `G(y) G(y)⁻¹ = 1` for `y ∈ V`, so `A(y)* (A(y) a(y)) = A(y)* u(y)` there.
  have hGG : ∀ y ∈ V, ∀ w : Rn n, ContinuousLinearMap.adjoint (fderiv ℝ ψ y) (fderiv ℝ ψ y
      (Ring.inverse (ContinuousLinearMap.adjoint (fderiv ℝ ψ y) ∘L fderiv ℝ ψ y) w)) = w :=
    fun y hy w ↦ congrArg (fun T : Rn n →L[ℝ] Rn n ↦ T w) (Ring.mul_inverse_cancel _
      (Submission.gram_inverse_range_starProjection n N _ (fderiv ℝ ψ y) (hinj y hy) rfl).1)
  have hGa : ∀ y ∈ V, ContinuousLinearMap.adjoint (fderiv ℝ ψ y) (fderiv ℝ ψ y (a y)) =
      ContinuousLinearMap.adjoint (fderiv ℝ ψ y) (u y) := fun y hy ↦ hGG y hy _
  -- Step 3: `y ↦ ⟪A(y) c, u y - A(y) (a y)⟫` vanishes on `V`; its derivative at `x` in direction
  -- `v` is `⟪A c, Du v - (A Da v + S v a)⟫ + ⟪S v c, u - A a⟫`, which is therefore `0`.
  have hkey : ∀ c v : Rn n, inner ℝ (fderiv ℝ ψ x c) (fderiv ℝ u x v -
      (fderiv ℝ ψ x (fderiv ℝ a x v) + fderiv ℝ (fderiv ℝ ψ) x v (a x))) +
      inner ℝ (fderiv ℝ (fderiv ℝ ψ) x v c) (u x - fderiv ℝ ψ x (a x)) = 0 := by
    intro c v
    have hF := (hA.clm_apply (hasFDerivAt_const c x)).inner ℝ (hu'.sub (hA.clm_apply ha'))
    have hF0 : HasFDerivAt (fun y ↦ inner ℝ (fderiv ℝ ψ y c) (u y - fderiv ℝ ψ y (a y)))
        (0 : Rn n →L[ℝ] ℝ) x := by
      refine (hasFDerivAt_const (0 : ℝ) x).congr_of_eventuallyEq ?_
      filter_upwards [hxV] with y hy
      rw [← ContinuousLinearMap.adjoint_inner_right, map_sub, hGa y hy, sub_self,
        inner_zero_right]
    have h := congrArg (fun L : Rn n →L[ℝ] ℝ ↦ L v) (hF.unique hF0)
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      fderivInnerCLM_apply, add_apply, sub_apply, Pi.sub_apply, ContinuousLinearMap.flip_apply,
      zero_apply, map_zero, zero_add] using h
  -- Step 4: for every `e`, with `c = G⁻¹ e` (so `A* A c = e`) and `G⁻¹` symmetric,
  -- `⟪e, Da e⟫ + ⟪e, G⁻¹ A* S(a) e⟫ = ⟪e, G⁻¹ A* Du e⟫ + ⟪u - A a, S e c⟫`.
  obtain ⟨-, hsym, -⟩ :=
    Submission.gram_inverse_range_starProjection n N _ (fderiv ℝ ψ x) (hinj x hx) rfl
  have hterm : ∀ e : Rn n, inner ℝ e (fderiv ℝ a x e) + inner ℝ e ((Ring.inverse
      (ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x) ∘L
      ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ (fderiv ℝ ψ) x (a x)) e) =
      inner ℝ e ((Ring.inverse (ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x) ∘L
        ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ u x) e) +
      inner ℝ (u x - fderiv ℝ ψ x (a x)) (fderiv ℝ (fderiv ℝ ψ) x e (Ring.inverse
        (ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x) e)) := by
    intro e
    have hk :=
      hkey (Ring.inverse (ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x) e) e
    rw [inner_sub_right (fderiv ℝ ψ x _), inner_add_right (fderiv ℝ ψ x _), hS e (a x),
      ← ContinuousLinearMap.adjoint_inner_left (fderiv ℝ ψ x) (fderiv ℝ a x e), hGG x hx,
      real_inner_comm (u x - fderiv ℝ ψ x (a x))] at hk
    simp only [ContinuousLinearMap.comp_apply]
    rw [← hsym e, ← hsym e, ContinuousLinearMap.adjoint_inner_right,
      ContinuousLinearMap.adjoint_inner_right]
    linarith
  -- Step 5: compute the three traces in the standard orthonormal basis `e_l` and sum.
  have htr : ∀ T : Rn n →L[ℝ] Rn n, LinearMap.trace ℝ (Rn n) T.toLinearMap =
      ∑ l : Fin n, inner ℝ (EuclideanSpace.single l (1 : ℝ) : Rn n)
        (T (EuclideanSpace.single l 1)) := by
    intro T
    rw [LinearMap.trace_eq_sum_inner T.toLinearMap (EuclideanSpace.basisFun (Fin n) ℝ)]
    simp only [EuclideanSpace.basisFun_apply, ContinuousLinearMap.coe_coe]
  rw [htr, htr, htr, inner_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun l _ ↦ hterm _
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

/-- **Simon Ch. 2, 4.21–4.30 (pp. 59–61) in a chart: the divergence density.** Assume `(TH)`, the
frozen statement of `simon_submanifold_tangent_basics`. Let `(V, W, ψ)` be a class-`2` local
representation of `M`, `Y` a `C¹` field, and put `A = Dψ`, `G = A*A`, `J = areaJacobianAt ψ`,
`u = Y ∘ ψ`, `a = G⁻¹A*u`. Then `w = J • a` is `C¹` on `V` and vanishes where `u` does. By the
product rule and Jacobi's formula, `trace Dw = J (trace Da + trace(G⁻¹A* D²ψ[a]))`, and the
coefficient trace identity rewrites the bracket as `trace(G⁻¹A* Du) + ⟨u - Aa, ∑ₗ D²ψ[eₗ, G⁻¹eₗ]⟩`.
The first term is `div_M Y ∘ ψ` (chain rule and the chart formula for `div_M`). Since `Aa = Pu` with
`P = AG⁻¹A*` self-adjoint, the chart formulas for `H` and `B` make the second term `⟨u, H ∘ ψ⟩`. -/
theorem Submission.chart_divergence_density_formula : ((∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)) (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N), 1 ≤ r → Chapter02.IsSimonLocalRepresentation r M V W ψ → ∀ x ∈ V, tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap) ∧ ∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)), Chapter02.IsSimonSubmanifold (E := Rn n) r M → MeasurableSet M ∧ ContinuousOn (tangentProjection M) M) → ∀ (n N : ℕ) (M : Set (Rn N)) (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N) (Y : Rn N → Rn N), Chapter02.IsSimonLocalRepresentation 2 M V W ψ → ContDiff ℝ 1 Y → ∃ w : Rn n → Rn n, ContDiffOn ℝ 1 w V ∧ (∀ x ∈ V, Y (ψ x) = 0 → w x = 0) ∧ ∀ x ∈ V, LinearMap.trace ℝ (Rn n) (fderiv ℝ w x).toLinearMap = Chapter02.areaJacobianAt ψ x * (tangentialDivergence M Y (ψ x) + inner ℝ (Y (ψ x)) (meanCurvature M (ψ x))) := by
  intro hTH n N M V W ψ Y hψ hY
  have hV : IsOpen V := hψ.isOpen_source
  have hψ2 : ContDiffOn ℝ 2 ψ V := hψ.contDiffOn
  have hinj : ∀ x ∈ V, Function.Injective (fderiv ℝ ψ x) := fun x hx ↦ hψ.injective_fderiv hx
  have hu : ContDiffOn ℝ 1 (fun x ↦ Y (ψ x)) V := hY.comp_contDiffOn (hψ2.of_le (by norm_num))
  obtain ⟨hJ, hDJ⟩ :=
    Submission.areaJacobianAt_contDiffOn_fderiv_eq_gram_trace n N V ψ hV hψ2 hinj
  have ha := Submission.chart_tangential_coefficient_contDiffOn n N V ψ _ hV hψ2 hinj hu
  -- `w = J • a` with `a = G⁻¹A*(Y ∘ ψ)`.
  refine ⟨fun x ↦ Chapter02.areaJacobianAt ψ x • Ring.inverse
      (ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x)
      (ContinuousLinearMap.adjoint (fderiv ℝ ψ x) (Y (ψ x))), hJ.smul ha,
    fun x _ h0 ↦ by simp only [h0, map_zero, smul_zero], fun x hx ↦ ?_⟩
  have hxV : V ∈ 𝓝 x := hV.mem_nhds hx
  have hT : tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap :=
    hTH.1 n N 2 M V W ψ (by norm_num) hψ x hx
  -- Product rule and Jacobi's formula: `trace Dw = J trace Da + J trace(G⁻¹A* D²ψ[a])`.
  have hsr (f : Rn n →L[ℝ] ℝ) (v : Rn n) :
      LinearMap.trace ℝ (Rn n) (f.smulRight v).toLinearMap = f v :=
    LinearMap.trace_smulRight f.toLinearMap v
  rw [fderiv_fun_smul (hJ.contDiffAt hxV).differentiableAt_one
      (ha.contDiffAt hxV).differentiableAt_one, ContinuousLinearMap.toLinearMap_add,
    ContinuousLinearMap.toLinearMap_smul, map_add, map_smul, smul_eq_mul, hsr, hDJ x hx]
  -- The coefficient trace identity, with `Du(x) = DY(ψ x) ∘ A` (chain rule).
  have hcore :=
    Submission.chart_tangential_coefficient_trace_identity n N V ψ _ hV hψ2 hinj hu x hx
  dsimp only at hcore
  rw [fderiv_fun_comp x (hY.differentiable one_ne_zero _)
    ((hψ2.contDiffAt hxV).differentiableAt (by norm_num)), inner_sub_left] at hcore
  -- The chart formulas for `div_M Y` and `H`; `P = AG⁻¹A*` is self-adjoint.
  have hP := (Submission.gram_inverse_range_starProjection n N (tangentSpace M (ψ x))
    (fderiv ℝ ψ x) (hinj x hx) hT).2.2
  rw [Submission.chart_tangentialDivergence_eq_gram_trace n N M (ψ x) (fderiv ℝ ψ x) Y
      (hinj x hx) hT,
    Submission.chart_meanCurvature_eq_normalPart_gram_sum n N M (ψ x) (fderiv ℝ ψ x)
      (fderiv ℝ (fderiv ℝ ψ) x) (hinj x hx) hT
      (Submission.second_fundamental_form_chart_formula hTH n N M V W ψ hψ x hx),
    normalPart, tangentProjection, inner_sub_right,
    ← Submodule.inner_starProjection_left_eq_right, hP, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]
  linear_combination Chapter02.areaJacobianAt ψ x * hcore

/-- The frozen Chapter 2 contract: the conjunction of all headline results. -/
theorem main_theorem : LipschitzExtension ∧ Rademacher ∧ C1Approximation ∧ WhitneyExtension ∧ LipschitzImageHausdorff ∧ EilenbergInequality ∧ BVCompactness ∧ BVPoincare ∧ BVExtensionEstimate ∧ AreaFormula ∧ FirstVariation ∧ SecondVariation ∧ StationaryIffMeanCurvatureZero ∧ SecondVariationStationary ∧ CoareaFormula ∧ C1Sard := by sorry

end GMT.Ch02
