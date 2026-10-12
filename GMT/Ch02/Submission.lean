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

/-- **Simon Ch. 2, proof of Theorem 2.6, step A0: unweighted uniform bounds.** For open `W ⊆ ℝⁿ`
with `Lⁿ(W) < ∞`, the frozen hypothesis `sup_k ∫_W (|u_k| + |Du_k|(W)) dLⁿ < ∞` (the constant
`|Du_k|(W)` inside the integrand) yields one real `c ≥ 0` with `∫_W |u_k| ≤ c` and `|Du_k|(W) ≤ c`
for every `k`. If `W = ∅` both quantities vanish; otherwise `0 < Lⁿ(W) < ∞`, the integral of the
constant is `|Du_k|(W) Lⁿ(W)`, and `c = S + S / Lⁿ(W)` with `S` the supremum. -/
theorem Submission.bv_compactness_uniform_bounds : ∀ (n : ℕ) (W : Set (Rn n)) (u : ℕ → Rn n → ℝ), IsOpen W → volume W < ⊤ → ⨆ k, (∫⁻ x in W, ‖u k x‖ₑ + Chapter02.bvVariationOn (u k) W) < ⊤ → ∃ c : ℝ, 0 ≤ c ∧ ∀ k, (∫⁻ x in W, ‖u k x‖ₑ) ≤ ENNReal.ofReal c ∧ Chapter02.bvVariationOn (u k) W ≤ ENNReal.ofReal c := by
  intro n W u hW hWfin hS
  rcases W.eq_empty_or_nonempty with rfl | hne
  -- Step 1: `W = ∅`. Both quantities are integrals against `volume.restrict ∅ = 0`.
  · refine ⟨0, le_rfl, fun k ↦ ⟨by simp, ?_⟩⟩
    simp [Chapter02.bvVariationOn]
  -- Step 2: `0 < Lⁿ(W) < ∞` (`Lⁿ` is positive on nonempty open sets).
  · have h0 : volume W ≠ 0 := (hW.measure_pos volume hne).ne'
    have hfin : volume W ≠ ⊤ := hWfin.ne
    set S := ⨆ k, (∫⁻ x in W, ‖u k x‖ₑ + Chapter02.bvVariationOn (u k) W)
    -- Step 3: `∫_W |u_k| + |Du_k|(W) Lⁿ(W) = ∫_W (|u_k| + |Du_k|(W)) ≤ S`.
    have hk : ∀ k, (∫⁻ x in W, ‖u k x‖ₑ) + Chapter02.bvVariationOn (u k) W * volume W ≤ S :=
      fun k ↦ by
        rw [← setLIntegral_const, ← lintegral_add_right _ measurable_const]
        exact le_iSup (fun k ↦ ∫⁻ x in W, ‖u k x‖ₑ + Chapter02.bvVariationOn (u k) W) k
    -- Step 5: `C = S + S / Lⁿ(W) < ∞`; take `c = C.toReal`, so `ofReal c = C`.
    have hC : S + S / volume W ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hS.ne, ENNReal.div_ne_top hS.ne h0⟩
    refine ⟨(S + S / volume W).toReal, ENNReal.toReal_nonneg, fun k ↦ ?_⟩
    rw [ENNReal.ofReal_toReal hC]
    -- Steps 4 and 6: `∫_W |u_k| ≤ S` and `|Du_k|(W) ≤ S / Lⁿ(W)`.
    refine ⟨le_add_right (le_self_add.trans (hk k)), le_add_left ?_⟩
    rw [ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl hfin)]
    exact le_add_self.trans (hk k)
/-- **Simon Ch. 2, proof of Theorem 2.6 (step A4): a variation bound gives the bound (2.1).** If
`|Du|(W) ≤ c` (`Chapter02.bvVariationOn`, Simon 2.4) and `g` is a compactly supported `C¹` field
with `spt g ⊆ W`, then `∫_W u div g ≤ c sup |g|`. With `s = sup |g|`: if `s = 0` then `g = 0` and
both sides vanish; otherwise `h = s⁻¹ g` is an admissible Lipschitz field in (2.4) with
`sup |h| ≤ 1` and `div h = s⁻¹ div g`, so `s⁻¹ ∫_W u div g = ∫_W u div h ≤ |Du|(W) ≤ c`. -/
theorem Submission.bv_integral_div_le_of_variation_le : ∀ (n : ℕ) (W : Set (Rn n)) (u : Rn n → ℝ) (c : ℝ), 0 ≤ c → Chapter02.bvVariationOn u W ≤ ENNReal.ofReal c → ∀ g : CompactlySupportedContinuousMap (Rn n) (Rn n), Chapter02.IsC1TestField g → tsupport g ⊆ W → (∫ x in W, u x * Chapter02.euclideanDivergence (g : Rn n → Rn n) x) ≤ c * Chapter02.compactlySupportedSupNorm g := by
  intro n W u c hc hvar g hg hsupp
  set s := Chapter02.compactlySupportedSupNorm g
  -- Step 1: `g` is bounded, so `‖g x‖ ≤ s` for every `x`, and `0 ≤ s`.
  have hbdd : BddAbove (range fun x ↦ ‖g x‖) := by
    obtain ⟨C, hC⟩ := (map_continuous g).bounded_above_of_compact_support g.hasCompactSupport
    exact ⟨C, by rintro _ ⟨x, rfl⟩; exact hC x⟩
  have hle : ∀ x, ‖g x‖ ≤ s := fun x ↦ le_csSup hbdd ⟨x, rfl⟩
  have hs0 : 0 ≤ s := (norm_nonneg _).trans (hle 0)
  rcases hs0.eq_or_lt with hs | hs
  · -- Step 2: `s = 0`, so `g = 0`, `div g = 0` and both sides vanish.
    have hg0 : (g : Rn n → Rn n) = 0 := funext fun x ↦ norm_le_zero_iff.mp (hs ▸ hle x)
    have hdiv0 : ∀ x, Chapter02.euclideanDivergence (g : Rn n → Rn n) x = 0 := fun x ↦ by
      simp [Chapter02.euclideanDivergence, hg0]
    simp [hdiv0, ← hs]
  · -- Step 3: `s > 0`; normalize to `h := s⁻¹ • g`.
    set h : CompactlySupportedContinuousMap (Rn n) (Rn n) := s⁻¹ • g
    have hcoe : (h : Rn n → Rn n) = s⁻¹ • (g : Rn n → Rn n) :=
      CompactlySupportedContinuousMap.coe_smul _ _
    -- (a) `h` is `C¹`, hence an admissible Lipschitz test field.
    have hC1 : Chapter02.IsC1TestField h := by
      unfold Chapter02.IsC1TestField
      rw [hcoe]
      exact hg.const_smul s⁻¹
    -- (b) `tsupport h ⊆ tsupport g ⊆ W`.
    have hsupp' : tsupport h ⊆ W := by
      rw [hcoe]
      exact (tsupport_smul_subset_right (fun _ ↦ s⁻¹) g).trans hsupp
    -- (c) `sup |h| = s⁻¹ s ≤ 1`.
    have hnorm : Chapter02.compactlySupportedSupNorm h ≤ 1 := by
      refine csSup_le (range_nonempty _) ?_
      rintro _ ⟨x, rfl⟩
      simp only [hcoe, Pi.smul_apply, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hs.le)]
      calc s⁻¹ * ‖g x‖ ≤ s⁻¹ * s := mul_le_mul_of_nonneg_left (hle x) (inv_nonneg.mpr hs.le)
        _ = 1 := inv_mul_cancel₀ hs.ne'
    -- (d) `div h = s⁻¹ div g`, since `D h = s⁻¹ D g` and the trace is linear.
    have hdiv : ∀ x, Chapter02.euclideanDivergence (h : Rn n → Rn n) x =
        s⁻¹ * Chapter02.euclideanDivergence (g : Rn n → Rn n) x := fun x ↦ by
      have hd : DifferentiableAt ℝ (g : Rn n → Rn n) x := hg.differentiable one_ne_zero x
      simp only [Chapter02.euclideanDivergence, hcoe, fderiv_const_smul hd,
        ContinuousLinearMap.toLinearMap_smul, map_smul, smul_eq_mul]
    -- Step 4: `h` is admissible in `bvVariationOn u W`, so `∫_W u div h ≤ c`.
    have h1 : (∫ x in W, u x * Chapter02.euclideanDivergence (h : Rn n → Rn n) x) ≤ c :=
      (ENNReal.ofReal_le_ofReal_iff hc).mp
        ((Chapter02.ofReal_integral_le_bvVariationOn u W h hC1.isLipschitzTestField hsupp'
          hnorm).trans hvar)
    -- Step 5: `∫_W u div h = s⁻¹ ∫_W u div g`; multiply by `s > 0`.
    have h2 : (∫ x in W, u x * Chapter02.euclideanDivergence (h : Rn n → Rn n) x) =
        s⁻¹ * ∫ x in W, u x * Chapter02.euclideanDivergence (g : Rn n → Rn n) x := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      simp only [hdiv x]
      ring
    rw [h2, inv_mul_le_iff₀ hs] at h1
    linarith
/-- **Simon Ch. 2, proof of Theorem 2.6: sup and Lipschitz bounds for a mollification.** For `ρ`
bounded by `A` and `K`-Lipschitz, and `F ∈ L¹(ℝⁿ)`: `|(ρ * F)(x)| ≤ A ∫ |F|` and
`|(ρ * F)(x) - (ρ * F)(y)| ≤ K |x - y| ∫ |F|` (the uniform bounds behind the Arzelà step). In the
symmetric form `(ρ * F)(z) = ∫ ρ(z - t) F(t) dt` (translation and reflection invariance of `Lⁿ`),
both follow by integrating the majorants `A |F|` and `K |x - y| |F|`. -/
theorem Submission.bv_convolution_bound_and_lipschitz : ∀ (n : ℕ) (ρ F : Rn n → ℝ) (A : ℝ) (K : ℝ≥0), (∀ x, |ρ x| ≤ A) → LipschitzWith K ρ → Integrable F volume → ∀ x y : Rn n, |convolution ρ F (ContinuousLinearMap.lsmul ℝ ℝ) volume x| ≤ A * (∫ t, |F t|) ∧ |convolution ρ F (ContinuousLinearMap.lsmul ℝ ℝ) volume x - convolution ρ F (ContinuousLinearMap.lsmul ℝ ℝ) volume y| ≤ K * ‖x - y‖ * (∫ t, |F t|) := by
  intro n ρ F A K hA hK hF x y
  -- Step 2: `(ρ * F)(z) = ∫ ρ(z - t) F(t) dt`.
  have hswap : ∀ z, convolution ρ F (ContinuousLinearMap.lsmul ℝ ℝ) volume z =
      ∫ t, ρ (z - t) * F t := fun z ↦ by
    simp only [convolution_lsmul_swap, smul_eq_mul]
  -- Step 3: `t ↦ ρ(z - t) F(t)` is integrable: `t ↦ ρ(z - t)` is continuous (`ρ` is Lipschitz)
  -- and bounded by `A`.
  have hint : ∀ z, Integrable (fun t ↦ ρ (z - t) * F t) volume := fun z ↦
    hF.bdd_mul (hK.continuous.comp (continuous_sub_left z)).aestronglyMeasurable
      (Eventually.of_forall fun t ↦ by rw [Real.norm_eq_abs]; exact hA (z - t))
  refine ⟨?_, ?_⟩
  -- Step 4: `|ρ(x - t) F(t)| ≤ A |F(t)|`.
  · calc |convolution ρ F (ContinuousLinearMap.lsmul ℝ ℝ) volume x|
        = ‖∫ t, ρ (x - t) * F t‖ := by rw [hswap, Real.norm_eq_abs]
      _ ≤ ∫ t, A * |F t| := by
        refine norm_integral_le_of_norm_le (hF.abs.const_mul A) (Eventually.of_forall fun t ↦ ?_)
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right (hA _) (abs_nonneg _)
      _ = A * ∫ t, |F t| := integral_const_mul A _
  -- Step 5: `|(ρ(x - t) - ρ(y - t)) F(t)| ≤ K |x - y| |F(t)|`.
  · calc |convolution ρ F (ContinuousLinearMap.lsmul ℝ ℝ) volume x -
          convolution ρ F (ContinuousLinearMap.lsmul ℝ ℝ) volume y|
        = ‖∫ t, (ρ (x - t) * F t - ρ (y - t) * F t)‖ := by
          rw [hswap, hswap, integral_sub (hint x) (hint y), Real.norm_eq_abs]
      _ ≤ ∫ t, K * ‖x - y‖ * |F t| := by
        refine norm_integral_le_of_norm_le (hF.abs.const_mul _) (Eventually.of_forall fun t ↦ ?_)
        rw [Real.norm_eq_abs, ← sub_mul, abs_mul]
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        have hLip := hK.dist_le_mul (x - t) (y - t)
        rwa [Real.dist_eq, dist_eq_norm, sub_sub_sub_cancel_right] at hLip
      _ = K * ‖x - y‖ * ∫ t, |F t| := integral_const_mul _ _
/-- **Simon Ch. 2, proof of Theorem 2.6: finite `L¹(Q)`-nets (the Arzelà step).** Let `Q ⊂ ℝⁿ` be
compact and `u_k ∈ L¹(Q)`. Suppose that for each `ε > 0` there are `w_k`, bounded by `B` and
`Λ`-Lipschitz on `Q` (`B`, `Λ` independent of `k`), with `∫_Q |u_k - w_k| ≤ ε`. Then for each
`ε > 0` finitely many `u_j` form an `ε`-net of `{u_k}` in `L¹(Q)`. The values of the `w_k` on a
finite `r`-net `T ⊂ Q` lie in a compact ball of `T → ℝ`, so up to `η / 2` they take finitely many
values; `w_k`, `w_j` with nearby values on `T` are uniformly `η`-close on `Q`. -/
theorem Submission.bv_lintegral_finite_net_of_lipschitz_approx : ∀ (n : ℕ) (Q : Set (Rn n)) (u : ℕ → Rn n → ℝ), IsCompact Q → (∀ k, IntegrableOn (u k) Q volume) → (∀ ε : ℝ, 0 < ε → ∃ (B Λ : ℝ) (w : ℕ → Rn n → ℝ), (∀ k, ∀ x ∈ Q, |w k x| ≤ B) ∧ (∀ k, ∀ x ∈ Q, ∀ y ∈ Q, |w k x - w k y| ≤ Λ * ‖x - y‖) ∧ ∀ k, (∫⁻ x in Q, ‖u k x - w k x‖ₑ) ≤ ENNReal.ofReal ε) → ∀ ε : ℝ, 0 < ε → ∃ F : Finset ℕ, ∀ k, ∃ j ∈ F, (∫⁻ x in Q, ‖u k x - u j x‖ₑ) < ENNReal.ofReal ε := by
  intro n Q u hQ hu happrox ε hε
  -- Step 1: `Q` is closed, hence measurable, and `Lⁿ(Q) < ∞`; put `m = Lⁿ(Q)`.
  have hQm : MeasurableSet Q := hQ.isClosed.measurableSet
  have hQfin : volume Q < ⊤ := hQ.measure_lt_top
  set m : ℝ := (volume Q).toReal with hm
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  -- Step 3: approximate at accuracy `ε / 4`; `Λ' = max Λ 0 ≥ 0` is also a Lipschitz constant.
  obtain ⟨B, Λ, w, hB, hΛ, hw⟩ := happrox (ε / 4) (by positivity)
  obtain ⟨Λ', hΛ'0, hwΛ'⟩ : ∃ Λ' : ℝ, 0 ≤ Λ' ∧
      ∀ k, ∀ x ∈ Q, ∀ y ∈ Q, |w k x - w k y| ≤ Λ' * ‖x - y‖ :=
    ⟨max Λ 0, le_max_right _ _, fun k x hx y hy ↦
      (hΛ k x hx y hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))⟩
  -- Step 4 (with the Remark's radius): `η = ε / (4 (m + 1))`, `r = η / (4 (Λ' + 1))`, and a finite
  -- `T ⊂ Q` with `Q ⊂ ⋃_{q ∈ T} B(q, r)` (open balls).
  set η : ℝ := ε / (4 * (m + 1)) with hη
  have hη0 : 0 < η := by positivity
  set r : ℝ := η / (4 * (Λ' + 1)) with hr
  have hr0 : 0 < r := by positivity
  obtain ⟨T, hTQ, hTfin, hQT⟩ := hQ.finite_cover_balls hr0
  have : Fintype T := hTfin.fintype
  -- Steps 5–6 (Remark): `p_k = (w_k(q))_{q ∈ T}` lies in the compact closed ball of radius
  -- `max B 0` of the sup-normed `T → ℝ`, so `{p_k}` has a finite `η / 2`-net `t ⊂ {p_k}`; `F`
  -- consists of one index `j` with `p_j = y` for each `y ∈ t`.
  let p : ℕ → T → ℝ := fun k q ↦ w k q
  have hpB : Set.range p ⊆ closedBall 0 (max B 0) := by
    rintro _ ⟨k, rfl⟩
    rw [mem_closedBall, dist_pi_le_iff (le_max_right _ _)]
    intro q
    rw [Real.dist_eq, Pi.zero_apply, sub_zero]
    exact (hB k q (hTQ q.2)).trans (le_max_left _ _)
  have hptb : TotallyBounded (Set.range p) := (isCompact_closedBall _ _).totallyBounded.subset hpB
  obtain ⟨t, htp, htfin, hpt⟩ := Metric.finite_approx_of_totallyBounded hptb (η / 2) (by positivity)
  refine ⟨htfin.toFinset.image (Function.invFun p), fun k ↦ ?_⟩
  obtain ⟨y, hyt, hky⟩ : ∃ y ∈ t, p k ∈ ball y (η / 2) := by
    simpa using hpt (Set.mem_range_self k)
  set j := Function.invFun p y
  have hpj : p j = y := Function.invFun_eq (htp hyt)
  refine ⟨j, Finset.mem_image.2 ⟨y, htfin.mem_toFinset.2 hyt, rfl⟩, ?_⟩
  -- Step 7: `|w_k(q) - w_j(q)| ≤ dist p_k p_j < η / 2` for `q ∈ T`.
  have hT : ∀ q ∈ T, |w k q - w j q| < η / 2 := fun q hq ↦ by
    have hd : dist (p k) (p j) < η / 2 := by rw [hpj]; exact hky
    have hq' := dist_le_pi_dist (p k) (p j) ⟨q, hq⟩
    rw [Real.dist_eq] at hq'
    exact hq'.trans_lt hd
  -- Step 8: for `x ∈ Q` and `q ∈ T` with `|x - q| < r`,
  -- `|w_k(x) - w_j(x)| ≤ Λ' r + η / 2 + Λ' r ≤ η`, since `Λ' r ≤ η / 4`.
  have hΛr : Λ' * r ≤ η / 4 := by
    rw [hr, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hQpt : ∀ x ∈ Q, ‖w k x - w j x‖ₑ ≤ ENNReal.ofReal η := fun x hx ↦ by
    obtain ⟨q, hqT, hxq⟩ : ∃ q ∈ T, x ∈ ball q r := by simpa using hQT hx
    have hq : q ∈ Q := hTQ hqT
    rw [mem_ball, dist_eq_norm] at hxq
    have h1 : |w k x - w k q| ≤ Λ' * r :=
      (hwΛ' k x hx q hq).trans (mul_le_mul_of_nonneg_left hxq.le hΛ'0)
    have h2 : |w j q - w j x| ≤ Λ' * r := by
      refine (hwΛ' j q hq x hx).trans (mul_le_mul_of_nonneg_left ?_ hΛ'0)
      rw [norm_sub_rev]
      exact hxq.le
    have h3 : |w k x - w j x| ≤ η := calc
      |w k x - w j x| = |(w k x - w k q) + (w k q - w j q) + (w j q - w j x)| := by
        congr 1; ring
      _ ≤ |w k x - w k q| + |w k q - w j q| + |w j q - w j x| := abs_add_three _ _ _
      _ ≤ η := by linarith [hT q hqT]
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal h3
  -- Step 9: `∫_Q |w_k - w_j| ≤ η m ≤ ε / 4`.
  have hηm : η * m ≤ ε / 4 := by
    rw [hη, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hwkj : (∫⁻ x in Q, ‖w k x - w j x‖ₑ) ≤ ENNReal.ofReal (ε / 4) := calc
    (∫⁻ x in Q, ‖w k x - w j x‖ₑ) ≤ ∫⁻ _ in Q, ENNReal.ofReal η :=
      setLIntegral_mono measurable_const hQpt
    _ = ENNReal.ofReal (η * m) := by
      rw [setLIntegral_const, ENNReal.ofReal_mul hη0.le, hm, ENNReal.ofReal_toReal hQfin.ne]
    _ ≤ ENNReal.ofReal (ε / 4) := ENNReal.ofReal_le_ofReal hηm
  -- Step 10: `u_k` is a.e.-strongly measurable for `Lⁿ ⌞ Q`, and so is each `w_i`, being
  -- Lipschitz, hence continuous, on the measurable set `Q`.
  have hwm : ∀ i, AEStronglyMeasurable (w i) (volume.restrict Q) := fun i ↦
    (LipschitzOnWith.of_dist_le_mul (K := Real.toNNReal Λ') fun x hx y hy ↦ by
      rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hΛ'0]
      exact hwΛ' i x hx y hy).continuousOn.aestronglyMeasurable hQm
  have hk : AEMeasurable (fun x ↦ ‖u k x - w k x‖ₑ) (volume.restrict Q) :=
    ((hu k).aestronglyMeasurable.sub (hwm k)).enorm
  have hkj : AEMeasurable (fun x ↦ ‖u k x - w k x‖ₑ + ‖w k x - w j x‖ₑ) (volume.restrict Q) :=
    hk.add ((hwm k).sub (hwm j)).enorm
  -- Step 11: `|u_k - u_j| ≤ |u_k - w_k| + |w_k - w_j| + |u_j - w_j|`; integrate (additivity with
  -- a.e.-measurable left summands) and use the approximation for `k` and `j` and Step 9.
  calc (∫⁻ x in Q, ‖u k x - u j x‖ₑ)
      ≤ ∫⁻ x in Q, (‖u k x - w k x‖ₑ + ‖w k x - w j x‖ₑ + ‖u j x - w j x‖ₑ) := by
        refine lintegral_mono fun x ↦ ?_
        calc ‖u k x - u j x‖ₑ = ‖(u k x - w k x) + (w k x - w j x) + (w j x - u j x)‖ₑ := by
              congr 1; ring
          _ ≤ ‖u k x - w k x‖ₑ + ‖w k x - w j x‖ₑ + ‖w j x - u j x‖ₑ :=
              (enorm_add_le _ _).trans (add_le_add (enorm_add_le _ _) le_rfl)
          _ = _ := by rw [enorm_sub_rev (w j x)]
    _ = (∫⁻ x in Q, ‖u k x - w k x‖ₑ) + (∫⁻ x in Q, ‖w k x - w j x‖ₑ) +
          ∫⁻ x in Q, ‖u j x - w j x‖ₑ := by
        rw [lintegral_add_left' hkj, lintegral_add_left' hk]
    _ ≤ ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) :=
        add_le_add (add_le_add (hw k) hwkj) (hw j)
    _ = ENNReal.ofReal (3 * ε / 4) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf
    _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith)
/-- **Simon Ch. 2, proof of Theorem 2.6, compact exhaustion (step 1 of the diagonal extraction).**
If `U ⊆ ℝⁿ` is open, the sets `Q j = B_{j+1}(0) ∩ {x : 1/(j+1) ≤ infEDist x Uᶜ}` are compact, lie
in `U` and increase with `j`; indeed `Q j ⊆ interior (Q (j+1))`. Every `x ∈ U` lies in some `Q j`
since `Uᶜ` is closed, so the increasing open sets `interior (Q (j+1))` cover any compact `K ⊆ U`,
and one of them already contains `K`. -/
theorem Submission.bv_isOpen_exists_compact_exhaustion : ∀ (n : ℕ) (U : Set (Rn n)), IsOpen U → ∃ Q : ℕ → Set (Rn n), (∀ j, IsCompact (Q j)) ∧ (∀ j, Q j ⊆ U) ∧ Monotone Q ∧ ∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ j, K ⊆ Q j := by
  intro n U hU
  -- `Q j = B_{j+1}(0) ∩ {x : 1/(j+1) ≤ infEDist x Uᶜ}`; no case distinction on `U` or `n`.
  let Q : ℕ → Set (Rn n) := fun j ↦
    closedBall 0 ((j : ℝ) + 1) ∩ {x | ENNReal.ofReal (1 / ((j : ℝ) + 1)) ≤ infEDist x Uᶜ}
  -- (i) A compact ball cut by a closed superlevel set of the continuous `x ↦ infEDist x Uᶜ`.
  have hQc (j : ℕ) : IsCompact (Q j) :=
    (isCompact_closedBall 0 _).inter_right (isClosed_le continuous_const continuous_infEDist)
  -- (ii) Off `U` the distance `infEDist x Uᶜ` vanishes, while `1/(j+1) > 0`.
  have hQU (j : ℕ) : Q j ⊆ U := fun x hx ↦ by
    by_contra hxU
    have h1 : ENNReal.ofReal (1 / ((j : ℝ) + 1)) ≤ infEDist x Uᶜ := hx.2
    rw [infEDist_zero_of_mem hxU] at h1
    exact absurd h1 (not_le.2 (ENNReal.ofReal_pos.2 (by positivity)))
  -- `Q j ⊆ interior (Q (j+1))`: the open set `ball 0 (j+2) ∩ {1/(j+2) < infEDist · Uᶜ}` contains
  -- `Q j` and lies in `Q (j+1)`.
  have hQint (j : ℕ) : Q j ⊆ interior (Q (j + 1)) := fun x hx ↦ by
    have h2 : ((j + 1 : ℕ) : ℝ) + 1 = (j : ℝ) + 2 := by push_cast; ring
    have h12 : ENNReal.ofReal (1 / ((j : ℝ) + 2)) < ENNReal.ofReal (1 / ((j : ℝ) + 1)) :=
      (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2
        (one_div_lt_one_div_of_lt (by positivity) (by linarith))
    refine mem_interior.2 ⟨ball 0 ((j : ℝ) + 2) ∩
        {y | ENNReal.ofReal (1 / ((j : ℝ) + 2)) < infEDist y Uᶜ}, ?_,
      isOpen_ball.inter (isOpen_lt continuous_const continuous_infEDist), ?_⟩
    · rintro y ⟨hy1, hy2⟩
      refine ⟨mem_closedBall_zero_iff.2 ?_, ?_⟩
      · rw [h2]
        exact (mem_ball_zero_iff.1 hy1).le
      · show ENNReal.ofReal (1 / (((j + 1 : ℕ) : ℝ) + 1)) ≤ infEDist y Uᶜ
        rw [h2]
        exact le_of_lt hy2
    · have hx1 : ‖x‖ ≤ (j : ℝ) + 1 := mem_closedBall_zero_iff.1 hx.1
      have hx2 : ENNReal.ofReal (1 / ((j : ℝ) + 1)) ≤ infEDist x Uᶜ := hx.2
      exact ⟨mem_ball_zero_iff.2 (by linarith), lt_of_lt_of_le h12 hx2⟩
  -- (iii) Monotonicity from `Q j ⊆ interior (Q (j+1)) ⊆ Q (j+1)`.
  have hQm : Monotone Q := monotone_nat_of_le_succ fun j ↦ (hQint j).trans interior_subset
  -- Every `x ∈ U` lies in some `Q j`: `infEDist x Uᶜ ≠ 0` because `Uᶜ` is closed.
  have hQcover (x : Rn n) (hx : x ∈ U) : ∃ j, x ∈ Q j := by
    have hx0 : infEDist x Uᶜ ≠ 0 := fun h ↦
      (mem_iff_infEDist_zero_of_closed hU.isClosed_compl).2 h hx
    obtain ⟨m, hm⟩ := ENNReal.exists_inv_nat_lt hx0
    obtain ⟨j, hj⟩ := exists_nat_ge (max ‖x‖ (m : ℝ))
    have hmj : m ≤ j + 1 := by
      have : (m : ℝ) ≤ j := (le_max_right _ _).trans hj
      have : m ≤ j := by exact_mod_cast this
      omega
    refine ⟨j, mem_closedBall_zero_iff.2 (by linarith [le_max_left ‖x‖ (m : ℝ)]), ?_⟩
    show ENNReal.ofReal (1 / ((j : ℝ) + 1)) ≤ infEDist x Uᶜ
    calc ENNReal.ofReal (1 / ((j : ℝ) + 1)) = ((j + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
          rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity : (0 : ℝ) < (j : ℝ) + 1),
            ← Nat.cast_succ, ENNReal.ofReal_natCast]
      _ ≤ (m : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 (Nat.cast_le.2 hmj)
      _ ≤ infEDist x Uᶜ := hm.le
  -- (iv) The increasing open sets `interior (Q (j+1))` cover a compact `K ⊆ U`, so one of them
  -- contains `K`.
  refine ⟨Q, hQc, hQU, hQm, fun K hK hKU ↦ ?_⟩
  obtain ⟨j, hj⟩ := hK.elim_directed_cover (fun j ↦ interior (Q (j + 1)))
    (fun _ ↦ isOpen_interior)
    (fun x hx ↦ by
      obtain ⟨j, hj⟩ := hQcover x (hKU hx)
      exact mem_iUnion.2 ⟨j, hQint j hj⟩)
    (directed_of_isDirected_le fun i j hij ↦ interior_mono (hQm (Nat.succ_le_succ hij)))
  exact ⟨j + 1, hj.trans interior_subset⟩
/-- **One subsequence converging in `L¹` on countably many sets** (steps 0 and 2–4 of the diagonal
extraction in the proof of Simon 2.6). Let `Qⱼ ⊆ ℝⁿ` (`j ∈ ℕ`) be arbitrary sets and let every `u_k`
be integrable on every `Qⱼ`. Suppose that for every `j` and `ε > 0` finitely many `u_i` form an
`ε`-net of `{u_k}` for `∫_{Qⱼ} |· - ·|`. Then one strictly increasing `ψ` and functions `Gⱼ`, each
integrable on `Qⱼ`, satisfy `∫_{Qⱼ} |u_{ψ(k)} - Gⱼ| → 0` for every `j`. The classes
`[u_k] ∈ L¹(Qⱼ)` form a totally bounded set, so its closure `Cⱼ` is compact in the complete space
`L¹(Qⱼ)`. By Tychonoff `∏ⱼ Cⱼ` is compact in the first-countable space `∏ⱼ L¹(Qⱼ)`, so the sequence
`k ↦ ([u_k])ⱼ` has a convergent subsequence; `Gⱼ` is a representative of its `j`-th limit. -/
theorem Submission.bv_exists_subseq_tendsto_lintegral_of_finite_nets : ∀ (n : ℕ) (Q : ℕ → Set (Rn n)) (u : ℕ → Rn n → ℝ), (∀ j k, IntegrableOn (u k) (Q j) volume) → (∀ j, ∀ ε : ℝ, 0 < ε → ∃ F : Finset ℕ, ∀ k, ∃ i ∈ F, (∫⁻ x in Q j, ‖u k x - u i x‖ₑ) < ENNReal.ofReal ε) → ∃ (ψ : ℕ → ℕ) (G : ℕ → Rn n → ℝ), StrictMono ψ ∧ (∀ j, IntegrableOn (G j) (Q j) volume) ∧ ∀ j, Tendsto (fun k ↦ ∫⁻ x in Q j, ‖u (ψ k) x - G j x‖ₑ) atTop (𝓝 0) := by
  intro n Q u hint hnet
  -- Step 1: `f j k = [u k]` in the complete space `L¹(Q j)`.
  have hmem : ∀ j k, MemLp (u k) 1 (volume.restrict (Q j)) :=
    fun j k ↦ memLp_one_iff_integrable.2 (hint j k)
  let f : (j : ℕ) → ℕ → Lp ℝ 1 (volume.restrict (Q j)) := fun j k ↦ (hmem j k).toLp (u k)
  -- Step 2: the `L¹(Q j)` distances are the lower integrals of the hypotheses.
  have hdist : ∀ j k i, edist (f j k) (f j i) = ∫⁻ x in Q j, ‖u k x - u i x‖ₑ := by
    intro j k i
    rw [Lp.edist_toLp_toLp, eLpNorm_one_eq_lintegral_enorm
      ((hint j k).aestronglyMeasurable.sub (hint j i).aestronglyMeasurable)]
    rfl
  -- Step 3: the finite nets make `range (f j)` totally bounded, so its closure is compact.
  have htb : ∀ j, TotallyBounded (range (f j)) := by
    intro j
    rw [totallyBounded_iff]
    intro ε hε
    obtain ⟨F, hF⟩ := hnet j ε hε
    refine ⟨f j '' F, F.finite_toSet.image _, ?_⟩
    rintro _ ⟨k, rfl⟩
    obtain ⟨i, hiF, hi⟩ := hF k
    refine mem_iUnion₂.2 ⟨f j i, mem_image_of_mem _ hiF, ?_⟩
    rw [mem_ball, dist_edist]
    exact ENNReal.toReal_lt_of_lt_ofReal (by rw [hdist]; exact hi)
  have hcpt : ∀ j, IsCompact (closure (range (f j))) :=
    fun j ↦ (htb j).closure.isCompact_of_isClosed isClosed_closure
  -- Step 4: Tychonoff and sequential compactness in the first-countable product `∏ j, L¹(Q j)`.
  obtain ⟨a, -, ψ, hψ, hlim⟩ := (isCompact_univ_pi hcpt).tendsto_subseq
    (x := fun k j ↦ f j k) fun k ↦ mem_univ_pi.2 fun j ↦ subset_closure (mem_range_self k)
  -- Step 5: `G j = ⇑(a j)` is integrable on `Q j` and `f j (ψ k) → a j` in `L¹(Q j)`.
  refine ⟨ψ, fun j ↦ ⇑(a j), hψ, fun j ↦ memLp_one_iff_integrable.1 (Lp.memLp (a j)), fun j ↦ ?_⟩
  have h1 : Tendsto (fun k ↦ edist (f j (ψ k)) (a j)) atTop (𝓝 0) :=
    tendsto_iff_edist_tendsto_0.1 (tendsto_pi_nhds.1 hlim j)
  refine h1.congr fun k ↦ ?_
  rw [Lp.edist_def, eLpNorm_one_eq_lintegral_enorm
    ((Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _))]
  refine lintegral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (hmem j (ψ k))] with x hx
  simp only [f, Pi.sub_apply, hx]
/-- **Gluing compatible `L¹` limits along a compact exhaustion** (steps 5–8 of the diagonal extraction
in the proof of Simon 2.6). Let `U ⊆ ℝⁿ` be open and `Q₀ ⊆ Q₁ ⊆ ⋯` compact sets such that every
compact `K ⊆ U` lies in some `Qⱼ`. If every `w_k` is a.e.-strongly measurable on every `Qⱼ`, every
`Gⱼ` is integrable on `Qⱼ` and `∫_{Qⱼ} |w_k - Gⱼ| → 0` as `k → ∞`, then `w_k → v` in `L¹_loc(U)` for
some `v` that is locally integrable on `U`. For `i ≤ j` the triangle inequality gives
`∫_{Qᵢ} |Gᵢ - Gⱼ| ≤ ∫_{Qᵢ} |w_k - Gᵢ| + ∫_{Qⱼ} |w_k - Gⱼ| → 0`, so `Gᵢ = Gⱼ` a.e. on `Qᵢ`. Hence
`v(x) = G_{j(x)}(x)`, where `j(x)` is the least `j` with `x ∈ Qⱼ` (and `v = 0` off `⋃ⱼ Qⱼ`),
agrees with `Gⱼ` a.e. on every `Qⱼ`. -/
theorem Submission.bv_tendstoLocallyInL1On_of_exhaustion_limits : ∀ (n : ℕ) (U : Set (Rn n)) (Q : ℕ → Set (Rn n)) (w G : ℕ → Rn n → ℝ), IsOpen U → (∀ j, IsCompact (Q j)) → Monotone Q → (∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ j, K ⊆ Q j) → (∀ j k, AEStronglyMeasurable (w k) (volume.restrict (Q j))) → (∀ j, IntegrableOn (G j) (Q j) volume) → (∀ j, Tendsto (fun k ↦ ∫⁻ x in Q j, ‖w k x - G j x‖ₑ) atTop (𝓝 0)) → ∃ v : Rn n → ℝ, LocallyIntegrableOn v U volume ∧ Chapter02.TendstoLocallyInL1On w v U atTop := by
  intro n U Q w G hU hQc hQm hcof hw hG hlim
  -- Step 0: every `Q j` is compact, hence closed and measurable.
  have hQmeas : ∀ j, MeasurableSet (Q j) := fun j ↦ (hQc j).isClosed.measurableSet
  -- Step 1: compatibility, `G i = G j` a.e. on `Q i` for `i ≤ j`.
  have compat : ∀ i j, i ≤ j → G i =ᵐ[volume.restrict (Q i)] G j := by
    intro i j hij
    have hsub : Q i ⊆ Q j := hQm hij
    have hGi : AEStronglyMeasurable (G i) (volume.restrict (Q i)) := (hG i).aestronglyMeasurable
    have hGj : AEStronglyMeasurable (G j) (volume.restrict (Q i)) :=
      (hG j).aestronglyMeasurable.mono_measure (Measure.restrict_mono hsub le_rfl)
    have hbound : ∀ k, ∫⁻ x in Q i, ‖G i x - G j x‖ₑ ≤
        (∫⁻ x in Q i, ‖w k x - G i x‖ₑ) + ∫⁻ x in Q j, ‖w k x - G j x‖ₑ := by
      intro k
      calc ∫⁻ x in Q i, ‖G i x - G j x‖ₑ
          ≤ ∫⁻ x in Q i, (‖w k x - G i x‖ₑ + ‖w k x - G j x‖ₑ) := by
            refine lintegral_mono fun x ↦ ?_
            calc ‖G i x - G j x‖ₑ = ‖(w k x - G j x) - (w k x - G i x)‖ₑ := by congr 1; ring
              _ ≤ ‖w k x - G j x‖ₑ + ‖w k x - G i x‖ₑ := enorm_sub_le
              _ = ‖w k x - G i x‖ₑ + ‖w k x - G j x‖ₑ := add_comm _ _
        _ = (∫⁻ x in Q i, ‖w k x - G i x‖ₑ) + ∫⁻ x in Q i, ‖w k x - G j x‖ₑ :=
            lintegral_add_left' ((hw i k).sub hGi).enorm _
        _ ≤ (∫⁻ x in Q i, ‖w k x - G i x‖ₑ) + ∫⁻ x in Q j, ‖w k x - G j x‖ₑ :=
            add_le_add le_rfl (lintegral_mono_set hsub)
    have hzero : ∫⁻ x in Q i, ‖G i x - G j x‖ₑ = 0 := by
      have hT : Tendsto (fun k ↦ (∫⁻ x in Q i, ‖w k x - G i x‖ₑ) +
          ∫⁻ x in Q j, ‖w k x - G j x‖ₑ) atTop (𝓝 0) := by
        simpa using (hlim i).add (hlim j)
      exact le_antisymm (ge_of_tendsto' hT hbound) zero_le
    filter_upwards [(lintegral_eq_zero_iff' (hGi.sub hGj).enorm).1 hzero] with x hx
    simpa [sub_eq_zero] using hx
  -- Step 2: gluing, `v x = G (j x) x` with `j x` the least `j` such that `x ∈ Q j`.
  classical
  let v : Rn n → ℝ := fun x ↦ if h : ∃ j, x ∈ Q j then G (Nat.find h) x else 0
  have hv : ∀ j, v =ᵐ[volume.restrict (Q j)] G j := by
    intro j
    have h1 : ∀ i, ∀ᵐ x ∂(volume : Measure (Rn n)), i ≤ j → x ∈ Q i → G i x = G j x := by
      intro i
      by_cases hij : i ≤ j
      · filter_upwards [(ae_restrict_iff' (hQmeas i)).1 (compat i j hij)] with x hx _ hxi
        exact hx hxi
      · exact Eventually.of_forall fun x h ↦ absurd h hij
    rw [EventuallyEq, ae_restrict_iff' (hQmeas j)]
    filter_upwards [ae_all_iff.2 h1] with x hx hxj
    have hex : ∃ j, x ∈ Q j := ⟨j, hxj⟩
    simp only [v, hex, ↓reduceDIte]
    exact hx _ (Nat.find_min' hex hxj) (Nat.find_spec hex)
  -- Step 3: `v` is integrable on every `Q j`.
  have hvint : ∀ j, IntegrableOn v (Q j) volume := fun j ↦ (hG j).congr_fun_ae (hv j).symm
  refine ⟨v, ?_, ?_⟩
  · -- Step 5: local integrability on the open set `U`.
    rw [locallyIntegrableOn_iff hU.isLocallyClosed]
    intro K hKU hK
    obtain ⟨j, hj⟩ := hcof K hK hKU
    exact (hvint j).mono_set hj
  · -- Step 4: convergence on every compact `K ⊆ U`, squeezed by `∫⁻_{Q j} ‖w k - G j‖ₑ → 0`.
    intro K hK hKU
    obtain ⟨j, hj⟩ := hcof K hK hKU
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hlim j)
      (fun _ ↦ zero_le) fun k ↦ ?_
    calc ∫⁻ x in K, ‖w k x - v x‖ₑ ≤ ∫⁻ x in Q j, ‖w k x - v x‖ₑ := lintegral_mono_set hj
      _ = ∫⁻ x in Q j, ‖w k x - G j x‖ₑ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hv j] with x hx
        rw [hx]

/-- **Diagonal extraction in `L¹_loc(U)`** (step A2 of the proof of Simon Ch. 2, Theorem 2.6,
p. 50). Let `U ⊆ ℝⁿ` be open and every `u_k` locally integrable on `U`. Suppose that for every
compact `Q ⊆ U` and `ε > 0` finitely many `u_j` form an `ε`-net of `{u_k}` for `∫_Q |· - ·|`. Then a
subsequence `u_{ψ(k)}` converges in `L¹_loc(U)` to some `v` that is locally integrable on `U`.
Choose a compact exhaustion `Q₀ ⊆ Q₁ ⊆ ⋯` of `U`; every `u_k` is integrable on every `Qⱼ`, so one
strictly increasing `ψ` and functions `Gⱼ` satisfy `∫_{Qⱼ} |u_{ψ(k)} - Gⱼ| → 0` for every `j`, and
the `Gⱼ` glue to the limit `v`. -/
theorem Submission.bv_exists_subseq_tendstoLocallyInL1On : ∀ (n : ℕ) (U : Set (Rn n)) (u : ℕ → Rn n → ℝ), IsOpen U → (∀ k, LocallyIntegrableOn (u k) U volume) → (∀ Q : Set (Rn n), IsCompact Q → Q ⊆ U → ∀ ε : ℝ, 0 < ε → ∃ F : Finset ℕ, ∀ k, ∃ j ∈ F, (∫⁻ x in Q, ‖u k x - u j x‖ₑ) < ENNReal.ofReal ε) → ∃ (ψ : ℕ → ℕ) (v : Rn n → ℝ), StrictMono ψ ∧ LocallyIntegrableOn v U volume ∧ Chapter02.TendstoLocallyInL1On (fun k ↦ u (ψ k)) v U atTop := by
  intro n U u hU hloc hnet
  -- Step 1: a compact exhaustion `Q 0 ⊆ Q 1 ⊆ ⋯` of `U`.
  obtain ⟨Q, hQc, hQU, hQm, hcof⟩ := Submission.bv_isOpen_exists_compact_exhaustion n U hU
  -- Every `u k` is integrable on every compact `Q j ⊆ U`.
  have hint : ∀ j k, IntegrableOn (u k) (Q j) volume :=
    fun j k ↦ (hloc k).integrableOn_compact_subset (hQU j) (hQc j)
  -- Steps 2–4: the finite nets on each `Q j` give one subsequence converging in every `L¹(Q j)`.
  obtain ⟨ψ, G, hψ, hG, hlim⟩ := Submission.bv_exists_subseq_tendsto_lintegral_of_finite_nets n Q
    u hint fun j ε hε ↦ hnet (Q j) (hQc j) (hQU j) ε hε
  -- Steps 5–8: glue the compatible limits `G j` into `v`.
  obtain ⟨v, hv, hconv⟩ := Submission.bv_tendstoLocallyInL1On_of_exhaustion_limits n U Q
    (fun k ↦ u (ψ k)) G hU hQc hQm hcof (fun j k ↦ (hint j (ψ k)).aestronglyMeasurable) hG hlim
  exact ⟨ψ, v, hψ, hv, hconv⟩

/-- The frozen Chapter 2 contract: the conjunction of all headline results. -/
theorem main_theorem : LipschitzExtension ∧ Rademacher ∧ C1Approximation ∧ WhitneyExtension ∧ LipschitzImageHausdorff ∧ EilenbergInequality ∧ BVCompactness ∧ BVPoincare ∧ BVExtensionEstimate ∧ AreaFormula ∧ FirstVariation ∧ SecondVariation ∧ StationaryIffMeanCurvatureZero ∧ SecondVariationStationary ∧ CoareaFormula ∧ C1Sard := by sorry

end GMT.Ch02
