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

/-- **Simon Ch. 2, §6 (p. 66), toward Theorem 6.4.** `J*_f(x) = 0` precisely when `df_x` has rank
`< m`: with `L = Df(x) ∘ ι : T_x M → ℝᵐ`, `L L*` is positive semidefinite, so `√det(L L*) = 0` iff
`L L*` is singular, iff `ker L* = (range L)ᗮ ≠ 0`, iff `range L ≠ ℝᵐ`. No hypothesis on `M`, `f` or
`x` is needed. -/
theorem Submission.c1_sard_coarea_jacobian_eq_zero_iff : ∀ (N m : ℕ) (M : Set (Rn N)) (f : Rn N → Rn m) (x : Rn N), coareaJacobian M f x = 0 ↔ Module.finrank ℝ (LinearMap.range ((fderiv ℝ f x).toLinearMap ∘ₗ (tangentSpace M x).subtype)) < m := by
  intro N m M f x
  -- `L = Df(x) ∘ ι : T_x M → ℝᵐ`; by definition `J*_f(x) = √det(L L*)`.
  set L : tangentSpace M x →ₗ[ℝ] Rn m := (fderiv ℝ f x).toLinearMap ∘ₗ (tangentSpace M x).subtype
  have hJ : coareaJacobian M f x = Real.sqrt (L ∘ₗ L.adjoint).det := rfl
  -- Step 1: `det(L L*) = (normDet L*)² ≥ 0`, as `L** = L`.
  have hdet : 0 ≤ (L ∘ₗ L.adjoint).det := by
    have hsq : L.adjoint.normDet ^ 2 = (L ∘ₗ L.adjoint).det := by
      simpa using L.adjoint.normDet_sq
    exact hsq ▸ sq_nonneg _
  -- Steps 2–4: `√det(L L*) = 0 ↔ det(L L*) = 0 ↔ ker(L L*) ≠ 0`, and `ker(L L*) = ker L*`.
  rw [hJ, Real.sqrt_eq_zero hdet, LinearMap.det_eq_zero_iff_ker_ne_bot,
    LinearMap.ker_self_comp_adjoint]
  -- Step 5: `ker L* = (range L)ᗮ`, which is `0` iff `range L = ℝᵐ`.
  rw [← LinearMap.orthogonal_range, ne_eq, Submodule.orthogonal_eq_bot_iff]
  -- Step 6: a subspace of `ℝᵐ` is proper iff its dimension is `< m = dim ℝᵐ`.
  have hm : Module.finrank ℝ (Rn m) = m := finrank_euclideanSpace_fin
  refine ⟨fun h ↦ (Submodule.finrank_lt h).trans_eq hm, fun h htop ↦ ?_⟩
  rw [htop, finrank_top, hm] at h
  exact lt_irrefl m h
/-- **Simon Ch. 2, §6 (pp. 66–67), toward Theorem 6.4.** If `f` is `C¹` on an open `U ⊇ M` and
the tangent projection `x ↦ P_x` is continuous on `M`, then `J*_f` is continuous on `M`: the
adjoint of the inclusion `T_x M → ℝᴺ` is the orthogonal projection onto `T_x M`, so
`df_x ∘ df_x* = Df(x) ∘ P_x ∘ Df(x)*`. Hence for every `y` the critical part
`M ∩ f⁻¹{y} ∩ {J*_f = 0}` of the fiber is relatively closed in `M`. -/
theorem Submission.c1_sard_coarea_jacobian_continuousOn : ∀ (N m : ℕ) (M U : Set (Rn N)) (f : Rn N → Rn m), IsOpen U → M ⊆ U → ContDiffOn ℝ 1 f U → ContinuousOn (tangentProjection M) M → ContinuousOn (coareaJacobian M f) M ∧ ∀ y : Rn m, ∃ F : Set (Rn N), IsClosed F ∧ M ∩ f ⁻¹' {y} ∩ {x | coareaJacobian M f x = 0} = M ∩ F := by
  intro N m M U f hU hMU hf hP
  -- `(Df(x) ∘ ι)(Df(x) ∘ ι)* = Df(x) ∘ (ι ∘ π) ∘ Df(x)*`, as `ι* = π` and `ι ∘ π = P_x`.
  have key : ∀ x, coareaJacobian M f x = Real.sqrt ((fderiv ℝ f x ∘L
      (tangentProjection M x ∘L ContinuousLinearMap.adjoint (fderiv ℝ f x))).det) := by
    intro x
    simp only [coareaJacobian]
    congr 2
    rw [ContinuousLinearMap.adjoint_comp, Submodule.adjoint_subtypeL]
    rfl
  have hJ : ContinuousOn (coareaJacobian M f) M := by
    have hD : ContinuousOn (fderiv ℝ f) M := (hf.continuousOn_fderiv_of_isOpen hU le_rfl).mono hMU
    have hD' : ContinuousOn (fun x ↦ ContinuousLinearMap.adjoint (fderiv ℝ f x)) M :=
      (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Rn N) (F := Rn m)).continuous.comp_continuousOn hD
    refine ContinuousOn.congr ?_ fun x _ ↦ key x
    exact Real.continuous_sqrt.comp_continuousOn
      (ContinuousLinearMap.continuous_det.comp_continuousOn (hD.clm_comp (hP.clm_comp hD')))
  refine ⟨hJ, fun y ↦ ?_⟩
  -- `S = M ∩ f⁻¹{y} ∩ {J*_f = 0}` satisfies `S = M ∩ closure S`, as `f` and `J*_f` are continuous
  -- on `M ⊇ S`.
  set S := M ∩ f ⁻¹' {y} ∩ {x | coareaJacobian M f x = 0}
  refine ⟨closure S, isClosed_closure, Subset.antisymm (fun x hx ↦ ⟨hx.1.1, subset_closure hx⟩) ?_⟩
  rintro x ⟨hxM, hxS⟩
  have hSM : S ⊆ M := fun z hz ↦ hz.1.1
  have hfx : f x ∈ closure {y} :=
    (((hf.continuousOn.mono hMU) x hxM).mono hSM).mem_closure hxS fun z hz ↦ hz.1.2
  have hJx : coareaJacobian M f x ∈ closure {0} :=
    ((hJ x hxM).mono hSM).mem_closure hxS fun z hz ↦ hz.2
  rw [closure_singleton] at hfx hJx
  exact ⟨⟨hxM, hfx⟩, hJx⟩
/-- **Simon Ch. 2, §6 (p. 66), consequence of 6.3.** Given the co-area formula, the critical set
`C = {x ∈ M : J*_f(x) = 0}` meets `Lᵐ`-a.e. fiber `f⁻¹(y)` in an `Hᵏ`-null set: use 6.3 with
`g = 1_C`, for which the integrand `1_C J*_f` vanishes identically. `C` is measurable because `M`
is measurable and `J*_f` is continuous on `M`. -/
theorem Submission.c1_sard_critical_fibers_null : CoareaFormula → ∀ (N m k : ℕ) (M U : Set (Rn N)) (f : Rn N → Rn m), 0 < k → Chapter02.IsSimonSubmanifold (E := Rn (m + k)) 1 M → IsOpen U → M ⊆ U → ContDiffOn ℝ 1 f U → MeasurableSet M → ContinuousOn (coareaJacobian M f) M → ∀ᵐ y ∂(volume : Measure (Rn m)), μHE[k] (M ∩ f ⁻¹' {y} ∩ {x | coareaJacobian M f x = 0}) = 0 := by
  intro hco N m k M U f hk hM hU hMU hf hMmeas hJ
  -- `C = M ∩ {J*_f = 0}` is relatively closed in the measurable set `M`.
  obtain ⟨F₀, hF₀, h₀⟩ := continuousOn_iff_isClosed.mp hJ {0} isClosed_singleton
  set C : Set (Rn N) := M ∩ {x | coareaJacobian M f x = 0}
  have hC : C = M ∩ F₀ := by
    ext x; constructor
    · rintro ⟨hxM, hx⟩
      have : x ∈ F₀ ∩ M := h₀ ▸ ⟨hx, hxM⟩
      exact ⟨hxM, this.1⟩
    · rintro ⟨hxM, hx⟩
      have : x ∈ coareaJacobian M f ⁻¹' {0} ∩ M := h₀.symm ▸ ⟨hx, hxM⟩
      exact ⟨hxM, this.1⟩
  have hCmeas : MeasurableSet C := hC ▸ hMmeas.inter hF₀.measurableSet
  -- Co-area formula with `g = 1_C`: the left side is `0`, so the fiber integrals vanish a.e.
  set g : Rn N → ℝ≥0∞ := C.indicator 1
  have hgm : AEMeasurable g (μHE[m + k].restrict M) :=
    (measurable_one.indicator hCmeas).aemeasurable
  obtain ⟨hAEM, hEq⟩ := hco N m k M U f g hk hM hU hMU hf hgm
  have hLHS : (fun x => g x * ENNReal.ofReal (coareaJacobian M f x)) = 0 := by
    funext x
    by_cases hx : x ∈ C
    · have hx2 : coareaJacobian M f x = 0 := hx.2
      simp [hx2]
    · simp [g, hx]
  rw [hLHS] at hEq
  have hEq0 : ∫⁻ y, ∫⁻ x in M ∩ f ⁻¹' {y}, g x ∂μHE[k] ∂(volume : Measure (Rn m)) = 0 := by
    rw [← hEq]; exact lintegral_zero
  have hae := (lintegral_eq_zero_iff' hAEM).mp hEq0
  -- The fiber integral of `1_C` is the `Hᵏ`-measure of the critical part of the fiber.
  filter_upwards [hae] with y hy
  have hinner : ∫⁻ x in M ∩ f ⁻¹' {y}, g x ∂μHE[k] =
      μHE[k] (M ∩ f ⁻¹' {y} ∩ {x | coareaJacobian M f x = 0}) := by
    rw [lintegral_indicator_one hCmeas, Measure.restrict_apply hCmeas]
    congr 1
    ext x; constructor
    · rintro ⟨⟨hxM, hxZ⟩, hxM', hxy⟩; exact ⟨⟨hxM, hxy⟩, hxZ⟩
    · rintro ⟨⟨hxM, hxy⟩, hxZ⟩; exact ⟨⟨hxM, hxZ⟩, hxM, hxy⟩
  rw [← hinner]; exact hy
/-- **Simon Ch. 2, §6 (pp. 66–67), level sets of a submersion.** If `G` is `C¹` on the open set
`V ∋ x₀` and `DG(x₀)` is onto, then near `x₀` the level set `G⁻¹{G x₀}` has a `C¹` Simon local
representation (Simon 4.1) inside `V`. Let `π = e ∘ P_K`, where `P_K` is the orthogonal projection
onto `K = ker DG(x₀)` and `e : K ≃ ℝᵏ`. Then `Φ(x) = (G x, π(x - x₀))` has invertible derivative at
`x₀`, and by the inverse function theorem `l(z) = Φ⁻¹(G x₀, z)` on a small ball `D` is the chart. -/
theorem Submission.c1_sard_submersion_level_set_chart : ∀ (m k : ℕ) (V : Set (Rn (m + k))) (G : Rn (m + k) → Rn m) (x₀ : Rn (m + k)), IsOpen V → x₀ ∈ V → ContDiffOn ℝ 1 G V → Function.Surjective (fderiv ℝ G x₀) → ∃ (D : Set (Rn k)) (V₁ : Set (Rn (m + k))) (l : Rn k → Rn (m + k)), x₀ ∈ V₁ ∧ V₁ ⊆ V ∧ Chapter02.IsSimonLocalRepresentation 1 (G ⁻¹' {G x₀}) D V₁ l := by
  intro m k V G x₀ hV hx₀ hG hsurj
  -- `K = ker DG(x₀)` has dimension `k`; `π = e ∘ P_K` with `e : K ≃ ℝᵏ`.
  set A : Rn (m + k) →L[ℝ] Rn m := fderiv ℝ G x₀
  set K : Submodule ℝ (Rn (m + k)) := LinearMap.ker (A : Rn (m + k) →ₗ[ℝ] Rn m) with hK
  have hrange : LinearMap.range (A : Rn (m + k) →ₗ[ℝ] Rn m) = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hKdim : Module.finrank ℝ K = Module.finrank ℝ (Rn k) := by
    have h := LinearMap.finrank_range_add_finrank_ker (A : Rn (m + k) →ₗ[ℝ] Rn m)
    rw [hrange, finrank_top, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin, ← hK] at h
    rw [finrank_euclideanSpace_fin]
    omega
  let e : K ≃ₗ[ℝ] Rn k := LinearEquiv.ofFinrankEq K (Rn k) hKdim
  let π : Rn (m + k) →L[ℝ] Rn k :=
    (e.toContinuousLinearEquiv : K →L[ℝ] Rn k) ∘L K.orthogonalProjectionOnto
  have hπK : ∀ v : K, π v = e v := by
    intro v
    simp [π]
  -- `Φ(x) = (G x, π(x - x₀))` is `C¹` on `V` with `DΦ(x) = (DG(x), π)`.
  let Φ : Rn (m + k) → Rn m × Rn k := fun x => (G x, π (x - x₀))
  have hπaff : ContDiff ℝ 1 (fun x : Rn (m + k) => π (x - x₀)) :=
    π.contDiff.comp (contDiff_id.sub contDiff_const)
  have hΦC : ContDiffOn ℝ 1 Φ V := hG.prodMk hπaff.contDiffOn
  have hΦCA : ∀ x ∈ V, ContDiffAt ℝ 1 Φ x := fun x hx => hΦC.contDiffAt (hV.mem_nhds hx)
  have hπd : ∀ x, HasFDerivAt (fun x : Rn (m + k) => π (x - x₀)) π x := by
    intro x
    have h1 : HasFDerivAt (fun x : Rn (m + k) => x - x₀) (ContinuousLinearMap.id ℝ (Rn (m + k))) x :=
      (hasFDerivAt_id x).sub_const x₀
    have h2 := (π.hasFDerivAt (x := x - x₀)).comp x h1
    rw [ContinuousLinearMap.comp_id] at h2
    exact h2
  have hΦd : ∀ x ∈ V, HasFDerivAt Φ ((fderiv ℝ G x).prod π) x := by
    intro x hx
    have hGx : HasFDerivAt G (fderiv ℝ G x) x :=
      ((hG.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds hx)).hasFDerivAt
    exact hGx.prodMk (hπd x)
  -- `DΦ(x₀) = (A, π)` is injective, hence (equal dimensions) a linear isomorphism `Φ'`.
  have hinj : Function.Injective (A.prod π) := by
    intro v w hvw
    have h1 : A v = A w := congrArg Prod.fst hvw
    have h2 : π v = π w := congrArg Prod.snd hvw
    have hmem : v - w ∈ K := by
      show A (v - w) = 0
      rw [map_sub, h1, sub_self]
    have h3 : e ⟨v - w, hmem⟩ = e 0 := by
      rw [← hπK, map_zero]
      show π (v - w) = 0
      rw [map_sub, h2, sub_self]
    have := congrArg Subtype.val (e.injective h3)
    simpa [sub_eq_zero] using this
  have hdim : Module.finrank ℝ (Rn (m + k)) = Module.finrank ℝ (Rn m × Rn k) := by
    rw [Module.finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin,
      finrank_euclideanSpace_fin]
  have hsurjΦ : Function.Surjective (A.prod π) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  let Φ' : Rn (m + k) ≃L[ℝ] Rn m × Rn k :=
    (LinearEquiv.ofBijective ((A.prod π : Rn (m + k) →L[ℝ] Rn m × Rn k) :
      Rn (m + k) →ₗ[ℝ] Rn m × Rn k) ⟨hinj, hsurjΦ⟩).toContinuousLinearEquiv
  have hΦ'd : HasFDerivAt Φ (Φ' : Rn (m + k) →L[ℝ] Rn m × Rn k) x₀ := by
    have : (Φ' : Rn (m + k) →L[ℝ] Rn m × Rn k) = A.prod π := by ext1 v; rfl
    rw [this]; exact hΦd x₀ hx₀
  -- Inverse function theorem: a local homeomorphism `h = Φ` near `x₀`.
  have hΦs : HasStrictFDerivAt Φ (Φ' : Rn (m + k) →L[ℝ] Rn m × Rn k) x₀ :=
    (hΦCA x₀ hx₀).hasStrictFDerivAt' hΦ'd one_ne_zero
  let h := hΦs.toOpenPartialHomeomorph Φ
  -- Restrict `h` to the open set `Vinv ⊆ V` where `DΦ` is invertible.
  set Vinv : Set (Rn (m + k)) := V ∩ (fderiv ℝ Φ) ⁻¹'
    (range ((↑) : (Rn (m + k) ≃L[ℝ] Rn m × Rn k) → Rn (m + k) →L[ℝ] Rn m × Rn k))
  have hVinvo : IsOpen Vinv :=
    (hΦC.continuousOn_fderiv_of_isOpen hV le_rfl).isOpen_inter_preimage hV
      ContinuousLinearEquiv.isOpen
  have hx₀inv : x₀ ∈ Vinv := ⟨hx₀, Φ', (hΦ'd.fderiv).symm⟩
  let h' := h.restrOpen Vinv hVinvo
  have hh' : (h' : Rn (m + k) → Rn m × Rn k) = Φ := rfl
  have hx₀src : x₀ ∈ h'.source := ⟨hΦs.mem_toOpenPartialHomeomorph_source, hx₀inv⟩
  have hsrcV : h'.source ⊆ V := fun x hx => hx.2.1
  have hΦx₀ : Φ x₀ = (G x₀, 0) := by simp [Φ]
  have htgt : (G x₀, (0 : Rn k)) ∈ h'.target := by
    rw [← hΦx₀, ← hh']; exact h'.map_source hx₀src
  -- A box `O = B(G x₀, ε) × B(0, ε)` inside the target.
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp h'.open_target _ htgt
  set O : Set (Rn m × Rn k) := ball (G x₀) ε ×ˢ ball (0 : Rn k) ε with hO
  have hOt : O ⊆ h'.target := by rw [hO, ball_prod_same]; exact hball
  have hjO : ∀ z ∈ ball (0 : Rn k) ε, ((G x₀, z) : Rn m × Rn k) ∈ O :=
    fun z hz => ⟨mem_ball_self hε, hz⟩
  -- On the target, `h'⁻¹` is `C¹` with invertible derivative.
  have hsymm : ∀ ω ∈ h'.target, ∃ eqv : Rn (m + k) ≃L[ℝ] Rn m × Rn k,
      HasFDerivAt h'.symm (eqv.symm : Rn m × Rn k →L[ℝ] Rn (m + k)) ω ∧
        ContDiffAt ℝ 1 h'.symm ω := by
    intro ω hω
    have hxs : h'.symm ω ∈ h'.source := h'.map_target hω
    obtain ⟨eqv, heqv⟩ := hxs.2.2
    have hxV : h'.symm ω ∈ V := hxs.2.1
    have hd : HasFDerivAt h' (eqv : Rn (m + k) →L[ℝ] Rn m × Rn k) (h'.symm ω) := by
      rw [heqv]; exact ((hΦCA _ hxV).differentiableAt one_ne_zero).hasFDerivAt
    exact ⟨eqv, h'.hasFDerivAt_symm hω hd, h'.contDiffAt_symm hω hd (hΦCA _ hxV)⟩
  -- The chart: `D = B(0, ε)`, `V₁ = source ∩ Φ⁻¹ O`, `l(z) = h'⁻¹(G x₀, z)`.
  refine ⟨ball (0 : Rn k) ε, h'.source ∩ Φ ⁻¹' O, fun z => h'.symm (G x₀, z),
    ⟨hx₀src, ?_⟩, fun x hx => hsrcV hx.1, ?_⟩
  · rw [Set.mem_preimage, hΦx₀]; exact ⟨mem_ball_self hε, mem_ball_self hε⟩
  refine ⟨isOpen_ball, h'.isOpen_inter_preimage (isOpen_ball.prod isOpen_ball), ?_, ?_, ?_, ?_, ?_⟩
  · -- `l` is `C¹` on `D`
    intro z hz
    obtain ⟨eqv, -, hcd⟩ := hsymm _ (hOt (hjO z hz))
    exact (hcd.comp z (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt
  · -- `l` is injective on `D`
    intro z hz z' hz' hzz
    have h1 := h'.right_inv (hOt (hjO z hz))
    have h2 := h'.right_inv (hOt (hjO z' hz'))
    have := congrArg h' hzz
    simp only at this
    rw [h1, h2] at this
    exact (Prod.mk.inj this).2
  · -- `l(D) = V₁ ∩ G⁻¹{G x₀}`
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hω := hOt (hjO z hz)
      refine ⟨⟨h'.map_target hω, ?_⟩, ?_⟩
      · show Φ (h'.symm (G x₀, z)) ∈ O
        rw [← hh', h'.right_inv hω]; exact hjO z hz
      · show G (h'.symm (G x₀, z)) = G x₀
        exact congrArg Prod.fst (h'.right_inv hω)
    · rintro ⟨⟨hxs, hxO⟩, hxG⟩
      have hxG' : G x = G x₀ := hxG
      refine ⟨π (x - x₀), hxO.2, ?_⟩
      show h'.symm (G x₀, π (x - x₀)) = x
      have : ((G x₀, π (x - x₀)) : Rn m × Rn k) = h' x := by rw [hh']; simp [Φ, hxG']
      rw [this, h'.left_inv hxs]
  · -- properness: `D ∩ l⁻¹ Q` is a closed slice of the compact set `Φ(Q)`
    intro Q hQ hQV₁
    have hΦQ : IsCompact (Φ '' Q) :=
      hQ.image_of_continuousOn (hΦC.continuousOn.mono (fun x hx => hsrcV (hQV₁ hx).1))
    have heq : ball (0 : Rn k) ε ∩ (fun z => h'.symm (G x₀, z)) ⁻¹' Q =
        (fun z : Rn k => ((G x₀, z) : Rn m × Rn k)) ⁻¹' (Φ '' Q) := by
      ext z
      constructor
      · rintro ⟨hz, hzQ⟩
        refine ⟨_, hzQ, ?_⟩
        rw [← hh', h'.right_inv (hOt (hjO z hz))]
      · rintro ⟨q, hq, hqz⟩
        have hqz' : Φ q = (G x₀, z) := hqz
        have hqO : Φ q ∈ O := (hQV₁ hq).2
        rw [hqz'] at hqO
        refine ⟨hqO.2, ?_⟩
        show h'.symm (G x₀, z) ∈ Q
        rw [← hqz', ← hh', h'.left_inv (hQV₁ hq).1]; exact hq
    rw [heq]
    refine (hΦQ.image continuous_snd).of_isClosed_subset
      (hΦQ.isClosed.preimage (continuous_const.prodMk continuous_id)) ?_
    intro z hz
    exact ⟨_, hz, rfl⟩
  · -- `Dl(z) = (DΦ)⁻¹ ∘ (0, ·)` is injective
    intro z hz
    obtain ⟨eqv, hd, -⟩ := hsymm _ (hOt (hjO z hz))
    have hj : HasFDerivAt (fun z : Rn k => ((G x₀, z) : Rn m × Rn k))
        ((0 : Rn k →L[ℝ] Rn m).prod (ContinuousLinearMap.id ℝ (Rn k))) z :=
      (hasFDerivAt_const (G x₀) z).prodMk (hasFDerivAt_id z)
    have hcomp := hd.comp z hj
    rw [show (fun z => h'.symm (G x₀, z)) =
      h'.symm ∘ (fun z : Rn k => ((G x₀, z) : Rn m × Rn k)) from rfl, hcomp.fderiv,
      ContinuousLinearMap.coe_comp]
    refine eqv.symm.injective.comp ?_
    intro a b hab
    have := congrArg Prod.snd hab
    simpa using this
/-- **Simon Ch. 2, 4.1–4.2 (p. 55), composition of local representations.** If `(V, W, ψ)` is a
`C¹` local representation of `M`, `S ⊆ M`, and `(D, V₁, l)` is a `C¹` local representation of
`ψ⁻¹(S)` with `V₁ ⊆ V`, then `ψ(V₁) = W₁ ∩ M` for some open `W₁ ⊆ W` (4.2: by relative
properness, `ψ(V \ V₁)` is closed relative to `W`), and `(D, W₁, ψ ∘ l)` is a `C¹` local
representation of `S`. -/
theorem Submission.c1_sard_local_representation_comp : ∀ (n k N : ℕ) (M S : Set (Rn N)) (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N) (D : Set (Rn k)) (V₁ : Set (Rn n)) (l : Rn k → Rn n), Chapter02.IsSimonLocalRepresentation 1 M V W ψ → S ⊆ M → V₁ ⊆ V → Chapter02.IsSimonLocalRepresentation 1 (ψ ⁻¹' S) D V₁ l → ∃ W₁ : Set (Rn N), W₁ ⊆ W ∧ ψ '' V₁ = W₁ ∩ M ∧ Chapter02.IsSimonLocalRepresentation 1 S D W₁ (ψ ∘ l) := by
  intro n k N M S V W ψ D V₁ l hψ hSM hV₁V hl
  obtain ⟨hV, hW, hψC, hψinj, hψimg, hψprop, hψder⟩ := hψ
  obtain ⟨hD, hV₁, hlC, hlinj, hlimg, hlprop, hlder⟩ := hl
  -- Simon 4.2: `ψ(V \ V₁)` is closed relative to `W`. Near `y ∈ W` it lies in the image of the
  -- compact set `(V ∩ ψ⁻¹(B̄)) \ V₁`, where `B̄ ⊆ W` is a closed ball about `y`.
  have hrel : ∀ y ∈ W, y ∈ closure (ψ '' (V \ V₁)) → y ∈ ψ '' (V \ V₁) := by
    intro y hyW hycl
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hW y hyW
    have hQW : closedBall y (r / 2) ⊆ W := (closedBall_subset_ball (half_lt_self hr)).trans hball
    have hK : IsCompact (ψ '' (V ∩ ψ ⁻¹' closedBall y (r / 2) ∩ V₁ᶜ)) :=
      ((hψprop _ (isCompact_closedBall y (r / 2)) hQW).inter_right
        hV₁.isClosed_compl).image_of_continuousOn (hψC.continuousOn.mono fun x hx => hx.1.1)
    have hsub :
        ball y (r / 2) ∩ ψ '' (V \ V₁) ⊆ ψ '' (V ∩ ψ ⁻¹' closedBall y (r / 2) ∩ V₁ᶜ) := by
      rintro _ ⟨hyb, x, ⟨hxV, hxV₁⟩, rfl⟩
      exact ⟨x, ⟨⟨hxV, ball_subset_closedBall hyb⟩, hxV₁⟩, rfl⟩
    obtain ⟨x, ⟨⟨hxV, -⟩, hxV₁⟩, hxy⟩ := closure_minimal hsub hK.isClosed
      (isOpen_ball.inter_closure ⟨mem_ball_self (half_pos hr), hycl⟩)
    exact ⟨x, ⟨hxV, hxV₁⟩, hxy⟩
  obtain ⟨W₁, hW₁, hW₁W, hW₁img⟩ : ∃ W₁ : Set (Rn N), IsOpen W₁ ∧ W₁ ⊆ W ∧ ψ '' V₁ = W₁ ∩ M := by
    refine ⟨W \ closure (ψ '' (V \ V₁)), hW.sdiff isClosed_closure, sdiff_subset, ?_⟩
    ext y
    constructor
    · rintro ⟨x, hxV₁, rfl⟩
      have hxM : ψ x ∈ W ∩ M := by rw [← hψimg]; exact ⟨x, hV₁V hxV₁, rfl⟩
      refine ⟨⟨hxM.1, fun hcl => ?_⟩, hxM.2⟩
      obtain ⟨x', ⟨hx'V, hx'V₁⟩, hx'⟩ := hrel _ hxM.1 hcl
      rw [hψinj hx'V (hV₁V hxV₁) hx'] at hx'V₁
      exact hx'V₁ hxV₁
    · rintro ⟨⟨hyW, hycl⟩, hyM⟩
      obtain ⟨x, hxV, rfl⟩ : y ∈ ψ '' V := by rw [hψimg]; exact ⟨hyW, hyM⟩
      by_cases hx : x ∈ V₁
      · exact ⟨x, hx, rfl⟩
      · exact (hycl (subset_closure ⟨x, ⟨hxV, hx⟩, rfl⟩)).elim
  have hlD : MapsTo l D V₁ := fun z hz => by
    have : l z ∈ l '' D := ⟨z, hz, rfl⟩
    rw [hlimg] at this; exact this.1
  refine ⟨W₁, hW₁W, hW₁img, hD, hW₁, ?_, ?_, ?_, ?_, ?_⟩
  · exact hψC.comp hlC (hlD.mono_right hV₁V)
  · exact hψinj.comp hlinj (hlD.mono_right hV₁V)
  · rw [image_comp, hlimg, image_inter_preimage, hW₁img, inter_assoc, inter_eq_right.mpr hSM]
  · intro Q hQ hQW₁
    have hK := hψprop Q hQ (hQW₁.trans hW₁W)
    have hKV₁ : V ∩ ψ ⁻¹' Q ⊆ V₁ := by
      rintro x ⟨hxV, hxQ⟩
      have hxM : ψ x ∈ W ∩ M := by rw [← hψimg]; exact ⟨x, hxV, rfl⟩
      have : ψ x ∈ ψ '' V₁ := by rw [hW₁img]; exact ⟨hQW₁ hxQ, hxM.2⟩
      obtain ⟨x', hx'V₁, hx'⟩ := this
      rw [← hψinj (hV₁V hx'V₁) hxV hx']
      exact hx'V₁
    have heq : D ∩ (ψ ∘ l) ⁻¹' Q = D ∩ l ⁻¹' (V ∩ ψ ⁻¹' Q) := by
      ext z
      constructor
      · rintro ⟨hz, hzQ⟩; exact ⟨hz, hV₁V (hlD hz), hzQ⟩
      · rintro ⟨hz, _, hzQ⟩; exact ⟨hz, hzQ⟩
    rw [heq]
    exact hlprop _ hK hKV₁
  · intro z hz
    have hlz : l z ∈ V := hV₁V (hlD hz)
    have hdψ : DifferentiableAt ℝ ψ (l z) :=
      (hψC.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds hlz)
    have hdl : DifferentiableAt ℝ l z :=
      (hlC.differentiableOn one_ne_zero).differentiableAt (hD.mem_nhds hz)
    rw [fderiv_comp z hdψ hdl, ContinuousLinearMap.coe_comp]
    exact (hψder (l z) hlz).comp (hlder z hz)

/-- **Simon Ch. 2, Theorem 6.4 (p. 67), regular fibres** (steps 6, 7 and 11 of the `C1Sard`
proof). Fix `p ∈ Σ_y = (M ∩ f⁻¹{y}) \ {J*_f = 0}` and a Simon chart `(V, W, ψ)` of `M` with
`p = ψ(x_p)`. On the open set `V' = {x ∈ V : J*_f(ψ x) ≠ 0}` (continuity of `J*_f` on `M`) the
map `G = f ∘ ψ` is `C¹`, and `DG(x_p) = Df(p) ∘ Dψ(x_p)` is onto: `df_p` has rank `m`
(`c1_sard_coarea_jacobian_eq_zero_iff`) and `T_p M = range Dψ(x_p)`. The level-set chart
`(D, V₁, l)` of `G⁻¹{y}` at `x_p` (`c1_sard_submersion_level_set_chart`) is a chart of
`ψ⁻¹(Σ_y)` because the two sets agree on `V₁ ⊆ V'`, and `c1_sard_local_representation_comp`
turns it into the chart `(D, W₁, ψ ∘ l)` of `Σ_y` at `p`. -/
theorem Submission.c1_sard_regular_fiber_submanifold : ∀ (N m k : ℕ) (M U : Set (Rn N)) (f : Rn N → Rn m), Chapter02.IsSimonSubmanifold (E := Rn (m + k)) 1 M → IsOpen U → M ⊆ U → ContDiffOn ℝ 1 f U → (∀ (V : Set (Rn (m + k))) (W : Set (Rn N)) (ψ : Rn (m + k) → Rn N), Chapter02.IsSimonLocalRepresentation 1 M V W ψ → ∀ x ∈ V, tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap) → ContinuousOn (coareaJacobian M f) M → ∀ y : Rn m, Chapter02.IsSimonSubmanifold (E := Rn k) 1 ((M ∩ f ⁻¹' {y}) \ {x | coareaJacobian M f x = 0}) := by
  intro N m k M U f hM hU hMU hf htan hJ y
  refine ⟨le_rfl, ?_⟩
  rintro p ⟨⟨hpM, hpy⟩, hpZ⟩
  -- A Simon chart `(V, W, ψ)` of `M` with `p = ψ x_p`; then `y = f (ψ x_p)`.
  obtain ⟨V, W, ψ, hpW, hψ⟩ := hM.2 p hpM
  obtain ⟨xp, hxpV, rfl⟩ : p ∈ ψ '' V := by rw [hψ.image_eq]; exact ⟨hpW, hpM⟩
  obtain rfl : f (ψ xp) = y := hpy
  have hψM : MapsTo ψ V M := fun x hx ↦ (hψ.image_eq.subset (mem_image_of_mem ψ hx)).2
  -- The regular part `V'` of the chart is open and contains `x_p`.
  set V' : Set (Rn (m + k)) := V ∩ (coareaJacobian M f ∘ ψ) ⁻¹' {0}ᶜ
  have hV'open : IsOpen V' := (hJ.comp hψ.contDiffOn.continuousOn hψM).isOpen_inter_preimage
    hψ.isOpen_source isOpen_compl_singleton
  have hV'V : V' ⊆ V := inter_subset_left
  have hxpV' : xp ∈ V' := ⟨hxpV, hpZ⟩
  -- `G = f ∘ ψ` is `C¹` on `V'`, and `DG(x_p) = Df(p) ∘ Dψ(x_p)` is onto.
  have hG : ContDiffOn ℝ 1 (f ∘ ψ) V' :=
    hf.comp (hψ.contDiffOn.mono hV'V) fun x hx ↦ hMU (hψM (hV'V hx))
  have hdf : DifferentiableAt ℝ f (ψ xp) :=
    (hf.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds (hMU hpM))
  have hdψ : DifferentiableAt ℝ ψ xp :=
    (hψ.contDiffOn.differentiableOn one_ne_zero).differentiableAt (hψ.isOpen_source.mem_nhds hxpV)
  have hsurjL : LinearMap.range
      ((fderiv ℝ f (ψ xp)).toLinearMap ∘ₗ (tangentSpace M (ψ xp)).subtype) = ⊤ := by
    have h1 := (Submission.c1_sard_coarea_jacobian_eq_zero_iff N m M f (ψ xp)).not.mp hpZ
    apply Submodule.eq_top_of_finrank_eq
    have h2 := Submodule.finrank_le
      (LinearMap.range ((fderiv ℝ f (ψ xp)).toLinearMap ∘ₗ (tangentSpace M (ψ xp)).subtype))
    rw [finrank_euclideanSpace_fin] at h2 ⊢
    omega
  have hsurjG : Function.Surjective (fderiv ℝ (f ∘ ψ) xp) := by
    intro w
    have hw : w ∈ LinearMap.range
        ((fderiv ℝ f (ψ xp)).toLinearMap ∘ₗ (tangentSpace M (ψ xp)).subtype) := by
      rw [hsurjL]; trivial
    obtain ⟨t, ht⟩ := hw
    have htmem : (t : Rn N) ∈ LinearMap.range (fderiv ℝ ψ xp).toLinearMap := by
      rw [← htan V W ψ hψ xp hxpV]; exact t.2
    obtain ⟨v, hv⟩ := htmem
    refine ⟨v, ?_⟩
    rw [fderiv_comp xp hdf hdψ]
    have hv' : fderiv ℝ ψ xp v = t := hv
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, hv']
    simpa using ht
  -- The level-set chart of `G⁻¹{y}` at `x_p` is a chart of `ψ⁻¹(Σ_y)`.
  obtain ⟨D, V₁, l, hxpV₁, hV₁V', hl⟩ :=
    Submission.c1_sard_submersion_level_set_chart m k V' (f ∘ ψ) xp hV'open hxpV' hG hsurjG
  set S : Set (Rn N) := (M ∩ f ⁻¹' {f (ψ xp)}) \ {x | coareaJacobian M f x = 0}
  have hset : V₁ ∩ (f ∘ ψ) ⁻¹' {(f ∘ ψ) xp} = V₁ ∩ ψ ⁻¹' S := by
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩
      have hxV' := hV₁V' hx1
      exact ⟨hx1, ⟨hψM hxV'.1, hx2⟩, hxV'.2⟩
    · rintro ⟨hx1, ⟨_, hx2⟩, _⟩
      exact ⟨hx1, hx2⟩
  have hl' : Chapter02.IsSimonLocalRepresentation 1 (ψ ⁻¹' S) D V₁ l := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hl
    exact ⟨h1, h2, h3, h4, h5.trans hset, h6, h7⟩
  -- Composing with `ψ` gives the chart `(D, W₁, ψ ∘ l)` of `Σ_y`, and `p = ψ x_p ∈ W₁`.
  obtain ⟨W₁, -, hW₁img, hrep⟩ := Submission.c1_sard_local_representation_comp (m + k) k N M
    S V W ψ D V₁ l hψ (fun x hx ↦ hx.1.1) (hV₁V'.trans hV'V) hl'
  exact ⟨D, W₁, ψ ∘ l, (hW₁img.subset (mem_image_of_mem ψ hxpV₁)).1, hrep⟩
/-- **Simon Ch. 2, 4.3 (p. 55): chart velocities are tangent vectors.** If `V ⊆ ℝⁿ` is open,
`ψ : ℝⁿ → ℝᴺ` is `C¹` on `V` and maps `V` into `M`, then `range Dψ(x) ⊆ T_{ψ(x)} M` for `x ∈ V`.
For `w ≠ 0` choose `B(x, ρ) ⊆ V` and `κ = ρ/(2|w|)`; the curve `γ(t) = ψ(x + κ t w)` is `C¹` on
`(-1,1)`, maps `(-1,1)` into `M`, has `γ(0) = ψ(x)` and, by the chain rule, `γ'(0) = κ Dψ(x) w`.
So `κ Dψ(x) w` is a generator of `T_{ψ(x)} M` and `Dψ(x) w = κ⁻¹ (κ Dψ(x) w)` lies in the span. -/
theorem Submission.simon_chart_range_fderiv_le_tangentSpace : ∀ (n N : ℕ) (M : Set (Rn N)) (V : Set (Rn n)) (ψ : Rn n → Rn N), IsOpen V → ContDiffOn ℝ 1 ψ V → MapsTo ψ V M → ∀ x ∈ V, LinearMap.range (fderiv ℝ ψ x).toLinearMap ≤ tangentSpace M (ψ x) := by
  intro n N M V ψ hV hψ hMaps x₀ hx₀
  -- Step 1: `ψ` is differentiable at `x₀`, with derivative `A = fderiv ℝ ψ x₀`.
  have hA : HasFDerivAt ψ (fderiv ℝ ψ x₀) x₀ :=
    (hψ.contDiffAt (hV.mem_nhds hx₀)).differentiableAt_one.hasFDerivAt
  rintro _ ⟨w, rfl⟩
  -- Step 2: `A 0 = 0` lies in the subspace; for `w ≠ 0` fix `B(x₀, ρ) ⊆ V` and `κ = ρ/(2|w|)`.
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hV x₀ hx₀
  have hw' : 0 < ‖w‖ := norm_pos_iff.mpr hw
  set κ : ℝ := ρ / (2 * ‖w‖) with hκ
  have hκ0 : 0 < κ := div_pos hρ (by positivity)
  set ℓ : ℝ → Rn n := fun t ↦ x₀ + (κ * t) • w with hℓ
  -- Step 3: `ℓ` maps `(-1,1)` into `B(x₀, ρ) ⊆ V`, so `γ = ψ ∘ ℓ` is a `C¹` curve in `M`.
  have hℓV : MapsTo ℓ (Ioo (-1) 1) V := by
    intro t ht
    apply hball
    have ht' : |t| < 1 := abs_lt.mpr ht
    have hκw : κ * ‖w‖ = ρ / 2 := by rw [hκ]; field_simp
    rw [Metric.mem_ball, dist_eq_norm, hℓ, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_mul, abs_of_pos hκ0, mul_right_comm, hκw]
    nlinarith
  have hℓC : ContDiff ℝ 1 ℓ :=
    contDiff_const.add ((contDiff_const.mul contDiff_id).smul contDiff_const)
  have hγC : ContDiffOn ℝ 1 (ψ ∘ ℓ) (Ioo (-1) 1) := hψ.comp hℓC.contDiffOn hℓV
  have hγM : MapsTo (ψ ∘ ℓ) (Ioo (-1) 1) M := hMaps.comp hℓV
  have hℓ0 : ℓ 0 = x₀ := by simp [hℓ]
  have hγ0 : (ψ ∘ ℓ) 0 = ψ x₀ := by simp [Function.comp, hℓ0]
  -- Step 4: chain rule, `γ'(0) = A (κ • w)`, so `κ • A w` is a generator of the span.
  have hℓd : HasDerivAt ℓ (κ • w) 0 := by
    have h := (((hasDerivAt_id (0 : ℝ)).const_mul κ).smul_const w).const_add x₀
    rwa [mul_one] at h
  have hγd : HasDerivAt (ψ ∘ ℓ) (fderiv ℝ ψ x₀ (κ • w)) 0 :=
    hA.comp_hasDerivAt_of_eq (0 : ℝ) hℓd hℓ0.symm
  have hmem : fderiv ℝ ψ x₀ (κ • w) ∈ tangentSpace M (ψ x₀) :=
    Submodule.subset_span ⟨ψ ∘ ℓ, hγC, hγM, hγ0, hγd⟩
  rw [map_smul] at hmem
  have h := (tangentSpace M (ψ x₀)).smul_mem κ⁻¹ hmem
  rwa [smul_smul, inv_mul_cancel₀ hκ0.ne', one_smul] at h
/-- **Simon Ch. 2, 4.3 (p. 55), velocity of a lifted curve.** If `ψ` is differentiable at `x₀`
with injective derivative `A = Dψ(x₀)`, `c(t) → x₀` as `t → 0`, `γ = ψ ∘ c` near `0` and
`γ'(0) = v`, then `v ∈ range A` (`c` need not be differentiable). Injectivity gives
`|ζ| ≤ K |Aζ|`, so the remainder `e(t) = ψ(c(t)) - ψ(x₀) - A(c(t) - x₀) = o(|c(t) - x₀|)` forces
`c(t) - x₀ = O(t)` and `e(t) = o(t)`; then `A(t⁻¹(c(t) - x₀)) = t⁻¹(γ(t) - γ(0)) - t⁻¹e(t) → v`,
and `range A` is closed. -/
theorem Submission.simon_lift_velocity_mem_range_fderiv : ∀ (n N : ℕ) (ψ : Rn n → Rn N) (x₀ : Rn n) (c : ℝ → Rn n) (γ : ℝ → Rn N) (v : Rn N), DifferentiableAt ℝ ψ x₀ → Function.Injective (fderiv ℝ ψ x₀) → Tendsto c (𝓝 (0 : ℝ)) (𝓝 x₀) → (∀ᶠ t in 𝓝 (0 : ℝ), γ t = ψ (c t)) → HasDerivAt γ v 0 → v ∈ LinearMap.range (fderiv ℝ ψ x₀).toLinearMap := by
  intro n N ψ x₀ c γ v hψ hinj hc hγψ hγ
  set A := fderiv ℝ ψ x₀
  -- The unpunctured limit gives `c 0 = x₀`, hence `γ 0 = ψ x₀`.
  have hc0 : c 0 = x₀ :=
    tendsto_nhds_unique (tendsto_pure_nhds c 0) (hc.mono_left (pure_le_nhds 0))
  have hγ0 : γ 0 = ψ x₀ := by rw [hγψ.self_of_nhds, hc0]
  -- The remainder `e(t) = ψ(c t) - ψ x₀ - A (c t - x₀)` is `o(c t - x₀)`.
  have he : (fun t => ψ (c t) - ψ x₀ - A (c t - x₀)) =o[𝓝 0] (fun t => c t - x₀) :=
    hψ.hasFDerivAt.isLittleO.comp_tendsto hc
  -- Injectivity in finite dimension: `‖ζ‖ ≤ K ‖A ζ‖`.
  obtain ⟨K, -, hK⟩ := A.toLinearMap.exists_antilipschitzWith (LinearMap.ker_eq_bot.mpr hinj)
  have hu : (fun t => c t - x₀) =O[𝓝 0] (fun t => A (c t - x₀)) :=
    Asymptotics.IsBigO.of_bound (K : ℝ)
      (Eventually.of_forall fun t => A.bound_of_antilipschitz hK _)
  -- Hence `A (c t - x₀) = O(γ t - γ 0) = O(t)`, so `c t - x₀ = O(t)` and `e(t) = o(t)`.
  have hAu : (fun t => A (c t - x₀)) =O[𝓝 0] (fun t => γ t - γ 0) := by
    refine (he.trans_isBigO hu).right_isBigO_add.congr' EventuallyEq.rfl ?_
    filter_upwards [hγψ] with t ht
    rw [ht, hγ0, sub_add_cancel]
  have hγO : (fun t => γ t - γ 0) =O[𝓝 0] (fun t : ℝ => t) := by
    simpa only [sub_zero] using hγ.isBigO_sub
  have het : (fun t => ψ (c t) - ψ x₀ - A (c t - x₀)) =o[𝓝 0] (fun t : ℝ => t) :=
    he.trans_isBigO (hu.trans (hAu.trans hγO))
  -- `A (t⁻¹ (c t - x₀)) = t⁻¹ (γ t - γ 0) - t⁻¹ e(t) → v` as `t → 0`, `t ≠ 0`.
  have hslope : Tendsto (fun t : ℝ => t⁻¹ • (γ t - γ 0)) (𝓝[≠] 0) (𝓝 v) := by
    simpa only [zero_add] using hγ.tendsto_slope_zero
  have hlim : Tendsto (fun t : ℝ => t⁻¹ • (γ t - γ 0) - t⁻¹ • (ψ (c t) - ψ x₀ - A (c t - x₀)))
      (𝓝[≠] 0) (𝓝 (v - 0)) :=
    hslope.sub (het.tendsto_inv_smul_nhds_zero.mono_left nhdsWithin_le_nhds)
  rw [sub_zero] at hlim
  -- Every term lies in `range A`, a closed subspace.
  refine SetLike.mem_coe.mp <|
    (LinearMap.range A.toLinearMap).closed_of_finiteDimensional.mem_of_tendsto hlim ?_
  filter_upwards [hγψ.filter_mono nhdsWithin_le_nhds] with t ht
  have hAt : t⁻¹ • (γ t - γ 0) - t⁻¹ • (ψ (c t) - ψ x₀ - A (c t - x₀)) =
      A (t⁻¹ • (c t - x₀)) := by
    rw [ht, hγ0, ← smul_sub, map_smul, sub_sub_cancel]
  rw [hAt]
  exact LinearMap.mem_range_self A.toLinearMap _
/-- **Simon Ch. 2, 4.2 (p. 55).** The inverse `g = invFunOn ψ V` of a local representation is
continuous on `W ∩ M = ψ(V)`. For `y ∈ W ∩ M`, a closed ball `Q ⊆ W` about `y` has compact preimage
`K = V ∩ ψ⁻¹(Q)` (relative properness), and `g` maps `W ∩ M ∩ Q` into `K`. Every cluster point `x'`
of `g` at `y` lies in `K ⊆ V` and has `ψ x' = y` by continuity of `ψ`, so `x' = g y` by
injectivity; a map eventually in a compact set with a unique cluster point converges to it. The
injectivity of `Dψ` is not needed. -/
theorem Submission.simon_submanifold_chart_inverse_continuousOn : ∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)) (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N), Chapter02.IsSimonLocalRepresentation r M V W ψ → ContinuousOn (Function.invFunOn ψ V) (W ∩ M) := by
  intro n N r M V W ψ h
  obtain ⟨hV, hW, hψ, hinj, himg, hprop, -⟩ := h
  -- Step 2: on `W ∩ M = ψ(V)`, `g` takes values in `V` and is a right inverse of `ψ`.
  have hg : ∀ y ∈ W ∩ M, Function.invFunOn ψ V y ∈ V ∧ ψ (Function.invFunOn ψ V y) = y := by
    intro y hy
    rw [← himg] at hy
    exact ⟨Function.invFunOn_mem hy, Function.invFunOn_eq hy⟩
  intro y hy
  obtain ⟨hgyV, hψgy⟩ := hg y hy
  -- Step 4, with a compact ball `Q = closedBall y ε ⊆ W` in place of `{y_j} ∪ {y}`:
  -- `K = V ∩ ψ⁻¹(Q)` is compact, and `g z ∈ K` for every `z ∈ W ∩ M` close to `y`.
  obtain ⟨ε, hε, hQW⟩ := nhds_basis_closedBall.mem_iff.1 (hW.mem_nhds hy.1)
  have hK : IsCompact (V ∩ ψ ⁻¹' closedBall y ε) := hprop _ (isCompact_closedBall y ε) hQW
  have hev : ∀ᶠ z in 𝓝[W ∩ M] y, Function.invFunOn ψ V z ∈ V ∩ ψ ⁻¹' closedBall y ε := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (closedBall_mem_nhds y hε)]
      with z hz hzQ
    obtain ⟨hgzV, hψgz⟩ := hg z hz
    exact ⟨hgzV, by rwa [mem_preimage, hψgz]⟩
  -- Steps 5–6, with cluster points in place of subsequential limits: a cluster point `x' ∈ K`
  -- of `g` at `y` has `ψ x' = y` (Step 1: `ψ` is continuous at `x' ∈ V`), hence `x' = g y`.
  refine hK.tendsto_nhds_of_unique_mapClusterPt hev fun x' hx' hcl ↦ ?_
  have hψx' : ContinuousAt ψ x' := hψ.continuousOn.continuousAt (hV.mem_nhds hx'.1)
  have hcl' : MapClusterPt (ψ x') (𝓝[W ∩ M] y) id := by
    refine (hcl.continuousAt_comp hψx').congrFun ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (hg z hz).2
  have hψx'y : ψ x' = y :=
    eq_of_nhds_neBot (mapClusterPt_id_iff.1 hcl' |>.mono nhdsWithin_le_nhds).neBot
  exact hinj hx'.1 hgyV (hψx'y.trans hψgy.symm)
/-- **Simon Ch. 2, §4 (p. 55), projection onto the range of an injective map.** The orthogonal
projection `P_{range A}` depends continuously on `A` on the set of injective `A ∈ L(ℝⁿ, ℝᴺ)`.
For injective `A`, the endomorphism `A* A` of `ℝⁿ` is injective, hence invertible. Moreover
`A (A* A)⁻¹ A*` is the orthogonal projection onto `range A`, since its values lie in `range A` and
`v - A (A* A)⁻¹ A* v ⊥ range A`. The map `A ↦ A ∘ Ring.inverse (A* A) ∘ A*` is continuous at every
injective `A`: the adjoint is a linear isometry, composition is jointly continuous, and
`Ring.inverse` is continuous at units. -/
theorem Submission.simon_submanifold_range_starProjection_continuousOn : ∀ (n N : ℕ), ContinuousOn (fun A : Rn n →L[ℝ] Rn N ↦ (LinearMap.range A.toLinearMap).starProjection) {A : Rn n →L[ℝ] Rn N | Function.Injective A} := by
  intro n N
  -- Step 1: `A* A` is a unit of `L(ℝⁿ, ℝⁿ)` for injective `A`.
  have hunit : ∀ A : Rn n →L[ℝ] Rn N, Function.Injective A →
      IsUnit (ContinuousLinearMap.adjoint A ∘L A) := by
    intro A hA
    have hinj : Function.Injective (ContinuousLinearMap.adjoint A ∘L A) := by
      rw [ContinuousLinearMap.coe_comp]
      exact (ContinuousLinearMap.adjoint_comp_self_injective_iff A).2 hA
    exact ContinuousLinearMap.isUnit_iff_bijective.2
      ⟨hinj, LinearMap.surjective_of_injective
        (f := (ContinuousLinearMap.adjoint A ∘L A : Rn n →ₗ[ℝ] Rn n)) hinj⟩
  -- Steps 2–3: for injective `A`, `A (A* A)⁻¹ A*` is the orthogonal projection onto `range A`.
  have hF : ∀ A : Rn n →L[ℝ] Rn N, Function.Injective A →
      A ∘L (Ring.inverse (ContinuousLinearMap.adjoint A ∘L A) ∘L ContinuousLinearMap.adjoint A) =
        (LinearMap.range A.toLinearMap).starProjection := by
    intro A hA
    ext1 v
    symm
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (LinearMap.mem_range_self _ _) ?_
    rintro _ ⟨w, rfl⟩
    -- `A* (A (A* A)⁻¹ A* v) = A* v`, because `(A* A) (A* A)⁻¹ = 1`.
    have hfix : ContinuousLinearMap.adjoint A
        ((A ∘L (Ring.inverse (ContinuousLinearMap.adjoint A ∘L A) ∘L
          ContinuousLinearMap.adjoint A)) v) = ContinuousLinearMap.adjoint A v := by
      simpa using congrArg (fun T : Rn n →L[ℝ] Rn n ↦ T (ContinuousLinearMap.adjoint A v))
        (Ring.mul_inverse_cancel _ (hunit A hA))
    rw [ContinuousLinearMap.coe_coe, ← ContinuousLinearMap.adjoint_inner_left, map_sub, hfix,
      sub_self, inner_zero_left]
  -- Steps 4–5: `A ↦ A (A* A)⁻¹ A*` is continuous at each injective `A₀`, and it agrees with
  -- `A ↦ P_{range A}` on the injective maps.
  intro A₀ hA₀
  have hadj : Continuous fun A : Rn n →L[ℝ] Rn N ↦ ContinuousLinearMap.adjoint A :=
    ContinuousLinearMap.adjoint.continuous
  have hinv : ContinuousAt (fun A : Rn n →L[ℝ] Rn N ↦
      Ring.inverse (ContinuousLinearMap.adjoint A ∘L A)) A₀ :=
    (NormedRing.inverse_continuousAt (hunit A₀ hA₀).unit).comp_of_eq
      (hadj.clm_comp continuous_id).continuousAt (hunit A₀ hA₀).unit_spec.symm
  have hcont : ContinuousAt (fun A : Rn n →L[ℝ] Rn N ↦
      A ∘L (Ring.inverse (ContinuousLinearMap.adjoint A ∘L A) ∘L
        ContinuousLinearMap.adjoint A)) A₀ :=
    continuousAt_id.clm_comp (hinv.clm_comp hadj.continuousAt)
  exact hcont.continuousWithinAt.congr (fun A hA ↦ (hF A hA).symm) (hF A₀ hA₀).symm
/-- **Simon Ch. 2, §4 (p. 55).** A `C^r` submanifold `M ⊆ ℝᴺ` in the sense of 4.1 is a Borel set.
If `(V, W, ψ)` is a local representation, relative properness and continuity of `ψ` on `V` give
`W ∩ closure (W ∩ M) ⊆ M`, so `W ∩ M = W ∩ closure (W ∩ M)` is the intersection of an open set and a
closed set. By second countability, countably many chart sets `W_y` (`y ∈ M`) cover `M`. Hence `M`
is a countable union of such intersections. -/
theorem Submission.simon_submanifold_measurableSet : ∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)), Chapter02.IsSimonSubmanifold (E := Rn n) r M → MeasurableSet M := by
  intro n N r M hM
  -- Step 1: local closedness. For every local representation `(V, W, ψ)`,
  -- `W ∩ closure (W ∩ M) ⊆ M`.
  have hloc : ∀ (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N),
      Chapter02.IsSimonLocalRepresentation r M V W ψ → W ∩ closure (W ∩ M) ⊆ M := by
    rintro V W ψ ⟨hV, -, hψ, -, himg, hprop, -⟩ z ⟨hzW, hz⟩
    obtain ⟨u, huWM, hu⟩ := mem_closure_iff_seq_limit.1 hz
    -- `Q = {u j : j ∈ ℕ} ∪ {z} ⊆ W` is compact, so relative properness makes `V ∩ ψ⁻¹(Q)` compact.
    have hK : IsCompact (V ∩ ψ ⁻¹' insert z (range u)) :=
      hprop _ hu.isCompact_insert_range (insert_subset hzW (range_subset_iff.2 fun j ↦ (huWM j).1))
    -- Since `u j ∈ W ∩ M = ψ(V)`, choose `x j ∈ V` with `ψ (x j) = u j`.
    have hpre : ∀ j, ∃ x ∈ V, ψ x = u j := fun j ↦ (mem_image ψ V (u j)).1 (himg ▸ huWM j)
    choose x hxV hψx using hpre
    obtain ⟨a, ⟨haV, -⟩, φ, hφ, hxa⟩ := hK.tendsto_subseq (x := x) fun j ↦
      ⟨hxV j, mem_insert_of_mem _ ⟨j, (hψx j).symm⟩⟩
    -- `ψ` is continuous at `a ∈ V`, so `ψ a = lim ψ (x (φ k)) = lim u (φ k) = z`.
    have hψa : Tendsto (ψ ∘ x ∘ φ) atTop (𝓝 (ψ a)) :=
      (hψ.continuousOn.continuousAt (hV.mem_nhds haV)).tendsto.comp hxa
    have hz' : Tendsto (ψ ∘ x ∘ φ) atTop (𝓝 z) := by
      have hcomp : ψ ∘ x ∘ φ = u ∘ φ := funext fun k ↦ hψx (φ k)
      rw [hcomp]
      exact hu.comp hφ.tendsto_atTop
    have hzimg : z ∈ ψ '' V := ⟨a, haV, tendsto_nhds_unique hψa hz'⟩
    exact (himg ▸ hzimg).2
  -- Step 3: Lindelöf. Choose a local representation `(V y, W y, ψ y)` with `y ∈ W y` for every
  -- `y ∈ M`; the union of the open sets `W y`, `y ∈ M`, is a union over a countable `T ⊆ M`.
  choose! V W ψ hyW hrep using hM.2
  obtain ⟨T, hTM, hTc, hTU⟩ :=
    TopologicalSpace.isOpen_biUnion_countable M W fun y hy ↦ (hrep y hy).2.1
  -- Steps 2 and 4: `M = ⋃ y ∈ T, (W y ∩ closure (W y ∩ M))`; `⊆` uses
  -- `W y ∩ M ⊆ closure (W y ∩ M)`, and `⊇` is Step 1.
  have hMeq : M = ⋃ y ∈ T, (W y ∩ closure (W y ∩ M)) := by
    refine Subset.antisymm (fun z hz ↦ ?_) (iUnion₂_subset fun y hy ↦ hloc _ _ _ (hrep y (hTM hy)))
    have hzT : z ∈ ⋃ y ∈ T, W y := hTU ▸ mem_biUnion hz (hyW z hz)
    obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.1 hzT
    exact mem_biUnion hy ⟨hzy, subset_closure ⟨hzy, hz⟩⟩
  -- Step 5: each `W y ∩ closure (W y ∩ M)` is Borel, and `T` is countable.
  rw [hMeq]
  exact .biUnion hTc fun y hy ↦
    (hrep y (hTM hy)).2.1.measurableSet.inter isClosed_closure.measurableSet

/-- The frozen Chapter 2 contract: the conjunction of all headline results. -/
theorem main_theorem : LipschitzExtension ∧ Rademacher ∧ C1Approximation ∧ WhitneyExtension ∧ LipschitzImageHausdorff ∧ EilenbergInequality ∧ BVCompactness ∧ BVPoincare ∧ BVExtensionEstimate ∧ AreaFormula ∧ FirstVariation ∧ SecondVariation ∧ StationaryIffMeanCurvatureZero ∧ SecondVariationStationary ∧ CoareaFormula ∧ C1Sard := by sorry

/-- **Simon Ch. 2, 4.3 (p. 55), `T_{ψ(x)} M ⊆ range Dψ(x)`.** If `(V, W, ψ)` is a `C^r` local
representation of `M`, `r ≥ 1`, and `ψ⁻¹ = invFunOn ψ V` is continuous on `W ∩ M`, then
`T_{ψ(x)} M ⊆ range Dψ(x)` for `x ∈ V`. A `C¹` curve `γ` in `M` through `ψ(x)` stays in `W ∩ M`
near `0`, so `γ = ψ ∘ c` there with `c = ψ⁻¹ ∘ γ → x`, and `simon_lift_velocity_mem_range_fderiv`
puts `γ'(0)` in `range Dψ(x)`. -/
theorem Submission.simon_chart_tangentSpace_le_range_fderiv : ∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)) (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N), 1 ≤ r → Chapter02.IsSimonLocalRepresentation r M V W ψ → ContinuousOn (Function.invFunOn ψ V) (W ∩ M) → ∀ x ∈ V, tangentSpace M (ψ x) ≤ LinearMap.range (fderiv ℝ ψ x).toLinearMap := by
  intro n N r M V W ψ hr hψ hcont x₀ hx₀
  obtain ⟨hV, hW, hψC, hψinj, hψimg, -, hψder⟩ := hψ
  have hdiff : DifferentiableAt ℝ ψ x₀ :=
    ((hψC.of_le (by exact_mod_cast hr)).differentiableOn_one x₀ hx₀).differentiableAt
      (hV.mem_nhds hx₀)
  have hy₀ : ψ x₀ ∈ W ∩ M := by rw [← hψimg]; exact mem_image_of_mem ψ hx₀
  -- It suffices to treat a generator `v = γ'(0)` of `T_{ψ(x₀)} M`.
  rw [tangentSpace, Submodule.span_le]
  rintro v ⟨γ, -, hγM, hγ0, hγv⟩
  -- `γ(t) ∈ W ∩ M` for `t` near `0`.
  have hγWM : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ W ∩ M := by
    have hγ0W : γ 0 ∈ W := by rw [hγ0]; exact hy₀.1
    filter_upwards [hγv.continuousAt.preimage_mem_nhds (hW.mem_nhds hγ0W),
      Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num) one_pos] with t htW htI
    exact ⟨htW, hγM htI⟩
  -- The lift `c = ψ⁻¹ ∘ γ` satisfies `γ = ψ ∘ c` near `0` and `c(t) → ψ⁻¹(ψ x₀) = x₀`.
  have hfac : ∀ᶠ t in 𝓝 (0 : ℝ), γ t = ψ (Function.invFunOn ψ V (γ t)) := by
    filter_upwards [hγWM] with t ht
    rw [← hψimg] at ht
    exact (Function.invFunOn_eq ht).symm
  have hc : Tendsto (fun t ↦ Function.invFunOn ψ V (γ t)) (𝓝 (0 : ℝ)) (𝓝 x₀) := by
    have hγt : Tendsto γ (𝓝 (0 : ℝ)) (𝓝[W ∩ M] (ψ x₀)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, hγWM⟩
      rw [← hγ0]
      exact hγv.continuousAt.tendsto
    have hg := (hcont (ψ x₀) hy₀).tendsto
    rw [hψinj.leftInvOn_invFunOn hx₀] at hg
    exact hg.comp hγt
  exact Submission.simon_lift_velocity_mem_range_fderiv n N ψ x₀
    (fun t ↦ Function.invFunOn ψ V (γ t)) γ v hdiff (hψder x₀ hx₀) hc hfac hγv

/-- **Simon Ch. 2, 4.3 (p. 55).** If `(V, W, ψ)` is a `C^r` local representation of `M`, `r ≥ 1`,
then `T_{ψ(x)} M = range Dψ(x)` for `x ∈ V`. `range Dψ(x) ⊆ T_{ψ(x)} M` holds for any `C¹` map of
the open set `V` into `M` (here `ψ(V) = W ∩ M`). Conversely, every generating velocity of
`T_{ψ(x)} M` lies in `range Dψ(x)`, since its curve lifts through `ψ⁻¹ = invFunOn ψ V`, which is
continuous on `W ∩ M` by 4.2. -/
theorem Submission.simon_submanifold_tangentSpace_eq_range : ∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)) (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N), 1 ≤ r → Chapter02.IsSimonLocalRepresentation r M V W ψ → ∀ x ∈ V, tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap := by
  intro n N r M V W ψ hr h x hx
  -- Part A: `ψ` is a `C¹` map of the open set `V` into `ψ(V) = W ∩ M ⊆ M`.
  have hA : LinearMap.range (fderiv ℝ ψ x).toLinearMap ≤ tangentSpace M (ψ x) :=
    Submission.simon_chart_range_fderiv_le_tangentSpace n N M V ψ h.isOpen_source
      (h.contDiffOn.of_le (by exact_mod_cast hr))
      ((mapsTo_image ψ V).mono_right (h.image_eq.subset.trans inter_subset_right)) x hx
  -- Part B: generating curves lift through `invFunOn ψ V`, continuous on `W ∩ M` (Simon 4.2).
  have hB : tangentSpace M (ψ x) ≤ LinearMap.range (fderiv ℝ ψ x).toLinearMap :=
    Submission.simon_chart_tangentSpace_le_range_fderiv n N r M V W ψ hr h
      (Submission.simon_submanifold_chart_inverse_continuousOn n N r M V W ψ h) x hx
  exact le_antisymm hB hA

/-- **Simon Ch. 2, §4 (p. 55), from 4.1–4.3: the tangent projection `y ↦ P_y` is continuous on
`M`.** Near `y₀ ∈ M` take a local representation `(V, W, ψ)` with `y₀ ∈ W` and let
`g = invFunOn ψ V : W ∩ M → V`. As `T_{ψ(x)} M = range Dψ(x)` (4.3,
`simon_submanifold_tangentSpace_eq_range`), `P_y = P_{range Dψ(g(y))}` for `y ∈ W ∩ M`. The right
side is continuous on `W ∩ M`: it composes `g` (`simon_submanifold_chart_inverse_continuousOn`),
`x ↦ Dψ(x)` (continuous on the open `V`, with injective values) and `A ↦ P_{range A}`
(`simon_submanifold_range_starProjection_continuousOn`). As `W` is a neighbourhood of `y₀`,
continuity within `W ∩ M` at `y₀` is continuity within `M`. -/
theorem Submission.simon_submanifold_tangentProjection_continuousOn : ∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)), Chapter02.IsSimonSubmanifold (E := Rn n) r M → ContinuousOn (tangentProjection M) M := by
  intro n N r M hM y₀ hy₀
  -- Step 1: a local representation `(V, W, ψ)` with `y₀ ∈ W`; `g = invFunOn ψ V`.
  obtain ⟨V, W, ψ, hy₀W, hψ⟩ := hM.exists_localRepresentation hy₀
  set g := Function.invFunOn ψ V
  -- Step 2: `W ∩ M = ψ(V)`, so `g` maps `W ∩ M` into `V` and `ψ (g y) = y` there.
  have hsurj : SurjOn ψ V (W ∩ M) := hψ.image_eq.symm.subset
  have hgV : MapsTo g (W ∩ M) V := hsurj.mapsTo_invFunOn
  have hψg : RightInvOn g ψ (W ∩ M) := hsurj.rightInvOn_invFunOn
  -- Step 3: `P_y = P_{range Dψ(g(y))}` on `W ∩ M`, as `T_y M = T_{ψ(g(y))} M = range Dψ(g(y))`.
  have hP : EqOn (tangentProjection M)
      (fun y ↦ (LinearMap.range (fderiv ℝ ψ (g y)).toLinearMap).starProjection) (W ∩ M) := by
    intro y hy
    have hT := Submission.simon_submanifold_tangentSpace_eq_range n N r M V W ψ hM.1 hψ (g y)
      (hgV hy)
    rw [hψg hy] at hT
    simp only [tangentProjection, hT]
  -- Step 4: the right side is continuous on `W ∩ M`, as the composite of `g`, `x ↦ Dψ(x)` (which
  -- maps `V` into the injective maps) and `A ↦ P_{range A}`.
  have hDψ : ContinuousOn (fderiv ℝ ψ) V :=
    hψ.contDiffOn.continuousOn_fderiv_of_isOpen hψ.isOpen_source (by exact_mod_cast hM.1)
  have hcont : ContinuousOn
      (fun y ↦ (LinearMap.range (fderiv ℝ ψ (g y)).toLinearMap).starProjection) (W ∩ M) :=
    (Submission.simon_submanifold_range_starProjection_continuousOn n N).comp
      (hDψ.comp (Submission.simon_submanifold_chart_inverse_continuousOn n N r M V W ψ hψ) hgV)
      fun _ hy ↦ hψ.injective_fderiv (hgV hy)
  -- Steps 5–6: so `P` is continuous within `W ∩ M` at `y₀`, and `W ∩ M ∈ 𝓝[M] y₀` as `W` is open.
  exact (hcont.congr hP y₀ ⟨hy₀W, hy₀⟩).mono_of_mem_nhdsWithin
    (mem_nhdsWithin.2 ⟨W, hψ.isOpen_target, hy₀W, subset_rfl⟩)

/-- **Simon Ch. 2, 4.1–4.3 (p. 55).** (1) If `ψ : V → W` is a local representation of `M` of class
`C^r`, `r ≥ 1`, then `T_{ψ(x)} M = range Dψ(x)` for every `x ∈ V`. (2) An `n`-dimensional `C^r`
submanifold `M` is a Borel set and `y ↦ P_y` is continuous on `M`. Part (1) is
`simon_submanifold_tangentSpace_eq_range`. In part (2), `M` is Borel because properness makes it
locally closed and countably many charts cover it (`simon_submanifold_measurableSet`). On a chart,
`P_y` is the projection onto `range Dψ(ψ⁻¹ y)`, which depends continuously on `y` because `Dψ` and
`ψ⁻¹` are continuous (`simon_submanifold_tangentProjection_continuousOn`). -/
theorem Submission.simon_submanifold_tangent_basics : (∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)) (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N), 1 ≤ r → Chapter02.IsSimonLocalRepresentation r M V W ψ → ∀ x ∈ V, tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap) ∧ ∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)), Chapter02.IsSimonSubmanifold (E := Rn n) r M → MeasurableSet M ∧ ContinuousOn (tangentProjection M) M :=
  ⟨Submission.simon_submanifold_tangentSpace_eq_range, fun n N r M hM ↦
    ⟨Submission.simon_submanifold_measurableSet n N r M hM,
      Submission.simon_submanifold_tangentProjection_continuousOn n N r M hM⟩⟩

end GMT.Ch02
