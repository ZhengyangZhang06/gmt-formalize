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

/-- **Concavity of the distance to the complement of a convex set** (Simon 2.8, proof, C1(b)).
For a convex `U ⊆ ℝⁿ`, `d(x) = infDist x Uᶜ` is concave on `U`; `U` need not be open, and
`infDist x ∅ = 0`. Fix `x, y ∈ U` and `a, b ≥ 0` with `a + b = 1`, and put `z = a • x + b • y`,
`s = a d(x) + b d(y)`. Suppose some `p ∈ Uᶜ` had `dist z p < s`, and put `h = p - z`. Then the
shifted points `x + (d(x)/s) • h` and `y + (d(y)/s) • h` lie in `U`
(`Metric.ball_infDist_compl_subset`), and their `a, b`-combination is `p`. This contradicts
convexity, so `s ≤ d(z)` by `Metric.le_infDist`. -/
theorem Submission.bv_ext_infDist_compl_concaveOn : ∀ (n : ℕ) (U : Set (Rn n)), Convex ℝ U → ConcaveOn ℝ U (fun x ↦ infDist x Uᶜ) := by
  intro n U hU
  -- Step 1: fix `x, y ∈ U` and weights `a, b ≥ 0` with `a + b = 1`.
  refine ⟨hU, fun x hx y hy a b ha hb hab ↦ ?_⟩
  simp only [smul_eq_mul]
  -- Step 2: if `Uᶜ = ∅` both sides vanish; otherwise it suffices to bound `dist z p`, `p ∈ Uᶜ`.
  rcases (Uᶜ).eq_empty_or_nonempty with hE | hne
  · simp [hE]
  rw [le_infDist hne]
  intro p hp
  -- Step 4: suppose `dist z p < s`; then `s > 0`, and `h = p - z` has `‖h‖ < s`.
  by_contra! hlt
  set s := a * infDist x Uᶜ + b * infDist y Uᶜ
  have hs0 : 0 < s := dist_nonneg.trans_lt hlt
  set h := p - (a • x + b • y) with hh
  have hnorm : ‖h‖ < s := by rwa [hh, ← dist_eq_norm, dist_comm]
  -- Steps 3 and 5: each shifted point `q + (d(q)/s) • h`, `q ∈ U`, lies in `U`.
  have hshift : ∀ q ∈ U, q + (infDist q Uᶜ / s) • h ∈ U := by
    intro q hq
    rcases (infDist_nonneg (x := q) (s := Uᶜ)).eq_or_lt with h0 | hpos
    · rw [← h0, zero_div, zero_smul, add_zero]
      exact hq
    · apply ball_infDist_compl_subset
      rw [mem_ball, dist_self_add_left, norm_smul, Real.norm_of_nonneg (div_nonneg hpos.le hs0.le)]
      calc infDist q Uᶜ / s * ‖h‖ < infDist q Uᶜ / s * s := by gcongr
        _ = infDist q Uᶜ := div_mul_cancel₀ _ hs0.ne'
  -- Step 6: the `a, b`-combination of the shifted points is `z + h = p`, so `p ∈ U`.
  have hcoef : a * (infDist x Uᶜ / s) + b * (infDist y Uᶜ / s) = 1 := by
    rw [mul_div_assoc', mul_div_assoc', ← add_div, div_self hs0.ne']
  have hp' : a • (x + (infDist x Uᶜ / s) • h) + b • (y + (infDist y Uᶜ / s) • h) = p := by
    calc a • (x + (infDist x Uᶜ / s) • h) + b • (y + (infDist y Uᶜ / s) • h)
        = (a • x + b • y) + (a * (infDist x Uᶜ / s) + b * (infDist y Uᶜ / s)) • h := by
          simp only [smul_add, smul_smul, add_smul]
          abel
      _ = p := by rw [hcoef, one_smul, hh, add_sub_cancel]
  exact hp (hp' ▸ hU (hshift x hx) (hshift y hy) ha hb hab)
/-- **Unit gradient of the distance function off a closed set** (Simon 2.8 proof, C1(c), with `S`
in place of `Uᶜ`). If `S ⊆ ℝⁿ` is closed and nonempty, `x ∉ S` and `d = infDist · S` is
differentiable at `x`, then `‖Dd(x)‖ = 1`. Since `d` is 1-Lipschitz, `‖Dd(x)‖ ≤ 1`
(`norm_fderiv_le_of_lipschitz`). Conversely, take a nearest point `a ∈ S`
(`IsClosed.exists_infDist_eq_dist`), `ρ = d(x) > 0` and the unit vector `e = ρ⁻¹ • (a - x)`. Then
`d(x + t • e) ≤ ρ - t` for `0 ≤ t ≤ ρ`, so the right difference quotients of `t ↦ d(x + t • e)` at
`0` give `Dd(x) e ≤ -1`, and `‖Dd(x)‖ ≥ |Dd(x) e| ≥ 1`. -/
theorem Submission.bv_ext_norm_fderiv_infDist_eq_one : ∀ (n : ℕ) (S : Set (Rn n)) (x : Rn n), IsClosed S → S.Nonempty → x ∉ S → DifferentiableAt ℝ (fun y ↦ infDist y S) x → ‖fderiv ℝ (fun y ↦ infDist y S) x‖ = 1 := by
  intro n S x hS hne hx hd
  set L := fderiv ℝ (fun y ↦ infDist y S) x with hL
  -- Step 1: `infDist · S` is 1-Lipschitz, so `‖L‖ ≤ 1`.
  have hup : ‖L‖ ≤ 1 := by
    simpa using norm_fderiv_le_of_lipschitz ℝ (x₀ := x) (lipschitz_infDist_pt S)
  -- Step 2: a nearest point `a ∈ S`, with `ρ = infDist x S = ‖a - x‖ > 0`.
  obtain ⟨a, haS, hda⟩ := hS.exists_infDist_eq_dist hne x
  have hρ : 0 < infDist x S := (hS.notMem_iff_infDist_pos hne).1 hx
  set ρ := infDist x S with hρdef
  have hax : ‖a - x‖ = ρ := by rw [hda, dist_comm, dist_eq_norm]
  -- Step 3: along the unit vector `e` towards `a`, `infDist (x + t • e) S ≤ ρ - t` on `[0, ρ]`.
  set e : Rn n := ρ⁻¹ • (a - x) with he
  have he1 : ‖e‖ = 1 := by
    rw [he, norm_smul, hax, Real.norm_eq_abs, abs_inv, abs_of_pos hρ, inv_mul_cancel₀ hρ.ne']
  have hdec : ∀ t : ℝ, 0 ≤ t → t ≤ ρ → infDist (x + t • e) S ≤ ρ - t := by
    intro t ht0 htρ
    have hvec : a - (x + t • e) = (1 - t / ρ) • (a - x) := by
      rw [he, smul_smul, sub_smul, one_smul, div_eq_mul_inv]; abel
    have hcoef : 0 ≤ 1 - t / ρ := by rw [sub_nonneg, div_le_one hρ]; exact htρ
    calc infDist (x + t • e) S ≤ dist (x + t • e) a := infDist_le_dist_of_mem haS
      _ = ρ - t := by
        rw [dist_comm, dist_eq_norm, hvec, norm_smul, hax, Real.norm_eq_abs, abs_of_nonneg hcoef]
        field_simp
  -- Step 4: `t ↦ infDist (x + t • e) S` has derivative `L e` at `0`; its right difference
  -- quotients are `≤ -1` on `(0, ρ]`, hence `L e ≤ -1`.
  have hderiv : HasDerivAt (fun t : ℝ ↦ infDist (x + t • e) S) (L e) 0 := by
    have hline : HasDerivAt (fun t : ℝ ↦ x + t • e) e 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add x
    have hdx : HasFDerivAt (fun y ↦ infDist y S) L (x + (0 : ℝ) • e) := by
      simpa using hd.hasFDerivAt
    exact hdx.comp_hasDerivAt (0 : ℝ) hline
  have hLe : L e ≤ -1 := by
    refine le_of_tendsto hderiv.tendsto_slope_zero_right ?_
    filter_upwards [Ioc_mem_nhdsGT hρ] with t ht
    have h3 := hdec t ht.1.le ht.2
    simp only [zero_add, zero_smul, add_zero, smul_eq_mul]
    rw [inv_mul_le_iff₀ ht.1]
    linarith
  -- Step 5: `1 ≤ -L e = ‖L e‖ ≤ ‖L‖ * ‖e‖ = ‖L‖`.
  have hlow : 1 ≤ ‖L‖ := by
    have h := L.le_opNorm e
    rw [he1, mul_one, Real.norm_eq_abs, abs_of_neg (by linarith)] at h
    linarith
  -- Step 6: combine the two bounds.
  exact le_antisymm hup hlow
/-- **Divergence of a scalar multiple** (Simon 2.8 proof, C4(b) and C5(b)). If `φ : ℝⁿ → ℝ` and
`g : ℝⁿ → ℝⁿ` are differentiable at `x`, then `div(φ g)(x) = φ(x) div g(x) + Dφ(x)[g(x)]`. By the
product rule (`fderiv_fun_smul`), `D(φ g)(x) = φ(x) Dg(x) + Dφ(x).smulRight (g x)`. The trace is
linear, and the rank-one map `h ↦ Dφ(x)[h] g(x)` has trace `Dφ(x)[g(x)]`
(`LinearMap.trace_smulRight`). -/
theorem Submission.bv_ext_euclideanDivergence_smul : ∀ (n : ℕ) (φ : Rn n → ℝ) (g : Rn n → Rn n) (x : Rn n), DifferentiableAt ℝ φ x → DifferentiableAt ℝ g x → Chapter02.euclideanDivergence (fun y ↦ φ y • g y) x = φ x * Chapter02.euclideanDivergence g x + fderiv ℝ φ x (g x) := by
  intro n φ g x hφ hg
  -- Step 1: the divergence is the trace of the derivative, viewed as a linear map.
  unfold Chapter02.euclideanDivergence
  -- Step 2: product rule `D(φ g)(x) = φ(x) • Dg(x) + Dφ(x).smulRight (g x)`. The coercion to linear
  -- maps and the trace are additive and commute with scalar multiplication.
  rw [fderiv_fun_smul hφ hg, ContinuousLinearMap.toLinearMap_add,
    ContinuousLinearMap.toLinearMap_smul, map_add, map_smul, smul_eq_mul]
  -- Step 3: the coercion of `Dφ(x).smulRight (g x)` is definitionally
  -- `(Dφ(x) : ℝⁿ →ₗ[ℝ] ℝ).smulRight (g x)`, whose trace is `Dφ(x)[g(x)]`.
  congr 1
  exact LinearMap.trace_smulRight (fderiv ℝ φ x).toLinearMap (g x)
/-- **Admissible fields for `|Dv|(W)` (Simon 2.4).** A `K`-Lipschitz, compactly supported field
`G : ℝⁿ → ℝⁿ` with `spt G ⊆ W` and `|G| ≤ 1` is one of the fields in the supremum defining
`Chapter02.bvVariationOn v W`, so `ofReal (∫_W v div G) ≤ |Dv|(W)`. No openness or measurability of
`W` and no integrability of `v` is needed: this is the defining supremum bound. `G` is packaged as
`g ∈ C_c(ℝⁿ, ℝⁿ)` with `⇑g = G`. It is Lipschitz with constant `K`, and `sup |g| ≤ 1` by `csSup_le`. -/
theorem Submission.bv_ext_ofReal_integral_le_bvVariationOn : ∀ (n : ℕ) (W : Set (Rn n)) (v : Rn n → ℝ) (G : Rn n → Rn n) (K : ℝ≥0), LipschitzWith K G → HasCompactSupport G → tsupport G ⊆ W → (∀ x, ‖G x‖ ≤ 1) → ENNReal.ofReal (∫ x in W, v x * Chapter02.euclideanDivergence G x) ≤ Chapter02.bvVariationOn v W := by
  intro n W v G K hG hcs hsupp hnorm
  -- Step 1: package `G` (continuous, being Lipschitz) as `g ∈ C_c(ℝⁿ, ℝⁿ)`; `⇑g` is `G` by definition.
  let g : CompactlySupportedContinuousMap (Rn n) (Rn n) := ⟨⟨G, hG.continuous⟩, hcs⟩
  -- Step 2: `g` is a Lipschitz test field with constant `K`, and `tsupport ⇑g = tsupport G ⊆ W`.
  have hg : Chapter02.IsLipschitzTestField g := ⟨K, hG⟩
  -- Step 3: `sup |g| ≤ 1`, since the range of `‖g ·‖` is nonempty and bounded by `1`.
  have hn : Chapter02.compactlySupportedSupNorm g ≤ 1 :=
    csSup_le (range_nonempty _) (by rintro _ ⟨x, rfl⟩; exact hnorm x)
  -- Step 4: the defining supremum bound for the admissible field `g`.
  exact Chapter02.ofReal_integral_le_bvVariationOn v W g hg hsupp hn

/-- The frozen Chapter 2 contract: the conjunction of all headline results. -/
theorem main_theorem : LipschitzExtension ∧ Rademacher ∧ C1Approximation ∧ WhitneyExtension ∧ LipschitzImageHausdorff ∧ EilenbergInequality ∧ BVCompactness ∧ BVPoincare ∧ BVExtensionEstimate ∧ AreaFormula ∧ FirstVariation ∧ SecondVariation ∧ StationaryIffMeanCurvatureZero ∧ SecondVariationStationary ∧ CoareaFormula ∧ C1Sard := by sorry

/-- **The distance gradient points into `U` near `∂U`** (Simon 2.8, proof, C2, inequality (1)).
Let `U ⊆ ℝⁿ` be open and convex with `Uᶜ ≠ ∅`, `r > 0`, `closedBall ξ r ⊆ U`, and
`d(y) = infDist y Uᶜ`. Take `η > 0` to be the minimum of `d` over the compact ball
`closedBall ξ r ⊆ U`. Fix `x ∈ U` with `d(x) < η` at which `d` is differentiable, and put
`L = Dd(x)`. Then `‖L‖ = 1` (`Submission.bv_ext_norm_fderiv_infDist_eq_one`), so the Riesz
vector `ν` of `L` is a unit vector with `L ν = 1`. The point `w = ξ - r • ν` lies in the ball,
so `d(x) < η ≤ d(w)`. Since `d` is concave on `U` (`Submission.bv_ext_infDist_compl_concaveOn`),
its restriction to the segment from `x` to `w` gives `d(w) - d(x) ≤ L (w - x) = -L (x - ξ) - r`
(`ConcaveOn.slope_le_of_hasDerivAt`). -/
theorem Submission.bv_ext_infDist_compl_fderiv_lt : ∀ (n : ℕ) (U : Set (Rn n)) (ξ : Rn n) (r : ℝ), IsOpen U → Convex ℝ U → Uᶜ.Nonempty → 0 < r → closedBall ξ r ⊆ U → ∃ η : ℝ, 0 < η ∧ ∀ x ∈ U, infDist x Uᶜ < η → DifferentiableAt ℝ (fun y ↦ infDist y Uᶜ) x → r < -fderiv ℝ (fun y ↦ infDist y Uᶜ) x (x - ξ) := by
  intro n U ξ r hUo hUc hne hr hball
  -- Step 1: `Uᶜ` is closed and nonempty, so `d > 0` on `U`.
  have hcl : IsClosed Uᶜ := hUo.isClosed_compl
  have hpos : ∀ y ∈ U, 0 < infDist y Uᶜ := fun y hy ↦
    (hcl.notMem_iff_infDist_pos hne).1 (Set.notMem_compl_iff.2 hy)
  -- Step 2: `η = d(y₀)` is the minimum of `d` over the compact ball `closedBall ξ r ⊆ U`.
  obtain ⟨y₀, hy₀, hmin⟩ := (isCompact_closedBall ξ r).exists_isMinOn
    (nonempty_closedBall.2 hr.le) (continuous_infDist_pt Uᶜ).continuousOn
  refine ⟨infDist y₀ Uᶜ, hpos y₀ (hball hy₀), fun x hx hxη hdiff ↦ ?_⟩
  -- Step 3: `L = Dd(x)` has norm `1`.
  generalize hL : fderiv ℝ (fun y ↦ infDist y Uᶜ) x = L
  have hfd : HasFDerivAt (fun y ↦ infDist y Uᶜ) L x := hL ▸ hdiff.hasFDerivAt
  have hLnorm : ‖L‖ = 1 := hL ▸ Submission.bv_ext_norm_fderiv_infDist_eq_one n Uᶜ x hcl hne
    (Set.notMem_compl_iff.2 hx) hdiff
  -- Step 4: the Riesz vector `ν` of `L` is a unit vector with `L ν = 1`.
  obtain ⟨ν, hν, hLν⟩ : ∃ ν : Rn n, ‖ν‖ = 1 ∧ L ν = 1 := by
    set e := InnerProductSpace.toDual ℝ (Rn n)
    refine ⟨e.symm L, by rw [LinearIsometryEquiv.norm_map, hLnorm], ?_⟩
    rw [← InnerProductSpace.toDual_symm_apply (x := e.symm L) (y := L),
      real_inner_self_eq_norm_sq, LinearIsometryEquiv.norm_map, hLnorm, one_pow]
  -- Step 5: `w = ξ - r • ν` lies in `closedBall ξ r ⊆ U`, so `d(x) < η ≤ d(w)`.
  obtain ⟨w, hw⟩ : ∃ w : Rn n, w = ξ - r • ν := ⟨_, rfl⟩
  have hwball : w ∈ closedBall ξ r := by
    rw [mem_closedBall, dist_eq_norm, hw, sub_sub_cancel_left, norm_neg, norm_smul, hν, mul_one,
      Real.norm_of_nonneg hr.le]
  have hdw : infDist x Uᶜ < infDist w Uᶜ := hxη.trans_le (isMinOn_iff.1 hmin w hwball)
  -- Step 6: concavity of `d` along the segment from `x` to `w` gives `d(w) - d(x) ≤ L (w - x)`.
  have hsuper : infDist w Uᶜ - infDist x Uᶜ ≤ L (w - x) := by
    have hcv := (Submission.bv_ext_infDist_compl_concaveOn n U hUc).comp_affineMap
      (AffineMap.lineMap x w)
    have hder := hfd.comp_hasDerivAt_of_eq 0 (AffineMap.hasDerivAt_lineMap (a := x) (b := w))
      (AffineMap.lineMap_apply_zero x w).symm
    simpa [slope_def_field] using
      hcv.slope_le_of_hasDerivAt (by simpa using hx) (by simpa using hball hwball) zero_lt_one hder
  -- Step 7: `L (w - x) = -L (x - ξ) - r`.
  have hcomp : L (w - x) = -L (x - ξ) - r := by
    rw [show w - x = -(x - ξ) - r • ν by rw [hw]; abel, map_sub, map_neg, map_smul, hLν,
      smul_eq_mul, mul_one]
  -- Step 8: `0 < d(w) - d(x) ≤ -L (x - ξ) - r`.
  linarith

/-- **Cut-offs for the BV extension estimate** (Simon Ch. 2, proof of Lemma 2.8, (2)–(3), p. 52).
Let `U ⊂ ℝⁿ` be bounded, open and convex, and `B_r(ξ) ⊂ U` with `r > 0`. Then there are Lipschitz
`φ_j : ℝⁿ → [0, 1]` with compact support in `U` such that `φ_j → 1_U` pointwise and
`r |Dφ_j| ≤ -Dφ_j(x)[x - ξ]` for `Lⁿ`-a.e. `x`. Take `φ_j = γ_j ∘ d`, where `d = dist(·, ℝⁿ \ U)` and
`γ_j(t) = min(1, max(0, 2t/ε_j - 1))`. The level `ε_j < min(η, 1/(j+1))` is chosen so that
`{d = ε_j}` and `{d = ε_j/2}` are `Lⁿ`-null. Here `η` is given by
`Submission.bv_ext_infDist_compl_fderiv_lt`: `r < -Dd(x)[x - ξ]` at every `x ∈ U` with `d(x) < η`
at which `d` is differentiable. -/
theorem Submission.bv_ext_exists_cutoffs : ∀ (n : ℕ) (U : Set (Rn n)) (ξ : Rn n) (r : ℝ), IsOpen U → Bornology.IsBounded U → Convex ℝ U → 0 < r → closedBall ξ r ⊆ U → ∃ φ : ℕ → Rn n → ℝ, (∀ j, ∃ K, LipschitzWith K (φ j)) ∧ (∀ j x, 0 ≤ φ j x ∧ φ j x ≤ 1) ∧ (∀ j, HasCompactSupport (φ j)) ∧ (∀ j, tsupport (φ j) ⊆ U) ∧ (∀ x, Tendsto (fun j ↦ φ j x) atTop (𝓝 (U.indicator (fun _ ↦ (1 : ℝ)) x))) ∧ ∀ j, ∀ᵐ x ∂volume, r * ‖fderiv ℝ (φ j) x‖ ≤ -fderiv ℝ (φ j) x (x - ξ) := by
  intro n U ξ r hUo hUb hUc hr hball
  rcases Uᶜ.eq_empty_or_nonempty with hUe | hne
  · -- Step 1: `Uᶜ = ∅`, so `U = univ` is compact and `φ_j ≡ 1` works.
    have hU : U = univ := compl_empty_iff.1 hUe
    have hcpt : IsCompact (univ : Set (Rn n)) :=
      Metric.isCompact_of_isClosed_isBounded isClosed_univ (hU ▸ hUb)
    refine ⟨fun _ _ ↦ 1, fun _ ↦ ⟨0, LipschitzWith.const 1⟩,
      fun _ _ ↦ ⟨zero_le_one, le_rfl⟩, fun _ ↦ ?_, fun _ ↦ ?_, fun x ↦ ?_, fun _ ↦ ?_⟩
    · exact hcpt.of_isClosed_subset (isClosed_tsupport _) (subset_univ _)
    · rw [hU]; exact subset_univ _
    · rw [hU, indicator_univ]; exact tendsto_const_nhds
    · exact Filter.Eventually.of_forall fun x ↦ by simp
  -- Step 2: `d = infDist · Uᶜ` is 1-Lipschitz, `0` off `U`, positive on `U`, `‖Dd‖ ≤ 1`, and
  -- differentiable a.e. (Rademacher).
  set d : Rn n → ℝ := fun y ↦ infDist y Uᶜ with hd_def
  have hdlip : LipschitzWith 1 d := lipschitz_infDist_pt Uᶜ
  have hdcont : Continuous d := hdlip.continuous
  have hd0 : ∀ x, x ∉ U → d x = 0 := fun x hx ↦ infDist_zero_of_mem hx
  have hdpos : ∀ x ∈ U, 0 < d x := fun x hx ↦
    (hUo.isClosed_compl.notMem_iff_infDist_pos hne).1 (not_not.2 hx)
  have hDd : ∀ x, ‖fderiv ℝ d x‖ ≤ 1 := fun x ↦ by
    simpa using norm_fderiv_le_of_lipschitz ℝ (x₀ := x) hdlip
  have hdiff : ∀ᵐ x ∂(volume : Measure (Rn n)), DifferentiableAt ℝ d x :=
    hdlip.ae_differentiableAt
  -- Step 3: the boundary-direction inequality near `∂U`.
  obtain ⟨η, hη, hkey⟩ :=
    Submission.bv_ext_infDist_compl_fderiv_lt n U ξ r hUo hUc hne hr hball
  -- Step 4: only countably many levels of `d` have positive measure, so we can pick `ε_j` with
  -- `{d = ε_j}` and `{d = ε_j / 2}` null.
  have hB : {t : ℝ | 0 < (volume : Measure (Rn n)) {y | d y = t}}.Countable :=
    Measure.countable_meas_level_set_pos hdcont.measurable
  have hB' : ({t : ℝ | 0 < (volume : Measure (Rn n)) {y | d y = t}} ∪
      (fun t ↦ 2 * t) '' {t : ℝ | 0 < (volume : Measure (Rn n)) {y | d y = t}}).Countable :=
    hB.union (hB.image _)
  have hε : ∀ j : ℕ, ∃ ε : ℝ, 0 < ε ∧ ε < η ∧ ε < 1 / ((j : ℝ) + 1) ∧
      (volume : Measure (Rn n)) {y | d y = ε} = 0 ∧
      (volume : Measure (Rn n)) {y | d y = ε / 2} = 0 := by
    intro j
    have hpos : 0 < min η (1 / ((j : ℝ) + 1)) := lt_min hη (by positivity)
    have hns : ¬ Ioo 0 (min η (1 / ((j : ℝ) + 1))) ⊆
        {t : ℝ | 0 < (volume : Measure (Rn n)) {y | d y = t}} ∪
        (fun t ↦ 2 * t) '' {t : ℝ | 0 < (volume : Measure (Rn n)) {y | d y = t}} := by
      intro hsub
      have h0 := measure_mono_null hsub (hB'.measure_zero volume)
      rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at h0
      linarith
    obtain ⟨ε, hεI, hεB⟩ := not_subset.1 hns
    refine ⟨ε, hεI.1, hεI.2.trans_le (min_le_left _ _), hεI.2.trans_le (min_le_right _ _), ?_, ?_⟩
    · by_contra h
      exact hεB (Or.inl (pos_iff_ne_zero.2 h))
    · by_contra h
      exact hεB (Or.inr ⟨ε / 2, pos_iff_ne_zero.2 h, by beta_reduce; ring⟩)
  choose ε hε0 hεη hεj hεnull hεnull2 using hε
  -- Step 5: the cut-offs `φ_j = min 1 (max 0 (2 d / ε_j - 1))`.
  set φ : ℕ → Rn n → ℝ := fun j x ↦ min 1 (max 0 (2 * d x / ε j - 1)) with hφ_def
  have hφ0 : ∀ j x, d x ≤ ε j / 2 → φ j x = 0 := by
    intro j x hx
    have h1 : 2 * d x / ε j - 1 ≤ 0 := by
      rw [sub_nonpos, div_le_one (hε0 j)]; linarith
    simp only [hφ_def, max_eq_left h1, min_eq_right zero_le_one]
  have hφ1 : ∀ j x, ε j ≤ d x → φ j x = 1 := by
    intro j x hx
    have h1 : 1 ≤ 2 * d x / ε j - 1 := by
      rw [le_sub_iff_add_le, le_div_iff₀ (hε0 j)]; linarith
    simp only [hφ_def, max_eq_right (zero_le_one.trans h1), min_eq_left h1]
  have hφlin : ∀ j x, ε j / 2 ≤ d x → d x ≤ ε j → φ j x = 2 * d x / ε j - 1 := by
    intro j x h1 h2
    have a1 : 0 ≤ 2 * d x / ε j - 1 := by
      rw [sub_nonneg, one_le_div (hε0 j)]; linarith
    have a2 : 2 * d x / ε j - 1 ≤ 1 := by
      rw [sub_le_iff_le_add, div_le_iff₀ (hε0 j)]; linarith
    simp only [hφ_def, max_eq_right a1, min_eq_right a2]
  -- Step 7: `tsupport φ_j ⊆ {ε_j / 2 ≤ d} ⊆ U`.
  have htsupp : ∀ j, tsupport (φ j) ⊆ {x | ε j / 2 ≤ d x} := by
    intro j
    refine closure_minimal ?_ (isClosed_le continuous_const hdcont)
    intro x hx
    by_contra h
    exact hx (hφ0 j x (le_of_lt (not_le.1 h)))
  have hFU : ∀ j, {x | ε j / 2 ≤ d x} ⊆ U := by
    intro j x hx
    by_contra h
    have h1 := hd0 x h
    have h2 := hε0 j
    simp only [mem_ofPred_eq] at hx
    linarith
  refine ⟨φ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Step 6: `φ_j` is `(2 / ε_j)`-Lipschitz.
    intro j
    have he := hε0 j
    have hlin : LipschitzWith (Real.toNNReal (2 / ε j)) (fun x ↦ 2 * d x / ε j - 1) := by
      refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
      rw [Real.coe_toNNReal _ (by positivity), Real.dist_eq]
      have hxy : |d x - d y| ≤ dist x y := by
        simpa [Real.dist_eq] using hdlip.dist_le_mul x y
      calc |2 * d x / ε j - 1 - (2 * d y / ε j - 1)| = 2 / ε j * |d x - d y| := by
            rw [show 2 * d x / ε j - 1 - (2 * d y / ε j - 1) = 2 / ε j * (d x - d y) by ring,
              abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / ε j)]
        _ ≤ 2 / ε j * dist x y := by gcongr
    exact ⟨_, (hlin.const_max 0).const_min 1⟩
  · -- Step 6: `0 ≤ φ_j ≤ 1`.
    intro j x
    exact ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩
  · -- Step 7: `{ε_j / 2 ≤ d}` is closed and bounded, hence compact.
    intro j
    have hF : IsCompact {x | ε j / 2 ≤ d x} :=
      Metric.isCompact_of_isClosed_isBounded (isClosed_le continuous_const hdcont)
        (hUb.subset (hFU j))
    exact hF.of_isClosed_subset (isClosed_tsupport _) (htsupp j)
  · intro j
    exact (htsupp j).trans (hFU j)
  · -- Step 8: `φ_j(x)` is eventually `1_U(x)`.
    intro x
    by_cases hx : x ∈ U
    · rw [indicator_of_mem hx]
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt (hdpos x hx)
      refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun j hj ↦ ?_⟩)
      symm
      apply hφ1
      have : 1 / ((j : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
        gcongr
      linarith [hεj j]
    · rw [indicator_of_notMem hx]
      refine tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun j ↦ ?_)
      symm
      apply hφ0
      rw [hd0 x hx]
      have := hε0 j
      linarith
  · -- Step 9: off `{d = ε_j} ∪ {d = ε_j / 2}` and the non-differentiability set of `d`, either
    -- `Dφ_j(x) = 0` or `Dφ_j(x) = (2 / ε_j) Dd(x)` with `0 < d(x) < ε_j < η`.
    intro j
    have he := hε0 j
    have hn1 : ∀ᵐ x ∂(volume : Measure (Rn n)), d x ≠ ε j := by
      rw [ae_iff]; simpa using hεnull j
    have hn2 : ∀ᵐ x ∂(volume : Measure (Rn n)), d x ≠ ε j / 2 := by
      rw [ae_iff]; simpa using hεnull2 j
    filter_upwards [hdiff, hn1, hn2] with x hxd hx1 hx2
    rcases lt_or_gt_of_ne hx2 with hlt | hgt
    · -- (a) `d x < ε_j / 2`: `φ_j = 0` near `x`.
      have hloc : φ j =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := by
        filter_upwards [(isOpen_lt hdcont continuous_const).mem_nhds hlt] with y hy
        exact hφ0 j y (le_of_lt hy)
      rw [hloc.fderiv_eq]
      simp
    rcases lt_or_gt_of_ne hx1 with hlt' | hgt'
    · -- (c) `ε_j / 2 < d x < ε_j`: `φ_j = 2 d / ε_j - 1` near `x`.
      have hloc : φ j =ᶠ[𝓝 x] fun y ↦ 2 * d y / ε j - 1 := by
        filter_upwards [(isOpen_lt continuous_const hdcont).mem_nhds hgt,
          (isOpen_lt hdcont continuous_const).mem_nhds hlt'] with y hy1 hy2
        exact hφlin j y (le_of_lt hy1) (le_of_lt hy2)
      have hderiv : fderiv ℝ (φ j) x = (2 / ε j) • fderiv ℝ d x := by
        rw [hloc.fderiv_eq]
        have hfun : (fun y ↦ 2 * d y / ε j - 1) = (fun y ↦ 2 / ε j * d y - 1) := by
          funext y; ring
        rw [hfun]
        exact ((hxd.hasFDerivAt.const_mul (2 / ε j)).sub_const 1).fderiv
      have hxU : x ∈ U := by
        by_contra h
        rw [hd0 x h] at hgt
        linarith
      have hk : r < -fderiv ℝ d x (x - ξ) := hkey x hxU (by linarith [hεη j]) hxd
      have h2e : (0 : ℝ) < 2 / ε j := by positivity
      rw [hderiv, norm_smul, smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_of_pos h2e]
      calc r * (2 / ε j * ‖fderiv ℝ d x‖) ≤ r * (2 / ε j * 1) := by
            gcongr
            exact hDd x
        _ = 2 / ε j * r := by ring
        _ ≤ 2 / ε j * (-fderiv ℝ d x (x - ξ)) := mul_le_mul_of_nonneg_left hk.le h2e.le
        _ = -(2 / ε j * fderiv ℝ d x (x - ξ)) := by ring
    · -- (b) `d x > ε_j`: `φ_j = 1` near `x`.
      have hloc : φ j =ᶠ[𝓝 x] fun _ ↦ (1 : ℝ) := by
        filter_upwards [(isOpen_lt continuous_const hdcont).mem_nhds hgt'] with y hy
        exact hφ1 j y (le_of_lt hy)
      rw [hloc.fderiv_eq]
      simp

end GMT.Ch02
