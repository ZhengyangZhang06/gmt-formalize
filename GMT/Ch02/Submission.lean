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

/-- **Euclidean divergence theorem for a field vanishing off a compact set.** If `V ⊆ ℝⁿ` is open,
`Q ⊆ V` is compact and `w : ℝⁿ → ℝⁿ` is `C¹` on `V` with `w = 0` on `V \ Q`, then
`∫_V trace Dw(x) dLⁿ(x) = 0`. The extension `W` of `w` by `0` off `V` is `C¹` on `ℝⁿ` with support
in `Q`, and `DW = Dw` on `V`, `DW = 0` off `Q`. Writing `trace DW = ∑ᵢ ⟨eᵢ, DW eᵢ⟩` in the standard
orthonormal basis `(eᵢ)`, each coordinate integral `∫ ⟨eᵢ, DW(x) eᵢ⟩ dx` vanishes by Mathlib's
integration by parts `LipschitzWith.integral_lineDeriv_mul_eq` against the constant function `1`. -/
theorem Submission.euclidean_setIntegral_trace_fderiv_eq_zero : ∀ (n : ℕ) (V Q : Set (Rn n)) (w : Rn n → Rn n), IsOpen V → IsCompact Q → Q ⊆ V → ContDiffOn ℝ 1 w V → (∀ x ∈ V, x ∉ Q → w x = 0) → ∫ x in V, LinearMap.trace ℝ (Rn n) (fderiv ℝ w x).toLinearMap = 0 := by
  intro n V Q w hV hQ hQV hw hw0
  -- Step 2 (extension by zero): `W = w` near each point of the open set `V`, and `W = 0` near
  -- each point of the open set `Qᶜ` (on `V \ Q` by hypothesis, off `V` by definition).
  let W : Rn n → Rn n := V.indicator w
  have hWV : ∀ x ∈ V, W =ᶠ[𝓝 x] w := fun x hx ↦
    Filter.eventuallyEq_of_mem (hV.mem_nhds hx) fun y hy ↦ indicator_of_mem hy w
  have hWQ : ∀ x ∉ Q, W =ᶠ[𝓝 x] fun _ ↦ 0 := fun x hx ↦
    Filter.eventuallyEq_of_mem (hQ.isClosed.isOpen_compl.mem_nhds hx) fun y hy ↦ by
      by_cases hyV : y ∈ V
      · simp [W, hyV, hw0 y hyV hy]
      · simp [W, hyV]
  -- Steps 3–4: `W` is `C¹` on `ℝⁿ = V ∪ Qᶜ` and has compact support (contained in `Q`).
  have hWc : ContDiff ℝ 1 W := contDiff_iff_contDiffAt.2 fun x ↦ by
    by_cases hx : x ∈ V
    · exact (hw.contDiffAt (hV.mem_nhds hx)).congr_of_eventuallyEq (hWV x hx)
    · exact contDiffAt_const.congr_of_eventuallyEq (hWQ x fun hxQ ↦ hx (hQV hxQ))
  have hWs : HasCompactSupport W := HasCompactSupport.intro hQ fun x hx ↦ (hWQ x hx).self_of_nhds
  -- Step 5: `DW = Dw` on `V` and `DW = 0` off `Q`.
  have hDV : ∀ x ∈ V, fderiv ℝ W x = fderiv ℝ w x := fun x hx ↦ (hWV x hx).fderiv_eq
  have hDQ : ∀ x ∉ Q, fderiv ℝ W x = 0 := fun x hx ↦ by
    rw [(hWQ x hx).fderiv_eq]
    simp
  -- Step 6: `∫_V trace Dw = ∫_V trace DW = ∫_{ℝⁿ} trace DW`, as `trace DW = 0` off `V ⊇ Q`.
  have h6a : ∫ x in V, LinearMap.trace ℝ (Rn n) (fderiv ℝ w x).toLinearMap
      = ∫ x in V, LinearMap.trace ℝ (Rn n) (fderiv ℝ W x).toLinearMap :=
    setIntegral_congr_fun hV.measurableSet fun x hx ↦ by rw [hDV x hx]
  have h6b : ∫ x in V, LinearMap.trace ℝ (Rn n) (fderiv ℝ W x).toLinearMap
      = ∫ x, LinearMap.trace ℝ (Rn n) (fderiv ℝ W x).toLinearMap :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [hDQ x fun hxQ ↦ hx (hQV hxQ)]
      simp
  -- Steps 7–8: `trace DW(x) = ∑ᵢ ⟨eᵢ, DW(x) eᵢ⟩` in the standard orthonormal basis `(eᵢ)`.
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have h8 : ∀ x, LinearMap.trace ℝ (Rn n) (fderiv ℝ W x).toLinearMap
      = ∑ i, inner ℝ (b i) (fderiv ℝ W x (b i)) := fun x ↦ by
    rw [LinearMap.trace_eq_sum_inner _ b]
    rfl
  -- Step 9: each summand is continuous with compact support, hence integrable.
  have h9 : ∀ i, Integrable (fun x ↦ inner ℝ (b i) (fderiv ℝ W x (b i))) := fun i ↦
    Continuous.integrable_of_hasCompactSupport
      (continuous_const.inner ((hWc.continuous_fderiv one_ne_zero).clm_apply continuous_const))
      ((hWs.fderiv_apply ℝ (b i)).comp_left (g := fun y : Rn n ↦ inner ℝ (b i) y)
        (inner_zero_right _))
  -- Steps 10–11: the coordinate `gᵢ = ⟨eᵢ, W⟩` is `C¹` with compact support, hence Lipschitz, and
  -- `Dgᵢ(x) eᵢ = ⟨eᵢ, DW(x) eᵢ⟩`. Integration by parts against `1` (whose line derivative is `0`)
  -- gives `0 = ∫ Dgᵢ(x)(-eᵢ) dx = -∫ ⟨eᵢ, DW(x) eᵢ⟩ dx`.
  have h10 : ∀ i, ∫ x, inner ℝ (b i) (fderiv ℝ W x (b i)) = 0 := fun i ↦ by
    let g : Rn n → ℝ := fun y ↦ inner ℝ (b i) (W y)
    have hgc : ContDiff ℝ 1 g := (innerSL ℝ (b i)).contDiff.comp hWc
    have hgs : HasCompactSupport g :=
      hWs.comp_left (g := fun y : Rn n ↦ inner ℝ (b i) y) (inner_zero_right _)
    obtain ⟨L, hL⟩ := hgc.lipschitzWith_of_hasCompactSupport hgs one_ne_zero
    have hibp := (LipschitzWith.const (α := Rn n) (1 : ℝ)).integral_lineDeriv_mul_eq
      (μ := volume) hL hgs (b i)
    have hd : ∀ x, lineDeriv ℝ g x (-b i) = -inner ℝ (b i) (fderiv ℝ W x (b i)) := fun x ↦ by
      have hx : HasFDerivAt g ((innerSL ℝ (b i)).comp (fderiv ℝ W x)) x :=
        (innerSL ℝ (b i)).hasFDerivAt.comp x ((hWc.differentiable one_ne_zero) x).hasFDerivAt
      rw [hx.differentiableAt.lineDeriv_eq_fderiv, hx.fderiv]
      simp
    have h0 : ∀ x, lineDeriv ℝ (fun _ : Rn n ↦ (1 : ℝ)) x (b i) = 0 := fun x ↦ by
      simp [lineDeriv]
    simp only [h0, zero_mul, integral_zero, hd, mul_one, integral_neg] at hibp
    exact neg_eq_zero.1 hibp.symm
  rw [h6a, h6b]
  simp_rw [h8]
  rw [integral_finsetSum _ fun i _ ↦ h9 i]
  exact Finset.sum_eq_zero fun i _ ↦ h10 i

/-- **Chart localization for the divergence identity** (Simon Ch. 2, 4.22(2)(*) and 4.30, p. 59,
in one chart via the area formula 3.2/3.5). Let `(V, W, ψ)` be a Simon local representation of class
`r ≥ 1` of a measurable `M ⊆ ℝᴺ`, `K ⊆ W` compact and `g = 0` on `M \ K`. If `w : ℝⁿ → ℝⁿ` is `C¹`
on `V`, `w = 0` at the points of `V` that `ψ` maps outside `K`, and `trace Dw = Jψ · (g ∘ ψ)` on
`V`, then `∫_M g dHⁿ = 0`. Restrict `∫_M` to the chart image `ψ(V) = W ∩ M`, pull it back to
`∫_V Jψ · (g ∘ ψ) dLⁿ` by the area formula, and apply the Euclidean divergence theorem
`Submission.euclidean_setIntegral_trace_fderiv_eq_zero` to `V`, `Q = V ∩ ψ⁻¹(K)` and `w`. -/
theorem Submission.chart_setIntegral_eq_zero_of_trace_fderiv_eq : ∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)) (V : Set (Rn n)) (W K : Set (Rn N)) (ψ : Rn n → Rn N) (g : Rn N → ℝ) (w : Rn n → Rn n), 1 ≤ r → Chapter02.IsSimonLocalRepresentation r M V W ψ → MeasurableSet M → IsCompact K → K ⊆ W → (∀ y ∈ M, y ∉ K → g y = 0) → ContDiffOn ℝ 1 w V → (∀ x ∈ V, ψ x ∉ K → w x = 0) → (∀ x ∈ V, LinearMap.trace ℝ (Rn n) (fderiv ℝ w x).toLinearMap = Chapter02.areaJacobianAt ψ x * g (ψ x)) → ∫ y in M, g y ∂μHE[n] = 0 := by
  classical
  /- Simon (3.2)/(3.5) in Bochner form: for an injective `Φ` with injective derivative on a
  measurable `s` and an arbitrary real weight `h`, `∫_{Φ(s)} h dHⁿ = ∫_s JΦ · (h ∘ Φ) dLⁿ`, where
  `JΦ = normDet DΦ`. This is the pinned SimonGMT theorem
  `Chapter02.integral_area_formula_of_injective_derivative`, whose module `Chapter02/WeightedArea`
  is not imported here; its kernel-checked proof (SimonGMT `Chapter02/AreaApproximation`,
  `AreaDerivative`, `AreaFormula`, `WeightedArea`, the derivative-control step adapted from
  Mathlib's `MeasureTheory/Function/Jacobian.lean`) is replayed as a local step. The image-measure
  part is the same replay as in the accepted node `Submission.coarea_chart_area_pullback`. No
  integrability of `h` is needed: both sides integrate `h` against one measure, transported along
  a measurable embedding. -/
  have area : ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F]
      [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
      (s : Set E) (Φ : E → F), MeasurableSet s → (∀ x ∈ s, DifferentiableAt ℝ Φ x) →
      (∀ x ∈ s, Function.Injective (fderiv ℝ Φ x)) → InjOn Φ s → ∀ h : F → ℝ,
      ∫ y in Φ '' s, h y ∂μHE[Module.finrank ℝ E] =
        ∫ x in s, (fderiv ℝ Φ x).toLinearMap.normDet * h (Φ x) := by
    intro E F _ _ _ _ _ _ _ _ _ _ s Φ hs hΦ hregΦ hinjΦ h
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
    -- Measure-level transport, then the Bochner integral of an arbitrary real weight.
    have hcont : ContinuousOn Φ s := fun x hx ↦ (hΦ x hx).continuousAt.continuousWithinAt
    have hemb : MeasurableEmbedding (s.domRestrict Φ) := hcont.measurableEmbedding hs hinjΦ
    have hsub := MeasurableEmbedding.subtype_coe hs
    have hJmeas : Measurable (fun x : E ↦ (fderiv ℝ Φ x).toLinearMap.normDet) :=
      hcontJ.measurable.comp (measurable_fderiv ℝ Φ)
    have hmap : Measure.map (s.domRestrict Φ)
        (((volume : Measure E).withDensity
          (fun x ↦ ENNReal.ofReal (fderiv ℝ Φ x).toLinearMap.normDet)).comap
            (Subtype.val : s → E)) = (μHE[Module.finrank ℝ E] : Measure F).restrict (Φ '' s) := by
      ext u hu
      rw [Measure.map_apply hemb.measurable hu, hsub.comap_apply]
      have hBm : MeasurableSet (Subtype.val '' ((s.domRestrict Φ) ⁻¹' u)) :=
        hsub.measurableSet_image' (hemb.measurable hu)
      have hBs : Subtype.val '' ((s.domRestrict Φ) ⁻¹' u) ⊆ s := by
        rintro x ⟨v, _, rfl⟩
        exact v.property
      rw [withDensity_apply _ hBm, ← hcore _ hBm hBs, Measure.restrict_apply hu]
      congr 1
      ext y
      constructor
      · rintro ⟨x, ⟨v, hv, rfl⟩, rfl⟩
        exact ⟨hv, ⟨v, v.property, rfl⟩⟩
      · rintro ⟨hy, x, hx, rfl⟩
        exact ⟨x, ⟨⟨x, hx⟩, hy, rfl⟩, rfl⟩
    rw [← hmap, hemb.integral_map]
    change (∫ x : s, (fun x : E ↦ h (Φ x)) x ∂
      (((volume : Measure E).withDensity
        (fun x ↦ (((fderiv ℝ Φ x).toLinearMap.normDet.toNNReal : ℝ≥0) : ℝ≥0∞))).comap
          (Subtype.val : s → E))) = _
    rw [integral_subtype_comap hs (fun x : E ↦ h (Φ x)),
      setIntegral_withDensity_eq_setIntegral_smul₀ hJmeas.real_toNNReal.aemeasurable _ hs]
    refine setIntegral_congr_fun hs ?_
    intro x _
    show ((fderiv ℝ Φ x).toLinearMap.normDet.toNNReal : ℝ≥0) • h (Φ x) =
      (fderiv ℝ Φ x).toLinearMap.normDet * h (Φ x)
    rw [NNReal.smul_def, Real.coe_toNNReal _ (LinearMap.normDet_nonneg _), smul_eq_mul]
  intro n N r M V W K ψ g w hr hψ hM hK hKW hgK hw hwK htrace
  /- Step 1: the compact parameter set `Q = V ∩ ψ⁻¹(K)` (relative properness of the
  representation), with `w = 0` on `V \ Q`. -/
  have hV : IsOpen V := hψ.isOpen_source
  have hQ : IsCompact (V ∩ ψ ⁻¹' K) := hψ.isCompact_source_inter_preimage K hK hKW
  have hwQ : ∀ x ∈ V, x ∉ V ∩ ψ ⁻¹' K → w x = 0 := fun x hx hxQ ↦
    hwK x hx fun hxK ↦ hxQ ⟨hx, hxK⟩
  /- Step 2: `ψ(V) = W ∩ M ⊆ M`, and `g = 0` on `M \ ψ(V) = M \ W ⊆ M \ K`, so
  `∫_M g dHⁿ = ∫_{ψ(V)} g dHⁿ` (an identity of Bochner integrals; no integrability needed). -/
  have himage : ψ '' V = W ∩ M := hψ.image_eq
  have hrestrict : ∫ y in M, g y ∂μHE[n] = ∫ y in ψ '' V, g y ∂μHE[n] := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hM ?_ ?_
    · rw [himage]
      exact inter_subset_right
    · rintro y ⟨hyM, hyV⟩
      refine hgK y hyM fun hyK ↦ hyV ?_
      rw [himage]
      exact ⟨hKW hyK, hyM⟩
  /- Step 3: `ψ` is `C^r`, `r ≥ 1`, hence differentiable at every point of the open set `V`; its
  derivative is injective on `V` and `ψ` is injective on `V`. -/
  have hdiff : ∀ x ∈ V, DifferentiableAt ℝ ψ x := fun x hx ↦
    (hψ.contDiffOn.differentiableOn
      (by exact_mod_cast (ne_of_gt (lt_of_lt_of_le (show (0 : ℕ∞) < 1 by simp) hr))) x
      hx).differentiableAt (hV.mem_nhds hx)
  /- Step 4: the area formula for `ψ` on `V`, with `finrank ℝⁿ = n`. -/
  have key := area (Rn n) (Rn N) V ψ hV.measurableSet hdiff
    (fun x hx ↦ hψ.injective_fderiv hx) hψ.injOn g
  rw [finrank_euclideanSpace_fin] at key
  /- Steps 5–7: `Jψ · (g ∘ ψ) = trace Dw` on `V`, and the Euclidean divergence theorem for
  `(V, Q, w)`. -/
  rw [hrestrict, key]
  calc ∫ x in V, (fderiv ℝ ψ x).toLinearMap.normDet * g (ψ x)
      = ∫ x in V, LinearMap.trace ℝ (Rn n) (fderiv ℝ w x).toLinearMap := by
        refine setIntegral_congr_fun hV.measurableSet ?_
        intro x hx
        show (fderiv ℝ ψ x).toLinearMap.normDet * g (ψ x) =
          LinearMap.trace ℝ (Rn n) (fderiv ℝ w x).toLinearMap
        rw [htrace x hx, Chapter02.areaJacobianAt_eq_normDet]
    _ = 0 := Submission.euclidean_setIntegral_trace_fderiv_eq_zero n V (V ∩ ψ ⁻¹' K) w hV hQ
        inter_subset_left hw hwQ
/-- **Simon Ch. 2, divergence theorem on a submanifold (4.22(*), 4.29–4.30), proof steps 3a–3b:
a finite `C¹` partition of unity near a compact set.** If `C ⊆ ℝᴺ` is compact and every `y ∈ C`
lies in an open `U` with `P U`, there are finitely many `C¹` compactly supported `ζ_q` with
`tsupport ζ_q ⊆ U_q`, `P U_q`, and `∑_q ζ_q = 1` on an open `O ⊇ C`. Cover `C` by finitely many
open balls `ball c_q (ε_q / 4)` with `ball c_q ε_q ⊆ U_{c_q}`, take bumps `β_q` equal to `1` on
`closedBall c_q (ε_q / 4)` with `tsupport β_q = closedBall c_q (ε_q / 2)`, and set
`ζ_q = β_q ∏_{l<q} (1 - β_l)`; telescoping gives `∑_q ζ_q = 1 - ∏_q (1 - β_q)`, which is `1` on
`O = ⋃_q ball c_q (ε_q / 4)`. -/
theorem Submission.exists_finite_contDiff_partition_near_compact : ∀ (N : ℕ) (C : Set (Rn N)) (P : Set (Rn N) → Prop), IsCompact C → (∀ y ∈ C, ∃ U : Set (Rn N), IsOpen U ∧ y ∈ U ∧ P U) → ∃ (p : ℕ) (ζ : Fin p → Rn N → ℝ) (O : Set (Rn N)), IsOpen O ∧ C ⊆ O ∧ (∀ z ∈ O, ∑ q, ζ q z = 1) ∧ ∀ q, ContDiff ℝ 1 (ζ q) ∧ HasCompactSupport (ζ q) ∧ ∃ U : Set (Rn N), P U ∧ tsupport (ζ q) ⊆ U := by
  intro N C P hC hP
  -- Step 1: radii `ε_y > 0` with `ball y ε_y ⊆ U_y` and `P U_y`.
  have hrad : ∀ y ∈ C, ∃ ε > 0, ∃ U : Set (Rn N), P U ∧ ball y ε ⊆ U := fun y hy ↦ by
    obtain ⟨U, hUo, hyU, hPU⟩ := hP y hy
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hUo y hyU
    exact ⟨ε, hε, U, hPU, hεU⟩
  choose! ε hε U hPU hεU using hrad
  -- Step 2: a finite subcover of `C` by the balls `ball c_q (ε_q / 4)`, `q : Fin p`.
  obtain ⟨p, c, hcC, hCc⟩ : ∃ (p : ℕ) (c : Fin p → Rn N), (∀ q, c q ∈ C) ∧
      C ⊆ ⋃ q, ball (c q) (ε (c q) / 4) := by
    obtain ⟨T, hTC, hCT⟩ := hC.elim_nhds_subcover (fun y ↦ ball y (ε y / 4))
      fun y hy ↦ ball_mem_nhds y (by linarith [hε y hy])
    refine ⟨T.card, fun q ↦ T.equivFin.symm q, fun q ↦ hTC _ (T.equivFin.symm q).2, fun z hz ↦ ?_⟩
    obtain ⟨y, hyT, hzy⟩ := mem_iUnion₂.1 (hCT hz)
    exact mem_iUnion.2 ⟨T.equivFin ⟨y, hyT⟩, by simpa using hzy⟩
  have hεc : ∀ q, 0 < ε (c q) := fun q ↦ hε _ (hcC q)
  -- Step 3: bumps `β_q` at `c_q` with radii `ε_q / 4 < ε_q / 2`.
  let β : ∀ q, ContDiffBump (c q) := fun q ↦
    ⟨ε (c q) / 4, ε (c q) / 2, by linarith [hεc q], by linarith [hεc q]⟩
  -- Step 4: `ζ_q = β_q ∏_{l<q} (1 - β_l)` and `O = ⋃_q ball c_q (ε_q / 4)`.
  refine ⟨p, fun q x ↦ β q x * ∏ l ∈ Finset.univ with l < q, (1 - β l x),
    ⋃ q, ball (c q) (ε (c q) / 4), isOpen_iUnion fun q ↦ isOpen_ball, hCc, fun z hz ↦ ?_,
    fun q ↦ ⟨?_, ?_, U (c q), hPU _ (hcC q), ?_⟩⟩
  -- Steps 6–7: `∑_q ζ_q = 1 - ∏_q (1 - β_q)`, and some `β_q` equals `1` at each point of `O`.
  · obtain ⟨q₀, hzq₀⟩ := mem_iUnion.1 hz
    have h1 : β q₀ z = 1 := (β q₀).one_of_mem_closedBall (ball_subset_closedBall hzq₀)
    have h0 : ∏ q, (1 - β q z) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ q₀) (sub_eq_zero.2 h1.symm)
    have key := Finset.prod_one_sub_ordered Finset.univ fun q ↦ β q z
    rw [h0, eq_comm, sub_eq_zero] at key
    exact key.symm
  -- Step 5: `ζ_q` is `C¹` with compact support, and
  -- `tsupport ζ_q ⊆ closedBall c_q (ε_q / 2) ⊆ ball c_q ε_q ⊆ U_{c_q}`.
  · exact (β q).contDiff.mul (contDiff_prod fun l _ ↦ contDiff_const.sub (β l).contDiff)
  · exact (β q).hasCompactSupport.mul_right
  · calc tsupport (fun x ↦ β q x * ∏ l ∈ Finset.univ with l < q, (1 - β l x))
        ⊆ tsupport (β q) := tsupport_mul_subset_left
      _ = closedBall (c q) (ε (c q) / 2) := (β q).tsupport_eq
      _ ⊆ ball (c q) (ε (c q)) := closedBall_subset_ball (by linarith [hεc q])
      _ ⊆ U (c q) := hεU _ (hcC q)

/-- The frozen Chapter 2 contract: the conjunction of all headline results. -/
theorem main_theorem : LipschitzExtension ∧ Rademacher ∧ C1Approximation ∧ WhitneyExtension ∧ LipschitzImageHausdorff ∧ EilenbergInequality ∧ BVCompactness ∧ BVPoincare ∧ BVExtensionEstimate ∧ AreaFormula ∧ FirstVariation ∧ SecondVariation ∧ StationaryIffMeanCurvatureZero ∧ SecondVariationStationary ∧ CoareaFormula ∧ C1Sard := by sorry

end GMT.Ch02
