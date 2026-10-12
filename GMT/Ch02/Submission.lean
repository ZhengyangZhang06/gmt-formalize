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

/-- **Level-set (Markov) step of Simon 2.7.** Let `U ⊆ ℝⁿ` be measurable, `u` a.e.-measurable on
`U`, `θ > 0`, and let `β, c` be constants with
`θ Lⁿ(U) ≤ min {Lⁿ{x ∈ U : u ≥ β}, Lⁿ{x ∈ U : u ≤ β}}` (outer measures; the level sets need not be
measurable). Then `∫_U |u - β| ≤ (1 + θ⁻¹) ∫_U |u - c|` in `[0, ∞]`. Write `I = ∫_U |u - c|` and
`a = |c - β|`. The triangle inequality gives `∫_U |u - β| ≤ I + a Lⁿ(U)`. The level set `{u ≥ β}`
(if `c ≤ β`) or `{u ≤ β}` (if `β < c`) lies in `{|u - c| ≥ a}`, so Markov's inequality
(`mul_meas_ge_le_lintegral₀`) gives `a θ Lⁿ(U) ≤ I`; multiplying by `θ⁻¹` gives `a Lⁿ(U) ≤ θ⁻¹ I`. -/
theorem Submission.poincare_level_set_lintegral_le : ∀ (n : ℕ) (U : Set (Rn n)) (u : Rn n → ℝ) (θ β c : ℝ), MeasurableSet U → AEMeasurable u (volume.restrict U) → 0 < θ → ENNReal.ofReal θ * volume U ≤ min (volume {x ∈ U | β ≤ u x}) (volume {x ∈ U | u x ≤ β}) → ∫⁻ x in U, ‖u x - β‖ₑ ≤ ENNReal.ofReal (1 + θ⁻¹) * ∫⁻ x in U, ‖u x - c‖ₑ := by
  intro n U u θ β c hU hu hθ hlev
  -- Step 1: integrate `‖u x - β‖ₑ ≤ ‖u x - c‖ₑ + ‖c - β‖ₑ` over `U`.
  have h1 : ∫⁻ x in U, ‖u x - β‖ₑ ≤ (∫⁻ x in U, ‖u x - c‖ₑ) + ‖c - β‖ₑ * volume U :=
    calc ∫⁻ x in U, ‖u x - β‖ₑ ≤ ∫⁻ x in U, (‖u x - c‖ₑ + ‖c - β‖ₑ) :=
          lintegral_mono fun x ↦ by
            simpa only [sub_add_sub_cancel] using enorm_add_le (u x - c) (c - β)
      _ = (∫⁻ x in U, ‖u x - c‖ₑ) + ‖c - β‖ₑ * volume U := by
          rw [lintegral_add_right _ measurable_const, setLIntegral_const]
  -- Step 2: the relevant level set lies in `{‖c - β‖ₑ ≤ ‖u - c‖ₑ}`; apply Markov on `U`.
  have hlevel : ENNReal.ofReal θ * volume U ≤ volume ({x | ‖c - β‖ₑ ≤ ‖u x - c‖ₑ} ∩ U) := by
    rcases le_or_gt c β with hcb | hbc
    · -- (a) `c ≤ β`: if `β ≤ u x` then `|u x - c| ≥ β - c = |c - β|`.
      have hsub : {x ∈ U | β ≤ u x} ⊆ {x | ‖c - β‖ₑ ≤ ‖u x - c‖ₑ} ∩ U := fun x hx ↦ by
        refine ⟨?_, hx.1⟩
        show ‖c - β‖ₑ ≤ ‖u x - c‖ₑ
        rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, abs_sub_comm c β,
          abs_of_nonneg (sub_nonneg.2 hcb)]
        exact ENNReal.ofReal_le_ofReal (by linarith [hx.2, le_abs_self (u x - c)])
      exact (hlev.trans (min_le_left _ _)).trans (measure_mono hsub)
    · -- (b) `β < c`: if `u x ≤ β` then `|u x - c| ≥ c - β = |c - β|`.
      have hsub : {x ∈ U | u x ≤ β} ⊆ {x | ‖c - β‖ₑ ≤ ‖u x - c‖ₑ} ∩ U := fun x hx ↦ by
        refine ⟨?_, hx.1⟩
        show ‖c - β‖ₑ ≤ ‖u x - c‖ₑ
        rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, abs_of_pos (sub_pos.2 hbc)]
        exact ENNReal.ofReal_le_ofReal (by linarith [hx.2, neg_le_abs (u x - c)])
      exact (hlev.trans (min_le_right _ _)).trans (measure_mono hsub)
  have h2 : ‖c - β‖ₑ * (ENNReal.ofReal θ * volume U) ≤ ∫⁻ x in U, ‖u x - c‖ₑ :=
    calc ‖c - β‖ₑ * (ENNReal.ofReal θ * volume U)
        ≤ ‖c - β‖ₑ * volume ({x | ‖c - β‖ₑ ≤ ‖u x - c‖ₑ} ∩ U) := by gcongr
      _ = ‖c - β‖ₑ * (volume.restrict U) {x | ‖c - β‖ₑ ≤ ‖u x - c‖ₑ} := by
          rw [Measure.restrict_apply' hU]
      _ ≤ ∫⁻ x in U, ‖u x - c‖ₑ := mul_meas_ge_le_lintegral₀ (hu.sub_const c).enorm _
  -- Step 3: multiply by `ofReal θ⁻¹`, using `ofReal θ⁻¹ * ofReal θ = 1`.
  have hinv : ENNReal.ofReal θ⁻¹ * ENNReal.ofReal θ = 1 := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hθ.le), inv_mul_cancel₀ hθ.ne', ENNReal.ofReal_one]
  have h3 : ‖c - β‖ₑ * volume U ≤ ENNReal.ofReal θ⁻¹ * ∫⁻ x in U, ‖u x - c‖ₑ :=
    calc ‖c - β‖ₑ * volume U
        = ENNReal.ofReal θ⁻¹ * ENNReal.ofReal θ * (‖c - β‖ₑ * volume U) := by
          rw [hinv, one_mul]
      _ = ENNReal.ofReal θ⁻¹ * (‖c - β‖ₑ * (ENNReal.ofReal θ * volume U)) := by ring
      _ ≤ ENNReal.ofReal θ⁻¹ * ∫⁻ x in U, ‖u x - c‖ₑ := by gcongr
  -- Step 4: `I + ofReal θ⁻¹ * I = ofReal (1 + θ⁻¹) * I`.
  calc ∫⁻ x in U, ‖u x - β‖ₑ ≤ (∫⁻ x in U, ‖u x - c‖ₑ) + ‖c - β‖ₑ * volume U := h1
    _ ≤ (∫⁻ x in U, ‖u x - c‖ₑ) + ENNReal.ofReal θ⁻¹ * ∫⁻ x in U, ‖u x - c‖ₑ := by gcongr
    _ = ENNReal.ofReal (1 + θ⁻¹) * ∫⁻ x in U, ‖u x - c‖ₑ := by
        rw [ENNReal.ofReal_add zero_le_one (inv_nonneg.2 hθ.le), ENNReal.ofReal_one, add_mul,
          one_mul]
/-- **Poincaré inequality for `C¹` functions on bounded convex open sets** (step B1 of the proof of
Simon 2.7, "the usual Poincaré inequality for smooth functions"). If `O ⊆ ℝⁿ` is open, bounded and
convex and `w` is `C¹`, then `∫_O |w - w̄| ≤ 2ⁿ diam(O) ∫_O |Dw|`, where `w̄` is the mean of `w` over
`O`. For `x, y ∈ O` the fundamental theorem of calculus along the segment gives
`|w(x) - w(y)| ≤ diam(O) ∫₀¹ |Dw(x + t(y - x))| dt`. After Tonelli, the dilation `y ↦ (1 - t)x + ty`
(for `t ≥ 1/2`) or `x ↦ (1 - t)x + ty` (for `t < 1/2`) costs a factor at most `2ⁿ`
(`Measure.map_addHaar_smul`), and averaging over `y` bounds `|w(x) - w̄|`. -/
theorem Submission.convex_poincare_smooth_lintegral_le : ∀ (n : ℕ) (O : Set (Rn n)) (w : Rn n → ℝ), IsOpen O → Bornology.IsBounded O → Convex ℝ O → ContDiff ℝ 1 w → ∫⁻ x in O, ‖w x - (volume O).toReal⁻¹ * ∫ y in O, w y‖ₑ ≤ ENNReal.ofReal (2 ^ n * Metric.diam O) * ∫⁻ x in O, ‖fderiv ℝ w x‖ₑ := by
  intro n O w hO hOb hOc hw
  -- Step 1: the case `O = ∅` is trivial.
  rcases O.eq_empty_or_nonempty with rfl | hne
  · simp
  -- Step 3: dilation identity `∫⁻ F(a + s•y) dy = ofReal((sⁿ)⁻¹) ∫⁻ F`.
  have dil : ∀ (F : Rn n → ℝ≥0∞) (a : Rn n) (s : ℝ), 0 < s →
      ∫⁻ y, F (a + s • y) = ENNReal.ofReal ((s ^ n)⁻¹) * ∫⁻ y, F y := by
    intro F a s hs
    have hmap := Measure.map_addHaar_smul (volume : Measure (Rn n)) hs.ne'
    rw [finrank_euclideanSpace_fin, abs_of_pos (inv_pos.mpr (pow_pos hs n))] at hmap
    have hemb : MeasurableEmbedding (fun y : Rn n ↦ s • y) :=
      (Homeomorph.smulOfNeZero s hs.ne').measurableEmbedding
    calc ∫⁻ y, F (a + s • y)
          = ∫⁻ z, F (a + z) ∂(Measure.map (fun y : Rn n ↦ s • y) volume) := by
          rw [hemb.lintegral_map]
      _ = ENNReal.ofReal ((s ^ n)⁻¹) * ∫⁻ z, F (a + z) := by
          rw [hmap, lintegral_smul_measure]; rfl
      _ = ENNReal.ofReal ((s ^ n)⁻¹) * ∫⁻ y, F y := by
          rw [lintegral_add_left_eq_self]
  have half : ∀ s : ℝ, 1 / 2 ≤ s → ENNReal.ofReal ((s ^ n)⁻¹) ≤ 2 ^ n := by
    intro s hs
    have hs0 : 0 < s := by linarith
    have h1 : s⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hs0 (by norm_num)]; linarith
    calc ENNReal.ofReal ((s ^ n)⁻¹) ≤ ENNReal.ofReal (2 ^ n) := by
          apply ENNReal.ofReal_le_ofReal
          rw [← inv_pow]
          exact pow_le_pow_left₀ (inv_nonneg.mpr hs0.le) h1 n
      _ = 2 ^ n := by rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  -- Step 4 (first half): FTC along the segment.
  have seg : ∀ x y : Rn n, ‖w x - w y‖ₑ
      ≤ ∫⁻ t in Ioc (0:ℝ) 1, ‖fderiv ℝ w (x + t • (y - x))‖ₑ * ‖y - x‖ₑ := by
    intro x y
    have hdiff : Differentiable ℝ w := hw.differentiable one_ne_zero
    have hderiv : ∀ t ∈ uIcc (0:ℝ) 1, HasDerivAt (fun t : ℝ ↦ w (x + t • (y - x)))
        (fderiv ℝ w (x + t • (y - x)) (y - x)) t := by
      intro t _
      have hg : HasDerivAt (fun t : ℝ ↦ x + t • (y - x)) (y - x) t := by
        simpa using ((hasDerivAt_id t).smul_const (y - x)).const_add x
      exact (hdiff _).hasFDerivAt.comp_hasDerivAt t hg
    have hint : IntervalIntegrable (fun t : ℝ ↦ fderiv ℝ w (x + t • (y - x)) (y - x))
        volume 0 1 := by
      have hcont : Continuous (fun z ↦ fderiv ℝ w z) := hw.continuous_fderiv one_ne_zero
      apply Continuous.intervalIntegrable
      fun_prop
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    rw [intervalIntegral.integral_of_le zero_le_one] at hftc
    simp only [zero_smul, add_zero, one_smul, add_sub_cancel] at hftc
    calc ‖w x - w y‖ₑ = ‖w y - w x‖ₑ := by rw [← enorm_neg, neg_sub]
      _ = ‖∫ t in Ioc (0:ℝ) 1, fderiv ℝ w (x + t • (y - x)) (y - x)‖ₑ := by rw [hftc]
      _ ≤ ∫⁻ t in Ioc (0:ℝ) 1, ‖fderiv ℝ w (x + t • (y - x)) (y - x)‖ₑ :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ t in Ioc (0:ℝ) 1, ‖fderiv ℝ w (x + t • (y - x))‖ₑ * ‖y - x‖ₑ := by
          apply lintegral_mono
          intro t
          exact ContinuousLinearMap.le_opENorm _ _
  -- Steps 5–6: Tonelli and the dilation bound.
  have double : ∀ F : Rn n → ℝ≥0∞, Measurable F →
      ∫⁻ x in O, ∫⁻ y in O, ∫⁻ t in Ioc (0:ℝ) 1, F (x + t • (y - x))
        ≤ 2 ^ n * (∫⁻ z, F z) * volume O := by
    intro F hF
    have swap1 : ∀ x, ∫⁻ y in O, ∫⁻ t in Ioc (0:ℝ) 1, F (x + t • (y - x))
        = ∫⁻ t in Ioc (0:ℝ) 1, ∫⁻ y in O, F (x + t • (y - x)) := by
      intro x
      apply lintegral_lintegral_swap
      exact (hF.comp (by fun_prop)).aemeasurable
    have swap2 : ∫⁻ x in O, ∫⁻ t in Ioc (0:ℝ) 1, ∫⁻ y in O, F (x + t • (y - x))
        = ∫⁻ t in Ioc (0:ℝ) 1, ∫⁻ x in O, ∫⁻ y in O, F (x + t • (y - x)) := by
      apply lintegral_lintegral_swap
      exact (Measurable.lintegral_prod_right'
        (f := fun q : (Rn n × ℝ) × Rn n ↦ F (q.1.1 + q.1.2 • (q.2 - q.1.1)))
        (hF.comp (by fun_prop))).aemeasurable
    rw [lintegral_congr swap1, swap2]
    -- Step 6: `J(t) ≤ 2ⁿ (∫⁻ F) μ(O)` for `t ∈ (0, 1]`.
    have hJ : ∀ t ∈ Ioc (0:ℝ) 1, ∫⁻ x in O, ∫⁻ y in O, F (x + t • (y - x))
        ≤ 2 ^ n * (∫⁻ z, F z) * volume O := by
      intro t ht
      by_cases h2 : 1 / 2 ≤ t
      · -- (a) `t ≥ 1/2`: dilate in `y`.
        calc ∫⁻ x in O, ∫⁻ y in O, F (x + t • (y - x))
              ≤ ∫⁻ x in O, 2 ^ n * ∫⁻ z, F z := by
              apply lintegral_mono; intro x
              calc ∫⁻ y in O, F (x + t • (y - x)) ≤ ∫⁻ y, F (x + t • (y - x)) :=
                    setLIntegral_le_lintegral _ _
                _ = ∫⁻ y, F ((1 - t) • x + t • y) := by
                    congr 1; ext y; congr 1; module
                _ = ENNReal.ofReal ((t ^ n)⁻¹) * ∫⁻ z, F z := dil F ((1 - t) • x) t ht.1
                _ ≤ 2 ^ n * ∫⁻ z, F z := by gcongr; exact half t h2
          _ = 2 ^ n * (∫⁻ z, F z) * volume O := setLIntegral_const _ _
      · -- (b) `t < 1/2`: swap `x` and `y`, then dilate in `x`.
        push Not at h2
        have hm : Measurable (Function.uncurry fun x y : Rn n ↦ F (x + t • (y - x))) :=
          hF.comp (by fun_prop)
        rw [lintegral_lintegral_swap hm.aemeasurable]
        calc ∫⁻ y in O, ∫⁻ x in O, F (x + t • (y - x))
              ≤ ∫⁻ y in O, 2 ^ n * ∫⁻ z, F z := by
              apply lintegral_mono; intro y
              calc ∫⁻ x in O, F (x + t • (y - x)) ≤ ∫⁻ x, F (x + t • (y - x)) :=
                    setLIntegral_le_lintegral _ _
                _ = ∫⁻ x, F (t • y + (1 - t) • x) := by
                    congr 1; ext x; congr 1; module
                _ = ENNReal.ofReal (((1 - t) ^ n)⁻¹) * ∫⁻ z, F z :=
                    dil F (t • y) (1 - t) (by linarith)
                _ ≤ 2 ^ n * ∫⁻ z, F z := by gcongr; exact half (1 - t) (by linarith)
          _ = 2 ^ n * (∫⁻ z, F z) * volume O := setLIntegral_const _ _
    calc ∫⁻ t in Ioc (0:ℝ) 1, ∫⁻ x in O, ∫⁻ y in O, F (x + t • (y - x))
          ≤ ∫⁻ t in Ioc (0:ℝ) 1, 2 ^ n * (∫⁻ z, F z) * volume O :=
          setLIntegral_mono' measurableSet_Ioc hJ
      _ = 2 ^ n * (∫⁻ z, F z) * volume O := by
          rw [setLIntegral_const, Real.volume_Ioc]; simp
  -- Step 7: the mean step, `‖w x - w̄‖ₑ ≤ μ(O)⁻¹ ∫⁻_O ‖w x - w y‖ₑ dy`.
  have hm0 : volume O ≠ 0 := (hO.measure_pos volume hne).ne'
  have hmt : volume O ≠ ⊤ := hOb.measure_lt_top.ne
  have hwint : IntegrableOn w O volume :=
    (hw.continuous.continuousOn.integrableOn_compact hOb.isCompact_closure).mono_set subset_closure
  have mean : ∀ x, ‖w x - (volume O).toReal⁻¹ * ∫ y in O, w y‖ₑ
      ≤ (volume O)⁻¹ * ∫⁻ y in O, ‖w x - w y‖ₑ := by
    intro x
    have hI : ∫ y in O, (w x - w y) = (volume O).toReal * w x - ∫ y in O, w y := by
      rw [integral_sub (integrableOn_const (C := w x) hmt) hwint, setIntegral_const, smul_eq_mul,
        measureReal_def]
    have hmR : (volume O).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hm0, hmt⟩
    have key : w x - (volume O).toReal⁻¹ * ∫ y in O, w y
        = (volume O).toReal⁻¹ * ∫ y in O, (w x - w y) := by
      rw [hI]; field_simp
    have hinv : ‖(volume O).toReal⁻¹‖ₑ = (volume O)⁻¹ := by
      rw [Real.enorm_of_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg), ← ENNReal.toReal_inv,
        ENNReal.ofReal_toReal (ENNReal.inv_ne_top.mpr hm0)]
    rw [key, enorm_mul, hinv]
    gcongr
    exact enorm_integral_le_lintegral_enorm _
  -- Step 2 and Step 4 (second half): the indicator `F` and the pointwise segment bound.
  have hcont : Continuous (fun z ↦ fderiv ℝ w z) := hw.continuous_fderiv one_ne_zero
  set F : Rn n → ℝ≥0∞ := O.indicator (fun z ↦ ‖fderiv ℝ w z‖ₑ) with hFdef
  have hF : Measurable F := (hcont.enorm.measurable).indicator hO.measurableSet
  have hFint : ∫⁻ z, F z = ∫⁻ x in O, ‖fderiv ℝ w x‖ₑ := lintegral_indicator hO.measurableSet _
  set D := Metric.diam O with hD
  have hseg : ∀ x ∈ O, ∀ y ∈ O, ‖w x - w y‖ₑ
      ≤ ENNReal.ofReal D * ∫⁻ t in Ioc (0:ℝ) 1, F (x + t • (y - x)) := by
    intro x hx y hy
    calc ‖w x - w y‖ₑ ≤ ∫⁻ t in Ioc (0:ℝ) 1, ‖fderiv ℝ w (x + t • (y - x))‖ₑ * ‖y - x‖ₑ :=
          seg x y
      _ ≤ ∫⁻ t in Ioc (0:ℝ) 1, ENNReal.ofReal D * F (x + t • (y - x)) := by
          apply setLIntegral_mono' measurableSet_Ioc
          intro t ht
          have hmem : x + t • (y - x) ∈ O := hOc.add_smul_sub_mem hx hy ⟨ht.1.le, ht.2⟩
          rw [hFdef, indicator_of_mem hmem, mul_comm]
          gcongr
          rw [← ofReal_norm, ← dist_eq_norm]
          exact ENNReal.ofReal_le_ofReal (dist_le_diam_of_mem hOb hy hx)
      _ = ENNReal.ofReal D * ∫⁻ t in Ioc (0:ℝ) 1, F (x + t • (y - x)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  -- (★) `∫⁻_O ∫⁻_O ‖w x - w y‖ₑ ≤ diam(O) 2ⁿ (∫⁻ F) μ(O)`.
  have hstar : ∫⁻ x in O, ∫⁻ y in O, ‖w x - w y‖ₑ
      ≤ ENNReal.ofReal D * (2 ^ n * (∫⁻ z, F z) * volume O) := by
    calc ∫⁻ x in O, ∫⁻ y in O, ‖w x - w y‖ₑ
          ≤ ∫⁻ x in O, ∫⁻ y in O, ENNReal.ofReal D * ∫⁻ t in Ioc (0:ℝ) 1, F (x + t • (y - x)) := by
          apply setLIntegral_mono' hO.measurableSet; intro x hx
          apply setLIntegral_mono' hO.measurableSet; intro y hy
          exact hseg x hx y hy
      _ = ENNReal.ofReal D * ∫⁻ x in O, ∫⁻ y in O, ∫⁻ t in Ioc (0:ℝ) 1, F (x + t • (y - x)) := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1; ext x
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal D * (2 ^ n * (∫⁻ z, F z) * volume O) := by
          gcongr; exact double F hF
  -- Step 8: integrate the mean step over `x` and cancel `μ(O)⁻¹ μ(O) = 1`.
  calc ∫⁻ x in O, ‖w x - (volume O).toReal⁻¹ * ∫ y in O, w y‖ₑ
        ≤ ∫⁻ x in O, (volume O)⁻¹ * ∫⁻ y in O, ‖w x - w y‖ₑ := lintegral_mono mean
    _ = (volume O)⁻¹ * ∫⁻ x in O, ∫⁻ y in O, ‖w x - w y‖ₑ :=
        lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hm0)
    _ ≤ (volume O)⁻¹ * (ENNReal.ofReal D * (2 ^ n * (∫⁻ z, F z) * volume O)) := by gcongr
    _ = ((volume O)⁻¹ * volume O) * (2 ^ n * ENNReal.ofReal D * ∫⁻ z, F z) := by ring
    _ = ENNReal.ofReal (2 ^ n * D) * ∫⁻ x in O, ‖fderiv ℝ w x‖ₑ := by
        rw [ENNReal.inv_mul_cancel hm0 hmt, one_mul, hFint, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
/-- **Inner exhaustion of an open convex set** (Simon 2.7, "`W = {x ∈ U : dist(x, ∂U) > σ}`").
Every open convex `U ⊆ ℝⁿ` is the increasing union of open convex sets `O_j` with
`closedBall x σ_j ⊆ U` for `x ∈ O_j`, where `σ_j > 0` and `σ_j → 0`. Take `σ_j = 1/(j+1)`. If
`U = ℝⁿ`, let `O_j = ℝⁿ`. Otherwise `Uᶜ` is closed and nonempty; with `d = infDist(·, Uᶜ)` let
`O_j = {d > σ_j}`. A point `z` with `dist(x, z) < d(x)` lies in `U`; this gives the margins and
`O_j ⊆ U`, and `d > 0` on `U` gives `⋃_j O_j = U`. Convexity: if `‖v‖ < min(d(x), d(y))` then
`x + v, y + v ∈ U`, so `a(x + v) + b(y + v) = ax + by + v ∈ U`; hence `d(ax + by) ≥ min(d(x), d(y))`. -/
theorem Submission.convex_open_exists_inner_exhaustion : ∀ (n : ℕ) (U : Set (Rn n)), IsOpen U → Convex ℝ U → ∃ (O : ℕ → Set (Rn n)) (σ : ℕ → ℝ), Monotone O ∧ ⋃ j, O j = U ∧ Tendsto σ atTop (𝓝 0) ∧ ∀ j, IsOpen (O j) ∧ Convex ℝ (O j) ∧ 0 < σ j ∧ ∀ x ∈ O j, closedBall x (σ j) ⊆ U := by
  intro n U hU hconv
  -- Step 1: the radii `σ_j = 1/(j+1)` are positive and decreasing.
  have hσpos : ∀ j : ℕ, (0 : ℝ) < 1 / ((j : ℝ) + 1) := fun j ↦ by positivity
  have hσanti : ∀ i j : ℕ, i ≤ j → 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) := fun i j hij ↦
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
  by_cases hUniv : U = univ
  · -- Step 2: `U = ℝⁿ`; take `O_j = ℝⁿ`.
    subst hUniv
    exact ⟨fun _ ↦ univ, fun j ↦ 1 / ((j : ℝ) + 1), monotone_const, iUnion_const _,
      tendsto_one_div_add_atTop_nhds_zero_nat,
      fun j ↦ ⟨isOpen_univ, convex_univ, hσpos j, fun _ _ ↦ subset_univ _⟩⟩
  -- Step 3: `Uᶜ` is closed and nonempty; `O_j = {x | σ_j < infDist x Uᶜ}`.
  have hne : (Uᶜ).Nonempty := nonempty_compl.2 hUniv
  have hcl : IsClosed Uᶜ := hU.isClosed_compl
  -- (a) A point closer to `x` than `infDist x Uᶜ` lies in `U`.
  have key : ∀ x z : Rn n, dist x z < infDist x Uᶜ → z ∈ U := fun x z h ↦
    notMem_compl_iff.1 (notMem_of_dist_lt_infDist h)
  refine ⟨fun j ↦ {x | 1 / ((j : ℝ) + 1) < infDist x Uᶜ}, fun j ↦ 1 / ((j : ℝ) + 1), ?_, ?_,
    tendsto_one_div_add_atTop_nhds_zero_nat, fun j ↦ ⟨?_, ?_, hσpos j, ?_⟩⟩
  · -- (b) Monotone: `σ_j ≤ σ_i` for `i ≤ j`.
    intro i j hij x hx
    exact (hσanti i j hij).trans_lt hx
  · -- (e) Union: `x ∈ O_j` gives `x ∈ U` by (a); `x ∈ U` gives `0 < infDist x Uᶜ`.
    ext x
    simp only [mem_iUnion, mem_ofPred_eq]
    constructor
    · rintro ⟨j, hj⟩
      exact key x x (by rw [dist_self]; exact (hσpos j).trans hj)
    · intro hx
      exact exists_nat_one_div_lt ((hcl.notMem_iff_infDist_pos hne).1 (notMem_compl_iff.2 hx))
  · -- (c) Open: `infDist · Uᶜ` is continuous.
    exact isOpen_lt continuous_const (continuous_infDist_pt _)
  · -- (f) Convex: `min (infDist x Uᶜ) (infDist y Uᶜ) ≤ infDist (a • x + b • y) Uᶜ`.
    intro x hx y hy a b ha hb hab
    simp only [mem_ofPred_eq] at hx hy ⊢
    refine (lt_min hx hy).trans_le ((le_infDist hne).2 fun p hp ↦ not_lt.1 fun hlt ↦ hp ?_)
    -- `v = p - (a • x + b • y)` has `‖v‖ < min (infDist x Uᶜ) (infDist y Uᶜ)`, so `x + v`,
    -- `y + v ∈ U` by (a), and `a • (x + v) + b • (y + v) = p` lies in `U` by convexity.
    rw [dist_comm, dist_eq_norm] at hlt
    have hxv : x + (p - (a • x + b • y)) ∈ U := key x _ (by
      rw [dist_eq_norm, sub_add_cancel_left, norm_neg]
      exact hlt.trans_le (min_le_left _ _))
    have hyv : y + (p - (a • x + b • y)) ∈ U := key y _ (by
      rw [dist_eq_norm, sub_add_cancel_left, norm_neg]
      exact hlt.trans_le (min_le_right _ _))
    have hcomb : a • (x + (p - (a • x + b • y))) + b • (y + (p - (a • x + b • y))) = p := by
      rw [smul_add, smul_add, add_add_add_comm, ← add_smul, hab, one_smul, add_sub_cancel]
    exact hcomb ▸ hconv hxv hyv ha hb hab
  · -- (d) Margin: `dist x p ≤ σ_j < infDist x Uᶜ` for `p ∈ closedBall x σ_j`.
    intro x hx p hp
    rw [mem_closedBall, dist_comm] at hp
    exact key x p (hp.trans_lt hx)

/-- The frozen Chapter 2 contract: the conjunction of all headline results. -/
theorem main_theorem : LipschitzExtension ∧ Rademacher ∧ C1Approximation ∧ WhitneyExtension ∧ LipschitzImageHausdorff ∧ EilenbergInequality ∧ BVCompactness ∧ BVPoincare ∧ BVExtensionEstimate ∧ AreaFormula ∧ FirstVariation ∧ SecondVariation ∧ StationaryIffMeanCurvatureZero ∧ SecondVariationStationary ∧ CoareaFormula ∧ C1Sard := by sorry

end GMT.Ch02
