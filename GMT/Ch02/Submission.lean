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

/-- **Simon Ch. 2, Theorems 1.2 and 1.4.** McShane's optimal Lipschitz extension and
Rademacher's theorem. -/
theorem Submission.lipschitz_extension_and_rademacher : LipschitzExtension ∧ Rademacher := by
  refine ⟨?_, ?_⟩
  · intro X _ A f hA hf
    obtain ⟨F, hFLip, hEq, hconst⟩ :=
      Poincare.SimonGMT.Chapter02.lipschitz_extension_real_optimal hA f hf
    exact ⟨F, hFLip, hconst, hEq⟩
  · rintro n f ⟨K, hK⟩
    exact hK.ae_differentiableAt
/-- **Simon Ch. 2, toward Theorem 1.6 (pp. 42–43): a Whitney cover of `ℝⁿ ∖ A`.** Let `A ⊆ ℝⁿ` be
closed and nonempty, and put `r(x) = min{1, d(x, A)}/20`. Vitali's lemma (closed balls, `τ = 5`)
selects `J ⊆ ℝⁿ ∖ A` such that the balls `B̄(s, r(s))`, `s ∈ J`, are pairwise disjoint and every
`x ∉ A` lies within `5r(s)` of some `s ∈ J`. The sets `J(x) = {s ∈ J : |x - s| < 10r(s)}` have at
most `N` elements for one `N`, and the sets `J'(x) = {s ∈ J : B(s, 10r(s)) ∩ B(x, r(x)) ≠ ∅}` are
finite: rescaling by `r(x)` maps `J'(x) ⊇ J(x)` injectively onto a `1/2`-separated subset of
`B̄(0, 31)`. -/
theorem Submission.whitney_cover_finite_overlap : ∀ (n : ℕ) (A : Set (Rn n)), IsClosed A → A.Nonempty → ∃ (J : Set (Rn n)) (N : ℕ), J ⊆ Aᶜ ∧ (∀ x ∉ A, ∃ s ∈ J, ‖x - s‖ ≤ 5 * (min 1 (Metric.infDist s A) / 20)) ∧ (∀ x ∉ A, Set.Finite {s : Rn n | s ∈ J ∧ ‖x - s‖ < 10 * (min 1 (Metric.infDist s A) / 20)} ∧ Set.ncard {s : Rn n | s ∈ J ∧ ‖x - s‖ < 10 * (min 1 (Metric.infDist s A) / 20)} ≤ N) ∧ (∀ x ∉ A, Set.Finite {s : Rn n | s ∈ J ∧ ∃ z : Rn n, ‖z - s‖ < 10 * (min 1 (Metric.infDist s A) / 20) ∧ ‖z - x‖ < min 1 (Metric.infDist x A) / 20}) := by
  intro n A hA hne
  -- Step 1: the scale `r(x) = min{1, d(x)}/20` is in `[0, 1/20]`, positive off `A`, and
  -- `1/20`-Lipschitz.
  obtain ⟨r, hr⟩ : ∃ r : Rn n → ℝ, ∀ x, r x = min 1 (infDist x A) / 20 := ⟨_, fun _ ↦ rfl⟩
  simp only [← hr]
  have r_nonneg : ∀ x, 0 ≤ r x := fun x ↦ by
    have h : 0 ≤ min 1 (infDist x A) := le_min zero_le_one infDist_nonneg
    rw [hr]
    linarith
  have r_le : ∀ x, r x ≤ 1 / 20 := fun x ↦ by
    have h := min_le_left (1 : ℝ) (infDist x A)
    rw [hr]
    linarith
  have r_pos : ∀ x ∉ A, 0 < r x := fun x hx ↦ by
    have h : 0 < min 1 (infDist x A) := lt_min one_pos ((hA.notMem_iff_infDist_pos hne).mp hx)
    rw [hr]
    linarith
  have r_lip : ∀ x y, r x ≤ r y + ‖x - y‖ / 20 := fun x y ↦ by
    have h := ((lipschitz_infDist_pt A).const_min 1).dist_le_mul x y
    simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
    rw [dist_eq_norm] at h
    have h' := (abs_sub_le_iff.mp h).1
    rw [hr, hr]
    linarith
  -- Step 2 (F1): `|x - s| ≤ 10r(s)` gives `(2/3)r(x) ≤ r(s) ≤ 2r(x)`.
  have comp : ∀ x s, ‖x - s‖ ≤ 10 * r s → r s ≤ 2 * r x ∧ 2 * r x ≤ 3 * r s := fun x s h ↦ by
    have h₁ := r_lip x s
    have h₂ := r_lip s x
    rw [norm_sub_rev] at h₂
    constructor <;> linarith
  -- Step 3: Vitali selection on `ℝⁿ ∖ A` with radii `r ≤ 1/20` and `τ = 5`.
  obtain ⟨J, hJA, hJd, hJc⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall
    Aᶜ (fun x ↦ x) r (1 / 20) (fun x _ ↦ r_le x) 5 (by norm_num)
  -- Step 4: distinct `s, s' ∈ J` satisfy `|s - s'| > r(s)`.
  have sep : ∀ s ∈ J, ∀ s' ∈ J, s ≠ s' → r s < ‖s - s'‖ := fun s hs s' hs' hss' ↦ by
    refine not_le.mp fun h ↦ ?_
    have h₁ : s' ∈ closedBall s (r s) := by rwa [mem_closedBall, dist_eq_norm, norm_sub_rev]
    have h₂ : s' ∈ closedBall s' (r s') := mem_closedBall_self (r_nonneg s')
    exact Set.disjoint_left.mp (hJd hs hs' hss') h₁ h₂
  -- Step 5: a `δ`-separated subset of a totally bounded `K` injects into a finite `δ/2`-net of `K`.
  have packing : ∀ K : Set (Rn n), TotallyBounded K → ∀ δ : ℝ, 0 < δ → ∃ N : ℕ,
      ∀ S : Set (Rn n), S ⊆ K → S.Pairwise (fun y z ↦ δ ≤ dist y z) → S.Finite ∧ S.ncard ≤ N := by
    intro K hK δ hδ
    obtain ⟨T, hT, hKT⟩ := Metric.totallyBounded_iff.mp hK (δ / 2) (by positivity)
    refine ⟨T.ncard, fun S hSK hS ↦ ?_⟩
    have hq : ∀ y : S, ∃ q : T, dist (y : Rn n) q < δ / 2 := fun y ↦ by
      obtain ⟨q, hqT, hyq⟩ := mem_iUnion₂.mp (hKT (hSK y.2))
      exact ⟨⟨q, hqT⟩, hyq⟩
    choose q hq using hq
    have hinj : Function.Injective q := fun y y' hyy' ↦ by
      by_contra hne
      have h₁ := hS y.2 y'.2 (fun h ↦ hne (Subtype.ext h))
      have h₂ := dist_triangle (y : Rn n) (q y') y'
      have h₃ := hq y
      rw [hyy'] at h₃
      have h₄ := hq y'
      rw [dist_comm] at h₄
      linarith
    have : Finite T := hT.to_subtype
    have : Finite S := Finite.of_injective q hinj
    exact ⟨S.toFinite, Nat.card_le_card_of_injective q hinj⟩
  obtain ⟨N, hN⟩ := packing (closedBall 0 31) (isCompact_closedBall _ _).totallyBounded (1 / 2)
    (by norm_num)
  -- Steps 6–7 (F2, F3): for `x ∉ A`, `c ↦ (c - x)/r(x)` maps `J'(x)` injectively onto a
  -- `1/2`-separated subset of `B̄(0, 31)`, so `J'(x)` is finite with at most `N` elements.
  have key : ∀ x ∉ A, {s | s ∈ J ∧ ∃ z, ‖z - s‖ < 10 * r s ∧ ‖z - x‖ < r x}.Finite ∧
      {s | s ∈ J ∧ ∃ z, ‖z - s‖ < 10 * r s ∧ ‖z - x‖ < r x}.ncard ≤ N := by
    intro x hx
    have hρ := r_pos x hx
    obtain ⟨f, hf⟩ : ∃ f : Rn n → Rn n, ∀ c, f c = (r x)⁻¹ • (c - x) := ⟨_, fun _ ↦ rfl⟩
    have hfinj : Function.Injective f := fun c c' h ↦ by
      rw [hf, hf] at h
      exact sub_left_inj.mp (smul_right_injective (Rn n) (inv_ne_zero hρ.ne') h)
    have hfnorm : ∀ c, ‖f c‖ = (r x)⁻¹ * ‖c - x‖ := fun c ↦ by
      rw [hf, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hρ]
    have hfdist : ∀ c c', dist (f c) (f c') = (r x)⁻¹ * ‖c - c'‖ := fun c c' ↦ by
      rw [dist_eq_norm, hf, hf, ← smul_sub, sub_sub_sub_cancel_right, norm_smul, norm_inv,
        Real.norm_eq_abs, abs_of_pos hρ]
    -- For `s ∈ J'(x)` with witness `z`: `r(s) > r(x)/2` and `|s - x| < 31r(x)`.
    have hbd : ∀ s ∈ {s | s ∈ J ∧ ∃ z, ‖z - s‖ < 10 * r s ∧ ‖z - x‖ < r x},
        r x < 2 * r s ∧ ‖s - x‖ < 31 * r x := by
      rintro s ⟨-, z, hzs, hzx⟩
      obtain ⟨h₁, h₂⟩ := comp z s hzs.le
      have h₃ := r_lip z x
      have h₄ := r_lip x z
      rw [norm_sub_rev] at h₄
      have h₅ := norm_sub_le_norm_sub_add_norm_sub s z x
      rw [norm_sub_rev s z] at h₅
      have h₆ := r_nonneg s
      constructor <;> linarith
    have hsub : f '' {s | s ∈ J ∧ ∃ z, ‖z - s‖ < 10 * r s ∧ ‖z - x‖ < r x} ⊆ closedBall 0 31 := by
      rintro _ ⟨s, hs, rfl⟩
      rw [mem_closedBall, dist_zero_right, hfnorm, inv_mul_le_iff₀ hρ]
      linarith [(hbd s hs).2]
    have hsep : (f '' {s | s ∈ J ∧ ∃ z, ‖z - s‖ < 10 * r s ∧ ‖z - x‖ < r x}).Pairwise
        (fun y z ↦ 1 / 2 ≤ dist y z) := by
      rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩ hne
      have hss' : s ≠ s' := fun h ↦ hne (congrArg f h)
      rw [hfdist, le_inv_mul_iff₀ hρ]
      linarith [sep s hs.1 s' hs'.1 hss', (hbd s hs).1]
    obtain ⟨hfin, hcard⟩ := hN _ hsub hsep
    exact ⟨hfin.of_finite_image hfinj.injOn, Set.ncard_image_of_injective _ hfinj ▸ hcard⟩
  -- Step 8: (C1)–(C4); `J(x) ⊆ J'(x)` (take `z = x`), so (C3) follows from the bound on `J'(x)`.
  refine ⟨J, N, hJA, fun x hx ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ (key x hx).1⟩
  · obtain ⟨s, hs, hxs⟩ := hJc x hx
    exact ⟨s, hs, by simpa [dist_eq_norm] using hxs (mem_closedBall_self (r_nonneg x))⟩
  · have hJJ' : {s | s ∈ J ∧ ‖x - s‖ < 10 * r s} ⊆
        {s | s ∈ J ∧ ∃ z, ‖z - s‖ < 10 * r s ∧ ‖z - x‖ < r x} := fun s hs ↦
      ⟨hs.1, x, hs.2, by rw [sub_self, norm_zero]; exact r_pos x hx⟩
    obtain ⟨hfin, hcard⟩ := key x hx
    exact ⟨hfin.subset hJJ', (Set.ncard_le_ncard hJJ' hfin).trans hcard⟩
/-- **Simon Ch. 2, Theorem 1.6 (proof after [EG92]), Whitney partition of unity from a ball
cover.** Let `A ⊆ ℝⁿ` be closed and nonempty, `d(x) = dist(x, A)` and `r(x) = min{1, d(x)}/20`.
Let `J ⊆ ℝⁿ ∖ A` be such that the balls `B̄(s, 5r(s))`, `s ∈ J`, cover `ℝⁿ ∖ A`, each `x ∉ A`
lies in at most `N` of the balls `B(s, 10r(s))`, and only finitely many of these meet
`B(x, r(x))`. Then the normalised bumps `φ_s = θ_s / Σ_t θ_t`, with `θ_s = 1` on `B̄(s, 5r(s))`
and `θ_s = 0` off `B(s, 9r(s))`, form a locally finite `C¹` partition of unity on `ℝⁿ ∖ A`. If
`φ_s(x) ≠ 0` then `|x - p_s| ≤ 3d(x)` for a nearest point `p_s ∈ A` to `s`, and
`Σ_s ‖Dφ_s(x)‖ ≤ M/d(x)` when `d(x) ≤ 1`, with `M = 30ΛN(N + 1)` for a Lipschitz constant `Λ`
of `θ`. -/
theorem Submission.whitney_partition_of_finite_overlap_cover : ∀ (n : ℕ) (A J : Set (Rn n)) (N : ℕ), IsClosed A → A.Nonempty → J ⊆ Aᶜ → (∀ x ∉ A, ∃ s ∈ J, ‖x - s‖ ≤ 5 * (min 1 (Metric.infDist s A) / 20)) → (∀ x ∉ A, Set.Finite {s : Rn n | s ∈ J ∧ ‖x - s‖ < 10 * (min 1 (Metric.infDist s A) / 20)} ∧ Set.ncard {s : Rn n | s ∈ J ∧ ‖x - s‖ < 10 * (min 1 (Metric.infDist s A) / 20)} ≤ N) → (∀ x ∉ A, Set.Finite {s : Rn n | s ∈ J ∧ ∃ z : Rn n, ‖z - s‖ < 10 * (min 1 (Metric.infDist s A) / 20) ∧ ‖z - x‖ < min 1 (Metric.infDist x A) / 20}) → ∃ (ι : Type) (φ : ι → Rn n → ℝ) (p : ι → Rn n) (C M : ℝ), 0 ≤ C ∧ 0 ≤ M ∧ (∀ i, p i ∈ A) ∧ (∀ i, ∀ x ∉ A, ContDiffAt ℝ 1 (φ i) x) ∧ (∀ i, ∀ x ∉ A, 0 ≤ φ i x) ∧ (∀ x ∉ A, ∃ s : Finset ι, ∃ V ∈ 𝓝 x, ∀ i ∉ s, ∀ y ∈ V, φ i y = 0) ∧ (∀ x ∉ A, ∑ᶠ i, φ i x = 1) ∧ (∀ i, ∀ x ∉ A, φ i x ≠ 0 → ‖x - p i‖ ≤ C * Metric.infDist x A) ∧ (∀ x ∉ A, Metric.infDist x A ≤ 1 → ∑ᶠ i, ‖fderiv ℝ (φ i) x‖ ≤ M / Metric.infDist x A) := by
  intro n A J N hA hne hJ hcov hnear hwide
  classical
  -- The scale `r(x) = min{1, d(x)}/20`, kept opaque through its defining equation.
  obtain ⟨r, hr⟩ : ∃ r : Rn n → ℝ, ∀ x, r x = min 1 (infDist x A) / 20 := ⟨_, fun _ => rfl⟩
  simp only [← hr] at hcov hnear hwide
  have hr0 : ∀ x, 0 ≤ r x := fun x => by
    rw [hr]; exact div_nonneg (le_min zero_le_one infDist_nonneg) (by norm_num)
  have hr20 : ∀ x, 20 * r x ≤ infDist x A := fun x => by
    rw [hr]; linarith [min_le_right (1 : ℝ) (infDist x A)]
  have hrpos : ∀ x, x ∉ A → 0 < r x := fun x hx => by
    rw [hr]; exact div_pos (lt_min one_pos ((hA.notMem_iff_infDist_pos hne).mp hx)) (by norm_num)
  have hreq : ∀ x, infDist x A ≤ 1 → r x = infDist x A / 20 := fun x h => by
    rw [hr, min_eq_right h]
  -- `r` is `1/20`-Lipschitz, so the radii of nearby balls are comparable.
  have hrlip : ∀ x y, r x ≤ r y + ‖x - y‖ / 20 := fun x y => by
    have h := ((lipschitz_infDist_pt A).const_min 1).dist_le_mul x y
    simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
    have h' := (abs_sub_le_iff.mp h).1
    rw [dist_eq_norm] at h'
    rw [hr, hr]; linarith
  have hcomp : ∀ x s, ‖x - s‖ ≤ 10 * r s → r s ≤ 2 * r x ∧ 2 / 3 * r x ≤ r s := fun x s h => by
    have h₁ := hrlip x s
    have h₂ := hrlip s x
    rw [norm_sub_rev] at h₂
    have hs := hr0 s
    constructor <;> linarith
  have hJpos : ∀ s : J, 0 < r s := fun s => hrpos s (hJ s.2)
  -- The base bump `θ`: `1` on `B̄(0, 5)`, support `B(0, 9)`, `Λ`-Lipschitz.
  obtain ⟨θ, hθin, hθout⟩ : ∃ θ : ContDiffBump (0 : Rn n), θ.rIn = 5 ∧ θ.rOut = 9 :=
    ⟨⟨5, 9, by norm_num, by norm_num⟩, rfl, rfl⟩
  have hθC : ContDiff ℝ 1 θ := θ.contDiff (n := 1)
  obtain ⟨Λ, hΛ⟩ := hθC.lipschitzWith_of_hasCompactSupport θ.hasCompactSupport one_ne_zero
  -- The rescaled bumps `θ_s(x) = θ((x - s)/r_s)`.
  obtain ⟨b, hb⟩ : ∃ b : Rn n → Rn n → ℝ, ∀ s x, b s x = θ ((r s)⁻¹ • (x - s)) :=
    ⟨_, fun _ _ => rfl⟩
  have hbC : ∀ s, ContDiff ℝ 1 (b s) := fun s => by
    rw [show b s = fun x => θ ((r s)⁻¹ • (x - s)) from funext (hb s)]
    exact hθC.comp ((contDiff_id.sub contDiff_const).const_smul _)
  have hb0 : ∀ s x, 0 ≤ b s x := fun s x => by rw [hb]; exact θ.nonneg
  have hb1 : ∀ s x, b s x ≤ 1 := fun s x => by rw [hb]; exact θ.le_one
  have hbone : ∀ s x, 0 < r s → ‖x - s‖ ≤ 5 * r s → b s x = 1 := fun s x hs hx => by
    rw [hb]
    apply θ.one_of_mem_closedBall
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hs.le),
      hθin, inv_mul_le_iff₀ hs]
    linarith
  have hbzero : ∀ s x, 0 < r s → 9 * r s ≤ ‖x - s‖ → b s x = 0 := fun s x hs hx => by
    rw [hb]
    apply Function.notMem_support.mp
    rw [θ.support_eq, mem_ball, dist_zero_right, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hs.le), hθout, not_lt, le_inv_mul_iff₀ hs]
    linarith
  have hbne : ∀ s x, 0 < r s → b s x ≠ 0 → ‖x - s‖ < 9 * r s := fun s x hs hx =>
    lt_of_not_ge fun h => hx (hbzero s x hs h)
  -- If `|x - s| ≥ 10r_s`, then `θ_s` vanishes on `B(x, r_s)`.
  have hbev : ∀ s x, 0 < r s → 10 * r s ≤ ‖x - s‖ → b s =ᶠ[𝓝 x] fun _ => 0 := fun s x hs hx => by
    filter_upwards [ball_mem_nhds x hs] with y hy
    apply hbzero s y hs
    rw [mem_ball, dist_eq_norm] at hy
    have := norm_sub_le_norm_sub_add_norm_sub x y s
    rw [norm_sub_rev x y] at this
    linarith
  -- `‖Dθ_s‖ ≤ Λ/r_s`: `θ_s` is `θ` composed with a `(1/r_s)`-Lipschitz affine map.
  have hbder : ∀ s, 0 < r s → ∀ x, ‖fderiv ℝ (b s) x‖ ≤ Λ / r s := fun s hs x => by
    have hf : LipschitzWith (Real.toNNReal (r s)⁻¹) (fun y : Rn n => (r s)⁻¹ • (y - s)) := by
      apply LipschitzWith.of_dist_le_mul
      intro y z
      rw [Real.coe_toNNReal _ (inv_nonneg.mpr hs.le), dist_eq_norm, dist_eq_norm, ← smul_sub,
        sub_sub_sub_cancel_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hs.le)]
    rw [show b s = θ ∘ fun y : Rn n => (r s)⁻¹ • (y - s) from funext (hb s)]
    refine (norm_fderiv_le_of_lipschitz ℝ (hΛ.comp hf)).trans_eq ?_
    rw [NNReal.coe_mul, Real.coe_toNNReal _ (inv_nonneg.mpr hs.le), div_eq_mul_inv]
  -- The finite sets `J'(x) ⊇ J(x)` of the hypotheses, as finsets of the index type `J`.
  have hF : ∀ x, x ∉ A → ∃ F : Finset J,
      ∀ s : J, s ∈ F ↔ ∃ z : Rn n, ‖z - s‖ < 10 * r s ∧ ‖z - x‖ < r x := fun x hx => by
    refine ⟨((hwide x hx).preimage Subtype.val_injective.injOn).toFinset, fun s => ?_⟩
    rw [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_ofPred_eq]
    exact ⟨fun h => h.2, fun h => ⟨s.2, h⟩⟩
  choose F hFmem using hF
  have hG : ∀ x, x ∉ A → ∃ G : Finset J,
      (∀ s : J, s ∈ G ↔ ‖x - s‖ < 10 * r s) ∧ G.card ≤ N := fun x hx => by
    have hfin : ((↑) ⁻¹' {s : Rn n | s ∈ J ∧ ‖x - s‖ < 10 * r s} : Set J).Finite :=
      (hnear x hx).1.preimage Subtype.val_injective.injOn
    refine ⟨hfin.toFinset, fun s => ?_, ?_⟩
    · rw [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_ofPred_eq]
      exact ⟨fun h => h.2, fun h => ⟨s.2, h⟩⟩
    · rw [← Set.ncard_eq_toFinset_card _ hfin,
        Set.ncard_preimage_of_injective_subset_range Subtype.val_injective]
      · exact (hnear x hx).2
      · intro s hs
        exact ⟨⟨s, hs.1⟩, rfl⟩
  choose G hGmem hGcard using hG
  -- For `s ∉ J'(x)`, `θ_s` vanishes on `B(x, r(x))`.
  have hbF : ∀ x (hx : x ∉ A) y, ‖y - x‖ < r x → ∀ s : J, s ∉ F x hx → b s y = 0 :=
    fun x hx y hy s hs => by
      by_contra hne'
      apply hs
      rw [hFmem]
      have := hbne s y (hJpos s) hne'
      exact ⟨y, by linarith [hJpos s], hy⟩
  -- The normalising sum `Σ = Σᶠ_s θ_s` is the finite sum over `J'(x)` on `B(x, r(x))`, so it is
  -- `C¹` there. The cover gives `Σ ≥ 1`, and only `s ∈ J(x)` contribute to `DΣ(x)`.
  obtain ⟨S, hS⟩ : ∃ S : Rn n → ℝ, ∀ x, S x = ∑ᶠ s : J, b s x := ⟨_, fun _ => rfl⟩
  have hSloc : ∀ x (hx : x ∉ A) y, ‖y - x‖ < r x → S y = ∑ s ∈ F x hx, b s y :=
    fun x hx y hy => by
      rw [hS]
      apply finsum_eq_sum_of_support_subset
      intro s hs
      by_contra h'
      exact hs (hbF x hx y hy s h')
  have hSev : ∀ x (hx : x ∉ A), S =ᶠ[𝓝 x] fun y => ∑ s ∈ F x hx, b s y := fun x hx => by
    filter_upwards [ball_mem_nhds x (hrpos x hx)] with y hy
    rw [mem_ball, dist_eq_norm] at hy
    exact hSloc x hx y hy
  have hSC : ∀ x, x ∉ A → ContDiffAt ℝ 1 S x := fun x hx =>
    (ContDiff.sum (f := fun (s : J) => b s) fun s _ => hbC s).contDiffAt.congr_of_eventuallyEq
      (hSev x hx)
  have hS1 : ∀ x, x ∉ A → 1 ≤ S x := fun x hx => by
    have hx0 : ‖x - x‖ < r x := by rw [sub_self, norm_zero]; exact hrpos x hx
    rw [hSloc x hx x hx0]
    obtain ⟨s, hs, hxs⟩ := hcov x hx
    have hspos : 0 < r s := hrpos s (hJ hs)
    have hi : (⟨s, hs⟩ : J) ∈ F x hx := (hFmem x hx _).2 ⟨x, by linarith, hx0⟩
    calc (1 : ℝ) = b s x := (hbone s x hspos hxs).symm
      _ ≤ ∑ t ∈ F x hx, b t x :=
        Finset.single_le_sum (f := fun t : J => b t x) (fun t _ => hb0 t x) hi
  have hSpos : ∀ x, x ∉ A → 0 < S x := fun x hx => lt_of_lt_of_le one_pos (hS1 x hx)
  have hSder : ∀ x (hx : x ∉ A), fderiv ℝ S x = ∑ s ∈ G x hx, fderiv ℝ (b s) x := fun x hx => by
    rw [(hSev x hx).fderiv_eq,
      fderiv_fun_sum (A := fun (s : J) => b s) fun s _ => (hbC s).differentiable one_ne_zero x]
    symm
    apply Finset.sum_subset
    · intro s hs
      rw [hGmem] at hs
      exact (hFmem x hx s).2 ⟨x, hs, by rw [sub_self, norm_zero]; exact hrpos x hx⟩
    · intro s _ hs
      rw [hGmem, not_lt] at hs
      rw [(hbev s x (hJpos s) hs).fderiv_eq]
      exact fderiv_const_apply 0
  -- The partition `φ_s = θ_s/Σ` with anchors `p_s ∈ A` nearest to `s`, `C = 3`, `M = 30ΛN(N + 1)`.
  obtain ⟨φ, hφ⟩ : ∃ φ : J → Rn n → ℝ, ∀ s x, φ s x = b s x / S x := ⟨_, fun _ _ => rfl⟩
  choose a ha hda using fun s : J => hA.exists_infDist_eq_dist hne (s : Rn n)
  refine ⟨J, φ, a, 3, 30 * Λ * N * (N + 1), by norm_num, by positivity, ha, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `φ_s` is `C¹` off `A`.
    intro s x hx
    rw [show φ s = fun y => b s y / S y from funext (hφ s)]
    exact (hbC s).contDiffAt.div (hSC x hx) (hSpos x hx).ne'
  · -- `φ_s ≥ 0` off `A`.
    intro s x hx
    rw [hφ]
    exact div_nonneg (hb0 s x) (hSpos x hx).le
  · -- Near `x ∉ A`, only the `φ_s` with `s ∈ J'(x)` are nonzero.
    intro x hx
    refine ⟨F x hx, ball x (r x), ball_mem_nhds x (hrpos x hx), fun s hs y hy => ?_⟩
    rw [mem_ball, dist_eq_norm] at hy
    rw [hφ, hbF x hx y hy s hs, zero_div]
  · -- `Σᶠ_s φ_s(x) = (Σ_{s ∈ J'(x)} θ_s(x))/Σ(x) = 1`.
    intro x hx
    have hx0 : ‖x - x‖ < r x := by rw [sub_self, norm_zero]; exact hrpos x hx
    have hsupp : Function.support (fun s : J => φ s x) ⊆ ↑(F x hx) := by
      intro s hs
      by_contra h'
      exact hs (by show φ s x = 0; rw [hφ, hbF x hx x hx0 s h', zero_div])
    rw [finsum_eq_sum_of_support_subset _ hsupp]
    simp only [hφ]
    rw [← Finset.sum_div, ← hSloc x hx x hx0]
    exact div_self (hSpos x hx).ne'
  · -- `φ_s(x) ≠ 0` gives `|x - s| < 9r_s`, so `|x - p_s| ≤ |x - s| + d(s) ≤ d(x) + 2|x - s|`, and
    -- `r_s ≤ 2r(x) ≤ d(x)/10` bounds this by `3d(x)`.
    intro s x hx hφ0
    have hθ : b s x ≠ 0 := fun h0 => hφ0 (by rw [hφ, h0, zero_div])
    have hlt := hbne s x (hJpos s) hθ
    have h1 : infDist (s : Rn n) A ≤ infDist x A + dist (s : Rn n) x :=
      infDist_le_infDist_add_dist
    rw [dist_eq_norm, norm_sub_rev] at h1
    have h2 := hda s
    rw [dist_eq_norm] at h2
    have h3 := norm_sub_le_norm_sub_add_norm_sub x (s : Rn n) (a s)
    have h4 := (hcomp x s (by linarith [hJpos s])).1
    have h5 := hr20 x
    have h6 := hr0 x
    linarith
  · -- For `s ∈ J(x)`, `r_s ≥ 2r(x)/3`, so `‖Dθ_s(x)‖ ≤ T = 3Λ/(2r(x))` and `‖DΣ(x)‖ ≤ NT`.
    intro x hx hd1
    have hrx := hrpos x hx
    have hreqx := hreq x hd1
    obtain ⟨T, hT⟩ : ∃ T : ℝ, T = 3 / 2 * Λ / r x := ⟨_, rfl⟩
    have hT0 : 0 ≤ T := by rw [hT]; positivity
    have hbump : ∀ s ∈ G x hx, ‖fderiv ℝ (b s) x‖ ≤ T := by
      intro s hs
      rw [hGmem] at hs
      have hsr := hJpos s
      have hlow := (hcomp x s hs.le).2
      refine (hbder s hsr x).trans ?_
      rw [hT, div_le_div_iff₀ hsr hrx]
      have := mul_le_mul_of_nonneg_left hlow Λ.coe_nonneg
      linarith
    have hcard : ((G x hx).card : ℝ) ≤ N := by exact_mod_cast hGcard x hx
    have hsum : ‖fderiv ℝ S x‖ ≤ (N : ℝ) * T := by
      rw [hSder x hx]
      calc ‖∑ s ∈ G x hx, fderiv ℝ (b s) x‖
          ≤ ∑ s ∈ G x hx, ‖fderiv ℝ (b s) x‖ := norm_sum_le _ _
        _ ≤ ∑ _s ∈ G x hx, T := Finset.sum_le_sum hbump
        _ = ((G x hx).card : ℝ) * T := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (N : ℝ) * T := mul_le_mul_of_nonneg_right hcard hT0
    -- Off `J(x)`, `φ_s` vanishes near `x`, so `Dφ_s(x) = 0`.
    have hφev : ∀ s : J, s ∉ G x hx → fderiv ℝ (φ s) x = 0 := by
      intro s hs
      rw [hGmem, not_lt] at hs
      have hev : φ s =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [hbev s x (hJpos s) hs] with y hy
        rw [hφ, hy, zero_div]
      rw [hev.fderiv_eq]
      exact fderiv_const_apply 0
    -- Quotient rule: `‖Dφ_s(x)‖ ≤ ‖Dθ_s(x)‖ + ‖DΣ(x)‖` since `Σ(x) ≥ 1` and `0 ≤ θ_s ≤ 1`.
    have hφder : ∀ s : J, ‖fderiv ℝ (φ s) x‖ ≤ ‖fderiv ℝ (b s) x‖ + ‖fderiv ℝ S x‖ := by
      intro s
      have hS1x := hS1 x hx
      have hSx := hSpos x hx
      have hSi : (S x)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hS1x
      have hSi2 : (S x ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hS1x)
      have hbd := ((hbC s).differentiable one_ne_zero x).hasFDerivAt
      have hSd := ((hSC x hx).differentiableAt one_ne_zero).hasFDerivAt
      have hi := (hasDerivAt_inv hSx.ne').comp_hasFDerivAt x hSd
      have hprod := hbd.fun_mul hi
      have hder : fderiv ℝ (φ s) x =
          b s x • (-(S x ^ 2)⁻¹ • fderiv ℝ S x) + (S x)⁻¹ • fderiv ℝ (b s) x := by
        rw [show φ s = fun y => b s y * ((fun t : ℝ => t⁻¹) ∘ S) y from
          funext fun y => by rw [hφ, div_eq_mul_inv, Function.comp_apply]]
        exact hprod.fderiv
      rw [hder]
      have hb0x := hb0 s x
      have hb1x := hb1 s x
      calc ‖b s x • (-(S x ^ 2)⁻¹ • fderiv ℝ S x) + (S x)⁻¹ • fderiv ℝ (b s) x‖
          ≤ ‖b s x • (-(S x ^ 2)⁻¹ • fderiv ℝ S x)‖ + ‖(S x)⁻¹ • fderiv ℝ (b s) x‖ :=
            norm_add_le _ _
        _ = b s x * ((S x ^ 2)⁻¹ * ‖fderiv ℝ S x‖) + (S x)⁻¹ * ‖fderiv ℝ (b s) x‖ := by
          rw [norm_smul, norm_smul, norm_smul, Real.norm_of_nonneg hb0x, norm_neg,
            Real.norm_of_nonneg (inv_nonneg.mpr (sq_nonneg (S x))),
            Real.norm_of_nonneg (inv_nonneg.mpr hSx.le)]
        _ ≤ ‖fderiv ℝ (b s) x‖ + ‖fderiv ℝ S x‖ := by
          have h₁ := mul_le_mul_of_nonneg_right hSi (norm_nonneg (fderiv ℝ (b s) x))
          have h₂ := mul_le_mul_of_nonneg_right hSi2 (norm_nonneg (fderiv ℝ S x))
          have h₃ := mul_le_mul_of_nonneg_right hb1x
            (mul_nonneg (inv_nonneg.mpr (sq_nonneg (S x))) (norm_nonneg (fderiv ℝ S x)))
          linarith
    have hsupp : Function.support (fun s : J => ‖fderiv ℝ (φ s) x‖) ⊆ ↑(G x hx) := by
      intro s hs
      by_contra h'
      exact hs (by show ‖fderiv ℝ (φ s) x‖ = 0; rw [hφev s h', norm_zero])
    rw [finsum_eq_sum_of_support_subset _ hsupp]
    have hw : ∀ s ∈ G x hx, ‖fderiv ℝ (φ s) x‖ ≤ T + (N : ℝ) * T := fun s hs =>
      (hφder s).trans (add_le_add (hbump s hs) hsum)
    calc ∑ s ∈ G x hx, ‖fderiv ℝ (φ s) x‖
        ≤ ∑ _s ∈ G x hx, (T + (N : ℝ) * T) := Finset.sum_le_sum hw
      _ = ((G x hx).card : ℝ) * (T + (N : ℝ) * T) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) * (T + (N : ℝ) * T) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 30 * Λ * N * (N + 1) / infDist x A := by
        rw [hT, hreqx]
        field_simp
        ring
/-- **Simon Ch. 2, proof of Theorem 1.6 (pp. 42–43), Whitney gluing off `A`: local structure.**
Let `A ⊆ ℝⁿ` be closed, let the weights `φ i` (`i : ι`) be nonnegative and `C¹` off `A`, locally
finitely supported off `A`, with `∑ᶠ i, φ i = 1` off `A`, and let `g = ∑ᶠ i, φ i * P i` off `A`,
where `P i y = h (p i) + ⟪ν (p i), y - p i⟫` is affine. Then at each `x ∉ A`, `g` is `C¹` at `x`
and a finite `S` with `φ i x > 0` on `S` carries every sum: `∑_{i∈S} φ i x = 1`,
`g x = ∑_{i∈S} φ i x * P i x`, `Dg(x) = ∑_{i∈S} (φ i x • ⟪ν (p i), ·⟫ + P i x • Dφ i (x))`,
`∑_{i∈S} Dφ i (x) = 0` and `∑ᶠ i, ‖Dφ i (x)‖ = ∑_{i∈S} ‖Dφ i (x)‖`. Near `x` both finsums are
sums over the finite `s` given by local finiteness, so the product, sum and constant rules apply;
`S = {i ∈ s | φ i x ≠ 0}`, and an index with `φ i x = 0` has `Dφ i (x) = 0` because `x` is then a
local minimum of `φ i ≥ 0` on the open set `ℝⁿ \ A`. -/
theorem Submission.whitney_gluing_local_structure : ∀ (n : ℕ) (A : Set (Rn n)) (h : Rn n → ℝ) (ν : Rn n → Rn n) (ι : Type) (φ : ι → Rn n → ℝ) (p : ι → Rn n) (g : Rn n → ℝ), IsClosed A → (∀ i, ∀ x ∉ A, ContDiffAt ℝ 1 (φ i) x) → (∀ i, ∀ x ∉ A, 0 ≤ φ i x) → (∀ x ∉ A, ∃ s : Finset ι, ∃ V ∈ 𝓝 x, ∀ i ∉ s, ∀ y ∈ V, φ i y = 0) → (∀ x ∉ A, ∑ᶠ i, φ i x = 1) → (∀ x ∉ A, g x = ∑ᶠ i, φ i x * (h (p i) + inner ℝ (ν (p i)) (x - p i))) → ∀ x ∉ A, ContDiffAt ℝ 1 g x ∧ ∃ S : Finset ι, (∀ i ∈ S, 0 < φ i x) ∧ ∑ i ∈ S, φ i x = 1 ∧ g x = ∑ i ∈ S, φ i x * (h (p i) + inner ℝ (ν (p i)) (x - p i)) ∧ fderiv ℝ g x = ∑ i ∈ S, (φ i x • innerSL ℝ (ν (p i)) + (h (p i) + inner ℝ (ν (p i)) (x - p i)) • fderiv ℝ (φ i) x) ∧ ∑ i ∈ S, fderiv ℝ (φ i) x = 0 ∧ ∑ᶠ i, ‖fderiv ℝ (φ i) x‖ = ∑ i ∈ S, ‖fderiv ℝ (φ i) x‖ := by
  intro n A h ν ι φ p g hA hφC1 hφnn hlf hsum hgU x hx
  classical
  obtain ⟨s, V, hV, hVzero⟩ := hlf x hx
  -- The affine pieces `P i`: derivative `⟪ν (p i), ·⟫` everywhere, and `C¹`.
  set P : ι → Rn n → ℝ := fun i y => h (p i) + inner ℝ (ν (p i)) (y - p i)
  have hPderiv : ∀ i y, HasFDerivAt (P i) (innerSL ℝ (ν (p i))) y := by
    intro i y
    have h1 := (((innerSL ℝ (ν (p i))).hasFDerivAt (x := y - p i)).comp y
      ((hasFDerivAt_id y).sub_const (p i))).const_add (h (p i))
    simpa [P, Function.comp_def, innerSL_apply_apply] using h1
  have hPcd : ∀ i, ContDiff ℝ 1 (P i) := by
    intro i
    exact contDiff_const.add ((innerSL ℝ (ν (p i))).contDiff.comp (contDiff_id.sub contDiff_const))
  -- On `W = V ∩ Aᶜ ∈ 𝓝 x` both finsums are finite sums over `s`.
  have hU : (Aᶜ : Set (Rn n)) ∈ 𝓝 x := hA.isOpen_compl.mem_nhds hx
  have hW : V ∩ Aᶜ ∈ 𝓝 x := inter_mem hV hU
  have hrep : ∀ y ∈ V ∩ Aᶜ, g y = ∑ i ∈ s, φ i y * P i y ∧ ∑ i ∈ s, φ i y = 1 := by
    intro y hy
    have hsupp1 : Function.support (fun i => φ i y) ⊆ ↑s := by
      intro i hi
      by_contra his
      exact hi (hVzero i his y hy.1)
    have hsupp2 : Function.support (fun i => φ i y * P i y) ⊆ ↑s := by
      intro i hi
      by_contra his
      apply hi
      simp [hVzero i his y hy.1]
    constructor
    · rw [hgU y hy.2, finsum_eq_sum_of_support_subset _ hsupp2]
    · rw [← finsum_eq_sum_of_support_subset _ hsupp1]
      exact hsum y hy.2
  have hg_ev : g =ᶠ[𝓝 x] fun y => ∑ i ∈ s, φ i y * P i y := by
    filter_upwards [hW] with y hy using (hrep y hy).1
  have hsum_ev : (fun y => ∑ i ∈ s, φ i y) =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
    filter_upwards [hW] with y hy using (hrep y hy).2
  -- `g` is `C¹` at `x`; its derivative, and that of `∑ i ∈ s, φ i = 1`, as sums over `s`.
  have hGcd : ContDiffAt ℝ 1 (fun y => ∑ i ∈ s, φ i y * P i y) x :=
    ContDiffAt.sum fun i _ => (hφC1 i x hx).mul (hPcd i).contDiffAt
  have hgcd : ContDiffAt ℝ 1 g x := hGcd.congr_of_eventuallyEq hg_ev
  have hφdiff : ∀ i, DifferentiableAt ℝ (φ i) x := fun i =>
    (hφC1 i x hx).differentiableAt (by norm_num)
  have hGderiv : HasFDerivAt (fun y => ∑ i ∈ s, φ i y * P i y)
      (∑ i ∈ s, (φ i x • innerSL ℝ (ν (p i)) + P i x • fderiv ℝ (φ i) x)) x := by
    apply HasFDerivAt.fun_sum
    intro i _
    exact (hφdiff i).hasFDerivAt.mul (hPderiv i x)
  have hfd_s : fderiv ℝ g x = ∑ i ∈ s, (φ i x • innerSL ℝ (ν (p i)) + P i x • fderiv ℝ (φ i) x) := by
    rw [hg_ev.fderiv_eq, hGderiv.fderiv]
  have hD0_s : ∑ i ∈ s, fderiv ℝ (φ i) x = 0 := by
    have h1 : HasFDerivAt (fun y => ∑ i ∈ s, φ i y) (∑ i ∈ s, fderiv ℝ (φ i) x) x :=
      HasFDerivAt.fun_sum fun i _ => (hφdiff i).hasFDerivAt
    have h2 : HasFDerivAt (fun y => ∑ i ∈ s, φ i y) (0 : Rn n →L[ℝ] ℝ) x :=
      (hasFDerivAt_const (1 : ℝ) x).congr_of_eventuallyEq hsum_ev
    exact h1.unique h2
  -- Indices with zero weight at `x` have zero derivative there (local minimum of `φ i ≥ 0`).
  have hzero : ∀ i, φ i x = 0 → fderiv ℝ (φ i) x = 0 := by
    intro i hi
    apply IsLocalMin.fderiv_eq_zero
    filter_upwards [hU] with y hy
    rw [hi]
    exact hφnn i y hy
  have hxV : x ∈ V := mem_of_mem_nhds hV
  have hout : ∀ i, i ∉ s → φ i x = 0 := fun i hi => hVzero i hi x hxV
  -- `S = {i ∈ s | φ i x ≠ 0}`: dropping the other indices of `s` changes no sum.
  let S : Finset ι := s.filter (fun i => φ i x ≠ 0)
  have hSpos : ∀ i ∈ S, 0 < φ i x := by
    intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    exact lt_of_le_of_ne (hφnn i x hx) (Ne.symm hi')
  have hS1 : ∑ i ∈ S, φ i x = 1 := by
    have := (hrep x ⟨hxV, hx⟩).2
    rw [← this]
    exact Finset.sum_filter_ne_zero s
  refine ⟨hgcd, S, hSpos, hS1, ?_, ?_, ?_, ?_⟩
  · rw [(hrep x ⟨hxV, hx⟩).1]
    symm
    apply Finset.sum_filter_of_ne
    intro i _ hne h0
    exact hne (by rw [h0, zero_mul])
  · rw [hfd_s]
    symm
    apply Finset.sum_filter_of_ne
    intro i _ hne h0
    exact hne (by rw [h0, hzero i h0, zero_smul, smul_zero, add_zero])
  · rw [← hD0_s]
    apply Finset.sum_filter_of_ne
    intro i _ hne h0
    exact hne (hzero i h0)
  · apply finsum_eq_sum_of_support_subset
    intro i hi
    have hne : fderiv ℝ (φ i) x ≠ 0 := by
      intro h0
      exact hi (by simp [h0])
    have hφne : φ i x ≠ 0 := fun h0 => hne (hzero i h0)
    have his : i ∈ s := by
      by_contra his
      exact hφne (hout i his)
    exact Finset.mem_filter.mpr ⟨his, hφne⟩

/-- Whitney gluing on `A` (the step `∇g = ν` on `A` in the proof of Simon Ch. 2, Theorem 1.6).
Let `A` be closed, `ν` continuous on `A`, and `h`, `ν` satisfy 1.6 (∗) uniformly on compact
subsets of `A`. If `g = h` on `A` and, at each `x ∉ A`, `g(x)` is a convex combination
`∑ᵢ φᵢ(x) (h(pᵢ) + ν(pᵢ)·(x - pᵢ))` over finitely many anchors `pᵢ ∈ A` with
`|x - pᵢ| ≤ C dist(x, A)`, then `g` is differentiable at every `a ∈ A` with `Dg(a) = ν(a)·`. -/
theorem Submission.whitney_gluing_hasFDerivAt : (∀ (n : ℕ) (A : Set (Rn n)) (h : Rn n → ℝ) (ν : Rn n → Rn n) (ι : Type) (φ : ι → Rn n → ℝ) (p : ι → Rn n) (C : ℝ) (g : Rn n → ℝ), IsClosed A → ContinuousOn ν A → (∀ K ⊆ A, IsCompact K → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ y ∈ A, 0 < ‖y - x‖ → ‖y - x‖ < δ → |h y - h x - inner ℝ (ν x) (y - x)| ≤ ε * ‖y - x‖) → 0 ≤ C → (∀ i, p i ∈ A) → (∀ x ∈ A, g x = h x) → (∀ x ∉ A, ∃ S : Finset ι, (∀ i ∈ S, 0 ≤ φ i x ∧ ‖x - p i‖ ≤ C * Metric.infDist x A) ∧ ∑ i ∈ S, φ i x = 1 ∧ g x = ∑ i ∈ S, φ i x * (h (p i) + inner ℝ (ν (p i)) (x - p i))) → ∀ a ∈ A, HasFDerivAt g (innerSL ℝ (ν a)) a) := by
  intro n A h ν ι φ p C g hA hν hW hC hp hgA hrep a ha
  apply HasFDerivAt.of_isLittleO
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  have hC1 : 0 < 2 * C + 1 := by linarith
  set ε := c / (2 * C + 1) with hε_def
  have hε : 0 < ε := div_pos hc hC1
  have hεc : (2 * C + 1) * ε = c := by rw [hε_def]; field_simp
  set K : Set (Rn n) := A ∩ closedBall a 1 with hK_def
  have hK : IsCompact K := (isCompact_closedBall a 1).inter_left hA
  obtain ⟨δ₁, hδ₁, hWK⟩ := hW K inter_subset_left hK ε hε
  obtain ⟨τ, hτ, hντ⟩ := Metric.continuousWithinAt_iff.mp (hν a ha) ε hε
  set r := min 1 (min δ₁ τ) with hr_def
  have hr : 0 < r := lt_min one_pos (lt_min hδ₁ hτ)
  have hrδ : r ≤ δ₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hrτ : r ≤ τ := (min_le_right _ _).trans (min_le_right _ _)
  set ρ := r / (C + 2) with hρ_def
  have hC2 : 0 < C + 2 := by linarith
  have hρ : 0 < ρ := div_pos hr hC2
  have hρr : (C + 1) * ρ < r := by
    rw [hρ_def, mul_div_assoc', div_lt_iff₀ hC2]
    nlinarith
  have hρr' : ρ < r := by
    have : ρ ≤ (C + 1) * ρ := by nlinarith
    linarith
  have haK : a ∈ K := ⟨ha, mem_closedBall_self zero_le_one⟩
  have hWa : ∀ b ∈ A, ‖b - a‖ < δ₁ → |h b - h a - inner ℝ (ν a) (b - a)| ≤ ε * ‖b - a‖ := by
    intro b hb hba
    rcases eq_or_ne b a with rfl | hne
    · simp
    · exact hWK a haK b hb (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) hba
  filter_upwards [Metric.ball_mem_nhds a hρ] with x hx
  have hxa : ‖x - a‖ < ρ := by simpa [dist_eq_norm] using hx
  rw [innerSL_apply_apply, hgA a ha, Real.norm_eq_abs, ← hεc]
  by_cases hxA : x ∈ A
  · rw [hgA x hxA]
    have h1 := hWa x hxA (by linarith)
    have h2 : ε * ‖x - a‖ ≤ (2 * C + 1) * ε * ‖x - a‖ := by
      have : ε ≤ (2 * C + 1) * ε := by nlinarith
      exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
    exact h1.trans h2
  · obtain ⟨S, hS, hS1, hval⟩ := hrep x hxA
    have hid : g x - h a - inner ℝ (ν a) (x - a) = ∑ i ∈ S, φ i x *
        ((h (p i) + inner ℝ (ν (p i)) (x - p i)) - (h a + inner ℝ (ν a) (x - a))) := by
      rw [hval]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hS1, one_mul]
      ring
    rw [hid]
    have hdx : infDist x A ≤ ‖x - a‖ := by rw [← dist_eq_norm]; exact infDist_le_dist_of_mem ha
    have hterm : ∀ i ∈ S, |(h (p i) + inner ℝ (ν (p i)) (x - p i)) - (h a + inner ℝ (ν a) (x - a))|
        ≤ (2 * C + 1) * ε * ‖x - a‖ := by
      intro i hi
      have hxp : ‖x - p i‖ ≤ C * ‖x - a‖ := (hS i hi).2.trans (mul_le_mul_of_nonneg_left hdx hC)
      have hpa : ‖p i - a‖ ≤ (C + 1) * ‖x - a‖ := by
        calc ‖p i - a‖ = ‖(x - a) - (x - p i)‖ := by congr 1; abel
          _ ≤ ‖x - a‖ + ‖x - p i‖ := norm_sub_le _ _
          _ ≤ ‖x - a‖ + C * ‖x - a‖ := by linarith
          _ = (C + 1) * ‖x - a‖ := by ring
      have hpa_lt : ‖p i - a‖ < r := by
        have : (C + 1) * ‖x - a‖ ≤ (C + 1) * ρ := mul_le_mul_of_nonneg_left hxa.le (by linarith)
        linarith
      have hνi : ‖ν (p i) - ν a‖ ≤ ε := by
        have := hντ (hp i) (by rw [dist_eq_norm]; linarith)
        rw [dist_eq_norm] at this
        exact this.le
      have hWi := hWa (p i) (hp i) (by linarith)
      have hE1 : (h (p i) + inner ℝ (ν (p i)) (x - p i)) - (h a + inner ℝ (ν a) (x - a)) =
          (h (p i) - h a - inner ℝ (ν a) (p i - a)) + inner ℝ (ν (p i) - ν a) (x - p i) := by
        have hsplit : x - a = (x - p i) + (p i - a) := by abel
        rw [inner_sub_left, hsplit, inner_add_right]
        ring
      rw [hE1]
      calc |(h (p i) - h a - inner ℝ (ν a) (p i - a)) + inner ℝ (ν (p i) - ν a) (x - p i)|
          ≤ |h (p i) - h a - inner ℝ (ν a) (p i - a)| + |inner ℝ (ν (p i) - ν a) (x - p i)| :=
            abs_add_le _ _
        _ ≤ ε * ‖p i - a‖ + ‖ν (p i) - ν a‖ * ‖x - p i‖ :=
            add_le_add hWi (abs_real_inner_le_norm _ _)
        _ ≤ ε * ((C + 1) * ‖x - a‖) + ε * (C * ‖x - a‖) := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left hpa hε.le
            · exact mul_le_mul hνi hxp (norm_nonneg _) hε.le
        _ = (2 * C + 1) * ε * ‖x - a‖ := by ring
    calc |∑ i ∈ S, φ i x * ((h (p i) + inner ℝ (ν (p i)) (x - p i)) - (h a + inner ℝ (ν a) (x - a)))|
        ≤ ∑ i ∈ S, |φ i x * ((h (p i) + inner ℝ (ν (p i)) (x - p i)) - (h a + inner ℝ (ν a) (x - a)))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ S, φ i x * |(h (p i) + inner ℝ (ν (p i)) (x - p i)) - (h a + inner ℝ (ν a) (x - a))| := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [abs_mul, abs_of_nonneg (hS i hi).1]
      _ ≤ ∑ i ∈ S, φ i x * ((2 * C + 1) * ε * ‖x - a‖) := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_left (hterm i hi) (hS i hi).1
      _ = (2 * C + 1) * ε * ‖x - a‖ := by rw [← Finset.sum_mul, hS1, one_mul]

/-- **Simon Ch. 2, Theorem 1.6 (pp. 42–43), Whitney extension: continuity of `Dg` on `A`.** Let
`A ⊂ ℝⁿ` be closed, `ν` continuous on `A`, `(h, ν)` satisfy the uniform first-order condition of
1.6 on compact subsets of `A`, `C, M ≥ 0`, and the anchors `pᵢ` lie in `A`. Suppose
`Dg(x) = ⟨ν(x), ·⟩` for `x ∈ A`, and for `x ∉ A`, with `d = dist(·, A)`, there is a finite `S` with
`Dg(x) = ∑_{i ∈ S} (φᵢ(x) ⟨ν(pᵢ), ·⟩ + Pᵢ(x) Dφᵢ(x))`, `Pᵢ(x) = h(pᵢ) + ⟨ν(pᵢ), x - pᵢ⟩`,
where `φᵢ(x) ≥ 0`, `|x - pᵢ| ≤ C d(x)`, `∑ φᵢ(x) = 1`, `∑ Dφᵢ(x) = 0`, and
`∑ ‖Dφᵢ(x)‖ ≤ M / d(x)` if `d(x) ≤ 1`. Then `Dg` is continuous at every `a ∈ A`. For `x ∉ A`
near `a`, `Dg(x) - ⟨ν(a), ·⟩ = ∑ φᵢ(x) ⟨ν(pᵢ) - ν(a), ·⟩ + ∑ (Pᵢ(x) - c) Dφᵢ(x)`, where `c` is
the jet of a nearest point `a* ∈ A` evaluated at `x`; `|Pᵢ(x) - c| ≤ ε(3C + 1) d(x)` then gives
`‖Dg(x) - Dg(a)‖ ≤ ε(1 + (3C + 1)M)`. -/
theorem Submission.whitney_gluing_continuousAt_fderiv : ∀ (n : ℕ) (A : Set (Rn n)) (h : Rn n → ℝ) (ν : Rn n → Rn n) (ι : Type) (φ : ι → Rn n → ℝ) (p : ι → Rn n) (C M : ℝ) (g : Rn n → ℝ), IsClosed A → ContinuousOn ν A → (∀ K ⊆ A, IsCompact K → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ y ∈ A, 0 < ‖y - x‖ → ‖y - x‖ < δ → |h y - h x - inner ℝ (ν x) (y - x)| ≤ ε * ‖y - x‖) → 0 ≤ C → 0 ≤ M → (∀ i, p i ∈ A) → (∀ x ∈ A, fderiv ℝ g x = innerSL ℝ (ν x)) → (∀ x ∉ A, ∃ S : Finset ι, (∀ i ∈ S, 0 ≤ φ i x ∧ ‖x - p i‖ ≤ C * Metric.infDist x A) ∧ ∑ i ∈ S, φ i x = 1 ∧ ∑ i ∈ S, fderiv ℝ (φ i) x = 0 ∧ (Metric.infDist x A ≤ 1 → ∑ i ∈ S, ‖fderiv ℝ (φ i) x‖ ≤ M / Metric.infDist x A) ∧ fderiv ℝ g x = ∑ i ∈ S, (φ i x • innerSL ℝ (ν (p i)) + (h (p i) + inner ℝ (ν (p i)) (x - p i)) • fderiv ℝ (φ i) x)) → ∀ a ∈ A, ContinuousAt (fderiv ℝ g) a := by
  intro n A h ν ι φ p C M g hA hν hW hC hM hp hFD hrep a ha
  rw [Metric.continuousAt_iff]
  intro η hη
  -- Step 1: `ε = η / (2B)` with `B = 1 + (3C + 1)M ≥ 1`, so `εB < η` and `ε < η`.
  have hB : 0 < 1 + (3 * C + 1) * M := by nlinarith
  set ε := η / (2 * (1 + (3 * C + 1) * M)) with hε_def
  have hε : 0 < ε := div_pos hη (by linarith)
  have hεB : ε * (1 + (3 * C + 1) * M) < η := by
    rw [hε_def, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  have hεη : ε < η := by
    have h0 : 0 ≤ (3 * C + 1) * M := mul_nonneg (by linarith) hM
    have : ε ≤ ε * (1 + (3 * C + 1) * M) := by nlinarith [mul_nonneg hε.le h0]
    linarith
  -- Step 2: the uniform condition on the compact `K = A ∩ B̄(a, 1)` gives `δ₁`.
  set K : Set (Rn n) := A ∩ closedBall a 1 with hK_def
  have hK : IsCompact K := (isCompact_closedBall a 1).inter_left hA
  obtain ⟨δ₁, hδ₁, hWK⟩ := hW K inter_subset_left hK ε hε
  -- Step 3: continuity of `ν` on `A` at `a` gives `τ`.
  obtain ⟨τ, hτ, hντ⟩ := Metric.continuousWithinAt_iff.mp (hν a ha) ε hε
  -- Step 4: `r = min {1, δ₁, τ}` and `ρ = r / (C + 2)`.
  set r := min 1 (min δ₁ τ) with hr_def
  have hr : 0 < r := lt_min one_pos (lt_min hδ₁ hτ)
  have hr1 : r ≤ 1 := min_le_left _ _
  have hrδ : r ≤ δ₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hrτ : r ≤ τ := (min_le_right _ _).trans (min_le_right _ _)
  have hC2 : 0 < C + 2 := by linarith
  set ρ := r / (C + 2) with hρ_def
  have hρ : 0 < ρ := div_pos hr hC2
  have hρr : (C + 1) * ρ < r := by
    rw [hρ_def, mul_div_assoc', div_lt_iff₀ hC2]
    nlinarith
  have hρr2 : 2 * ρ ≤ r := by
    rw [hρ_def, mul_div_assoc', div_le_iff₀ hC2]
    nlinarith
  have hρr' : ρ < r := by
    have : ρ ≤ (C + 1) * ρ := by nlinarith
    linarith
  -- (2a): the uniform estimate with base point in `K`, including the trivial case `y = b`.
  have hWK' : ∀ b ∈ K, ∀ y ∈ A, ‖y - b‖ < δ₁ →
      |h y - h b - inner ℝ (ν b) (y - b)| ≤ ε * ‖y - b‖ := by
    intro b hb y hy hyb
    rcases eq_or_ne y b with rfl | hne
    · simp
    · exact hWK b hb y hy (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) hyb
  -- (3a): `‖ν(b) - ν(a)‖ < ε` for `b ∈ A` with `‖b - a‖ < r`.
  have hνa : ∀ b ∈ A, ‖b - a‖ < r → ‖ν b - ν a‖ < ε := by
    intro b hb hba
    have := hντ hb (by rw [dist_eq_norm]; linarith)
    rwa [dist_eq_norm] at this
  -- Step 5: let `‖x - a‖ < ρ`.
  refine ⟨ρ, hρ, fun x hx => ?_⟩
  have hxa : ‖x - a‖ < ρ := by rwa [dist_eq_norm] at hx
  rw [dist_eq_norm, hFD a ha]
  by_cases hxA : x ∈ A
  · -- Case `x ∈ A`: `‖Dg(x) - Dg(a)‖ = ‖ν(x) - ν(a)‖ < ε < η`.
    rw [hFD x hxA, ← map_sub, innerSL_apply_norm]
    exact (hνa x hxA (by linarith)).trans hεη
  · -- Case `x ∉ A`.
    obtain ⟨S, hS, hS1, hD0, hDbound, hfd⟩ := hrep x hxA
    -- (a): `0 < d(x) ≤ ‖x - a‖ < 1`.
    have hne : A.Nonempty := ⟨a, ha⟩
    have hdpos : 0 < infDist x A := (hA.notMem_iff_infDist_pos hne).mp hxA
    have hdx : infDist x A ≤ ‖x - a‖ := by rw [← dist_eq_norm]; exact infDist_le_dist_of_mem ha
    have hd1 : infDist x A ≤ 1 := by linarith
    -- (b): a nearest point `a' ∈ A` of `x` lies in `K` and `‖ν(a') - ν(a)‖ < ε`.
    obtain ⟨a', ha', hda'⟩ := hA.exists_infDist_eq_dist hne x
    have hxa' : ‖x - a'‖ = infDist x A := by rw [hda', dist_eq_norm]
    have ha'a : ‖a' - a‖ < r := by
      have : ‖a' - a‖ ≤ ‖x - a'‖ + ‖x - a‖ := by
        calc ‖a' - a‖ = ‖(x - a) - (x - a')‖ := by congr 1; abel
          _ ≤ ‖x - a‖ + ‖x - a'‖ := norm_sub_le _ _
          _ = ‖x - a'‖ + ‖x - a‖ := add_comm _ _
      linarith
    have ha'K : a' ∈ K := ⟨ha', by rw [mem_closedBall, dist_eq_norm]; linarith⟩
    have hνa' : ‖ν a' - ν a‖ < ε := hνa a' ha' ha'a
    set d := infDist x A with hd_def
    set c := h a' + inner ℝ (ν a') (x - a') with hc_def
    -- (c): `‖ν(pᵢ) - ν(a)‖ ≤ ε` for `i ∈ S`.
    have hνi : ∀ i ∈ S, ‖ν (p i) - ν a‖ ≤ ε := by
      intro i hi
      have hxp : ‖x - p i‖ ≤ C * ‖x - a‖ := (hS i hi).2.trans (mul_le_mul_of_nonneg_left hdx hC)
      have hpa : ‖p i - a‖ ≤ (C + 1) * ‖x - a‖ := by
        calc ‖p i - a‖ = ‖(x - a) - (x - p i)‖ := by congr 1; abel
          _ ≤ ‖x - a‖ + ‖x - p i‖ := norm_sub_le _ _
          _ ≤ ‖x - a‖ + C * ‖x - a‖ := by linarith
          _ = (C + 1) * ‖x - a‖ := by ring
      have : (C + 1) * ‖x - a‖ ≤ (C + 1) * ρ := mul_le_mul_of_nonneg_left hxa.le (by linarith)
      exact (hνa (p i) (hp i) (by linarith)).le
    -- (d), (e): `|Pᵢ(x) - c| ≤ ε(3C + 1)d` for `i ∈ S`, via (E1).
    have hPi : ∀ i ∈ S, |(h (p i) + inner ℝ (ν (p i)) (x - p i)) - c| ≤ ε * (3 * C + 1) * d := by
      intro i hi
      have hxp : ‖x - p i‖ ≤ C * d := (hS i hi).2
      have hpa' : ‖p i - a'‖ ≤ (C + 1) * d := by
        calc ‖p i - a'‖ = ‖(x - a') - (x - p i)‖ := by congr 1; abel
          _ ≤ ‖x - a'‖ + ‖x - p i‖ := norm_sub_le _ _
          _ ≤ d + C * d := by rw [hxa']; linarith
          _ = (C + 1) * d := by ring
      have hpa'δ : ‖p i - a'‖ < δ₁ := by
        have : (C + 1) * d ≤ (C + 1) * ρ := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        linarith
      have hWi := hWK' a' ha'K (p i) (hp i) hpa'δ
      have hνpa' : ‖ν (p i) - ν a'‖ ≤ 2 * ε := by
        calc ‖ν (p i) - ν a'‖ = ‖(ν (p i) - ν a) - (ν a' - ν a)‖ := by congr 1; abel
          _ ≤ ‖ν (p i) - ν a‖ + ‖ν a' - ν a‖ := norm_sub_le _ _
          _ ≤ ε + ε := add_le_add (hνi i hi) hνa'.le
          _ = 2 * ε := by ring
      have hE1 : (h (p i) + inner ℝ (ν (p i)) (x - p i)) - c =
          (h (p i) - h a' - inner ℝ (ν a') (p i - a')) + inner ℝ (ν (p i) - ν a') (x - p i) := by
        have hsplit : x - a' = (x - p i) + (p i - a') := by abel
        rw [hc_def, inner_sub_left, hsplit, inner_add_right]
        ring
      rw [hE1]
      calc |(h (p i) - h a' - inner ℝ (ν a') (p i - a')) + inner ℝ (ν (p i) - ν a') (x - p i)|
          ≤ |h (p i) - h a' - inner ℝ (ν a') (p i - a')| + |inner ℝ (ν (p i) - ν a') (x - p i)| :=
            abs_add_le _ _
        _ ≤ ε * ‖p i - a'‖ + ‖ν (p i) - ν a'‖ * ‖x - p i‖ :=
            add_le_add hWi (abs_real_inner_le_norm _ _)
        _ ≤ ε * ((C + 1) * d) + (2 * ε) * (C * d) := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left hpa' hε.le
            · exact mul_le_mul hνpa' hxp (norm_nonneg _) (by linarith)
        _ = ε * (3 * C + 1) * d := by ring
    -- (f): `Dg(x) - ⟨ν(a), ·⟩ = ∑ φᵢ(x) (L_{ν(pᵢ)} - L_{ν(a)}) + ∑ (Pᵢ(x) - c) Dφᵢ(x)`.
    have hrepr : fderiv ℝ g x - innerSL ℝ (ν a) =
        ∑ i ∈ S, φ i x • (innerSL ℝ (ν (p i)) - innerSL ℝ (ν a)) +
          ∑ i ∈ S, ((h (p i) + inner ℝ (ν (p i)) (x - p i)) - c) • fderiv ℝ (φ i) x := by
      rw [hfd]
      simp_rw [smul_sub, sub_smul]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        ← Finset.sum_smul, ← Finset.smul_sum, hS1, hD0, one_smul, smul_zero, sub_zero]
      abel
    rw [hrepr]
    -- (g): the first sum has norm `≤ ε`, the second `≤ ε(3C + 1)M`.
    have hfirst : ‖∑ i ∈ S, φ i x • (innerSL ℝ (ν (p i)) - innerSL ℝ (ν a))‖ ≤ ε := by
      calc ‖∑ i ∈ S, φ i x • (innerSL ℝ (ν (p i)) - innerSL ℝ (ν a))‖
          ≤ ∑ i ∈ S, ‖φ i x • (innerSL ℝ (ν (p i)) - innerSL ℝ (ν a))‖ := norm_sum_le _ _
        _ = ∑ i ∈ S, φ i x * ‖ν (p i) - ν a‖ := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [norm_smul, Real.norm_of_nonneg (hS i hi).1, ← map_sub, innerSL_apply_norm]
        _ ≤ ∑ i ∈ S, φ i x * ε := by
            apply Finset.sum_le_sum
            intro i hi
            exact mul_le_mul_of_nonneg_left (hνi i hi) (hS i hi).1
        _ = ε := by rw [← Finset.sum_mul, hS1, one_mul]
    have hsecond : ‖∑ i ∈ S, ((h (p i) + inner ℝ (ν (p i)) (x - p i)) - c) • fderiv ℝ (φ i) x‖ ≤
        ε * (3 * C + 1) * M := by
      calc ‖∑ i ∈ S, ((h (p i) + inner ℝ (ν (p i)) (x - p i)) - c) • fderiv ℝ (φ i) x‖
          ≤ ∑ i ∈ S, ‖((h (p i) + inner ℝ (ν (p i)) (x - p i)) - c) • fderiv ℝ (φ i) x‖ :=
            norm_sum_le _ _
        _ = ∑ i ∈ S, |(h (p i) + inner ℝ (ν (p i)) (x - p i)) - c| * ‖fderiv ℝ (φ i) x‖ := by
            apply Finset.sum_congr rfl
            intro i _
            rw [norm_smul, Real.norm_eq_abs]
        _ ≤ ∑ i ∈ S, (ε * (3 * C + 1) * d) * ‖fderiv ℝ (φ i) x‖ := by
            apply Finset.sum_le_sum
            intro i hi
            exact mul_le_mul_of_nonneg_right (hPi i hi) (norm_nonneg _)
        _ = (ε * (3 * C + 1) * d) * ∑ i ∈ S, ‖fderiv ℝ (φ i) x‖ := by rw [Finset.mul_sum]
        _ ≤ (ε * (3 * C + 1) * d) * (M / d) := by
            apply mul_le_mul_of_nonneg_left (hDbound hd1)
            have : 0 ≤ 3 * C + 1 := by linarith
            positivity
        _ = ε * (3 * C + 1) * M := by field_simp
    calc ‖∑ i ∈ S, φ i x • (innerSL ℝ (ν (p i)) - innerSL ℝ (ν a)) +
          ∑ i ∈ S, ((h (p i) + inner ℝ (ν (p i)) (x - p i)) - c) • fderiv ℝ (φ i) x‖
        ≤ ‖∑ i ∈ S, φ i x • (innerSL ℝ (ν (p i)) - innerSL ℝ (ν a))‖ +
          ‖∑ i ∈ S, ((h (p i) + inner ℝ (ν (p i)) (x - p i)) - c) • fderiv ℝ (φ i) x‖ :=
          norm_add_le _ _
      _ ≤ ε + ε * (3 * C + 1) * M := add_le_add hfirst hsecond
      _ = ε * (1 + (3 * C + 1) * M) := by ring
      _ < η := hεB

/-- Simon Ch. 2, Theorem 1.6, gluing step: let `A ⊆ ℝⁿ` be closed, `(h, ν)` a Whitney jet on `A`
(`ν` continuous on `A`, `R(x,y) → 0` uniformly on compact subsets of `A`), and `(φᵢ, pᵢ)` a locally
finite partition of unity on `ℝⁿ \ A` with anchors `pᵢ ∈ A`, `|x - pᵢ| ≤ C d(x)` where `φᵢ(x) ≠ 0`,
and `∑ᶠ ‖Dφᵢ(x)‖ ≤ M / d(x)` where `d(x) = dist(x, A) ≤ 1`. Then the function `g = h` on `A`,
`g = ∑ᶠ φᵢ (h(pᵢ) + ⟨ν(pᵢ), · - pᵢ⟩)` off `A` is `C¹` with `Dg(x)v = ⟨ν(x), v⟩` for `x ∈ A`. -/
theorem Submission.whitney_jet_gluing_c1 : (∀ (n : ℕ) (A : Set (Rn n)) (h : Rn n → ℝ) (ν : Rn n → Rn n) (ι : Type) (φ : ι → Rn n → ℝ) (p : ι → Rn n) (C M : ℝ) (g : Rn n → ℝ), IsClosed A → ContinuousOn ν A → (∀ K ⊆ A, IsCompact K → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ y ∈ A, 0 < ‖y - x‖ → ‖y - x‖ < δ → |h y - h x - inner ℝ (ν x) (y - x)| ≤ ε * ‖y - x‖) → 0 ≤ C → 0 ≤ M → (∀ i, p i ∈ A) → (∀ i, ∀ x ∉ A, ContDiffAt ℝ 1 (φ i) x) → (∀ i, ∀ x ∉ A, 0 ≤ φ i x) → (∀ x ∉ A, ∃ s : Finset ι, ∃ V ∈ 𝓝 x, ∀ i ∉ s, ∀ y ∈ V, φ i y = 0) → (∀ x ∉ A, ∑ᶠ i, φ i x = 1) → (∀ i, ∀ x ∉ A, φ i x ≠ 0 → ‖x - p i‖ ≤ C * Metric.infDist x A) → (∀ x ∉ A, Metric.infDist x A ≤ 1 → ∑ᶠ i, ‖fderiv ℝ (φ i) x‖ ≤ M / Metric.infDist x A) → (∀ x ∈ A, g x = h x) → (∀ x ∉ A, g x = ∑ᶠ i, φ i x * (h (p i) + inner ℝ (ν (p i)) (x - p i))) → ContDiff ℝ 1 g ∧ ∀ x ∈ A, ∀ v, fderiv ℝ g x v = inner ℝ (ν x) v) := by
  intro n A h ν ι φ p C M g hA hν hW hC hM hp hφC1 hφnn hlf hsum hanchor hder hgA hgU
  -- Step 1: off `A`, `g` is `C¹` and is a finite convex combination of the affine jets.
  have hloc := Submission.whitney_gluing_local_structure n A h ν ι φ p g hA hφC1 hφnn hlf hsum hgU
  -- Step 3: `Dg(a) = ⟨ν(a), ·⟩` for `a ∈ A`.
  have hdiffA : ∀ a ∈ A, HasFDerivAt g (innerSL ℝ (ν a)) a := by
    refine Submission.whitney_gluing_hasFDerivAt n A h ν ι φ p C g hA hν hW hC hp hgA ?_
    intro x hx
    obtain ⟨-, S, hpos, hS1, hgx, -, -, -⟩ := hloc x hx
    exact ⟨S, fun i hi => ⟨(hpos i hi).le, hanchor i x hx (hpos i hi).ne'⟩, hS1, hgx⟩
  have hfderivA : ∀ x ∈ A, fderiv ℝ g x = innerSL ℝ (ν x) := fun x hx => (hdiffA x hx).fderiv
  -- Step 4: `Dg` is continuous at every `a ∈ A`.
  have hcontA : ∀ a ∈ A, ContinuousAt (fderiv ℝ g) a := by
    refine Submission.whitney_gluing_continuousAt_fderiv n A h ν ι φ p C M g hA hν hW hC hM hp
      hfderivA ?_
    intro x hx
    obtain ⟨-, S, hpos, hS1, -, hDg, hD0, hnorm⟩ := hloc x hx
    exact ⟨S, fun i hi => ⟨(hpos i hi).le, hanchor i x hx (hpos i hi).ne'⟩, hS1, hD0,
      fun hd => hnorm.symm.le.trans (hder x hx hd), hDg⟩
  -- Step 5: `g` is differentiable with continuous derivative at points of `A` and off `A`.
  refine ⟨contDiff_one_iff_fderiv.mpr ⟨fun x => ?_, continuous_iff_continuousAt.mpr fun x => ?_⟩,
    fun x hx v => by rw [hfderivA x hx, innerSL_apply_apply]⟩
  · by_cases hx : x ∈ A
    · exact (hdiffA x hx).differentiableAt
    · exact (hloc x hx).1.differentiableAt (by norm_num)
  · by_cases hx : x ∈ A
    · exact hcontA x hx
    · exact (hloc x hx).1.continuousAt_fderiv (by norm_num)

/-- **Simon Ch. 2, proof of Theorem 1.6 (pp. 42–43), Whitney partition of unity.** For closed
nonempty `A ⊆ ℝⁿ` and `d = dist(·, A)` there are weights `φ_i`, `C¹`, `≥ 0`, locally finite and
summing to `1` on `ℝⁿ ∖ A`, and anchors `p_i ∈ A` with `|x - p_i| ≤ C d(x)` whenever `φ_i(x) ≠ 0`
and `∑ᶠ i, ‖Dφ_i(x)‖ ≤ M / d(x)` when `d(x) ≤ 1`. With `r = min{1, d}/20`, the Vitali lemma gives
centres `J ⊆ ℝⁿ ∖ A` such that every `x ∉ A` has some `s ∈ J` with `|x - s| ≤ 5 r(s)`, at most
`N` centres with `|x - s| < 10 r(s)`, and only finitely many `s` whose open ball of radius
`10 r(s)` meets the open ball of radius `r(x)` about `x`. The rescaled bumps over this cover,
normalised by their sum and anchored at nearest points of `A`, are the required weights. -/
theorem Submission.whitney_smooth_partition_of_unity : ∀ (n : ℕ) (A : Set (Rn n)), IsClosed A → A.Nonempty → ∃ (ι : Type) (φ : ι → Rn n → ℝ) (p : ι → Rn n) (C M : ℝ), 0 ≤ C ∧ 0 ≤ M ∧ (∀ i, p i ∈ A) ∧ (∀ i, ∀ x ∉ A, ContDiffAt ℝ 1 (φ i) x) ∧ (∀ i, ∀ x ∉ A, 0 ≤ φ i x) ∧ (∀ x ∉ A, ∃ s : Finset ι, ∃ V ∈ 𝓝 x, ∀ i ∉ s, ∀ y ∈ V, φ i y = 0) ∧ (∀ x ∉ A, ∑ᶠ i, φ i x = 1) ∧ (∀ i, ∀ x ∉ A, φ i x ≠ 0 → ‖x - p i‖ ≤ C * Metric.infDist x A) ∧ (∀ x ∉ A, Metric.infDist x A ≤ 1 → ∑ᶠ i, ‖fderiv ℝ (φ i) x‖ ≤ M / Metric.infDist x A) := by
  intro n A hA hne
  -- Steps 1–5 (Vitali cover of `ℝⁿ ∖ A`): covering, bounded overlap `N`, local finiteness.
  obtain ⟨J, N, hJ, hcov, hover, hloc⟩ := Submission.whitney_cover_finite_overlap n A hA hne
  -- Steps 6–9: nearest-point anchors and the normalised rescaled bumps over that cover.
  exact Submission.whitney_partition_of_finite_overlap_cover n A J N hA hne hJ hcov hover hloc

/-- **Simon Ch. 2, Theorem 1.6 (pp. 42–43), Whitney extension** (DAG node
`root.whitney_extension-a1`). If `A = ∅` take `g = 0`. Otherwise take a Whitney partition of
unity `φᵢ` of `ℝⁿ \ A` with anchors `pᵢ ∈ A` (`Submission.whitney_smooth_partition_of_unity`),
put `g = h` on `A` and `g = ∑ᶠ i, φᵢ · (h(pᵢ) + ⟨ν(pᵢ), · - pᵢ⟩)` off `A`, and conclude by the
`C¹` gluing lemma `Submission.whitney_jet_gluing_c1`. -/
theorem Submission.whitney_extension_theorem : WhitneyExtension := by
  intro n A h ν hA _ hν hW
  rcases A.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ ↦ 0, contDiff_const, fun x hx ↦ absurd hx (notMem_empty x)⟩
  obtain ⟨ι, φ, p, C, M, hC, hM, hp, hφ, hφ0, hloc, hsum, hanchor, hdφ⟩ :=
    Submission.whitney_smooth_partition_of_unity n A hA hne
  classical
  let g : Rn n → ℝ := fun x ↦
    if x ∈ A then h x else ∑ᶠ i, φ i x * (h (p i) + inner ℝ (ν (p i)) (x - p i))
  have hgA : ∀ x ∈ A, g x = h x := fun x hx ↦ ite_eq_left hx
  obtain ⟨hg, hDg⟩ := Submission.whitney_jet_gluing_c1 n A h ν ι φ p C M g hA hν hW hC hM hp hφ
    hφ0 hloc hsum hanchor hdφ hgA fun x hx ↦ ite_eq_right hx
  exact ⟨g, hg, fun x hx ↦ ⟨hgA x hx, hDg x hx⟩⟩

/-- The frozen Chapter 2 contract: the conjunction of all headline results. -/
theorem main_theorem : LipschitzExtension ∧ Rademacher ∧ C1Approximation ∧ WhitneyExtension ∧ LipschitzImageHausdorff ∧ EilenbergInequality ∧ BVCompactness ∧ BVPoincare ∧ BVExtensionEstimate ∧ AreaFormula ∧ FirstVariation ∧ SecondVariation ∧ StationaryIffMeanCurvatureZero ∧ SecondVariationStationary ∧ CoareaFormula ∧ C1Sard := by sorry

end GMT.Ch02
