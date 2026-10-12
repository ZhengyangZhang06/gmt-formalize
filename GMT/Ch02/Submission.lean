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

/-- **Weighted gradient estimate** (Simon 2.8 proof, C4, Simon's (5)). Let `U ⊆ B_R(ξ)` be open,
`u ∈ L¹(ℝⁿ)` and `φ : ℝⁿ → ℝ` Lipschitz with `0 ≤ φ ≤ 1`, `spt φ ⊆ U` compact and
`r |Dφ(x)| ≤ -Dφ(x)[x - ξ]` for a.e. `x`. Then `r ∫ |u| |Dφ| ≤ R |D|u||(U) + n ∫_U |u|`. The field
`V = φ (x - ξ)/R` is Lipschitz with `spt V ⊆ U` compact and `|V| ≤ 1`, so `-V` is admissible for
`|D|u||(U)`. By Rademacher, `R div V = n φ + Dφ[x - ξ]` a.e., so
`r |u| |Dφ| ≤ n |u| φ - R |u| div V` a.e., and integrating gives the estimate. -/
theorem Submission.bv_ext_lintegral_enorm_mul_fderiv_le : ∀ (n : ℕ) (U : Set (Rn n)) (ξ : Rn n) (R r : ℝ) (u φ : Rn n → ℝ), IsOpen U → 0 < R → U ⊆ closedBall ξ R → Integrable u volume → (∃ K, LipschitzWith K φ) → (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) → HasCompactSupport φ → tsupport φ ⊆ U → (∀ᵐ x ∂volume, r * ‖fderiv ℝ φ x‖ ≤ -fderiv ℝ φ x (x - ξ)) → ENNReal.ofReal r * ∫⁻ x, ‖u x‖ₑ * ‖fderiv ℝ φ x‖ₑ ≤ ENNReal.ofReal R * Chapter02.bvVariationOn (fun x ↦ |u x|) U + (n : ℝ≥0∞) * ∫⁻ x in U, ‖u x‖ₑ := by
  rintro n U ξ R r u φ hUo hR hUB hu ⟨K, hφ⟩ hφ01 hφcs hφU hdir
  -- Step 1: the case `r ≤ 0` is trivial, since then `ofReal r = 0`.
  rcases le_or_gt r 0 with hr | hr
  · rw [ENNReal.ofReal_of_nonpos hr, zero_mul]
    exact bot_le
  -- Step 2: the field `V = φ • c`, where `c y = R⁻¹ • (y - ξ)`.
  set c : Rn n → Rn n := fun y ↦ R⁻¹ • (y - ξ) with hc_def
  set V : Rn n → Rn n := fun y ↦ φ y • c y with hV_def
  have hRinv : 0 ≤ R⁻¹ := inv_nonneg.mpr hR.le
  -- (i) `‖y - ξ‖ ≤ R` wherever `φ y ≠ 0`, since then `y ∈ tsupport φ ⊆ U ⊆ B_R(ξ)`.
  have hball : ∀ y, φ y ≠ 0 → ‖y - ξ‖ ≤ R := fun y hy ↦ by
    have hy' : y ∈ closedBall ξ R := hUB (hφU (subset_tsupport φ hy))
    rwa [mem_closedBall, dist_eq_norm] at hy'
  have hφ1 : ∀ x, ‖φ x‖ ≤ 1 := fun x ↦ by
    rw [Real.norm_of_nonneg (hφ01 x).1]
    exact (hφ01 x).2
  -- (ii) `V` is `(K + R⁻¹)`-Lipschitz: if `φ x ≠ 0`, then
  -- `V x - V y = R⁻¹ • ((φ x - φ y) • (x - ξ) + φ y • (x - y))`.
  have hkey : ∀ x y, φ x ≠ 0 → ‖V x - V y‖ ≤ (K + R⁻¹) * ‖x - y‖ := fun x y hx ↦ by
    have hsplit : V x - V y = R⁻¹ • ((φ x - φ y) • (x - ξ) + φ y • (x - y)) := by
      simp only [hV_def, hc_def]
      module
    have hφxy : ‖φ x - φ y‖ ≤ K * ‖x - y‖ := by
      simpa only [dist_eq_norm] using hφ.dist_le_mul x y
    rw [hsplit, norm_smul, Real.norm_of_nonneg hRinv]
    calc R⁻¹ * ‖(φ x - φ y) • (x - ξ) + φ y • (x - y)‖
        ≤ R⁻¹ * (‖φ x - φ y‖ * ‖x - ξ‖ + ‖φ y‖ * ‖x - y‖) := by
          gcongr
          rw [← norm_smul, ← norm_smul]
          exact norm_add_le _ _
      _ ≤ R⁻¹ * (K * ‖x - y‖ * R + 1 * ‖x - y‖) := by
          gcongr
          · exact hball x hx
          · exact hφ1 y
      _ = (K + R⁻¹) * ‖x - y‖ := by
          field_simp
  -- The case `φ y ≠ 0` is symmetric, and `V x = V y = 0` if `φ x = φ y = 0`.
  have hVlip : LipschitzWith (K + R⁻¹.toNNReal) V := by
    refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_add, Real.coe_toNNReal _ hRinv]
    by_cases hx : φ x = 0
    · by_cases hy : φ y = 0
      · simp only [hV_def, hx, hy, zero_smul, sub_self, norm_zero]
        positivity
      · rw [norm_sub_rev, norm_sub_rev x y]
        exact hkey y x hy
    · exact hkey x y hx
  -- (iii) `V` has compact support and `tsupport V ⊆ tsupport φ ⊆ U`.
  have hVcs : HasCompactSupport V := hφcs.smul_right
  have hVU : tsupport V ⊆ U := (tsupport_smul_subset_left φ c).trans hφU
  -- (iv) `‖V y‖ = φ y ‖y - ξ‖ / R ≤ 1`.
  have hV1 : ∀ y, ‖V y‖ ≤ 1 := fun y ↦ by
    by_cases hy : φ y = 0
    · simp [hV_def, hy]
    · calc ‖V y‖ = ‖φ y‖ * (R⁻¹ * ‖y - ξ‖) := by
            rw [hV_def, hc_def]
            simp only
            rw [norm_smul, norm_smul, Real.norm_of_nonneg hRinv]
        _ ≤ 1 * (R⁻¹ * R) := by
            gcongr
            · exact hφ1 y
            · exact hball y hy
        _ = 1 := by field_simp
  -- Step 3: `-V` is admissible for `U`, so `ofReal b ≤ |D|u||(U)`.
  have hadm : ENNReal.ofReal (∫ x in U, |u x| * Chapter02.euclideanDivergence (-V) x) ≤
      Chapter02.bvVariationOn (fun x ↦ |u x|) U :=
    Submission.bv_ext_ofReal_integral_le_bvVariationOn n U (fun x ↦ |u x|) (-V) _ hVlip.neg
      hVcs.neg (by rw [tsupport_neg]; exact hVU) (fun y ↦ by rw [Pi.neg_apply, norm_neg]; exact hV1 y)
  -- Step 4: `div (-V) = - div V`, and `div (-V)` vanishes off `tsupport (-V) ⊆ U`.
  have hdivneg : ∀ x, Chapter02.euclideanDivergence (-V) x = -Chapter02.euclideanDivergence V x := by
    intro x
    unfold Chapter02.euclideanDivergence
    rw [fderiv_neg, ContinuousLinearMap.toLinearMap_neg, map_neg]
  set b : ℝ := ∫ x in U, |u x| * Chapter02.euclideanDivergence (-V) x with hb_def
  have hb : b = -∫ x, |u x| * Chapter02.euclideanDivergence V x := by
    rw [hb_def, setIntegral_eq_integral_of_forall_compl_eq_zero, ← integral_neg]
    · simp only [hdivneg, mul_neg]
    · intro x hx
      have h0 : Chapter02.euclideanDivergence (-V) x = 0 := Function.notMem_support.mp fun h ↦
        hx ((tsupport_neg V ▸ hVU) (Chapter02.support_euclideanDivergence_subset (-V) h))
      rw [h0, mul_zero]
  -- Step 5: `Dc = R⁻¹ • id`, so `div c = n / R`, and where `φ` is differentiable (a.e., by
  -- Rademacher) the product rule gives `-Dφ(x)[x - ξ] = n φ(x) - R div V(x)`.
  have hc_deriv : ∀ x, HasFDerivAt c (R⁻¹ • ContinuousLinearMap.id ℝ (Rn n)) x := fun x ↦
    ((hasFDerivAt_id x).sub_const ξ).const_smul R⁻¹
  have hdivc : ∀ x, Chapter02.euclideanDivergence c x = R⁻¹ * n := by
    intro x
    unfold Chapter02.euclideanDivergence
    rw [(hc_deriv x).fderiv, ContinuousLinearMap.toLinearMap_smul, map_smul,
      ContinuousLinearMap.coe_id, LinearMap.trace_id, finrank_euclideanSpace_fin, smul_eq_mul]
  have hdivV : ∀ᵐ x ∂(volume : Measure (Rn n)),
      -fderiv ℝ φ x (x - ξ) = n * φ x - R * Chapter02.euclideanDivergence V x := by
    filter_upwards [hφ.ae_differentiableAt] with x hφx
    have h := Submission.bv_ext_euclideanDivergence_smul n φ c x hφx (hc_deriv x).differentiableAt
    rw [hdivc x] at h
    rw [h]
    simp only [hc_def, map_smul, smul_eq_mul]
    field_simp
    ring
  -- Step 6: the pointwise a.e. inequality `r |u| ‖Dφ‖ ≤ n |u| φ - R |u| div V`.
  have hpt : ∀ᵐ x ∂(volume : Measure (Rn n)),
      r * (|u x| * ‖fderiv ℝ φ x‖) ≤
        n * (|u x| * φ x) - R * (|u x| * Chapter02.euclideanDivergence V x) := by
    filter_upwards [hdir, hdivV] with x hx hxV
    have hux : 0 ≤ |u x| := abs_nonneg _
    have := mul_le_mul_of_nonneg_left hx hux
    rw [hxV] at this
    nlinarith [this]
  -- Step 7: integrability: `|u| ∈ L¹` times the bounded measurable `‖Dφ‖ ≤ K`, `φ ≤ 1` and
  -- `|div V| ≤ n (K + R⁻¹)`.
  have hint1 : Integrable fun x ↦ |u x| * ‖fderiv ℝ φ x‖ :=
    hu.abs.mul_bdd (measurable_fderiv ℝ φ).norm.aestronglyMeasurable
      (ae_of_all _ fun x ↦ (norm_norm _).trans_le (norm_fderiv_le_of_lipschitz ℝ hφ))
  have hint2 : Integrable fun x ↦ |u x| * φ x :=
    hu.abs.mul_bdd hφ.continuous.aestronglyMeasurable (ae_of_all _ hφ1)
  have hint3 : Integrable fun x ↦ |u x| * Chapter02.euclideanDivergence V x :=
    hu.abs.mul_bdd (Chapter02.measurable_euclideanDivergence _).aestronglyMeasurable
      (ae_of_all _ (Chapter02.norm_euclideanDivergence_le_of_lipschitz hVlip))
  -- Step 8: integrate the pointwise inequality.
  have hineq : r * ∫ x, |u x| * ‖fderiv ℝ φ x‖ ≤
      n * (∫ x, |u x| * φ x) - R * ∫ x, |u x| * Chapter02.euclideanDivergence V x := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul, ← integral_sub]
    · exact integral_mono_ae (hint1.const_mul r) ((hint2.const_mul _).sub (hint3.const_mul _)) hpt
    · exact hint2.const_mul _
    · exact hint3.const_mul _
  -- Step 9: the first term: `|u| φ` vanishes off `U` and `|u| φ ≤ |u|`, so `∫ |u| φ ≤ a`.
  set a : ℝ := ∫ x in U, |u x| with ha_def
  have hfirst : ∫ x, |u x| * φ x ≤ a := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := U)]
    · refine setIntegral_mono_on hint2.integrableOn hu.abs.integrableOn hUo.measurableSet
        fun x _ ↦ ?_
      exact mul_le_of_le_one_right (abs_nonneg _) (hφ01 x).2
    · intro x hx
      rw [image_eq_zero_of_notMem_tsupport fun h ↦ hx (hφU h), mul_zero]
  have hA : ENNReal.ofReal a = ∫⁻ x in U, ‖u x‖ₑ := by
    rw [ha_def, ← ofReal_integral_norm_eq_lintegral_enorm hu.integrableOn]
    simp only [Real.norm_eq_abs]
  -- Step 10: the second term is `-∫ |u| div V = b` (Step 4), and `ofReal b ≤ |D|u||(U)`.
  -- Step 11: so `r ∫ |u| ‖Dφ‖ ≤ n a + R b`; convert to `[0, ∞]`.
  have hreal : r * ∫ x, |u x| * ‖fderiv ℝ φ x‖ ≤ n * a + R * b := by
    rw [hb]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [mul_le_mul_of_nonneg_left hfirst hn0]
  have hlint : ∫⁻ x, ‖u x‖ₑ * ‖fderiv ℝ φ x‖ₑ = ENNReal.ofReal (∫ x, |u x| * ‖fderiv ℝ φ x‖) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint1
      (ae_of_all _ fun x ↦ mul_nonneg (abs_nonneg _) (norm_nonneg _))]
    refine lintegral_congr fun x ↦ ?_
    rw [ENNReal.ofReal_mul (abs_nonneg _), ← Real.norm_eq_abs, ofReal_norm, ofReal_norm]
  calc ENNReal.ofReal r * ∫⁻ x, ‖u x‖ₑ * ‖fderiv ℝ φ x‖ₑ
      = ENNReal.ofReal (r * ∫ x, |u x| * ‖fderiv ℝ φ x‖) := by
        rw [hlint, ENNReal.ofReal_mul hr.le]
    _ ≤ ENNReal.ofReal (n * a + R * b) := ENNReal.ofReal_le_ofReal hreal
    _ ≤ ENNReal.ofReal (n * a) + ENNReal.ofReal (R * b) := ENNReal.ofReal_add_le
    _ = (n : ℝ≥0∞) * ENNReal.ofReal a + ENNReal.ofReal R * ENNReal.ofReal b := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast,
          ENNReal.ofReal_mul hR.le]
    _ ≤ (n : ℝ≥0∞) * (∫⁻ x in U, ‖u x‖ₑ) +
          ENNReal.ofReal R * Chapter02.bvVariationOn (fun x ↦ |u x|) U := by
        rw [hA]
        gcongr
    _ = ENNReal.ofReal R * Chapter02.bvVariationOn (fun x ↦ |u x|) U +
          (n : ℝ≥0∞) * ∫⁻ x in U, ‖u x‖ₑ :=
        add_comm _ _
/-- **Simon Ch. 2, 2.8, estimate (4) for one test field.** Let `u ∈ L¹(ℝⁿ)`, let `φ` be Lipschitz
with `0 ≤ φ ≤ 1`, compact support and `tsupport φ ⊆ U`, and let `g` be a Lipschitz `C_c` test
field with `sup |g| ≤ 1`. Then `∫ φ u div g ≤ |Du|(U) + ∫ |u| |Dφ|` in `[0, ∞]`. The field
`ψ = φ • g` is admissible for `bvVariationOn u U`, and wherever `φ` and `g` are differentiable
(a.e., by Rademacher) `div ψ = φ div g + Dφ[g]`, so `φ u div g ≤ u div ψ + |u| ‖Dφ‖` a.e. Since
`div ψ` vanishes off `tsupport ψ ⊆ U`, `∫ u div ψ = ∫_U u div ψ ≤ |Du|(U)`. -/
theorem Submission.bv_ext_ofReal_integral_cutoff_le : ∀ (n : ℕ) (U : Set (Rn n)) (u φ : Rn n → ℝ) (g : CompactlySupportedContinuousMap (Rn n) (Rn n)), IsOpen U → Integrable u volume → (∃ K, LipschitzWith K φ) → (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) → HasCompactSupport φ → tsupport φ ⊆ U → Chapter02.IsLipschitzTestField g → Chapter02.compactlySupportedSupNorm g ≤ 1 → ENNReal.ofReal (∫ x, φ x * u x * Chapter02.euclideanDivergence (g : Rn n → Rn n) x) ≤ Chapter02.bvVariationOn u U + ∫⁻ x, ‖u x‖ₑ * ‖fderiv ℝ φ x‖ₑ := by
  rintro n U u φ g - hu ⟨Kφ, hφ⟩ hφ01 hφcs hφU ⟨Kg, hg⟩ hgn
  -- Step 1: `‖g x‖ ≤ compactlySupportedSupNorm g ≤ 1`, and `‖φ x‖ ≤ 1`.
  have hg1 : ∀ x, ‖g x‖ ≤ 1 := by
    obtain ⟨C, hC⟩ := g.continuous.bounded_above_of_compact_support g.hasCompactSupport
    have hbdd : BddAbove (range fun x ↦ ‖g x‖) := ⟨C, by rintro _ ⟨y, rfl⟩; exact hC y⟩
    exact fun x ↦ (le_csSup hbdd ⟨x, rfl⟩).trans hgn
  have hφ1 : ∀ x, ‖φ x‖ ≤ 1 := fun x ↦ by
    rw [Real.norm_of_nonneg (hφ01 x).1]
    exact (hφ01 x).2
  -- Step 2: `ψ = φ • g` is `(Kφ + Kg)`-Lipschitz, compactly supported in `U`, and `‖ψ‖ ≤ 1`.
  set ψ : Rn n → Rn n := fun y ↦ φ y • g y with hψ_def
  have hψ : LipschitzWith (Kφ + Kg) ψ := by
    refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
    have hφxy : ‖φ x - φ y‖ ≤ Kφ * ‖x - y‖ := by
      simpa only [dist_eq_norm] using hφ.dist_le_mul x y
    have hgxy : ‖g x - g y‖ ≤ Kg * ‖x - y‖ := by
      simpa only [dist_eq_norm] using hg.dist_le_mul x y
    have hgx := hg1 x
    have hφy := hφ1 y
    have hsplit : ψ x - ψ y = (φ x - φ y) • g x + φ y • (g x - g y) := by
      simp only [hψ_def]
      rw [sub_smul, smul_sub, sub_add_sub_cancel]
    rw [dist_eq_norm, dist_eq_norm, hsplit]
    calc ‖(φ x - φ y) • g x + φ y • (g x - g y)‖
        ≤ ‖φ x - φ y‖ * ‖g x‖ + ‖φ y‖ * ‖g x - g y‖ := by
          rw [← norm_smul, ← norm_smul]
          exact norm_add_le _ _
      _ ≤ Kφ * ‖x - y‖ * 1 + 1 * (Kg * ‖x - y‖) := by gcongr
      _ = ((Kφ + Kg : ℝ≥0) : ℝ) * ‖x - y‖ := by push_cast; ring
  have hψcs : HasCompactSupport ψ := hφcs.smul_right
  have hψU : tsupport ψ ⊆ U := (tsupport_smul_subset_left φ (g : Rn n → Rn n)).trans hφU
  have hψ1 : ∀ x, ‖ψ x‖ ≤ 1 := fun x ↦ by
    calc ‖ψ x‖ = ‖φ x‖ * ‖g x‖ := norm_smul _ _
      _ ≤ 1 := (mul_le_of_le_one_left (norm_nonneg _) (hφ1 x)).trans (hg1 x)
  -- Step 3: `ψ` is admissible in `U`, and `∫_U u div ψ = ∫ u div ψ` since `div ψ = 0` off
  -- `tsupport ψ ⊆ U`.
  have hset : ∫ x in U, u x * Chapter02.euclideanDivergence ψ x =
      ∫ x, u x * Chapter02.euclideanDivergence ψ x := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ ?_
    rw [Function.notMem_support.mp fun h ↦
      hx (hψU (Chapter02.support_euclideanDivergence_subset ψ h)), mul_zero]
  have hadm : ENNReal.ofReal (∫ x, u x * Chapter02.euclideanDivergence ψ x) ≤
      Chapter02.bvVariationOn u U := by
    rw [← hset]
    exact Submission.bv_ext_ofReal_integral_le_bvVariationOn n U u ψ (Kφ + Kg) hψ hψcs hψU hψ1
  -- Steps 4–5: where `φ` and `g` are differentiable (a.e., Rademacher), the product rule gives
  -- `div ψ = φ div g + Dφ[g]`, so `φ u div g = u div ψ - u Dφ[g] ≤ u div ψ + |u| ‖Dφ‖`.
  have hpt : ∀ᵐ x ∂(volume : Measure (Rn n)),
      φ x * u x * Chapter02.euclideanDivergence (g : Rn n → Rn n) x ≤
        u x * Chapter02.euclideanDivergence ψ x + |u x| * ‖fderiv ℝ φ x‖ := by
    filter_upwards [hφ.ae_differentiableAt, hg.ae_differentiableAt] with x hφx hgx
    have hdiv : Chapter02.euclideanDivergence ψ x =
        φ x * Chapter02.euclideanDivergence (g : Rn n → Rn n) x + fderiv ℝ φ x (g x) :=
      Submission.bv_ext_euclideanDivergence_smul n φ g x hφx hgx
    have hD : ‖fderiv ℝ φ x (g x)‖ ≤ ‖fderiv ℝ φ x‖ := by
      simpa only [mul_one] using (fderiv ℝ φ x).le_opNorm_of_le (hg1 x)
    have hneg : -(u x * fderiv ℝ φ x (g x)) ≤ |u x| * ‖fderiv ℝ φ x‖ :=
      calc -(u x * fderiv ℝ φ x (g x)) ≤ |u x * fderiv ℝ φ x (g x)| := neg_le_abs _
        _ = |u x| * ‖fderiv ℝ φ x (g x)‖ := by rw [abs_mul, Real.norm_eq_abs]
        _ ≤ |u x| * ‖fderiv ℝ φ x‖ := by gcongr
    rw [hdiv]
    linarith
  -- Step 6: integrability, from `|φ| ≤ 1`, `|div g| ≤ n Kg`, `|div ψ| ≤ n (Kφ + Kg)` and
  -- `‖Dφ‖ ≤ Kφ`.
  have hint₁ : Integrable fun x ↦
      φ x * u x * Chapter02.euclideanDivergence (g : Rn n → Rn n) x :=
    (hu.bdd_mul hφ.continuous.aestronglyMeasurable (ae_of_all _ hφ1)).mul_bdd
      (Chapter02.measurable_euclideanDivergence _).aestronglyMeasurable
      (ae_of_all _ (Chapter02.norm_euclideanDivergence_le_of_lipschitz hg))
  have hint₂ : Integrable fun x ↦ u x * Chapter02.euclideanDivergence ψ x :=
    hu.mul_bdd (Chapter02.measurable_euclideanDivergence _).aestronglyMeasurable
      (ae_of_all _ (Chapter02.norm_euclideanDivergence_le_of_lipschitz hψ))
  have hint₃ : Integrable fun x ↦ |u x| * ‖fderiv ℝ φ x‖ :=
    hu.abs.mul_bdd (measurable_fderiv ℝ φ).norm.aestronglyMeasurable
      (ae_of_all _ fun x ↦ (norm_norm _).trans_le (norm_fderiv_le_of_lipschitz ℝ hφ))
  -- Step 7: integrate the a.e. inequality.
  have hle : ∫ x, φ x * u x * Chapter02.euclideanDivergence (g : Rn n → Rn n) x ≤
      (∫ x, u x * Chapter02.euclideanDivergence ψ x) + ∫ x, |u x| * ‖fderiv ℝ φ x‖ := by
    rw [← integral_add hint₂ hint₃]
    exact integral_mono_ae hint₁ (hint₂.add hint₃) hpt
  -- Step 8: pass to `[0, ∞]`, where `ofReal (∫ |u| ‖Dφ‖) = ∫⁻ ‖u‖ₑ ‖Dφ‖ₑ`.
  have hlint : ENNReal.ofReal (∫ x, |u x| * ‖fderiv ℝ φ x‖) =
      ∫⁻ x, ‖u x‖ₑ * ‖fderiv ℝ φ x‖ₑ := by
    rw [ofReal_integral_eq_lintegral_ofReal hint₃
      (ae_of_all _ fun x ↦ mul_nonneg (abs_nonneg _) (norm_nonneg _))]
    refine lintegral_congr fun x ↦ ?_
    rw [ENNReal.ofReal_mul (abs_nonneg _), ← Real.norm_eq_abs, ofReal_norm, ofReal_norm]
  calc ENNReal.ofReal (∫ x, φ x * u x * Chapter02.euclideanDivergence (g : Rn n → Rn n) x)
      ≤ ENNReal.ofReal ((∫ x, u x * Chapter02.euclideanDivergence ψ x) +
          ∫ x, |u x| * ‖fderiv ℝ φ x‖) := ENNReal.ofReal_le_ofReal hle
    _ ≤ ENNReal.ofReal (∫ x, u x * Chapter02.euclideanDivergence ψ x) +
          ENNReal.ofReal (∫ x, |u x| * ‖fderiv ℝ φ x‖) := ENNReal.ofReal_add_le
    _ ≤ Chapter02.bvVariationOn u U + ∫⁻ x, ‖u x‖ₑ * ‖fderiv ℝ φ x‖ₑ :=
      add_le_add hadm hlint.le
/-- **`|Du|(A) = 0` when `u = 0` a.e. on `A`** (Simon 2.8, proof, C0). For a measurable
`A ⊆ ℝⁿ` and `u` vanishing `Lⁿ`-a.e. on `A`, every term `∫_A u div g` of the supremum
`bvVariationOn u A` has an integrand that vanishes `(volume.restrict A)`-a.e.
(`ae_restrict_iff'`), so it is `ofReal 0 = 0`. A supremum of zeros is `0`. -/
theorem Submission.bv_ext_variation_eq_zero_of_ae_eq_zero : ∀ (n : ℕ) (A : Set (Rn n)) (u : Rn n → ℝ), MeasurableSet A → (∀ᵐ x ∂volume, x ∈ A → u x = 0) → Chapter02.bvVariationOn u A = 0 := by
  intro n A u hA hu
  -- Step 2: since `A` is measurable, `u = 0` holds `(volume.restrict A)`-a.e.
  have hu' : ∀ᵐ x ∂(volume.restrict A), u x = 0 := (ae_restrict_iff' hA).2 hu
  -- Step 1: `0 ≤ bvVariationOn u A`, so it suffices to bound every admissible term by `0`.
  refine le_antisymm (iSup_le fun g ↦ iSup_le fun _ ↦ iSup_le fun _ ↦ iSup_le fun _ ↦ ?_) bot_le
  -- Step 3: the integrand `u · div g` vanishes a.e. on `A`, so the term is `ofReal 0 = 0`.
  have h0 : ∫ x in A, u x * Chapter02.euclideanDivergence (g : Rn n → Rn n) x = 0 :=
    integral_eq_zero_of_ae (hu'.mono fun x hx ↦ by simp [hx])
  rw [h0, ENNReal.ofReal_zero]
/-- **Monotonicity of `bvVariationOn` in the domain.** For every `u : ℝⁿ → ℝ` and all sets
`W ⊆ O ⊆ ℝⁿ`, `bvVariationOn u W ≤ bvVariationOn u O`; no openness, measurability or integrability is
assumed. A field `g` admissible for `W` is admissible for `O`, as `tsupport g ⊆ W ⊆ O`. Since `div g`
vanishes off `tsupport g` (SimonGMT `support_euclideanDivergence_subset`), both pairings
`∫_W u div g` and `∫_O u div g` equal `∫ u div g` (`setIntegral_eq_integral_of_forall_compl_eq_zero`,
which needs no measurability of the set). -/
theorem Submission.bv_abs_variation_mono_set : ∀ (n : ℕ) (u : Rn n → ℝ) (W O : Set (Rn n)), W ⊆ O → Chapter02.bvVariationOn u W ≤ Chapter02.bvVariationOn u O := by
  intro n u W O hWO
  -- Step 2: it suffices to bound the pairing of a single field `g` admissible for `W`.
  refine iSup_le fun g ↦ iSup_le fun hg ↦ iSup_le fun hs ↦ iSup_le fun hn ↦ ?_
  -- Step 3: `g` is admissible for `O`.
  have hO : tsupport g ⊆ O := hs.trans hWO
  -- Step 1: `u · div g` vanishes off every `T ⊇ tsupport g`, because `div g` does.
  have hvan : ∀ T : Set (Rn n), tsupport g ⊆ T → ∀ x ∉ T,
      u x * Chapter02.euclideanDivergence (g : Rn n → Rn n) x = 0 := fun T hT x hx ↦ by
    rw [Function.notMem_support.mp fun h ↦ hx (hT (Chapter02.support_euclideanDivergence_subset _ h)),
      mul_zero]
  -- Steps 4–5: both set pairings equal the whole-space pairing, and `g` is admissible for `O`.
  calc ENNReal.ofReal (∫ x in W, u x * Chapter02.euclideanDivergence (g : Rn n → Rn n) x)
      = ENNReal.ofReal (∫ x in O, u x * Chapter02.euclideanDivergence (g : Rn n → Rn n) x) := by
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero (hvan W hs),
          setIntegral_eq_integral_of_forall_compl_eq_zero (hvan O hO)]
    _ ≤ Chapter02.bvVariationOn u O := Chapter02.ofReal_integral_le_bvVariationOn u O g hg hO hn
/-- **Simon Ch. 2, before 2.5 (p. 49), mollifier kernel**, as used for `|D|u|| ≤ |Du|` in the
proof of 2.8 (p. 52). For every `n` and `σ > 0` there is a `C^∞` kernel `ρ ≥ 0` on `ℝⁿ` with
`support ρ ⊆ B(0, σ)` (open ball) and `∫ ρ dLⁿ = 1`. Take the smooth bump `φ` at `0` with radii
`σ/2 < σ`. Its support is `B(0, σ)`, so `∫ φ > 0`, and `ρ = φ / ∫ φ` works. -/
theorem Submission.bv_abs_variation_exists_kernel : ∀ (n : ℕ) (σ : ℝ), 0 < σ → ∃ ρ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ρ ∧ (∀ x, 0 ≤ ρ x) ∧ Function.support ρ ⊆ ball 0 σ ∧ ∫ x, ρ x = 1 := by
  intro n σ hσ
  -- Step 1: a smooth bump `φ` at `0` with `rIn = σ/2`, `rOut = σ` (inner-product-space instance).
  obtain ⟨φ, hφ⟩ : ∃ φ : ContDiffBump (0 : Rn n), φ.rOut = σ :=
    ⟨⟨σ / 2, σ, half_pos hσ, half_lt_self hσ⟩, rfl⟩
  -- Step 2: `∫ φ > 0`, as `φ ≥ 0` is integrable with support the nonempty open ball `B(0, σ)`.
  have hpos : 0 < ∫ x, φ x := by
    refine (integral_pos_iff_support_of_nonneg φ.nonneg'
      (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport)).2 ?_
    rw [φ.support_eq]
    exact measure_ball_pos _ _ φ.rOut_pos
  -- Steps 3–6: `ρ = φ / ∫ φ` is smooth, nonnegative, supported in `B(0, σ)`, of unit mass.
  refine ⟨fun x ↦ φ x / ∫ y, φ y, φ.contDiff.div_const _, fun x ↦ div_nonneg φ.nonneg hpos.le,
    ?_, ?_⟩
  · rw [Function.support_div, φ.support_eq, Function.support_const hpos.ne', inter_univ, hφ]
  · rw [integral_div, div_self hpos.ne']
/-- **Smoothed absolute value.** For `w ∈ C¹(ℝⁿ)` and `η > 0`, `F = √(w² + η²) - η` is `C¹`,
satisfies `‖DF(x)‖ ≤ ‖Dw(x)‖` and is uniformly `η`-close to `|w|`. With `ψ(t) = √(t² + η²) - η`
and `F = ψ ∘ w`: `|t| ≤ √(t² + η²) ≤ |t| + η` gives the closeness, and the chain rule gives
`DF(x) = (w(x) / √(w(x)² + η²)) • Dw(x)` with a coefficient of absolute value at most `1`. -/
theorem Submission.bv_abs_variation_smoothed_abs : ∀ (n : ℕ) (w : Rn n → ℝ) (η : ℝ), 0 < η → ContDiff ℝ 1 w → ContDiff ℝ 1 (fun x ↦ Real.sqrt (w x ^ 2 + η ^ 2) - η) ∧ (∀ x, ‖fderiv ℝ (fun x ↦ Real.sqrt (w x ^ 2 + η ^ 2) - η) x‖ ≤ ‖fderiv ℝ w x‖) ∧ ∀ x, abs (Real.sqrt (w x ^ 2 + η ^ 2) - η - |w x|) ≤ η := by
  intro n w η hη hw
  -- Step 1: the radicand `t² + η²` is positive.
  have hpos : ∀ t : ℝ, 0 < t ^ 2 + η ^ 2 := fun t ↦ by positivity
  -- Step 2: `|t| = √(t²) ≤ √(t² + η²)`.
  have hlow : ∀ t : ℝ, |t| ≤ Real.sqrt (t ^ 2 + η ^ 2) := fun t ↦ by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg η))
  -- Step 3: `√(t² + η²) ≤ √((|t| + η)²) = |t| + η`.
  have hup : ∀ t : ℝ, Real.sqrt (t ^ 2 + η ^ 2) ≤ |t| + η := fun t ↦ by
    rw [← Real.sqrt_sq (add_nonneg (abs_nonneg t) hη.le)]
    exact Real.sqrt_le_sqrt (by nlinarith [abs_nonneg t, sq_abs t])
  refine ⟨?_, fun x ↦ ?_, fun x ↦ ?_⟩
  -- Step 5: the radicand is `C¹` and never vanishes, so `F` is `C¹`.
  · have h1 : ContDiff ℝ 1 (fun x ↦ w x ^ 2 + η ^ 2) := (hw.pow 2).add contDiff_const
    exact (h1.sqrt fun x ↦ (hpos (w x)).ne').sub contDiff_const
  -- Step 6: `ψ'(t₀) = 2t₀ / (2√(t₀² + η²))` at `t₀ = w(x)`; the chain rule gives
  -- `DF(x) = ψ'(t₀) • Dw(x)`, and `|ψ'(t₀)| ≤ 1` by Step 2.
  · have hψ : HasDerivAt (fun t : ℝ ↦ Real.sqrt (t ^ 2 + η ^ 2) - η)
        (2 * w x / (2 * Real.sqrt (w x ^ 2 + η ^ 2))) (w x) := by
      have h1 : HasDerivAt (fun t : ℝ ↦ t ^ 2 + η ^ 2) (2 * w x) (w x) := by
        simpa using (hasDerivAt_pow 2 (w x)).add_const (η ^ 2)
      exact (h1.sqrt (hpos (w x)).ne').sub_const η
    have hwx : HasFDerivAt w (fderiv ℝ w x) x := (hw.differentiable one_ne_zero x).hasFDerivAt
    have hF : HasFDerivAt (fun x ↦ Real.sqrt (w x ^ 2 + η ^ 2) - η)
        ((2 * w x / (2 * Real.sqrt (w x ^ 2 + η ^ 2))) • fderiv ℝ w x) x :=
      hψ.comp_hasFDerivAt x hwx
    have h2s : 0 < 2 * Real.sqrt (w x ^ 2 + η ^ 2) := by
      have := Real.sqrt_pos.2 (hpos (w x))
      positivity
    have hc : |2 * w x / (2 * Real.sqrt (w x ^ 2 + η ^ 2))| ≤ 1 := by
      rw [abs_div, abs_of_pos h2s, div_le_one h2s, abs_mul, abs_two]
      linarith [hlow (w x)]
    rw [hF.fderiv, norm_smul, Real.norm_eq_abs]
    calc |2 * w x / (2 * Real.sqrt (w x ^ 2 + η ^ 2))| * ‖fderiv ℝ w x‖
        ≤ 1 * ‖fderiv ℝ w x‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
      _ = ‖fderiv ℝ w x‖ := one_mul _
  -- Step 4: `-η ≤ F(x) - |w(x)| ≤ 0 ≤ η`, by Steps 2 and 3.
  · rw [abs_le]
    constructor
    · linarith [hlow (w x)]
    · linarith [hup (w x)]
/-- **Simon Ch. 2, proof of Lemma 2.5: transposing a mollification.** For `F ∈ L¹(ℝⁿ)` and
continuous, compactly supported `ρ`, `h`, with `ρ̌(t) = ρ(-t)`: `∫ (ρ * F) h = ∫ F (ρ̌ * h)` (the
step `∫ (φ_σ * u) div g = ∫ u (φ_σ * div g)`, for a kernel that need not be even). Both
convolutions are rewritten in the symmetric form `(a * b)(x) = ∫ a(x - t) b(t) dt` (translation and
reflection invariance of `Lⁿ`); then one application of Fubini to `(x, s) ↦ ρ(x - s) F(s) h(x)`
gives the identity. -/
theorem Submission.bv_integral_convolution_mul_reflect : ∀ (n : ℕ) (F ρ h : Rn n → ℝ), Integrable F volume → Continuous ρ → HasCompactSupport ρ → Continuous h → HasCompactSupport h → ∫ x, convolution ρ F (ContinuousLinearMap.lsmul ℝ ℝ) volume x * h x = ∫ x, F x * convolution (fun t ↦ ρ (-t)) h (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
  intro n F ρ h hF hρ hρc hh hhc
  -- Step 1: `ρ` is integrable and `h` is bounded, `|h| ≤ C`.
  have hρi : Integrable ρ volume := hρ.integrable_of_hasCompactSupport hρc
  obtain ⟨C, hC⟩ := hh.bounded_above_of_compact_support hhc
  -- Step 2: `(x, s) ↦ ρ(x - s) F(s) h(x)` is integrable on `ℝⁿ × ℝⁿ`: the convolution integrand
  -- `F(s) ρ(x - s)` is integrable and `h(x)` is continuous and bounded.
  have hG : Integrable (fun p : Rn n × Rn n ↦ ρ (p.1 - p.2) * F p.2 * h p.1)
      (volume.prod volume) := by
    refine ((hF.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hρi).mul_bdd
      (hh.comp continuous_fst).aestronglyMeasurable
      (Eventually.of_forall fun p ↦ hC p.1)).congr (Eventually.of_forall fun p ↦ ?_)
    simp only [Function.comp_apply, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    ring
  -- Step 3: `(ρ * F)(x) = ∫ ρ(x - s) F(s) ds` and `(ρ̌ * h)(s) = ∫ ρ(x - s) h(x) dx`; swap the
  -- order of integration once.
  calc ∫ x, convolution ρ F (ContinuousLinearMap.lsmul ℝ ℝ) volume x * h x
      = ∫ x, ∫ s, ρ (x - s) * F s * h x := by
        refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
        simp only [convolution_lsmul_swap, smul_eq_mul, ← integral_mul_const]
    _ = ∫ s, ∫ x, ρ (x - s) * F s * h x := integral_integral_swap hG
    _ = ∫ s, F s * convolution (fun t ↦ ρ (-t)) h (ContinuousLinearMap.lsmul ℝ ℝ) volume s := by
        refine integral_congr_ae (Eventually.of_forall fun s ↦ ?_)
        simp only [convolution_lsmul_swap, smul_eq_mul, neg_sub, ← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
        ring
/-- **Simon Ch. 2, proof of Lemma 2.5: divergence commutes with convolution.** For a locally
integrable kernel `κ` on `ℝⁿ` and a `C¹` vector field `g` with compact support,
`div(κ * g) = κ * div g` pointwise (the step `φ_σ * div g = div(φ_σ * g)`). By
`HasCompactSupport.hasFDerivAt_convolution_right`, `D(κ * g)(x) = ∫ κ(t) • Dg(x - t) dt`, whose
integrand is integrable because `Dg` is continuous with compact support. The trace is a continuous
linear map on `ℝⁿ →L[ℝ] ℝⁿ`, so it commutes with the integral, and
`trace (κ(t) • Dg(x - t)) = κ(t) div g(x - t)`. -/
theorem Submission.bv_euclideanDivergence_convolution : ∀ (n : ℕ) (κ : Rn n → ℝ) (g : Rn n → Rn n), LocallyIntegrable κ volume → ContDiff ℝ 1 g → HasCompactSupport g → ∀ x, Chapter02.euclideanDivergence (convolution κ g (ContinuousLinearMap.lsmul ℝ ℝ) volume) x = convolution κ (Chapter02.euclideanDivergence g) (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
  intro n κ g hκ hg hgc x
  -- Step 1: `Dg = fderiv ℝ g` is continuous with compact support.
  have hDg : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  have hDgc : HasCompactSupport (fderiv ℝ g) := hgc.fderiv ℝ
  -- Step 2: `D(κ * g)(x) = ∫ L' (κ t) (Dg (x - t)) dt` with `L' = (lsmul ℝ ℝ).precompR ℝⁿ`.
  have hD := (hgc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hκ hg x).fderiv
  -- Step 3: the integrand `t ↦ L' (κ t) (Dg (x - t))` is integrable.
  have hI := (hDgc.convolutionExists_right
    ((ContinuousLinearMap.lsmul ℝ ℝ).precompR (Rn n)) hκ hDg x).integrable
  -- Step 4: the trace, as a continuous linear map on `ℝⁿ →L[ℝ] ℝⁿ`, commutes with the integral.
  let T : (Rn n →L[ℝ] Rn n) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    (LinearMap.trace ℝ (Rn n) ∘ₗ ContinuousLinearMap.coeLM ℝ)
  have hT : ∀ A : Rn n →L[ℝ] Rn n, T A = LinearMap.trace ℝ (Rn n) A := fun A ↦ rfl
  calc Chapter02.euclideanDivergence (convolution κ g (ContinuousLinearMap.lsmul ℝ ℝ) volume) x
      = T (∫ t, (ContinuousLinearMap.lsmul ℝ ℝ).precompR (Rn n) (κ t) (fderiv ℝ g (x - t))) := by
        rw [hT, Chapter02.euclideanDivergence, hD, convolution_def]
    _ = ∫ t, T ((ContinuousLinearMap.lsmul ℝ ℝ).precompR (Rn n) (κ t) (fderiv ℝ g (x - t))) :=
        (T.integral_comp_comm hI).symm
    _ = convolution κ (Chapter02.euclideanDivergence g) (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
        -- Step 5: `L' (κ t) A = κ t • A`, so `trace (L' (κ t) (Dg (x - t))) = κ t * div g (x - t)`.
        rw [convolution_def]
        refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
        have hc : ((ContinuousLinearMap.lsmul ℝ ℝ (κ t)).comp (fderiv ℝ g (x - t)) :
            Rn n →L[ℝ] Rn n) = κ t • fderiv ℝ g (x - t) :=
          ContinuousLinearMap.ext fun v ↦ by
            simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.lsmul_apply, smul_apply]
        simp only [ContinuousLinearMap.precompR_apply, ContinuousLinearMap.compL_apply, hc, hT,
          ContinuousLinearMap.toLinearMap_smul, map_smul, smul_eq_mul,
          Chapter02.euclideanDivergence, ContinuousLinearMap.lsmul_apply]

/-- **Simon Ch. 2, proof of Lemma 2.5: the duality bound for a mollification.** Let `W ⊂ ℝⁿ` be
open, `u ∈ L¹(W)`, `ρ ≥ 0` continuous with `ρ = 0` off the open ball `{|x| < σ}` and `∫ ρ = 1`, and
`g` a `C¹` field with compact support, `|g| ≤ 1` and `B_σ(y) ⊂ W` for `y ∈ spt g`. Then
`w = ρ * (1_W u)` satisfies `∫ w div g ≤ |Du|(W)` (Simon's `∫ g · ∇u_σ = -∫ u div(φ_σ * g)`).
With `ρ̌(t) = ρ(-t)` and `G = ρ̌ * g`, transposition and `div G = ρ̌ * div g` give
`∫ w div g = ∫_W u div G`. `G` is `C¹`, hence Lipschitz, `spt G ⊂ B_σ(0) + spt g ⊂ W` is compact and
`|G| ≤ ∫ ρ̌ = 1`, so `G` is admissible in the supremum defining `|Du|(W)`. -/
theorem Submission.bv_mollifier_integral_mul_div_le : ∀ (n : ℕ) (W : Set (Rn n)) (u ρ : Rn n → ℝ) (σ : ℝ) (g : Rn n → Rn n), IsOpen W → IntegrableOn u W volume → Continuous ρ → (∀ x, 0 ≤ ρ x) → Function.support ρ ⊆ ball 0 σ → ∫ x, ρ x = 1 → ContDiff ℝ 1 g → HasCompactSupport g → (∀ x, ‖g x‖ ≤ 1) → (∀ y ∈ tsupport g, closedBall y σ ⊆ W) → ENNReal.ofReal (∫ x, convolution ρ (W.indicator u) (ContinuousLinearMap.lsmul ℝ ℝ) volume x * Chapter02.euclideanDivergence g x) ≤ Chapter02.bvVariationOn u W := by
  intro n W u ρ σ g hW hu hρ hρ0 hρs hρ1 hg hgc hg1 hgW
  -- Step 1: `F = 1_W u` is integrable, and `ρ` vanishes off the compact ball `closedBall 0 σ`.
  have hF : Integrable (W.indicator u) volume := (integrable_indicator_iff hW.measurableSet).2 hu
  have hρc : HasCompactSupport ρ := HasCompactSupport.intro (isCompact_closedBall 0 σ)
    fun x hx ↦ Function.notMem_support.1 fun h ↦ hx (ball_subset_closedBall (hρs h))
  -- Step 2: the reflected kernel `ρ̌(t) = ρ(-t)` is supported in `closedBall 0 σ`, is integrable,
  -- and `∫ ρ̌ = ∫ ρ = 1` by reflection invariance of `Lⁿ`.
  have hρrs : Function.support (fun t ↦ ρ (-t)) ⊆ closedBall (0 : Rn n) σ := fun t ht ↦ by
    have h1 : -t ∈ ball (0 : Rn n) σ := hρs (Function.mem_support.2 (Function.mem_support.1 ht))
    rw [mem_ball_zero_iff, norm_neg] at h1
    exact mem_closedBall_zero_iff.2 h1.le
  have hρri : Integrable (fun t ↦ ρ (-t)) volume :=
    (hρ.comp continuous_neg).integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_closedBall 0 σ)
        fun x hx ↦ Function.notMem_support.1 fun h ↦ hx (hρrs h))
  have hρr1 : ∫ t, ρ (-t) = 1 := (integral_neg_eq_self ρ volume).trans hρ1
  -- Step 3: `div g = trace ∘ Dg` is continuous, with support in the compact `tsupport g`.
  have hh : Continuous (Chapter02.euclideanDivergence g) := by
    let T : (Rn n →L[ℝ] Rn n) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
      (LinearMap.trace ℝ (Rn n) ∘ₗ ContinuousLinearMap.coeLM ℝ)
    exact T.continuous.comp (hg.continuous_fderiv one_ne_zero)
  have hhc : HasCompactSupport (Chapter02.euclideanDivergence g) :=
    hgc.mono' (Chapter02.support_euclideanDivergence_subset g)
  -- Step 4: the comparison field `G = ρ̌ * g` has `div G = ρ̌ * div g`.
  obtain ⟨G, hG⟩ : ∃ G, G = convolution (fun t ↦ ρ (-t)) g (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    ⟨_, rfl⟩
  have hdivG : ∀ x, Chapter02.euclideanDivergence G x =
      convolution (fun t ↦ ρ (-t)) (Chapter02.euclideanDivergence g)
        (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
    rw [hG]
    exact Submission.bv_euclideanDivergence_convolution n _ g hρri.locallyIntegrable hg hgc
  -- Step 5: transposing the mollification, `∫ w div g = ∫ F (ρ̌ * div g) = ∫_W u div G`.
  have hint : ∫ x, convolution ρ (W.indicator u) (ContinuousLinearMap.lsmul ℝ ℝ) volume x *
      Chapter02.euclideanDivergence g x = ∫ x in W, u x * Chapter02.euclideanDivergence G x := by
    rw [Submission.bv_integral_convolution_mul_reflect n (W.indicator u) ρ _ hF hρ hρc hh hhc,
      ← integral_indicator hW.measurableSet]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    by_cases hx : x ∈ W
    · simp only [Set.indicator_of_mem hx, hdivG]
    · simp only [Set.indicator_of_notMem hx, zero_mul]
  -- Step 6: `G` is `C¹`.
  have hGd : ContDiff ℝ 1 G := by
    rw [hG]
    exact hgc.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hρri.locallyIntegrable hg
  -- Step 7: `tsupport G ⊆ S := closedBall 0 σ + tsupport g ⊆ W`, and `S` is compact.
  obtain ⟨S, hS, hGS, hSW⟩ : ∃ S : Set (Rn n), IsCompact S ∧ tsupport G ⊆ S ∧ S ⊆ W := by
    open Pointwise in
    refine ⟨closedBall 0 σ + tsupport g, (isCompact_closedBall 0 σ).add hgc, ?_, ?_⟩
    · rw [hG]
      exact closure_minimal ((support_convolution_subset _).trans
        (add_subset_add hρrs (subset_tsupport g))) ((isCompact_closedBall 0 σ).add hgc).isClosed
    · rintro _ ⟨t, ht, y, hy, rfl⟩
      refine hgW y hy ?_
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_right]
      exact mem_closedBall_zero_iff.1 ht
  have hGc : HasCompactSupport G := hS.of_isClosed_subset (isClosed_tsupport G) hGS
  -- Step 8: `‖G s‖ ≤ ∫ ρ̌(t) ‖g(s - t)‖ dt ≤ ∫ ρ̌ = 1`.
  have hGle : ∀ s, ‖G s‖ ≤ 1 := by
    intro s
    rw [hG, convolution_def, ← hρr1]
    refine norm_integral_le_of_norm_le hρri (Eventually.of_forall fun t ↦ ?_)
    rw [ContinuousLinearMap.lsmul_apply, norm_smul, Real.norm_of_nonneg (hρ0 _)]
    exact mul_le_of_le_one_right (hρ0 _) (hg1 _)
  -- Step 9: `G` is an admissible field: Lipschitz (`C¹` with compact support), supported in `W`,
  -- with supremum norm at most one.
  let Gc : CompactlySupportedContinuousMap (Rn n) (Rn n) := ⟨⟨G, hGd.continuous⟩, hGc⟩
  have hLip : Chapter02.IsLipschitzTestField Gc :=
    ContDiff.lipschitzWith_of_hasCompactSupport hGc hGd one_ne_zero
  have hsupp : tsupport Gc ⊆ W := hGS.trans hSW
  have hnorm : Chapter02.compactlySupportedSupNorm Gc ≤ 1 :=
    csSup_le (range_nonempty _) (by rintro _ ⟨x, rfl⟩; exact hGle x)
  -- Step 10: the supremum defining `|Du|(W)` dominates the pairing with `G`.
  rw [hint]
  exact Chapter02.ofReal_integral_le_bvVariationOn u W Gc hLip hsupp hnorm
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
/-- **Simon Ch. 2, proof of Lemma 2.5, passage from compact subsets to an open set.** If `O ⊆ ℝⁿ`
is open, `f ≥ 0` is measurable and `∫⁻_L f dLⁿ ≤ M` for every compact `L ⊆ O`, then
`∫⁻_O f dLⁿ ≤ M`. A closed exhaustion `F l` of `O` cut down by the balls `B_l(0)` gives compact
sets `L l = F l ∩ B_l(0)` increasing to `O`. Then `1_{L l} f` increase to `1_O f`, and monotone
convergence gives `∫⁻_O f = sup_l ∫⁻_{L l} f ≤ M`. -/
theorem Submission.bv_lintegral_open_le_of_compact : ∀ (n : ℕ) (O : Set (Rn n)) (f : Rn n → ℝ≥0∞) (M : ℝ≥0∞), IsOpen O → Measurable f → (∀ L, IsCompact L → L ⊆ O → ∫⁻ x in L, f x ≤ M) → ∫⁻ x in O, f x ≤ M := by
  intro n O f M hO hf hM
  -- A closed exhaustion `F l` of `O`, cut down to the compact sets `L l = F l ∩ B_l(0)`.
  obtain ⟨F, hFc, hFO, hFU, hFm⟩ := hO.exists_iUnion_isClosed
  let L : ℕ → Set (Rn n) := fun l ↦ F l ∩ closedBall 0 l
  have hLc (l : ℕ) : IsCompact (L l) := (isCompact_closedBall 0 l).inter_left (hFc l)
  have hLO (l : ℕ) : L l ⊆ O := inter_subset_left.trans (hFO l)
  have hLm : Monotone L := fun i j hij ↦
    inter_subset_inter (hFm hij) (closedBall_subset_closedBall (Nat.cast_le.2 hij))
  have hLU : ⋃ l, L l = O := by
    refine Subset.antisymm (iUnion_subset hLO) fun x hx ↦ ?_
    rw [← hFU] at hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    obtain ⟨j, hj⟩ := exists_nat_ge ‖x‖
    exact mem_iUnion.2 ⟨max i j, hFm (le_max_left i j) hi,
      mem_closedBall_zero_iff.2 (hj.trans (Nat.cast_le.2 (le_max_right i j)))⟩
  -- The measurable functions `1_{L l} f` increase to `1_O f`; apply monotone convergence.
  have hLmeas (l : ℕ) : MeasurableSet (L l) := (hLc l).isClosed.measurableSet
  calc ∫⁻ x in O, f x
      = ∫⁻ x, ⨆ l, (L l).indicator f x := by
        rw [← lintegral_indicator hO.measurableSet, ← hLU]
        simp_rw [indicator_iUnion_apply bot_eq_zero]
    _ = ⨆ l, ∫⁻ x, (L l).indicator f x :=
        lintegral_iSup (fun l ↦ hf.indicator (hLmeas l))
          fun i j hij ↦ indicator_le_indicator_of_subset (hLm hij) fun _ ↦ zero_le
    _ = ⨆ l, ∫⁻ x in L l, f x := iSup_congr fun l ↦ lintegral_indicator (hLmeas l) f
    _ ≤ M := iSup_le fun l ↦ hM (L l) (hLc l) (hLO l)
/-- **Integration by parts against a compactly supported Lipschitz vector field.** For `F ∈ C¹(ℝⁿ)`
and a `K`-Lipschitz `g : ℝⁿ → ℝⁿ` with compact support, `∫ F div g = -∫ DF(x)[g(x)] dx`, where
`div g = trace Dg` and `Dg = fderiv ℝ g` (which is `0` where `g` is not differentiable). This is the
Fubini / absolute-continuity-on-lines step of Simon's proof of Rademacher's theorem (Ch. 2, 1.4).
`F` is replaced by `χF` for a smooth bump `χ` equal to `1` near `spt g`; Mathlib's
`LipschitzWith.integral_lineDeriv_mul_eq` is applied to each coordinate `⟨eᵢ, g⟩`; the line
derivatives are identified with `fderiv` (everywhere for `χF`, a.e. for `g` by Rademacher's
theorem); and the identities are summed over the standard orthonormal basis `(eᵢ)`. -/
theorem Submission.bv_lipschitz_integration_by_parts : ∀ (n : ℕ) (F : Rn n → ℝ) (g : Rn n → Rn n) (K : ℝ≥0), ContDiff ℝ 1 F → LipschitzWith K g → HasCompactSupport g → ∫ x, F x * Chapter02.euclideanDivergence g x = -∫ x, fderiv ℝ F x (g x) := by
  intro n F g K hF hg hgc
  -- Step 3 (cut-off): `G = χF`, with `χ` a smooth bump equal to `1` on a ball `U ⊇ tsupport g`,
  -- is `C¹` with compact support and equals `F` on the open set `U`.
  obtain ⟨G, hG, hGc, U, hU, hSU, hEq⟩ : ∃ G : Rn n → ℝ, ContDiff ℝ 1 G ∧ HasCompactSupport G ∧
      ∃ U : Set (Rn n), IsOpen U ∧ tsupport g ⊆ U ∧ EqOn G F U := by
    obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.subset_ball (0 : Rn n)
    let χ : ContDiffBump (0 : Rn n) :=
      ⟨max R 1, max R 1 + 1, lt_of_lt_of_le one_pos (le_max_right _ _), lt_add_one _⟩
    refine ⟨fun x ↦ χ x * F x, χ.contDiff.mul hF, χ.hasCompactSupport.mul_right,
      ball 0 (max R 1), isOpen_ball, hR.trans (ball_subset_ball (le_max_left _ _)), fun x hx ↦ ?_⟩
    simp [χ.one_of_mem_closedBall (ball_subset_closedBall hx)]
  -- `G` is Lipschitz (`C¹` with compact support) and differentiable everywhere.
  obtain ⟨L, hL⟩ := hG.lipschitzWith_of_hasCompactSupport hGc one_ne_zero
  have hGd : Differentiable ℝ G := hG.differentiable one_ne_zero
  -- The coordinates `gᵢ = ⟨eᵢ, g⟩` in the standard orthonormal basis `(eᵢ)` are `K`-Lipschitz
  -- with compact support.
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let gi : Fin n → Rn n → ℝ := fun i x ↦ inner ℝ (b i) (g x)
  have hgi_lip : ∀ i, LipschitzWith K (gi i) := fun i ↦ by
    have h1 : LipschitzWith 1 (fun y : Rn n ↦ inner ℝ (b i) y) :=
      LipschitzWith.of_dist_le_mul fun y z ↦ by
        rw [dist_eq_norm, dist_eq_norm, ← inner_sub_right]
        simpa [b.norm_eq_one] using norm_inner_le_norm (𝕜 := ℝ) (b i) (y - z)
    have h2 := h1.comp hg
    rw [one_mul] at h2
    exact h2
  have hgi_c : ∀ i, HasCompactSupport (gi i) := fun i ↦
    hgc.comp_left (g := fun y : Rn n ↦ inner ℝ (b i) y) (inner_zero_right (b i))
  -- Steps 4–5: Lipschitz integration by parts for `G` and `gᵢ` in the direction `eᵢ`. Here
  -- `lineDeriv G x eᵢ = DG(x)[eᵢ]` everywhere, and `lineDeriv gᵢ x (-eᵢ) = -⟨eᵢ, Dg(x)[eᵢ]⟩` at
  -- every point where `g` is differentiable, i.e. a.e. by Rademacher's theorem.
  have hcoord : ∀ i, ∫ x, fderiv ℝ G x (b i) * gi i x
      = -∫ x, inner ℝ (b i) (fderiv ℝ g x (b i)) * G x := fun i ↦ by
    calc ∫ x, fderiv ℝ G x (b i) * gi i x
        = ∫ x, lineDeriv ℝ G x (b i) * gi i x := by
          congr 1
          funext x
          rw [(hGd x).lineDeriv_eq_fderiv]
      _ = ∫ x, lineDeriv ℝ (gi i) x (-b i) * G x :=
          hL.integral_lineDeriv_mul_eq (hgi_lip i) (hgi_c i) (b i)
      _ = ∫ x, -(inner ℝ (b i) (fderiv ℝ g x (b i)) * G x) := by
          refine integral_congr_ae ?_
          filter_upwards [hg.ae_differentiableAt (μ := volume)] with x hx
          have hd : HasFDerivAt (gi i) ((innerSL ℝ (b i)).comp (fderiv ℝ g x)) x :=
            (innerSL ℝ (b i)).hasFDerivAt.comp x hx.hasFDerivAt
          rw [hd.differentiableAt.lineDeriv_eq_fderiv, hd.fderiv]
          simp
      _ = -∫ x, inner ℝ (b i) (fderiv ℝ g x (b i)) * G x := integral_neg _
  -- The summands are integrable: the first is continuous with compact support; the second is
  -- measurable, bounded by `K` (as `‖Dg(x)‖ ≤ K`) and multiplied by the integrable `G`.
  have hint1 : ∀ i, Integrable (fun x ↦ fderiv ℝ G x (b i) * gi i x) := fun i ↦
    Continuous.integrable_of_hasCompactSupport
      (((hG.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul
        (continuous_const.inner hg.continuous)) (hgi_c i).mul_left
  have hint2 : ∀ i, Integrable (fun x ↦ inner ℝ (b i) (fderiv ℝ g x (b i)) * G x) := fun i ↦ by
    refine (hG.continuous.integrable_of_hasCompactSupport hGc).bdd_mul (c := K)
      (measurable_const.inner (measurable_fderiv_apply_const ℝ g (b i))).aestronglyMeasurable
      (Eventually.of_forall fun x ↦ ?_)
    calc ‖inner ℝ (b i) (fderiv ℝ g x (b i))‖ ≤ ‖b i‖ * ‖fderiv ℝ g x (b i)‖ :=
          norm_inner_le_norm _ _
      _ ≤ ‖b i‖ * (‖fderiv ℝ g x‖ * ‖b i‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ K := by
          simpa only [b.norm_eq_one, one_mul, mul_one] using
            norm_fderiv_le_of_lipschitz ℝ hg (x₀ := x)
  -- Step 6 (summation): `Σᵢ DG(x)[eᵢ] gᵢ(x) = DG(x)[g(x)]` and `Σᵢ ⟨eᵢ, Dg(x) eᵢ⟩ = div g(x)`.
  have hsum1 : ∀ x, fderiv ℝ G x (g x) = ∑ i, fderiv ℝ G x (b i) * gi i x := fun x ↦ by
    conv_lhs => rw [← b.sum_repr' (g x)]
    simp [gi, map_sum, map_smul, smul_eq_mul, mul_comm]
  have hsum2 : ∀ x, G x * Chapter02.euclideanDivergence g x
      = ∑ i, inner ℝ (b i) (fderiv ℝ g x (b i)) * G x := fun x ↦ by
    rw [Chapter02.euclideanDivergence_eq_sum_inner b g x, Finset.mul_sum]
    simp [mul_comm]
  have hGibp : ∫ x, G x * Chapter02.euclideanDivergence g x = -∫ x, fderiv ℝ G x (g x) := by
    simp_rw [hsum1, hsum2]
    rw [integral_finsetSum _ fun i _ ↦ hint2 i, integral_finsetSum _ fun i _ ↦ hint1 i]
    simp_rw [hcoord, Finset.sum_neg_distrib, neg_neg]
  -- Step 7: replacing `G` by `F` changes neither integrand. Off `tsupport g`, `div g` and `g`
  -- vanish; on it, `G = F` and `DG = DF`, as `G = F` on the open set `U ⊇ tsupport g`.
  have h1 : ∫ x, F x * Chapter02.euclideanDivergence g x
      = ∫ x, G x * Chapter02.euclideanDivergence g x := by
    congr 1
    funext x
    by_cases hx : x ∈ tsupport g
    · rw [hEq (hSU hx)]
    · have h0 : Chapter02.euclideanDivergence g x = 0 := by
        by_contra h
        exact hx (Chapter02.support_euclideanDivergence_subset g h)
      simp [h0]
  have h2 : ∫ x, fderiv ℝ F x (g x) = ∫ x, fderiv ℝ G x (g x) := by
    congr 1
    funext x
    by_cases hx : x ∈ tsupport g
    · rw [(Filter.eventuallyEq_of_mem (hU.mem_nhds (hSU hx)) hEq).fderiv_eq]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  rw [h1, h2, hGibp]
/-- **Simon Ch. 2, Lemma 2.5 (`L¹` part), convergence of mollifiers.** If `F ∈ L¹(ℝⁿ)` and the
kernels `ρ j` are continuous, nonnegative, of integral `1` and supported in the open ball
`ball 0 (σ j)` with `σ j → 0`, then `ρ j * F → F` in `L¹`. The `L¹` contraction
`‖ρ j * G‖₁ ≤ ‖G‖₁` (Tonelli and translation invariance) and the density of compactly supported
continuous `g` in `L¹` (inner and outer regularity, Urysohn, `MemLp.induction_dense`) reduce it
to such `g`, for which `ρ j * g → g` uniformly (`dist_convolution_le`) and both vanish off a
fixed ball. -/
theorem Submission.bv_mollifier_tendsto_L1 : ∀ (n : ℕ) (F : Rn n → ℝ) (ρ : ℕ → Rn n → ℝ) (σ : ℕ → ℝ), Integrable F volume → (∀ j, Continuous (ρ j)) → (∀ j x, 0 ≤ ρ j x) → (∀ j, Function.support (ρ j) ⊆ ball 0 (σ j)) → (∀ j, ∫ x, ρ j x = 1) → Tendsto σ atTop (𝓝 0) → Tendsto (fun j ↦ ∫⁻ x, ‖convolution (ρ j) F (ContinuousLinearMap.lsmul ℝ ℝ) volume x - F x‖ₑ) atTop (𝓝 0) := by
  intro n F ρ σ hF hρc hρn hρs hρi hσ
  -- Step 1 (L¹ contraction): `∫⁻ |ρ_j * G| ≤ ∫⁻ |G|` for integrable `G`, by Tonelli and
  -- translation invariance, since `∫⁻ |ρ_j| = ∫ ρ_j = 1`.
  have hcontr : ∀ j (G : Rn n → ℝ), Integrable G volume →
      ∫⁻ x, ‖convolution (ρ j) G (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ ≤ ∫⁻ x, ‖G x‖ₑ := by
    intro j G hG
    have hρ : Integrable (ρ j) volume := integrable_of_integral_eq_one (hρi j)
    have hmeas : AEStronglyMeasurable
        (fun p : Rn n × Rn n ↦ ContinuousLinearMap.lsmul ℝ ℝ (ρ j p.2) (G (p.1 - p.2)))
        (volume.prod volume) :=
      hρ.aestronglyMeasurable.convolution_integrand _ hG.aestronglyMeasurable
    have hρ1 : ∫⁻ t, ‖ρ j t‖ₑ = 1 := by
      have h1 := ofReal_integral_eq_lintegral_ofReal hρ (Eventually.of_forall (hρn j))
      rw [hρi j, ENNReal.ofReal_one] at h1
      rw [h1]
      exact lintegral_congr fun t ↦ Real.enorm_eq_ofReal (hρn j t)
    calc ∫⁻ x, ‖convolution (ρ j) G (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ
        ≤ ∫⁻ x, ∫⁻ t, ‖ContinuousLinearMap.lsmul ℝ ℝ (ρ j t) (G (x - t))‖ₑ :=
          lintegral_mono fun x ↦ enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ t, ∫⁻ x, ‖ContinuousLinearMap.lsmul ℝ ℝ (ρ j t) (G (x - t))‖ₑ :=
          lintegral_lintegral_swap hmeas.enorm
      _ = ∫⁻ t, ‖ρ j t‖ₑ * ∫⁻ x, ‖G x‖ₑ := by
          refine lintegral_congr fun t ↦ ?_
          simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, enorm_mul]
          rw [lintegral_const_mul' _ _ enorm_ne_top]
          congr 1
          exact lintegral_sub_right_eq_self (fun x ↦ ‖G x‖ₑ) t
      _ = (∫⁻ t, ‖ρ j t‖ₑ) * ∫⁻ x, ‖G x‖ₑ := lintegral_mul_const'' _ hρ.aestronglyMeasurable.enorm
      _ = ∫⁻ x, ‖G x‖ₑ := by rw [hρ1, one_mul]
  -- Step 2 (the `C_c` case): for `g` continuous with compact support, `ρ_j * g → g` uniformly
  -- (`dist_convolution_le` and uniform continuity) and both vanish off a fixed ball `S`.
  have hcc : ∀ g : Rn n → ℝ, Continuous g → HasCompactSupport g →
      Tendsto (fun j ↦ ∫⁻ x, ‖convolution (ρ j) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x - g x‖ₑ)
        atTop (𝓝 0) := by
    intro g hgc hgs
    obtain ⟨R, hR⟩ := hgs.isCompact.isBounded.subset_closedBall (0 : Rn n)
    have hgR : ∀ y, R < ‖y‖ → g y = 0 := by
      intro y hy
      refine image_eq_zero_of_notMem_tsupport fun hys ↦ ?_
      have h := hR hys
      rw [mem_closedBall, dist_zero_right] at h
      linarith
    set S : Set (Rn n) := closedBall (0 : Rn n) (R + 1) with hSdef
    have hSm : MeasurableSet S := measurableSet_closedBall
    have hSf : volume S ≠ ∞ := measure_closedBall_lt_top.ne
    have huc : UniformContinuous g := hgs.uniformContinuous_of_continuous hgc
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    obtain ⟨ε₀, hε₀, hε₀le⟩ : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ENNReal.ofReal ε₀ ≤ ε := by
      rcases eq_or_ne ε ∞ with h | h
      · exact ⟨1, one_pos, h ▸ le_top⟩
      · exact ⟨ε.toReal, ENNReal.toReal_pos hε.ne' h, (ENNReal.ofReal_toReal h).le⟩
    set m : ℝ := (volume S).toReal with hm
    have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
    set ε' : ℝ := ε₀ / (m + 1) with hε'eq
    have hε' : 0 < ε' := div_pos hε₀ (by linarith)
    obtain ⟨δ, hδ, hδg⟩ := Metric.uniformContinuous_iff.1 huc ε' hε'
    have hr : (0 : ℝ) < min δ 1 := lt_min hδ one_pos
    filter_upwards [hσ.eventually (Iio_mem_nhds hr)] with j hj
    have hjδ : σ j < δ := hj.trans_le (min_le_left _ _)
    have hj1 : σ j < 1 := hj.trans_le (min_le_right _ _)
    have hpt : ∀ x, ‖convolution (ρ j) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x - g x‖ₑ ≤
        S.indicator (fun _ ↦ ENNReal.ofReal ε') x := by
      intro x
      by_cases hx : x ∈ S
      · rw [indicator_of_mem hx]
        have hd := dist_convolution_le (μ := volume) (f := ρ j) (g := g) (x₀ := x) (R := σ j)
          (z₀ := g x) hε'.le (hρs j) (hρn j) (hρi j) hgc.aestronglyMeasurable
          (fun y hy ↦ (hδg ((mem_ball.1 hy).trans hjδ)).le)
        rw [dist_eq_norm] at hd
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal hd
      · rw [indicator_of_notMem hx]
        have hxR : R + 1 < ‖x‖ := by
          rw [hSdef, mem_closedBall, dist_zero_right, not_le] at hx
          exact hx
        have hconv : convolution (ρ j) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x = 0 := by
          rw [convolution_def]
          refine integral_eq_zero_of_ae (Eventually.of_forall fun t ↦ ?_)
          simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, Pi.zero_apply]
          by_cases ht : ρ j t = 0
          · rw [ht, zero_mul]
          · have htb : ‖t‖ < σ j := mem_ball_zero_iff.1 (hρs j ht)
            have hxt : ‖x‖ - ‖t‖ ≤ ‖x - t‖ := norm_sub_norm_le x t
            rw [hgR (x - t) (by linarith), mul_zero]
        rw [hconv, hgR x (by linarith), sub_zero, enorm_zero]
    calc ∫⁻ x, ‖convolution (ρ j) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x - g x‖ₑ
        ≤ ∫⁻ x, S.indicator (fun _ ↦ ENNReal.ofReal ε') x := lintegral_mono hpt
      _ = ENNReal.ofReal ε' * volume S := lintegral_indicator_const hSm _
      _ = ENNReal.ofReal (ε' * m) := by
          rw [ENNReal.ofReal_mul hε'.le, hm, ENNReal.ofReal_toReal hSf]
      _ ≤ ENNReal.ofReal ε₀ := by
          apply ENNReal.ofReal_le_ofReal
          rw [hε'eq, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
          nlinarith
      _ ≤ ε := hε₀le
  -- Step 3 (density of `C_c` in `L¹`): approximate indicators of finite-measure sets by inner
  -- (compact `K`) and outer (open `V`) regularity and an Urysohn function `K ≤ f ≤ V`, then
  -- extend to `L¹` by `MemLp.induction_dense`.
  have hdense : ∀ δ : ℝ≥0∞, δ ≠ 0 → ∃ g : Rn n → ℝ,
      eLpNorm (F - g) 1 volume ≤ δ ∧ (Continuous g ∧ HasCompactSupport g) := by
    intro δ hδ
    refine (memLp_one_iff_integrable.2 hF).induction_dense ENNReal.one_ne_top
      (fun g ↦ Continuous g ∧ HasCompactSupport g) ?_ ?_ hδ
    · intro c s hs hsfin ε hε
      obtain ⟨η, hηpos, hη⟩ := exists_Lp_half ℝ (volume : Measure (Rn n)) 1 hε
      obtain ⟨ζ, hζpos, hζ⟩ :=
        exists_eLpNorm_indicator_le (μ := (volume : Measure (Rn n))) ENNReal.one_ne_top c hηpos.ne'
      have hζpos' : (0 : ℝ≥0∞) < ζ := ENNReal.coe_pos.2 hζpos
      obtain ⟨K, hKs, hK, hKsmall⟩ := hs.exists_isCompact_sdiff_lt hsfin.ne hζpos'.ne'
      obtain ⟨V, hKV, hV, -, hVsmall⟩ :=
        hK.measurableSet.exists_isOpen_sdiff_lt (μ := volume) hK.measure_lt_top.ne hζpos'.ne'
      obtain ⟨f, hfK, hfc, hfV, hfI⟩ :=
        exists_continuousMap_one_of_isCompact_subset_isOpen hK hV hKV
      have hfzero : ∀ x ∉ V, f x = 0 := fun x hx ↦
        image_eq_zero_of_notMem_tsupport fun h ↦ hx (hfV h)
      have hgcont : Continuous (fun x ↦ f x * c) := f.continuous.mul continuous_const
      have hgc : HasCompactSupport (fun x ↦ f x * c) :=
        (show HasCompactSupport f from hfc).mul_right
      have hgmem : MemLp (fun x ↦ f x * c) 1 volume := hgcont.memLp_of_hasCompactSupport hgc
      have hdiff : ∀ x, ‖f x * c - K.indicator (fun _ ↦ c) x‖ ≤
          ‖(V \ K).indicator (fun _ ↦ c) x‖ := by
        intro x
        by_cases hxK : x ∈ K
        · simp [hxK, hfK hxK]
        · by_cases hxV : x ∈ V
          · simp only [indicator_of_notMem hxK, sub_zero,
              indicator_of_mem (mem_sdiff_of_mem hxV hxK), norm_mul, Real.norm_eq_abs,
              abs_of_nonneg (hfI x).1]
            exact mul_le_of_le_one_left (abs_nonneg c) (hfI x).2
          · simp [hxK, hxV, hfzero x hxV]
      have I1 : eLpNorm ((fun x ↦ f x * c) - K.indicator (fun _ ↦ c)) 1 volume ≤ η :=
        (eLpNorm_mono (hgmem.aestronglyMeasurable.sub
          (aestronglyMeasurable_const.indicator hK.measurableSet)) hdiff).trans
          (hζ _ hVsmall.le (hV.measurableSet.diff hK.measurableSet).nullMeasurableSet)
      have I2 : eLpNorm (K.indicator (fun _ ↦ c) - s.indicator (fun _ ↦ c)) 1 volume ≤ η := by
        rw [← eLpNorm_neg, neg_sub, ← indicator_sdiff hKs]
        exact hζ _ hKsmall.le (hs.diff hK.measurableSet).nullMeasurableSet
      refine ⟨fun x ↦ f x * c, ?_, hgcont, hgc⟩
      convert (hη _ _ I1 I2).le using 2
      ext x
      simp
    · intro f g hf hg
      exact ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  -- Step 4 (ε/3 argument): `ρ_j * F - F = ρ_j * (F - g) + (ρ_j * g - g) + (g - F)`.
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ : ℝ≥0∞, 0 < δ ∧ δ + (δ + δ) ≤ ε := by
    refine ⟨ε / 3, ENNReal.div_pos hε.ne' (by norm_num), ?_⟩
    have h3 : ε / 3 + (ε / 3 + ε / 3) = 3 * (ε / 3) := by ring
    rw [h3]
    exact ENNReal.mul_div_le
  obtain ⟨g, hgF, hg_cont, hg_supp⟩ := hdense δ hδpos.ne'
  have hg_int : Integrable g volume := hg_cont.integrable_of_hasCompactSupport hg_supp
  have hFg : Integrable (fun x ↦ F x - g x) volume := hF.sub hg_int
  have hg_close : ∫⁻ x, ‖F x - g x‖ₑ ≤ δ := by
    rwa [eLpNorm_one_eq_lintegral_enorm (hF.aestronglyMeasurable.sub hg_int.aestronglyMeasurable)]
      at hgF
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 (hcc g hg_cont hg_supp)) δ hδpos] with j hj
  have hρcs : HasCompactSupport (ρ j) :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 (σ j))
      ((hρs j).trans ball_subset_closedBall)
  have hexF : ConvolutionExists (ρ j) (fun x ↦ F x - g x) (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    hρcs.convolutionExists_left _ (hρc j) hFg.locallyIntegrable
  have hexg : ConvolutionExists (ρ j) g (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    hρcs.convolutionExists_left _ (hρc j) hg_int.locallyIntegrable
  have hsplit : ∀ x, convolution (ρ j) F (ContinuousLinearMap.lsmul ℝ ℝ) volume x =
      convolution (ρ j) (fun x ↦ F x - g x) (ContinuousLinearMap.lsmul ℝ ℝ) volume x +
        convolution (ρ j) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
    intro x
    have h := (hexF x).distrib_add (hexg x)
    have hfun : ((fun x ↦ F x - g x) + g) = F := by
      funext y
      simp
    rwa [hfun] at h
  have hpt : ∀ x, ‖convolution (ρ j) F (ContinuousLinearMap.lsmul ℝ ℝ) volume x - F x‖ₑ ≤
      ‖convolution (ρ j) (fun x ↦ F x - g x) (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ +
        (‖convolution (ρ j) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x - g x‖ₑ + ‖F x - g x‖ₑ) := by
    intro x
    rw [hsplit x]
    set a := convolution (ρ j) (fun x ↦ F x - g x) (ContinuousLinearMap.lsmul ℝ ℝ) volume x
    set b := convolution (ρ j) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x
    have : a + b - F x = a + ((b - g x) + -(F x - g x)) := by ring
    rw [this]
    refine (enorm_add_le _ _).trans ?_
    gcongr
    refine (enorm_add_le _ _).trans ?_
    rw [enorm_neg]
  have hcontg : Continuous (convolution (ρ j) g (ContinuousLinearMap.lsmul ℝ ℝ) volume) :=
    hρcs.continuous_convolution_left _ (hρc j) hg_int.locallyIntegrable
  have hm1 : AEMeasurable (fun x ↦ ‖F x - g x‖ₑ) volume := hFg.aestronglyMeasurable.enorm
  have hm2 : AEMeasurable
      (fun x ↦ ‖convolution (ρ j) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x - g x‖ₑ) volume :=
    (hcontg.sub hg_cont).measurable.enorm.aemeasurable
  have hm3 : AEMeasurable
      (fun x ↦ ‖convolution (ρ j) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x - g x‖ₑ + ‖F x - g x‖ₑ)
      volume :=
    hm2.add hm1
  calc ∫⁻ x, ‖convolution (ρ j) F (ContinuousLinearMap.lsmul ℝ ℝ) volume x - F x‖ₑ
      ≤ ∫⁻ x, (‖convolution (ρ j) (fun x ↦ F x - g x) (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ +
        (‖convolution (ρ j) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x - g x‖ₑ + ‖F x - g x‖ₑ)) :=
        lintegral_mono hpt
    _ = (∫⁻ x, ‖convolution (ρ j) (fun x ↦ F x - g x) (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ) +
        ((∫⁻ x, ‖convolution (ρ j) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x - g x‖ₑ) +
          ∫⁻ x, ‖F x - g x‖ₑ) := by
        rw [lintegral_add_right' _ hm3, lintegral_add_right' _ hm1]
    _ ≤ δ + (δ + δ) :=
        add_le_add ((hcontr j _ hFg).trans hg_close) (add_le_add hj hg_close)
    _ ≤ ε := hδ

/-- **Gradient bound for a mollification (Simon Ch. 2, proof of Lemma 2.5).** Let `W ⊆ ℝⁿ` be
open, `u ∈ L¹(W)`, and let `ρ ≥ 0` be a `C²` kernel with `spt ρ ⊆ B_σ(0)` (open ball) and
`∫ ρ = 1`. If `B_σ(x) ⊆ W` (closed ball) for every `x ∈ K`, then `w = ρ * (1_W u)` satisfies
`∫_K |Dw| ≤ |Du|(W)`. The set `O = {x : B_σ(x) ⊆ W}` is open and contains `K`, and `w` is `C²`.
For a `C¹` field `g` with compact support in `O` and `|g| ≤ 1`, integration by parts
(`Submission.bv_lipschitz_integration_by_parts`) gives `-∫ Dw[g] = ∫ w div g`, which is at most
`|Du|(W)` by the duality bound `Submission.bv_mollifier_integral_mul_div_le`. Smooth duality
(`Submission.bv_lintegral_norm_fderiv_le_of_dual_compact`) then bounds `∫_L |Dw|` for each
compact `L ⊆ O`, compact exhaustion (`Submission.bv_lintegral_open_le_of_compact`) bounds
`∫_O |Dw|`, and `K ⊆ O` finishes. -/
theorem Submission.bv_mollifier_fderiv_lintegral_le : ∀ (n : ℕ) (W K : Set (Rn n)) (u ρ : Rn n → ℝ) (σ : ℝ), IsOpen W → IntegrableOn u W volume → ContDiff ℝ 2 ρ → (∀ x, 0 ≤ ρ x) → Function.support ρ ⊆ ball 0 σ → ∫ x, ρ x = 1 → (∀ x ∈ K, closedBall x σ ⊆ W) → ∫⁻ x in K, ‖fderiv ℝ (convolution ρ (W.indicator u) (ContinuousLinearMap.lsmul ℝ ℝ) volume) x‖ₑ ≤ Chapter02.bvVariationOn u W := by
  intro n W K u ρ σ hW hu hρ hρ0 hρs hρ1 hK
  set w := convolution ρ (W.indicator u) (ContinuousLinearMap.lsmul ℝ ℝ) volume
  -- Step 0: `O = {x : B_σ(x) ⊆ W}` is open. If `B_σ(x) ⊆ W`, then some `δ`-neighbourhood of the
  -- compact set `B_σ(x)` lies in `W`, and for `|y - x| < δ` each `z ∈ B_σ(y)` is within `|x - y|`
  -- of `z + (x - y) ∈ B_σ(x)`, so `B_σ(y) ⊆ W`.
  let O : Set (Rn n) := {x | closedBall x σ ⊆ W}
  have hO : IsOpen O := by
    refine Metric.isOpen_iff.2 fun x hx ↦ ?_
    obtain ⟨δ, hδ, hδW⟩ := (isCompact_closedBall x σ).exists_cthickening_subset_open hW hx
    refine ⟨δ, hδ, fun y hy z hz ↦ hδW (mem_cthickening_of_dist_le z (z + (x - y)) δ _ ?_ ?_)⟩
    · rw [mem_closedBall, dist_eq_norm] at hz ⊢
      rwa [show z + (x - y) - x = z - y by abel]
    · rw [dist_self_add_right, ← dist_eq_norm]
      exact (mem_ball'.1 hy).le
  have hKO : K ⊆ O := fun x hx ↦ hK x hx
  -- `ρ` has compact support (in `B_σ(0)`) and `1_W u` is integrable, so `w` is `C²`.
  have hρc : HasCompactSupport ρ :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 σ)
      (hρs.trans ball_subset_closedBall)
  have hF : Integrable (W.indicator u) volume := (integrable_indicator_iff hW.measurableSet).2 hu
  have hw : ContDiff ℝ 2 w :=
    hρc.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hρ hF.locallyIntegrable
  -- Step 1 (dual bound): a `C¹` field `g` with compact support is Lipschitz, so integration by
  -- parts gives `-∫ Dw[g] = ∫ w div g`, and the duality bound applies as `tsupport g ⊆ O`.
  have hdual : ∀ g : Rn n → Rn n, ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ O →
      (∀ x, ‖g x‖ ≤ 1) →
      ENNReal.ofReal (-∫ x, fderiv ℝ w x (g x)) ≤ Chapter02.bvVariationOn u W := by
    intro g hg hgc hgO hg1
    obtain ⟨C, hC⟩ := hg.lipschitzWith_of_hasCompactSupport hgc one_ne_zero
    rw [← Submission.bv_lipschitz_integration_by_parts n w g C (hw.of_le one_le_two) hC hgc]
    exact Submission.bv_mollifier_integral_mul_div_le n W u ρ σ g hW hu hρ.continuous hρ0 hρs hρ1
      hg hgc hg1 fun y hy ↦ hgO hy
  -- Steps 2–3: smooth duality on each compact `L ⊆ O`, exhaustion of `O` by compact sets (the
  -- integrand `‖Dw‖ₑ` is continuous, hence measurable), and monotonicity in the set, `K ⊆ O`.
  have hmeas : Measurable fun x ↦ ‖fderiv ℝ w x‖ₑ :=
    (hw.continuous_fderiv two_ne_zero).enorm.measurable
  calc ∫⁻ x in K, ‖fderiv ℝ w x‖ₑ ≤ ∫⁻ x in O, ‖fderiv ℝ w x‖ₑ := lintegral_mono_set hKO
    _ ≤ Chapter02.bvVariationOn u W :=
      Submission.bv_lintegral_open_le_of_compact n O (fun x ↦ ‖fderiv ℝ w x‖ₑ) _ hO hmeas
        fun L hL hLO ↦
          Submission.bv_lintegral_norm_fderiv_le_of_dual_compact n w O L _ hw hO hL hLO hdual

/-- **`|D|u||(O) ≤ |Du|(O)`, as used in Simon's proof of Ch. 2, Lemma 2.8.** For `O` open and
`u ∈ L¹_loc(O)`, the variation (2.4) of `|u|` on `O` is at most that of `u`. Fix an admissible
Lipschitz field `g` with `S = spt g ⊂ O` and thicken `S ⊂ V ⊂ V' ⊂⊂ O`. The mollifications
`w_j = ρ_j * (1_{V'} u)` satisfy `∫_V |Dw_j| ≤ |Du|(V') ≤ |Du|(O)`. For the smoothed absolute value
`F_j = √(w_j² + η_j²) - η_j`, integration by parts gives `∫ F_j div g = -∫ DF_j[g] ≤ ∫_V |Dw_j|`.
Since `F_j → |u|` in `L¹(V)` and `div g` is bounded and vanishes off `S`, the limit is
`∫_O |u| div g ≤ |Du|(O)`. -/
theorem Submission.bv_abs_variation_le : ∀ (n : ℕ) (O : Set (Rn n)) (u : Rn n → ℝ), IsOpen O → LocallyIntegrableOn u O volume → Chapter02.bvVariationOn (fun x ↦ |u x|) O ≤ Chapter02.bvVariationOn u O := by
  intro n O u hO hu
  -- Step 0 (reduction): it suffices to bound `∫_O |u| div g` for one admissible field `g`.
  refine iSup_le fun g ↦ iSup_le fun hg ↦ iSup_le fun hgO ↦ iSup_le fun hgn ↦ ?_
  obtain ⟨Λ, hΛ⟩ := hg
  set S : Set (Rn n) := tsupport (g : Rn n → Rn n)
  have hScpt : IsCompact S := g.hasCompactSupport.isCompact
  have hSmeas : MeasurableSet S := (isClosed_tsupport _).measurableSet
  have hg1 : ∀ x, ‖g x‖ ≤ 1 := fun x ↦
    (le_csSup (g.continuous.norm.bddAbove_range_of_hasCompactSupport g.hasCompactSupport.norm)
      (mem_range_self x)).trans hgn
  have hdiv0 : ∀ x, x ∉ S → Chapter02.euclideanDivergence (g : Rn n → Rn n) x = 0 := by
    intro x hx
    by_contra h
    exact hx (Chapter02.support_euclideanDivergence_subset _ h)
  -- Step 1 (neighbourhoods): `S ⊆ V = thickening (δ/4) S ⊆ V' = thickening δ S ⊆ O`, with
  -- `closure V'` compact in `O`, so `u` is integrable on `V'`.
  obtain ⟨δ, hδ, hδO⟩ := hScpt.exists_cthickening_subset_open hO hgO
  set V : Set (Rn n) := thickening (δ / 4) S
  set V' : Set (Rn n) := thickening δ S
  have hK : IsCompact (cthickening δ S) := hScpt.cthickening
  have hV'K : V' ⊆ cthickening δ S := thickening_subset_cthickening δ S
  have hVV' : V ⊆ V' := thickening_mono (by linarith) S
  have hSV : S ⊆ V := self_subset_thickening (by linarith) S
  have hV'O : V' ⊆ O := hV'K.trans hδO
  have hV'open : IsOpen V' := isOpen_thickening
  have hVmeas : MeasurableSet V := isOpen_thickening.measurableSet
  have hV'meas : MeasurableSet V' := hV'open.measurableSet
  have hVfin : volume V ≠ ∞ :=
    ((measure_mono (hVV'.trans hV'K)).trans_lt hK.measure_lt_top).ne
  have huV' : IntegrableOn u V' volume := (hu.integrableOn_compact_subset hδO hK).mono_set hV'K
  have huV : IntegrableOn u V volume := huV'.mono_set hVV'
  have hu'int : Integrable (V'.indicator u) volume := huV'.integrable_indicator hV'meas
  -- Step 2 (mollification): radii `σ j ≤ δ/4`, `σ j → 0`, kernels `ρ j` and `w j = ρ j * 1_{V'} u`.
  obtain ⟨η, hηpos, hη1, hηlim⟩ : ∃ η : ℕ → ℝ, (∀ j, 0 < η j) ∧ (∀ j, η j ≤ 1) ∧
      Tendsto η atTop (𝓝 0) :=
    ⟨fun j ↦ 1 / ((j : ℝ) + 1), fun j ↦ Nat.one_div_pos_of_nat,
      fun j ↦ (div_le_one (by positivity)).2 (by linarith [(j.cast_nonneg : (0 : ℝ) ≤ j)]),
      tendsto_one_div_add_atTop_nhds_zero_nat⟩
  obtain ⟨σ, hσpos, hσle, hσlim⟩ : ∃ σ : ℕ → ℝ, (∀ j, 0 < σ j) ∧ (∀ j, σ j ≤ δ / 4) ∧
      Tendsto σ atTop (𝓝 0) :=
    ⟨fun j ↦ δ / 4 * η j, fun j ↦ mul_pos (by linarith) (hηpos j),
      fun j ↦ mul_le_of_le_one_right (by linarith) (hη1 j),
      by simpa only [mul_zero] using hηlim.const_mul (δ / 4)⟩
  choose ρ hρs hρn hρsupp hρi using fun j ↦
    Submission.bv_abs_variation_exists_kernel n (σ j) (hσpos j)
  have hρ2 : ∀ j, ContDiff ℝ 2 (ρ j) := fun j ↦ (hρs j).of_le (WithTop.coe_le_coe.2 le_top)
  have hρc : ∀ j, HasCompactSupport (ρ j) := fun j ↦
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 (σ j))
      ((hρsupp j).trans ball_subset_closedBall)
  set w : ℕ → Rn n → ℝ := fun j ↦
    convolution (ρ j) (V'.indicator u) (ContinuousLinearMap.lsmul ℝ ℝ) volume
  have hw1 : ∀ j, ContDiff ℝ 1 (w j) := fun j ↦
    (hρc j).contDiff_convolution_left (n := 1) (ContinuousLinearMap.lsmul ℝ ℝ)
      ((hρs j).of_le (WithTop.coe_le_coe.2 le_top)) hu'int.locallyIntegrable
  -- `closedBall x (σ j) ⊆ V'` for `x ∈ V`, so the gradient bound of the mollifier applies:
  -- `∫_V ‖D w j‖ ≤ |Du|(V') ≤ |Du|(O)`.
  have hball : ∀ j, ∀ x ∈ V, closedBall x (σ j) ⊆ V' := fun j x hx ↦
    (closedBall_subset_cthickening hx (σ j)).trans <|
      (cthickening_thickening_subset (hσpos j).le (δ / 4) S).trans <|
        cthickening_subset_thickening' hδ (by linarith [hσle j]) S
  have hgrad : ∀ j, ∫⁻ x in V, ‖fderiv ℝ (w j) x‖ₑ ≤ Chapter02.bvVariationOn u O := fun j ↦
    (Submission.bv_mollifier_fderiv_lintegral_le n V' V u (ρ j) (σ j) hV'open huV' (hρ2 j)
      (hρn j) (hρsupp j) (hρi j) (hball j)).trans
      (Submission.bv_abs_variation_mono_set n u V' O hV'O)
  -- Step 3 (smoothed absolute value): `F j = √((w j)² + (η j)²) - η j`.
  set F : ℕ → Rn n → ℝ := fun j x ↦ Real.sqrt (w j x ^ 2 + η j ^ 2) - η j
  have hF : ∀ j, ContDiff ℝ 1 (F j) ∧ (∀ x, ‖fderiv ℝ (F j) x‖ ≤ ‖fderiv ℝ (w j) x‖) ∧
      ∀ x, abs (F j x - |w j x|) ≤ η j := fun j ↦
    Submission.bv_abs_variation_smoothed_abs n (w j) (η j) (hηpos j) (hw1 j)
  -- Step 4 (integration by parts): `∫ F j div g = -∫ D(F j)[g] ≤ ∫_S ‖D w j‖ ≤ |Du|(O)`.
  have hIbound : ∀ j, ENNReal.ofReal (∫ x, F j x * Chapter02.euclideanDivergence g x) ≤
      Chapter02.bvVariationOn u O := by
    intro j
    obtain ⟨hF1, hFd, -⟩ := hF j
    have hpt : ∀ x, ‖fderiv ℝ (F j) x (g x)‖ₑ ≤ S.indicator (fun x ↦ ‖fderiv ℝ (w j) x‖ₑ) x := by
      intro x
      by_cases hx : x ∈ S
      · rw [indicator_of_mem hx]
        calc ‖fderiv ℝ (F j) x (g x)‖ₑ ≤ ‖fderiv ℝ (F j) x‖ₑ * ‖g x‖ₑ :=
              ContinuousLinearMap.le_opENorm _ _
          _ ≤ ‖fderiv ℝ (w j) x‖ₑ * 1 := by
              gcongr
              · rw [← ofReal_norm, ← ofReal_norm]
                exact ENNReal.ofReal_le_ofReal (hFd x)
              · rw [← ofReal_norm, ← ENNReal.ofReal_one]
                exact ENNReal.ofReal_le_ofReal (hg1 x)
          _ = ‖fderiv ℝ (w j) x‖ₑ := mul_one _
      · rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx, map_zero, enorm_zero]
    rw [Submission.bv_lipschitz_integration_by_parts n (F j) g Λ hF1 hΛ g.hasCompactSupport]
    calc ENNReal.ofReal (-∫ x, fderiv ℝ (F j) x (g x))
        ≤ ‖-∫ x, fderiv ℝ (F j) x (g x)‖ₑ := Real.ofReal_le_enorm _
      _ = ‖∫ x, fderiv ℝ (F j) x (g x)‖ₑ := enorm_neg _
      _ ≤ ∫⁻ x, ‖fderiv ℝ (F j) x (g x)‖ₑ := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ x, S.indicator (fun x ↦ ‖fderiv ℝ (w j) x‖ₑ) x := lintegral_mono hpt
      _ = ∫⁻ x in S, ‖fderiv ℝ (w j) x‖ₑ := lintegral_indicator hSmeas _
      _ ≤ ∫⁻ x in V, ‖fderiv ℝ (w j) x‖ₑ := lintegral_mono_set hSV
      _ ≤ Chapter02.bvVariationOn u O := hgrad j
  -- Step 5 (limit): `div g` vanishes off `S ⊆ V`, so all integrals may be taken over `V`, where
  -- `F j → |u|` in `L¹`: `|F j - |u|| ≤ η j + |w j - 1_{V'} u|` on `V`.
  have hIV : ∀ j, ∫ x, F j x * Chapter02.euclideanDivergence g x =
      ∫ x in V, F j x * Chapter02.euclideanDivergence g x := fun j ↦
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [hdiv0 x fun h ↦ hx (hSV h), mul_zero]).symm
  have hOV : ∫ x in O, |u x| * Chapter02.euclideanDivergence g x =
      ∫ x in V, |u x| * Chapter02.euclideanDivergence g x := by
    have h1 : ∀ x ∉ O, |u x| * Chapter02.euclideanDivergence g x = 0 := fun x hx ↦ by
      rw [hdiv0 x fun h ↦ hx (hgO h), mul_zero]
    have h2 : ∀ x ∉ V, |u x| * Chapter02.euclideanDivergence g x = 0 := fun x hx ↦ by
      rw [hdiv0 x fun h ↦ hx (hSV h), mul_zero]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero h1,
      setIntegral_eq_integral_of_forall_compl_eq_zero h2]
  have hL1 : Tendsto (fun j ↦ ∫⁻ x in V, ‖F j x - |u x|‖ₑ) atTop (𝓝 0) := by
    have hconv := Submission.bv_mollifier_tendsto_L1 n (V'.indicator u) ρ σ hu'int
      (fun j ↦ (hρs j).continuous) hρn hρsupp hρi hσlim
    have hη' : Tendsto (fun j ↦ ENNReal.ofReal (η j) * volume V) atTop (𝓝 0) := by
      simpa only [ENNReal.ofReal_zero, zero_mul] using
        ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal hηlim) (Or.inr hVfin)
    have hmaj := hη'.add hconv
    rw [add_zero] at hmaj
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmaj
      (fun _ ↦ zero_le) fun j ↦ ?_
    have hpt : ∀ x ∈ V, ‖F j x - |u x|‖ₑ ≤ ENNReal.ofReal (η j) + ‖w j x - V'.indicator u x‖ₑ := by
      intro x hx
      rw [indicator_of_mem (hVV' hx) u, Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
        ← ENNReal.ofReal_add (hηpos j).le (abs_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ((abs_sub_le _ (|w j x|) _).trans (add_le_add ?_ ?_))
      · exact (hF j).2.2 x
      · exact abs_abs_sub_abs_le_abs_sub _ _
    calc ∫⁻ x in V, ‖F j x - |u x|‖ₑ
        ≤ ∫⁻ x in V, (ENNReal.ofReal (η j) + ‖w j x - V'.indicator u x‖ₑ) :=
          setLIntegral_mono' hVmeas hpt
      _ = ENNReal.ofReal (η j) * volume V + ∫⁻ x in V, ‖w j x - V'.indicator u x‖ₑ := by
          rw [lintegral_add_left measurable_const, setLIntegral_const]
      _ ≤ ENNReal.ofReal (η j) * volume V + ∫⁻ x, ‖w j x - V'.indicator u x‖ₑ := by
          gcongr
          exact Measure.restrict_le_self
  have hlim : Tendsto (fun j ↦ ∫ x in V, F j x * Chapter02.euclideanDivergence g x) atTop
      (𝓝 (∫ x in V, |u x| * Chapter02.euclideanDivergence g x)) :=
    Chapter02.tendsto_integral_mul_of_lintegral_sub (μ := volume.restrict V) (v := F)
      (u := fun x ↦ |u x|) (w := Chapter02.euclideanDivergence (g : Rn n → Rn n))
      (continuous_abs.comp_aestronglyMeasurable huV.aestronglyMeasurable)
      (Eventually.of_forall fun j ↦
        ((hF j).1.continuous.continuousOn.integrableOn_compact hK).mono_set (hVV'.trans hV'K))
      (Chapter02.measurable_euclideanDivergence _).aestronglyMeasurable
      (ae_of_all _ (Chapter02.norm_euclideanDivergence_le_of_lipschitz hΛ)) hL1
  have hlim' : Tendsto (fun j ↦ ENNReal.ofReal (∫ x, F j x * Chapter02.euclideanDivergence g x))
      atTop (𝓝 (ENNReal.ofReal (∫ x in O, |u x| * Chapter02.euclideanDivergence g x))) := by
    rw [hOV]
    refine (ENNReal.tendsto_ofReal hlim).congr fun j ↦ ?_
    rw [hIV j]
  exact le_of_tendsto' hlim' hIbound

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
