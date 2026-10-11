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

/-- **Simon Ch. 2, Theorem 1.8(i) (pp. 44–45), measure of a Lipschitz image.** For metric spaces
`X, Y`, real `m ≥ 0`, an arbitrary `E ⊆ X` (no measurability needed) and `f` `K`-Lipschitz on `E`,
`𝓗ᵐ(f(E)) ≤ Kᵐ 𝓗ᵐ(E)`. The covering argument is Mathlib's
`LipschitzOnWith.hausdorffMeasure_image_le` for `μH[m]`; multiplying it by the common
normalization `ω_m / 2^m` of `𝓗ᵐ = (ω_m / 2^m) • μH[m]` gives the bound for `𝓗ᵐ`. -/
theorem Submission.lipschitzImage_hausdorff_image_le : ∀ (X Y : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] (m : ℝ) (E : Set X) (f : X → Y) (K : ℝ≥0), 0 ≤ m → LipschitzOnWith K f E → Chapter01.simonHausdorffMeasureReal m (f '' E) ≤ (K : ℝ≥0∞) ^ m * Chapter01.simonHausdorffMeasureReal m E := by
  intro X Y _ _ _ _ _ _ m E f K hm hf
  -- The covering argument for the unnormalized measure: `μH[m] (f '' E) ≤ Kᵐ μH[m] E`.
  have h := hf.hausdorffMeasure_image_le hm
  -- `𝓗ᵐ S = (ω_m / 2^m) * μH[m] S` on `Y` and on `X`; scale `h` by `ω_m / 2^m` and reassociate.
  simp only [Chapter01.simonHausdorffMeasureReal, Measure.smul_apply, smul_eq_mul]
  calc Chapter01.realUnitBallVolume m / 2 ^ m * μH[m] (f '' E)
      ≤ Chapter01.realUnitBallVolume m / 2 ^ m * ((K : ℝ≥0∞) ^ m * μH[m] E) := by gcongr
    _ = (K : ℝ≥0∞) ^ m * (Chapter01.realUnitBallVolume m / 2 ^ m * μH[m] E) :=
      mul_left_comm _ _ _

/-- **Simon Ch. 2, Theorem 1.8(i) (pp. 44–45), measurability of a Lipschitz image.** If `X` is a
σ-compact metric space, `m ≥ 0`, `A ⊆ X` is `𝓗^m`-measurable with `𝓗^m(A) < ∞` and `f` is
`K`-Lipschitz on `A`, then `f(A)` is `𝓗^m`-measurable. A Borel kernel `B ⊆ A` with
`𝓗^m(A \ B) = 0` has finite measure, so `𝓗^m ⌞ B` is a finite, hence regular, measure on the
σ-compact space `X` (Simon's appeal to Ch. 1, 1.15(2)) and gives compact `C j ⊆ B` with
`𝓗^m(B \ C j) < 1/j`. Then `f(A) = ⋃ j, f(C j) ∪ (f(A) \ ⋃ j, f(C j))`: the first set is a
countable union of compact sets, and the second lies in the image of the `𝓗^m`-null set
`A \ ⋃ j, C j`, which is null by the first part (`Submission.lipschitzImage_hausdorff_image_le`). -/
theorem Submission.lipschitzImage_nullMeasurableSet_image : ∀ (X Y : Type) [MetricSpace X] [SigmaCompactSpace X] [MeasurableSpace X] [BorelSpace X] [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] (m : ℝ) (A : Set X) (f : X → Y) (K : ℝ≥0), 0 ≤ m → NullMeasurableSet A (Chapter01.simonHausdorffMeasureReal m) → Chapter01.simonHausdorffMeasureReal m A < ⊤ → LipschitzOnWith K f A → NullMeasurableSet (f '' A) (Chapter01.simonHausdorffMeasureReal m) := by
  intro X Y _ _ _ _ _ _ _ m A f K hm hA hAfin hf
  -- Null subsets of `A` have null images: `𝓗^m(f(E)) ≤ K^m 𝓗^m(E) = 0`.
  have hnull (E : Set X) (hEA : E ⊆ A) (hE : Chapter01.simonHausdorffMeasureReal m E = 0) :
      Chapter01.simonHausdorffMeasureReal m (f '' E) = 0 := by
    have h := Submission.lipschitzImage_hausdorff_image_le X Y m E f K hm (hf.mono hEA)
    rwa [hE, mul_zero, nonpos_iff_eq_zero] at h
  -- A Borel kernel `B ⊆ A` with `𝓗^m(A \ B) = 0`; it has finite measure.
  obtain ⟨B, hBA, hBmeas, hBae⟩ := hA.exists_measurable_subset_ae_eq
  have hAB : Chapter01.simonHausdorffMeasureReal m (A \ B) = 0 := ae_le_set.mp hBae.symm.le
  have hBfin : Chapter01.simonHausdorffMeasureReal m B ≠ ⊤ :=
    ne_top_of_le_ne_top hAfin.ne (measure_mono hBA)
  -- `ν = 𝓗^m ⌞ B` is a finite Borel measure on the σ-compact metric space `X`, hence regular:
  -- there are compact `C j ⊆ B` with `ν(B \ C j) < 1/j`.
  let ν : Measure X := (Chapter01.simonHausdorffMeasureReal m).restrict B
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 hBfin
  have : ν.Regular := inferInstance
  choose C hCB hCc hBC using fun j : ℕ ↦
    hBmeas.exists_isCompact_sdiff_lt (μ := ν) (measure_ne_top ν B)
      (show ((j : ℝ≥0∞)⁻¹) ≠ 0 by simp)
  have hCA (j : ℕ) : C j ⊆ A := (hCB j).trans hBA
  -- The Borel set `B \ ⋃ j, C j ⊆ B` has `𝓗^m`-measure `ν(B \ ⋃ j, C j) ≤ ν(B \ C j) < 1/j`.
  have hBCmeas : MeasurableSet (B \ ⋃ j, C j) :=
    hBmeas.diff (MeasurableSet.iUnion fun j ↦ (hCc j).measurableSet)
  have hBC0 : Chapter01.simonHausdorffMeasureReal m (B \ ⋃ j, C j) = 0 := by
    have h : ν (B \ ⋃ j, C j) = 0 := by
      refine le_antisymm (ge_of_tendsto ENNReal.tendsto_inv_nat_nhds_zero ?_) bot_le
      filter_upwards [] with j
      exact (measure_mono (show B \ ⋃ i, C i ⊆ B \ C j from
        fun x hx ↦ ⟨hx.1, fun hxC ↦ hx.2 (mem_iUnion.2 ⟨j, hxC⟩)⟩)).trans (hBC j).le
    change (Chapter01.simonHausdorffMeasureReal m).restrict B (B \ ⋃ j, C j) = 0 at h
    rwa [Measure.restrict_apply hBCmeas, inter_eq_left.2 sdiff_subset] at h
  -- Hence `D = A \ ⋃ j, C j ⊆ (A \ B) ∪ (B \ ⋃ j, C j)` is `𝓗^m`-null.
  have hD : Chapter01.simonHausdorffMeasureReal m (A \ ⋃ j, C j) = 0 := by
    refine measure_mono_null (show A \ ⋃ j, C j ⊆ (A \ B) ∪ (B \ ⋃ j, C j) from
      fun x hx ↦ ?_) (measure_union_null hAB hBC0)
    by_cases hxB : x ∈ B
    · exact mem_union_right _ ⟨hxB, hx.2⟩
    · exact mem_union_left _ ⟨hx.1, hxB⟩
  -- `G = ⋃ j, f(C j) ⊆ f(A)` is Borel, each `f(C j)` being compact.
  have hGmeas : MeasurableSet (⋃ j, f '' C j) :=
    MeasurableSet.iUnion fun j ↦
      ((hCc j).image_of_continuousOn (hf.mono (hCA j)).continuousOn).measurableSet
  have hGA : (⋃ j, f '' C j) ⊆ f '' A := iUnion_subset fun j ↦ image_mono (hCA j)
  -- `f(A) \ G ⊆ f(D)`, which is `𝓗^m`-null.
  have hrest : f '' A \ ⋃ j, f '' C j ⊆ f '' (A \ ⋃ j, C j) := by
    rintro y ⟨⟨x, hxA, rfl⟩, hy⟩
    refine ⟨x, ⟨hxA, fun hxC ↦ ?_⟩, rfl⟩
    obtain ⟨j, hxj⟩ := mem_iUnion.1 hxC
    exact hy (mem_iUnion.2 ⟨j, mem_image_of_mem f hxj⟩)
  rw [← union_sdiff_cancel hGA]
  exact hGmeas.nullMeasurableSet.union
    (NullMeasurableSet.of_null (measure_mono_null hrest (hnull _ sdiff_subset hD)))
/-- **Simon Ch. 2, proof of Theorem 1.8(ii) (p. 45), nested partitions.** A separable metric space
`X` has countable Borel partitions `(P i j)_j`, `i ∈ ℕ`, into pieces of mesh `< 1/(i+1)`, each
refining the previous one. For a dense sequence `q`, level `i` uses the disjointed balls
`Q i l = B(q l, rᵢ) \ ⋃_{l' < l} B(q l', rᵢ)`, `rᵢ = 1/(3(i+1))`; then `P 0 = Q 0` and
`P (i+1) n = P i u ∩ Q (i+1) v`, where `(u, v) = Nat.unpair n`. -/
theorem Submission.lipschitzImage_exists_nested_partitions : ∀ (X : Type) [MetricSpace X] [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [BorelSpace X], ∃ P : ℕ → ℕ → Set X, (∀ i j, MeasurableSet (P i j)) ∧ (∀ i j k, j ≠ k → Disjoint (P i j) (P i k)) ∧ (∀ i, ⋃ j, P i j = Set.univ) ∧ (∀ i j, ∀ x ∈ P i j, ∀ x' ∈ P i j, dist x x' < 1 / ((i : ℝ) + 1)) ∧ (∀ i j, ∃ k, P (i + 1) j ⊆ P i k) := by
  intro X _ _ _ _
  -- Empty `X`: all pieces are empty.
  rcases isEmpty_or_nonempty X with hX | hX
  · exact ⟨fun _ _ ↦ ∅, fun _ _ ↦ MeasurableSet.empty, fun _ _ _ _ ↦ empty_disjoint _,
      fun _ ↦ eq_univ_of_forall isEmptyElim, fun _ _ x ↦ isEmptyElim x, fun _ _ ↦ ⟨0, subset_rfl⟩⟩
  -- A dense sequence `q`, and the level-`i` pieces `Q i l`: Borel, disjoint, covering, and
  -- contained in `B(q l, 1/(3(i+1)))`.
  obtain ⟨q, hq⟩ := TopologicalSpace.exists_dense_seq X
  obtain ⟨Q, hQmeas, hQdisj, hQcov, hQball⟩ : ∃ Q : ℕ → ℕ → Set X,
      (∀ i l, MeasurableSet (Q i l)) ∧ (∀ i l l', l ≠ l' → Disjoint (Q i l) (Q i l')) ∧
      (∀ i (x : X), ∃ l, x ∈ Q i l) ∧ ∀ i l, Q i l ⊆ ball (q l) (1 / ((i : ℝ) + 1) / 3) := by
    refine ⟨fun i ↦ disjointed fun l ↦ ball (q l) (1 / ((i : ℝ) + 1) / 3),
      fun i ↦ MeasurableSet.disjointed fun _ ↦ measurableSet_ball,
      fun i _ _ h ↦ disjoint_disjointed _ h, fun i x ↦ ?_,
      fun i ↦ disjointed_subset fun l ↦ ball (q l) (1 / ((i : ℝ) + 1) / 3)⟩
    obtain ⟨l, hl⟩ := hq.exists_dist_lt x (by positivity : (0 : ℝ) < 1 / ((i : ℝ) + 1) / 3)
    have hx : x ∈ ⋃ l, ball (q l) (1 / ((i : ℝ) + 1) / 3) := mem_iUnion.2 ⟨l, mem_ball.2 hl⟩
    rw [← iUnion_disjointed] at hx
    exact mem_iUnion.1 hx
  -- The refinement: `P 0 = Q 0` and `P (i+1) n = P i (unpair n).1 ∩ Q (i+1) (unpair n).2`.
  obtain ⟨P, hP0, hPsucc⟩ : ∃ P : ℕ → ℕ → Set X, (∀ n, P 0 n = Q 0 n) ∧
      ∀ i n, P (i + 1) n = P i (Nat.unpair n).1 ∩ Q (i + 1) (Nat.unpair n).2 :=
    ⟨fun i ↦ Nat.rec (motive := fun _ ↦ ℕ → Set X) (Q 0)
      (fun i Pi n ↦ Pi (Nat.unpair n).1 ∩ Q (i + 1) (Nat.unpair n).2) i, fun _ ↦ rfl,
      fun _ _ ↦ rfl⟩
  have hPcov : ∀ i (x : X), ∃ j, x ∈ P i j := by
    intro i x
    induction i with
    | zero =>
      obtain ⟨l, hl⟩ := hQcov 0 x
      exact ⟨l, (hP0 l).symm ▸ hl⟩
    | succ i ih =>
      obtain ⟨j, hj⟩ := ih
      obtain ⟨l, hl⟩ := hQcov (i + 1) x
      refine ⟨Nat.pair j l, ?_⟩
      rw [hPsucc, Nat.unpair_pair]
      exact ⟨hj, hl⟩
  refine ⟨P, fun i ↦ ?_, fun i ↦ ?_, fun i ↦ eq_univ_of_forall fun x ↦ mem_iUnion.2 (hPcov i x),
    fun i n x hx x' hx' ↦ ?_,
    fun i n ↦ ⟨(Nat.unpair n).1, (hPsucc i n).subset.trans inter_subset_left⟩⟩
  · -- Borel.
    induction i with
    | zero => exact fun n ↦ (hP0 n).symm ▸ hQmeas 0 n
    | succ i ih => exact fun n ↦ (hPsucc i n).symm ▸ (ih _).inter (hQmeas _ _)
  · -- Disjoint: distinct `n, n'` have distinct `unpair n, unpair n'`.
    induction i with
    | zero => intro j k hjk; rw [hP0, hP0]; exact hQdisj 0 j k hjk
    | succ i ih =>
      intro j k hjk
      rw [hPsucc, hPsucc]
      by_cases hu : (Nat.unpair j).1 = (Nat.unpair k).1
      · have hv : (Nat.unpair j).2 ≠ (Nat.unpair k).2 := fun hv ↦
          hjk (by rw [← Nat.pair_unpair j, ← Nat.pair_unpair k, hu, hv])
        exact (hQdisj _ _ _ hv).mono inter_subset_right inter_subset_right
      · exact (ih _ _ hu).mono inter_subset_left inter_subset_left
  · -- Mesh: `P i n` lies in a ball of radius `1/(3(i+1))`.
    obtain ⟨l, hl⟩ : ∃ l, P i n ⊆ Q i l := by
      cases i with
      | zero => exact ⟨n, (hP0 n).subset⟩
      | succ i => exact ⟨(Nat.unpair n).2, (hPsucc i n).subset.trans inter_subset_right⟩
    have h₁ := mem_ball.1 (hQball i l (hl hx))
    have h₂ := mem_ball.1 (hQball i l (hl hx'))
    have hi : (0 : ℝ) < 1 / ((i : ℝ) + 1) := by positivity
    linarith [dist_triangle_right x x' (q l)]
/-- **Simon Ch. 2, Theorem 1.8(ii), counting step (p. 45).** For nested partitions `P i ·` of `X`
into pieces any two of whose points are at distance `< 1/(i+1)`, the piece counts
`N_i(y) = ∑ⱼ 1_{f(A ∩ P i j)}(y)` increase pointwise to the multiplicity `N(f, y) = fiberCount A f y`. -/
theorem Submission.lipschitzImage_iSup_pieceCount_eq_fiberCount : ∀ (X Y : Type) [MetricSpace X] (A : Set X) (f : X → Y) (P : ℕ → ℕ → Set X), (∀ i j k, j ≠ k → Disjoint (P i j) (P i k)) → (∀ i, ⋃ j, P i j = Set.univ) → (∀ i j, ∀ x ∈ P i j, ∀ x' ∈ P i j, dist x x' < 1 / ((i : ℝ) + 1)) → (∀ i j, ∃ k, P (i + 1) j ⊆ P i k) → ∀ y : Y, Monotone (fun i ↦ ∑' j, (f '' (A ∩ P i j)).indicator (1 : Y → ℝ≥0∞) y) ∧ ⨆ i, ∑' j, (f '' (A ∩ P i j)).indicator (1 : Y → ℝ≥0∞) y = fiberCount A f y := by
  intro X Y _ A f P hdisj hcov hdiam hnest y
  -- Every point lies in exactly one piece of each level.
  have hmem : ∀ i (x : X), ∃ j, x ∈ P i j := fun i x ↦ by
    have hx : x ∈ ⋃ j, P i j := by rw [hcov i]; exact Set.mem_univ x
    exact Set.mem_iUnion.1 hx
  have uniq : ∀ {i j k : ℕ} {x : X}, x ∈ P i j → x ∈ P i k → j = k := by
    intro i j k x hj hk
    by_contra hne
    exact Set.disjoint_left.1 (hdisj i j k hne) hj hk
  choose p hp using hmem
  choose q hq using hnest
  set S := A ∩ f ⁻¹' {y}
  -- `N_i(y)` is the cardinality of `p i '' S`, the set of `j` with `y ∈ f(A ∩ P i j)`.
  have hiff : ∀ i j, y ∈ f '' (A ∩ P i j) ↔ j ∈ p i '' S := by
    intro i j
    constructor
    · rintro ⟨x, ⟨hxA, hxP⟩, hfx⟩
      exact ⟨x, ⟨hxA, hfx⟩, uniq (hp i x) hxP⟩
    · rintro ⟨x, ⟨hxA, hfx⟩, rfl⟩
      exact ⟨x, ⟨hxA, hp i x⟩, hfx⟩
  have hN : ∀ i, ∑' j, (f '' (A ∩ P i j)).indicator (1 : Y → ℝ≥0∞) y =
      ((p i '' S).encard : ℝ≥0∞) := by
    intro i
    have hind : ∀ j, (f '' (A ∩ P i j)).indicator (1 : Y → ℝ≥0∞) y =
        (p i '' S).indicator (fun _ ↦ (1 : ℝ≥0∞)) j := by
      intro j
      by_cases hj : j ∈ p i '' S
      · rw [Set.indicator_of_mem hj, Set.indicator_of_mem ((hiff i j).2 hj), Pi.one_apply]
      · rw [Set.indicator_of_notMem hj, Set.indicator_of_notMem (mt (hiff i j).1 hj)]
    rw [tsum_congr hind, ← tsum_subtype, ENNReal.tsum_set_one]
  -- (a) `p i '' S` is the image of `p (i + 1) '' S` under the nesting map `q i`.
  have hmono : ∀ i, (p i '' S).encard ≤ (p (i + 1) '' S).encard := by
    intro i
    have himage : p i '' S = q i '' (p (i + 1) '' S) := by
      rw [Set.image_image]
      exact Set.image_congr fun x _ ↦ uniq (hp i x) (hq i (p (i + 1) x) (hp (i + 1) x))
    rw [himage]
    exact Set.encard_image_le _ _
  -- (c) A finite `F ⊆ S` with `n` points meets `n` distinct pieces once `1/(i+1)` is below all
  -- distances between distinct points of `F`.
  have hexh : ∀ n : ℕ, (n : ℕ∞) ≤ S.encard → ∃ i, (n : ℕ∞) ≤ (p i '' S).encard := by
    intro n hn
    obtain ⟨F, hFS, hFn⟩ := Set.exists_subset_encard_eq hn
    have hFfin : F.Finite := Set.finite_of_encard_eq_coe hFn
    have hev : ∀ᶠ i : ℕ in atTop, ∀ z ∈ F ×ˢ F, z.1 ≠ z.2 → 1 / ((i : ℝ) + 1) < dist z.1 z.2 := by
      rw [Filter.eventually_all_finite (hFfin.prod hFfin)]
      intro z _
      by_cases hz : z.1 = z.2
      · exact Filter.Eventually.of_forall fun _ h ↦ absurd hz h
      · filter_upwards [tendsto_one_div_add_atTop_nhds_zero_nat.eventually
          (gt_mem_nhds (dist_pos.2 hz))] with i hi _
        exact hi
    obtain ⟨i, hi⟩ := hev.exists
    have hinj : Set.InjOn (p i) F := by
      intro x hx x' hx' hxx'
      by_contra hne
      have hx'P : x' ∈ P i (p i x) := by rw [hxx']; exact hp i x'
      exact absurd ((hi (x, x') ⟨hx, hx'⟩ hne).trans (hdiam i (p i x) x (hp i x) x' hx'P))
        (lt_irrefl _)
    refine ⟨i, ?_⟩
    calc (n : ℕ∞) = F.encard := hFn.symm
      _ = (p i '' F).encard := hinj.encard_image.symm
      _ ≤ (p i '' S).encard := Set.encard_le_encard (Set.image_mono hFS)
  simp only [hN]
  refine ⟨monotone_nat_of_le_succ fun i ↦ ENat.toENNReal_le.2 (hmono i), ?_⟩
  show ⨆ i, ((p i '' S).encard : ℝ≥0∞) = ((S.encard : ℕ∞) : ℝ≥0∞)
  -- (b) `N_i(y) ≤ encard S`; the reverse inequality for the supremum follows from (c).
  refine le_antisymm (iSup_le fun i ↦ ENat.toENNReal_le.2 (Set.encard_image_le _ _)) ?_
  rcases eq_or_ne S.encard ⊤ with htop | htop
  · rw [htop, ENat.toENNReal_top]
    refine top_le_iff.2 (ENNReal.eq_top_of_forall_nnreal_le fun r ↦ ?_)
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ENNReal.coe_ne_top : (r : ℝ≥0∞) ≠ ⊤)
    obtain ⟨i, hi⟩ := hexh n (by rw [htop]; exact le_top)
    calc (r : ℝ≥0∞) ≤ n := hn.le
      _ = ((n : ℕ∞) : ℝ≥0∞) := (ENat.toENNReal_coe n).symm
      _ ≤ ((p i '' S).encard : ℝ≥0∞) := ENat.toENNReal_le.2 hi
      _ ≤ ⨆ i, ((p i '' S).encard : ℝ≥0∞) := le_iSup (fun i ↦ ((p i '' S).encard : ℝ≥0∞)) i
  · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 htop
    obtain ⟨i, hi⟩ := hexh k hk.le
    calc ((S.encard : ℕ∞) : ℝ≥0∞) = ((k : ℕ∞) : ℝ≥0∞) := by rw [hk]
      _ ≤ ((p i '' S).encard : ℝ≥0∞) := ENat.toENNReal_le.2 hi
      _ ≤ ⨆ i, ((p i '' S).encard : ℝ≥0∞) := le_iSup (fun i ↦ ((p i '' S).encard : ℝ≥0∞)) i

/-- The frozen Chapter 2 contract: the conjunction of all headline results. -/
theorem main_theorem : LipschitzExtension ∧ Rademacher ∧ C1Approximation ∧ WhitneyExtension ∧ LipschitzImageHausdorff ∧ EilenbergInequality ∧ BVCompactness ∧ BVPoincare ∧ BVExtensionEstimate ∧ AreaFormula ∧ FirstVariation ∧ SecondVariation ∧ StationaryIffMeanCurvatureZero ∧ SecondVariationStationary ∧ CoareaFormula ∧ C1Sard := by sorry

end GMT.Ch02


/-- **Simon Ch. 2, Theorem 1.8 (p. 44).** (i) is the two image results applied to `A`. (ii): cut `A`
along nested Borel partitions `P i ·` of `X` of mesh `< 1/(i+1)`. The piece counts
`N_i(y) = ∑'_j 1_{f(A ∩ P i j)}(y)` are a.e.-measurable (each `f(A ∩ P i j)` is null-measurable by
(i)) and increase to `fiberCount A f`, so by monotone convergence `∫ N = sup_i ∫ N_i`, where
`∫ N_i = ∑'_j Hᵐ(f(A ∩ P i j)) ≤ Kᵐ ∑'_j Hᵐ(A ∩ P i j) = Kᵐ Hᵐ(A)`. -/
theorem Submission.lipschitz_image_hausdorff_theorem : LipschitzImageHausdorff := by
  intro X Y _ _ _ _ _ _ _ m A f K hm hA hAfin hf
  refine ⟨⟨Submission.lipschitzImage_nullMeasurableSet_image X Y m A f K hm hA hAfin hf,
    Submission.lipschitzImage_hausdorff_image_le X Y m A f K hm hf⟩, ?_⟩
  obtain ⟨P, hPmeas, hPdisj, hPcover, hPdiam, hPnest⟩ :=
    Submission.lipschitzImage_exists_nested_partitions X
  have hcount := Submission.lipschitzImage_iSup_pieceCount_eq_fiberCount X Y A f P hPdisj hPcover
    hPdiam hPnest
  have hpiece (i j : ℕ) : NullMeasurableSet (A ∩ P i j) (Chapter01.simonHausdorffMeasureReal m) :=
    hA.inter (hPmeas i j).nullMeasurableSet
  have himage (i j : ℕ) :
      NullMeasurableSet (f '' (A ∩ P i j)) (Chapter01.simonHausdorffMeasureReal m) :=
    Submission.lipschitzImage_nullMeasurableSet_image X Y m (A ∩ P i j) f K hm (hpiece i j)
      ((measure_mono Set.inter_subset_left).trans_lt hAfin) (hf.mono Set.inter_subset_left)
  have hind (i j : ℕ) : AEMeasurable ((f '' (A ∩ P i j)).indicator (1 : Y → ℝ≥0∞))
      (Chapter01.simonHausdorffMeasureReal m) :=
    aemeasurable_one.indicator₀ (himage i j)
  have hN (i : ℕ) : AEMeasurable (fun y ↦ ∑' j, (f '' (A ∩ P i j)).indicator (1 : Y → ℝ≥0∞) y)
      (Chapter01.simonHausdorffMeasureReal m) :=
    AEMeasurable.tsum (hind i)
  have hfib : fiberCount A f =
      fun y ↦ ⨆ i, ∑' j, (f '' (A ∩ P i j)).indicator (1 : Y → ℝ≥0∞) y :=
    funext fun y ↦ (hcount y).2.symm
  refine ⟨by rw [hfib]; exact AEMeasurable.iSup hN, ?_⟩
  calc ∫⁻ y, fiberCount A f y ∂Chapter01.simonHausdorffMeasureReal m
      = ⨆ i, ∫⁻ y, ∑' j, (f '' (A ∩ P i j)).indicator (1 : Y → ℝ≥0∞) y
          ∂Chapter01.simonHausdorffMeasureReal m := by
        rw [hfib]
        exact lintegral_iSup' hN (ae_of_all _ fun y ↦ (hcount y).1)
    _ ≤ (K : ℝ≥0∞) ^ m * Chapter01.simonHausdorffMeasureReal m A := by
        refine iSup_le fun i ↦ ?_
        calc ∫⁻ y, ∑' j, (f '' (A ∩ P i j)).indicator (1 : Y → ℝ≥0∞) y
              ∂Chapter01.simonHausdorffMeasureReal m
            = ∑' j, Chapter01.simonHausdorffMeasureReal m (f '' (A ∩ P i j)) := by
              rw [lintegral_tsum (hind i)]
              exact tsum_congr fun j ↦ lintegral_indicator_one₀ (himage i j)
          _ ≤ ∑' j, (K : ℝ≥0∞) ^ m * Chapter01.simonHausdorffMeasureReal m (A ∩ P i j) :=
              ENNReal.tsum_le_tsum fun j ↦ Submission.lipschitzImage_hausdorff_image_le X Y m
                (A ∩ P i j) f K hm (hf.mono Set.inter_subset_left)
          _ = (K : ℝ≥0∞) ^ m * Chapter01.simonHausdorffMeasureReal m A := by
              rw [ENNReal.tsum_mul_left, ← measure_iUnion₀ (f := fun j ↦ A ∩ P i j)
                (fun j k hjk ↦ ((hPdisj i j k hjk).mono Set.inter_subset_right
                  Set.inter_subset_right).aedisjoint) (hpiece i), ← Set.inter_iUnion, hPcover i,
                Set.inter_univ]
