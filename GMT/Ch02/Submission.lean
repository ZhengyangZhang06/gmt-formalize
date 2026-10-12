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
/-- **Simon Ch. 2, 4.20, 4.27 and 4.30 (pp. 59–61), integrability for the divergence identity.**
Let `M ⊆ ℝᴺ` be measurable, with `y ↦ P_y` and `H` continuous on `M` and `Hⁿ` finite on compact
subsets of `M`, and let `Y` be `C¹` and vanish off a closed set `F` with `M ∩ F` compact. Then
`div_M Y` and `Y · H` are `Hⁿ`-integrable on `M`. As `P_y = ι ∘ π` (`ι` the inclusion of `T_y M`,
`π` the orthogonal projection onto it), cyclicity of the trace gives
`div_M Y(y) = trace(DY(y) ∘ P_y)`, so both functions are continuous on `M`. They vanish off `F`
(`DY = 0` on the open set `Fᶜ`), are bounded on the compact set `M ∩ F`, and `Hⁿ(M ∩ F) < ∞`. -/
theorem Submission.tangentialDivergence_meanCurvature_integrableOn : ∀ (n N : ℕ) (M F : Set (Rn N)) (Y : Rn N → Rn N), MeasurableSet M → ContinuousOn (tangentProjection M) M → ContinuousOn (meanCurvature M) M → (∀ C ⊆ M, IsCompact C → μHE[n] C < ⊤) → ContDiff ℝ 1 Y → IsClosed F → (∀ x ∉ F, Y x = 0) → IsCompact (M ∩ F) → IntegrableOn (tangentialDivergence M Y) M μHE[n] ∧ IntegrableOn (fun y ↦ inner ℝ (Y y) (meanCurvature M y)) M μHE[n] := by
  intro n N M F Y hM hP hH hfin hY hF hYF hMF
  -- Step 5: a function continuous on `M` and vanishing on `M \ F` is integrable on `M`: it is
  -- bounded on the compact set `M ∩ F`, which has finite measure.
  have key : ∀ f : Rn N → ℝ, ContinuousOn f M → (∀ y ∈ M, y ∉ F → f y = 0) →
      IntegrableOn f M μHE[n] := by
    intro f hf hf0
    have hfMF : ContinuousOn f (M ∩ F) := hf.mono inter_subset_left
    have hmeas : MeasurableSet (M ∩ F) := hM.inter hF.measurableSet
    obtain ⟨C, hC⟩ := hMF.exists_bound_of_continuousOn hfMF
    have hint : IntegrableOn f (M ∩ F) μHE[n] :=
      IntegrableOn.of_bound (hfin _ inter_subset_left hMF) (hfMF.aestronglyMeasurable hmeas) C
        ((ae_restrict_iff' hmeas).2 (Eventually.of_forall hC))
    exact hint.of_forall_sdiff_eq_zero hM fun y hy ↦ hf0 y hy.1 fun hyF ↦ hy.2 ⟨hy.1, hyF⟩
  -- Step 4: `DY(y) = 0` off `F`, since `Y` vanishes on the open set `Fᶜ`.
  have hD0 : ∀ y ∉ F, fderiv ℝ Y y = 0 := by
    intro y hy
    have hY0 : Y =ᶠ[𝓝 y] fun _ ↦ 0 :=
      eventually_of_mem (hF.isOpen_compl.mem_nhds hy) fun x hx ↦ hYF x hx
    rw [hY0.fderiv_eq]
    simp
  -- Step 1: `div_M Y(y) = trace(DY(y) ∘ P_y)`, as `P_y = ι ∘ π` and the trace is cyclic.
  have htr : ∀ y, tangentialDivergence M Y y = LinearMap.trace ℝ (Rn N)
      ((fderiv ℝ Y y ∘L tangentProjection M y : Rn N →L[ℝ] Rn N) : Rn N →ₗ[ℝ] Rn N) := by
    intro y
    set T := tangentSpace M y
    have hPT : ((fderiv ℝ Y y ∘L tangentProjection M y : Rn N →L[ℝ] Rn N) : Rn N →ₗ[ℝ] Rn N) =
        ((fderiv ℝ Y y : Rn N →ₗ[ℝ] Rn N) ∘ₗ T.subtype) ∘ₗ
          (T.orthogonalProjectionOnto : Rn N →ₗ[ℝ] T) := rfl
    rw [hPT, LinearMap.trace_comp_comm', LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ T)]
    simp [tangentialDivergence, tangentFrame, T]
  -- Step 2: `div_M Y` is continuous on `M`, the trace being continuous on `ℝᴺ →L[ℝ] ℝᴺ`.
  have hdiv : ContinuousOn (tangentialDivergence M Y) M := by
    have htrc : Continuous fun A : Rn N →L[ℝ] Rn N ↦
        LinearMap.trace ℝ (Rn N) (A : Rn N →ₗ[ℝ] Rn N) :=
      ((LinearMap.trace ℝ (Rn N)).comp
        (ContinuousLinearMap.coeLM ℝ)).continuous_of_finiteDimensional
    exact (htrc.comp_continuousOn
      ((hY.continuous_fderiv one_ne_zero).continuousOn.clm_comp hP)).congr fun y _ ↦ htr y
  -- Steps 3 and 6: `Y · H` is continuous on `M`, and both functions vanish off `F`.
  refine ⟨key _ hdiv fun y _ hy ↦ ?_, key _ (hY.continuous.continuousOn.inner hH) fun y _ hy ↦ ?_⟩
  · simp [tangentialDivergence, hD0 y hy]
  · simp [hYF y hy]
/-- **Simon Ch. 2, partition-of-unity step for 4.22(*) and 4.29–4.30 (pp. 59–61).** With `div_M`
as in 4.20 and `H` as in 4.27: let `Y` and `ζ_q` (`q < p`) be `C¹`, `Y = 0` off the closed set `S`,
and `∑_q ζ_q = 1` on an open `O ⊇ M ∩ S`. Then at every `y ∈ M`,
`div_M Y(y) + Y(y) · H(y) = ∑_q (div_M(ζ_q Y)(y) + ζ_q(y) Y(y) · H(y))`. Near `y`, `Y = ∑_q ζ_q Y`
(on `O` if `y ∈ S`, on `Sᶜ` otherwise), so `DY(y) = ∑_q D(ζ_q Y)(y)`; both terms are linear. -/
theorem Submission.tangentialDivergence_add_inner_eq_sum_partition : ∀ (N p : ℕ) (M S O : Set (Rn N)) (Y : Rn N → Rn N) (ζ : Fin p → Rn N → ℝ), ContDiff ℝ 1 Y → (∀ q, ContDiff ℝ 1 (ζ q)) → IsClosed S → (∀ x ∉ S, Y x = 0) → IsOpen O → M ∩ S ⊆ O → (∀ z ∈ O, ∑ q, ζ q z = 1) → ∀ y ∈ M, tangentialDivergence M Y y + inner ℝ (Y y) (meanCurvature M y) = ∑ q, (tangentialDivergence M (fun z ↦ ζ q z • Y z) y + inner ℝ (ζ q y • Y y) (meanCurvature M y)) := by
  intro N p M S O Y ζ hY hζ hS hYS hO hMSO hsum y hy
  -- Step 1: `Y = ∑_q ζ_q Y` near `y`: on `O` if `y ∈ S`, on `Sᶜ` (where `Y = 0`) otherwise.
  have hloc : Y =ᶠ[𝓝 y] fun z ↦ ∑ q, ζ q z • Y z := by
    by_cases hyS : y ∈ S
    · filter_upwards [hO.mem_nhds (hMSO ⟨hy, hyS⟩)] with z hz
      rw [← Finset.sum_smul, hsum z hz, one_smul]
    · filter_upwards [hS.isOpen_compl.mem_nhds hyS] with z hz
      simp [hYS z hz]
  -- Step 2: `DY(y) = ∑_q D(ζ_q Y)(y)`, each `ζ_q Y` being `C¹`.
  have hD : fderiv ℝ Y y = ∑ q, fderiv ℝ (fun z ↦ ζ q z • Y z) y := by
    rw [hloc.fderiv_eq, fderiv_fun_sum fun q _ ↦
      (((hζ q).fun_smul hY).differentiable one_ne_zero).differentiableAt]
  -- Step 3: the frame sum is linear in `DY(y)`; exchange the two finite sums.
  have hdiv : tangentialDivergence M Y y =
      ∑ q, tangentialDivergence M (fun z ↦ ζ q z • Y z) y := by
    simp only [tangentialDivergence, hD, _root_.sum_apply, inner_sum]
    exact Finset.sum_comm
  -- Step 4: `Y(y) = ∑_q ζ_q(y) Y(y)`, so the mean-curvature term splits the same way.
  have hval : Y y = ∑ q, ζ q y • Y y := hloc.eq_of_nhds
  have hinner : inner ℝ (Y y) (meanCurvature M y) =
      ∑ q, inner ℝ (ζ q y • Y y) (meanCurvature M y) := by
    rw [← sum_inner, ← hval]
  -- Step 5: add the two identities and regroup the sums.
  rw [Finset.sum_add_distrib, hdiv, hinner]
/-- **Simon Ch. 2, §5 (pp. 61–63), the hypothesis `Hⁿ(K ∩ M) < ∞`.** An `n`-dimensional `C^r`
submanifold `M ⊆ ℝᴺ` has locally finite and locally positive `Hⁿ`-measure.
(a) Compact `C ⊆ M`: near `y ∈ C` take a chart `ψ : V → W`; `C' = C ∩ B̄_{ρ/2}(y) ⊆ W` is `ψ(Q)` with
`Q = V ∩ ψ⁻¹(C')` compact (relative properness), and `ψ` is locally Lipschitz on `V`, so
`Hⁿ(C') < ∞`. (b) `y = ψ(x₀) ∈ O`: `V' = V ∩ ψ⁻¹(O ∩ W)` is an open neighbourhood of `x₀` with
`ψ(V') ⊆ M ∩ O`. A linear left inverse `P` of the injective `Dψ(x₀)` makes `P ∘ ψ` open at `x₀`
(inverse function theorem), so `0 < Lⁿ(P(ψ(V'))) ≤ ‖P‖ⁿ Hⁿ(ψ(V'))`. -/
theorem Submission.simon_submanifold_hausdorff_finite_pos : ∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)), Chapter02.IsSimonSubmanifold (E := Rn n) r M → (∀ C ⊆ M, IsCompact C → μHE[n] C < ⊤) ∧ ∀ y ∈ M, ∀ O : Set (Rn N), IsOpen O → y ∈ O → 0 < μHE[n] (M ∩ O) := by
  intro n N r M hM
  have hr : (1 : WithTop ℕ∞) ≤ r := by exact_mod_cast hM.1
  refine ⟨fun C hCM hC => ?_, fun y hyM O hO hyO => ?_⟩
  · -- (a) It suffices that every `y ∈ C` has a relative neighbourhood `C'` of finite measure.
    refine hC.measure_lt_top_of_nhdsWithin fun y hy => ?_
    obtain ⟨V, W, ψ, hyW, hψ⟩ := hM.2 y (hCM hy)
    obtain ⟨ρ, hρ, hρW⟩ := Metric.isOpen_iff.mp hψ.isOpen_target y hyW
    -- `C' = C ∩ B̄_{ρ/2}(y)` is a compact subset of `W`, so `Q = V ∩ ψ⁻¹(C')` is compact.
    have hC'W : C ∩ closedBall y (ρ / 2) ⊆ W := fun z hz =>
      hρW (closedBall_subset_ball (by linarith) hz.2)
    have hQ : IsCompact (V ∩ ψ ⁻¹' (C ∩ closedBall y (ρ / 2))) :=
      hψ.isCompact_source_inter_preimage _ (hC.inter_right isClosed_closedBall) hC'W
    -- `C' ⊆ M ∩ W = ψ(V)`, hence `C' = ψ(Q)`.
    have himg : C ∩ closedBall y (ρ / 2) ⊆ ψ '' (V ∩ ψ ⁻¹' (C ∩ closedBall y (ρ / 2))) := by
      intro z hz
      have hz' : z ∈ W ∩ M := ⟨hC'W hz, hCM hz.1⟩
      rw [← hψ.image_eq] at hz'
      obtain ⟨x, hxV, rfl⟩ := hz'
      exact ⟨x, ⟨hxV, hz⟩, rfl⟩
    refine ⟨C ∩ closedBall y (ρ / 2), inter_mem_nhdsWithin C (closedBall_mem_nhds y (by positivity)),
      (measure_mono himg).trans_lt ?_⟩
    -- `ψ` is locally Lipschitz on `V`, so the compact `Q` is covered by finitely many pieces
    -- with images of finite measure.
    refine hQ.induction_on (p := fun s => μHE[n] (ψ '' s) < ⊤) (by simp) ?_ ?_ ?_
    · intro s t hst ht
      exact (measure_mono (image_mono hst)).trans_lt ht
    · intro s t hs ht
      rw [image_union]
      exact (measure_union_le _ _).trans_lt (ENNReal.add_lt_top.2 ⟨hs, ht⟩)
    · intro x hx
      have hψx : ContDiffAt ℝ 1 ψ x :=
        (hψ.contDiffOn.contDiffAt (hψ.isOpen_source.mem_nhds hx.1)).of_le hr
      obtain ⟨K, t, ht, hK⟩ := hψx.exists_lipschitzOnWith
      refine ⟨t ∩ ball x 1, mem_nhdsWithin_of_mem_nhds (inter_mem ht (ball_mem_nhds x one_pos)), ?_⟩
      calc μHE[n] (ψ '' (t ∩ ball x 1)) ≤ (K : ℝ≥0∞) ^ n * μHE[n] (t ∩ ball x 1) :=
            Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n (hK.mono inter_subset_left)
        _ < ⊤ := by
            refine ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) ?_
            rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
            exact (measure_mono inter_subset_right).trans_lt measure_ball_lt_top
  · -- (b) Write `y = ψ(x₀)`; `V' = V ∩ ψ⁻¹(O ∩ W)` is an open neighbourhood of `x₀`.
    obtain ⟨V, W, ψ, hyW, hψ⟩ := hM.2 y hyM
    have hy : y ∈ ψ '' V := by rw [hψ.image_eq]; exact ⟨hyW, hyM⟩
    obtain ⟨x₀, hx₀V, rfl⟩ := hy
    have hV' : IsOpen (V ∩ ψ ⁻¹' (O ∩ W)) :=
      hψ.contDiffOn.continuousOn.isOpen_inter_preimage hψ.isOpen_source (hO.inter hψ.isOpen_target)
    have hx₀ : x₀ ∈ V ∩ ψ ⁻¹' (O ∩ W) := ⟨hx₀V, hyO, hyW⟩
    have himg : ψ '' (V ∩ ψ ⁻¹' (O ∩ W)) ⊆ M ∩ O := by
      rintro _ ⟨x, ⟨hxV, hxO, -⟩, rfl⟩
      have h : ψ x ∈ W ∩ M := hψ.image_eq ▸ mem_image_of_mem ψ hxV
      exact ⟨h.2, hxO⟩
    refine lt_of_lt_of_le ?_ (measure_mono himg)
    -- `Dψ(x₀)` is injective, so it has a linear left inverse `P : ℝᴺ → ℝⁿ`.
    obtain ⟨g, hg⟩ := (fderiv ℝ ψ x₀).toLinearMap.exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.2 (hψ.injective_fderiv hx₀V))
    set P : Rn N →L[ℝ] Rn n := LinearMap.toContinuousLinearMap g with hP
    have hPL : P.comp (fderiv ℝ ψ x₀) = ((ContinuousLinearEquiv.refl ℝ (Rn n) : Rn n ≃L[ℝ] Rn n) :
        Rn n →L[ℝ] Rn n) := by
      refine ContinuousLinearMap.ext fun v => ?_
      simpa [hP] using LinearMap.congr_fun hg v
    -- `P ∘ ψ` has derivative `id` at `x₀`, so it maps neighbourhoods of `x₀` onto neighbourhoods.
    have hPψ : HasStrictFDerivAt (fun x => P (ψ x))
        ((ContinuousLinearEquiv.refl ℝ (Rn n) : Rn n ≃L[ℝ] Rn n) : Rn n →L[ℝ] Rn n) x₀ := by
      rw [← hPL]
      exact P.hasStrictFDerivAt.comp x₀
        ((hψ.contDiffOn.contDiffAt (hψ.isOpen_source.mem_nhds hx₀V)).hasStrictFDerivAt
          (lt_of_lt_of_le zero_lt_one hr).ne')
    have hnhds : P '' (ψ '' (V ∩ ψ ⁻¹' (O ∩ W))) ∈ 𝓝 (P (ψ x₀)) := by
      rw [image_image, ← hPψ.map_nhds_eq_of_equiv]
      exact image_mem_map (hV'.mem_nhds hx₀)
    -- `0 < Lⁿ(P(ψ(V'))) = Hⁿ(P(ψ(V'))) ≤ ‖P‖ⁿ Hⁿ(ψ(V'))`.
    have hpos : 0 < μHE[n] (P '' (ψ '' (V ∩ ψ ⁻¹' (O ∩ W)))) := by
      rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
      exact Measure.measure_pos_of_mem_nhds _ hnhds
    have hle := Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
      (P.lipschitzWith.lipschitzOnWith (s := ψ '' (V ∩ ψ ⁻¹' (O ∩ W))))
    refine pos_iff_ne_zero.2 fun h0 => hpos.ne' ?_
    rw [h0, mul_zero] at hle
    exact nonpos_iff_eq_zero.mp hle
/-- **Symmetry of the second derivative (Schwarz)**, used for the symmetry `B_y(τ, η) = B_y(η, τ)`
of Simon Ch. 2, 4.26. If `f : ℝⁿ → ℝᴺ` is `C²` at `x`, then `L = D²f(x)` is symmetric. The Mathlib
statement (`ContDiffAt.isSymmSndFDerivAt`) is not imported, so this is the classical mean value
proof: `f` is differentiable near `x` and `Df` has derivative `L` at `x`, so
`‖Df(x + h) - Df(x) - L h‖ ≤ ε‖h‖` for `‖h‖ < δ`. The mean value inequality for
`g(s) = f(x + (t • u + (s * t) • v)) - f(x + (s * t) • v) - s • L (t • u) (t • v)` on `[0, 1]`
bounds the second difference `Δ = f(x + (t • u + t • v)) - f(x + t • v) - (f(x + t • u) - f(x))` by
`‖Δ - t² L u v‖ ≤ 2εt²(‖u‖ + ‖v‖)‖v‖`. Since `Δ` is symmetric in `u, v`, exchanging `a` and `b`
gives `‖L a b - L b a‖ ≤ 2ε(‖a‖ + ‖b‖)²` for every `ε > 0`. -/
theorem Submission.fderiv_fderiv_symm_of_contDiffAt : ∀ (n N : ℕ) (f : Rn n → Rn N) (x : Rn n), ContDiffAt ℝ 2 f x → ∀ a b : Rn n, fderiv ℝ (fderiv ℝ f) x a b = fderiv ℝ (fderiv ℝ f) x b a := by
  intro n N f x hf a b
  set L := fderiv ℝ (fderiv ℝ f) x
  -- Step 1: `f` is differentiable near `x`, and `Df` has derivative `L` at `x`.
  have hdiff : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y := by
    filter_upwards [hf.eventually (by simp)] with y hy
    exact hy.differentiableAt two_ne_zero
  have hDf : HasFDerivAt (fderiv ℝ f) L x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  -- Step 2: uniform first-order expansion of `Df` at `x`.
  have hexp : ∀ ε > 0, ∃ δ > 0, ∀ h : Rn n, ‖h‖ < δ → DifferentiableAt ℝ f (x + h) ∧
      ‖fderiv ℝ f (x + h) - fderiv ℝ f x - L h‖ ≤ ε * ‖h‖ := by
    intro ε hε
    have h1 := Asymptotics.isLittleO_iff.1 (hasFDerivAt_iff_isLittleO_nhds_zero.1 hDf) hε
    have h2 : ∀ᶠ h in 𝓝 (0 : Rn n), DifferentiableAt ℝ f (x + h) :=
      ((continuous_const.add continuous_id).tendsto' (0 : Rn n) x (by simp)).eventually hdiff
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (h2.and h1)
    exact ⟨δ, hδ, fun h hh ↦ hball (by simpa [dist_eq_norm] using hh)⟩
  -- Steps 3–5: the mean value inequality bounds the second difference.
  have hsec : ∀ ε > 0, ∀ δ > 0, (∀ h : Rn n, ‖h‖ < δ → DifferentiableAt ℝ f (x + h) ∧
      ‖fderiv ℝ f (x + h) - fderiv ℝ f x - L h‖ ≤ ε * ‖h‖) →
      ∀ u v : Rn n, ∀ t : ℝ, 0 < t → t * (‖u‖ + ‖v‖) < δ →
      ‖f (x + (t • u + t • v)) - f (x + t • v) - (f (x + t • u) - f x) - t ^ 2 • L u v‖ ≤
        2 * ε * t ^ 2 * (‖u‖ + ‖v‖) * ‖v‖ := by
    intro ε hε δ hδ hball u v t ht htδ
    have hnorm1 : ∀ s ∈ Icc (0 : ℝ) 1, ‖t • u + (s * t) • v‖ ≤ t * (‖u‖ + ‖v‖) := by
      intro s hs
      calc ‖t • u + (s * t) • v‖ ≤ ‖t • u‖ + ‖(s * t) • v‖ := norm_add_le _ _
        _ = t * ‖u‖ + s * t * ‖v‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ht.le,
            Real.norm_of_nonneg (mul_nonneg hs.1 ht.le)]
        _ ≤ t * (‖u‖ + ‖v‖) := by
          nlinarith [mul_nonneg (sub_nonneg.2 hs.2) (mul_nonneg ht.le (norm_nonneg v))]
    have hnorm2 : ∀ s ∈ Icc (0 : ℝ) 1, ‖(s * t) • v‖ ≤ t * (‖u‖ + ‖v‖) := by
      intro s hs
      rw [norm_smul, Real.norm_of_nonneg (mul_nonneg hs.1 ht.le)]
      nlinarith [mul_nonneg (sub_nonneg.2 hs.2) (mul_nonneg ht.le (norm_nonneg v)), norm_nonneg u]
    have hderiv : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt
        (fun s : ℝ ↦ f (x + (t • u + (s * t) • v)) - f (x + (s * t) • v) - s • L (t • u) (t • v))
        (fderiv ℝ f (x + (t • u + (s * t) • v)) (t • v) - fderiv ℝ f (x + (s * t) • v) (t • v) -
          L (t • u) (t • v)) (Icc 0 1) s := by
      intro s hs
      have hd1 : DifferentiableAt ℝ f (x + (t • u + (s * t) • v)) :=
        (hball _ ((hnorm1 s hs).trans_lt htδ)).1
      have hd2 : DifferentiableAt ℝ f (x + (s * t) • v) := (hball _ ((hnorm2 s hs).trans_lt htδ)).1
      have hc2 : HasDerivAt (fun s : ℝ ↦ x + (s * t) • v) (t • v) s := by
        simpa using ((hasDerivAt_mul_const t).smul_const v).const_add x
      have hc1 : HasDerivAt (fun s : ℝ ↦ x + (t • u + (s * t) • v)) (t • v) s := by
        simpa [add_assoc] using hc2.const_add (t • u)
      have hlin : HasDerivAt (fun s : ℝ ↦ s • L (t • u) (t • v)) (L (t • u) (t • v)) s := by
        simpa using (hasDerivAt_id s).smul_const (L (t • u) (t • v))
      exact (((hd1.hasFDerivAt.comp_hasDerivAt s hc1).sub
        (hd2.hasFDerivAt.comp_hasDerivAt s hc2)).sub hlin).hasDerivWithinAt
    have hbound : ∀ s ∈ Ico (0 : ℝ) 1,
        ‖fderiv ℝ f (x + (t • u + (s * t) • v)) (t • v) - fderiv ℝ f (x + (s * t) • v) (t • v) -
          L (t • u) (t • v)‖ ≤ 2 * ε * t ^ 2 * (‖u‖ + ‖v‖) * ‖v‖ := by
      intro s hs
      have hs' : s ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self hs
      have hR₁ := (hball _ ((hnorm1 s hs').trans_lt htδ)).2
      have hR₂ := (hball _ ((hnorm2 s hs').trans_lt htδ)).2
      have hgR : fderiv ℝ f (x + (t • u + (s * t) • v)) (t • v) -
          fderiv ℝ f (x + (s * t) • v) (t • v) - L (t • u) (t • v) =
          (fderiv ℝ f (x + (t • u + (s * t) • v)) - fderiv ℝ f x - L (t • u + (s * t) • v))
            (t • v) -
          (fderiv ℝ f (x + (s * t) • v) - fderiv ℝ f x - L ((s * t) • v)) (t • v) := by
        simp only [sub_apply, map_add, add_apply]
        abel
      have htv : ‖t • v‖ = t * ‖v‖ := by rw [norm_smul, Real.norm_of_nonneg ht.le]
      rw [hgR]
      calc _ ≤ ‖(fderiv ℝ f (x + (t • u + (s * t) • v)) - fderiv ℝ f x - L (t • u + (s * t) • v))
              (t • v)‖ +
            ‖(fderiv ℝ f (x + (s * t) • v) - fderiv ℝ f x - L ((s * t) • v)) (t • v)‖ :=
            norm_sub_le _ _
        _ ≤ ‖fderiv ℝ f (x + (t • u + (s * t) • v)) - fderiv ℝ f x - L (t • u + (s * t) • v)‖ *
              ‖t • v‖ + ‖fderiv ℝ f (x + (s * t) • v) - fderiv ℝ f x - L ((s * t) • v)‖ * ‖t • v‖ :=
            add_le_add (ContinuousLinearMap.le_opNorm _ _) (ContinuousLinearMap.le_opNorm _ _)
        _ ≤ ε * (t * (‖u‖ + ‖v‖)) * (t * ‖v‖) + ε * (t * (‖u‖ + ‖v‖)) * (t * ‖v‖) := by
            rw [htv]
            gcongr
            · exact hR₁.trans (mul_le_mul_of_nonneg_left (hnorm1 s hs') hε.le)
            · exact hR₂.trans (mul_le_mul_of_nonneg_left (hnorm2 s hs') hε.le)
        _ = 2 * ε * t ^ 2 * (‖u‖ + ‖v‖) * ‖v‖ := by ring
    have hmvt := norm_image_sub_le_of_norm_deriv_le_segment_01' hderiv hbound
    have hg : f (x + (t • u + (1 * t) • v)) - f (x + (1 * t) • v) - (1 : ℝ) • L (t • u) (t • v) -
        (f (x + (t • u + (0 * t) • v)) - f (x + (0 * t) • v) - (0 : ℝ) • L (t • u) (t • v)) =
        f (x + (t • u + t • v)) - f (x + t • v) - (f (x + t • u) - f x) - t ^ 2 • L u v := by
      simp only [one_mul, zero_mul, zero_smul, add_zero, sub_zero, map_smul, smul_apply, smul_smul,
        sq]
      abel
    rw [← hg]
    exact hmvt
  -- Steps 6–7: exchange `a` and `b`, divide by `t²` and let `ε → 0`.
  have hsymm : ∀ ε > 0, ‖L a b - L b a‖ ≤ 2 * ε * (‖a‖ + ‖b‖) ^ 2 := by
    intro ε hε
    obtain ⟨δ, hδ, hball⟩ := hexp ε hε
    have hpos : 0 < 2 * (‖a‖ + ‖b‖ + 1) := by positivity
    set t : ℝ := δ / (2 * (‖a‖ + ‖b‖ + 1)) with ht_def
    have ht : 0 < t := div_pos hδ hpos
    have htδ : t * (‖a‖ + ‖b‖) < δ := by
      rw [ht_def, div_mul_eq_mul_div, div_lt_iff₀ hpos]
      nlinarith [norm_nonneg a, norm_nonneg b]
    have htδ' : t * (‖b‖ + ‖a‖) < δ := by rwa [add_comm ‖b‖]
    have h1 := hsec ε hε δ hδ hball a b t ht htδ
    have h2 := hsec ε hε δ hδ hball b a t ht htδ'
    have hΔ : f (x + (t • b + t • a)) - f (x + t • a) - (f (x + t • b) - f x) =
        f (x + (t • a + t • b)) - f (x + t • b) - (f (x + t • a) - f x) := by
      rw [add_comm (t • b) (t • a)]
      abel
    rw [hΔ] at h2
    have hkey : t ^ 2 • (L a b - L b a) =
        (f (x + (t • a + t • b)) - f (x + t • b) - (f (x + t • a) - f x) - t ^ 2 • L b a) -
        (f (x + (t • a + t • b)) - f (x + t • b) - (f (x + t • a) - f x) - t ^ 2 • L a b) := by
      rw [smul_sub]
      abel
    have ht2 : 0 < t ^ 2 := by positivity
    have hmul : t ^ 2 * ‖L a b - L b a‖ ≤ t ^ 2 * (2 * ε * (‖a‖ + ‖b‖) ^ 2) := by
      calc t ^ 2 * ‖L a b - L b a‖ = ‖t ^ 2 • (L a b - L b a)‖ := by
            rw [norm_smul, Real.norm_of_nonneg ht2.le]
        _ ≤ 2 * ε * t ^ 2 * (‖b‖ + ‖a‖) * ‖a‖ + 2 * ε * t ^ 2 * (‖a‖ + ‖b‖) * ‖b‖ := by
            rw [hkey]
            exact (norm_sub_le _ _).trans (add_le_add h2 h1)
        _ = t ^ 2 * (2 * ε * (‖a‖ + ‖b‖) ^ 2) := by ring
    exact le_of_mul_le_mul_left hmul ht2
  -- Conclusion: the bound holds for every `ε > 0`.
  apply eq_of_forall_dist_le
  intro ε hε
  have hD : 0 < 2 * (‖a‖ + ‖b‖) ^ 2 + 1 := by positivity
  rw [dist_eq_norm]
  calc ‖L a b - L b a‖ ≤ 2 * (ε / (2 * (‖a‖ + ‖b‖) ^ 2 + 1)) * (‖a‖ + ‖b‖) ^ 2 :=
        hsymm _ (div_pos hε hD)
    _ = ε * (2 * (‖a‖ + ‖b‖) ^ 2 / (2 * (‖a‖ + ‖b‖) ^ 2 + 1)) := by ring
    _ ≤ ε * 1 := by
        gcongr
        rw [div_le_one hD]
        linarith
    _ = ε := mul_one ε
/-- **Invertibility of the Gram operator.** For an injective continuous linear map
`A : ℝⁿ → ℝᴺ`, the Gram operator `G = A* ∘ A` is a unit of the ring `ℝⁿ →L[ℝ] ℝⁿ`, whose
multiplication is composition. If `G w = 0` then `⟪A w, A w⟫ = ⟪w, A* (A w)⟫ = ⟪w, G w⟫ = 0`, so
`A w = 0` and `w = 0` by injectivity of `A`; thus `G` is an injective endomorphism of the
finite-dimensional `ℝⁿ`, i.e. a linear automorphism (`LinearEquiv.ofInjectiveEndo`), which is
continuous with continuous inverse (`LinearEquiv.toContinuousLinearEquiv`), and its unit
(`ContinuousLinearEquiv.toUnit`) has underlying map `G`. -/
theorem Submission.gram_operator_isUnit_of_injective : ∀ (n N : ℕ) (A : Rn n →L[ℝ] Rn N), Function.Injective A → IsUnit (ContinuousLinearMap.adjoint A ∘L A) := by
  intro n N A hA
  -- Step 1: `G` has trivial kernel, since `⟪A w, A w⟫ = ⟪w, A* (A w)⟫ = ⟪w, G w⟫`.
  have hker : ∀ w : Rn n, (ContinuousLinearMap.adjoint A ∘L A) w = 0 → w = 0 := by
    intro w hw
    have h : inner ℝ (A w) (A w) = 0 := by
      rw [← ContinuousLinearMap.adjoint_inner_right]
      exact (congrArg (inner ℝ w) hw).trans (inner_zero_right w)
    exact hA ((inner_self_eq_zero.mp h).trans (map_zero A).symm)
  -- Step 2: `G` is injective, by linearity.
  have hinj : Function.Injective (ContinuousLinearMap.adjoint A ∘L A) := fun u v huv ↦
    sub_eq_zero.mp (hker _ (by rw [map_sub, huv, sub_self]))
  -- Step 3: an injective endomorphism of the finite-dimensional `ℝⁿ` is a continuous linear
  -- automorphism `e`, with `e v = G v` by construction.
  let e : Rn n ≃L[ℝ] Rn n :=
    (LinearEquiv.ofInjectiveEndo (ContinuousLinearMap.adjoint A ∘L A : Rn n →ₗ[ℝ] Rn n)
      hinj).toContinuousLinearEquiv
  -- Step 4: the unit `e.toUnit` of `ℝⁿ →L[ℝ] ℝⁿ` has underlying map `G`.
  exact ⟨e.toUnit, ContinuousLinearMap.ext fun v ↦ rfl⟩

/-- **Simon Ch. 2, 4.26 (p. 60): `B_y` is a symmetric bilinear form with values in `(T_y M)^⊥`.**
Let `M` be an `n`-dimensional `C²` submanifold of `ℝᴺ`. Assume, for every `C²` local representation
`(V, W, ψ)` of `M` and `x ∈ V`, (R) `T_{ψ(x)} M = range Dψ(x)` and (C) the chart formula
`B_{ψ(x)}(Dψ(x)a, Dψ(x)b) = (D²ψ(x)[a, b])^⊥`. Then `B_y(τ, η) = B_y(η, τ)` and `B_y(τ, η) · v = 0`
for `y ∈ M` and `τ, η, v ∈ T_y M`. Take a chart with `y = ψ(x)`; by (R), `τ = Dψ(x)a` and
`η = Dψ(x)b`, so by (C) `B_y(τ, η)` and `B_y(η, τ)` are the normal parts of `D²ψ(x)[a, b]` and
`D²ψ(x)[b, a]`, which agree because `ψ` is `C²` at `x`
(`Submission.fderiv_fderiv_symm_of_contDiffAt`). A normal part `w - P_y w` is orthogonal to `T_y M`. -/
theorem Submission.second_fundamental_form_symm_normal_of_chart_formula : ∀ (n N : ℕ) (M : Set (Rn N)), Chapter02.IsSimonSubmanifold (E := Rn n) 2 M → (∀ (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N), Chapter02.IsSimonLocalRepresentation 2 M V W ψ → ∀ x ∈ V, tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap) → (∀ (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N), Chapter02.IsSimonLocalRepresentation 2 M V W ψ → ∀ x ∈ V, ∀ a b : Rn n, secondFundamentalForm M (ψ x) (fderiv ℝ ψ x a) (fderiv ℝ ψ x b) = normalPart M (ψ x) (fderiv ℝ (fderiv ℝ ψ) x a b)) → ∀ y ∈ M, ∀ τ ∈ tangentSpace M y, ∀ η ∈ tangentSpace M y, secondFundamentalForm M y τ η = secondFundamentalForm M y η τ ∧ ∀ v ∈ tangentSpace M y, inner ℝ (secondFundamentalForm M y τ η) v = 0 := by
  intro n N M hM hR hC y hy τ hτ η hη
  -- Step 1: a `C²` chart `(V, W, ψ)` of `M` with `y ∈ W`, and `x ∈ V` with `ψ x = y`.
  obtain ⟨V, W, ψ, hyW, hψ⟩ := hM.exists_localRepresentation hy
  obtain ⟨x, hx, rfl⟩ : y ∈ ψ '' V := by
    rw [hψ.image_eq]
    exact ⟨hyW, hy⟩
  -- Step 2: by (R), `τ = Dψ(x) a` and `η = Dψ(x) b`.
  rw [hR V W ψ hψ x hx] at hτ hη
  obtain ⟨a, rfl⟩ := hτ
  obtain ⟨b, rfl⟩ := hη
  simp only [ContinuousLinearMap.coe_coe]
  -- Step 3: `ψ` is `C²` at `x`, so `D²ψ(x)[a, b] = D²ψ(x)[b, a]`.
  have hψ2 : ContDiffAt ℝ 2 ψ x := hψ.contDiffOn.contDiffAt (hψ.isOpen_source.mem_nhds hx)
  have hS : fderiv ℝ (fderiv ℝ ψ) x a b = fderiv ℝ (fderiv ℝ ψ) x b a :=
    Submission.fderiv_fderiv_symm_of_contDiffAt n N ψ x hψ2 a b
  -- Step 4: by (C), `B_y(τ, η) = (D²ψ(x)[a, b])^⊥ = (D²ψ(x)[b, a])^⊥ = B_y(η, τ)`.
  rw [hC V W ψ hψ x hx a b, hC V W ψ hψ x hx b a, hS]
  -- Step 5: the normal part `w - P_y w` of `w = D²ψ(x)[b, a]` lies in `(T_y M)^⊥`.
  exact ⟨rfl, fun v hv ↦ Submodule.inner_left_of_mem_orthogonal hv
    (Submodule.sub_starProjection_mem_orthogonal _)⟩
/-- **Derivative of a field normal along `M`** (Simon 5.11 proof: `τᵢ · D_{τⱼ}X = -X · B(τᵢ, τⱼ)`
"by virtue of 4.24 and the fact that `X` is normal to `M`"). Let `M` be an `n`-dimensional `C²`
submanifold such that, on every class-2 chart `ψ`, (R) `T_{ψ(x)}M = range Dψ(x)` and
(C) `B_{ψ(x)}(Dψ(x)a, Dψ(x)b) = (D²ψ(x)[a, b])^⊥`. If `Y` is differentiable at `y ∈ M` and normal
along `M`, then `η · DY(y)τ = -Y(y) · B_y(τ, η)` for all `τ, η ∈ T_y M`. In a chart with `ψ(x) = y`,
`τ = Dψ(x)a` and `η = Dψ(x)b`, the function `x' ↦ Y(ψ(x')) · Dψ(x')b` vanishes on the open set
`V`, so its derivative at `x` in direction `a`, `Y(y) · D²ψ(x)[a, b] + DY(y)τ · η`, is `0`; and
`Y(y) · D²ψ(x)[a, b] = Y(y) · (D²ψ(x)[a, b])^⊥ = Y(y) · B_y(τ, η)` as `Y(y) ⊥ T_y M`. -/
theorem Submission.inner_fderiv_normal_field_eq_neg_second_fundamental_form : ∀ (n N : ℕ) (M : Set (Rn N)), Chapter02.IsSimonSubmanifold (E := Rn n) 2 M → (∀ (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N), Chapter02.IsSimonLocalRepresentation 2 M V W ψ → ∀ x ∈ V, tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap) → (∀ (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N), Chapter02.IsSimonLocalRepresentation 2 M V W ψ → ∀ x ∈ V, ∀ a b : Rn n, secondFundamentalForm M (ψ x) (fderiv ℝ ψ x a) (fderiv ℝ ψ x b) = normalPart M (ψ x) (fderiv ℝ (fderiv ℝ ψ) x a b)) → ∀ (Y : Rn N → Rn N) (y : Rn N), y ∈ M → DifferentiableAt ℝ Y y → (∀ z ∈ M, ∀ v ∈ tangentSpace M z, inner ℝ (Y z) v = 0) → ∀ τ ∈ tangentSpace M y, ∀ η ∈ tangentSpace M y, inner ℝ η (fderiv ℝ Y y τ) = -inner ℝ (Y y) (secondFundamentalForm M y τ η) := by
  intro n N M hM hR hC Y y hy hY hnorm τ hτ η hη
  -- Step 1: a class-2 chart `(V, W, ψ)` and `x ∈ V` with `ψ x = y`; by (R), `τ = Dψ(x) a` and
  -- `η = Dψ(x) b`.
  obtain ⟨V, W, ψ, hyW, hrep⟩ := hM.2 y hy
  obtain ⟨x, hxV, rfl⟩ : y ∈ ψ '' V := hrep.image_eq ▸ ⟨hyW, hy⟩
  rw [hR V W ψ hrep x hxV] at hτ hη
  obtain ⟨a, rfl⟩ := hτ
  obtain ⟨b, rfl⟩ := hη
  simp only [ContinuousLinearMap.coe_coe]
  -- Step 2: `ψ` and `Dψ` are differentiable at `x`; derivatives of `x' ↦ Dψ(x') b` and `Y ∘ ψ`.
  have hV : IsOpen V := hrep.isOpen_source
  have hψ2 : ContDiffAt ℝ 2 ψ x := hrep.contDiffOn.contDiffAt (hV.mem_nhds hxV)
  have hψ : HasFDerivAt ψ (fderiv ℝ ψ x) x := (hψ2.differentiableAt (by norm_num)).hasFDerivAt
  have hDψ : HasFDerivAt (fderiv ℝ ψ) (fderiv ℝ (fderiv ℝ ψ) x) x :=
    ((hψ2.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  have hg := hDψ.clm_apply (hasFDerivAt_const b x)
  have hYψ := hY.hasFDerivAt.comp x hψ
  -- Step 3: `f x' = ⟪Y (ψ x'), Dψ(x') b⟫` vanishes on the open set `V`, so `Df(x) = 0`.
  have hf0 : HasFDerivAt (fun x' => inner ℝ ((Y ∘ ψ) x') (fderiv ℝ ψ x' b))
      (0 : Rn n →L[ℝ] ℝ) x := by
    refine (hasFDerivAt_const (0 : ℝ) x).congr_of_eventuallyEq ?_
    filter_upwards [hV.mem_nhds hxV] with x' hx'
    have hmem : ψ x' ∈ M := (hrep.image_eq ▸ mem_image_of_mem ψ hx').2
    exact hnorm _ hmem _ (by rw [hR V W ψ hrep x' hx']; exact ⟨b, rfl⟩)
  -- Step 4: product rule and uniqueness of the derivative, evaluated at `a`.
  have h4 : inner ℝ (Y (ψ x)) (fderiv ℝ (fderiv ℝ ψ) x a b) +
      inner ℝ (fderiv ℝ Y (ψ x) (fderiv ℝ ψ x a)) (fderiv ℝ ψ x b) = 0 := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      fderivInnerCLM_apply, Function.comp_apply, ContinuousLinearMap.comp_zero, zero_add,
      ContinuousLinearMap.flip_apply, zero_apply] using
      DFunLike.congr_fun ((hYψ.inner ℝ hg).unique hf0) a
  -- Step 5: `Y (ψ x)` is normal, so it only sees the normal part of `D²ψ(x)[a, b]`, which is
  -- `B(τ, η)` by (C).
  have h5 : inner ℝ (Y (ψ x)) (tangentProjection M (ψ x) (fderiv ℝ (fderiv ℝ ψ) x a b)) = 0 :=
    hnorm _ hy _ (Submodule.starProjection_apply_mem _ _)
  rw [hC V W ψ hrep x hxV a b, normalPart, inner_sub_right, h5, sub_zero]
  -- Step 6: symmetry of the real inner product.
  have h6 := real_inner_comm (fderiv ℝ ψ x b) (fderiv ℝ Y (ψ x) (fderiv ℝ ψ x a))
  linarith
/-- **Mean curvature through the Gram operator of a chart** (Simon Ch. 2, 4.27, at one point). Let
`A : ℝⁿ → ℝᴺ` be injective with `T_y M = range A` and `S` bilinear with `B_y(A a, A b) = S(a, b)^⊥`.
With `G = A* ∘ A`, a unit by `Submission.gram_operator_isUnit_of_injective`, and `(eₖ)` the
standard basis of `ℝⁿ`, `H(y) = (∑ₖ,ₗ ⟨eₖ, G⁻¹ eₗ⟩ S(eₖ, eₗ))^⊥`. Choose `aᵢ` with `A aᵢ = τᵢ`;
then `H(y) = (∑ᵢ S(aᵢ, aᵢ))^⊥`, since `v ↦ v^⊥ = (I - P) v` is linear. The adjoint identity gives
`⟨eₖ, aᵢ⟩ = ⟨A G⁻¹ eₖ, τᵢ⟩`, so Parseval in `T_y M` gives
`∑ᵢ ⟨eₖ, aᵢ⟩⟨eₗ, aᵢ⟩ = ⟨A G⁻¹ eₖ, A G⁻¹ eₗ⟩ = ⟨eₖ, G⁻¹ eₗ⟩`; expanding each `aᵢ` in the standard
basis and using the bilinearity of `S` finishes the proof. -/
theorem Submission.mean_curvature_eq_normalPart_gram_trace : ∀ (n N : ℕ) (M : Set (Rn N)) (y : Rn N) (A : Rn n →L[ℝ] Rn N) (S : Rn n →L[ℝ] Rn n →L[ℝ] Rn N), Function.Injective A → tangentSpace M y = LinearMap.range A.toLinearMap → (∀ a b : Rn n, secondFundamentalForm M y (A a) (A b) = normalPart M y (S a b)) → meanCurvature M y = normalPart M y (∑ k : Fin n, ∑ l : Fin n, inner ℝ (EuclideanSpace.single k (1 : ℝ)) (Ring.inverse (ContinuousLinearMap.adjoint A ∘L A) (EuclideanSpace.single l (1 : ℝ))) • S (EuclideanSpace.single k (1 : ℝ)) (EuclideanSpace.single l (1 : ℝ))) := by
  intro n N M y A S hA hT hB
  set G : Rn n →L[ℝ] Rn n := ContinuousLinearMap.adjoint A ∘L A
  -- Step 1: `G` is a unit of `ℝⁿ →L[ℝ] ℝⁿ`, whose multiplication is composition, so
  -- `G (G⁻¹ v) = v`; by the adjoint identity, `⟨G u, w⟩ = ⟨A u, A w⟩`.
  have hGGi : ∀ v : Rn n, G (Ring.inverse G v) = v := fun v ↦ by
    rw [← mul_apply_eq_comp,
      Ring.mul_inverse_cancel _ (Submission.gram_operator_isUnit_of_injective n N A hA),
      one_apply_eq_self]
  have hGinner : ∀ u w : Rn n, inner ℝ (G u) w = inner ℝ (A u) (A w) := fun u w ↦
    ContinuousLinearMap.adjoint_inner_left A w (A u)
  -- Step 2: preimages `aᵢ` of the frame vectors `τᵢ ∈ T_y M = range A`.
  have hτ : ∀ i, ∃ a : Rn n, A a = tangentFrame M y i := fun i ↦ by
    have hi : tangentFrame M y i ∈ tangentSpace M y :=
      ((stdOrthonormalBasis ℝ (tangentSpace M y)) i).2
    rw [hT] at hi
    exact LinearMap.mem_range.mp hi
  choose a ha using hτ
  -- Step 3: `H(y) = ∑ᵢ B(A aᵢ, A aᵢ) = (∑ᵢ S(aᵢ, aᵢ))^⊥`, as `w ↦ w^⊥` is the linear map `I - P`.
  have hnp : ∀ v, normalPart M y v =
      (ContinuousLinearMap.id ℝ (Rn N) - tangentProjection M y) v := fun v ↦ rfl
  have hH : meanCurvature M y = normalPart M y (∑ i, S (a i) (a i)) := by
    rw [hnp, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← ha i, hB, hnp]
  rw [hH]
  congr 1
  -- Step 4: `⟨eₖ, aᵢ⟩ = ⟨G (G⁻¹ eₖ), aᵢ⟩ = ⟨A G⁻¹ eₖ, τᵢ⟩`.
  have hcoord : ∀ k i, inner ℝ (EuclideanSpace.single k (1 : ℝ)) (a i) =
      inner ℝ (A (Ring.inverse G (EuclideanSpace.single k (1 : ℝ)))) (tangentFrame M y i) := by
    intro k i
    rw [← ha i, ← hGinner, hGGi]
  -- Step 5: Parseval in `T_y M` for `uₖ = A G⁻¹ eₖ ∈ T_y M`:
  -- `∑ᵢ ⟨eₖ, aᵢ⟩⟨eₗ, aᵢ⟩ = ⟨uₖ, uₗ⟩ = ⟨G G⁻¹ eₖ, G⁻¹ eₗ⟩ = ⟨eₖ, G⁻¹ eₗ⟩`.
  have hmem : ∀ v, A v ∈ tangentSpace M y := fun v ↦ by
    rw [hT]
    exact LinearMap.mem_range_self _ v
  have hgram : ∀ k l, ∑ i, inner ℝ (EuclideanSpace.single k (1 : ℝ)) (a i) *
      inner ℝ (EuclideanSpace.single l (1 : ℝ)) (a i) =
      inner ℝ (EuclideanSpace.single k (1 : ℝ))
        (Ring.inverse G (EuclideanSpace.single l (1 : ℝ))) := by
    intro k l
    have hP := (stdOrthonormalBasis ℝ (tangentSpace M y)).sum_inner_mul_inner
      ⟨_, hmem (Ring.inverse G (EuclideanSpace.single k (1 : ℝ)))⟩
      ⟨_, hmem (Ring.inverse G (EuclideanSpace.single l (1 : ℝ)))⟩
    simp only [Submodule.coe_inner] at hP
    rw [← hGGi (EuclideanSpace.single k (1 : ℝ)), hGinner, ← hP]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hGGi, hcoord k i, hcoord l i,
      real_inner_comm (tangentFrame M y i) (A (Ring.inverse G (EuclideanSpace.single l (1 : ℝ))))]
    rfl
  -- Step 6: `v = ∑ₖ ⟨eₖ, v⟩ eₖ`, so by bilinearity `S(v, v) = ∑ₖ,ₗ ⟨eₖ, v⟩⟨eₗ, v⟩ S(eₖ, eₗ)`.
  have hexp : ∀ v : Rn n, S v v = ∑ k : Fin n, ∑ l : Fin n,
      (inner ℝ (EuclideanSpace.single k (1 : ℝ)) v *
        inner ℝ (EuclideanSpace.single l (1 : ℝ)) v) •
        S (EuclideanSpace.single k (1 : ℝ)) (EuclideanSpace.single l (1 : ℝ)) := by
    intro v
    have hv : ∑ k : Fin n, inner ℝ (EuclideanSpace.single k (1 : ℝ)) v •
        EuclideanSpace.single k (1 : ℝ) = v := by
      simpa only [EuclideanSpace.basisFun_apply] using
        (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr' v
    conv_lhs => rw [← hv]
    simp only [map_sum, map_smul, sum_apply, smul_apply, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ by rw [mul_comm]
  -- Summing over `i` and exchanging the finite sums, the coefficients are those of step 5.
  calc ∑ i, S (a i) (a i)
      = ∑ i, ∑ k : Fin n, ∑ l : Fin n, (inner ℝ (EuclideanSpace.single k (1 : ℝ)) (a i) *
          inner ℝ (EuclideanSpace.single l (1 : ℝ)) (a i)) •
            S (EuclideanSpace.single k (1 : ℝ)) (EuclideanSpace.single l (1 : ℝ)) :=
        Finset.sum_congr rfl fun i _ ↦ hexp (a i)
    _ = ∑ k : Fin n, ∑ l : Fin n, (∑ i, inner ℝ (EuclideanSpace.single k (1 : ℝ)) (a i) *
          inner ℝ (EuclideanSpace.single l (1 : ℝ)) (a i)) •
            S (EuclideanSpace.single k (1 : ℝ)) (EuclideanSpace.single l (1 : ℝ)) := by
        simp only [Finset.sum_smul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_comm
    _ = _ := by simp only [hgram]

/-- **Simon Ch. 2, 4.27 (p. 60): the mean curvature is continuous in a `C²` chart.** Let
`ψ : V → W` be a `C²` local representation of `M ⊆ ℝᴺ` with `T_{ψ(x)} M = range Dψ(x)` and
`B_{ψ(x)}(Dψ(x)a, Dψ(x)b) = (D²ψ(x)[a, b])^⊥`, and let `y ↦ P_y` be continuous on `M`. By the
Gram trace formula, `H(ψ(x)) = w(x) - P_{ψ(x)} w(x)` on `V`, where `G(x) = Dψ(x)* ∘ Dψ(x)` and
`w(x) = ∑ₖ ∑ₗ ⟪eₖ, G(x)⁻¹ eₗ⟫ D²ψ(x)[eₖ, eₗ]`. Here `Dψ` and `D²ψ` are continuous on the open `V`,
`G` is continuous and unit-valued, `Ring.inverse` is continuous at units, and `x ↦ P_{ψ(x)}` is
continuous because `ψ` maps `V` into `M`. -/
theorem Submission.mean_curvature_comp_chart_continuousOn : ∀ (n N : ℕ) (M : Set (Rn N)) (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N), Chapter02.IsSimonLocalRepresentation 2 M V W ψ → ContinuousOn (tangentProjection M) M → (∀ x ∈ V, tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap) → (∀ x ∈ V, ∀ a b : Rn n, secondFundamentalForm M (ψ x) (fderiv ℝ ψ x a) (fderiv ℝ ψ x b) = normalPart M (ψ x) (fderiv ℝ (fderiv ℝ ψ) x a b)) → ContinuousOn (fun x ↦ meanCurvature M (ψ x)) V := by
  intro n N M V W ψ hψ hP htan hsff
  have hV : IsOpen V := hψ.isOpen_source
  -- Step 1: `Dψ` and `D²ψ` are continuous on the open set `V`, as `ψ` is `C²` there.
  have hA : ContinuousOn (fderiv ℝ ψ) V :=
    hψ.contDiffOn.continuousOn_fderiv_of_isOpen hV (by norm_num)
  have hS : ContinuousOn (fderiv ℝ (fderiv ℝ ψ)) V :=
    (hψ.contDiffOn.fderiv_of_isOpen hV (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen hV
      le_rfl
  -- Step 2: the Gram operator `G(x) = Dψ(x)* ∘ Dψ(x)` is continuous on `V`; it is a unit at each
  -- `x ∈ V` (`Dψ(x)` is injective), and `Ring.inverse` is continuous at units, so `G⁻¹` is too.
  have hG : ContinuousOn (fun x ↦ ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x) V :=
    ((ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Rn n) (F := Rn N)).continuous.comp_continuousOn
      hA).clm_comp hA
  have hGinv : ContinuousOn
      (fun x ↦ Ring.inverse (ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x)) V := by
    intro x hx
    have hu := Submission.gram_operator_isUnit_of_injective n N (fderiv ℝ ψ x)
      (hψ.injective_fderiv hx)
    have hinv := NormedRing.inverse_continuousAt hu.unit
    rw [hu.unit_spec] at hinv
    exact ContinuousAt.comp_continuousWithinAt
      (f := fun x ↦ ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x) hinv (hG x hx)
  -- Step 3: `w(x) = ∑ₖ ∑ₗ ⟪eₖ, G(x)⁻¹ eₗ⟫ • D²ψ(x)[eₖ, eₗ]` is continuous on `V`.
  have hw : ContinuousOn (fun x ↦ ∑ k : Fin n, ∑ l : Fin n,
      inner ℝ (EuclideanSpace.single k (1 : ℝ))
          (Ring.inverse (ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x)
            (EuclideanSpace.single l (1 : ℝ))) •
        fderiv ℝ (fderiv ℝ ψ) x (EuclideanSpace.single k (1 : ℝ))
          (EuclideanSpace.single l (1 : ℝ))) V :=
    continuousOn_finsetSum _ fun k _ ↦ continuousOn_finsetSum _ fun l _ ↦
      (continuousOn_const.inner (hGinv.clm_apply continuousOn_const)).fun_smul
        ((hS.clm_apply continuousOn_const).clm_apply continuousOn_const)
  -- Step 4: `x ↦ P_{ψ(x)}` is continuous on `V`, since `ψ` maps `V` into `M`.
  have hmaps : MapsTo ψ V M := fun x hx ↦ (hψ.image_eq ▸ mem_image_of_mem ψ hx).2
  have hPψ : ContinuousOn (fun x ↦ tangentProjection M (ψ x)) V :=
    hP.comp hψ.contDiffOn.continuousOn hmaps
  -- Step 5: on `V`, `H(ψ(x)) = w(x)^⊥ = w(x) - P_{ψ(x)} w(x)` by the Gram trace formula.
  refine (hw.sub (hPψ.clm_apply hw)).congr fun x hx ↦ ?_
  exact Submission.mean_curvature_eq_normalPart_gram_trace n N M (ψ x) (fderiv ℝ ψ x)
    (fderiv ℝ (fderiv ℝ ψ) x) (hψ.injective_fderiv hx) (htan x hx) (hsff x hx)
/-- **Continuity on a Simon submanifold can be checked in charts.** If `M ⊆ ℝᴺ` is an
`n`-dimensional `C^r` Simon submanifold and `x ↦ F (ψ x)` is continuous on `V` for every chart
`(V, W, ψ)` of `M`, then `F` is continuous on `M`. At `y₀ = ψ x₀ ∈ M`, continuity of `F ∘ ψ` at
`x₀` gives an open `U₀ ∋ x₀` with `F (ψ x) ∈ O` for `x ∈ U₀`. If `closedBall y₀ ε ⊆ W`, relative
properness makes `K = V ∩ ψ⁻¹(closedBall y₀ ε)` compact, so `C = ψ (K \ U₀)` is compact, hence
closed, and `y₀ ∉ C` by injectivity of `ψ` on `V`. As `ψ V = W ∩ M`, every `z` in
`(ball y₀ ε \ C) ∩ M` is `ψ x` with `x ∈ K ∩ U₀`, so `F z ∈ O`. -/
theorem Submission.simon_submanifold_continuousOn_of_chart_continuousOn : ∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)) (X : Type) [TopologicalSpace X] (F : Rn N → X), Chapter02.IsSimonSubmanifold (E := Rn n) r M → (∀ (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N), Chapter02.IsSimonLocalRepresentation r M V W ψ → ContinuousOn (fun x ↦ F (ψ x)) V) → ContinuousOn F M := by
  intro n N r M X _ F hM hF y₀ hy₀
  -- Step 2: a chart `(V, W, ψ)` with `y₀ ∈ W`, and `x₀ ∈ V` with `ψ x₀ = y₀`.
  obtain ⟨V, W, ψ, hy₀W, hψ⟩ := hM.2 y₀ hy₀
  obtain ⟨x₀, hx₀V, rfl⟩ : y₀ ∈ ψ '' V := by
    rw [hψ.image_eq]
    exact ⟨hy₀W, hy₀⟩
  -- Step 1: it suffices that `F ⁻¹' O ∈ 𝓝[M] (ψ x₀)` for each neighbourhood `O` of `F (ψ x₀)`.
  rw [ContinuousWithinAt, Filter.tendsto_def]
  intro O hO
  -- Step 3: `F ∘ ψ` is continuous at `x₀ ∈ V` (`V` is open), so an open `U₀ ∋ x₀` maps into `O`.
  have hFψ : ContinuousAt (fun x ↦ F (ψ x)) x₀ :=
    (hF V W ψ hψ x₀ hx₀V).continuousAt (hψ.isOpen_source.mem_nhds hx₀V)
  obtain ⟨U₀, hU₀O, hU₀, hx₀U₀⟩ := _root_.mem_nhds_iff.mp (hFψ.preimage_mem_nhds hO)
  -- Step 4: `Q = closedBall (ψ x₀) ε ⊆ W`; `K = V ∩ ψ ⁻¹' Q` is compact by relative properness,
  -- so `C = ψ '' (K \ U₀)` is compact, hence closed.
  obtain ⟨ε, hε, hQW⟩ := nhds_basis_closedBall.mem_iff.mp (hψ.isOpen_target.mem_nhds hy₀W)
  have hK : IsCompact (V ∩ ψ ⁻¹' closedBall (ψ x₀) ε) :=
    hψ.isCompact_source_inter_preimage _ (isCompact_closedBall _ _) hQW
  have hC : IsClosed (ψ '' ((V ∩ ψ ⁻¹' closedBall (ψ x₀) ε) \ U₀)) :=
    ((hK.diff hU₀).image_of_continuousOn
      (hψ.contDiffOn.continuousOn.mono fun _ hx ↦ hx.1.1)).isClosed
  -- Step 5: `ψ x₀ ∉ C`, by injectivity of `ψ` on `V`.
  have hx₀C : ψ x₀ ∉ ψ '' ((V ∩ ψ ⁻¹' closedBall (ψ x₀) ε) \ U₀) := by
    rintro ⟨x, ⟨⟨hxV, -⟩, hxU₀⟩, hx⟩
    exact hxU₀ (hψ.injOn hxV hx₀V hx ▸ hx₀U₀)
  -- Steps 6–7: `W₀ = ball (ψ x₀) ε \ C` is open and contains `ψ x₀`; every `z ∈ W₀ ∩ M` is
  -- `ψ x` with `x ∈ K ∩ U₀`, so `F z ∈ O`.
  refine mem_nhdsWithin.mpr ⟨ball (ψ x₀) ε \ ψ '' ((V ∩ ψ ⁻¹' closedBall (ψ x₀) ε) \ U₀),
    isOpen_ball.sdiff hC, ⟨mem_ball_self hε, hx₀C⟩, ?_⟩
  rintro z ⟨⟨hzB, hzC⟩, hzM⟩
  obtain ⟨x, hxV, rfl⟩ : z ∈ ψ '' V := by
    rw [hψ.image_eq]
    exact ⟨hQW (ball_subset_closedBall hzB), hzM⟩
  have hxU₀ : x ∈ U₀ := by
    by_contra hxU₀
    exact hzC ⟨x, ⟨⟨hxV, ball_subset_closedBall hzB⟩, hxU₀⟩, rfl⟩
  exact hU₀O hxU₀
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

/-- **Simon Ch. 2, 4.26–4.27 (p. 60) and the identity in the proof of 5.11 (p. 65): properties of
`B` and `H`.** Assume (TH), the frozen statement of `Submission.simon_submanifold_tangent_basics`,
and let `M` be an `n`-dimensional `C²` submanifold of `ℝᴺ`. Then (i) `B_y(τ, η) = B_y(η, τ)` lies in
`(T_y M)^⊥` for `y ∈ M` and `τ, η ∈ T_y M`; (ii) `y ↦ H(y)` is continuous on `M`; (iii) if `Y` is
differentiable at `y ∈ M` and normal along `M`, then `⟨η, DY(y)τ⟩ = -⟨Y(y), B_y(τ, η)⟩` for
`τ, η ∈ T_y M`. In every `C²` chart `(V, W, ψ)` of `M`, (TH1) gives `T_{ψ(x)} M = range Dψ(x)`, and
`B_{ψ(x)}(Dψ(x)a, Dψ(x)b) = (D²ψ(x)[a, b])^⊥` (`Submission.second_fundamental_form_chart_formula`).
From these two chart facts, (i) is `Submission.second_fundamental_form_symm_normal_of_chart_formula`
and (iii) is `Submission.inner_fderiv_normal_field_eq_neg_second_fundamental_form`. For (ii), with
`G(x) = Dψ(x)* ∘ Dψ(x)`, the map `x ↦ H(ψ(x)) = (∑_{k,l} ⟨e_k, G(x)⁻¹ e_l⟩ D²ψ(x)[e_k, e_l])^⊥` is
continuous on `V` because `z ↦ P_z` is continuous on `M` by (TH2)
(`Submission.mean_curvature_comp_chart_continuousOn`); continuity on `M` can be checked in charts
(`Submission.simon_submanifold_continuousOn_of_chart_continuousOn`). -/
theorem Submission.second_fundamental_form_symm_normal_continuity : ((∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)) (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N), 1 ≤ r → Chapter02.IsSimonLocalRepresentation r M V W ψ → ∀ x ∈ V, tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap) ∧ ∀ (n N : ℕ) (r : ℕ∞) (M : Set (Rn N)), Chapter02.IsSimonSubmanifold (E := Rn n) r M → MeasurableSet M ∧ ContinuousOn (tangentProjection M) M) → ∀ (n N : ℕ) (M : Set (Rn N)), Chapter02.IsSimonSubmanifold (E := Rn n) 2 M → (∀ y ∈ M, ∀ τ ∈ tangentSpace M y, ∀ η ∈ tangentSpace M y, secondFundamentalForm M y τ η = secondFundamentalForm M y η τ ∧ ∀ v ∈ tangentSpace M y, inner ℝ (secondFundamentalForm M y τ η) v = 0) ∧ ContinuousOn (meanCurvature M) M ∧ ∀ (Y : Rn N → Rn N) (y : Rn N), y ∈ M → DifferentiableAt ℝ Y y → (∀ z ∈ M, ∀ v ∈ tangentSpace M z, inner ℝ (Y z) v = 0) → ∀ τ ∈ tangentSpace M y, ∀ η ∈ tangentSpace M y, inner ℝ η (fderiv ℝ Y y τ) = -inner ℝ (Y y) (secondFundamentalForm M y τ η) := by
  intro hTH n N M hM
  -- Step 1 (TH1, class `2 ≥ 1`): `T_{ψ(x)} M = range Dψ(x)` in every `C²` chart of `M`.
  have hR : ∀ (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N),
      Chapter02.IsSimonLocalRepresentation 2 M V W ψ →
        ∀ x ∈ V, tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap :=
    fun V W ψ hψ ↦ hTH.1 n N 2 M V W ψ (by norm_num) hψ
  -- Step 2: `B_{ψ(x)}(Dψ(x)a, Dψ(x)b) = (D²ψ(x)[a, b])^⊥` in every `C²` chart of `M`.
  have hC : ∀ (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N),
      Chapter02.IsSimonLocalRepresentation 2 M V W ψ → ∀ x ∈ V, ∀ a b : Rn n,
        secondFundamentalForm M (ψ x) (fderiv ℝ ψ x a) (fderiv ℝ ψ x b) =
          normalPart M (ψ x) (fderiv ℝ (fderiv ℝ ψ) x a b) :=
    fun V W ψ hψ ↦ Submission.second_fundamental_form_chart_formula hTH n N M V W ψ hψ
  -- Step 3: (i) symmetry and normality of `B` and (iii) the normal-field identity, from Steps 1–2.
  refine ⟨Submission.second_fundamental_form_symm_normal_of_chart_formula n N M hM hR hC, ?_,
    Submission.inner_fderiv_normal_field_eq_neg_second_fundamental_form n N M hM hR hC⟩
  -- Step 4: (ii) `H ∘ ψ` is continuous on `V` for every `C²` chart (TH2: `z ↦ P_z` is continuous on
  -- `M`), and continuity on `M` is checked in charts.
  exact Submission.simon_submanifold_continuousOn_of_chart_continuousOn n N 2 M (Rn N)
    (meanCurvature M) hM fun V W ψ hψ ↦
      Submission.mean_curvature_comp_chart_continuousOn n N M V W ψ hψ (hTH.2 n N 2 M hM).2
        (hR V W ψ hψ) (hC V W ψ hψ)

/-- The frozen Chapter 2 contract: the conjunction of all headline results. -/
theorem main_theorem : LipschitzExtension ∧ Rademacher ∧ C1Approximation ∧ WhitneyExtension ∧ LipschitzImageHausdorff ∧ EilenbergInequality ∧ BVCompactness ∧ BVPoincare ∧ BVExtensionEstimate ∧ AreaFormula ∧ FirstVariation ∧ SecondVariation ∧ StationaryIffMeanCurvatureZero ∧ SecondVariationStationary ∧ CoareaFormula ∧ C1Sard := by sorry

end GMT.Ch02
