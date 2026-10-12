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

/-- **Simon Ch. 2, proof of Theorem 1.5 (p. 44), Lusin's theorem for sets of infinite measure.** If
`S ⊆ ℝⁿ` is Borel and `ν : ℝⁿ → ℝᵐ` is Borel, then for each `ε > 0` there is a closed `C ⊆ S` with
`ν|C` continuous and `Lⁿ(S \ C) < ε` (Simon Ch. 1, Theorem 1.17, extended to `Lⁿ(S) = ∞`). On a
Borel set `E` of finite measure, closed inner approximations (weak regularity of `Lⁿ`) of
`E ∩ ν⁻¹(U)` and `E \ ν⁻¹(U)`, `U` running through a countable basis of `ℝᵐ`, cut out a closed
`F ⊆ E` on which `ν⁻¹(U)` is relatively open for every basic `U`. Applied to `S ∩ P j` for the
bounded shells `P j = {j ≤ |x| < j + 1}`, this gives a locally finite family of closed sets whose
union is the required `C`. -/
theorem Submission.c1approx_lusin_closed_continuousOn : ∀ (n m : ℕ) (S : Set (Rn n)) (ν : Rn n → Rn m), MeasurableSet S → Measurable ν → ∀ ε : ℝ, 0 < ε → ∃ C ⊆ S, IsClosed C ∧ ContinuousOn ν C ∧ volume (S \ C) < ENNReal.ofReal ε := by
  intro n m S ν hS hν ε hε
  -- Lusin on a Borel set `E` of finite measure: a countable basis `b` of `ℝᵐ`, and for each
  -- `U ∈ b` closed `A U ⊆ E ∩ ν⁻¹(U)`, `B U ⊆ E \ ν⁻¹(U)` with `Lⁿ(E \ (A U ∪ B U)) < η U`.
  have fin_lusin : ∀ E : Set (Rn n), MeasurableSet E → volume E ≠ ∞ → ∀ δ : ℝ≥0∞, δ ≠ 0 →
      ∃ F ⊆ E, IsClosed F ∧ ContinuousOn ν F ∧ volume (E \ F) < δ := by
    intro E hE hEfin δ hδ
    obtain ⟨b, hbc, -, hb⟩ := TopologicalSpace.exists_countable_basis (Rn m)
    have : Countable b := hbc.to_subtype
    have hδ2 : δ / 2 ≠ 0 := (ENNReal.half_pos hδ).ne'
    obtain ⟨η, hηpos, hηsum⟩ := ENNReal.exists_pos_sum_of_countable' hδ2 b
    have hAB : ∀ U : b, ∃ A B : Set (Rn n), A ⊆ E ∩ ν ⁻¹' (U : Set (Rn m)) ∧
        B ⊆ E \ ν ⁻¹' (U : Set (Rn m)) ∧ IsClosed A ∧ IsClosed B ∧
        volume (E \ (A ∪ B)) < η U := by
      intro U
      have hU : MeasurableSet (ν ⁻¹' (U : Set (Rn m))) := hν (hb.isOpen U.2).measurableSet
      have hη2 : η U / 2 ≠ 0 := (ENNReal.half_pos (hηpos U).ne').ne'
      obtain ⟨A, hAsub, hAc, hAμ⟩ := (hE.inter hU).exists_isClosed_sdiff_lt
        (ne_top_of_le_ne_top hEfin (measure_mono inter_subset_left)) hη2
      obtain ⟨B, hBsub, hBc, hBμ⟩ := (hE.diff hU).exists_isClosed_sdiff_lt
        (ne_top_of_le_ne_top hEfin (measure_mono sdiff_subset)) hη2
      refine ⟨A, B, hAsub, hBsub, hAc, hBc, ?_⟩
      have hsub : E \ (A ∪ B) ⊆ ((E ∩ ν ⁻¹' (U : Set (Rn m))) \ A) ∪
          ((E \ ν ⁻¹' (U : Set (Rn m))) \ B) := by
        rintro x ⟨hxE, hxAB⟩
        by_cases hx : x ∈ ν ⁻¹' (U : Set (Rn m))
        · exact Or.inl ⟨⟨hxE, hx⟩, fun h ↦ hxAB (Or.inl h)⟩
        · exact Or.inr ⟨⟨hxE, hx⟩, fun h ↦ hxAB (Or.inr h)⟩
      calc volume (E \ (A ∪ B))
          ≤ volume ((E ∩ ν ⁻¹' (U : Set (Rn m))) \ A) +
              volume ((E \ ν ⁻¹' (U : Set (Rn m))) \ B) :=
            (measure_mono hsub).trans (measure_union_le _ _)
        _ < η U / 2 + η U / 2 := ENNReal.add_lt_add hAμ hBμ
        _ = η U := ENNReal.add_halves _
    choose A B hAsub hBsub hAc hBc hABμ using hAB
    obtain ⟨F0, hF0sub, hF0c, hF0μ⟩ := hE.exists_isClosed_sdiff_lt hEfin hδ2
    refine ⟨F0 ∩ ⋂ U, (A U ∪ B U), inter_subset_left.trans hF0sub,
      hF0c.inter (isClosed_iInter fun U ↦ (hAc U).union (hBc U)), ?_, ?_⟩
    · -- For `x ∈ F` and open `t ∋ ν x` pick `U ∈ b` with `ν x ∈ U ⊆ t`; then `(B U)ᶜ` is an
      -- open neighbourhood of `x` whose points in `F` lie in `A U ⊆ ν⁻¹(U)`.
      rw [_root_.continuousOn_iff]
      intro x _ t ht hxt
      obtain ⟨U, hUb, hxU, hUt⟩ := hb.exists_subset_of_mem_open hxt ht
      refine ⟨(B ⟨U, hUb⟩)ᶜ, (hBc _).isOpen_compl, fun hxB ↦ (hBsub _ hxB).2 hxU, ?_⟩
      rintro y ⟨hyB, -, hy⟩
      rcases mem_iInter.1 hy ⟨U, hUb⟩ with hyA | hyB'
      · exact hUt (hAsub _ hyA).2
      · exact absurd hyB' hyB
    · have hsub : E \ (F0 ∩ ⋂ U, (A U ∪ B U)) ⊆ (E \ F0) ∪ ⋃ U, E \ (A U ∪ B U) := by
        rintro x ⟨hxE, hx⟩
        by_cases h0 : x ∈ F0
        · obtain ⟨U, hU⟩ : ∃ U, x ∉ A U ∪ B U := by
            by_contra! hcon
            exact hx ⟨h0, mem_iInter.2 hcon⟩
          exact Or.inr (mem_iUnion.2 ⟨U, hxE, hU⟩)
        · exact Or.inl ⟨hxE, h0⟩
      calc volume (E \ (F0 ∩ ⋂ U, (A U ∪ B U)))
          ≤ volume (E \ F0) + volume (⋃ U, E \ (A U ∪ B U)) :=
            (measure_mono hsub).trans (measure_union_le _ _)
        _ ≤ volume (E \ F0) + ∑' U, volume (E \ (A U ∪ B U)) := by
            gcongr; exact measure_iUnion_le _
        _ < δ / 2 + δ / 2 :=
            ENNReal.add_lt_add hF0μ ((ENNReal.tsum_le_tsum fun U ↦ (hABμ U).le).trans_lt hηsum)
        _ = δ := ENNReal.add_halves δ
  -- The half-open shells `P j = {j ≤ |x| < j + 1}`: Borel, bounded, and covering `ℝⁿ`.
  let P : ℕ → Set (Rn n) := fun j ↦ ball (0 : Rn n) ((j : ℝ) + 1) \ ball 0 (j : ℝ)
  have hPmeas : ∀ j, MeasurableSet (P j) := fun j ↦ measurableSet_ball.diff measurableSet_ball
  have hPfin : ∀ j, volume (S ∩ P j) ≠ ∞ := fun j ↦
    ((measure_mono (inter_subset_right.trans sdiff_subset)).trans_lt measure_ball_lt_top).ne
  have hcover : ∀ x : Rn n, ∃ j, x ∈ P j := by
    intro x
    refine ⟨⌊‖x‖⌋₊, ?_, ?_⟩
    · simp only [mem_ball, dist_zero_right]; exact Nat.lt_floor_add_one _
    · simp only [mem_ball, dist_zero_right, not_lt]; exact Nat.floor_le (norm_nonneg _)
  -- Closed `C j ⊆ S ∩ P j` with `ν|C j` continuous and losses `δ j` summing to less than `ε`.
  obtain ⟨δ, hδpos, hδsum⟩ :=
    ENNReal.exists_pos_sum_of_countable' (ENNReal.ofReal_pos.2 hε).ne' ℕ
  have hpiece : ∀ j, ∃ F ⊆ S ∩ P j, IsClosed F ∧ ContinuousOn ν F ∧
      volume ((S ∩ P j) \ F) < δ j :=
    fun j ↦ fin_lusin _ (hS.inter (hPmeas j)) (hPfin j) _ (hδpos j).ne'
  choose C hCsub hCclosed hCcont hCμ using hpiece
  -- `ball x 1` meets `C j ⊆ P j` only for `j < ⌈|x| + 1⌉`, so the family `C` is locally finite.
  have hlf : LocallyFinite C := by
    intro x
    refine ⟨ball x 1, ball_mem_nhds x one_pos, (Set.finite_Iio ⌈‖x‖ + 1⌉₊).subset ?_⟩
    rintro j ⟨y, hyC, hyx⟩
    have hyP := (hCsub j hyC).2
    simp only [P, Set.mem_sdiff, mem_ball, dist_zero_right, not_lt] at hyP
    rw [mem_ball, dist_eq_norm] at hyx
    have hy : ‖y‖ < ‖x‖ + 1 := by linarith [norm_sub_norm_le y x]
    exact Nat.lt_ceil.2 (lt_of_le_of_lt hyP.2 hy)
  refine ⟨⋃ j, C j, iUnion_subset fun j ↦ (hCsub j).trans inter_subset_left,
    hlf.isClosed_iUnion hCclosed, hlf.continuousOn_iUnion hCclosed hCcont, ?_⟩
  -- `S \ ⋃ j, C j ⊆ ⋃ j, (S ∩ P j) \ C j`, of measure at most `∑ j, δ j < ε`.
  have hsub : S \ ⋃ j, C j ⊆ ⋃ j, (S ∩ P j) \ C j := by
    rintro x ⟨hxS, hxC⟩
    obtain ⟨j, hj⟩ := hcover x
    exact mem_iUnion.2 ⟨j, ⟨hxS, hj⟩, fun h ↦ hxC (mem_iUnion.2 ⟨j, h⟩)⟩
  calc volume (S \ ⋃ j, C j) ≤ ∑' j, volume ((S ∩ P j) \ C j) :=
        (measure_mono hsub).trans (measure_iUnion_le _)
    _ ≤ ∑' j, δ j := ENNReal.tsum_le_tsum fun j ↦ (hCμ j).le
    _ < ENNReal.ofReal ε := hδsum
/-- **Simon Ch. 2, proof of Theorem 1.5 (p. 44), Borel remainder moduli.** For a Lipschitz
`f : ℝⁿ → ℝ`, a Borel `ν : ℝⁿ → ℝⁿ` and any `C ⊆ ℝⁿ` there are Borel functions `η k` with
`|f y - f x - ν(x)·(y - x)| ≤ η k x |y - x|` for `x, y ∈ C`, `0 < |y - x| < 1/(k + 1)`, and
`η k x → 0` at each `x ∈ C` where `f` has derivative `v ↦ ν(x)·v`. Simon's
`η_k(x) = sup {|R(x,y)| : y ∈ C ∩ B_{1/k}(x) \ {x}}` is replaced by the supremum of the quotients
`|R(x,q)|`, `0 < |q - x| < 1/(k + 1)`, over a countable dense `D ⊆ ℝⁿ`; it is Borel, and it
dominates `|R(x,y)|` at every `y` with `0 < |y - x| < 1/(k + 1)` by continuity in `y`. -/
theorem Submission.c1approx_measurable_remainder_modulus : ∀ (n : ℕ) (K : ℝ≥0) (C : Set (Rn n)) (f : Rn n → ℝ) (ν : Rn n → Rn n), LipschitzWith K f → Measurable ν → ∃ η : ℕ → Rn n → ℝ, (∀ k, Measurable (η k)) ∧ (∀ k : ℕ, ∀ x ∈ C, ∀ y ∈ C, 0 < ‖y - x‖ → ‖y - x‖ < 1 / ((k : ℝ) + 1) → |f y - f x - inner ℝ (ν x) (y - x)| ≤ η k x * ‖y - x‖) ∧ ∀ x ∈ C, HasFDerivAt f (innerSL ℝ (ν x)) x → Tendsto (fun k ↦ η k x) atTop (𝓝 0) := by
  intro n K C f ν hf hν
  -- A countable dense set `D ⊆ ℝⁿ`.
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Rn n)
  have : Countable D := hDc.to_subtype
  have : Nonempty D := hDd.nonempty.to_subtype
  -- The remainder quotient `ρ x q = |f q - f x - ν(x)·(q - x)| / |q - x|` lies in `[0, K + |ν x|]`.
  let ρ : Rn n → Rn n → ℝ := fun x q ↦ |f q - f x - inner ℝ (ν x) (q - x)| / ‖q - x‖
  have hρ0 (x q : Rn n) : 0 ≤ ρ x q := by positivity
  have hρK (x q : Rn n) : ρ x q ≤ K + ‖ν x‖ := by
    refine div_le_of_le_mul₀ (norm_nonneg _) (by positivity) ?_
    calc |f q - f x - inner ℝ (ν x) (q - x)| ≤ |f q - f x| + |inner ℝ (ν x) (q - x)| := abs_sub _ _
      _ ≤ K * ‖q - x‖ + ‖ν x‖ * ‖q - x‖ := by
        gcongr
        · rw [← Real.dist_eq, ← dist_eq_norm]
          exact hf.dist_le_mul q x
        · exact abs_real_inner_le_norm _ _
      _ = (K + ‖ν x‖) * ‖q - x‖ := by ring
  -- `φ k q` is `ρ (·) q` on the open set `U k q = {x | 0 < |q - x| < 1/(k + 1)}` and `0` off it;
  -- `η k = sup_{q ∈ D} φ k q`.
  let U : ℕ → Rn n → Set (Rn n) := fun k q ↦ {x | 0 < ‖q - x‖ ∧ ‖q - x‖ < 1 / ((k : ℝ) + 1)}
  have hU (k : ℕ) (q : Rn n) : IsOpen (U k q) :=
    (isOpen_lt continuous_const (continuous_const.sub continuous_id).norm).inter
      (isOpen_lt (continuous_const.sub continuous_id).norm continuous_const)
  let φ : ℕ → Rn n → Rn n → ℝ := fun k q ↦ (U k q).indicator fun x ↦ ρ x q
  have hφ0 (k : ℕ) (q x : Rn n) : 0 ≤ φ k q x := indicator_nonneg (fun x _ ↦ hρ0 x q) x
  have hbdd (k : ℕ) (x : Rn n) : BddAbove (range fun q : D ↦ φ k q x) := by
    refine ⟨K + ‖ν x‖, ?_⟩
    rintro _ ⟨q, rfl⟩
    exact (indicator_le_self' (fun x _ ↦ hρ0 x q) x).trans (hρK x q)
  let η : ℕ → Rn n → ℝ := fun k x ↦ ⨆ q : D, φ k q x
  refine ⟨η, fun k ↦ ?_, fun k x _ y _ hpos hlt ↦ ?_, fun x _ hfd ↦ ?_⟩
  · -- Each `φ k q` is Borel, and `η k` is a countable supremum of them.
    refine Measurable.iSup fun q ↦ Measurable.indicator ?_ (hU k q).measurableSet
    have hfm : Measurable f := hf.continuous.measurable
    exact (continuous_abs.measurable.comp ((measurable_const.sub hfm).sub
      (hν.inner (measurable_const.sub measurable_id)))).div (measurable_const.sub measurable_id).norm
  · -- The `q` with `|f q - f x - ν(x)·(q - x)| ≤ η k x |q - x|` form a closed set containing the
    -- points of `D` in the open set `{q | 0 < |q - x| < 1/(k + 1)}`, which are dense in it.
    have hF : IsClosed {q : Rn n | |f q - f x - inner ℝ (ν x) (q - x)| ≤ η k x * ‖q - x‖} :=
      isClosed_le ((hf.continuous.sub continuous_const).sub
        (continuous_const.inner (continuous_id.sub continuous_const))).abs
        (continuous_const.mul (continuous_id.sub continuous_const).norm)
    have hV : IsOpen {q : Rn n | 0 < ‖q - x‖ ∧ ‖q - x‖ < 1 / ((k : ℝ) + 1)} :=
      (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).inter
        (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const)
    refine closure_minimal (fun q hq ↦ ?_) hF (hDd.open_subset_closure_inter hV ⟨hpos, hlt⟩)
    have hle : φ k q x ≤ η k x := le_ciSup (hbdd k x) ⟨q, hq.2⟩
    rw [show φ k q x = ρ x q from indicator_of_mem hq.1 _] at hle
    exact (div_le_iff₀ hq.1.1).1 hle
  · -- Given `δ > 0`, the `o(|y - x|)` estimate holds on `ball x r`; once `1/(k + 1) < r`, every
    -- `φ k q x` is at most `δ / 2`.
    refine Metric.tendsto_atTop.2 fun δ hδ ↦ ?_
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 (hfd.isLittleO.bound (half_pos hδ))
    obtain ⟨k₀, hk₀⟩ := exists_nat_one_div_lt hr
    refine ⟨k₀, fun k hk ↦ ?_⟩
    have hle : η k x ≤ δ / 2 := by
      refine ciSup_le fun q ↦ indicator_apply_le' (fun hq ↦ ?_) fun _ ↦ (half_pos hδ).le
      have hqr : dist (q : Rn n) x < r := by
        rw [dist_eq_norm]
        exact hq.2.trans_le ((Nat.one_div_le_one_div hk).trans hk₀.le)
      have h := hball hqr
      rw [innerSL_apply_apply, Real.norm_eq_abs] at h
      exact (div_le_iff₀ hq.1).2 h
    have h0 : 0 ≤ η k x := Real.iSup_nonneg fun q ↦ hφ0 k q x
    rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
    exact hle.trans_lt (half_lt_self hδ)
/-- **Simon Ch. 2, proof of Theorem 1.5 (p. 44), Egorov step with a closed set.** If `C ⊆ ℝⁿ` is
Borel and the Borel functions `F k` converge to the Borel function `G` at every point of `C`, then
for each `ε > 0` there is a closed `A ⊆ C` with `Lⁿ(C \ A) < ε` such that `F k → G` uniformly on
every compact subset of `A`. Egorov's theorem on the bounded shells `P j = {j ≤ |x| < j + 1}` and
closed inner approximation (weak regularity of `Lⁿ`) give closed `Fc j ⊆ P j` of total loss `ε/2`
on which `F k → G` uniformly. The family `Fc` is locally finite, so `A = ⋃ j, Fc j` is closed, and
a compact `K ⊆ A` meets only finitely many `Fc j`. -/
theorem Submission.c1approx_egorov_closed_compact_uniform : ∀ (n : ℕ) (C : Set (Rn n)) (F : ℕ → Rn n → ℝ) (G : Rn n → ℝ), MeasurableSet C → (∀ k, Measurable (F k)) → Measurable G → (∀ x ∈ C, Tendsto (fun k ↦ F k x) atTop (𝓝 (G x))) → ∀ ε : ℝ, 0 < ε → ∃ A ⊆ C, IsClosed A ∧ volume (C \ A) < ENNReal.ofReal ε ∧ ∀ K ⊆ A, IsCompact K → TendstoUniformlyOn F G atTop K := by
  intro n C F G hC hF hG hconv ε hε
  -- The shells `P j = {j ≤ |x| < j + 1}`: Borel, bounded, and covering `ℝⁿ`.
  let P : ℕ → Set (Rn n) := fun j ↦ {x | (j : ℝ) ≤ ‖x‖ ∧ ‖x‖ < j + 1}
  have hPmeas (j : ℕ) : MeasurableSet (P j) :=
    (measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_lt measurable_norm measurable_const)
  have hCP (j : ℕ) : MeasurableSet (C ∩ P j) := hC.inter (hPmeas j)
  have hCPfin (j : ℕ) : volume (C ∩ P j) ≠ ∞ :=
    ((measure_mono fun x hx ↦ mem_closedBall_zero_iff.2 hx.2.2.le).trans_lt
      measure_closedBall_lt_top).ne
  have hmemP (x : Rn n) : x ∈ P ⌊‖x‖⌋₊ := ⟨Nat.floor_le (norm_nonneg x), Nat.lt_floor_add_one _⟩
  -- Egorov on `C ∩ P j`, then a closed inner approximation of the good set, each with loss
  -- `η j = ε 2^{-j-3}`.
  let η : ℕ → ℝ≥0∞ := fun j ↦ ENNReal.ofReal (ε / 2 ^ (j + 3))
  have hη (j : ℕ) : 0 < η j := ENNReal.ofReal_pos.2 (by positivity)
  have hEg (j : ℕ) : ∃ t ⊆ C ∩ P j, MeasurableSet t ∧ volume t ≤ η j ∧
      TendstoUniformlyOn F G atTop ((C ∩ P j) \ t) :=
    tendstoUniformlyOn_of_ae_tendsto (fun k ↦ (hF k).stronglyMeasurable) hG.stronglyMeasurable
      (hCP j) (hCPfin j) (ae_of_all _ fun x hx ↦ hconv x hx.1) (hη j)
  choose t _ ht htη htunif using hEg
  have hcl (j : ℕ) : ∃ Fc ⊆ (C ∩ P j) \ t j, IsClosed Fc ∧ volume (((C ∩ P j) \ t j) \ Fc) < η j :=
    ((hCP j).diff (ht j)).exists_isClosed_sdiff_lt
      ((measure_mono sdiff_subset).trans_lt (hCPfin j).lt_top).ne (hη j).ne'
  choose Fc hFc hFcc hFcη using hcl
  have hFcP (j : ℕ) : Fc j ⊆ P j := (hFc j).trans (sdiff_subset.trans inter_subset_right)
  refine ⟨⋃ j, Fc j, iUnion_subset fun j ↦ (hFc j).trans (sdiff_subset.trans inter_subset_left),
    ?_, ?_, ?_⟩
  · -- `ball x 1` meets `Fc j ⊆ P j` only for `j < ⌈|x|⌉ + 1`, so `⋃ j, Fc j` is closed.
    refine LocallyFinite.isClosed_iUnion (fun x ↦ ?_) hFcc
    refine ⟨ball x 1, ball_mem_nhds x one_pos, (finite_lt_nat (⌈‖x‖⌉₊ + 1)).subset ?_⟩
    rintro j ⟨y, hyF, hyx⟩
    have hj : (j : ℝ) ≤ ‖y‖ := (hFcP j hyF).1
    have hy : ‖y‖ - ‖x‖ < 1 := (norm_sub_norm_le y x).trans_lt (mem_ball_iff_norm.1 hyx)
    have hx := Nat.le_ceil ‖x‖
    have : (j : ℝ) < ⌈‖x‖⌉₊ + 1 := by linarith
    exact_mod_cast this
  · -- `C \ ⋃ j, Fc j ⊆ ⋃ j, (t j ∪ (A'_j \ Fc j))` has measure `≤ ∑ j, 2 η j = ε/2 < ε`.
    have hsub : C \ ⋃ j, Fc j ⊆ ⋃ j, (t j ∪ (((C ∩ P j) \ t j) \ Fc j)) := by
      rintro x ⟨hxC, hxA⟩
      refine mem_iUnion.2 ⟨⌊‖x‖⌋₊, ?_⟩
      by_cases hxt : x ∈ t ⌊‖x‖⌋₊
      · exact Or.inl hxt
      · exact Or.inr ⟨⟨⟨hxC, hmemP x⟩, hxt⟩, fun hxF ↦ hxA (mem_iUnion.2 ⟨_, hxF⟩)⟩
    have h2η (j : ℕ) : η j + η j = ENNReal.ofReal (ε / 2 / 2 / 2 ^ j) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    have hsum : ∑' j, (η j + η j) = ENNReal.ofReal (ε / 2) := by
      rw [tsum_congr h2η, ← ENNReal.ofReal_tsum_of_nonneg (fun j ↦ by positivity)
        (summable_geometric_two' _), tsum_geometric_two']
    calc volume (C \ ⋃ j, Fc j)
        ≤ volume (⋃ j, (t j ∪ (((C ∩ P j) \ t j) \ Fc j))) := measure_mono hsub
      _ ≤ ∑' j, volume (t j ∪ (((C ∩ P j) \ t j) \ Fc j)) := measure_iUnion_le _
      _ ≤ ∑' j, (η j + η j) := ENNReal.tsum_le_tsum fun j ↦
          (measure_union_le _ _).trans (add_le_add (htη j) (hFcη j).le)
      _ = ENNReal.ofReal (ε / 2) := hsum
      _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith)
  · -- A compact `K ⊆ A` lies in `closedBall 0 J`, hence in `Fc 0 ∪ ⋯ ∪ Fc J`, and the uniform
    -- convergence on the finitely many good sets `A'_j`, `j ≤ J`, passes to `K`.
    intro K hKA hK
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
    obtain ⟨J, hJ⟩ := exists_nat_ge R
    intro u hu
    have hev : ∀ᶠ k in atTop, ∀ j ∈ Finset.range (J + 1), ∀ x, x ∈ (C ∩ P j) \ t j →
        (G x, F k x) ∈ u :=
      (eventually_all_finset _).2 fun j _ ↦ htunif j u hu
    filter_upwards [hev] with k hk x hx
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hKA hx)
    have h1 : (j : ℝ) ≤ ‖x‖ := (hFcP j hj).1
    have h2 : ‖x‖ ≤ R := mem_closedBall_zero_iff.1 (hR hx)
    have hjJ : (j : ℝ) ≤ J := by linarith
    exact hk j (Finset.mem_range_succ_iff.2 (by exact_mod_cast hjJ)) x (hFc j hj)
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

/-- **Simon Ch. 2, Theorem 1.5 (p. 42), `C¹` approximation**, by the printed proof (p. 44).
`f` is differentiable on a co-null Borel set `B` (Rademacher 1.4) with Borel gradient `ν`. Lusin
gives a closed `C ⊆ B` with `ν|C` continuous and `Lⁿ(B ∖ C) < ε/2`. The remainder moduli `η_k`
of `f` on `C` tend to `0` on `C`, and Egorov gives a closed `A ⊆ C` with `Lⁿ(C ∖ A) < ε/2` on
whose compact subsets `η_k → 0` uniformly. That is the hypothesis of Whitney 1.6 for `(A, f, ν)`,
and the resulting `C¹` function `g` satisfies `g = f` and `Dg = Df` on `A`, where
`Lⁿ(ℝⁿ ∖ A) < ε`. -/
theorem Submission.c1_approximation_theorem : C1Approximation := by
  intro n f hf ε hε
  obtain ⟨K, hK⟩ := hf
  -- Steps 1–2: `B = {x | DifferentiableAt ℝ f x}` is Borel and co-null, `ν = ∇f` is Borel.
  have hB : MeasurableSet {x : Rn n | DifferentiableAt ℝ f x} :=
    measurableSet_of_differentiableAt ℝ f
  have hB_null : volume {x : Rn n | ¬ DifferentiableAt ℝ f x} = 0 :=
    ae_iff.1 (Submission.lipschitz_extension_and_rademacher.2 n f ⟨K, hK⟩)
  obtain ⟨ν, hν, hν_fderiv⟩ : ∃ ν : Rn n → Rn n, Measurable ν ∧
      ∀ x, innerSL ℝ (ν x) = fderiv ℝ f x :=
    ⟨fun x ↦ (InnerProductSpace.toDual ℝ (Rn n)).symm (fderiv ℝ f x),
      (InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.measurable.comp (measurable_fderiv ℝ f),
      fun x ↦ ContinuousLinearMap.ext fun v ↦ by
        rw [innerSL_apply_apply, InnerProductSpace.toDual_symm_apply]⟩
  -- Step 3 (Lusin): a closed `C ⊆ B` with `ν|C` continuous and `Lⁿ(B ∖ C) < ε/2`.
  obtain ⟨C, hCB, hC, hνC, hBC⟩ :=
    Submission.c1approx_lusin_closed_continuousOn n n _ ν hB hν (ε / 2) (half_pos hε)
  have hCf : ∀ x ∈ C, HasFDerivAt f (fderiv ℝ f x) x := fun x hx ↦
    DifferentiableAt.hasFDerivAt (hCB hx)
  -- Step 4: Borel remainder moduli `η_k` on `C`, tending to `0` at every point of `C`.
  obtain ⟨η, hη, hη_le, hη_lim⟩ :=
    Submission.c1approx_measurable_remainder_modulus n K C f ν hK hν
  -- Steps 5–6 (Egorov): a closed `A ⊆ C` with `Lⁿ(C ∖ A) < ε/2` and `η_k → 0` uniformly on
  -- every compact subset of `A`.
  obtain ⟨A, hAC, hA, hCA, hA_unif⟩ :=
    Submission.c1approx_egorov_closed_compact_uniform n C η (fun _ ↦ 0) hC.measurableSet hη
      measurable_const (fun x hx ↦ hη_lim x hx (by rw [hν_fderiv]; exact hCf x hx)) (ε / 2)
      (half_pos hε)
  -- Step 7: the hypothesis of Whitney's theorem for `(A, f, ν)`, with `δ = 1 / (k + 1)`.
  have hW : ∀ L ⊆ A, IsCompact L → ∀ ε' : ℝ, 0 < ε' → ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ L, ∀ y ∈ A,
      0 < ‖y - x‖ → ‖y - x‖ < δ → |f y - f x - inner ℝ (ν x) (y - x)| ≤ ε' * ‖y - x‖ := by
    intro L hLA hL ε' hε'
    obtain ⟨k, hk⟩ := eventually_atTop.1
      (Metric.tendstoUniformlyOn_iff.1 (hA_unif L hLA hL) ε' hε')
    refine ⟨1 / ((k : ℝ) + 1), by positivity, fun x hx y hy hxy hxyk ↦ ?_⟩
    have hηk : η k x < ε' := by
      have h := hk k le_rfl x hx
      simp only [Real.dist_eq, zero_sub, abs_neg] at h
      exact (le_abs_self _).trans_lt h
    calc |f y - f x - inner ℝ (ν x) (y - x)| ≤ η k x * ‖y - x‖ :=
          hη_le k x (hAC (hLA hx)) y (hAC hy) hxy hxyk
      _ ≤ ε' * ‖y - x‖ := mul_le_mul_of_nonneg_right hηk.le (norm_nonneg _)
  obtain ⟨g, hg, hgA⟩ :=
    Submission.whitney_extension_theorem n A f ν hA hK.continuous.continuousOn (hνC.mono hAC) hW
  refine ⟨g, hg, ?_⟩
  -- Step 8: the exceptional set lies in `ℝⁿ ∖ A ⊆ (ℝⁿ ∖ B) ∪ (B ∖ C) ∪ (C ∖ A)`.
  have hsub : {x | f x ≠ g x} ∪ {x | ¬ HasFDerivAt f (fderiv ℝ g x) x} ⊆
      {x | ¬ DifferentiableAt ℝ f x} ∪ ({x | DifferentiableAt ℝ f x} \ C) ∪ (C \ A) := by
    intro x hx
    by_cases hxA : x ∈ A
    · obtain ⟨hgx, hDg⟩ := hgA x hxA
      have hfg : fderiv ℝ g x = fderiv ℝ f x := by
        rw [← hν_fderiv]
        ext v
        rw [hDg v, innerSL_apply_apply]
      rcases hx with hx | hx
      · exact (hx hgx.symm).elim
      · exact (hx (hfg ▸ hCf x (hAC hxA))).elim
    · by_cases hxC : x ∈ C
      · exact Or.inr ⟨hxC, hxA⟩
      · by_cases hxB : DifferentiableAt ℝ f x
        · exact Or.inl (Or.inr ⟨hxB, hxC⟩)
        · exact Or.inl (Or.inl hxB)
  calc volume ({x | f x ≠ g x} ∪ {x | ¬ HasFDerivAt f (fderiv ℝ g x) x})
      ≤ volume ({x | ¬ DifferentiableAt ℝ f x} ∪ ({x | DifferentiableAt ℝ f x} \ C) ∪ (C \ A)) :=
        measure_mono hsub
    _ ≤ volume {x | ¬ DifferentiableAt ℝ f x} + volume ({x | DifferentiableAt ℝ f x} \ C) +
          volume (C \ A) :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
        rw [hB_null, zero_add]
        exact ENNReal.add_lt_add hBC hCA
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le, add_halves]
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
/-- **Simon Ch. 2, proof of Theorem 1.9 (p. 46), isodiametric step.** If `f : X → ℝᵐ` is
`K`-Lipschitz on `D`, then `Lᵐ(closure f(D)) ≤ ω_m Kᵐ (diam D)ᵐ / 2ᵐ`: the closed set `closure f(D)` has
diameter `diam f(D) ≤ K diam D`, and the isodiametric inequality (Simon Ch. 1, 2.10)
`Lᵐ(A) ≤ ω_m (diam A / 2)ᵐ` is applied to it. The isodiametric inequality is proved inline:
successive coordinate Steiner symmetrizations of a compact set (Fubini for the volume, a slice
estimate for the diameter) give a centrally symmetric compact set, which lies in a ball of radius
`diam / 2`; the ball volume `ω_m rᵐ` comes from the Gaussian integral and the `Γ` integral. -/
theorem Submission.eilenberg_covering_lipschitz_image_volume_le : ∀ (X : Type) [MetricSpace X] (m : ℕ) (D : Set X) (f : X → Rn m) (K : ℝ≥0), LipschitzOnWith K f D → volume (closure (f '' D)) ≤ Chapter01.realUnitBallVolume (m : ℝ) * (K : ℝ≥0∞) ^ m * ediam D ^ m / (2 : ℝ≥0∞) ^ m := by
  intro X _ m D f K hf
  -- `diam f(D) ≤ K diam D`.
  have hfD : ediam (f '' D) ≤ K * ediam D := by
    refine ediam_le ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩
    calc edist (f x) (f x') ≤ K * edist x x' := hf hx hx'
      _ ≤ K * ediam D := by gcongr; exact edist_le_ediam_of_mem hx hx'
  rcases m with _ | n
  · -- `ℝ⁰` is a single point of volume one.
    simp only [pow_zero, mul_one, div_one, Nat.cast_zero, Chapter01.realUnitBallVolume_zero]
    calc volume (closure (f '' D)) ≤ volume (univ : Set (Rn 0)) := measure_mono (subset_univ _)
      _ = 1 := by rw [volume_euclideanSpace_eq_dirac, measure_univ]
  -- The unit ball of `ℝⁿ⁺¹` has volume `ω_{n+1}`.
  have hball : volume (ball (0 : Rn (n + 1)) 1) = Chapter01.realUnitBallVolume ((n + 1 : ℕ) : ℝ) := by
    -- The Gaussian integral `∫ exp (-‖x‖²) = π^{(n+1)/2}`, by Tonelli over the coordinates.
    have hG1 : ∫⁻ t : ℝ, ENNReal.ofReal (Real.exp (-t ^ 2)) = ENNReal.ofReal (√Real.pi) := by
      have h := integral_gaussian 1
      rw [div_one] at h
      rw [← h, ofReal_integral_eq_lintegral_ofReal (integrable_exp_neg_mul_sq one_pos)
        (ae_of_all _ fun t => (Real.exp_pos _).le)]
      simp only [neg_mul, one_mul]
    have hprod : ∀ k : ℕ, ∫⁻ y : Fin k → ℝ, ∏ i, ENNReal.ofReal (Real.exp (-y i ^ 2)) =
        ENNReal.ofReal (√Real.pi) ^ k := by
      have hg : Measurable fun t : ℝ => ENNReal.ofReal (Real.exp (-t ^ 2)) := by fun_prop
      intro k
      induction k with
      | zero => simp [volume_pi]
      | succ k ih =>
        rw [← ((volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0).symm).lintegral_comp_emb
          (MeasurableEquiv.measurableEmbedding _)]
        simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply,
          Fin.prod_univ_succ, Fin.insertNth_zero', Fin.cons_zero, Fin.cons_succ]
        rw [show (volume : Measure (ℝ × (Fin k → ℝ))) = volume.prod volume from rfl,
          lintegral_prod_mul (g := fun z : Fin k → ℝ => ∏ i, ENNReal.ofReal (Real.exp (-z i ^ 2)))
            hg.aemeasurable (Finset.measurable_prod _ fun i _ => hg.comp (measurable_pi_apply i)).aemeasurable,
          hG1, ih, pow_succ']
    have hgauss : ∫⁻ x : Rn (n + 1), ENNReal.ofReal (Real.exp (-‖x‖ ^ 2)) =
        ENNReal.ofReal (√Real.pi) ^ (n + 1) := by
      rw [← (PiLp.volume_preserving_toLp (Fin (n + 1))).lintegral_comp (by fun_prop), ← hprod]
      congr 1
      funext y
      rw [EuclideanSpace.norm_sq_eq, ← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le),
        ← Real.exp_sum, ← Finset.sum_neg_distrib]
      simp [Real.norm_eq_abs, sq_abs]
    -- Layer cake: `exp (-‖x‖²) = ∫_{‖x‖²}^∞ e^{-t} dt`, then Tonelli and the `Γ` integral.
    set V := volume (ball (0 : Rn (n + 1)) 1)
    have hlayer : ∫⁻ x : Rn (n + 1), ENNReal.ofReal (Real.exp (-‖x‖ ^ 2)) =
        V * ENNReal.ofReal (Real.Gamma (((n + 1 : ℕ) : ℝ) / 2 + 1)) := by
      let F : Rn (n + 1) × ℝ → ℝ≥0∞ :=
        {p | ‖p.1‖ ^ 2 < p.2}.indicator fun p => ENNReal.ofReal (Real.exp (-p.2))
      have hF : Measurable F :=
        (by fun_prop : Measurable fun p : Rn (n + 1) × ℝ => ENNReal.ofReal (Real.exp (-p.2))).indicator
          (measurableSet_lt (by fun_prop) (by fun_prop))
      have hpt : ∀ x : Rn (n + 1), ENNReal.ofReal (Real.exp (-‖x‖ ^ 2)) = ∫⁻ t in Ioi 0, F (x, t) := by
        intro x
        rw [← integral_exp_neg_Ioi, ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi _)
          (ae_of_all _ fun t => (Real.exp_pos _).le)]
        change _ = ∫⁻ t in Ioi 0, (Ioi (‖x‖ ^ 2)).indicator (fun t => ENNReal.ofReal (Real.exp (-t))) t
        rw [lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
          inter_eq_left.mpr (Ioi_subset_Ioi (by positivity))]
      have hslice : ∀ t ∈ Ioi (0 : ℝ), ∫⁻ x, F (x, t) =
          ENNReal.ofReal (Real.exp (-t) * t ^ (((n + 1 : ℕ) : ℝ) / 2)) * V := by
        intro t ht
        have hset : {x : Rn (n + 1) | ‖x‖ ^ 2 < t} = ball 0 (√t) := by
          ext x
          rw [mem_ofPred_eq, mem_ball_zero_iff, Real.lt_sqrt (norm_nonneg x)]
        change ∫⁻ x, {x : Rn (n + 1) | ‖x‖ ^ 2 < t}.indicator (fun _ => ENNReal.ofReal (Real.exp (-t))) x = _
        rw [hset, lintegral_indicator_const measurableSet_ball,
          Measure.addHaar_ball_of_pos _ _ (Real.sqrt_pos.mpr ht), finrank_euclideanSpace_fin, ← mul_assoc,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
          ← Real.rpow_mul (le_of_lt ht), one_div_mul_eq_div]
      calc ∫⁻ x : Rn (n + 1), ENNReal.ofReal (Real.exp (-‖x‖ ^ 2))
          = ∫⁻ x, ∫⁻ t in Ioi 0, F (x, t) := lintegral_congr fun x => hpt x
        _ = ∫⁻ t in Ioi 0, ∫⁻ x, F (x, t) := lintegral_lintegral_swap hF.aemeasurable
        _ = ∫⁻ t in Ioi 0, ENNReal.ofReal (Real.exp (-t) * t ^ (((n + 1 : ℕ) : ℝ) / 2)) * V :=
          setLIntegral_congr_fun measurableSet_Ioi hslice
        _ = V * ENNReal.ofReal (Real.Gamma (((n + 1 : ℕ) : ℝ) / 2 + 1)) := by
          rw [lintegral_mul_const _ (by fun_prop), mul_comm, Real.Gamma_eq_integral (by positivity),
            add_sub_cancel_right, ofReal_integral_eq_lintegral_ofReal
              (by
                have h := Real.GammaIntegral_convergent (s := ((n + 1 : ℕ) : ℝ) / 2 + 1) (by positivity)
                rwa [add_sub_cancel_right] at h)
              (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
                have : (0 : ℝ) < t := ht
                positivity)]
    have hGpos : 0 < Real.Gamma (((n + 1 : ℕ) : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
    rw [hgauss] at hlayer
    rw [Chapter01.realUnitBallVolume, ENNReal.ofReal_div_of_pos hGpos, ENNReal.eq_div_iff
      (ENNReal.ofReal_pos.mpr hGpos).ne' ENNReal.ofReal_ne_top, mul_comm, ← hlayer,
      ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul Real.pi_pos.le]
    congr 2
    ring
  -- A compact set has a centrally symmetric compact replacement with no larger diameter and no
  -- smaller volume (successive coordinate Steiner symmetrizations).
  have hrep : ∀ A₀ : Set (Rn (n + 1)), IsCompact A₀ → ∃ L : Set (Rn (n + 1)), IsCompact L ∧
      ediam L ≤ ediam A₀ ∧ volume A₀ ≤ volume L ∧ ∀ x ∈ L, -x ∈ L := by
    intro A₀ hA₀
    -- One-dimensional step: centering two real slices keeps every cross distance `≤ d`.
    have hcen : ∀ (S T : Set ℝ) (d x y : ℝ), (∀ a ∈ S, ∀ b ∈ T, dist a b ≤ d) → S.Nonempty →
        T.Nonempty → |x| ≤ (volume S).toReal / 2 → |y| ≤ (volume T).toReal / 2 → dist x y ≤ d := by
      intro S T d x y hST ⟨a₀, ha₀⟩ ⟨b₀, hb₀⟩ hx hy
      have hab : ∀ a ∈ S, ∀ b ∈ T, a - b ≤ d ∧ b - a ≤ d := fun a ha b hb =>
        abs_sub_le_iff.mp (by simpa only [Real.dist_eq] using hST a ha b hb)
      have hbl : BddBelow S := ⟨b₀ - d, fun a ha => by linarith [(hab a ha b₀ hb₀).2]⟩
      have hbu : BddAbove S := ⟨b₀ + d, fun a ha => by linarith [(hab a ha b₀ hb₀).1]⟩
      have hT : ∀ b ∈ T, sSup S - d ≤ b ∧ b ≤ sInf S + d := fun b hb =>
        ⟨by linarith [csSup_le ⟨a₀, ha₀⟩ fun a ha => (by linarith [(hab a ha b hb).1] : a ≤ b + d)],
          by linarith [le_csInf ⟨a₀, ha₀⟩ fun a ha => (by linarith [(hab a ha b hb).2] : b - d ≤ a)]⟩
      have h1 : (volume S).toReal ≤ sSup S - sInf S := by
        refine ENNReal.toReal_le_of_le_ofReal (by linarith [csInf_le hbl ha₀, le_csSup hbu ha₀]) ?_
        rw [← Real.volume_Icc]
        exact measure_mono (subset_Icc_csInf_csSup hbl hbu)
      have h2 : (volume T).toReal ≤ sInf S + d - (sSup S - d) := by
        refine ENNReal.toReal_le_of_le_ofReal (by linarith [hT b₀ hb₀]) ?_
        rw [← Real.volume_Icc]
        exact measure_mono fun b hb => hT b hb
      rw [Real.dist_eq]
      linarith [abs_sub x y]
    -- Changing the `j`-th coordinate changes squared distances only in that coordinate.
    have hupd : ∀ (j : Fin (n + 1)) (x y : Rn (n + 1)) (a b : ℝ),
        dist (WithLp.toLp 2 (Function.update x.ofLp j a)) (WithLp.toLp 2 (Function.update y.ofLp j b)) ^ 2 =
          dist x y ^ 2 - dist (x j) (y j) ^ 2 + dist a b ^ 2 := by
      intro j x y a b
      rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ j),
        ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
      simp only [Function.update_self]
      rw [Finset.sum_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi),
        Function.update_of_ne (Finset.ne_of_mem_erase hi)]]
      ring
    -- Coordinate Steiner symmetrization: each slice along the `j`-th axis is replaced by the
    -- centered closed interval of the same length.
    let St : Fin (n + 1) → Set (Rn (n + 1)) → Set (Rn (n + 1)) := fun j A =>
      {x | {t : ℝ | WithLp.toLp 2 (Function.update x.ofLp j t) ∈ A}.Nonempty ∧
        |x j| ≤ (volume {t : ℝ | WithLp.toLp 2 (Function.update x.ofLp j t) ∈ A}).toReal / 2}
    have hdiam : ∀ (j : Fin (n + 1)) (A : Set (Rn (n + 1))), ediam (St j A) ≤ ediam A := by
      intro j A
      by_cases hfin : ediam A = ∞
      · rw [hfin]
        exact le_top
      have hbdd : Bornology.IsBounded A := isBounded_iff_ediam_ne_top.mpr hfin
      rw [← ENNReal.ofReal_toReal hfin]
      refine ediam_le_of_forall_dist_le fun x hx y hy => ?_
      obtain ⟨⟨a₀, ha₀⟩, hx⟩ := hx
      obtain ⟨⟨b₀, hb₀⟩, hy⟩ := hy
      have hsq : ∀ a ∈ {t : ℝ | WithLp.toLp 2 (Function.update x.ofLp j t) ∈ A},
          ∀ b ∈ {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A},
          dist a b ^ 2 ≤ (ediam A).toReal ^ 2 - dist x y ^ 2 + dist (x j) (y j) ^ 2 := by
        intro a ha b hb
        have h := pow_le_pow_left₀ dist_nonneg (dist_le_diam_of_mem hbdd ha hb) 2
        rw [hupd] at h
        change _ ≤ (ediam A).toReal ^ 2 at h
        linarith
      have hD := (sq_nonneg _).trans (hsq a₀ ha₀ b₀ hb₀)
      have hc := hcen _ _ _ (x j) (y j) (fun a ha b hb => Real.le_sqrt_of_sq_le (hsq a ha b hb))
        ⟨a₀, ha₀⟩ ⟨b₀, hb₀⟩ hx hy
      have h2 := pow_le_pow_left₀ dist_nonneg hc 2
      rw [Real.sq_sqrt hD] at h2
      exact (pow_le_pow_iff_left₀ dist_nonneg ENNReal.toReal_nonneg two_ne_zero).mp (by linarith)
    have hvol : ∀ (j : Fin (n + 1)) (A : Set (Rn (n + 1))), IsCompact A → volume A ≤ volume (St j A) := by
      intro j A hA
      set S := St j A
      -- `ℝⁿ⁺¹ ≃ ℝ × ℝⁿ`, splitting off the `j`-th coordinate, preserves volume.
      let φ : ℝ × (Fin n → ℝ) → Rn (n + 1) := fun p =>
        WithLp.toLp 2 ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) j).symm p)
      have hφ : MeasurePreserving φ volume volume := (PiLp.volume_preserving_toLp (Fin (n + 1))).comp
        (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) j).symm
      have hφj (t : ℝ) (z : Fin n → ℝ) : φ (t, z) j = t :=
        Fin.insertNth_apply_same (α := fun _ : Fin (n + 1) => ℝ) j t z
      have hφsl (t : ℝ) (z : Fin n → ℝ) :
          {s : ℝ | WithLp.toLp 2 (Function.update (φ (t, z)).ofLp j s) ∈ A} = (fun s => φ (s, z)) ⁻¹' A := by
        ext s
        change WithLp.toLp 2 (Function.update (j.insertNth t z) j s) ∈ A ↔ WithLp.toLp 2 (j.insertNth s z) ∈ A
        rw [Fin.update_insertNth]
      have hT := measurableSet_toMeasurable volume S
      calc volume A = volume (φ ⁻¹' A) := (hφ.measure_preimage hA.measurableSet.nullMeasurableSet).symm
        _ = ∫⁻ z, volume ((fun t => φ (t, z)) ⁻¹' A) :=
          Measure.prod_apply_symm (hA.measurableSet.preimage hφ.measurable)
        _ ≤ ∫⁻ z, volume ((fun t => φ (t, z)) ⁻¹' toMeasurable volume S) := lintegral_mono fun z => ?_
        _ = volume (φ ⁻¹' toMeasurable volume S) := (Measure.prod_apply_symm (hT.preimage hφ.measurable)).symm
        _ = volume S := by rw [hφ.measure_preimage hT.nullMeasurableSet, measure_toMeasurable]
      -- Each slice has the length of its centered interval, which lies in the slice of `S`.
      rcases eq_empty_or_nonempty ((fun t => φ (t, z)) ⁻¹' A) with h | h
      · rw [h, measure_empty]
        exact zero_le
      have hfin : volume ((fun t => φ (t, z)) ⁻¹' A) ≠ ∞ := by
        refine ne_top_of_le_ne_top ((hA.image (by fun_prop : Continuous fun x : Rn (n + 1) => x j)).measure_lt_top.ne)
          (measure_mono fun t ht => ⟨φ (t, z), ht, hφj t z⟩)
      calc volume ((fun t => φ (t, z)) ⁻¹' A)
          = volume (Icc (-((volume ((fun t => φ (t, z)) ⁻¹' A)).toReal / 2))
              ((volume ((fun t => φ (t, z)) ⁻¹' A)).toReal / 2)) := by
            rw [Real.volume_Icc, sub_neg_eq_add, add_halves, ENNReal.ofReal_toReal hfin]
        _ ≤ _ := measure_mono fun t ht => subset_toMeasurable volume S
            ⟨by rw [hφsl]; exact h, by rw [hφj, hφsl]; exact abs_le.mpr ht⟩
    -- Symmetrization along `j` creates symmetry under sign changes of the `j`-th coordinate and
    -- keeps the sign-change symmetries already present.
    have hsym : ∀ (j : Fin (n + 1)) (s : Finset (Fin (n + 1))) (A : Set (Rn (n + 1))),
        (∀ x ∈ A, ∀ y : Rn (n + 1), (∀ k, y k = x k ∨ (k ∈ s ∧ y k = -x k)) → y ∈ A) →
        ∀ x ∈ closure (St j A), ∀ y : Rn (n + 1), (∀ k, y k = x k ∨ (k ∈ insert j s ∧ y k = -x k)) →
          y ∈ closure (St j A) := by
      intro j s A hA x hx y hy
      let σ : Rn (n + 1) → Rn (n + 1) := fun z => WithLp.toLp 2 fun k => if y k = x k then z k else -z k
      have hσ : Continuous σ :=
        (PiLp.continuous_toLp 2 _).comp (continuous_pi fun k => by split_ifs <;> fun_prop)
      have hσx : σ x = y := by
        ext k
        change (if y k = x k then x k else -x k) = y k
        split_ifs with h
        exacts [h.symm, ((hy k).resolve_left h).2.symm]
      rw [← hσx]
      refine map_mem_closure hσ hx fun z hz => ?_
      -- the slices of `A` through `z` and `σ z` along `j` agree
      have hsl : {t : ℝ | WithLp.toLp 2 (Function.update (σ z).ofLp j t) ∈ A} =
          {t : ℝ | WithLp.toLp 2 (Function.update z.ofLp j t) ∈ A} := by
        ext t
        constructor <;> intro ht <;> refine hA _ ht _ fun k => ?_
        all_goals
          by_cases hk : k = j
          · subst hk
            simp
          by_cases h : y k = x k
          · simp [σ, Function.update_of_ne hk, h]
          exact Or.inr ⟨(Finset.mem_insert.mp ((hy k).resolve_left h).1).resolve_left hk,
            by simp [σ, Function.update_of_ne hk, h]⟩
      obtain ⟨hne, habs⟩ := hz
      refine ⟨hsl ▸ hne, ?_⟩
      rw [hsl]
      by_cases h : y j = x j <;> simpa [σ, h] using habs
    -- Symmetrize successively in every coordinate.
    have hsteps : ∀ s : Finset (Fin (n + 1)), ∃ M : Set (Rn (n + 1)), IsCompact M ∧ ediam M ≤ ediam A₀ ∧
        volume A₀ ≤ volume M ∧ ∀ x ∈ M, ∀ y : Rn (n + 1), (∀ k, y k = x k ∨ (k ∈ s ∧ y k = -x k)) → y ∈ M := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        refine ⟨A₀, hA₀, le_rfl, le_rfl, fun x hx y hy => ?_⟩
        have : y = x := by
          ext k
          rcases hy k with h | ⟨h, _⟩
          exacts [h, absurd h (Finset.notMem_empty k)]
        exact this ▸ hx
      | insert j s _ ih =>
        obtain ⟨M, hM, hdM, hvM, hsM⟩ := ih
        refine ⟨closure (St j M), (isBounded_iff_ediam_ne_top.mpr (ne_top_of_le_ne_top
          hM.isBounded.ediam_ne_top (hdiam j M))).isCompact_closure, ?_,
          hvM.trans ((hvol j M hM).trans (measure_mono subset_closure)), hsym j s M hsM⟩
        rw [ediam_closure]
        exact (hdiam j M).trans hdM
    obtain ⟨M, hM, hdM, hvM, hsM⟩ := hsteps Finset.univ
    exact ⟨M, hM, hdM, hvM, fun x hx => hsM x hx (-x) fun k => Or.inr ⟨Finset.mem_univ k, rfl⟩⟩
  -- The isodiametric inequality for the closed set `closure f(D)`.
  have hiso : volume (closure (f '' D)) ≤
      Chapter01.realUnitBallVolume ((n + 1 : ℕ) : ℝ) * (ediam (f '' D) / 2) ^ (n + 1) := by
    by_cases hfin : ediam (f '' D) = ∞
    · rw [hfin, ENNReal.top_div_of_ne_top ENNReal.ofNat_ne_top, ENNReal.top_pow n.succ_ne_zero,
        ENNReal.mul_top (Chapter01.realUnitBallVolume_pos (by positivity)).ne']
      exact le_top
    obtain ⟨L, hL, hdL, hvL, hsL⟩ := hrep _ (isBounded_iff_ediam_ne_top.mpr hfin).isCompact_closure
    -- a centrally symmetric set lies in the closed ball of radius `diam / 2` about `0`
    have hLball : L ⊆ closedBall 0 (diam L / 2) := fun x hx => by
      have h := dist_le_diam_of_mem hL.isBounded hx (hsL x hx)
      rw [dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ x, norm_smul, Real.norm_two] at h
      rw [mem_closedBall, dist_zero_right]
      linarith
    calc volume (closure (f '' D)) ≤ volume (closedBall (0 : Rn (n + 1)) (diam L / 2)) :=
          hvL.trans (measure_mono hLball)
      _ = Chapter01.realUnitBallVolume ((n + 1 : ℕ) : ℝ) * (ediam L / 2) ^ (n + 1) := by
        rw [Measure.addHaar_closedBall _ _ (by positivity), finrank_euclideanSpace_fin, hball, mul_comm,
          ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_ofNat, diam,
          ENNReal.ofReal_toReal hL.isBounded.ediam_ne_top]
      _ ≤ _ := by
        gcongr _ * (?_ / 2) ^ _
        exact hdL.trans (ediam_closure _).le
  calc volume (closure (f '' D))
      ≤ Chapter01.realUnitBallVolume ((n + 1 : ℕ) : ℝ) * (ediam (f '' D) / 2) ^ (n + 1) := hiso
    _ ≤ Chapter01.realUnitBallVolume ((n + 1 : ℕ) : ℝ) * (K * ediam D / 2) ^ (n + 1) := by gcongr
    _ = _ := by
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_pow, mul_pow, ENNReal.inv_pow]
      ring

/-- **Simon Ch. 2, proof of Theorem 1.9 (pp. 45–46), one scale of the covering argument.** Put
`s = m + k`. As `0 < r`, the size-`r` premeasure of `E` (the inner infimum of
`hausdorffMeasure_apply`) is at most `μH[s](E) < ∞`, so some cover `C` of `E` has
`ediam (C l) ≤ r` and `∑ (ediam (C l))^s < μH[s](E) + ε`. With `d l = ediam (C l ∩ E)`,
`g = ∑_l (ω_k/2^k) (d l)^k 1_{closure f(C l ∩ E)}` is Borel and dominates `ω_k/2^k` times the
size-`r` premeasure of each fibre `E ∩ f⁻¹{y}`, which is covered by the `C l ∩ E ∩ f⁻¹{y}`.
By `eilenberg_covering_lipschitz_image_volume_le`, `∫ g ≤ ∑_l a (d l)^s ≤ a (μH[s](E) + ε)` with
`a = ω_m ω_k K^m / 2^s`. Simon's `f(C_ij)` is replaced by the closed set `closure f(C l ∩ E)`,
which is Borel without σ-compactness of `X`. -/
theorem Submission.eilenberg_covering_fixed_scale_majorant : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (m : ℕ) (k : ℝ) (E : Set X) (f : X → Rn m) (K : ℝ≥0) (r ε : ℝ≥0∞), 0 < k → μH[(m : ℝ) + k] E < ⊤ → LipschitzOnWith K f E → 0 < r → 0 < ε → ∃ g : Rn m → ℝ≥0∞, Measurable g ∧ (∀ y, Chapter01.realUnitBallVolume k / (2 : ℝ≥0∞) ^ k * (⨅ (t : ℕ → Set X) (_ : E ∩ f ⁻¹' {y} ⊆ ⋃ n, t n) (_ : ∀ n, ediam (t n) ≤ r), ∑' n, ⨆ (_ : (t n).Nonempty), ediam (t n) ^ k) ≤ g y) ∧ ∫⁻ y, g y ∂volume ≤ Chapter01.realUnitBallVolume (m : ℝ) * Chapter01.realUnitBallVolume k * (K : ℝ≥0∞) ^ m / (2 : ℝ≥0∞) ^ ((m : ℝ) + k) * (μH[(m : ℝ) + k] E + ε) := by
  intro X _ _ _ m k E f K r ε hk hE hf hr hε
  have hs : 0 < (m : ℝ) + k := add_pos_of_nonneg_of_pos (Nat.cast_nonneg m) hk
  -- A cover `C` of `E` by sets of diameter `≤ r` with `∑ (ediam (C l))^s < μH[s](E) + ε`.
  have hpre : (⨅ (t : ℕ → Set X) (_ : E ⊆ ⋃ n, t n) (_ : ∀ n, ediam (t n) ≤ r),
      ∑' n, ⨆ (_ : (t n).Nonempty), ediam (t n) ^ ((m : ℝ) + k)) ≤ μH[(m : ℝ) + k] E := by
    rw [Measure.hausdorffMeasure_apply]
    exact le_iSup₂_of_le r hr le_rfl
  have hlt := (ENNReal.lt_add_right (ne_top_of_le_ne_top hE.ne hpre) hε.ne').trans_le
    (add_le_add hpre le_rfl)
  obtain ⟨C, hlt⟩ := iInf_lt_iff.1 hlt
  obtain ⟨hEC, hlt⟩ := iInf_lt_iff.1 hlt
  obtain ⟨hCr, hlt⟩ := iInf_lt_iff.1 hlt
  -- The trimmed pieces `C l ∩ E` still have `∑ (ediam (C l ∩ E))^s ≤ μH[s](E) + ε`.
  have hsum : ∑' l, ediam (C l ∩ E) ^ ((m : ℝ) + k) ≤ μH[(m : ℝ) + k] E + ε := by
    refine le_trans (ENNReal.tsum_le_tsum fun l ↦ ?_) hlt.le
    rcases (C l ∩ E).eq_empty_or_nonempty with h | h
    · rw [h, Metric.ediam_empty, ENNReal.zero_rpow_of_pos hs]
      exact zero_le
    · rw [iSup_pos (h.mono inter_subset_left)]
      exact ENNReal.rpow_le_rpow (Metric.ediam_mono inter_subset_left) hs.le
  -- `(ω_k/2^k) d^k (ω_m K^m d^m / 2^m) = a d^s` for every `d ∈ [0, ∞]`.
  have h2m₀ : (2 : ℝ≥0∞) ^ (m : ℝ) ≠ 0 := (ENNReal.rpow_pos (by norm_num) (by norm_num)).ne'
  have h2m : (2 : ℝ≥0∞) ^ (m : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (Nat.cast_nonneg m) (by norm_num)
  have hexp (d : ℝ≥0∞) : Chapter01.realUnitBallVolume k / 2 ^ k * d ^ k *
      (Chapter01.realUnitBallVolume (m : ℝ) * (K : ℝ≥0∞) ^ m * d ^ m / 2 ^ m) =
      Chapter01.realUnitBallVolume (m : ℝ) * Chapter01.realUnitBallVolume k * (K : ℝ≥0∞) ^ m /
        (2 : ℝ≥0∞) ^ ((m : ℝ) + k) * d ^ ((m : ℝ) + k) := by
    rw [← ENNReal.rpow_natCast d m, ← ENNReal.rpow_natCast 2 m,
      ENNReal.rpow_add_of_nonneg (x := d) _ _ (Nat.cast_nonneg m) hk.le,
      ENNReal.rpow_add (x := 2) _ _ two_ne_zero ENNReal.ofNat_ne_top]
    simp only [div_eq_mul_inv, ENNReal.mul_inv (Or.inl h2m₀) (Or.inl h2m)]
    ring
  refine ⟨fun y ↦ ∑' l, (closure (f '' (C l ∩ E))).indicator
      (fun _ ↦ Chapter01.realUnitBallVolume k / 2 ^ k * ediam (C l ∩ E) ^ k) y,
    Measurable.tsum fun l ↦ measurable_const.indicator isClosed_closure.measurableSet,
    fun y ↦ ?_, ?_⟩
  · -- The pieces `C l ∩ E ∩ f⁻¹{y}` form an admissible cover of the fibre.
    have hcov : E ∩ f ⁻¹' {y} ⊆ ⋃ l, C l ∩ E ∩ f ⁻¹' {y} := by
      rintro x ⟨hxE, hxy⟩
      obtain ⟨l, hl⟩ := mem_iUnion.1 (hEC hxE)
      exact mem_iUnion.2 ⟨l, ⟨hl, hxE⟩, hxy⟩
    have hdiam (l : ℕ) : ediam (C l ∩ E ∩ f ⁻¹' {y}) ≤ r :=
      (Metric.ediam_mono (inter_subset_left.trans inter_subset_left)).trans (hCr l)
    calc _ ≤ Chapter01.realUnitBallVolume k / 2 ^ k * ∑' l,
          ⨆ (_ : (C l ∩ E ∩ f ⁻¹' {y}).Nonempty), ediam (C l ∩ E ∩ f ⁻¹' {y}) ^ k := by
          gcongr Chapter01.realUnitBallVolume k / 2 ^ k * ?_
          exact iInf₂_le_of_le (fun l ↦ C l ∩ E ∩ f ⁻¹' {y}) hcov (iInf_le_of_le hdiam le_rfl)
      _ = ∑' l, Chapter01.realUnitBallVolume k / 2 ^ k *
          ⨆ (_ : (C l ∩ E ∩ f ⁻¹' {y}).Nonempty), ediam (C l ∩ E ∩ f ⁻¹' {y}) ^ k :=
          ENNReal.tsum_mul_left.symm
      _ ≤ _ := ENNReal.tsum_le_tsum fun l ↦ ?_
    rcases (C l ∩ E ∩ f ⁻¹' {y}).eq_empty_or_nonempty with h | h
    · simp [h]
    · have hy : y ∈ closure (f '' (C l ∩ E)) := by
        obtain ⟨x, hxD, hxy⟩ := h
        exact subset_closure ⟨x, hxD, hxy⟩
      rw [iSup_pos h, indicator_of_mem hy]
      gcongr Chapter01.realUnitBallVolume k / 2 ^ k * ?_
      exact ENNReal.rpow_le_rpow (Metric.ediam_mono inter_subset_left) hk.le
  · -- `∫ g = ∑ (ω_k/2^k) (d l)^k Lᵐ(closure f(C l ∩ E)) ≤ ∑ a (d l)^s ≤ a (μH[s](E) + ε)`.
    rw [lintegral_tsum fun l ↦
      (measurable_const.indicator isClosed_closure.measurableSet).aemeasurable]
    calc _ ≤ ∑' l, Chapter01.realUnitBallVolume (m : ℝ) * Chapter01.realUnitBallVolume k *
          (K : ℝ≥0∞) ^ m / (2 : ℝ≥0∞) ^ ((m : ℝ) + k) * ediam (C l ∩ E) ^ ((m : ℝ) + k) := by
          refine ENNReal.tsum_le_tsum fun l ↦ ?_
          rw [lintegral_indicator_const isClosed_closure.measurableSet, ← hexp]
          gcongr
          exact Submission.eilenberg_covering_lipschitz_image_volume_le X m (C l ∩ E) f K
            (hf.mono inter_subset_right)
      _ = Chapter01.realUnitBallVolume (m : ℝ) * Chapter01.realUnitBallVolume k *
          (K : ℝ≥0∞) ^ m / (2 : ℝ≥0∞) ^ ((m : ℝ) + k) *
          ∑' l, ediam (C l ∩ E) ^ ((m : ℝ) + k) := ENNReal.tsum_mul_left
      _ ≤ _ := by gcongr
/-- **Simon Ch. 2, proof of Theorem 1.9 (p. 46), limiting step**, with an explicit Borel majorant
in place of the upper integral. If `c` times the `r i`-scale Hausdorff pre-measure of `F y` is
bounded by measurable `g i y`, `∫⁻ g i ∂ν ≤ b i`, `r i → 0` and `b i → L`, then
`G = liminf g i` is a measurable majorant of `c * μH[d] (F y)` with `∫⁻ G ∂ν ≤ L` (Fatou). -/
theorem Submission.eilenberg_covering_liminf_majorant : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (Y : Type) [MeasurableSpace Y] (ν : Measure Y) (d : ℝ) (c : ℝ≥0∞) (F : Y → Set X) (r : ℕ → ℝ≥0∞) (g : ℕ → Y → ℝ≥0∞) (b : ℕ → ℝ≥0∞) (L : ℝ≥0∞), Tendsto r atTop (𝓝 0) → (∀ i, Measurable (g i)) → (∀ (i : ℕ) (y : Y), c * (⨅ (t : ℕ → Set X) (_ : F y ⊆ ⋃ n, t n) (_ : ∀ n, ediam (t n) ≤ r i), ∑' n, ⨆ (_ : (t n).Nonempty), ediam (t n) ^ d) ≤ g i y) → (∀ i, ∫⁻ y, g i y ∂ν ≤ b i) → Tendsto b atTop (𝓝 L) → ∃ G : Y → ℝ≥0∞, Measurable G ∧ (∀ y, c * μH[d] (F y) ≤ G y) ∧ ∫⁻ y, G y ∂ν ≤ L := by
  intro X _ _ _ Y _ ν d c F r g b L hr hg hcov hint hb
  refine ⟨fun y ↦ liminf (fun i ↦ g i y) atTop, Measurable.liminf hg, fun y ↦ ?_, ?_⟩
  · -- At each scale `R > 0`, eventually `r i ≤ R`, and covers at scale `r i` are admissible at `R`.
    rw [Measure.hausdorffMeasure_apply, ENNReal.mul_iSup]
    refine iSup_le fun R ↦ ?_
    rw [ENNReal.mul_iSup]
    refine iSup_le fun hR ↦ le_liminf_of_le (by isBoundedDefault) ?_
    filter_upwards [hr.eventually_le_const hR] with i hi
    refine le_trans ?_ (hcov i y)
    gcongr c * ?_
    exact le_iInf fun t ↦ le_iInf fun ht ↦ le_iInf fun htr ↦
      iInf₂_le_of_le t ht (iInf_le_of_le (fun n ↦ (htr n).trans hi) le_rfl)
  · -- Fatou's lemma, then `∫⁻ g i ∂ν ≤ b i → L`.
    calc ∫⁻ y, liminf (fun i ↦ g i y) atTop ∂ν
        ≤ liminf (fun i ↦ ∫⁻ y, g i y ∂ν) atTop := lintegral_liminf_le hg
      _ ≤ liminf b atTop := liminf_le_liminf (Eventually.of_forall hint)
      _ = L := hb.liminf_eq
/-- **Simon Ch. 2, Theorem 1.9 (p. 45), measurability of `y ↦ Hᵏ(A ∩ f⁻¹y)`**: for compact `F`
and `k > 0`, `μH[k](F)` is the supremum over `n` of the finite open-cover content of `F` at scale
`(n + 1)⁻¹`. Padding a finite open cover by `∅` bounds the fixed-scale precontent of
`hausdorffMeasure_apply` by the open content at the same scale. Conversely, thickening each set of
a near-optimal countable cover at scale `δ / 2` by a radius `ηₙ > 0` with `2ηₙ < δ / 2` and cost
`eₙ` (`∑ eₙ < ε / 2`), then extracting a finite subcover by compactness, bounds the open content
at scale `δ` by the precontent at scale `δ / 2` plus `ε`. -/
theorem Submission.eilenberg_compact_hausdorff_eq_iSup_open_content : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (k : ℝ) (F : Set X), 0 < k → IsCompact F → MeasureTheory.Measure.hausdorffMeasure k F = ⨆ n : ℕ, ⨅ (I : Finset ℕ) (O : ℕ → Set X) (_ : ∀ i ∈ I, IsOpen (O i) ∧ Metric.ediam (O i) < ((n : ℝ≥0∞) + 1)⁻¹) (_ : F ⊆ ⋃ i ∈ I, O i), ∑ i ∈ I, Metric.ediam (O i) ^ k := by
  intro X _ _ _ k F hk hF
  -- Step 1: the fixed-scale precontent of `hausdorffMeasure_apply` is antitone in the scale.
  have hmono : ∀ r r' : ℝ≥0∞, r ≤ r' →
      (⨅ (t : ℕ → Set X) (_ : F ⊆ ⋃ n, t n) (_ : ∀ n, ediam (t n) ≤ r'),
        ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ k) ≤
      ⨅ (t : ℕ → Set X) (_ : F ⊆ ⋃ n, t n) (_ : ∀ n, ediam (t n) ≤ r),
        ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ k := fun r r' h =>
    iInf_mono fun t => iInf_mono fun _ => iInf_mono' fun ht => ⟨fun n => (ht n).trans h, le_rfl⟩
  -- Step 2: padding a finite open cover by `∅` shows precontent ≤ open content.
  have hpre_le : ∀ δ : ℝ≥0∞,
      (⨅ (t : ℕ → Set X) (_ : F ⊆ ⋃ n, t n) (_ : ∀ n, ediam (t n) ≤ δ),
        ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ k) ≤
      ⨅ (I : Finset ℕ) (O : ℕ → Set X) (_ : ∀ i ∈ I, IsOpen (O i) ∧ ediam (O i) < δ)
        (_ : F ⊆ ⋃ i ∈ I, O i), ∑ i ∈ I, ediam (O i) ^ k := by
    intro δ
    refine le_iInf fun I => le_iInf fun O => le_iInf fun hO => le_iInf fun hcov => ?_
    set t : ℕ → Set X := fun n => if n ∈ I then O n else ∅
    have htcov : F ⊆ ⋃ n, t n := by
      intro x hx
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (hcov hx)
      exact mem_iUnion.2 ⟨i, by simp [t, hi, hxi]⟩
    have htdiam : ∀ n, ediam (t n) ≤ δ := by
      intro n
      by_cases hn : n ∈ I
      · simpa only [t, hn, ite_true] using (hO n hn).2.le
      · simp [t, hn]
    calc _ ≤ ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ k :=
          iInf_le_of_le t (iInf_le_of_le htcov (iInf_le_of_le htdiam le_rfl))
      _ = ∑ n ∈ I, ⨆ _ : (t n).Nonempty, ediam (t n) ^ k :=
          tsum_eq_sum fun n hn => by simp [t, hn]
      _ ≤ ∑ n ∈ I, ediam (O n) ^ k :=
          Finset.sum_le_sum fun n hn => iSup_le fun _ => by simp [t, hn]
  -- Step 3: thickening a near-optimal countable cover at scale `δ/2` and extracting a finite
  -- subcover by compactness shows open content at scale `δ` ≤ precontent at scale `δ/2`.
  have hle_pre : ∀ δ : ℝ≥0∞, 0 < δ → δ ≠ ∞ →
      (⨅ (I : Finset ℕ) (O : ℕ → Set X) (_ : ∀ i ∈ I, IsOpen (O i) ∧ ediam (O i) < δ)
        (_ : F ⊆ ⋃ i ∈ I, O i), ∑ i ∈ I, ediam (O i) ^ k) ≤
      ⨅ (t : ℕ → Set X) (_ : F ⊆ ⋃ n, t n) (_ : ∀ n, ediam (t n) ≤ δ / 2),
        ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ k := by
    intro δ hδpos hδ
    have hδ2 : δ / 2 ≠ ∞ := ENNReal.div_ne_top hδ two_ne_zero
    have hδ2pos : 0 < δ / 2 := ENNReal.half_pos hδpos.ne'
    refine ENNReal.le_of_forall_pos_le_add fun ε hε hlt => ?_
    have hε2 : (ε : ℝ≥0∞) / 2 ≠ 0 := (ENNReal.half_pos (by exact_mod_cast hε.ne')).ne'
    obtain ⟨C, hCcov, hCdiam, hCsum⟩ : ∃ C : ℕ → Set X, F ⊆ ⋃ n, C n ∧
        (∀ n, ediam (C n) ≤ δ / 2) ∧
        ∑' n, ⨆ _ : (C n).Nonempty, ediam (C n) ^ k <
          (⨅ (t : ℕ → Set X) (_ : F ⊆ ⋃ n, t n) (_ : ∀ n, ediam (t n) ≤ δ / 2),
            ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ k) + ε / 2 := by
      have := ENNReal.lt_add_right hlt.ne hε2
      simpa only [iInf_lt_iff, exists_prop] using this
    obtain ⟨e, he0, hesum⟩ := ENNReal.exists_pos_sum_of_countable' hε2 ℕ
    have hη : ∀ n, ∃ η : ℝ≥0, 0 < η ∧ 2 * (η : ℝ≥0∞) < δ / 2 ∧
        (ediam (C n) + 2 * η) ^ k < ediam (C n) ^ k + e n := by
      intro n
      have hfin : ediam (C n) ^ k ≠ ∞ :=
        ENNReal.rpow_ne_top_of_nonneg hk.le (ne_top_of_le_ne_top hδ2 (hCdiam n))
      have hc1 : Continuous fun η : ℝ≥0 => 2 * (η : ℝ≥0∞) :=
        (ENNReal.continuous_const_mul (by norm_num)).comp ENNReal.continuous_coe
      have hc2 : Continuous fun η : ℝ≥0 => (ediam (C n) + 2 * (η : ℝ≥0∞)) ^ k :=
        ENNReal.continuous_rpow_const.comp (continuous_const.add hc1)
      have h1 : ∀ᶠ η : ℝ≥0 in 𝓝 0, 2 * (η : ℝ≥0∞) < δ / 2 :=
        (hc1.tendsto 0).eventually_lt_const (by simpa using hδ2pos)
      have h2 : ∀ᶠ η : ℝ≥0 in 𝓝 0, (ediam (C n) + 2 * (η : ℝ≥0∞)) ^ k < ediam (C n) ^ k + e n :=
        (hc2.tendsto 0).eventually_lt_const
          (by simpa using ENNReal.lt_add_right hfin (he0 n).ne')
      obtain ⟨η, ⟨hη1, hη2⟩, hη0⟩ :=
        (((h1.and h2).filter_mono nhdsWithin_le_nhds).and
          (eventually_mem_nhdsWithin (s := Ioi (0 : ℝ≥0)) (a := 0))).exists
      exact ⟨η, hη0, hη1, hη2⟩
    choose η hη0 hη1 hη2 using hη
    set O : ℕ → Set X := fun n => thickening (η n : ℝ) (C n)
    have hOdiam : ∀ n, ediam (O n) < δ := fun n =>
      calc ediam (O n) ≤ ediam (C n) + 2 * η n := ediam_thickening_le _
        _ ≤ δ / 2 + 2 * η n := add_le_add (hCdiam n) le_rfl
        _ < δ / 2 + δ / 2 := ENNReal.add_lt_add_left hδ2 (hη1 n)
        _ = δ := ENNReal.add_halves δ
    have hcost : ∀ n, ediam (O n) ^ k ≤ (⨆ _ : (C n).Nonempty, ediam (C n) ^ k) + e n := by
      intro n
      rcases (C n).eq_empty_or_nonempty with hC | hC
      · simp [O, hC, ENNReal.zero_rpow_of_pos hk]
      · rw [iSup_pos hC]
        calc ediam (O n) ^ k ≤ (ediam (C n) + 2 * η n) ^ k :=
              ENNReal.rpow_le_rpow (ediam_thickening_le _) hk.le
          _ ≤ ediam (C n) ^ k + e n := (hη2 n).le
    obtain ⟨I, hI⟩ := hF.elim_finite_subcover O (fun n => isOpen_thickening)
      (hCcov.trans (iUnion_mono fun n =>
        self_subset_thickening (by exact_mod_cast hη0 n) (C n)))
    calc (⨅ (I : Finset ℕ) (O : ℕ → Set X) (_ : ∀ i ∈ I, IsOpen (O i) ∧ ediam (O i) < δ)
          (_ : F ⊆ ⋃ i ∈ I, O i), ∑ i ∈ I, ediam (O i) ^ k)
        ≤ ∑ i ∈ I, ediam (O i) ^ k :=
          iInf_le_of_le I (iInf_le_of_le O (iInf_le_of_le
            (fun i _ => ⟨isOpen_thickening, hOdiam i⟩) (iInf_le_of_le hI le_rfl)))
      _ ≤ ∑ i ∈ I, ((⨆ _ : (C i).Nonempty, ediam (C i) ^ k) + e i) :=
          Finset.sum_le_sum fun i _ => hcost i
      _ ≤ ∑' i, ((⨆ _ : (C i).Nonempty, ediam (C i) ^ k) + e i) := ENNReal.sum_le_tsum I
      _ = (∑' i, ⨆ _ : (C i).Nonempty, ediam (C i) ^ k) + ∑' i, e i := ENNReal.tsum_add
      _ ≤ ((⨅ (t : ℕ → Set X) (_ : F ⊆ ⋃ n, t n) (_ : ∀ n, ediam (t n) ≤ δ / 2),
            ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ k) + ε / 2) + ε / 2 :=
          add_le_add hCsum.le hesum.le
      _ = _ := by rw [add_assoc, ENNReal.add_halves]
  -- Step 4: compare both sides along the scales `(n + 1)⁻¹`.
  rw [Measure.hausdorffMeasure_apply]
  apply le_antisymm
  · refine iSup₂_le fun r hr => ?_
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hr.ne'
    have hnr : ((n : ℝ≥0∞) + 1)⁻¹ ≤ r := (ENNReal.inv_le_inv' le_self_add).trans hn.le
    exact (hmono _ _ hnr).trans ((hpre_le _).trans (le_iSup (fun m : ℕ =>
      ⨅ (I : Finset ℕ) (O : ℕ → Set X)
        (_ : ∀ i ∈ I, IsOpen (O i) ∧ ediam (O i) < ((m : ℝ≥0∞) + 1)⁻¹)
        (_ : F ⊆ ⋃ i ∈ I, O i), ∑ i ∈ I, ediam (O i) ^ k) n))
  · refine iSup_le fun n => ?_
    have hpos : 0 < ((n : ℝ≥0∞) + 1)⁻¹ := ENNReal.inv_pos.2 (by simp)
    have hne : ((n : ℝ≥0∞) + 1)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (by simp)
    exact (hle_pre _ hpos hne).trans
      (le_iSup₂_of_le (((n : ℝ≥0∞) + 1)⁻¹ / 2) (ENNReal.half_pos hpos.ne') le_rfl)
/-- **Simon Ch. 2, Theorem 1.9 (p. 45), measurability of `y ↦ Hᵏ(A ∩ f⁻¹y)`**: upper
semicontinuity of the finite open-cover content of the fibres `Q ∩ f⁻¹{y}`, for compact `Q` and
`f` continuous on `Q`. A cover `(I, O)` of the fibre over `y₀` with sum `< t` has open union `W`;
`f '' (Q \ W)` is compact, hence closed, and misses `y₀`, and off it the same cover still covers
the fibre. -/
theorem Submission.eilenberg_fiber_open_content_upperSemicontinuous : ∀ (X : Type) [MetricSpace X] (m : ℕ) (k : ℝ) (δ : ℝ≥0∞) (Q : Set X) (f : X → Rn m), IsCompact Q → ContinuousOn f Q → UpperSemicontinuous (fun y : Rn m ↦ ⨅ (I : Finset ℕ) (O : ℕ → Set X) (_ : ∀ i ∈ I, IsOpen (O i) ∧ Metric.ediam (O i) < δ) (_ : Q ∩ f ⁻¹' {y} ⊆ ⋃ i ∈ I, O i), ∑ i ∈ I, Metric.ediam (O i) ^ k) := by
  intro X _ m k δ Q f hQ hf y₀ t ht
  simp only [iInf_lt_iff] at ht
  obtain ⟨I, O, hO, hcov, hS⟩ := ht
  have hW : IsOpen (⋃ i ∈ I, O i) := isOpen_biUnion fun i hi ↦ (hO i hi).1
  have hK : IsClosed (f '' (Q \ ⋃ i ∈ I, O i)) :=
    ((hQ.diff hW).image_of_continuousOn (hf.mono sdiff_subset)).isClosed
  have hy₀ : y₀ ∈ (f '' (Q \ ⋃ i ∈ I, O i))ᶜ := by
    rintro ⟨x, ⟨hxQ, hxW⟩, rfl⟩
    exact hxW (hcov ⟨hxQ, rfl⟩)
  filter_upwards [hK.isOpen_compl.mem_nhds hy₀] with y hy
  -- Off `f '' (Q \ W)` the fibre over `y` lies in `W`, so `(I, O)` stays admissible.
  have hcov' : Q ∩ f ⁻¹' {y} ⊆ ⋃ i ∈ I, O i := fun x ⟨hxQ, hxy⟩ ↦
    by_contra fun hxW ↦ hy ⟨x, ⟨hxQ, hxW⟩, hxy⟩
  exact lt_of_le_of_lt (iInf_le_of_le I <| iInf_le_of_le O <| iInf_le_of_le hO <|
    iInf_le_of_le hcov' le_rfl) hS

/-- **Simon Ch. 2, Theorem 1.9 (pp. 45–46), measurability of `y ↦ Hᵏ(A ∩ f⁻¹y)`**, for compact
`A = Q` (Simon leaves this measurability as an exercise). For `f` continuous on `Q` every fibre
`Q ∩ f⁻¹{y}` is compact, so its `μH[k]` is the countable supremum over `n` of its finite open-cover
contents at scale `(n + 1)⁻¹` (`eilenberg_compact_hausdorff_eq_iSup_open_content`). Each content is
upper semicontinuous in `y` (`eilenberg_fiber_open_content_upperSemicontinuous`), hence Borel, and
`𝓗[k] = (ω_k / 2^k) • μH[k]`. -/
theorem Submission.eilenberg_compact_fiber_measurable : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (m : ℕ) (k : ℝ) (Q : Set X) (f : X → Rn m), 0 < k → IsCompact Q → ContinuousOn f Q → Measurable (fun y ↦ Chapter01.simonHausdorffMeasureReal k (Q ∩ f ⁻¹' {y})) := by
  intro X _ _ _ m k Q f hk hQ hf
  -- Each fibre is a closed subset of the compact set `Q`, hence compact.
  have hfib (y : Rn m) : IsCompact (Q ∩ f ⁻¹' {y}) :=
    hQ.of_isClosed_subset (hf.preimage_isClosed_of_isClosed hQ.isClosed isClosed_singleton)
      inter_subset_left
  have hμ : Measurable fun y : Rn m ↦ μH[k] (Q ∩ f ⁻¹' {y}) := by
    simp_rw [fun y ↦ Submission.eilenberg_compact_hausdorff_eq_iSup_open_content X k _ hk (hfib y)]
    exact Measurable.iSup fun n ↦
      (Submission.eilenberg_fiber_open_content_upperSemicontinuous X m k _ Q f hQ hf).measurable
  simp only [Chapter01.simonHausdorffMeasureReal, Measure.smul_apply, smul_eq_mul]
  exact hμ.const_mul _
/-- **Simon Ch. 2, proof of Theorem 1.8(i) (p. 45), compact exhaustion**, as used for Theorem 1.9.
In a σ-compact metric space, a `μ`-null-measurable `A` with `μ A < ∞` contains increasing compact
`Q j` with `μ (A \ ⋃ j, Q j) = 0`. A Borel kernel `B ⊆ A`, `B =ᵐ[μ] A`, carries the finite, hence
regular, measure `μ.restrict B`; it gives compact `K j ⊆ B` with `μ (B \ K j) < j⁻¹`, and
`Q = accumulate K` collects their finite unions. -/
theorem Submission.eilenberg_compact_exhaustion : ∀ (X : Type) [MetricSpace X] [SigmaCompactSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) (A : Set X), NullMeasurableSet A μ → μ A < ⊤ → ∃ Q : ℕ → Set X, (∀ j, IsCompact (Q j)) ∧ (∀ j, Q j ⊆ A) ∧ Monotone Q ∧ μ (A \ ⋃ j, Q j) = 0 := by
  intro X _ _ _ _ μ A hA hAfin
  obtain ⟨B, hBA, hB, hBae⟩ := hA.exists_measurable_subset_ae_eq
  have : IsFiniteMeasure (μ.restrict B) :=
    isFiniteMeasure_restrict.2 ((measure_mono hBA).trans_lt hAfin).ne
  have hK (j : ℕ) : ∃ K, K ⊆ B ∧ IsCompact K ∧ μ.restrict B (B \ K) < (j : ℝ≥0∞)⁻¹ :=
    hB.exists_isCompact_sdiff_lt (measure_ne_top _ _)
      (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top j))
  choose K hKB hKc hKlt using hK
  refine ⟨accumulate K, isCompact_accumulate hKc,
    fun j ↦ (accumulate_subset_iUnion j).trans ((iUnion_subset hKB).trans hBA),
    monotone_accumulate, ?_⟩
  -- `B \ ⋃ j, K j` is null, its measure being below every `j⁻¹`.
  have hnull : μ (B \ ⋃ j, K j) = 0 := by
    by_contra h
    obtain ⟨j, hj⟩ := ENNReal.exists_inv_nat_lt h
    have hle : μ (B \ ⋃ j, K j) ≤ μ.restrict B (B \ K j) := by
      rw [Measure.restrict_eq_self μ sdiff_subset]
      exact measure_mono (sdiff_subset_sdiff_right (subset_iUnion K j))
    exact lt_asymm hj (hle.trans_lt (hKlt j))
  rw [iUnion_accumulate]
  refine measure_mono_null (fun x hx ↦ ?_) (measure_union_null (ae_eq_set.1 hBae).2 hnull)
  by_cases hxB : x ∈ B
  exacts [Or.inr ⟨hxB, hx.2⟩, Or.inl ⟨hx.1, hxB⟩]

/-- The frozen Chapter 2 contract: the conjunction of all headline results. -/
theorem main_theorem : LipschitzExtension ∧ Rademacher ∧ C1Approximation ∧ WhitneyExtension ∧ LipschitzImageHausdorff ∧ EilenbergInequality ∧ BVCompactness ∧ BVPoincare ∧ BVExtensionEstimate ∧ AreaFormula ∧ FirstVariation ∧ SecondVariation ∧ StationaryIffMeanCurvatureZero ∧ SecondVariationStationary ∧ CoareaFormula ∧ C1Sard := by sorry

/-- **Simon Ch. 2, proof of Theorem 1.9 (pp. 45–46), covering majorant**, with a Borel majorant
`G` in place of the upper integral of Remark 1.10. Put `s = m + k`, `M = μH[s](E)` (finite, as
`𝓗^s = (ω_s/2^s) μH[s]`) and `a = ω_m ω_k K^m / 2^s`. At the scales `δ i = (i + 1)⁻¹`,
`eilenberg_covering_fixed_scale_majorant` gives Borel `g i` dominating `(ω_k/2^k)` times the
size-`δ i` Hausdorff premeasure of `E ∩ f⁻¹{y}`, with `∫ g i ≤ a (M + δ i)`;
`eilenberg_covering_liminf_majorant` turns them into `G ≥ (ω_k/2^k) μH[k](E ∩ f⁻¹{·}) = 𝓗^k(…)`
with `∫ G ≤ a M = (ω_m ω_k / ω_s) K^m 𝓗^s(E)`. -/
theorem Submission.eilenberg_covering_majorant : ∀ (X : Type) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (m : ℕ) (k : ℝ) (E : Set X) (f : X → Rn m) (K : ℝ≥0), 0 < k → Chapter01.simonHausdorffMeasureReal (m + k) E < ⊤ → LipschitzOnWith K f E → ∃ G : Rn m → ℝ≥0∞, Measurable G ∧ (∀ y, Chapter01.simonHausdorffMeasureReal k (E ∩ f ⁻¹' {y}) ≤ G y) ∧ ∫⁻ y, G y ∂volume ≤ Chapter01.realUnitBallVolume (m : ℝ) * Chapter01.realUnitBallVolume k / Chapter01.realUnitBallVolume (m + k) * (K : ℝ≥0∞) ^ m * Chapter01.simonHausdorffMeasureReal (m + k) E := by
  intro X _ _ _ m k E f K hk hE hf
  have hnorm (s : ℝ) (S : Set X) : Chapter01.simonHausdorffMeasureReal s S =
      Chapter01.realUnitBallVolume s / 2 ^ s * μH[s] S := by
    rw [Chapter01.simonHausdorffMeasureReal, Measure.smul_apply, smul_eq_mul]
  have hs : (0 : ℝ) ≤ m + k := add_nonneg (Nat.cast_nonneg m) hk.le
  have hω₀ : Chapter01.realUnitBallVolume (m + k) ≠ 0 := (Chapter01.realUnitBallVolume_pos hs).ne'
  have hω : Chapter01.realUnitBallVolume (m + k) ≠ ⊤ := Chapter01.realUnitBallVolume_ne_top _
  have h2₀ : (2 : ℝ≥0∞) ^ ((m : ℝ) + k) ≠ 0 := (ENNReal.rpow_pos (by norm_num) (by norm_num)).ne'
  have h2 : (2 : ℝ≥0∞) ^ ((m : ℝ) + k) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hs (by norm_num)
  have hM : μH[(m : ℝ) + k] E < ⊤ := by
    rw [hnorm] at hE
    exact ENNReal.lt_top_of_mul_ne_top_right hE.ne (ENNReal.div_pos hω₀ h2).ne'
  -- Scales and slacks `δ i = (i + 1)⁻¹ → 0`, and the fixed-scale majorants `g i`.
  set δ : ℕ → ℝ≥0∞ := fun i ↦ ((i : ℝ≥0∞) + 1)⁻¹ with hδ_def
  have hδ₀ (i : ℕ) : 0 < δ i :=
    ENNReal.inv_pos.2 (ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top i, ENNReal.one_ne_top⟩)
  have hδ : Tendsto δ atTop (𝓝 0) := by
    rw [hδ_def]
    simpa using (tendsto_add_atTop_iff_nat 1).2 ENNReal.tendsto_inv_nat_nhds_zero
  choose g hg hgle hgint using fun i ↦ Submission.eilenberg_covering_fixed_scale_majorant X m k E
    f K (δ i) (δ i) hk hM hf (hδ₀ i) (hδ₀ i)
  set a := Chapter01.realUnitBallVolume (m : ℝ) * Chapter01.realUnitBallVolume k * (K : ℝ≥0∞) ^ m /
    (2 : ℝ≥0∞) ^ ((m : ℝ) + k) with ha_def
  have ha : a ≠ ⊤ := ENNReal.div_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
    (Chapter01.realUnitBallVolume_ne_top _) (Chapter01.realUnitBallVolume_ne_top _))
    (ENNReal.pow_ne_top ENNReal.coe_ne_top)) h2₀
  have hb : Tendsto (fun i ↦ a * (μH[(m : ℝ) + k] E + δ i)) atTop
      (𝓝 (a * μH[(m : ℝ) + k] E)) := by
    simpa using ENNReal.Tendsto.const_mul (hδ.const_add (μH[(m : ℝ) + k] E)) (Or.inr ha)
  obtain ⟨G, hG, hGle, hGint⟩ := Submission.eilenberg_covering_liminf_majorant X (Rn m) volume k
    (Chapter01.realUnitBallVolume k / 2 ^ k) (fun y ↦ E ∩ f ⁻¹' {y}) δ g
    (fun i ↦ a * (μH[(m : ℝ) + k] E + δ i)) (a * μH[(m : ℝ) + k] E) hδ hg hgle hgint hb
  refine ⟨G, hG, fun y ↦ (hnorm k _).trans_le (hGle y), hGint.trans_eq ?_⟩
  -- `a M = (ω_m ω_k / ω_s) K^m (ω_s / 2^s) M`: the factor `ω_s` cancels.
  rw [hnorm, ha_def]
  calc _ = Chapter01.realUnitBallVolume (m : ℝ) * Chapter01.realUnitBallVolume k *
        (K : ℝ≥0∞) ^ m / (2 : ℝ≥0∞) ^ ((m : ℝ) + k) * μH[(m : ℝ) + k] E *
        ((Chapter01.realUnitBallVolume (m + k))⁻¹ * Chapter01.realUnitBallVolume (m + k)) := by
        rw [ENNReal.inv_mul_cancel hω₀ hω, mul_one]
    _ = _ := by
        simp only [div_eq_mul_inv]
        ring

/-- **Simon Ch. 2, Theorem 1.9 (pp. 45–46), Eilenberg inequality**, assembled from its three
children. `eilenberg_compact_exhaustion` gives increasing compact `Q j ⊆ A` with
`𝓗^{m+k}(N) = 0`, `N = A \ ⋃ j, Q j`. The `eilenberg_covering_majorant` of `N` has integral `0`,
so `𝓗^k(N ∩ f⁻¹{y}) = 0` for a.e. `y`. Hence, a.e., `𝓗^k(A ∩ f⁻¹{y}) = 𝓗^k((⋃ j, Q j) ∩ f⁻¹{y})
= ⨆ j, 𝓗^k(Q j ∩ f⁻¹{y})`, a supremum of Borel functions (`eilenberg_compact_fiber_measurable`).
The inequality is the `eilenberg_covering_majorant` of `A` itself. -/
theorem Submission.eilenberg_inequality_theorem : EilenbergInequality := by
  intro X _ _ _ _ m k A f K _ hk hA hAfin hf
  obtain ⟨Q, hQc, hQA, hQmono, hN⟩ := Submission.eilenberg_compact_exhaustion X
    (Chapter01.simonHausdorffMeasureReal (m + k)) A hA hAfin
  -- The majorant of the null remainder `N` vanishes a.e., hence so do the fibre measures of `N`.
  obtain ⟨G₀, hG₀, hG₀le, hG₀int⟩ := Submission.eilenberg_covering_majorant X m k
    (A \ ⋃ j, Q j) f K hk (hN.trans_lt ENNReal.zero_lt_top) (hf.mono sdiff_subset)
  rw [hN, mul_zero, nonpos_iff_eq_zero, lintegral_eq_zero_iff hG₀] at hG₀int
  -- Continuity from below along the increasing fibres `Q j ∩ f⁻¹{y}`.
  have hmeas : Measurable fun y ↦
      Chapter01.simonHausdorffMeasureReal k ((⋃ j, Q j) ∩ f ⁻¹' {y}) := by
    have hsup : (fun y ↦ Chapter01.simonHausdorffMeasureReal k ((⋃ j, Q j) ∩ f ⁻¹' {y})) =
        fun y ↦ ⨆ j, Chapter01.simonHausdorffMeasureReal k (Q j ∩ f ⁻¹' {y}) := by
      funext y
      rw [iUnion_inter]
      exact Monotone.measure_iUnion fun i j hij ↦ inter_subset_inter_left _ (hQmono hij)
    rw [hsup]
    exact Measurable.iSup fun j ↦ Submission.eilenberg_compact_fiber_measurable X m k (Q j) f hk
      (hQc j) (hf.mono (hQA j)).continuousOn
  have hae : (fun y ↦ Chapter01.simonHausdorffMeasureReal k ((⋃ j, Q j) ∩ f ⁻¹' {y})) =ᵐ[volume]
      fun y ↦ Chapter01.simonHausdorffMeasureReal k (A ∩ f ⁻¹' {y}) := by
    filter_upwards [hG₀int] with y hy
    refine le_antisymm (measure_mono (inter_subset_inter_left _ (iUnion_subset hQA))) ?_
    calc Chapter01.simonHausdorffMeasureReal k (A ∩ f ⁻¹' {y})
        ≤ Chapter01.simonHausdorffMeasureReal k ((⋃ j, Q j) ∩ f ⁻¹' {y}) +
            Chapter01.simonHausdorffMeasureReal k ((A \ ⋃ j, Q j) ∩ f ⁻¹' {y}) := by
          refine (measure_mono fun x hx ↦ ?_).trans (measure_union_le _ _)
          by_cases hxQ : x ∈ ⋃ j, Q j
          exacts [Or.inl ⟨hxQ, hx.2⟩, Or.inr ⟨⟨hx.1, hxQ⟩, hx.2⟩]
      _ = Chapter01.simonHausdorffMeasureReal k ((⋃ j, Q j) ∩ f ⁻¹' {y}) := by
          rw [nonpos_iff_eq_zero.1 ((hG₀le y).trans_eq hy), add_zero]
  obtain ⟨G, -, hGle, hGint⟩ := Submission.eilenberg_covering_majorant X m k A f K hk hAfin hf
  exact ⟨hmeas.aemeasurable.congr hae, (lintegral_mono hGle).trans hGint⟩

end GMT.Ch02
