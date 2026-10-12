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

/-- The frozen Chapter 2 contract: the conjunction of all headline results. -/
theorem main_theorem : LipschitzExtension ∧ Rademacher ∧ C1Approximation ∧ WhitneyExtension ∧ LipschitzImageHausdorff ∧ EilenbergInequality ∧ BVCompactness ∧ BVPoincare ∧ BVExtensionEstimate ∧ AreaFormula ∧ FirstVariation ∧ SecondVariation ∧ StationaryIffMeanCurvatureZero ∧ SecondVariationStationary ∧ CoareaFormula ∧ C1Sard := by sorry

end GMT.Ch02
