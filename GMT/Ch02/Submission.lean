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

/-- **Local submersion (rectification) chart** (cf. Spivak, *Calculus on Manifolds*, Thm 2-13).
If `G` is `C¹` on the open set `V ∋ a` and `DG(a)` is onto, let `π = e ∘ P_K`, where `P_K` is the
orthogonal projection onto `K = ker DG(a)` and `e : K ≃ ℝᵏ`. Then `Φ(x) = (G x, π(x - a))` has
invertible derivative at `a`. By the inverse function theorem, `Λ = Φ⁻¹` on
`Ω = {p ∈ target : Λ p ∈ V₁}` is the chart, where `V₁ ∋ a` is an open subset of `V` on which
`DΦ` is invertible; `G ∘ Λ = WithLp.fst` because `Φ ∘ Λ = id` on `Ω`. -/
theorem Submission.coarea_straightening_submersion_chart : ∀ (m k : ℕ) (V : Set (Rn (m + k))) (G : Rn (m + k) → Rn m) (a : Rn (m + k)), IsOpen V → ContDiffOn ℝ 1 G V → a ∈ V → Function.Surjective (fderiv ℝ G a) → ∃ (Ω : Set (WithLp 2 (Rn m × Rn k))) (Λ : WithLp 2 (Rn m × Rn k) → Rn (m + k)), IsOpen Ω ∧ ContDiffOn ℝ 1 Λ Ω ∧ InjOn Λ Ω ∧ IsOpen (Λ '' Ω) ∧ a ∈ Λ '' Ω ∧ Λ '' Ω ⊆ V ∧ (∀ p ∈ Ω, Function.Bijective (fderiv ℝ Λ p)) ∧ ∀ p ∈ Ω, G (Λ p) = WithLp.fst p := by
  intro m k V G a hV hG ha hsurj
  -- `K = ker DG(a)` has dimension `k` (rank–nullity).
  set A : Rn (m + k) →L[ℝ] Rn m := fderiv ℝ G a
  set K : Submodule ℝ (Rn (m + k)) := LinearMap.ker (A : Rn (m + k) →ₗ[ℝ] Rn m) with hK
  have hrange : LinearMap.range (A : Rn (m + k) →ₗ[ℝ] Rn m) = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hKdim : Module.finrank ℝ K = Module.finrank ℝ (Rn k) := by
    have h := LinearMap.finrank_range_add_finrank_ker (A : Rn (m + k) →ₗ[ℝ] Rn m)
    rw [hrange, finrank_top, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin, ← hK] at h
    rw [finrank_euclideanSpace_fin]
    omega
  -- `π = e ∘ P_K : ℝ^{m+k} → ℝᵏ` agrees on `K` with an isomorphism `e : K ≃ ℝᵏ`.
  let e : K ≃ₗ[ℝ] Rn k := LinearEquiv.ofFinrankEq K (Rn k) hKdim
  let π : Rn (m + k) →L[ℝ] Rn k :=
    (e.toContinuousLinearEquiv : K →L[ℝ] Rn k) ∘L K.orthogonalProjectionOnto
  have hπK : ∀ v : K, π v = e v := by
    intro v
    simp [π]
  -- `Φ(x) = toLp (G x, π(x - a))` is `C¹` on `V` with `DΦ(x) = T ∘ (DG(x), π)`.
  let T : (Rn m × Rn k) ≃L[ℝ] WithLp 2 (Rn m × Rn k) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ (Rn m) (Rn k)).symm
  let Φ : Rn (m + k) → WithLp 2 (Rn m × Rn k) := fun x => T (G x, π (x - a))
  have hπaff : ContDiff ℝ 1 (fun x : Rn (m + k) => π (x - a)) :=
    π.contDiff.comp (contDiff_id.sub contDiff_const)
  have hΦC : ContDiffOn ℝ 1 Φ V := T.contDiff.comp_contDiffOn (hG.prodMk hπaff.contDiffOn)
  have hΦCA : ∀ x ∈ V, ContDiffAt ℝ 1 Φ x := fun x hx => hΦC.contDiffAt (hV.mem_nhds hx)
  have hπd : ∀ x, HasFDerivAt (fun x : Rn (m + k) => π (x - a)) π x := by
    intro x
    have h1 : HasFDerivAt (fun x : Rn (m + k) => x - a) (ContinuousLinearMap.id ℝ (Rn (m + k))) x :=
      (hasFDerivAt_id x).sub_const a
    have h2 := (π.hasFDerivAt (x := x - a)).comp x h1
    rw [ContinuousLinearMap.comp_id] at h2
    exact h2
  have hΦd : ∀ x ∈ V, HasFDerivAt Φ
      ((T : Rn m × Rn k →L[ℝ] WithLp 2 (Rn m × Rn k)).comp ((fderiv ℝ G x).prod π)) x := by
    intro x hx
    have hGx : HasFDerivAt G (fderiv ℝ G x) x :=
      ((hG.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds hx)).hasFDerivAt
    exact T.hasFDerivAt.comp x (hGx.prodMk (hπd x))
  -- `(DG(a), π)` is injective, hence (equal dimensions) bijective; so `DΦ(a)` is an isomorphism.
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
  have hsurjA : Function.Surjective (A.prod π) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  let Φ' : Rn (m + k) ≃L[ℝ] WithLp 2 (Rn m × Rn k) :=
    (LinearEquiv.ofBijective ((A.prod π : Rn (m + k) →L[ℝ] Rn m × Rn k) :
      Rn (m + k) →ₗ[ℝ] Rn m × Rn k) ⟨hinj, hsurjA⟩).toContinuousLinearEquiv.trans T
  have hΦ'd : HasFDerivAt Φ (Φ' : Rn (m + k) →L[ℝ] WithLp 2 (Rn m × Rn k)) a := by
    have : (Φ' : Rn (m + k) →L[ℝ] WithLp 2 (Rn m × Rn k)) =
        (T : Rn m × Rn k →L[ℝ] WithLp 2 (Rn m × Rn k)).comp (A.prod π) := by ext1 v; rfl
    rw [this]; exact hΦd a ha
  -- The set `V'` of points of `V` at which `DΦ` is invertible is open and contains `a`.
  set V' : Set (Rn (m + k)) := V ∩ (fderiv ℝ Φ) ⁻¹'
    (range ((↑) : (Rn (m + k) ≃L[ℝ] WithLp 2 (Rn m × Rn k)) →
      Rn (m + k) →L[ℝ] WithLp 2 (Rn m × Rn k)))
  have hV'o : IsOpen V' :=
    (hΦC.continuousOn_fderiv_of_isOpen hV le_rfl).isOpen_inter_preimage hV
      ContinuousLinearEquiv.isOpen
  have haV' : a ∈ V' := ⟨ha, Φ', hΦ'd.fderiv.symm⟩
  -- Inverse function theorem: an open partial homeomorphism `h` with `⇑h = Φ` and `a ∈ S`.
  have hΦs : HasStrictFDerivAt Φ (Φ' : Rn (m + k) →L[ℝ] WithLp 2 (Rn m × Rn k)) a :=
    (hΦCA a ha).hasStrictFDerivAt' hΦ'd one_ne_zero
  let h := hΦs.toOpenPartialHomeomorph Φ
  -- `V₁ = S ∩ V'`, `Ω = {p ∈ S' : h⁻¹ p ∈ V₁}` and `Λ = h⁻¹`; then `Λ(Ω) = V₁`.
  set V₁ : Set (Rn (m + k)) := h.source ∩ V'
  have hV₁o : IsOpen V₁ := h.open_source.inter hV'o
  have haV₁ : a ∈ V₁ := ⟨hΦs.mem_toOpenPartialHomeomorph_source, haV'⟩
  have hV₁V : V₁ ⊆ V := fun x hx => hx.2.1
  set Ω : Set (WithLp 2 (Rn m × Rn k)) := h.target ∩ h.symm ⁻¹' V₁
  have himage : h.symm '' Ω = V₁ := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact hp.2
    · intro hx
      refine ⟨h x, ⟨h.map_source hx.1, ?_⟩, h.left_inv hx.1⟩
      rw [Set.mem_preimage, h.left_inv hx.1]
      exact hx
  -- At `p ∈ Ω`, `Λ` is `C¹` with derivative `(DΦ(Λ p))⁻¹`.
  have hsymm : ∀ p ∈ Ω, ∃ φ : Rn (m + k) ≃L[ℝ] WithLp 2 (Rn m × Rn k),
      HasFDerivAt h.symm (φ.symm : WithLp 2 (Rn m × Rn k) →L[ℝ] Rn (m + k)) p ∧
        ContDiffAt ℝ 1 h.symm p := by
    intro p hp
    obtain ⟨φ, hφ⟩ := hp.2.2.2
    have hxV : h.symm p ∈ V := hp.2.2.1
    have hd : HasFDerivAt h (φ : Rn (m + k) →L[ℝ] WithLp 2 (Rn m × Rn k)) (h.symm p) := by
      rw [hφ]; exact ((hΦCA _ hxV).differentiableAt one_ne_zero).hasFDerivAt
    exact ⟨φ, h.hasFDerivAt_symm hp.1 hd, h.contDiffAt_symm hp.1 hd (hΦCA _ hxV)⟩
  refine ⟨Ω, h.symm, h.isOpen_inter_preimage_symm hV₁o, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `Λ` is `C¹` on `Ω`
    intro p hp
    obtain ⟨φ, -, hcd⟩ := hsymm p hp
    exact hcd.contDiffWithinAt
  · -- `Λ` is injective on `Ω ⊆ S'`
    exact h.symm.injOn.mono inter_subset_left
  · rw [himage]; exact hV₁o
  · rw [himage]; exact haV₁
  · rw [himage]; exact hV₁V
  · -- `DΛ(p) = (DΦ(Λ p))⁻¹` is bijective
    intro p hp
    obtain ⟨φ, hd, -⟩ := hsymm p hp
    rw [hd.fderiv]
    exact φ.symm.bijective
  · -- `G(Λ p) = (Φ(Λ p))₁ = p₁`
    intro p hp
    exact congrArg WithLp.fst (h.right_inv hp.1)
/-- **Simon Ch. 2, 4.1–4.2 (p. 55), reparametrizing a local representation.** Let `(V, W, ψ)` be
a `C¹` local representation of `M` with `T_{ψ(x)} M = range Dψ(x)` for `x ∈ V`, and let `Λ` be
`C¹` and injective on the open set `Ω`, with bijective derivative and `Λ(Ω) ⊆ V` open. Then
`ψ ∘ Λ` is `C¹` and injective on `Ω` with injective derivative, `(ψ ∘ Λ)(Ω) = O ∩ M` for an open
`O` (4.2: by relative properness, `ψ(V \ Λ(Ω))` is closed relative to `W`), and
`T_{ψ(Λ(p))} M = range D(ψ ∘ Λ)(p)` for `p ∈ Ω`. -/
theorem Submission.coarea_straightening_reparametrize_chart : ∀ (N m k : ℕ) (M : Set (Rn N)) (V : Set (Rn (m + k))) (W : Set (Rn N)) (ψ : Rn (m + k) → Rn N) (Ω : Set (WithLp 2 (Rn m × Rn k))) (Λ : WithLp 2 (Rn m × Rn k) → Rn (m + k)), Chapter02.IsSimonLocalRepresentation 1 M V W ψ → (∀ x ∈ V, tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap) → IsOpen Ω → ContDiffOn ℝ 1 Λ Ω → InjOn Λ Ω → IsOpen (Λ '' Ω) → Λ '' Ω ⊆ V → (∀ p ∈ Ω, Function.Bijective (fderiv ℝ Λ p)) → ∃ O : Set (Rn N), IsOpen O ∧ (ψ ∘ Λ) '' Ω = O ∩ M ∧ ContDiffOn ℝ 1 (ψ ∘ Λ) Ω ∧ InjOn (ψ ∘ Λ) Ω ∧ (∀ p ∈ Ω, Function.Injective (fderiv ℝ (ψ ∘ Λ) p)) ∧ ∀ p ∈ Ω, tangentSpace M ((ψ ∘ Λ) p) = LinearMap.range (fderiv ℝ (ψ ∘ Λ) p).toLinearMap := by
  intro N m k M V W ψ Ω Λ hψ hT hΩ hΛC hΛinj hV₁ hV₁V hΛbij
  obtain ⟨hV, hW, hψC, hψinj, hψimg, hψprop, hψder⟩ := hψ
  have hΛV : MapsTo Λ Ω V := fun p hp => hV₁V ⟨p, hp, rfl⟩
  -- Simon 4.2: `ψ(V \ Λ(Ω))` is closed relative to `W`. Near `y ∈ W` it lies in the image of the
  -- compact set `(V ∩ ψ⁻¹(B̄)) \ Λ(Ω)`, where `B̄ ⊆ W` is a closed ball about `y`.
  have hrel : ∀ y ∈ W, y ∈ closure (ψ '' (V \ Λ '' Ω)) → y ∈ ψ '' (V \ Λ '' Ω) := by
    intro y hyW hycl
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hW y hyW
    have hQW : closedBall y (r / 2) ⊆ W := (closedBall_subset_ball (half_lt_self hr)).trans hball
    have hK : IsCompact (ψ '' (V ∩ ψ ⁻¹' closedBall y (r / 2) ∩ (Λ '' Ω)ᶜ)) :=
      ((hψprop _ (isCompact_closedBall y (r / 2)) hQW).inter_right
        hV₁.isClosed_compl).image_of_continuousOn (hψC.continuousOn.mono fun x hx => hx.1.1)
    have hsub : ball y (r / 2) ∩ ψ '' (V \ Λ '' Ω) ⊆
        ψ '' (V ∩ ψ ⁻¹' closedBall y (r / 2) ∩ (Λ '' Ω)ᶜ) := by
      rintro _ ⟨hyb, x, ⟨hxV, hxV₁⟩, rfl⟩
      exact ⟨x, ⟨⟨hxV, ball_subset_closedBall hyb⟩, hxV₁⟩, rfl⟩
    obtain ⟨x, ⟨⟨hxV, -⟩, hxV₁⟩, hxy⟩ := closure_minimal hsub hK.isClosed
      (isOpen_ball.inter_closure ⟨mem_ball_self (half_pos hr), hycl⟩)
    exact ⟨x, ⟨hxV, hxV₁⟩, hxy⟩
  -- Chain rule: `D(ψ ∘ Λ)(p) = Dψ(Λ(p)) ∘ DΛ(p)`.
  have hD : ∀ p ∈ Ω, fderiv ℝ (ψ ∘ Λ) p = (fderiv ℝ ψ (Λ p)).comp (fderiv ℝ Λ p) := fun p hp =>
    fderiv_comp p ((hψC.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds (hΛV hp)))
      ((hΛC.differentiableOn one_ne_zero).differentiableAt (hΩ.mem_nhds hp))
  refine ⟨W \ closure (ψ '' (V \ Λ '' Ω)), hW.sdiff isClosed_closure, ?_, hψC.comp hΛC hΛV,
    hψinj.comp hΛinj hΛV, fun p hp => ?_, fun p hp => ?_⟩
  · rw [image_comp]
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
      by_cases hx : x ∈ Λ '' Ω
      · exact ⟨x, hx, rfl⟩
      · exact (hycl (subset_closure ⟨x, ⟨hxV, hx⟩, rfl⟩)).elim
  · rw [hD p hp, ContinuousLinearMap.coe_comp]
    exact (hψder (Λ p) (hΛV hp)).comp (hΛbij p hp).1
  · -- `DΛ(p)` is onto, so `range D(ψ ∘ Λ)(p) = range Dψ(Λ(p)) = T_{ψ(Λ(p))} M`.
    rw [Function.comp_apply, hT (Λ p) (hΛV hp), hD p hp, ContinuousLinearMap.toLinearMap_comp,
      LinearMap.range_comp_of_range_eq_top]
    exact LinearMap.range_eq_top.mpr (hΛbij p hp).2
/-- **The co-area Jacobian as a norm determinant** (Simon Ch. 2, §6, p. 66). Let `T = T_x M`, let
`L = Df(x) ∘ ι_T : T → ℝᵐ` with `ι_T` the inclusion of `T` in `ℝᴺ`, and let `L*` be the adjoint
of `L`. Then `J*_f(x) = √det(L ∘ L*) = normDet(L*)`. For `g = L*` we have `g* = L`, so
`(normDet g)² = det(g* ∘ g) = det(L ∘ L*)`, and `normDet g ≥ 0`. -/
theorem Submission.coareaJacobian_eq_normDet_adjoint : ∀ (N m : ℕ) (M : Set (Rn N)) (f : Rn N → Rn m) (x : Rn N), coareaJacobian M f x = (LinearMap.adjoint ((fderiv ℝ f x).comp (tangentSpace M x).subtypeL).toLinearMap).normDet := by
  intro N m M f x
  -- Step 3: for `g = L*`, `(normDet g)² = det(g* ∘ₗ g) = det(L ∘ₗ L*)`, as `g* = L`.
  have hsq :=
    (LinearMap.adjoint ((fderiv ℝ f x).comp (tangentSpace M x).subtypeL).toLinearMap).normDet_sq
  rw [LinearMap.adjoint_adjoint] at hsq
  -- Step 4: `normDet g ≥ 0`, so `normDet g = √((normDet g)²)`.
  rw [← Real.sqrt_sq (LinearMap.normDet_nonneg _)]
  -- Steps 1-2 and 5: by unfolding, `coareaJacobian M f x = √det(L ∘ₗ L*)`, since
  -- `ContinuousLinearMap.det` is `LinearMap.det` of the underlying map and the underlying map of
  -- the continuous adjoint is `LinearMap.adjoint`.
  exact congrArg Real.sqrt hsq.symm
/-- **Norm determinant of a block lower-triangular map** (Simon Ch. 2, §6, p. 66: the block
computation behind the co-area Jacobian `J*_f`). Let `E₁, E₂, F₁, F₂` be finite-dimensional real
inner product spaces with `dim E₁ = dim F₁` and `dim E₂ = dim F₂`, and let
`G : E₁ × E₂ → F₁ × F₂` be linear between the `L²` products, with `(G (0, b))₁ = 0` for all `b`.
If `G₁₁ a = (G (a, 0))₁` and `G₂₂ b = (G (0, b))₂`, then `normDet G = normDet G₁₁ · normDet G₂₂`.
In product orthonormal bases the matrix of `G` is block lower-triangular, `[[G₁₁, 0], [*, G₂₂]]`,
and its determinant is the product of the determinants of the diagonal blocks. -/
theorem Submission.coarea_normDet_block_triangular : ∀ (E₁ E₂ F₁ F₂ : Type) [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁] [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂] [NormedAddCommGroup F₁] [InnerProductSpace ℝ F₁] [FiniteDimensional ℝ F₁] [NormedAddCommGroup F₂] [InnerProductSpace ℝ F₂] [FiniteDimensional ℝ F₂] (G : WithLp 2 (E₁ × E₂) →ₗ[ℝ] WithLp 2 (F₁ × F₂)) (G₁₁ : E₁ →ₗ[ℝ] F₁) (G₂₂ : E₂ →ₗ[ℝ] F₂), Module.finrank ℝ E₁ = Module.finrank ℝ F₁ → Module.finrank ℝ E₂ = Module.finrank ℝ F₂ → (∀ b : E₂, WithLp.fst (G (WithLp.toLp 2 (0, b))) = 0) → (∀ a : E₁, G₁₁ a = WithLp.fst (G (WithLp.toLp 2 (a, 0)))) → (∀ b : E₂, G₂₂ b = WithLp.snd (G (WithLp.toLp 2 (0, b)))) → G.normDet = G₁₁.normDet * G₂₂.normDet := by
  intro E₁ E₂ F₁ F₂ _ _ _ _ _ _ _ _ _ _ _ _ G G₁₁ G₂₂ h₁ h₂ h0 hG₁₁ hG₂₂
  classical
  -- Step 1: orthonormal bases indexed by `Fin d₁` (`E₁`, `F₁`) and `Fin d₂` (`E₂`, `F₂`).
  let bE₁ := stdOrthonormalBasis ℝ E₁
  let bE₂ := stdOrthonormalBasis ℝ E₂
  let bF₁ := (stdOrthonormalBasis ℝ F₁).reindex (finCongr h₁.symm)
  let bF₂ := (stdOrthonormalBasis ℝ F₂).reindex (finCongr h₂.symm)
  -- Step 2: the product orthonormal bases of the `L²` products, indexed by `Fin d₁ ⊕ Fin d₂`.
  let bE := bE₁.prod bE₂
  let bF := bF₁.prod bF₂
  -- Step 3: the `bF`-coordinates of `w` are the `bF₁`-coordinates of `w₁` and the
  -- `bF₂`-coordinates of `w₂`.
  have hrepr₁ : ∀ (v : WithLp 2 (F₁ × F₂)) i, bF.repr v (Sum.inl i) = bF₁.repr (WithLp.fst v) i := by
    intro v i
    simp [bF, OrthonormalBasis.repr_apply_apply]
  have hrepr₂ : ∀ (v : WithLp 2 (F₁ × F₂)) i, bF.repr v (Sum.inr i) = bF₂.repr (WithLp.snd v) i := by
    intro v i
    simp [bF, OrthonormalBasis.repr_apply_apply]
  -- Step 4: the matrix of `G` is block lower-triangular, with the matrices of `G₁₁` and `G₂₂` on
  -- the diagonal and a zero upper-right block.
  have hmat : LinearMap.toMatrix bE.toBasis bF.toBasis G =
      Matrix.fromBlocks (LinearMap.toMatrix bE₁.toBasis bF₁.toBasis G₁₁) 0
        (Matrix.of fun i j => bF₂.repr (WithLp.snd (G (WithLp.toLp 2 (bE₁ j, 0)))) i)
        (LinearMap.toMatrix bE₂.toBasis bF₂.toBasis G₂₂) := by
    ext (i | i) (j | j)
    · simp [LinearMap.toMatrix_apply, hrepr₁, bE, hG₁₁]
    · simp [LinearMap.toMatrix_apply, hrepr₁, bE, h0]
    · simp [LinearMap.toMatrix_apply, hrepr₂, bE]
    · simp [LinearMap.toMatrix_apply, hrepr₂, bE, hG₂₂]
  -- Steps 5–6: `normDet` is `‖det‖` of the matrix in orthonormal bases with a common index type,
  -- and `det (fromBlocks A 0 C D) = det A * det D`.
  rw [G.normDet_eq_norm_det_toMatrix bE bF, G₁₁.normDet_eq_norm_det_toMatrix bE₁ bF₁,
    G₂₂.normDet_eq_norm_det_toMatrix bE₂ bF₂, hmat, Matrix.det_fromBlocks_zero₁₂, norm_mul]

/-- **Chart identity for the coarea Jacobian** (Simon Ch. 2, §6, 6.2). If the linear bijection
`Φ : ℝᵐ × ℝᵏ → T` straightens `L : T → ℝᵐ` (`L ∘ Φ = WithLp.fst`) and `Ψ = Φ ∘ (0, ·)`, then
`normDet L* · normDet Φ = normDet Ψ`. In the orthogonal coordinates `C = (π_{Qᗮ}, π_Q)`,
`Q = ker L`, the map `C ∘ Φ` is block lower triangular with diagonal blocks
`α = π_{Qᗮ} ∘ Φ ∘ (·, 0)` and `Ψ` (corestricted to `Q`). Moreover `λ ∘ α = id` for
`λ = L|_{Qᗮ}`, and `normDet λ = normDet L*` because `L*` corestricted to `Qᗮ` is `λ*`. -/
theorem Submission.coarea_normDet_adjoint_mul_normDet_chart : ∀ (m k : ℕ) (T : Type) [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T] (L : T →ₗ[ℝ] Rn m) (Φ : WithLp 2 (Rn m × Rn k) →ₗ[ℝ] T) (Ψ : Rn k →ₗ[ℝ] T), Function.Bijective Φ → (∀ p, L (Φ p) = WithLp.fst p) → (∀ b, Ψ b = Φ (WithLp.toLp 2 (0, b))) → (LinearMap.adjoint L).normDet * Φ.normDet = Ψ.normDet := by
  intro m k T _ _ _ L Φ Ψ hΦ hL hΨ
  -- Step 1: `L` is onto.
  have hsurj : Function.Surjective L := fun a => ⟨Φ (WithLp.toLp 2 (a, 0)), by rw [hL]; rfl⟩
  -- Step 2: `dim P = dim T = m + k`, `dim Q = k` and `dim Qᗮ = m`, where `Q = ker L`.
  have hP : Module.finrank ℝ (WithLp 2 (Rn m × Rn k)) = m + k := by
    rw [(WithLp.linearEquiv 2 ℝ (Rn m × Rn k)).finrank_eq, Module.finrank_prod]
    simp
  have hT : Module.finrank ℝ T = m + k := by
    rw [← (LinearEquiv.ofBijective Φ hΦ).finrank_eq, hP]
  have hQ : Module.finrank ℝ (LinearMap.ker L) = k := by
    have h := L.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hT, finrank_euclideanSpace_fin] at h
    omega
  have hQperp : Module.finrank ℝ (LinearMap.ker L)ᗮ = m := by
    have := (LinearMap.ker L).finrank_add_finrank_orthogonal
    omega
  -- Step 3: the isometric coordinates `C t = (π_{Qᗮ} t, π_Q t)`.
  let C : T ≃ₗᵢ[ℝ] WithLp 2 ((LinearMap.ker L)ᗮ × LinearMap.ker L) :=
    (LinearMap.ker L).orthogonalDecomposition.trans (LinearIsometryEquiv.withLpProdComm 2 ℝ _ _)
  have hC : ∀ t, C t = WithLp.toLp 2 ((LinearMap.ker L)ᗮ.orthogonalProjectionOnto t,
      (LinearMap.ker L).orthogonalProjectionOnto t) := by
    intro t
    simp [C, Submodule.orthogonalDecomposition_apply, LinearIsometryEquiv.withLpProdComm_apply]
  -- Step 4: `G = C ∘ Φ` has `normDet G = normDet C · normDet Φ = normDet Φ`.
  let G : WithLp 2 (Rn m × Rn k) →ₗ[ℝ] WithLp 2 ((LinearMap.ker L)ᗮ × LinearMap.ker L) :=
    C.toLinearEquiv.toLinearMap ∘ₗ Φ
  have hGΦ : G.normDet = Φ.normDet := by
    rw [LinearMap.normDet_comp_of_finrank_eq _ _ (by rw [hP, hT])]
    have : (C.toLinearEquiv.toLinearMap).normDet = 1 := C.toLinearIsometry.normDet_eq_one
    rw [this, one_mul]
  -- Step 5: `Ψ` maps into `Q`, so the upper-right block of `G` vanishes.
  have hΨmem : ∀ b, Ψ b ∈ LinearMap.ker L := by
    intro b; rw [LinearMap.mem_ker, hΨ, hL]; rfl
  have h0 : ∀ b, WithLp.fst (G (WithLp.toLp 2 (0, b))) = 0 := by
    intro b
    simp only [G, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]
    rw [← hΨ, hC]
    simp [Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal
      ((LinearMap.ker L).le_orthogonal_orthogonal (hΨmem b))]
  -- Step 6: the diagonal blocks `α = G₁₁` and `Θ = G₂₂`, where `Θ` is `Ψ` corestricted to `Q`.
  let inl : Rn m →ₗ[ℝ] WithLp 2 (Rn m × Rn k) :=
    (WithLp.linearEquiv 2 ℝ (Rn m × Rn k)).symm.toLinearMap ∘ₗ LinearMap.inl ℝ (Rn m) (Rn k)
  let inr : Rn k →ₗ[ℝ] WithLp 2 (Rn m × Rn k) :=
    (WithLp.linearEquiv 2 ℝ (Rn m × Rn k)).symm.toLinearMap ∘ₗ LinearMap.inr ℝ (Rn m) (Rn k)
  let G₁₁ : Rn m →ₗ[ℝ] (LinearMap.ker L)ᗮ := (WithLp.fstL 2 ℝ _ _).toLinearMap ∘ₗ G ∘ₗ inl
  let G₂₂ : Rn k →ₗ[ℝ] LinearMap.ker L := (WithLp.sndL 2 ℝ _ _).toLinearMap ∘ₗ G ∘ₗ inr
  have hG₂₂ : G₂₂ = Ψ.codRestrict (LinearMap.ker L) hΨmem := by
    refine LinearMap.ext fun b => ?_
    apply Subtype.ext
    simp only [G₂₂, G, inr, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv, LinearMap.codRestrict_apply]
    have : (WithLp.linearEquiv 2 ℝ (Rn m × Rn k)).symm (LinearMap.inr ℝ (Rn m) (Rn k) b) =
        WithLp.toLp 2 (0, b) := rfl
    rw [this, ← hΨ, hC]
    simp [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨Ψ b, hΨmem b⟩]
  -- Step 7: the block lemma gives `normDet G = normDet α · normDet Θ`.
  have hG := Submission.coarea_normDet_block_triangular (Rn m) (Rn k) _ _ G G₁₁ G₂₂
    (by simp [hQperp]) (by simp [hQ]) h0 (fun a => rfl) (fun b => rfl)
  -- Step 8: `λ = L|_{Qᗮ}` satisfies `λ ∘ α = id`, since `L (π_{Qᗮ} t) = L (t - π_Q t) = L t`.
  let lam : (LinearMap.ker L)ᗮ →ₗ[ℝ] Rn m := L.domRestrict (LinearMap.ker L)ᗮ
  have hproj : ∀ t, L ((LinearMap.ker L)ᗮ.orthogonalProjectionOnto t) = L t := by
    intro t
    rw [Submodule.coe_orthogonalProjectionOnto_apply, Submodule.starProjection_orthogonal_val,
      map_sub, LinearMap.mem_ker.mp ((LinearMap.ker L).starProjection_apply_mem t), sub_zero]
  have hlam : lam ∘ₗ G₁₁ = LinearMap.id := by
    refine LinearMap.ext fun a => ?_
    have hα : G₁₁ a = WithLp.fst (C (Φ (WithLp.toLp 2 (a, 0)))) := rfl
    show L (G₁₁ a : T) = a
    rw [hα, hC]
    show L ((LinearMap.ker L)ᗮ.orthogonalProjectionOnto (Φ (WithLp.toLp 2 (a, 0))) : T) = a
    rw [hproj, hL]
    rfl
  have h1 : lam.normDet * G₁₁.normDet = 1 := by
    rw [← LinearMap.normDet_comp_of_finrank_eq _ _ (by simp [hQperp]), hlam, LinearMap.normDet_id]
  -- Step 9: `L*` maps onto `range L* = Qᗮ`, and corestricted to `Qᗮ` it is `λ*`. In orthonormal
  -- bases indexed by `Fin m` the matrix of `λ*` is the transpose of that of `λ`, so
  -- `normDet L* = normDet λ* = normDet λ`.
  have hm : ∀ y, (LinearMap.adjoint L) y ∈ (LinearMap.ker L)ᗮ := by
    intro y
    rw [LinearMap.orthogonal_ker]
    exact LinearMap.mem_range_self _ y
  have ha : (LinearMap.adjoint L).codRestrict (LinearMap.ker L)ᗮ hm = LinearMap.adjoint lam := by
    refine (LinearMap.eq_adjoint_iff _ _).mpr fun y q => ?_
    exact LinearMap.adjoint_inner_left L q y
  have hlamJ : lam.normDet = (LinearMap.adjoint L).normDet := by
    let bQ := (stdOrthonormalBasis ℝ (LinearMap.ker L)ᗮ).reindex (finCongr hQperp)
    let bR := EuclideanSpace.basisFun (Fin m) ℝ
    rw [← LinearMap.normDet_codRestrict hm, ha,
      (LinearMap.adjoint lam).normDet_eq_norm_det_toMatrix bR bQ,
      lam.normDet_eq_norm_det_toMatrix bQ bR, LinearMap.toMatrix_adjoint, Matrix.det_conjTranspose]
    simp
  -- Step 10: `normDet L* · normDet Φ = (normDet λ · normDet α) · normDet Ψ = normDet Ψ`.
  rw [← hGΦ, hG, hG₂₂, LinearMap.normDet_codRestrict, ← hlamJ, ← mul_assoc, h1, one_mul]

/-- **Chart identity for the co-area Jacobian** (part (2) of `coarea_jacobian_linear_algebra`).
Let `A : ℝᵐ × ℝᵏ → ℝᴺ` be injective with `range A = T_x M` and `Df(x) (A p) = p₁`, and let
`B b = A (0, b)`. Then `J*_f(x) · normDet A = normDet B`. Indeed `A` and `B` take values in
`T = T_x M`, and for `L = Df(x)|_T` the codomain restrictions `Φ = A|^T` (bijective) and
`Ψ = B|^T` satisfy `L (Φ p) = p₁` and `Ψ b = Φ (0, b)`, so
`coarea_normDet_adjoint_mul_normDet_chart` gives `normDet L* · normDet Φ = normDet Ψ`. Finally
`J*_f(x) = normDet L*` (`coareaJacobian_eq_normDet_adjoint`), and following a map by the isometric
inclusion `T ⊆ ℝᴺ` does not change `normDet` (`LinearMap.normDet_codRestrict`). -/
theorem Submission.coareaJacobian_mul_normDet_chart : ∀ (N m k : ℕ) (M : Set (Rn N))
    (f : Rn N → Rn m) (x : Rn N) (A : WithLp 2 (Rn m × Rn k) →L[ℝ] Rn N) (B : Rn k →L[ℝ] Rn N),
    Function.Injective A → tangentSpace M x = LinearMap.range A.toLinearMap →
    (∀ p, fderiv ℝ f x (A p) = WithLp.fst p) → (∀ b, B b = A (WithLp.toLp 2 (0, b))) →
    coareaJacobian M f x * A.toLinearMap.normDet = B.toLinearMap.normDet := by
  intro N m k M f x A B hA hT hD hB
  -- Step 1: `A` and `B` take values in `T = T_x M = range A`.
  have hAT : ∀ p, A.toLinearMap p ∈ tangentSpace M x := fun p ↦
    hT ▸ LinearMap.mem_range_self A.toLinearMap p
  have hBT : ∀ b, B.toLinearMap b ∈ tangentSpace M x := fun b ↦ by
    simpa only [ContinuousLinearMap.coe_coe, hB] using hAT (WithLp.toLp 2 (0, b))
  -- Step 2: the codomain restrictions `Φ = A|^T` and `Ψ = B|^T`.
  let Φ := A.toLinearMap.codRestrict (tangentSpace M x) hAT
  let Ψ := B.toLinearMap.codRestrict (tangentSpace M x) hBT
  -- Step 3: `Φ` is bijective, as `A` is injective and `T = range A`.
  have hΦ : Function.Bijective Φ := by
    refine ⟨fun p q hpq ↦ hA (congrArg Subtype.val hpq), fun t ↦ ?_⟩
    obtain ⟨p, hp⟩ : (t : Rn N) ∈ LinearMap.range A.toLinearMap := hT ▸ t.2
    exact ⟨p, Subtype.ext hp⟩
  -- Steps 4–6: for `L = Df(x)|_T`, `L (Φ p) = p₁` (by `hD`) and `Ψ b = Φ (toLp (0, b))` (by `hB`),
  -- so the abstract chart identity applies to `L`, `Φ` and `Ψ`.
  have key := Submission.coarea_normDet_adjoint_mul_normDet_chart m k (tangentSpace M x)
    ((fderiv ℝ f x).comp (tangentSpace M x).subtypeL).toLinearMap Φ Ψ hΦ hD
    fun b ↦ Subtype.ext (hB b)
  -- Steps 7–9: `J*_f(x) = normDet L*`, `normDet Φ = normDet A` and `normDet Ψ = normDet B`.
  rw [Submission.coareaJacobian_eq_normDet_adjoint, ← LinearMap.normDet_codRestrict hAT,
    ← LinearMap.normDet_codRestrict hBT]
  exact key

/-- The frozen Chapter 2 contract: the conjunction of all headline results. -/
theorem main_theorem : LipschitzExtension ∧ Rademacher ∧ C1Approximation ∧ WhitneyExtension ∧ LipschitzImageHausdorff ∧ EilenbergInequality ∧ BVCompactness ∧ BVPoincare ∧ BVExtensionEstimate ∧ AreaFormula ∧ FirstVariation ∧ SecondVariation ∧ StationaryIffMeanCurvatureZero ∧ SecondVariationStationary ∧ CoareaFormula ∧ C1Sard := by sorry

/-- **`J*_f(x) = 0` iff `Df(x) ∘ A` is not onto** (Simon Ch. 2, §6, p. 66: `J*_f(x) ≠ 0`
precisely when `df_x` has rank `m`), for `A : ℝⁿ → ℝᴺ` with `T_x M = range A`. With
`L = df_x = Df(x)|_{T_x M}`, `J*_f(x) = normDet(L*)` (`coareaJacobian_eq_normDet_adjoint`), which
vanishes iff `ker L* = (range L)ᗮ ≠ 0`, i.e. iff `L` is not onto; and `L` is onto iff `Df(x) ∘ A`
is, since both have range `Df(x)(T_x M)`. -/
theorem Submission.coareaJacobian_eq_zero_iff_not_surjective : ∀ (N m n : ℕ) (M : Set (Rn N))
    (f : Rn N → Rn m) (x : Rn N) (A : Rn n →L[ℝ] Rn N),
    tangentSpace M x = LinearMap.range A.toLinearMap →
    (coareaJacobian M f x = 0 ↔ ¬ Function.Surjective ((fderiv ℝ f x).comp A)) := by
  intro N m n M f x A hT
  -- Steps 1–3: `J*_f(x) = normDet(L*)` vanishes iff `(range L)ᗮ = ker L* ≠ 0` iff `L` is not onto.
  rw [Submission.coareaJacobian_eq_normDet_adjoint, LinearMap.normDet_eq_zero_iff_ker_ne_bot,
    ← LinearMap.orthogonal_range, ne_eq, Submodule.orthogonal_eq_bot_iff, LinearMap.range_eq_top]
  -- Step 4: since `T_x M = range A`, `L` is onto iff `Df(x) ∘ A` is.
  refine not_congr ⟨fun hs y ↦ ?_, fun hs y ↦ ?_⟩
  · obtain ⟨t, rfl⟩ := hs y
    obtain ⟨z, hz⟩ : (t : Rn N) ∈ LinearMap.range A.toLinearMap := hT ▸ t.2
    exact ⟨z, congrArg (fderiv ℝ f x) hz⟩
  · obtain ⟨z, rfl⟩ := hs y
    exact ⟨⟨A z, hT ▸ LinearMap.mem_range_self A.toLinearMap z⟩, rfl⟩

/-- **Linear algebra of the co-area Jacobian** (Simon Ch. 2, §6, 6.2, p. 66). Let `T = T_x M`,
`D = Df(x)` and `L = D|_T : T → ℝᵐ`, so that `J*_f(x) = √det(L L*)`.
(1) If `A : ℝⁿ → ℝᴺ` is linear with `T = range A`, then `J*_f(x) = 0` iff `D ∘ A` is not onto.
(2) Let `A : ℝᵐ × ℝᵏ → ℝᴺ` (Euclidean product) be injective and linear with `T = range A` and
`D (A p) = p₁`, and let `B b = A (0, b)`. Then `J*_f(x) · normDet A = normDet B`.
Part (1) is `coareaJacobian_eq_zero_iff_not_surjective` and part (2) is
`coareaJacobian_mul_normDet_chart`. -/
theorem Submission.coarea_jacobian_linear_algebra : (∀ (N m n : ℕ) (M : Set (Rn N)) (f : Rn N → Rn m) (x : Rn N) (A : Rn n →L[ℝ] Rn N), tangentSpace M x = LinearMap.range A.toLinearMap → (coareaJacobian M f x = 0 ↔ ¬ Function.Surjective ((fderiv ℝ f x).comp A))) ∧ ∀ (N m k : ℕ) (M : Set (Rn N)) (f : Rn N → Rn m) (x : Rn N) (A : WithLp 2 (Rn m × Rn k) →L[ℝ] Rn N) (B : Rn k →L[ℝ] Rn N), Function.Injective A → tangentSpace M x = LinearMap.range A.toLinearMap → (∀ p, fderiv ℝ f x (A p) = WithLp.fst p) → (∀ b, B b = A (WithLp.toLp 2 (0, b))) → coareaJacobian M f x * A.toLinearMap.normDet = B.toLinearMap.normDet :=
  -- Part (1), Steps 1–3: `J*_f(x) = 0` iff `L` is not onto, and `range L = range (D ∘ A)`.
  -- Part (2), Steps 4–9: corestrict `A` and `B` to `T` and compute in block-triangular form.
  ⟨Submission.coareaJacobian_eq_zero_iff_not_surjective,
    Submission.coareaJacobian_mul_normDet_chart⟩

/-- **Simon Ch. 2, §6 (pp. 66–67), straightening charts at regular points of `f` on `M`.** Let `M`
be an `(m+k)`-dimensional `C¹` submanifold whose local representations `ψ` satisfy
`T_{ψ(x)} M = range Dψ(x)`, `f` `C¹` on an open `U ⊇ M` and `J*_f(x₀) ≠ 0`. Take a chart `ψ` with
`ψ(a) = x₀`. Then `D(f ∘ ψ)(a) = Df(x₀) ∘ Dψ(a)` is onto, the local submersion theorem gives `Λ`
with `f ∘ ψ ∘ Λ = fst`, and `Ψ = ψ ∘ Λ` is the required chart. -/
theorem Submission.coarea_exists_straightening_chart : ∀ (N m k : ℕ) (M U : Set (Rn N)) (f : Rn N → Rn m) (x₀ : Rn N), Chapter02.IsSimonSubmanifold (E := Rn (m + k)) 1 M → IsOpen U → M ⊆ U → ContDiffOn ℝ 1 f U → (∀ (V : Set (Rn (m + k))) (W : Set (Rn N)) (ψ : Rn (m + k) → Rn N), Chapter02.IsSimonLocalRepresentation 1 M V W ψ → ∀ x ∈ V, tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap) → x₀ ∈ M → coareaJacobian M f x₀ ≠ 0 → ∃ (Ω : Set (WithLp 2 (Rn m × Rn k))) (O : Set (Rn N)) (Ψ : WithLp 2 (Rn m × Rn k) → Rn N), IsOpen Ω ∧ IsOpen O ∧ x₀ ∈ O ∧ ContDiffOn ℝ 1 Ψ Ω ∧ InjOn Ψ Ω ∧ Ψ '' Ω = O ∩ M ∧ (∀ p ∈ Ω, Function.Injective (fderiv ℝ Ψ p)) ∧ (∀ p ∈ Ω, f (Ψ p) = WithLp.fst p) ∧ ∀ p ∈ Ω, tangentSpace M (Ψ p) = LinearMap.range (fderiv ℝ Ψ p).toLinearMap := by
  intro N m k M U f x₀ hM hU hMU hf hT hx₀ hJ
  -- A chart `(V, W, ψ)` of `M` at `x₀ = ψ a`.
  obtain ⟨V, W, ψ, hx₀W, hψ⟩ := hM.exists_localRepresentation hx₀
  obtain ⟨a, haV, rfl⟩ : x₀ ∈ ψ '' V := by rw [hψ.image_eq]; exact ⟨hx₀W, hx₀⟩
  have hψVU : MapsTo ψ V U := fun x hx => by
    have hx' : ψ x ∈ W ∩ M := by rw [← hψ.image_eq]; exact mem_image_of_mem ψ hx
    exact hMU hx'.2
  -- `G = f ∘ ψ` is `C¹` on `V`, and `DG(a) = Df(ψ a) ∘ Dψ(a)` is onto because `J*_f(ψ a) ≠ 0`.
  have hGC : ContDiffOn ℝ 1 (f ∘ ψ) V := hf.comp hψ.contDiffOn hψVU
  have hDG : fderiv ℝ (f ∘ ψ) a = (fderiv ℝ f (ψ a)).comp (fderiv ℝ ψ a) :=
    fderiv_comp a ((hf.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds (hψVU haV)))
      ((hψ.contDiffOn.differentiableOn one_ne_zero).differentiableAt
        (hψ.isOpen_source.mem_nhds haV))
  have hsurj : Function.Surjective (fderiv ℝ (f ∘ ψ) a) := by
    rw [hDG]
    by_contra hns
    exact hJ (((Submission.coarea_jacobian_linear_algebra).1 N m (m + k) M f (ψ a)
      (fderiv ℝ ψ a) (hT V W ψ hψ a haV)).2 hns)
  -- The submersion chart `Λ` of `G` at `a`; then `Ψ = ψ ∘ Λ` is a chart of `M` near `x₀`.
  obtain ⟨Ω, Λ, hΩ, hΛC, hΛinj, hΛΩ, haΛ, hΛV, hΛder, hGΛ⟩ :=
    Submission.coarea_straightening_submersion_chart m k V (f ∘ ψ) a hψ.isOpen_source hGC haV
      hsurj
  obtain ⟨O, hO, hΨΩ, hΨC, hΨinj, hΨder, hΨT⟩ :=
    Submission.coarea_straightening_reparametrize_chart N m k M V W ψ Ω Λ hψ (hT V W ψ hψ) hΩ
      hΛC hΛinj hΛΩ hΛV hΛder
  refine ⟨Ω, O, ψ ∘ Λ, hΩ, hO, ?_, hΨC, hΨinj, hΨΩ, hΨder, hGΛ, hΨT⟩
  -- `x₀ = ψ a = Ψ p` for the `p ∈ Ω` with `Λ p = a`, so `x₀ ∈ Ψ(Ω) = O ∩ M`.
  obtain ⟨p, hp, hpa⟩ := haΛ
  have hpO : ψ (Λ p) ∈ O ∩ M := by rw [← hΨΩ]; exact ⟨p, hp, rfl⟩
  rw [hpa] at hpO
  exact hpO.1

end GMT.Ch02
