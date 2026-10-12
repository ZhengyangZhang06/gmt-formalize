import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Semicontinuity.Basic
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter02.AreaLipschitz

/-!
# Simon, *Introduction to GMT*, Chapter 4: Rectifiable `n`-varifolds (printed pp. 85–102)

Frozen problem statement. A rectifiable `n`-varifold `v(M, θ)` in `ℝ^{n+ℓ}` is built from
primitive data exactly as on p. 85: it is the equivalence class of admissible pairs `(M, θ)`
under `Hⁿ`-null modification. Its weight `μ_V = Hⁿ ⌞ θ` is well defined on classes (proved
below), and every other notion (`T_x V`, `div_M`, `∇^M`, `Θⁿ`, `spt V`, stationarity, generalized
mean curvature) is defined from `μ_V`. In particular `T_x V` is the approximate tangent space
*where it exists*; its `μ_V`-a.e. existence is the theorem `ApproxTangentAE` (Ch. 3, 1.9).

Conventions: `B_ρ(ξ)` is the closed ball (Simon's notation), `Hⁿ = μHE[n]` (Mathlib's Euclidean
Hausdorff measure, which equals Simon's `Hⁿ`), `ωₙ` is the Lebesgue measure of the unit ball of
`ℝⁿ`, and `n ≥ 1` (Simon's standing convention for `n`-varifolds).
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal ContDiff CompactlySupported

namespace GMT.Ch04

noncomputable section

/-- The ambient Euclidean space `ℝ^{n+ℓ}` of Simon Ch. 4. -/
abbrev Ambient (n ℓ : ℕ) : Type := EuclideanSpace ℝ (Fin (n + ℓ))

/-- Simon's `ωₙ`: the Lebesgue measure of the unit ball in `ℝⁿ`. -/
def omega (n : ℕ) : ℝ := (volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal

variable {n ℓ : ℕ}

/-! ## §1 Basic definitions -/

/-- Simon Ch. 4, opening paragraph (p. 85): `M ⊆ ℝ^{n+ℓ}` is countably `n`-rectifiable (Ch. 3, 1.1)
and `Hⁿ`-measurable, and `θ` is positive on `M` and locally `Hⁿ`-integrable on `M`
(`∫_{M ∩ K} θ dHⁿ < ∞` for every compact `K`). Values of `θ` off `M` are irrelevant. -/
structure IsRectifiablePair (n : ℕ) (M : Set (Ambient n ℓ)) (θ : Ambient n ℓ → ℝ) : Prop where
  countablyRectifiable : Poincare.SimonGMT.Chapter03.CountablyRectifiable n M
  measurable : NullMeasurableSet M (μHE[n] : Measure (Ambient n ℓ))
  pos : ∀ x ∈ M, 0 < θ x
  locallyIntegrable : ∀ K : Set (Ambient n ℓ), IsCompact K → IntegrableOn θ (M ∩ K) μHE[n]

/-- An admissible pair `(M, θ)` (Simon p. 85). -/
structure RectifiablePair (n ℓ : ℕ) where
  /-- the carrier `M` -/
  M : Set (Ambient n ℓ)
  /-- the multiplicity function `θ` -/
  θ : Ambient n ℓ → ℝ
  isRectifiablePair : IsRectifiablePair n M θ

/-- Simon p. 85: `(M̃, θ̃)` represents the same varifold as `(M, θ)` iff
`Hⁿ((M \ M̃) ∪ (M̃ \ M)) = 0` and `θ̃ = θ` `Hⁿ`-a.e. on `M ∩ M̃`. -/
def RectifiablePair.Equiv (a b : RectifiablePair n ℓ) : Prop :=
  (μHE[n] : Measure (Ambient n ℓ)) ((a.M \ b.M) ∪ (b.M \ a.M)) = 0 ∧
    ∀ᵐ x ∂(μHE[n] : Measure (Ambient n ℓ)).restrict (a.M ∩ b.M), b.θ x = a.θ x

/-- Simon p. 85: the rectifiable `n`-varifold `v(M, θ)` is the equivalence class of `(M, θ)`. -/
def RectifiableVarifold (n ℓ : ℕ) : Type := Quot (@RectifiablePair.Equiv n ℓ)

/-- The class `v(M, θ)` of an admissible pair. -/
def RectifiableVarifold.mk (a : RectifiablePair n ℓ) : RectifiableVarifold n ℓ := Quot.mk _ a

/-- Simon 1.1 (p. 86): the measure `Hⁿ ⌞ θ` of a pair, with `θ ≡ 0` off `M`. -/
def pairWeight (n : ℕ) (M : Set (Ambient n ℓ)) (θ : Ambient n ℓ → ℝ) : Measure (Ambient n ℓ) :=
  ((μHE[n] : Measure (Ambient n ℓ)).restrict M).withDensity fun x ↦ ENNReal.ofReal (θ x)

/-- Equivalent pairs have the same weight, so `μ_V` is well defined on classes. -/
theorem pairWeight_eq_of_equiv {a b : RectifiablePair n ℓ} (h : a.Equiv b) :
    pairWeight n a.M a.θ = pairWeight n b.M b.θ := by
  obtain ⟨h1, h2⟩ := h
  rw [measure_union_null_iff] at h1
  have hab : a.M =ᵐ[(μHE[n] : Measure (Ambient n ℓ))] b.M := ae_eq_set.2 h1
  have hsub : b.M \ (a.M ∩ b.M) ⊆ b.M \ a.M := by
    intro x hx
    exact ⟨hx.1, fun ha ↦ hx.2 ⟨ha, hx.1⟩⟩
  have hib : (a.M ∩ b.M : Set (Ambient n ℓ)) =ᵐ[(μHE[n] : Measure (Ambient n ℓ))] b.M := by
    refine ae_eq_set.2 ⟨?_, measure_mono_null hsub h1.2⟩
    rw [Set.sdiff_eq_empty.mpr Set.inter_subset_right]
    exact measure_empty
  rw [Measure.restrict_congr_set hib] at h2
  unfold pairWeight
  rw [Measure.restrict_congr_set hab]
  exact withDensity_congr_ae (h2.mono fun x hx ↦ by simp only [hx])

namespace RectifiableVarifold

/-- Simon 1.1 (p. 86): the weight measure `μ_V = Hⁿ ⌞ θ` of `V = v(M, θ)`. -/
def weight (V : RectifiableVarifold n ℓ) : Measure (Ambient n ℓ) :=
  Quot.lift (fun a : RectifiablePair n ℓ ↦ pairWeight n a.M a.θ)
    (fun _ _ h ↦ pairWeight_eq_of_equiv h) V

/-- Simon 1.4 (p. 86): `spt V = spt μ_V`. -/
def support (V : RectifiableVarifold n ℓ) : Set (Ambient n ℓ) := V.weight.support

/-- Simon 1.3 (p. 86) with Ch. 3, 1.7 and the remark after 1.2: `P` is the approximate tangent
space of `V` at `x`, i.e. `P` is an `n`-dimensional subspace and for some multiplicity
`c ∈ (0, ∞)`, `λ⁻ⁿ ∫ f(λ⁻¹(y - x)) dμ_V(y) → c ∫_P f dHⁿ` as `λ ↓ 0` for every `f ∈ C_c`.
(By the change of variables `y ↦ λ⁻¹(y - x)` the left side is Simon's
`∫_{η_{x,λ}(M)} f(y) θ(x + λy) dHⁿ(y)`; using `μ_V` makes the notion independent of the
representative, as Simon notes in 1.3; `c = θ(x)` for `Hⁿ`-a.e. `x ∈ M`, see `ApproxTangentAE`.) -/
def IsApproxTangentAt (V : RectifiableVarifold n ℓ) (x : Ambient n ℓ)
    (P : Submodule ℝ (Ambient n ℓ)) : Prop :=
  Module.finrank ℝ P = n ∧ ∃ c : ℝ, 0 < c ∧ ∀ f : C_c(Ambient n ℓ, ℝ),
    Tendsto (fun t : ℝ ↦ (t ^ n)⁻¹ * ∫ y, f (t⁻¹ • (y - x)) ∂V.weight) (𝓝[>] 0)
      (𝓝 (c * ∫ y in (P : Set (Ambient n ℓ)), f y ∂μHE[n]))

open Classical in
/-- Simon 1.3 (p. 86): the tangent space `T_x V`, where it exists (it is unique when it exists).
Where it does not exist we put `⊥`; this junk value only matters on a `μ_V`-null set. -/
def tangentSpace (V : RectifiableVarifold n ℓ) (x : Ambient n ℓ) : Submodule ℝ (Ambient n ℓ) :=
  if h : ∃ P, V.IsApproxTangentAt x P then h.choose else ⊥

/-- Simon 2.3 (p. 88): `div_M X (x) = ∑ⱼ eⱼ · ∇^M Xʲ = trace (DX(x) ∘ p_{T_x V})`. -/
def tangentialDiv (V : RectifiableVarifold n ℓ) (X : Ambient n ℓ → Ambient n ℓ)
    (x : Ambient n ℓ) : ℝ :=
  LinearMap.trace ℝ (Ambient n ℓ)
    ((fderiv ℝ X x).toLinearMap ∘ₗ (V.tangentSpace x).starProjection.toLinearMap)

/-- Simon Ch. 3 §2 / Ch. 4 §5: the tangential gradient `∇^M h (x) = p_{T_x V}(∇h(x))`. -/
def tangentialGradient (V : RectifiableVarifold n ℓ) (h : Ambient n ℓ → ℝ)
    (x : Ambient n ℓ) : Ambient n ℓ :=
  (V.tangentSpace x).starProjection (gradient h x)

/-- Simon 3.2–3.3 (pp. 89–90): `|D^⊥ r|² = |p_{(T_x V)^⊥}(x - ξ)|² / |x - ξ|²`, `r = |x - ξ|`. -/
def normalRadialSq (V : RectifiableVarifold n ℓ) (ξ x : Ambient n ℓ) : ℝ :=
  ‖(V.tangentSpace x)ᗮ.starProjection (x - ξ)‖ ^ 2 / ‖x - ξ‖ ^ 2

/-- Simon 3.9 (p. 91): `Θⁿ(μ_V, ξ) = lim_{ρ↓0} μ_V(B_ρ(ξ)) / (ωₙ ρⁿ)` (as a limit value; its
existence is part of the theorems below). -/
def density (V : RectifiableVarifold n ℓ) (ξ : Ambient n ℓ) : ℝ :=
  limUnder (𝓝[>] (0 : ℝ)) fun ρ ↦ V.weight.real (closedBall ξ ρ) / (omega n * ρ ^ n)

/-- The density quotient `μ_V(B_ρ(ξ)) / (ωₙ ρⁿ)` converges to `t` as `ρ ↓ 0`. -/
def HasDensityAt (V : RectifiableVarifold n ℓ) (ξ : Ambient n ℓ) (t : ℝ) : Prop :=
  Tendsto (fun ρ ↦ V.weight.real (closedBall ξ ρ) / (omega n * ρ ^ n)) (𝓝[>] 0) (𝓝 t)

/-- Simon 2.4 / 3.14: `X ∈ C¹_c(U; ℝ^{n+ℓ})` (a `C¹` field, compactly supported in `U`). -/
def IsTestField (U : Set (Ambient n ℓ)) (X : Ambient n ℓ → Ambient n ℓ) : Prop :=
  ContDiff ℝ 1 X ∧ HasCompactSupport X ∧ tsupport X ⊆ U

/-- Simon 2.4 (p. 88), in the equivalent form stated there: `V` is stationary in `U` iff
`∫ div_M X dμ_V = 0` for every `X ∈ C¹_c(U; ℝ^{n+ℓ})` (equivalence with the variational form:
`StationaryIffVariational`). -/
def IsStationaryIn (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)) : Prop :=
  ∀ X, IsTestField U X → ∫ x, V.tangentialDiv X x ∂V.weight = 0

/-- Simon 3.14 (p. 92): `V` has generalized mean curvature `H` in `U`:
`∫ div_M X dμ_V = -∫ X · H dμ_V` for all `X ∈ C¹_c(U; ℝ^{n+ℓ})`. Local `μ_V`-integrability of
`H` on `U` (needed for the right side to make sense for all `X`, and equivalent to it) is
included. -/
def HasMeanCurvatureIn (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ))
    (H : Ambient n ℓ → Ambient n ℓ) : Prop :=
  LocallyIntegrableOn H U V.weight ∧
    ∀ X, IsTestField U X →
      ∫ x, V.tangentialDiv X x ∂V.weight = -∫ x, inner ℝ (X x) (H x) ∂V.weight

/-- Simon §4–§6 hypothesis "`H ∈ L^p_loc(μ_V)` in `U`". -/
def IsLocallyLp (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ))
    (H : Ambient n ℓ → Ambient n ℓ) (p : ℝ) : Prop :=
  ∀ K, IsCompact K → K ⊆ U → MemLp H (ENNReal.ofReal p) (V.weight.restrict K)

/-- Simon 3.13, 4.10, §5, 6.3 hypothesis "`θ ≥ α` `μ_V`-a.e. in `U`" (equivalently `Hⁿ`-a.e. on
`M ∩ U`), for a representative `(M, θ)` of `V` (all representatives agree a.e.). -/
def MultiplicityGE (V : RectifiableVarifold n ℓ) (α : ℝ) (U : Set (Ambient n ℓ)) : Prop :=
  ∃ a : RectifiablePair n ℓ, mk a = V ∧
    ∀ᵐ x ∂(μHE[n] : Measure (Ambient n ℓ)).restrict (a.M ∩ U), α ≤ a.θ x

/-- Simon 3.12 (p. 91): the canonical carrier `M_V = {x ∈ U : Θⁿ(μ_V, x) > 0}`. -/
def canonicalCarrier (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)) : Set (Ambient n ℓ) :=
  {x | x ∈ U ∧ 0 < V.density x}

end RectifiableVarifold

open RectifiableVarifold

/-- Simon 2.1 (p. 87): `{φ_t}_{-ε<t<ε}` is a smooth one-parameter family of diffeomorphisms with
`φ₀ = id` and `φ_t = id` off the compact set `K` (families of diffeomorphisms of an open `U ⊇ K`
fixing `U \ K` are exactly restrictions of such families of `ℝ^{n+ℓ}`). -/
structure IsCompactVariation (φ : ℝ → Ambient n ℓ → Ambient n ℓ) (ε : ℝ)
    (K : Set (Ambient n ℓ)) : Prop where
  pos : 0 < ε
  compact : IsCompact K
  smooth : ContDiffOn ℝ ∞ (fun q : ℝ × Ambient n ℓ ↦ φ q.1 q.2) (Ioo (-ε) ε ×ˢ univ)
  diffeo : ∀ t ∈ Ioo (-ε) ε, Function.Bijective (φ t) ∧ ContDiff ℝ ∞ (Function.invFun (φ t))
  init : ∀ x, φ 0 x = x
  fixed : ∀ t ∈ Ioo (-ε) ε, ∀ x ∉ K, φ t x = x

/-- Simon 1.2, 1.5, 1.6 (pp. 86–87): for injective `f`, the mass
`M(f_#(V ⌞ K)) = ∫_{f(M ∩ K)} θ ∘ f⁻¹ dHⁿ` of the image of `V ⌞ K = v(M ∩ K, θ)`, computed from
the representative `a = (M, θ)` of `V`. -/
def imageMass (a : RectifiablePair n ℓ) (f : Ambient n ℓ → Ambient n ℓ)
    (K : Set (Ambient n ℓ)) : ℝ≥0∞ :=
  ∫⁻ y in f '' (a.M ∩ K), ENNReal.ofReal (a.θ (Function.invFun f y)) ∂μHE[n]

/-- The corrected constant `κ = (p - n)/(4p)` of Simon 4.2 (printed: `p/(4(p - n))`). -/
def lpKappa (n : ℕ) (p : ℝ) : ℝ := (p - n) / (4 * p)

/-! ## Headline results -/

/-- **Ch. 4, 1.3 + Ch. 3, 1.8(2), 1.9 (pp. 75, 86).** For every representative `(M, θ)` of
`V = v(M, θ)` and `Hⁿ`-a.e. `x ∈ M`: the approximate tangent space `T_x V` exists and is unique,
it is the approximate tangent space of `M` with respect to `θ` in the sense of Ch. 3, 1.7
(limit `θ(x) ∫_P f`), and `Θⁿ(μ_V, x) = θ(x)`. -/
def ApproxTangentAE : Prop :=
  ∀ (n ℓ : ℕ) (a : RectifiablePair n ℓ), 0 < n →
    ∀ᵐ x ∂(μHE[n] : Measure (Ambient n ℓ)).restrict a.M,
      (∃! P, (mk a).IsApproxTangentAt x P) ∧
      Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n a.M a.θ x
        ((mk a).tangentSpace x) ∧
      (mk a).HasDensityAt x (a.θ x)

/-- **Ch. 4, 2.2 (p. 88), first variation formula.** If `{φ_t}` is as in 2.1 with compact `K`
and initial velocity `X = ∂φ_t/∂t|_{t=0}`, then `t ↦ M(φ_t#(V ⌞ K))` is differentiable at
`0` with derivative `∫ div_M X dμ_V`. -/
def FirstVariationFormula : Prop :=
  ∀ (n ℓ : ℕ) (a : RectifiablePair n ℓ) (φ : ℝ → Ambient n ℓ → Ambient n ℓ) (ε : ℝ)
    (K : Set (Ambient n ℓ)), 0 < n → IsCompactVariation φ ε K →
    HasDerivAt (fun t ↦ (imageMass a (φ t) K).toReal)
      (∫ x, (mk a).tangentialDiv (fun y ↦ deriv (fun t ↦ φ t y) 0) x ∂(mk a).weight) 0

/-- **Ch. 4, 2.4 (p. 88), stationarity.** For `U` open, `V = v(M, θ)` is stationary in `U`
(`∫ div_M X dμ_V = 0` for all `X ∈ C¹_c(U)`) iff `d/dt M(φ_t#(V ⌞ K))|_{t=0} = 0` for every
family as in 2.1 with `K ⊆ U`. -/
def StationaryIffVariational : Prop :=
  ∀ (n ℓ : ℕ) (a : RectifiablePair n ℓ) (U : Set (Ambient n ℓ)), 0 < n → IsOpen U →
    ((mk a).IsStationaryIn U ↔
      ∀ (φ : ℝ → Ambient n ℓ → Ambient n ℓ) (ε : ℝ) (K : Set (Ambient n ℓ)),
        IsCompactVariation φ ε K → K ⊆ U → HasDerivAt (fun t ↦ (imageMass a (φ t) K).toReal) 0 0)

/-- **Ch. 4, 3.6, 3.8, 3.10 (pp. 90–91), monotonicity identity.** If `V` is stationary in the
open set `U` and `B_R(ξ) ⊆ U`, then for `0 < σ ≤ ρ < R`
`ρ⁻ⁿ μ_V(B_ρ(ξ)) - σ⁻ⁿ μ_V(B_σ(ξ)) = ∫_{B_ρ(ξ) \ B_σ(ξ)} |D^⊥r|² / rⁿ dμ_V`; hence
`ρ ↦ ρ⁻ⁿ μ_V(B_ρ(ξ))` is increasing on `(0, R)`, and for `0 < ρ < R` the integrand is
`μ_V`-integrable on `B_ρ(ξ)` with
`(ωₙρⁿ)⁻¹ μ_V(B_ρ(ξ)) - Θⁿ(μ_V, ξ) = ωₙ⁻¹ ∫_{B_ρ(ξ)} |D^⊥r|² / rⁿ dμ_V`. -/
def StationaryMonotonicity : Prop :=
  ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)) (ξ : Ambient n ℓ) (R : ℝ),
    0 < n → IsOpen U → V.IsStationaryIn U → closedBall ξ R ⊆ U →
    (∀ σ ρ : ℝ, 0 < σ → σ ≤ ρ → ρ < R →
      V.weight.real (closedBall ξ ρ) / ρ ^ n - V.weight.real (closedBall ξ σ) / σ ^ n =
        ∫ x in closedBall ξ ρ \ closedBall ξ σ, V.normalRadialSq ξ x / ‖x - ξ‖ ^ n ∂V.weight) ∧
    MonotoneOn (fun ρ ↦ V.weight.real (closedBall ξ ρ) / ρ ^ n) (Ioo 0 R) ∧
    ∀ ρ : ℝ, 0 < ρ → ρ < R →
      IntegrableOn (fun x ↦ V.normalRadialSq ξ x / ‖x - ξ‖ ^ n) (closedBall ξ ρ) V.weight ∧
      V.weight.real (closedBall ξ ρ) / (omega n * ρ ^ n) - V.density ξ =
        (omega n)⁻¹ * ∫ x in closedBall ξ ρ, V.normalRadialSq ξ x / ‖x - ξ‖ ^ n ∂V.weight

/-- **Ch. 4, 3.9, 3.11 (p. 91).** If `V` is stationary in the open set `U`, then
`Θⁿ(μ_V, ξ)` exists (as a real limit) at every `ξ ∈ U`, and `Θⁿ(μ_V, ·)` is upper
semicontinuous on `U`. -/
def StationaryDensity : Prop :=
  ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)),
    0 < n → IsOpen U → V.IsStationaryIn U →
    (∀ ξ ∈ U, V.HasDensityAt ξ (V.density ξ)) ∧ UpperSemicontinuousOn V.density U

/-- **Ch. 4, 3.12, 3.13 (p. 91), canonical representative.** If `V` is stationary in the open
set `U`, then `(M_V, θ_V) = ({x ∈ U : Θⁿ(μ_V, x) > 0}, Θⁿ(μ_V, ·))` is an admissible pair with
`v(M_V, θ_V) = V ⌞ U` (equality of weights); `{x ∈ M_V : θ_V(x) ≥ α}` is relatively closed in
`U` for each `α > 0`; and if `θ ≥ α > 0` `Hⁿ`-a.e. on `M ∩ U` then `M_V = spt V ∩ U` and
`θ_V ≥ α` at every point of `M_V`. -/
def CanonicalRepresentative : Prop :=
  ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)),
    0 < n → IsOpen U → V.IsStationaryIn U →
    IsRectifiablePair n (V.canonicalCarrier U) V.density ∧
    pairWeight n (V.canonicalCarrier U) V.density = V.weight.restrict U ∧
    (∀ α : ℝ, 0 < α → ∃ C, IsClosed C ∧ {x | x ∈ V.canonicalCarrier U ∧ α ≤ V.density x} = C ∩ U) ∧
    ∀ α : ℝ, 0 < α → V.MultiplicityGE α U →
      V.canonicalCarrier U = V.support ∩ U ∧ ∀ x ∈ V.canonicalCarrier U, α ≤ V.density x

/-- **Ch. 4, 3.17 (pp. 92–93) and the remark after it, bounded mean curvature.** If `V` has
generalized mean curvature `H` in the open set `U` with `|H| ≤ Λ` (`μ_V`-a.e. in `U`), then for
every `B_R(ξ) ⊆ U` there are `F` with `F(ρ) ∈ [e^{-Λρ}, e^{Λρ}]` (`0 < ρ < R`) and `G` with
`G(σ, ρ) ∈ [e^{-ΛR}, e^{ΛR}]` such that for `0 < σ ≤ ρ < R`
`F(ρ)ρ⁻ⁿμ_V(B_ρ(ξ)) - F(σ)σ⁻ⁿμ_V(B_σ(ξ)) = G(σ,ρ) ∫_{B_ρ(ξ) \ B_σ(ξ)} r⁻ⁿ|D^⊥r|² dμ_V`;
moreover `Θⁿ(μ_V, ·)` exists everywhere in `U` and is upper semicontinuous on `U` (the printed
"`N ∩ U`" is a typo for `U`). -/
def BoundedCurvatureMonotonicity : Prop :=
  ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ))
    (H : Ambient n ℓ → Ambient n ℓ) (Λ : ℝ),
    0 < n → IsOpen U → V.HasMeanCurvatureIn U H → 0 ≤ Λ →
    (∀ᵐ x ∂V.weight, x ∈ U → ‖H x‖ ≤ Λ) →
    (∀ (ξ : Ambient n ℓ) (R : ℝ), closedBall ξ R ⊆ U →
      ∃ (F : ℝ → ℝ) (G : ℝ → ℝ → ℝ),
        (∀ ρ ∈ Ioo 0 R, F ρ ∈ Icc (Real.exp (-(Λ * ρ))) (Real.exp (Λ * ρ))) ∧
        ∀ σ ρ : ℝ, 0 < σ → σ ≤ ρ → ρ < R →
          G σ ρ ∈ Icc (Real.exp (-(Λ * R))) (Real.exp (Λ * R)) ∧
          F ρ * (V.weight.real (closedBall ξ ρ) / ρ ^ n) -
              F σ * (V.weight.real (closedBall ξ σ) / σ ^ n) =
            G σ ρ * ∫ x in closedBall ξ ρ \ closedBall ξ σ,
              V.normalRadialSq ξ x / ‖x - ξ‖ ^ n ∂V.weight) ∧
    (∀ ξ ∈ U, V.HasDensityAt ξ (V.density ξ)) ∧ UpperSemicontinuousOn V.density U

/-- **Ch. 4, 3.18 (p. 93), logarithmic error.** If `V` has generalized mean curvature `H` in the
open set `U`, `B_ρ(ξ) ⊆ U`, `0 < σ < ρ`, and `τ^{1-n} ∫_{B_τ(ξ)} |H| dμ_V ≤ δ` for all
`σ ≤ τ ≤ ρ`, then
`|ρ⁻ⁿμ_V(B_ρ(ξ)) - σ⁻ⁿμ_V(B_σ(ξ)) - ∫_{B_ρ(ξ) \ B_σ(ξ)} r⁻ⁿ|D^⊥r|² dμ_V| ≤ δ log(ρ/σ)`. -/
def LogarithmicMonotonicityError : Prop :=
  ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ))
    (H : Ambient n ℓ → Ambient n ℓ) (ξ : Ambient n ℓ) (σ ρ δ : ℝ),
    0 < n → IsOpen U → V.HasMeanCurvatureIn U H → closedBall ξ ρ ⊆ U → 0 < σ → σ < ρ →
    (∀ τ ∈ Icc σ ρ, τ ^ (1 - (n : ℝ)) * ∫ x in closedBall ξ τ, ‖H x‖ ∂V.weight ≤ δ) →
    |V.weight.real (closedBall ξ ρ) / ρ ^ n - V.weight.real (closedBall ξ σ) / σ ^ n -
        ∫ x in closedBall ξ ρ \ closedBall ξ σ, V.normalRadialSq ξ x / ‖x - ξ‖ ^ n ∂V.weight| ≤
      δ * Real.log (ρ / σ)

/-- **Ch. 4, 4.2, 4.5, 4.7, 4.8 (pp. 93–94), `Lᵖ` mean-curvature monotonicity (corrected `κ`).**
Let `V` have generalized mean curvature `H ∈ L^p_loc(μ_V)` in the open set `U`, `p > n`,
`B_R(ξ) ⊆ U`, and `(R^{p-n} ∫_{B_R(ξ)} |H|^p dμ_V)^{1/p} ≤ κΛ` with `κ = (p-n)/(4p)`.
Then there are `F` and `G` such that, with `E(ρ) = F(ρ) - 1`, for `0 < ρ ≤ R`
`e^{-½Λ(ρ/R)^{1-n/p}} ≤ F(ρ) ≤ e^{½Λ(ρ/R)^{1-n/p}}` and `|E(ρ)| ≤ ½e^{½Λ}Λ(ρ/R)^{1-n/p}` (4.5);
for `0 < σ ≤ ρ ≤ R`, `G(σ,ρ) ∈ [e^{-Λ}, e^{Λ}]` and
`(F(ρ)ρ⁻ⁿμ_V(B_ρ) + E(ρ)) - (F(σ)σ⁻ⁿμ_V(B_σ) + E(σ)) = G(σ,ρ) ∫_{B_ρ \ B_σ} |D^⊥r|²/rⁿ dμ_V` (4.7);
and `F(ρ)ρ⁻ⁿμ_V(B_ρ(ξ)) + E(ρ)` is increasing on `(0, R]` (4.8).
Erratum: the printed `κ = p/(4(p-n))` does not give the claimed `∫₀^ρ|F₀| ≤ ½Λ(ρ/R)^{1-n/p}`;
the required value is `κ = (p-n)/(4p)`. -/
def LpMonotonicity : Prop :=
  ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ))
    (H : Ambient n ℓ → Ambient n ℓ) (p : ℝ) (ξ : Ambient n ℓ) (R Λ : ℝ),
    0 < n → IsOpen U → V.HasMeanCurvatureIn U H → (n : ℝ) < p → V.IsLocallyLp U H p →
    0 < R → closedBall ξ R ⊆ U →
    (R ^ (p - n) * ∫ x in closedBall ξ R, ‖H x‖ ^ p ∂V.weight) ^ (1 / p) ≤ lpKappa n p * Λ →
    ∃ (F : ℝ → ℝ) (G : ℝ → ℝ → ℝ),
      (∀ ρ ∈ Ioc 0 R,
        Real.exp (-(Λ / 2 * (ρ / R) ^ (1 - (n : ℝ) / p))) ≤ F ρ ∧
        F ρ ≤ Real.exp (Λ / 2 * (ρ / R) ^ (1 - (n : ℝ) / p)) ∧
        |F ρ - 1| ≤ Real.exp (Λ / 2) / 2 * Λ * (ρ / R) ^ (1 - (n : ℝ) / p)) ∧
      (∀ σ ρ : ℝ, 0 < σ → σ ≤ ρ → ρ ≤ R →
        G σ ρ ∈ Icc (Real.exp (-Λ)) (Real.exp Λ) ∧
        (F ρ * (V.weight.real (closedBall ξ ρ) / ρ ^ n) + (F ρ - 1)) -
            (F σ * (V.weight.real (closedBall ξ σ) / σ ^ n) + (F σ - 1)) =
          G σ ρ * ∫ x in closedBall ξ ρ \ closedBall ξ σ,
            V.normalRadialSq ξ x / ‖x - ξ‖ ^ n ∂V.weight) ∧
      MonotoneOn (fun ρ ↦ F ρ * (V.weight.real (closedBall ξ ρ) / ρ ^ n) + (F ρ - 1)) (Ioc 0 R)

/-- **Ch. 4, 4.9 (p. 95).** If `V` has generalized mean curvature `H ∈ L^p_loc(μ_V)` in the open
set `U` with `p > n`, then `Θⁿ(μ_V, ξ)` exists at every `ξ ∈ U` and is upper semicontinuous
on `U`. -/
def LpDensity : Prop :=
  ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ))
    (H : Ambient n ℓ → Ambient n ℓ) (p : ℝ),
    0 < n → IsOpen U → V.HasMeanCurvatureIn U H → (n : ℝ) < p → V.IsLocallyLp U H p →
    (∀ ξ ∈ U, V.HasDensityAt ξ (V.density ξ)) ∧ UpperSemicontinuousOn V.density U

/-- **Ch. 4, 4.10(1) (p. 95).** If moreover `θ ≥ 1` `μ_V`-a.e. in `U`, then `Θⁿ(μ_V, x) ≥ 1` at
every `x ∈ spt V ∩ U`, and `V ⌞ U = v(M_*, θ_*)` with `M_* = spt μ_V ∩ U` (relatively closed in
`U`), `θ_* = Θⁿ(μ_V, ·)`: `(M_*, θ_*)` is an admissible pair whose weight is `μ_V ⌞ U`. -/
def LpSupportRepresentation : Prop :=
  ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ))
    (H : Ambient n ℓ → Ambient n ℓ) (p : ℝ),
    0 < n → IsOpen U → V.HasMeanCurvatureIn U H → (n : ℝ) < p → V.IsLocallyLp U H p →
    V.MultiplicityGE 1 U →
    (∀ x ∈ V.support ∩ U, 1 ≤ V.density x) ∧
    IsRectifiablePair n (V.support ∩ U) V.density ∧
    pairWeight n (V.support ∩ U) V.density = V.weight.restrict U

/-- **Ch. 4, 5.6 (p. 97), Poincaré inequality.** For `α ∈ (0,1)`, `Γ > 0` there are
`β = β(n,α,Γ) ∈ (0, ½)` and `c = c(n,α,Γ) > 0` (independent of `ℓ`) such that: if `V` has
generalized mean curvature `H` in the open set `U`, `|H| ≤ Λ`, `θ ≥ 1` `μ_V`-a.e. in `U`,
`h ∈ C¹(U)`, `h ≥ 0`, `B_{2ρ}(ξ) ⊆ U`, `μ_V{x ∈ B_ρ(ξ) : h(x) > 0} ≤ (1-α)ωₙρⁿ`,
`e^{Λρ} ≤ 1 + α` and `μ_V(B_{2ρ}(ξ)) ≤ Γρⁿ`, then
`∫_{B_{βρ}(ξ)} h dμ_V ≤ c ρ ∫_{B_ρ(ξ)} |∇^M h| dμ_V`. -/
def PoincareInequality : Prop :=
  ∀ n : ℕ, 0 < n → ∀ α Γ : ℝ, 0 < α → α < 1 → 0 < Γ →
    ∃ β c : ℝ, 0 < β ∧ β < 1 / 2 ∧ 0 < c ∧
      ∀ (ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ))
        (H : Ambient n ℓ → Ambient n ℓ) (Λ : ℝ) (h : Ambient n ℓ → ℝ) (ξ : Ambient n ℓ) (ρ : ℝ),
        IsOpen U → V.HasMeanCurvatureIn U H → (∀ᵐ x ∂V.weight, x ∈ U → ‖H x‖ ≤ Λ) →
        V.MultiplicityGE 1 U → ContDiffOn ℝ 1 h U → (∀ x ∈ U, 0 ≤ h x) →
        0 < ρ → closedBall ξ (2 * ρ) ⊆ U →
        V.weight.real {x | x ∈ closedBall ξ ρ ∧ 0 < h x} ≤ (1 - α) * omega n * ρ ^ n →
        Real.exp (Λ * ρ) ≤ 1 + α →
        V.weight.real (closedBall ξ (2 * ρ)) ≤ Γ * ρ ^ n →
        ∫ x in closedBall ξ (β * ρ), h x ∂V.weight ≤
          c * ρ * ∫ x in closedBall ξ ρ, ‖V.tangentialGradient h x‖ ∂V.weight

/-- **Ch. 4, 5.7 and 5.9 (pp. 98–100), Michael–Simon Sobolev inequality.** For `n ≥ 2` there is
`c = c(n)` (independent of `ℓ`) such that if `V` has generalized mean curvature `H` (merely
`L¹_loc`) in the open set `U`, `θ ≥ 1` `μ_V`-a.e. in `U`, and `h ∈ C¹_c(U)`, `h ≥ 0`, then
`(∫ h^{n/(n-1)} dμ_V)^{(n-1)/n} ≤ c ∫ (|∇^M h| + h|H|) dμ_V`.
Correction: the printed statement has no dimension restriction, but the exponent `n/(n-1)`
requires `n ≥ 2`. -/
def SobolevInequality : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∃ c : ℝ, 0 < c ∧
    ∀ (ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ))
      (H : Ambient n ℓ → Ambient n ℓ) (h : Ambient n ℓ → ℝ),
      IsOpen U → V.HasMeanCurvatureIn U H → V.MultiplicityGE 1 U →
      ContDiffOn ℝ 1 h U → HasCompactSupport h → tsupport h ⊆ U → (∀ x, 0 ≤ h x) →
      (∫ x, h x ^ ((n : ℝ) / ((n : ℝ) - 1)) ∂V.weight) ^ (((n : ℝ) - 1) / n) ≤
        c * ∫ x, (‖V.tangentialGradient h x‖ + h x * ‖H x‖) ∂V.weight

/-- **Ch. 4, 6.1 (p. 100).** If `V` has (`L¹_loc`) generalized mean curvature `H` in
`U = ℝ^{n+ℓ} \ B_R(ξ)` with `n⁻¹|H(x)·(x - ξ)| < 1` `μ_V`-a.e. in `U`, and `spt V` is compact,
then `spt V ⊆ B_R(ξ)`. -/
def SupportInBall : Prop :=
  ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (H : Ambient n ℓ → Ambient n ℓ)
    (ξ : Ambient n ℓ) (R : ℝ),
    0 < n → 0 ≤ R → V.HasMeanCurvatureIn (closedBall ξ R)ᶜ H →
    (∀ᵐ x ∂V.weight, x ∈ (closedBall ξ R)ᶜ → (n : ℝ)⁻¹ * |inner ℝ (H x) (x - ξ)| < 1) →
    IsCompact V.support → V.support ⊆ closedBall ξ R

/-- **Ch. 4, 6.2 (p. 101), convex hull property.** If `spt V` is compact and `V` is stationary
in `ℝ^{n+ℓ} \ K` with `K` compact, then `spt V ⊆ conv K`. -/
def ConvexHullProperty : Prop :=
  ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (K : Set (Ambient n ℓ)),
    0 < n → IsCompact K → IsCompact V.support → V.IsStationaryIn Kᶜ →
    V.support ⊆ convexHull ℝ K

/-- **Ch. 4, 6.3 (p. 101).** If `θ ≥ 1` `μ_V`-a.e. in `U`, `V` has generalized mean curvature
`H ∈ L^p_loc(μ_V)` in the open set `U` with `p > n`, and the approximate tangent space `T_x V`
exists at `x ∈ U`, then it is a classical tangent plane of `spt V`:
`sup {ρ⁻¹ dist(y - x, T_x V) : y ∈ spt V ∩ B_ρ(x)} → 0` as `ρ ↓ 0` (the set is nonempty since
`x ∈ spt V`, and bounded by `1`, so `sSup` is the genuine supremum). Erratum: the printed `dist(y, T_x V)` must be `dist(y - x, T_x V)` (`T_x V` is a linear
subspace). -/
def ClassicalTangent : Prop :=
  ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ))
    (H : Ambient n ℓ → Ambient n ℓ) (p : ℝ) (x : Ambient n ℓ) (P : Submodule ℝ (Ambient n ℓ)),
    0 < n → IsOpen U → V.HasMeanCurvatureIn U H → V.MultiplicityGE 1 U → (n : ℝ) < p →
    V.IsLocallyLp U H p → x ∈ U → V.IsApproxTangentAt x P →
    Tendsto (fun ρ : ℝ ↦ sSup ((fun y ↦ ρ⁻¹ * infDist (y - x) (P : Set (Ambient n ℓ))) ''
      (V.support ∩ closedBall x ρ))) (𝓝[>] 0) (𝓝 0)

/-- **Ch. 4, 1.1 (p. 86): `μ_V = Hⁿ ⌞ θ`.** The weight of `V = v(M, θ)` is finite on compact
sets, and `∫ g dμ_V = ∫_M θ g dHⁿ` for every `g : ℝ^{n+ℓ} → ℝ` (Bochner integrals; both sides
vanish together when not integrable). -/
theorem Submission.ts_pwb_pair_weight_integral : ∀ (n ℓ : ℕ) (a : RectifiablePair n ℓ), IsFiniteMeasureOnCompacts (mk a).weight ∧ ∀ g : Ambient n ℓ → ℝ, ∫ y, g y ∂(mk a).weight = ∫ y in a.M, a.θ y * g y ∂μHE[n] := by
  intro n ℓ a
  have hM := a.isRectifiablePair.measurable
  -- `θ` is a.e.-strongly measurable on `M = ⋃ₖ (M ∩ B_k(0))`, being integrable on each piece.
  have hθ : AEStronglyMeasurable a.θ ((μHE[n] : Measure (Ambient n ℓ)).restrict a.M) := by
    have hU : a.M = ⋃ k : ℕ, a.M ∩ closedBall (0 : Ambient n ℓ) k := by
      ext y
      simp only [mem_iUnion, mem_inter_iff, mem_closedBall, dist_zero_right]
      constructor
      · intro hy
        obtain ⟨k, hk⟩ := exists_nat_ge ‖y‖
        exact ⟨k, hy, hk⟩
      · rintro ⟨k, hy, -⟩
        exact hy
    rw [hU, aestronglyMeasurable_iUnion_iff]
    intro k
    exact (a.isRectifiablePair.locallyIntegrable _ (isCompact_closedBall _ _)).aestronglyMeasurable
  -- `μ_V` is definitionally `(Hⁿ ⌞ M).withDensity (ofReal ∘ θ)`.
  have hw : (mk a).weight = ((μHE[n] : Measure (Ambient n ℓ)).restrict a.M).withDensity
      (fun x ↦ ENNReal.ofReal (a.θ x)) := rfl
  refine ⟨⟨fun K hK ↦ ?_⟩, fun g ↦ ?_⟩
  -- `μ_V(K) = ∫⁻_{K ∩ M} ofReal θ dHⁿ ≤ ∫⁻_{K ∩ M} |θ| dHⁿ < ∞`.
  · rw [hw, withDensity_apply _ hK.measurableSet, Measure.restrict_restrict hK.measurableSet]
    have hint := a.isRectifiablePair.locallyIntegrable K hK
    rw [inter_comm] at hint
    calc ∫⁻ x in K ∩ a.M, ENNReal.ofReal (a.θ x) ∂μHE[n]
        ≤ ∫⁻ x in K ∩ a.M, ‖a.θ x‖ₑ ∂μHE[n] := lintegral_mono fun x ↦ Real.ofReal_le_enorm _
      _ < ⊤ := hint.2
  -- `∫ g dμ_V = ∫_M (ofReal θ).toReal • g dHⁿ`, and `(ofReal θ).toReal = θ` on `M`.
  · rw [hw, integral_withDensity_eq_integral_toReal_smul₀
      (f := fun x ↦ ENNReal.ofReal (a.θ x))
      (ENNReal.measurable_ofReal.comp_aemeasurable hθ.aemeasurable)
      (Eventually.of_forall fun x ↦ ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem₀ hM] with y hy
    simp [ENNReal.toReal_ofReal (a.isRectifiablePair.pos y hy).le]
/-- **Upper density theorem (Simon Ch. 1, 3.6, localized as in Remark 3.7(2)).** If `ν` is finite
on compact sets and `A ⊆ ℝ^{n+ℓ}` is Borel, then for `Hⁿ`-a.e. `x ∉ A`, `ν(A ∩ B_r(x)) / rⁿ → 0`
as `r ↓ 0`. -/
theorem Submission.ts_pwb_upper_density_vanish_ae : ∀ (n ℓ : ℕ) (ν : Measure (Ambient n ℓ)) (A : Set (Ambient n ℓ)), IsFiniteMeasureOnCompacts ν → MeasurableSet A → ∀ᵐ x ∂(μHE[n] : Measure (Ambient n ℓ)), x ∉ A → Tendsto (fun r : ℝ ↦ ν.real (A ∩ closedBall x r) / r ^ n) (𝓝[>] 0) (𝓝 0) := by
  intro n ℓ ν A hν hA
  -- `T k m`: the points `x ∉ A` with `‖x‖ < m` such that `rⁿ ≤ k ν(A ∩ B_r(x))` for arbitrarily
  -- small `r > 0`.
  set T : ℕ → ℕ → Set (Ambient n ℓ) := fun k m ↦ {x | x ∉ A ∧ ‖x‖ < m ∧
    ∃ᶠ r in 𝓝[>] (0 : ℝ), r ^ n ≤ k * ν.real (A ∩ closedBall x r)}
  -- Each `T k m` is `μH[n]`-null.
  have hTnull : ∀ k m : ℕ, (μH[n] : Measure (Ambient n ℓ)) (T k m) = 0 := by
    intro k m
    set A' : Set (Ambient n ℓ) := A ∩ ball 0 ((m : ℝ) + 1)
    have hA'meas : MeasurableSet A' := hA.inter measurableSet_ball
    have hA'fin : ν A' ≠ ⊤ :=
      ((measure_mono (inter_subset_right.trans ball_subset_closedBall)).trans_lt
        (isCompact_closedBall _ _).measure_lt_top).ne
    -- Covering estimate: `μH[n](T k m) ≤ 8ⁿ k ν(A' \ F)` for every closed `F ⊆ A'`.
    have hcov : ∀ F : Set (Ambient n ℓ), IsClosed F → F ⊆ A' →
        (μH[n] : Measure (Ambient n ℓ)) (T k m) ≤ 8 ^ n * ((k : ℝ≥0∞) * ν (A' \ F)) := by
      intro F hF hFA'
      set S := A' \ F
      have hSmeas : MeasurableSet S := hA'meas.diff hF.measurableSet
      -- Every point of `T k m` is the center of arbitrarily small balls `B_r` with
      -- `rⁿ ≤ k ν(S ∩ B_r)`.
      have hfine : ∀ x ∈ T k m, ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧ r ≤ δ ∧
          ENNReal.ofReal r ^ n ≤ (k : ℝ≥0∞) * ν (S ∩ closedBall x r) := by
        rintro x ⟨hxA, hxm, hfreq⟩ δ hδ
        have hxF : x ∉ F := fun h ↦ hxA (hFA' h).1
        obtain ⟨ρ, hρ, hρF⟩ := Metric.isOpen_iff.1 hF.isOpen_compl x hxF
        obtain ⟨r, hrle, hr⟩ :=
          (hfreq.and_eventually (Ioo_mem_nhdsGT (lt_min hρ (lt_min one_pos hδ)))).exists
        have hr0 : 0 < r := hr.1
        have hrρ : r < ρ := hr.2.trans_le (min_le_left _ _)
        have hr1 : r < 1 := hr.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
        have hrδ : r ≤ δ := hr.2.le.trans ((min_le_right _ _).trans (min_le_right _ _))
        have hsub : A ∩ closedBall x r ⊆ S ∩ closedBall x r := by
          rintro y ⟨hyA, hyr⟩
          rw [mem_closedBall] at hyr
          refine ⟨⟨⟨hyA, ?_⟩, ?_⟩, hyr⟩
          · rw [mem_ball, dist_zero_right]
            have h1 := norm_le_insert' y x
            rw [← dist_eq_norm] at h1
            linarith
          · exact hρF (mem_ball.2 (hyr.trans_lt hrρ))
        refine ⟨r, hr0, hrδ, ?_⟩
        calc ENNReal.ofReal r ^ n = ENNReal.ofReal (r ^ n) := (ENNReal.ofReal_pow hr0.le n).symm
          _ ≤ ENNReal.ofReal (k * ν.real (A ∩ closedBall x r)) := ENNReal.ofReal_le_ofReal hrle
          _ = (k : ℝ≥0∞) * ν (A ∩ closedBall x r) := by
            rw [ENNReal.ofReal_mul (Nat.cast_nonneg k), ENNReal.ofReal_natCast,
              ofReal_measureReal ((measure_mono inter_subset_right).trans_lt
                (isCompact_closedBall x r).measure_lt_top).ne]
          _ ≤ (k : ℝ≥0∞) * ν (S ∩ closedBall x r) := mul_le_mul_right (measure_mono hsub) _
      -- Vitali covering at scale `δ`: a countable disjoint family of good balls whose
      -- 4-fold enlargements cover `T k m`.
      have hvit : ∀ δ : ℝ, 0 < δ → ∃ u : Set (Ambient n ℓ × ℝ), u.Countable ∧
          (∀ p ∈ u, 0 < p.2 ∧ p.2 ≤ δ) ∧ T k m ⊆ ⋃ p : u, closedBall p.1.1 (4 * p.1.2) ∧
          ∑' p : u, ENNReal.ofReal p.1.2 ^ n ≤ (k : ℝ≥0∞) * ν S := by
        intro δ hδ
        obtain ⟨u, hut, hudisj, hucov⟩ :=
          Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall
            {p : Ambient n ℓ × ℝ | 0 < p.2 ∧ p.2 ≤ δ ∧
              ENNReal.ofReal p.2 ^ n ≤ (k : ℝ≥0∞) * ν (S ∩ closedBall p.1 p.2)}
            Prod.fst Prod.snd δ (fun p hp ↦ hp.2.1) 4 (by norm_num)
        have hucount : u.Countable := hudisj.countable_of_nonempty_interior fun p hp ↦
          ⟨p.1, interior_mono ball_subset_closedBall
            (by rw [isOpen_ball.interior_eq]; exact mem_ball_self (hut hp).1)⟩
        refine ⟨u, hucount, fun p hp ↦ ⟨(hut hp).1, (hut hp).2.1⟩, ?_, ?_⟩
        · intro x hx
          obtain ⟨r, hr0, hrδ, hrν⟩ := hfine x hx δ hδ
          obtain ⟨b, hbu, hb⟩ := hucov (x, r) ⟨hr0, hrδ, hrν⟩
          exact mem_iUnion.2 ⟨⟨b, hbu⟩, hb (mem_closedBall_self hr0.le)⟩
        · calc ∑' p : u, ENNReal.ofReal p.1.2 ^ n
              ≤ ∑' p : u, (k : ℝ≥0∞) * ν (S ∩ closedBall p.1.1 p.1.2) :=
                ENNReal.tsum_le_tsum fun p ↦ (hut p.2).2.2
            _ = (k : ℝ≥0∞) * ν (⋃ p ∈ u, S ∩ closedBall p.1 p.2) := by
                rw [ENNReal.tsum_mul_left, measure_biUnion hucount
                  (hudisj.mono fun p ↦ inter_subset_right)
                  fun p _ ↦ hSmeas.inter measurableSet_closedBall]
            _ ≤ (k : ℝ≥0∞) * ν S :=
                mul_le_mul_right (measure_mono (iUnion₂_subset fun p _ ↦ inter_subset_left)) _
      choose u hucount hurad hucov hsum using
        fun j : ℕ ↦ hvit (1 / ((j : ℝ) + 1)) (by positivity)
      have : ∀ j, Countable ↥(u j) := fun j ↦ (hucount j).to_subtype
      have hlim : Tendsto (fun j : ℕ ↦ ENNReal.ofReal (8 * (1 / ((j : ℝ) + 1)))) atTop (𝓝 0) := by
        have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (8 : ℝ)
        rw [mul_zero] at h
        simpa using ENNReal.tendsto_ofReal h
      -- The Hausdorff measure is bounded by the `liminf` of the covering sums.
      have hH := Measure.hausdorffMeasure_le_liminf_tsum (ι := fun j ↦ ↥(u j)) (n : ℝ) (T k m)
        _ hlim (fun j p ↦ closedBall p.1.1 (4 * p.1.2))
        (Eventually.of_forall fun j p ↦ ?_) (Eventually.of_forall fun j ↦ hucov j)
      · refine hH.trans (liminf_le_of_frequently_le' (Frequently.of_forall fun j ↦ ?_))
        calc ∑' p : ↥(u j), Metric.ediam (closedBall p.1.1 (4 * p.1.2)) ^ (n : ℝ)
            ≤ ∑' p : ↥(u j), 8 ^ n * ENNReal.ofReal p.1.2 ^ n := by
              refine ENNReal.tsum_le_tsum fun p ↦ ?_
              rw [ENNReal.rpow_natCast, ← mul_pow]
              gcongr
              calc Metric.ediam (closedBall p.1.1 (4 * p.1.2)) ≤ ENNReal.ofReal (8 * p.1.2) := by
                    refine Metric.ediam_le_of_forall_dist_le fun y hy z hz ↦ ?_
                    have := dist_triangle_right y z p.1.1
                    rw [mem_closedBall] at hy hz
                    linarith
                _ = 8 * ENNReal.ofReal p.1.2 := by
                    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
          _ = 8 ^ n * ∑' p : ↥(u j), ENNReal.ofReal p.1.2 ^ n := ENNReal.tsum_mul_left
          _ ≤ 8 ^ n * ((k : ℝ≥0∞) * ν S) := mul_le_mul_right (hsum j) _
      · have hp := hurad j p.1 p.2
        refine (Metric.ediam_le_of_forall_dist_le fun y hy z hz ↦ ?_).trans
          (ENNReal.ofReal_le_ofReal (show 8 * p.1.2 ≤ 8 * (1 / ((j : ℝ) + 1)) by linarith))
        have := dist_triangle_right y z p.1.1
        rw [mem_closedBall] at hy hz
        linarith
    -- Inner regularity of `ν` makes `ν(A' \ F)` arbitrarily small.
    refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun η hη _ ↦ ?_) bot_le
    rw [zero_add]
    have hKtop : (8 : ℝ≥0∞) ^ n * (k : ℝ≥0∞) ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.pow_ne_top (by norm_num)) (ENNReal.natCast_ne_top k)
    obtain ⟨F, hFA', hFc, hFν⟩ := hA'meas.exists_isClosed_sdiff_lt hA'fin
      (ε := (η : ℝ≥0∞) / (8 ^ n * k)) (ENNReal.div_pos_iff.2 ⟨by exact_mod_cast hη.ne', hKtop⟩).ne'
    calc (μH[n] : Measure (Ambient n ℓ)) (T k m) ≤ 8 ^ n * ((k : ℝ≥0∞) * ν (A' \ F)) :=
          hcov F hFc hFA'
      _ = 8 ^ n * k * ν (A' \ F) := (mul_assoc _ _ _).symm
      _ ≤ 8 ^ n * k * ((η : ℝ≥0∞) / (8 ^ n * k)) := mul_le_mul_right hFν.le _
      _ ≤ η := ENNReal.mul_div_le
  -- Every `x ∉ A` at which the ratio does not tend to `0` lies in some `T k m`.
  rw [ae_iff]
  refine measure_mono_null (t := ⋃ k : ℕ, ⋃ m : ℕ, T k m) ?_
    (measure_iUnion_null fun k ↦ measure_iUnion_null fun m ↦ ?_)
  · intro x hx
    simp only [mem_ofPred_eq, not_imp] at hx
    obtain ⟨hxA, hnt⟩ := hx
    simp only [Metric.tendsto_nhds, not_forall, not_eventually, not_lt, exists_prop] at hnt
    obtain ⟨ε, hε, hfreq⟩ := hnt
    obtain ⟨k, hk⟩ := exists_nat_ge ε⁻¹
    obtain ⟨m, hm⟩ := exists_nat_gt ‖x‖
    refine mem_iUnion.2 ⟨k, mem_iUnion.2 ⟨m, hxA, hm, ?_⟩⟩
    refine (hfreq.and_eventually self_mem_nhdsWithin).mono fun r hr ↦ ?_
    obtain ⟨hr, hr0⟩ := hr
    have hr0' : (0 : ℝ) < r := hr0
    have hpos : 0 < r ^ n := pow_pos hr0' n
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg measureReal_nonneg hpos.le),
      le_div_iff₀ hpos] at hr
    calc r ^ n = ε⁻¹ * (ε * r ^ n) := by field_simp
      _ ≤ ε⁻¹ * ν.real (A ∩ closedBall x r) := by gcongr
      _ ≤ k * ν.real (A ∩ closedBall x r) := by gcongr
  · rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, hTnull k m, smul_zero]
/-- **Lusin compact cover (Simon Ch. 1, 1.17).** If `A ⊆ ℝ^{n+ℓ}` is `μ`-measurable with
`μ(A) < ∞` and `g` is `μ ⌞ A`-measurable, then `A` is covered up to a `μ`-null set by countably
many compact sets `K_k ⊆ A` on each of which `g` is continuous. -/
theorem Submission.ts_pwb_lusin_compact_cover : ∀ (n ℓ : ℕ) (μ : Measure (Ambient n ℓ)) (A : Set (Ambient n ℓ)) (g : Ambient n ℓ → ℝ), NullMeasurableSet A μ → μ A ≠ ⊤ → AEStronglyMeasurable g (μ.restrict A) → ∃ K : ℕ → Set (Ambient n ℓ), (∀ k, IsCompact (K k) ∧ K k ⊆ A ∧ ContinuousOn g (K k)) ∧ μ (A \ ⋃ k, K k) = 0 := by
  intro n ℓ μ A g hA hAfin hg
  -- Borel `A' ⊆ A` with `μ(A \ A') = 0`, and Borel `g'` with `g = g'` `μ ⌞ A`-a.e.
  obtain ⟨A', hA'A, hA'm, hA'eq⟩ := hA.exists_measurable_subset_ae_eq
  have hAA' : μ (A \ A') = 0 := (ae_eq_set.1 hA'eq).2
  obtain ⟨g', hg'm, hgg'⟩ := hg.aemeasurable
  -- Borel `S ⊇ {g ≠ g'}` with `μ(S ∩ A) = 0`; on the good set `A'' = A' \ S` we have `g = g'`.
  obtain ⟨S, hgS, hSm, hS0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgg')
  have hSA : μ (S ∩ A) = 0 := by rwa [Measure.restrict_apply hSm] at hS0
  set A'' := A' \ S
  have hA''m : MeasurableSet A'' := hA'm.diff hSm
  have hA''A : A'' ⊆ A := sdiff_subset.trans hA'A
  have hgA'' : ∀ y ∈ A'', g y = g' y := fun y hy ↦ by
    by_contra h
    exact hy.2 (hgS h)
  have hAA'' : μ (A \ A'') = 0 := by
    refine measure_mono_null (fun y ⟨hyA, hy⟩ ↦ ?_) (measure_union_null hAA' hSA)
    by_cases h : y ∈ A'
    · exact Or.inr ⟨by_contra fun hS ↦ hy ⟨h, hS⟩, hyA⟩
    · exact Or.inl ⟨hyA, h⟩
  -- Lusin for the finite measure `ν = μ ⌞ A''`: a compact `K ⊆ A''` with `μ(A'' \ K) < ε` on
  -- which `g'` is continuous.
  set ν := μ.restrict A''
  have : IsFiniteMeasure ν :=
    isFiniteMeasure_restrict.2 (ne_top_of_le_ne_top hAfin (measure_mono hA''A))
  have hb := TopologicalSpace.isBasis_countableBasis ℝ
  have : Countable (TopologicalSpace.countableBasis ℝ) :=
    (TopologicalSpace.countable_countableBasis ℝ).to_subtype
  have key : ∀ ε : ℝ≥0∞, ε ≠ 0 →
      ∃ K, IsCompact K ∧ K ⊆ A'' ∧ ContinuousOn g' K ∧ μ (A'' \ K) < ε := by
    intro ε hε
    obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_pos_sum_of_countable (ENNReal.half_pos hε).ne'
      (TopologicalSpace.countableBasis ℝ)
    -- Open `O_U ⊇ g'⁻¹(U)` with `ν(O_U \ g'⁻¹(U)) < δ_U` for each basic open `U`.
    choose O hgO hO _ hOδ using fun U : TopologicalSpace.countableBasis ℝ ↦
      (hg'm (hb.isOpen U.2).measurableSet).exists_isOpen_sdiff_lt (μ := ν)
        (measure_ne_top _ _) (ENNReal.coe_ne_zero.2 (hδ U).ne')
    -- The bad set `B = ⋃_U (O_U \ g'⁻¹(U))` has `ν(B) < ε/2`.
    set B := ⋃ U, (O U \ g' ⁻¹' U)
    have hBm : MeasurableSet B :=
      MeasurableSet.iUnion fun U ↦ (hO U).measurableSet.diff (hg'm (hb.isOpen U.2).measurableSet)
    have hνB : ν B < ε / 2 :=
      calc ν B ≤ ∑' U, ν (O U \ g' ⁻¹' U) := measure_iUnion_le _
        _ ≤ ∑' U, (δ U : ℝ≥0∞) := ENNReal.tsum_le_tsum fun U ↦ (hOδ U).le
        _ < ε / 2 := hδε
    -- Inner regularity: compact `K ⊆ A'' \ B` with `ν((A'' \ B) \ K) < ε/2`.
    obtain ⟨K, hKAB, hK, hKε⟩ := (hA''m.diff hBm).exists_isCompact_sdiff_lt (μ := ν)
      (measure_ne_top _ _) (ENNReal.half_pos hε).ne'
    refine ⟨K, hK, hKAB.trans sdiff_subset, fun x _ ↦ ?_, ?_⟩
    · -- On `K`, `g'⁻¹(U) ∩ K = O_U ∩ K` is relatively open, so `g'` is continuous on `K`.
      refine hb.nhds_hasBasis.tendsto_right_iff.2 fun U ⟨hUb, hxU⟩ ↦
        mem_nhdsWithin.2 ⟨O ⟨U, hUb⟩, hO _, hgO _ hxU, fun y ⟨hyO, hyK⟩ ↦ ?_⟩
      by_contra hyU
      exact (hKAB hyK).2 (mem_iUnion.2 ⟨⟨U, hUb⟩, hyO, hyU⟩)
    · calc μ (A'' \ K) = ν (A'' \ K) := (Measure.restrict_eq_self μ sdiff_subset).symm
        _ ≤ ν B + ν ((A'' \ B) \ K) :=
            (measure_mono (show A'' \ K ⊆ B ∪ ((A'' \ B) \ K) from fun y ⟨hyA, hyK⟩ ↦ by
              by_cases hyB : y ∈ B
              · exact Or.inl hyB
              · exact Or.inr ⟨⟨hyA, hyB⟩, hyK⟩)).trans (measure_union_le _ _)
        _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hνB hKε
        _ = ε := ENNReal.add_halves ε
  -- Exhaustion: `K_k` with `μ(A'' \ K_k) < 1/k`, so `μ(A \ ⋃ K_k) ≤ μ(A \ A'') + 0 = 0`.
  choose K hK hKA hKg hKε using fun k : ℕ ↦
    key (k : ℝ≥0∞)⁻¹ (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top k))
  refine ⟨K, fun k ↦ ⟨hK k, (hKA k).trans hA''A, (hKg k).congr fun y hy ↦ hgA'' y (hKA k hy)⟩, ?_⟩
  have hA''K : μ (A'' \ ⋃ k, K k) = 0 := by
    by_contra h
    obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt h
    exact lt_asymm hk
      ((measure_mono (sdiff_subset_sdiff_right (subset_iUnion K k))).trans_lt (hKε k))
  refine measure_mono_null (fun y ⟨hyA, hyK⟩ ↦ ?_) (measure_union_null hAA'' hA''K)
  by_cases h : y ∈ A''
  · exact Or.inr ⟨h, hyK⟩
  · exact Or.inl ⟨hyA, h⟩
/-- **Density points over a Lipschitz image (Lebesgue density theorem and Simon Ch. 2, 1.8(i)).**
If `C ⊆ ℝⁿ` is Borel and `F : ℝⁿ → ℝ^{n+ℓ}` is Lipschitz, then for `Hⁿ`-a.e. `x`, every `w ∈ C`
with `F(w) = x` is a Lebesgue density point of `C` (closed balls, quotient in `[0, ∞]`). -/
theorem Submission.ts_pwb_density_points_of_image_ae : ∀ (n ℓ : ℕ) (C : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → Ambient n ℓ), MeasurableSet C → (∃ K : NNReal, LipschitzWith K F) → ∀ᵐ x ∂(μHE[n] : Measure (Ambient n ℓ)), ∀ w ∈ C, F w = x → Tendsto (fun r : ℝ ↦ volume (C ∩ closedBall w r) / volume (closedBall w r)) (𝓝[>] 0) (𝓝 1) := by
  intro n ℓ C F hC ⟨κ, hF⟩
  -- `Z`: the points of `C` that are not Lebesgue density points of `C`.
  set Z : Set (EuclideanSpace ℝ (Fin n)) := {w | ¬ Tendsto (fun r : ℝ ↦ volume (C ∩ closedBall w r) / volume (closedBall w r)) (𝓝[>] 0) (𝓝 1)} ∩ C with hZ
  -- Lebesgue density theorem (Besicovitch): `Lⁿ ⌞ C`-a.e. point is a density point, so `Lⁿ(Z) = 0`.
  have hZ0 : volume Z = 0 := by
    have h := Besicovitch.ae_tendsto_measure_inter_div (volume : Measure (EuclideanSpace ℝ (Fin n))) C
    rw [ae_iff, Measure.restrict_apply' hC] at h
    exact h
  -- Lipschitz image bound with `μHE[n] = Lⁿ` on `ℝⁿ`: `Hⁿ(F(Z)) ≤ κⁿ Lⁿ(Z) = 0`.
  have hFZ : (μHE[n] : Measure (Ambient n ℓ)) (F '' Z) = 0 := by
    have h1 := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn
      (A := Z) n (hF.lipschitzOnWith (s := Z))
    rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume, hZ0, mul_zero] at h1
    exact le_antisymm h1 bot_le
  -- Every `x` violating the conclusion is `F(w)` for some `w ∈ Z`.
  rw [ae_iff]
  refine measure_mono_null ?_ hFZ
  intro x hx
  simp only [not_forall, mem_ofPred_eq] at hx
  obtain ⟨w, hwC, hFw, hnt⟩ := hx
  exact ⟨w, ⟨hnt, hwC⟩, hFw⟩
/-- **Image-ball bound for a lower-Lipschitz piece.** If `F : ℝⁿ → ℝ^{n+ℓ}` is `K`-Lipschitz and
`c ‖v - w‖ ≤ ‖F v - F w‖` for every `v ∈ C`, then `Hⁿ(F(C) ∩ B_ρ(F w)) ≤ Kⁿ ωₙ c⁻ⁿ ρⁿ` for all
`ρ > 0` (the uniform upper density bound in the blow-up of a Lipschitz piece). -/
theorem Submission.ts_pdb_image_closedBall_measure_le : ∀ (n ℓ : ℕ) (C : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → Ambient n ℓ) (K : NNReal) (c : ℝ) (w : EuclideanSpace ℝ (Fin n)), LipschitzWith K F → 0 < c → (∀ v ∈ C, c * ‖v - w‖ ≤ ‖F v - F w‖) → ∀ ρ : ℝ, 0 < ρ → (μHE[n] : Measure (Ambient n ℓ)) (F '' C ∩ closedBall (F w) ρ) ≤ ENNReal.ofReal ((K : ℝ) ^ n * omega n / c ^ n * ρ ^ n) := by
  intro n ℓ C F K c w hF hc hCw ρ hρ
  -- `F(C) ∩ B_ρ(F w) ⊆ F(S)` with `S = C ∩ B_{ρ/c}(w)`, by the lower bound at `w`.
  have hsub : F '' C ∩ closedBall (F w) ρ ⊆ F '' (C ∩ closedBall w (ρ / c)) := by
    rintro _ ⟨⟨v, hv, rfl⟩, hvρ⟩
    refine ⟨v, ⟨hv, ?_⟩, rfl⟩
    rw [mem_closedBall, dist_eq_norm] at hvρ
    rw [mem_closedBall, dist_eq_norm, le_div_iff₀ hc]
    linarith [hCw v hv]
  -- `Hⁿ(S) ≤ Lⁿ(B_{ρ/c}(w)) = (ρ/c)ⁿ ωₙ`, as `Hⁿ = Lⁿ` on `ℝⁿ`.
  have hS : μHE[n] (C ∩ closedBall w (ρ / c)) ≤
      ENNReal.ofReal ((ρ / c) ^ n) * ENNReal.ofReal (omega n) := by
    rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume, omega,
      ENNReal.ofReal_toReal measure_ball_lt_top.ne]
    refine (measure_mono inter_subset_right).trans_eq ?_
    rw [Measure.addHaar_closedBall _ _ (div_pos hρ hc).le, finrank_euclideanSpace_fin]
  -- Lipschitz image bound `Hⁿ(F(S)) ≤ Kⁿ Hⁿ(S)`, then `Kⁿ (ρ/c)ⁿ ωₙ = Kⁿ ωₙ / cⁿ ρⁿ`.
  have hω : 0 ≤ omega n := ENNReal.toReal_nonneg
  calc (μHE[n] : Measure (Ambient n ℓ)) (F '' C ∩ closedBall (F w) ρ)
      ≤ μHE[n] (F '' (C ∩ closedBall w (ρ / c))) := measure_mono hsub
    _ ≤ (K : ℝ≥0∞) ^ n * μHE[n] (C ∩ closedBall w (ρ / c)) :=
        Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
          hF.lipschitzOnWith
    _ ≤ (K : ℝ≥0∞) ^ n * (ENNReal.ofReal ((ρ / c) ^ n) * ENNReal.ofReal (omega n)) := by
        gcongr
    _ = ENNReal.ofReal ((K : ℝ) ^ n * omega n / c ^ n * ρ ^ n) := by
        rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_pow K.coe_nonneg,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
/-- **Area formula on a Lipschitz piece.** Let `C ⊆ ℝⁿ` be Borel and `F : ℝⁿ → ℝ^{n+ℓ}` be
Lipschitz, injective on `C`, with `DF` continuous on `C`. Then the Gram-determinant Jacobian
`J = √det (⟪DF eᵢ, DF eⱼ⟫)` is continuous on `C`, satisfies `Hⁿ(DF(v)(S)) = J(v) Lⁿ(S)` for
`v ∈ C`, and `∫_{F(C)} g dHⁿ = ∫_C J(v) g(F(v)) dv` for every continuous `g`. -/
theorem Submission.ts_pdb_piece_area_formula : ∀ (n ℓ : ℕ) (C : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → Ambient n ℓ) (K : NNReal), MeasurableSet C → LipschitzWith K F → Set.InjOn F C → ContinuousOn (fderiv ℝ F) C → ∃ J : EuclideanSpace ℝ (Fin n) → ℝ, ContinuousOn J C ∧ (∀ v ∈ C, 0 ≤ J v ∧ ∀ S : Set (EuclideanSpace ℝ (Fin n)), (μHE[n] : Measure (Ambient n ℓ)) (fderiv ℝ F v '' S) = ENNReal.ofReal (J v) * volume S) ∧ ∀ g : Ambient n ℓ → ℝ, Continuous g → ∫ y in F '' C, g y ∂μHE[n] = ∫ v in C, J v * g (F v) := by
  intro n ℓ C F K hC hF hinj hcont
  classical
  have hvol : (μHE[n] : Measure (EuclideanSpace ℝ (Fin n))) = volume :=
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume n
  /- `Jl A = √det (⟪A eᵢ, A eⱼ⟫)` is the Gram-determinant Jacobian of a linear map
  `A : ℝⁿ → ℝ^{n+ℓ}`; it is continuous and nonnegative. -/
  obtain ⟨Jl, hJl⟩ : ∃ Jl : (EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ) → ℝ, Jl = fun A =>
      Real.sqrt (Matrix.det (Matrix.of fun i j : Fin n =>
        inner ℝ (A (EuclideanSpace.basisFun (Fin n) ℝ i))
          (A (EuclideanSpace.basisFun (Fin n) ℝ j)))) :=
    ⟨_, rfl⟩
  have hJl_cont : Continuous Jl := by
    rw [hJl]
    fun_prop
  have hJl_nonneg : ∀ A, 0 ≤ Jl A := fun A => by
    rw [hJl]
    exact Real.sqrt_nonneg _
  /- An injective `A` factors as an isometric embedding after an endomorphism `T` of `ℝⁿ`
  (so `‖A z‖ = ‖T z‖`), and then `Jl A = |det T|` since the Gram matrix of `A` is `Mᵀ M`. -/
  have LA1 : ∀ A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ, Function.Injective A →
      ∃ T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n), (∀ z, ‖A z‖ = ‖T z‖) ∧
        Jl A = |LinearMap.det T| := by
    intro A hA
    set A' : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] Ambient n ℓ :=
      (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] Ambient n ℓ)
    have hA' : Function.Injective A' := hA
    have hW : Module.finrank ℝ (LinearMap.range A') = n := by
      rw [LinearMap.finrank_range_of_inj hA', finrank_euclideanSpace_fin]
    let b := (stdOrthonormalBasis ℝ (LinearMap.range A')).reindex (finCongr hW)
    let T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
      b.repr.toLinearEquiv.toLinearMap ∘ₗ A'.rangeRestrict
    have hTapp : ∀ z, T z = b.repr (A'.rangeRestrict z) := fun z => rfl
    have hT : ∀ z, ‖A z‖ = ‖T z‖ := by
      intro z
      rw [hTapp, LinearIsometryEquiv.norm_map]
      rfl
    have hinner : ∀ x y, inner ℝ (A x) (A y) = inner ℝ (T x) (T y) := by
      intro x y
      rw [hTapp, hTapp, LinearIsometryEquiv.inner_map_map, Submodule.coe_inner]
      rfl
    refine ⟨T, hT, ?_⟩
    have hG : (Matrix.of fun i j : Fin n => inner ℝ (A (EuclideanSpace.basisFun (Fin n) ℝ i))
        (A (EuclideanSpace.basisFun (Fin n) ℝ j))) =
        (LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
          (EuclideanSpace.basisFun (Fin n) ℝ).toBasis T).transpose *
        LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
          (EuclideanSpace.basisFun (Fin n) ℝ).toBasis T := by
      ext i j
      simp only [Matrix.of_apply, hinner, Matrix.mul_apply, Matrix.transpose_apply,
        LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
        OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr, PiLp.inner_apply,
        RCLike.inner_apply, conj_trivial]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hJl]
    simp only
    rw [hG, Matrix.det_mul, Matrix.det_transpose, Real.sqrt_mul_self_eq_abs, LinearMap.det_toMatrix]
  /- A non-injective `A` has a kernel vector, which is a kernel vector of its Gram matrix. -/
  have hker : ∀ A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ, ¬ Function.Injective A →
      ∃ x, x ≠ 0 ∧ A x = 0 := by
    intro A hA
    by_contra h
    push Not at h
    apply hA
    intro a b hab
    by_contra hne
    exact h (a - b) (sub_ne_zero.mpr hne) (by rw [map_sub, hab, sub_self])
  have LA2 : ∀ A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ, ¬ Function.Injective A →
      Jl A = 0 := by
    intro A hA
    obtain ⟨x, hx0, hAx⟩ := hker A hA
    have hdet : Matrix.det (Matrix.of fun i j : Fin n =>
        inner ℝ (A (EuclideanSpace.basisFun (Fin n) ℝ i))
          (A (EuclideanSpace.basisFun (Fin n) ℝ j))) = 0 := by
      rw [← Matrix.exists_mulVec_eq_zero_iff]
      refine ⟨x.ofLp, fun h => hx0 ?_, ?_⟩
      · ext i
        simp [h]
      · ext i
        have hx : x = ∑ j, x j • EuclideanSpace.basisFun (Fin n) ℝ j := by
          conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr x]
          simp
        have key : ∑ j, inner ℝ (A (EuclideanSpace.basisFun (Fin n) ℝ i))
            (A (EuclideanSpace.basisFun (Fin n) ℝ j)) * x j =
            inner ℝ (A (EuclideanSpace.basisFun (Fin n) ℝ i)) (A x) := by
          conv_rhs => rw [hx]
          rw [map_sum, inner_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_smul, inner_smul_right, mul_comm]
        simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
        rw [key, hAx, inner_zero_right]
    rw [hJl]
    simp only
    rw [hdet, Real.sqrt_zero]
  have LA3 : ∀ A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ, Function.Injective A → 0 < Jl A := by
    intro A hA
    obtain ⟨T, hT, hJ⟩ := LA1 A hA
    have hTinj : Function.Injective T := by
      intro a b hab
      apply hA
      rw [← sub_eq_zero, ← map_sub, ← norm_eq_zero, hT, map_sub, hab, sub_self, norm_zero]
    rw [hJ, abs_pos]
    intro h0
    exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp h0) (LinearMap.ker_eq_bot.mpr hTinj)
  /- Zero-Jacobian pieces: if `A` has a unit kernel vector `u`, then for `G` close to `A`,
  `G = G' ∘ M_θ` with `M_θ` the contraction by `θ` along `u` and `G'` Lipschitz, so
  `Hⁿ(G(P)) ≤ (‖A‖+1)ⁿ |det M_θ| Lⁿ(P)`, which is small since `det M_θ → det M_0 = 0`. -/
  have B3 : ∀ A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ, ¬ Function.Injective A →
      ∀ η : NNReal, 0 < η → ∃ δ : NNReal, 0 < δ ∧
        ∀ (G : EuclideanSpace ℝ (Fin n) → Ambient n ℓ) (P : Set (EuclideanSpace ℝ (Fin n))),
          ApproximatesLinearOn G A P δ →
            (μHE[n] : Measure (Ambient n ℓ)) (G '' P) ≤ η * volume P := by
    intro A hA η hη
    obtain ⟨x, hx0, hAx⟩ := hker A hA
    set u : EuclideanSpace ℝ (Fin n) := ‖x‖⁻¹ • x with hu_def
    have hu1 : ‖u‖ = 1 := by
      rw [hu_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx0)]
    have hAu : A u = 0 := by rw [hu_def, map_smul, hAx, smul_zero]
    let M : ℝ → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) := fun θ =>
      ContinuousLinearMap.id ℝ _ - (1 - θ) • (innerSL ℝ u).smulRight u
    have hMapp : ∀ θ z, M θ z = z - ((1 - θ) * inner ℝ u z) • u := by
      intro θ z
      simp [M, smul_smul]
    have hAM : ∀ θ z, A (M θ z) = A z := by
      intro θ z
      rw [hMapp, map_sub, map_smul, hAu, smul_zero, sub_zero]
    have hMnorm : ∀ θ : ℝ, 0 < θ → θ ≤ 1 → ∀ z, θ * ‖z‖ ≤ ‖M θ z‖ := by
      intro θ h0 h1 z
      have h2 : ‖M θ z‖ ^ 2 = ‖z‖ ^ 2 - (1 - θ ^ 2) * inner ℝ u z ^ 2 := by
        rw [hMapp, @norm_sub_sq_real, norm_smul, inner_smul_right, hu1, Real.norm_eq_abs, mul_one,
          sq_abs, real_inner_comm z u]
        ring
      have hcs : inner ℝ u z ^ 2 ≤ ‖z‖ ^ 2 := by
        have h := abs_real_inner_le_norm u z
        rw [hu1, one_mul] at h
        have := sq_le_sq' (neg_le_of_abs_le h) (le_of_abs_le h)
        simpa using this
      have h3 : (θ * ‖z‖) ^ 2 ≤ ‖M θ z‖ ^ 2 := by
        have h4 : (1 - θ ^ 2) * inner ℝ u z ^ 2 ≤ (1 - θ ^ 2) * ‖z‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hcs (sub_nonneg.mpr (pow_le_one₀ h0.le h1))
        rw [h2, show (θ * ‖z‖) ^ 2 = ‖z‖ ^ 2 - (1 - θ ^ 2) * ‖z‖ ^ 2 by ring]
        exact sub_le_sub_left h4 _
      exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp h3
    have hdet0 : (M 0).det = 0 := by
      have hM0u : M 0 u = 0 := by
        rw [hMapp, real_inner_self_eq_norm_sq, hu1]
        simp
      rw [ContinuousLinearMap.det, LinearMap.det_eq_zero_iff_ker_ne_bot]
      intro hker0
      have hmem : u ∈ LinearMap.ker (M 0).toLinearMap := LinearMap.mem_ker.mpr hM0u
      rw [hker0, Submodule.mem_bot] at hmem
      rw [hmem, norm_zero] at hu1
      exact zero_ne_one hu1
    have hcontM : Continuous fun θ : ℝ => (M θ).det :=
      ContinuousLinearMap.continuous_det.comp (by fun_prop)
    have hlim : Tendsto (fun θ : ℝ => ((‖A‖₊ : ℝ) + 1) ^ n * |(M θ).det|) (𝓝 0) (𝓝 0) := by
      have h := (hcontM.tendsto 0).abs.const_mul (((‖A‖₊ : ℝ) + 1) ^ n)
      rwa [hdet0, abs_zero, mul_zero] at h
    obtain ⟨θ, hθ, hθ0, hθ1⟩ :
        ∃ θ : ℝ, ((‖A‖₊ : ℝ) + 1) ^ n * |(M θ).det| < η ∧ 0 < θ ∧ θ ≤ 1 := by
      have h1 : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ((‖A‖₊ : ℝ) + 1) ^ n * |(M θ).det| < η :=
        nhdsWithin_le_nhds (hlim.eventually (gt_mem_nhds (show (0 : ℝ) < η from hη)))
      have h2 : ∀ᶠ θ in 𝓝[>] (0 : ℝ), 0 < θ ∧ θ ≤ 1 := by
        filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with θ hθ
        exact ⟨hθ.1, hθ.2.le⟩
      exact (h1.and h2).exists.imp fun θ h => ⟨h.1, h.2⟩
    refine ⟨⟨θ, hθ0.le⟩, hθ0, fun G P hGP => ?_⟩
    have hMinj : Function.Injective (M θ).toLinearMap := by
      intro a b hab
      have h := hMnorm θ hθ0 hθ1 (a - b)
      have hab' : M θ (a - b) = 0 := by
        rw [map_sub]
        exact sub_eq_zero.mpr hab
      rw [hab', norm_zero, ← mul_zero θ] at h
      have : ‖a - b‖ = 0 := le_antisymm (le_of_mul_le_mul_left h hθ0) (norm_nonneg _)
      exact sub_eq_zero.mp (norm_eq_zero.mp this)
    let Me := LinearEquiv.ofInjectiveEndo (M θ).toLinearMap hMinj
    have hMe : ∀ z, Me.symm (M θ z) = z := fun z => Me.symm_apply_apply z
    let G' := G ∘ Me.symm
    have hG' : ∀ z, G' (M θ z) = G z := fun z => by simp only [G', Function.comp_apply, hMe]
    have himg : G '' P = G' '' (M θ '' P) := by
      rw [Set.image_image]
      exact Set.image_congr fun z _ => (hG' z).symm
    have hLip : LipschitzOnWith (‖A‖₊ + 1) G' (M θ '' P) := by
      apply LipschitzOnWith.of_dist_le_mul
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [hG', hG', dist_eq_norm, dist_eq_norm]
      have happ : ‖G x - G y - A (x - y)‖ ≤ θ * ‖x - y‖ := hGP x hx y hy
      have hA1 : ‖A (x - y)‖ ≤ ‖A‖ * ‖M θ x - M θ y‖ := by
        rw [← hAM θ (x - y), map_sub]
        exact A.le_opNorm _
      have hA2 : θ * ‖x - y‖ ≤ ‖M θ x - M θ y‖ := by
        rw [← map_sub]
        exact hMnorm θ hθ0 hθ1 (x - y)
      have htri : ‖G x - G y‖ ≤ ‖G x - G y - A (x - y)‖ + ‖A (x - y)‖ := by
        have := norm_add_le (G x - G y - A (x - y)) (A (x - y))
        rwa [sub_add_cancel] at this
      push_cast
      rw [add_mul, one_mul]
      linarith only [htri, happ, hA1, hA2]
    have hdetθ : ((‖A‖₊ + 1 : NNReal) : ℝ≥0∞) ^ n * ENNReal.ofReal |(M θ).det| ≤ η := by
      have h := ENNReal.ofReal_le_ofReal hθ.le
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
        ENNReal.ofReal_coe_nnreal] at h
      convert h using 3
      rw [← ENNReal.ofReal_coe_nnreal]
      push_cast
      rfl
    calc (μHE[n] : Measure (Ambient n ℓ)) (G '' P) = μHE[n] (G' '' (M θ '' P)) := by rw [himg]
      _ ≤ ((‖A‖₊ + 1 : NNReal) : ℝ≥0∞) ^ n * μHE[n] (M θ '' P) :=
        Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hLip
      _ = ((‖A‖₊ + 1 : NNReal) : ℝ≥0∞) ^ n * (ENNReal.ofReal |(M θ).det| * volume P) := by
        rw [hvol]
        congr 1
        exact Measure.addHaar_image_linearMap volume (M θ).toLinearMap P
      _ ≤ η * volume P := by
        rw [← mul_assoc]
        exact mul_le_mul_left hdetθ _
  /- Injective pieces: with `‖A z‖ = ‖T z‖` and `‖z‖ ≤ κ ‖T z‖`, a map `G` that is
  `δ`-close to `A` on `P` satisfies `G = G' ∘ T` with `G'` `(1+δκ)`-Lipschitz, and (if `G` is
  injective on `P`) `T = H ∘ G` with `H` `(1-δκ)⁻¹`-Lipschitz; `Hⁿ(T(P)) = Jl A · Lⁿ(P)`. -/
  have B12 : ∀ A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ, Function.Injective A →
      ∀ c : ℝ, 1 < c → ∃ δ : NNReal, 0 < δ ∧
        ∀ (G : EuclideanSpace ℝ (Fin n) → Ambient n ℓ) (P : Set (EuclideanSpace ℝ (Fin n))),
          ApproximatesLinearOn G A P δ →
          (μHE[n] : Measure (Ambient n ℓ)) (G '' P) ≤
              ENNReal.ofReal c * (ENNReal.ofReal (Jl A) * volume P) ∧
          (Set.InjOn G P → ENNReal.ofReal (Jl A) * volume P ≤
              ENNReal.ofReal c * (μHE[n] : Measure (Ambient n ℓ)) (G '' P)) := by
    intro A hA c hc
    obtain ⟨T, hT, hjT⟩ := LA1 A hA
    have hTinj : Function.Injective T := by
      intro a b hab
      apply hA
      rw [← sub_eq_zero, ← map_sub, ← norm_eq_zero, hT, map_sub, hab, sub_self, norm_zero]
    have hTimg : ∀ P : Set (EuclideanSpace ℝ (Fin n)),
        (μHE[n] : Measure (EuclideanSpace ℝ (Fin n))) (T '' P) =
          ENNReal.ofReal (Jl A) * volume P := by
      intro P
      rw [hvol, hjT]
      exact Measure.addHaar_image_linearMap volume T P
    obtain ⟨κ, hκ, hantiT⟩ := LinearMap.exists_antilipschitzWith T (LinearMap.ker_eq_bot.mpr hTinj)
    have hκT : ∀ x y, ‖x - y‖ ≤ κ * ‖T x - T y‖ := by
      intro x y
      have := hantiT.le_mul_dist x y
      rwa [dist_eq_norm, dist_eq_norm] at this
    obtain ⟨t, ht0, ht1, htc1, htc2⟩ :
        ∃ t : ℝ, 0 < t ∧ t < 1 ∧ (1 + t) ^ n < c ∧ ((1 - t)⁻¹) ^ n < c := by
      have h1 : Tendsto (fun t : ℝ => (1 + t) ^ n) (𝓝 0) (𝓝 1) := by
        have : Continuous (fun t : ℝ => (1 + t) ^ n) := by fun_prop
        simpa using this.tendsto 0
      have h2 : Tendsto (fun t : ℝ => ((1 - t)⁻¹) ^ n) (𝓝 0) (𝓝 1) := by
        have : ContinuousAt (fun t : ℝ => ((1 - t)⁻¹) ^ n) 0 :=
          ((continuousAt_const.sub continuousAt_id).inv₀ (by norm_num)).pow n
        simpa using this.tendsto
      have e1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), (1 + t) ^ n < c :=
        nhdsWithin_le_nhds (h1.eventually (gt_mem_nhds hc))
      have e2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), ((1 - t)⁻¹) ^ n < c :=
        nhdsWithin_le_nhds (h2.eventually (gt_mem_nhds hc))
      have e3 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t < 1 := by
        filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
        exact ⟨ht.1, ht.2⟩
      obtain ⟨t, h1t, h2t, h3t⟩ := (e1.and (e2.and e3)).exists
      exact ⟨t, h3t.1, h3t.2, h1t, h2t⟩
    set δ : NNReal := Real.toNNReal (t / κ) with hδ
    have hδκ : (δ : ℝ) * κ = t := by
      rw [hδ, Real.coe_toNNReal _ (by positivity)]
      field_simp
    refine ⟨δ, by rw [hδ]; exact Real.toNNReal_pos.mpr (by positivity), fun G P hGP => ?_⟩
    have happ : ∀ x ∈ P, ∀ y ∈ P, ‖G x - G y - A (x - y)‖ ≤ t * ‖T x - T y‖ := by
      intro x hx y hy
      calc ‖G x - G y - A (x - y)‖ ≤ δ * ‖x - y‖ := hGP x hx y hy
        _ ≤ δ * (κ * ‖T x - T y‖) := mul_le_mul_of_nonneg_left (hκT x y) δ.2
        _ = t * ‖T x - T y‖ := by rw [← mul_assoc, hδκ]
    have hAT : ∀ x y, ‖A (x - y)‖ = ‖T x - T y‖ := by
      intro x y
      rw [hT, map_sub]
    constructor
    · let Te := LinearEquiv.ofInjectiveEndo T hTinj
      let G' := G ∘ Te.symm
      have hG' : ∀ z, G' (T z) = G z := fun z => by
        simp only [G', Function.comp_apply]
        exact congrArg G (Te.symm_apply_apply z)
      have himg : G '' P = G' '' (T '' P) := by
        rw [Set.image_image]
        exact Set.image_congr fun z _ => (hG' z).symm
      have hLip : LipschitzOnWith (Real.toNNReal (1 + t)) G' (T '' P) := by
        apply LipschitzOnWith.of_dist_le_mul
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        rw [hG', hG', dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
        have h1 := happ x hx y hy
        have htri : ‖G x - G y‖ ≤ ‖G x - G y - A (x - y)‖ + ‖A (x - y)‖ := by
          have := norm_add_le (G x - G y - A (x - y)) (A (x - y))
          rwa [sub_add_cancel] at this
        rw [hAT] at htri
        rw [add_mul, one_mul]
        linarith only [h1, htri]
      calc (μHE[n] : Measure (Ambient n ℓ)) (G '' P) = μHE[n] (G' '' (T '' P)) := by rw [himg]
        _ ≤ ((Real.toNNReal (1 + t) : NNReal) : ℝ≥0∞) ^ n * μHE[n] (T '' P) :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hLip
        _ ≤ ENNReal.ofReal c * (ENNReal.ofReal (Jl A) * volume P) := by
          rw [hTimg]
          refine mul_le_mul' ?_ le_rfl
          rw [← ENNReal.ofReal.eq_def, ← ENNReal.ofReal_pow (by positivity)]
          exact ENNReal.ofReal_le_ofReal htc1.le
    · intro hinjG
      let H : Ambient n ℓ → EuclideanSpace ℝ (Fin n) := T ∘ Function.invFunOn G P
      have hH : ∀ z ∈ P, H (G z) = T z := fun z hz => by
        simp only [H, Function.comp_apply]
        rw [hinjG.leftInvOn_invFunOn hz]
      have himg : T '' P = H '' (G '' P) := by
        rw [Set.image_image]
        exact Set.image_congr fun z hz => (hH z hz).symm
      have h1t : 0 < 1 - t := sub_pos.mpr ht1
      have hLip : LipschitzOnWith (Real.toNNReal ((1 - t)⁻¹)) H (G '' P) := by
        apply LipschitzOnWith.of_dist_le_mul
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        rw [hH x hx, hH y hy, dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
        have h1 := happ x hx y hy
        have htri : ‖A (x - y)‖ ≤ ‖G x - G y‖ + ‖G x - G y - A (x - y)‖ := by
          have := norm_sub_le (G x - G y) (G x - G y - A (x - y))
          rwa [sub_sub_cancel] at this
        rw [hAT] at htri
        rw [le_inv_mul_iff₀ h1t, sub_mul, one_mul]
        linarith only [h1, htri]
      calc ENNReal.ofReal (Jl A) * volume P = μHE[n] (T '' P) := (hTimg P).symm
        _ = μHE[n] (H '' (G '' P)) := by rw [himg]
        _ ≤ ((Real.toNNReal ((1 - t)⁻¹) : NNReal) : ℝ≥0∞) ^ n * μHE[n] (G '' P) :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hLip
        _ ≤ ENNReal.ofReal c * (μHE[n] : Measure (Ambient n ℓ)) (G '' P) := by
          refine mul_le_mul' ?_ le_rfl
          rw [← ENNReal.ofReal.eq_def, ← ENNReal.ofReal_pow (by positivity)]
          exact ENNReal.ofReal_le_ofReal htc2.le
  /- Two limit principles in `ℝ≥0∞`. -/
  have zero_of : ∀ X Y : ℝ≥0∞, Y ≠ ⊤ → (∀ η : NNReal, 0 < η → X ≤ η * Y) → X = 0 := by
    intro X Y hY h
    have ht : Tendsto (fun η : NNReal => (η : ℝ≥0∞) * Y) (𝓝[>] 0) (𝓝 0) := by
      have h0 : Tendsto (fun η : NNReal => (η : ℝ≥0∞)) (𝓝[>] 0) (𝓝 0) :=
        (ENNReal.continuous_coe.tendsto 0).mono_left nhdsWithin_le_nhds |>.trans (by simp)
      simpa using ENNReal.Tendsto.mul_const h0 (Or.inr hY)
    exact le_antisymm (ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun η hη => h η hη))
      zero_le
  have lim_le : ∀ X Y : ℝ≥0∞,
      (∀ c : ℝ, 1 < c → X ≤ ENNReal.ofReal c * (ENNReal.ofReal c * Y)) → X ≤ Y := by
    intro X Y h
    rcases eq_or_ne Y ⊤ with hY | hY
    · rw [hY]
      exact le_top
    have ht : Tendsto (fun c : ℝ => ENNReal.ofReal c * (ENNReal.ofReal c * Y)) (𝓝[>] 1) (𝓝 Y) := by
      have h1 : Tendsto (fun c : ℝ => ENNReal.ofReal c) (𝓝[>] 1) (𝓝 1) := by
        have := ENNReal.continuous_ofReal.tendsto (1 : ℝ)
        rw [ENNReal.ofReal_one] at this
        exact this.mono_left nhdsWithin_le_nhds
      have h2 := ENNReal.Tendsto.mul h1 (Or.inl one_ne_zero)
        (ENNReal.Tendsto.mul_const h1 (Or.inr hY)) (Or.inr ENNReal.one_ne_top)
      simpa using h2
    exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun c hc => h c hc)
  /- Linear area factor: `Hⁿ(A(S)) = Jl A · Lⁿ(S)` for every `S`. -/
  have hlin : ∀ (A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ)
      (S : Set (EuclideanSpace ℝ (Fin n))),
      (μHE[n] : Measure (Ambient n ℓ)) (A '' S) = ENNReal.ofReal (Jl A) * volume S := by
    intro A S
    by_cases hA : Function.Injective A
    · obtain ⟨T, hT, hjT⟩ := LA1 A hA
      have hTinj : Function.Injective T := by
        intro a b hab
        apply hA
        rw [← sub_eq_zero, ← map_sub, ← norm_eq_zero, hT, map_sub, hab, sub_self, norm_zero]
      let Te := LinearEquiv.ofInjectiveEndo T hTinj
      let Φ : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] Ambient n ℓ :=
        (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] Ambient n ℓ) ∘ₗ Te.symm.toLinearMap
      have hTe : ∀ y, T (Te.symm y) = y := fun y => Te.apply_symm_apply y
      have hΦ : Isometry Φ := AddMonoidHomClass.isometry_of_norm Φ fun y => by
        simp only [Φ, LinearMap.comp_apply, LinearEquiv.coe_coe, ContinuousLinearMap.coe_coe]
        rw [hT, hTe]
      have himg : A '' S = Φ '' (T '' S) := by
        rw [Set.image_image]
        refine Set.image_congr fun z _ => ?_
        simp only [Φ, LinearMap.comp_apply, LinearEquiv.coe_coe, ContinuousLinearMap.coe_coe]
        exact (congrArg A (Te.symm_apply_apply z)).symm
      rw [himg, hΦ.euclideanHausdorffMeasure_image, hvol, hjT]
      exact Measure.addHaar_image_linearMap volume T S
    · rw [LA2 A hA, ENNReal.ofReal_zero, zero_mul]
      have hball : ∀ m : ℕ, (μHE[n] : Measure (Ambient n ℓ)) (A '' (S ∩ ball 0 m)) = 0 := by
        intro m
        apply zero_of _ (volume (ball (0 : EuclideanSpace ℝ (Fin n)) m)) measure_ball_lt_top.ne
        intro η hη
        obtain ⟨δ, -, hB⟩ := B3 A hA η hη
        calc (μHE[n] : Measure (Ambient n ℓ)) (A '' (S ∩ ball 0 m))
            ≤ η * volume (S ∩ ball (0 : EuclideanSpace ℝ (Fin n)) m) :=
              hB A _ fun x _ y _ => by rw [map_sub, sub_self, norm_zero]; positivity
          _ ≤ η * volume (ball (0 : EuclideanSpace ℝ (Fin n)) m) :=
              mul_le_mul' le_rfl (measure_mono inter_subset_right)
      have hU : A '' S = ⋃ m : ℕ, A '' (S ∩ ball 0 m) := by
        rw [← image_iUnion, ← inter_iUnion, iUnion_ball_nat, inter_univ]
      rw [hU]
      exact measure_iUnion_null hball
  /- From here on we work with `F`. `D` is its (Borel) differentiability set, of full measure by
  Rademacher's theorem, and `J = Jl ∘ DF` is Borel and nonnegative. -/
  have hFc : Continuous F := hF.continuous
  have hFm : Measurable F := hFc.measurable
  obtain ⟨D, hD⟩ : ∃ D : Set (EuclideanSpace ℝ (Fin n)), D = {x | DifferentiableAt ℝ F x} :=
    ⟨_, rfl⟩
  have hDm : MeasurableSet D := by
    rw [hD]
    exact measurableSet_of_differentiableAt ℝ F
  have hDc : volume Dᶜ = 0 := by
    have h := hF.ae_differentiableAt (μ := volume)
    rw [ae_iff] at h
    rw [hD]
    exact h
  have hderiv : ∀ s ⊆ D, ∀ x ∈ s, HasFDerivWithinAt F (fderiv ℝ F x) s x := by
    intro s hs x hx
    have hxD : x ∈ D := hs hx
    rw [hD] at hxD
    exact hxD.hasFDerivAt.hasFDerivWithinAt
  obtain ⟨J, hJ⟩ : ∃ J : EuclideanSpace ℝ (Fin n) → ℝ, J = fun v => Jl (fderiv ℝ F v) := ⟨_, rfl⟩
  have hJv : ∀ v, J v = Jl (fderiv ℝ F v) := fun v => by rw [hJ]
  have hJm : Measurable J := by
    rw [hJ]
    exact hJl_cont.measurable.comp (measurable_fderiv ℝ F)
  have hJnn : ∀ v, 0 ≤ J v := fun v => by
    rw [hJv]
    exact hJl_nonneg _
  /- (Z) Sets where `J = 0` have `Hⁿ`-null images: partition into pieces where `F` is close to a
  non-injective `DF(y)` and apply `B3` on bounded parts. -/
  have hZ : ∀ s : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet s → s ⊆ D → (∀ x ∈ s, J x = 0) →
      (μHE[n] : Measure (Ambient n ℓ)) (F '' s) = 0 := by
    intro s hs hsD hs0
    have key : ∀ m : ℕ, (μHE[n] : Measure (Ambient n ℓ)) (F '' (s ∩ ball 0 m)) = 0 := by
      intro m
      have hs'm : MeasurableSet (s ∩ ball (0 : EuclideanSpace ℝ (Fin n)) m) :=
        hs.inter measurableSet_ball
      apply zero_of _ (volume (ball (0 : EuclideanSpace ℝ (Fin n)) m)) measure_ball_lt_top.ne
      intro η hη
      let r : (EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ) → NNReal := fun A =>
        if h : Function.Injective A then 1 else (B3 A h η hη).choose
      have rpos : ∀ A, r A ≠ 0 := by
        intro A
        by_cases h : Function.Injective A
        · simp only [r, h, dite_true]
          exact one_ne_zero
        · simp only [r, h, dite_false]
          exact (B3 A h η hη).choose_spec.1.ne'
      obtain ⟨t, A, htd, htm, hcov, happ, hAy⟩ :=
        exists_partition_approximatesLinearOn_of_hasFDerivWithinAt F
          (s ∩ ball (0 : EuclideanSpace ℝ (Fin n)) m) (fderiv ℝ F)
          (hderiv _ (inter_subset_left.trans hsD)) r rpos
      rcases (s ∩ ball (0 : EuclideanSpace ℝ (Fin n)) m).eq_empty_or_nonempty with he | hne
      · rw [he, image_empty, measure_empty]
        exact zero_le
      have hAni : ∀ k, ¬ Function.Injective (A k) := by
        intro k hk
        obtain ⟨y, hy, hAk⟩ := hAy hne k
        have h1 := LA3 _ hk
        rw [hAk, ← hJv, hs0 y hy.1] at h1
        exact lt_irrefl _ h1
      have hpiece : ∀ k, (μHE[n] : Measure (Ambient n ℓ)) (F '' (s ∩ ball 0 m ∩ t k)) ≤
          η * volume (s ∩ ball (0 : EuclideanSpace ℝ (Fin n)) m ∩ t k) := by
        intro k
        apply (B3 (A k) (hAni k) η hη).choose_spec.2 F
        have := happ k
        simp only [r, hAni k, dite_false] at this
        exact this
      calc (μHE[n] : Measure (Ambient n ℓ)) (F '' (s ∩ ball 0 m))
          ≤ μHE[n] (⋃ k, F '' (s ∩ ball 0 m ∩ t k)) := by
            apply measure_mono
            rw [← image_iUnion, ← inter_iUnion]
            exact image_mono (subset_inter subset_rfl hcov)
        _ ≤ ∑' k, μHE[n] (F '' (s ∩ ball 0 m ∩ t k)) := measure_iUnion_le _
        _ ≤ ∑' k, (η : ℝ≥0∞) * volume (s ∩ ball (0 : EuclideanSpace ℝ (Fin n)) m ∩ t k) :=
            ENNReal.tsum_le_tsum hpiece
        _ = η * volume (⋃ k, s ∩ ball (0 : EuclideanSpace ℝ (Fin n)) m ∩ t k) := by
            rw [ENNReal.tsum_mul_left, measure_iUnion]
            · exact htd.mono fun i j h => h.mono inter_subset_right inter_subset_right
            · exact fun k => hs'm.inter (htm k)
        _ ≤ η * volume (ball (0 : EuclideanSpace ℝ (Fin n)) m) :=
            mul_le_mul' le_rfl
              (measure_mono (iUnion_subset fun k => inter_subset_left.trans inter_subset_right))
    have hU : F '' s = ⋃ m : ℕ, F '' (s ∩ ball 0 m) := by
      rw [← image_iUnion, ← inter_iUnion, iUnion_ball_nat, inter_univ]
    rw [hU]
    exact measure_iUnion_null key
  /- (Pos) On sets where `J > 0` and `F` is injective, `Hⁿ(F(s)) = ∫_s J`: for `c > 1` split `s`
  into the level sets `c^k ≤ J < c^{k+1}` (`k ∈ ℤ`), partition each into pieces where `F` is close
  to an injective `DF(y)`, compare both sides on each piece with `B12` up to `c²`, and sum (the
  images of the pieces are disjoint and Borel by Lusin–Souslin). Then let `c → 1`. -/
  have hPos : ∀ s : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet s → s ⊆ D → Set.InjOn F s →
      (∀ x ∈ s, 0 < J x) →
      (μHE[n] : Measure (Ambient n ℓ)) (F '' s) = ∫⁻ x in s, ENNReal.ofReal (J x) := by
    intro s hs hsD hinjs hspos
    have himgd : ∀ a b : Set (EuclideanSpace ℝ (Fin n)), a ⊆ s → b ⊆ s → Disjoint a b →
        Disjoint (F '' a) (F '' b) := by
      intro a b ha hb hab
      rw [Set.disjoint_left]
      rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
      have hyx : y = x := hinjs (hb hy) (ha hx) hxy
      exact Set.disjoint_left.mp hab hx (hyx ▸ hy)
    have key : ∀ c : ℝ, 1 < c →
        (μHE[n] : Measure (Ambient n ℓ)) (F '' s) ≤
          ENNReal.ofReal c * (ENNReal.ofReal c * ∫⁻ x in s, ENNReal.ofReal (J x)) ∧
        ∫⁻ x in s, ENNReal.ofReal (J x) ≤
          ENNReal.ofReal c * (ENNReal.ofReal c * (μHE[n] : Measure (Ambient n ℓ)) (F '' s)) := by
      intro c hc
      have hc0 : 0 < c := zero_lt_one.trans hc
      let L : ℤ → Set (EuclideanSpace ℝ (Fin n)) := fun k => s ∩ J ⁻¹' Ico (c ^ k) (c ^ (k + 1))
      have hLm : ∀ k, MeasurableSet (L k) := fun k => hs.inter (hJm measurableSet_Ico)
      have hLs : ∀ k, L k ⊆ s := fun k => inter_subset_left
      have hLd : Pairwise (Function.onFun Disjoint L) := by
        intro k k' hkk'
        rw [Function.onFun, Set.disjoint_left]
        rintro x ⟨_, hx1, hx2⟩ ⟨_, hx1', hx2'⟩
        rcases lt_or_gt_of_ne hkk' with h | h
        · have : c ^ (k + 1) ≤ c ^ k' := zpow_le_zpow_right₀ hc.le (by omega)
          exact lt_irrefl _ ((this.trans hx1').trans_lt hx2)
        · have : c ^ (k' + 1) ≤ c ^ k := zpow_le_zpow_right₀ hc.le (by omega)
          exact lt_irrefl _ ((this.trans hx1).trans_lt hx2')
      have hLcov : s = ⋃ k, L k := by
        apply Subset.antisymm
        · intro x hx
          obtain ⟨k, hk⟩ := exists_mem_Ico_zpow (hspos x hx) hc
          exact mem_iUnion.mpr ⟨k, hx, hk⟩
        · exact iUnion_subset hLs
      let r : (EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ) → NNReal := fun A =>
        if h : Function.Injective A then (B12 A h c hc).choose else 1
      have rpos : ∀ A, r A ≠ 0 := by
        intro A
        by_cases h : Function.Injective A
        · simp only [r, h, dite_true]
          exact (B12 A h c hc).choose_spec.1.ne'
        · simp only [r, h, dite_false]
          exact one_ne_zero
      have hpart : ∀ k : ℤ, ∃ (t : ℕ → Set (EuclideanSpace ℝ (Fin n)))
          (A : ℕ → (EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ)),
          Pairwise (Function.onFun Disjoint t) ∧ (∀ j, MeasurableSet (t j)) ∧ L k ⊆ ⋃ j, t j ∧
          (∀ j, ApproximatesLinearOn F (A j) (L k ∩ t j) (r (A j))) ∧
          ((L k).Nonempty → ∀ j, ∃ y ∈ L k, A j = fderiv ℝ F y) := fun k =>
        exists_partition_approximatesLinearOn_of_hasFDerivWithinAt F (L k) (fderiv ℝ F)
          (hderiv _ ((hLs k).trans hsD)) r rpos
      choose t A htd htm hcov happ hAy using hpart
      have hPm : ∀ k j, MeasurableSet (L k ∩ t k j) := fun k j => (hLm k).inter (htm k j)
      have hPs : ∀ k j, L k ∩ t k j ⊆ s := fun k j => inter_subset_left.trans (hLs k)
      have hPd : ∀ k, Pairwise (Function.onFun Disjoint fun j => L k ∩ t k j) := fun k j j' h =>
        (htd k h).mono inter_subset_right inter_subset_right
      have hLP : ∀ k, L k = ⋃ j, L k ∩ t k j := fun k => by
        rw [← inter_iUnion]
        exact (inter_eq_left.mpr (hcov k)).symm
      have hpiece : ∀ k j,
          (μHE[n] : Measure (Ambient n ℓ)) (F '' (L k ∩ t k j)) ≤
            ENNReal.ofReal c * (ENNReal.ofReal c * ∫⁻ x in L k ∩ t k j, ENNReal.ofReal (J x)) ∧
          ∫⁻ x in L k ∩ t k j, ENNReal.ofReal (J x) ≤
            ENNReal.ofReal c * (ENNReal.ofReal c *
              (μHE[n] : Measure (Ambient n ℓ)) (F '' (L k ∩ t k j))) := by
        intro k j
        rcases (L k ∩ t k j).eq_empty_or_nonempty with he | hne
        · simp [he]
        obtain ⟨y, hy, hAky⟩ := hAy k (hne.mono inter_subset_left) j
        have hJA : Jl (A k j) = J y := by rw [hAky, hJv]
        have hJy : J y ∈ Ico (c ^ k) (c ^ (k + 1)) := hy.2
        have hck : 0 < c ^ k := zpow_pos hc0 k
        have hstep : c ^ (k + 1) = c * c ^ k := by rw [zpow_add_one₀ hc0.ne', mul_comm]
        have hinjA : Function.Injective (A k j) := by
          by_contra h
          exact (hck.trans_le hJy.1).ne' (by rw [← hJA]; exact LA2 _ h)
        have happ' :
            ApproximatesLinearOn F (A k j) (L k ∩ t k j) (B12 (A k j) hinjA c hc).choose := by
          have := happ k j
          simp only [r, hinjA, dite_true] at this
          exact this
        have hB := (B12 (A k j) hinjA c hc).choose_spec.2 F (L k ∩ t k j) happ'
        have hcmp1 : ENNReal.ofReal (Jl (A k j)) * volume (L k ∩ t k j) ≤
            ENNReal.ofReal c * ∫⁻ x in L k ∩ t k j, ENNReal.ofReal (J x) := by
          calc ENNReal.ofReal (Jl (A k j)) * volume (L k ∩ t k j)
              = ∫⁻ _ in L k ∩ t k j, ENNReal.ofReal (Jl (A k j)) := (setLIntegral_const _ _).symm
            _ ≤ ∫⁻ x in L k ∩ t k j, ENNReal.ofReal c * ENNReal.ofReal (J x) := by
              apply setLIntegral_mono (hJm.ennreal_ofReal.const_mul _)
              intro x hx
              have hJx : J x ∈ Ico (c ^ k) (c ^ (k + 1)) := hx.1.2
              rw [← ENNReal.ofReal_mul hc0.le]
              apply ENNReal.ofReal_le_ofReal
              rw [hJA]
              exact (hJy.2.trans_eq hstep).le.trans (mul_le_mul_of_nonneg_left hJx.1 hc0.le)
            _ = ENNReal.ofReal c * ∫⁻ x in L k ∩ t k j, ENNReal.ofReal (J x) :=
              lintegral_const_mul _ hJm.ennreal_ofReal
        have hcmp2 : ∫⁻ x in L k ∩ t k j, ENNReal.ofReal (J x) ≤
            ENNReal.ofReal c * (ENNReal.ofReal (Jl (A k j)) * volume (L k ∩ t k j)) := by
          calc ∫⁻ x in L k ∩ t k j, ENNReal.ofReal (J x)
              ≤ ∫⁻ _ in L k ∩ t k j, ENNReal.ofReal c * ENNReal.ofReal (Jl (A k j)) := by
                apply setLIntegral_mono measurable_const
                intro x hx
                have hJx : J x ∈ Ico (c ^ k) (c ^ (k + 1)) := hx.1.2
                rw [← ENNReal.ofReal_mul hc0.le]
                apply ENNReal.ofReal_le_ofReal
                rw [hJA]
                exact (hJx.2.trans_eq hstep).le.trans (mul_le_mul_of_nonneg_left hJy.1 hc0.le)
            _ = ENNReal.ofReal c * (ENNReal.ofReal (Jl (A k j)) * volume (L k ∩ t k j)) := by
                rw [setLIntegral_const, mul_assoc]
        constructor
        · calc (μHE[n] : Measure (Ambient n ℓ)) (F '' (L k ∩ t k j))
              ≤ ENNReal.ofReal c * (ENNReal.ofReal (Jl (A k j)) * volume (L k ∩ t k j)) := hB.1
            _ ≤ ENNReal.ofReal c * (ENNReal.ofReal c * ∫⁻ x in L k ∩ t k j, ENNReal.ofReal (J x)) :=
              mul_le_mul' le_rfl hcmp1
        · calc ∫⁻ x in L k ∩ t k j, ENNReal.ofReal (J x)
              ≤ ENNReal.ofReal c * (ENNReal.ofReal (Jl (A k j)) * volume (L k ∩ t k j)) := hcmp2
            _ ≤ ENNReal.ofReal c * (ENNReal.ofReal c *
                (μHE[n] : Measure (Ambient n ℓ)) (F '' (L k ∩ t k j))) :=
              mul_le_mul' le_rfl (hB.2 (hinjs.mono (hPs k j)))
      have hFL : ∀ k, (μHE[n] : Measure (Ambient n ℓ)) (F '' L k) =
          ∑' j, μHE[n] (F '' (L k ∩ t k j)) := by
        intro k
        conv_lhs => rw [hLP k, image_iUnion]
        apply measure_iUnion
        · intro j j' hjj'
          exact himgd _ _ (hPs k j) (hPs k j') (hPd k hjj')
        · exact fun j => (hPm k j).image_of_continuousOn_injOn hFc.continuousOn
            (hinjs.mono (hPs k j))
      have hFs : (μHE[n] : Measure (Ambient n ℓ)) (F '' s) = ∑' k, μHE[n] (F '' L k) := by
        conv_lhs => rw [hLcov, image_iUnion]
        apply measure_iUnion
        · intro k k' hkk'
          exact himgd _ _ (hLs k) (hLs k') (hLd hkk')
        · exact fun k => (hLm k).image_of_continuousOn_injOn hFc.continuousOn (hinjs.mono (hLs k))
      have hIL : ∀ k, ∫⁻ x in L k, ENNReal.ofReal (J x) =
          ∑' j, ∫⁻ x in L k ∩ t k j, ENNReal.ofReal (J x) := by
        intro k
        conv_lhs => rw [hLP k]
        exact lintegral_iUnion (hPm k) (hPd k) _
      have hIs : ∫⁻ x in s, ENNReal.ofReal (J x) = ∑' k, ∫⁻ x in L k, ENNReal.ofReal (J x) := by
        conv_lhs => rw [hLcov]
        exact lintegral_iUnion hLm hLd _
      rw [hFs, hIs]
      simp_rw [hFL, hIL]
      simp only [← ENNReal.tsum_mul_left]
      exact ⟨ENNReal.tsum_le_tsum fun k => ENNReal.tsum_le_tsum fun j => (hpiece k j).1,
        ENNReal.tsum_le_tsum fun k => ENNReal.tsum_le_tsum fun j => (hpiece k j).2⟩
    exact le_antisymm (lim_le _ _ fun c hc => (key c hc).1) (lim_le _ _ fun c hc => (key c hc).2)
  /- Area formula on Borel sets of injectivity: `Hⁿ(F(s)) = ∫_s J`. Split `s` into the part
  outside `D` (null, with null image since `F` is Lipschitz), the part where `J = 0` (null image
  by `hZ`) and the part where `J > 0` (`hPos`). -/
  have hMI : ∀ s : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet s → Set.InjOn F s →
      (μHE[n] : Measure (Ambient n ℓ)) (F '' s) = ∫⁻ x in s, ENNReal.ofReal (J x) := by
    intro s hs hinjs
    have hsDnull : volume (s \ D) = 0 := measure_mono_null (fun x hx => hx.2) hDc
    have hnull : (μHE[n] : Measure (Ambient n ℓ)) (F '' (s \ D)) = 0 := by
      have h := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
        (hF.lipschitzOnWith (s := s \ D))
      rw [hvol, hsDnull, mul_zero] at h
      exact le_antisymm h zero_le
    have hs₀m : MeasurableSet (s ∩ D ∩ J ⁻¹' {0}) :=
      (hs.inter hDm).inter (hJm (measurableSet_singleton 0))
    have hs₁m : MeasurableSet (s ∩ D ∩ J ⁻¹' Ioi 0) := (hs.inter hDm).inter (hJm measurableSet_Ioi)
    have hZ0 : (μHE[n] : Measure (Ambient n ℓ)) (F '' (s ∩ D ∩ J ⁻¹' {0})) = 0 :=
      hZ _ hs₀m (fun x hx => hx.1.2) (fun x hx => hx.2)
    have hP1 := hPos _ hs₁m (fun x hx => hx.1.2) (hinjs.mono fun x hx => hx.1.1) (fun x hx => hx.2)
    have hmeas_eq : (μHE[n] : Measure (Ambient n ℓ)) (F '' s) =
        μHE[n] (F '' (s ∩ D ∩ J ⁻¹' Ioi 0)) := by
      apply le_antisymm _ (measure_mono (image_mono fun x hx => hx.1.1))
      have hsub : F '' s ⊆ F '' (s ∩ D ∩ J ⁻¹' Ioi 0) ∪
          (F '' (s ∩ D ∩ J ⁻¹' {0}) ∪ F '' (s \ D)) := by
        rintro _ ⟨x, hx, rfl⟩
        by_cases hxD : x ∈ D
        · rcases (hJnn x).eq_or_lt with h0 | hpos
          · exact Or.inr (Or.inl ⟨x, ⟨⟨hx, hxD⟩, h0.symm⟩, rfl⟩)
          · exact Or.inl ⟨x, ⟨⟨hx, hxD⟩, hpos⟩, rfl⟩
        · exact Or.inr (Or.inr ⟨x, ⟨hx, hxD⟩, rfl⟩)
      calc (μHE[n] : Measure (Ambient n ℓ)) (F '' s)
          ≤ μHE[n] (F '' (s ∩ D ∩ J ⁻¹' Ioi 0) ∪
              (F '' (s ∩ D ∩ J ⁻¹' {0}) ∪ F '' (s \ D))) := measure_mono hsub
        _ ≤ μHE[n] (F '' (s ∩ D ∩ J ⁻¹' Ioi 0)) +
              μHE[n] (F '' (s ∩ D ∩ J ⁻¹' {0}) ∪ F '' (s \ D)) := measure_union_le _ _
        _ = μHE[n] (F '' (s ∩ D ∩ J ⁻¹' Ioi 0)) := by
            rw [measure_union_null hZ0 hnull, add_zero]
    have hint_eq : ∫⁻ x in s, ENNReal.ofReal (J x) =
        ∫⁻ x in s ∩ D ∩ J ⁻¹' Ioi 0, ENNReal.ofReal (J x) := by
      have h0 : ∫⁻ x in s \ (s ∩ D ∩ J ⁻¹' Ioi 0), ENNReal.ofReal (J x) = 0 := by
        apply le_antisymm _ zero_le
        calc ∫⁻ x in s \ (s ∩ D ∩ J ⁻¹' Ioi 0), ENNReal.ofReal (J x)
            ≤ ∫⁻ x in (s \ D) ∪ (s ∩ D ∩ J ⁻¹' {0}), ENNReal.ofReal (J x) := by
              apply lintegral_mono_set
              rintro x ⟨hx, hx'⟩
              by_cases hxD : x ∈ D
              · refine Or.inr ⟨⟨hx, hxD⟩, ?_⟩
                rcases (hJnn x).eq_or_lt with h0 | hpos
                · exact h0.symm
                · exact absurd ⟨⟨hx, hxD⟩, hpos⟩ hx'
              · exact Or.inl ⟨hx, hxD⟩
          _ ≤ (∫⁻ x in s \ D, ENNReal.ofReal (J x)) +
                ∫⁻ x in s ∩ D ∩ J ⁻¹' {0}, ENNReal.ofReal (J x) := lintegral_union_le _ _ _
          _ = 0 := by
              rw [setLIntegral_measure_zero _ _ hsDnull, zero_add]
              rw [setLIntegral_congr_fun hs₀m (g := fun _ => 0) fun x hx => by
                rw [show J x = 0 from hx.2, ENNReal.ofReal_zero]]
              exact lintegral_zero
      have hsub : s = (s ∩ D ∩ J ⁻¹' Ioi 0) ∪ (s \ (s ∩ D ∩ J ⁻¹' Ioi 0)) :=
        (union_sdiff_cancel fun x hx => hx.1.1).symm
      conv_lhs => rw [hsub]
      rw [lintegral_union (hs.diff hs₁m) disjoint_sdiff_right, h0, add_zero]
    rw [hmeas_eq, hint_eq]
    exact hP1
  refine ⟨J, ?_, ?_, ?_⟩
  · -- `J = Jl ∘ DF` is continuous on `C` since `DF` is.
    rw [hJ]
    exact hJl_cont.comp_continuousOn hcont
  · -- nonnegativity and the linear area factor
    intro v _
    refine ⟨hJnn v, fun S => ?_⟩
    rw [hJv]
    exact hlin _ S
  · -- `Hⁿ ⌞ F(C) = F_#((J · Lⁿ) ⌞ C)`, then change variables.
    intro g hg
    have hmeasure : (μHE[n] : Measure (Ambient n ℓ)).restrict (F '' C) =
        Measure.map F ((volume.restrict C).withDensity fun v => ENNReal.ofReal (J v)) := by
      ext T hT
      rw [Measure.restrict_apply hT, Measure.map_apply hFm hT, withDensity_apply _ (hFm hT),
        Measure.restrict_restrict (hFm hT)]
      have hset : T ∩ F '' C = F '' (F ⁻¹' T ∩ C) := by
        ext y
        constructor
        · rintro ⟨hyT, v, hvC, rfl⟩
          exact ⟨v, ⟨hyT, hvC⟩, rfl⟩
        · rintro ⟨v, ⟨hvT, hvC⟩, rfl⟩
          exact ⟨hvT, v, hvC, rfl⟩
      rw [hset]
      exact hMI _ ((hFm hT).inter hC) (hinj.mono inter_subset_right)
    rw [hmeasure, integral_map hFm.aemeasurable hg.aestronglyMeasurable,
      integral_withDensity_eq_integral_toReal_smul (f := fun v => ENNReal.ofReal (J v))
        (ENNReal.measurable_ofReal.comp hJm) (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only [ENNReal.toReal_ofReal (hJnn v), smul_eq_mul]
/-- Simon 2.1 (p. 87): first-order regularity of a family as in 2.1. The initial velocity
`X = ∂φ_t/∂t|_{t=0}` is `C¹` with `DX = 0` off `K`, and each `φ_t` (`|t| < ε`) is `C¹` and
Lipschitz. -/
theorem Submission.ts_fv_cv_first_order_regularity : ∀ (n ℓ : ℕ) (φ : ℝ → Ambient n ℓ → Ambient n ℓ) (ε : ℝ) (K : Set (Ambient n ℓ)), IsCompactVariation φ ε K → ContDiff ℝ 1 (fun y ↦ deriv (fun t ↦ φ t y) 0) ∧ (∀ y ∉ K, fderiv ℝ (fun y ↦ deriv (fun t ↦ φ t y) 0) y = 0) ∧ (∀ t ∈ Ioo (-ε) ε, (∃ L : NNReal, LipschitzWith L (φ t)) ∧ ContDiff ℝ 1 (φ t)) := by
  intro n ℓ φ ε K hφ
  -- `Φ(q) = φ q.1 q.2` is `C^∞` on the open set `S = (-ε, ε) × ℝ^{n+ℓ}`; `Kᶜ` is open.
  have hS : IsOpen (Ioo (-ε) ε ×ˢ (univ : Set (Ambient n ℓ))) := isOpen_Ioo.prod isOpen_univ
  have hmem : ∀ t ∈ Ioo (-ε) ε, ∀ y : Ambient n ℓ,
      (t, y) ∈ Ioo (-ε) ε ×ˢ (univ : Set (Ambient n ℓ)) :=
    fun t ht y ↦ ⟨ht, mem_univ y⟩
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_lt_zero.mpr hφ.pos, hφ.pos⟩
  have hKc : IsOpen Kᶜ := hφ.compact.isClosed.isOpen_compl
  -- Chain rule along `t ↦ (t, y)`: `X(y) = DΦ(0, y)(1, 0)`.
  have hvel : ∀ y, deriv (fun t ↦ φ t y) 0 =
      fderiv ℝ (fun q : ℝ × Ambient n ℓ ↦ φ q.1 q.2) (0, y) (1, 0) := by
    intro y
    have hdiff : DifferentiableAt ℝ (fun q : ℝ × Ambient n ℓ ↦ φ q.1 q.2) (0, y) :=
      (hφ.smooth.contDiffAt (hS.mem_nhds (hmem 0 h0 y))).differentiableAt (by simp)
    have hg : HasDerivAt (fun t : ℝ ↦ (t, y)) ((1 : ℝ), (0 : Ambient n ℓ)) 0 :=
      (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) y)
    exact (hdiff.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hg).deriv
  -- (a) `DΦ` is `C¹` on `S`, so `y ↦ DΦ(0, y)(1, 0)` is `C¹`.
  have ha : ContDiff ℝ 1 (fun y ↦ deriv (fun t ↦ φ t y) 0) := by
    have h1 : ContDiffOn ℝ 1 (fderiv ℝ (fun q : ℝ × Ambient n ℓ ↦ φ q.1 q.2))
        (Ioo (-ε) ε ×ˢ univ) :=
      hφ.smooth.fderiv_of_isOpen hS (WithTop.coe_le_coe.mpr le_top)
    have h2 : ContDiff ℝ 1
        (fun y : Ambient n ℓ ↦ fderiv ℝ (fun q : ℝ × Ambient n ℓ ↦ φ q.1 q.2) (0, y)) := by
      rw [← contDiffOn_univ]
      exact h1.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun y _ ↦ hmem 0 h0 y)
    simp_rw [hvel]
    exact h2.clm_apply contDiff_const
  -- Off `K`, `t ↦ φ t y` is constant near `0`, so `X(y) = 0`.
  have hzero : ∀ y ∉ K, deriv (fun t ↦ φ t y) 0 = 0 := by
    intro y hy
    have : (fun t ↦ φ t y) =ᶠ[𝓝 0] fun _ ↦ y := by
      filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr hφ.pos) hφ.pos] with t ht
      exact hφ.fixed t ht y hy
    rw [this.deriv_eq, deriv_const]
  refine ⟨ha, fun y hy ↦ ?_, fun t ht ↦ ?_⟩
  -- (b) `X = 0` on the open neighbourhood `Kᶜ` of `y`, so `DX(y) = 0`.
  · have : (fun y ↦ deriv (fun t ↦ φ t y) 0) =ᶠ[𝓝 y] fun _ ↦ (0 : Ambient n ℓ) := by
      filter_upwards [hKc.mem_nhds hy] with z hz
      exact hzero z hz
    rw [this.fderiv_eq, fderiv_const_apply]
  -- (c) `φ t = Φ ∘ (y ↦ (t, y))` is `C^∞`.
  have hsm : ContDiff ℝ ∞ (φ t) := by
    rw [contDiff_iff_contDiffAt]
    intro y
    exact (hφ.smooth.contDiffAt (hS.mem_nhds (hmem t ht y))).comp y
      (contDiffAt_const.prodMk contDiffAt_id)
  have hC1 : ContDiff ℝ 1 (φ t) := hsm.of_le (WithTop.coe_le_coe.mpr le_top)
  -- `Dφ_t = I` off `K`, so `‖Dφ_t‖ ≤ 1` there.
  have hout : ∀ y ∉ K, ‖fderiv ℝ (φ t) y‖ ≤ 1 := by
    intro y hy
    have : φ t =ᶠ[𝓝 y] id := by
      filter_upwards [hKc.mem_nhds hy] with z hz
      exact hφ.fixed t ht z hz
    rw [this.fderiv_eq, fderiv_id]
    exact ContinuousLinearMap.norm_id_le
  -- `Dφ_t` is continuous, hence bounded on the compact set `K`.
  obtain ⟨L₀, hL₀⟩ :=
    hφ.compact.exists_bound_of_continuousOn (hC1.continuous_fderiv one_ne_zero).continuousOn
  -- Mean value inequality with `‖Dφ_t‖ ≤ max L₀ 1`.
  let L : NNReal := ⟨max L₀ 1, zero_le_one.trans (le_max_right _ _)⟩
  refine ⟨⟨L, lipschitzWith_of_nnnorm_fderiv_le (hC1.differentiable one_ne_zero) fun y ↦ ?_⟩, hC1⟩
  rw [← NNReal.coe_le_coe, coe_nnnorm]
  change ‖fderiv ℝ (φ t) y‖ ≤ max L₀ 1
  by_cases hy : y ∈ K
  · exact (hL₀ y hy).trans (le_max_left _ _)
  · exact (hout y hy).trans (le_max_right _ _)
/-- Simon 2.1 (p. 87): for a family as in 2.1 and `0 < δ < ε`, the spatial derivatives
`Dφ_t(x)` (`|t| < δ`, `x ∈ ℝ^{n+ℓ}`) and their inverses are bounded uniformly:
`‖Dφ_t(x)‖ ≤ B` and `|v| ≤ B |Dφ_t(x) v|`. -/
theorem Submission.ts_fv_cv_slice_fderiv_bounds : ∀ (n ℓ : ℕ) (φ : ℝ → Ambient n ℓ → Ambient n ℓ) (ε : ℝ) (K : Set (Ambient n ℓ)), IsCompactVariation φ ε K → ∀ δ : ℝ, 0 < δ → δ < ε → ∃ B : ℝ, ∀ x, ∀ t ∈ Ioo (-δ) δ, ‖fderiv ℝ (φ t) x‖ ≤ B ∧ ∀ v, ‖v‖ ≤ B * ‖fderiv ℝ (φ t) x v‖ := by
  intro n ℓ φ ε K hφ δ hδ hδε
  have hU : IsOpen (Ioo (-ε) ε ×ˢ (univ : Set (Ambient n ℓ))) := isOpen_Ioo.prod isOpen_univ
  -- Chain rule along `y ↦ (t, y)`: `Dφ_t(y) = DΦ(t, y) ∘ ι₂` for `t ∈ (-ε, ε)`.
  have hslice : ∀ t ∈ Ioo (-ε) ε, ∀ y : Ambient n ℓ, HasFDerivAt (φ t)
      ((fderiv ℝ (fun q : ℝ × Ambient n ℓ ↦ φ q.1 q.2) (t, y)).comp
        (ContinuousLinearMap.inr ℝ ℝ (Ambient n ℓ))) y := by
    intro t ht y
    have hdiff : DifferentiableAt ℝ (fun q : ℝ × Ambient n ℓ ↦ φ q.1 q.2) (t, y) :=
      (hφ.smooth.contDiffAt (hU.mem_nhds ⟨ht, mem_univ _⟩)).differentiableAt (by simp)
    exact hdiff.hasFDerivAt.comp y ((hasFDerivAt_const t y).prodMk (hasFDerivAt_id y))
  -- `G(q) = Dφ_{q.1}(q.2)` is continuous on `U = (-ε, ε) × ℝ^{n+ℓ}`.
  have hG : ContinuousOn (fun q : ℝ × Ambient n ℓ ↦ fderiv ℝ (φ q.1) q.2)
      (Ioo (-ε) ε ×ˢ univ) := by
    have h1 := (hφ.smooth.continuousOn_fderiv_of_isOpen hU (by simp)).clm_comp
      (continuousOn_const (c := ContinuousLinearMap.inr ℝ ℝ (Ambient n ℓ)))
    refine h1.congr ?_
    rintro ⟨t, y⟩ ⟨ht, -⟩
    exact (hslice t ht y).fderiv
  -- `Dφ_t(x)` is a unit of `L(ℝ^{n+ℓ}, ℝ^{n+ℓ})`, with inverse `Dψ(φ_t x)`, `ψ = φ_t⁻¹`.
  have hunit : ∀ t ∈ Ioo (-ε) ε, ∀ x : Ambient n ℓ, IsUnit (fderiv ℝ (φ t) x) := by
    intro t ht x
    obtain ⟨hbij, hψ⟩ := hφ.diffeo t ht
    have hleft : ∀ y, Function.invFun (φ t) (φ t y) = y :=
      Function.leftInverse_invFun hbij.injective
    have hright : ∀ y, φ t (Function.invFun (φ t) y) = y :=
      Function.rightInverse_invFun hbij.surjective
    have hdφ : HasFDerivAt (φ t) (fderiv ℝ (φ t) x) x :=
      (hslice t ht x).differentiableAt.hasFDerivAt
    have hdψ : HasFDerivAt (Function.invFun (φ t))
        (fderiv ℝ (Function.invFun (φ t)) (φ t x)) (φ t x) :=
      (hψ.differentiable (by simp) (φ t x)).hasFDerivAt
    have h1 : (fderiv ℝ (Function.invFun (φ t)) (φ t x)).comp (fderiv ℝ (φ t) x) =
        ContinuousLinearMap.id ℝ (Ambient n ℓ) := by
      have hcomp := hdψ.comp x hdφ
      rw [show Function.invFun (φ t) ∘ φ t = id from funext hleft] at hcomp
      exact hcomp.unique (hasFDerivAt_id x)
    have h2 : (fderiv ℝ (φ t) x).comp (fderiv ℝ (Function.invFun (φ t)) (φ t x)) =
        ContinuousLinearMap.id ℝ (Ambient n ℓ) := by
      have hdφ' : HasFDerivAt (φ t) (fderiv ℝ (φ t) x) (Function.invFun (φ t) (φ t x)) := by
        rw [hleft]; exact hdφ
      have hcomp := hdφ'.comp (φ t x) hdψ
      rw [show φ t ∘ Function.invFun (φ t) = id from funext hright] at hcomp
      exact hcomp.unique (hasFDerivAt_id (φ t x))
    exact ⟨⟨fderiv ℝ (φ t) x, fderiv ℝ (Function.invFun (φ t)) (φ t x), h2, h1⟩, rfl⟩
  -- Off `K`, `φ_t = id` near the point, so `Dφ_t = I`.
  have hidK : ∀ t ∈ Ioo (-ε) ε, ∀ y ∉ K,
      fderiv ℝ (φ t) y = ContinuousLinearMap.id ℝ (Ambient n ℓ) := by
    intro t ht y hy
    have h : φ t =ᶠ[𝓝 y] id := by
      filter_upwards [hφ.compact.isClosed.isOpen_compl.mem_nhds hy] with z hz
      exact hφ.fixed t ht z hz
    rw [h.fderiv_eq, fderiv_id]
  -- The compact set `Q = [-δ, δ] × K ⊆ U`.
  have hQ : IsCompact (Icc (-δ) δ ×ˢ K) := isCompact_Icc.prod hφ.compact
  have hQU : Icc (-δ) δ ×ˢ K ⊆ Ioo (-ε) ε ×ˢ (univ : Set (Ambient n ℓ)) := by
    rintro ⟨t, y⟩ ⟨⟨h1, h2⟩, -⟩
    exact ⟨⟨by linarith, by linarith⟩, mem_univ _⟩
  -- `Ring.inverse ∘ G` is continuous on `Q`, since `Ring.inverse` is continuous at units.
  have hInv : ContinuousOn (fun q : ℝ × Ambient n ℓ ↦ Ring.inverse (fderiv ℝ (φ q.1) q.2))
      (Icc (-δ) δ ×ˢ K) := by
    intro q hq
    have hu : IsUnit (fderiv ℝ (φ q.1) q.2) := hunit q.1 (hQU hq).1 q.2
    have hcont : ContinuousAt Ring.inverse (fderiv ℝ (φ q.1) q.2) := by
      simpa only [hu.unit_spec] using NormedRing.inverse_continuousAt hu.unit
    exact hcont.comp_continuousWithinAt (f := fun q : ℝ × Ambient n ℓ ↦ fderiv ℝ (φ q.1) q.2)
      ((hG q (hQU hq)).mono hQU)
  obtain ⟨B₁, hB₁⟩ := hQ.exists_bound_of_continuousOn (hG.mono hQU)
  obtain ⟨B₃, hB₃⟩ := hQ.exists_bound_of_continuousOn hInv
  refine ⟨max 1 (max B₁ B₃), fun x t ht ↦ ?_⟩
  have htε : t ∈ Ioo (-ε) ε := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  by_cases hx : x ∈ K
  · have hq : (t, x) ∈ Icc (-δ) δ ×ˢ K := ⟨⟨ht.1.le, ht.2.le⟩, hx⟩
    have hb1 : ‖fderiv ℝ (φ t) x‖ ≤ B₁ := hB₁ (t, x) hq
    have hb3 : ‖Ring.inverse (fderiv ℝ (φ t) x)‖ ≤ B₃ := hB₃ (t, x) hq
    refine ⟨hb1.trans ((le_max_left _ _).trans (le_max_right _ _)), fun v ↦ ?_⟩
    have hv : Ring.inverse (fderiv ℝ (φ t) x) (fderiv ℝ (φ t) x v) = v := by
      change (Ring.inverse (fderiv ℝ (φ t) x) * fderiv ℝ (φ t) x) v = v
      rw [Ring.inverse_mul_cancel _ (hunit t htε x)]
      rfl
    calc ‖v‖ = ‖Ring.inverse (fderiv ℝ (φ t) x) (fderiv ℝ (φ t) x v)‖ := by rw [hv]
      _ ≤ ‖Ring.inverse (fderiv ℝ (φ t) x)‖ * ‖fderiv ℝ (φ t) x v‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ max 1 (max B₁ B₃) * ‖fderiv ℝ (φ t) x v‖ :=
        mul_le_mul_of_nonneg_right (hb3.trans ((le_max_right _ _).trans (le_max_right _ _)))
          (norm_nonneg _)
  · rw [hidK t htε x hx]
    exact ⟨ContinuousLinearMap.norm_id_le.trans (le_max_left _ _),
      fun v ↦ le_mul_of_one_le_left (norm_nonneg _) (le_max_left _ _)⟩
theorem Submission.ts_fv_cv_slice_fderiv_time_deriv : ∀ (n ℓ : ℕ) (φ : ℝ → Ambient n ℓ → Ambient n ℓ) (ε : ℝ) (K : Set (Ambient n ℓ)), IsCompactVariation φ ε K → ∃ Λ' : ℝ → Ambient n ℓ → (Ambient n ℓ →L[ℝ] Ambient n ℓ), (∀ x, Λ' 0 x = fderiv ℝ (fun y ↦ deriv (fun t ↦ φ t y) 0) x ∧ ∀ t ∈ Ioo (-ε) ε, HasDerivAt (fun s ↦ fderiv ℝ (φ s) x) (Λ' t x) t) ∧ ∀ δ : ℝ, 0 < δ → δ < ε → ∃ B : ℝ, ∀ x, ∀ t ∈ Ioo (-δ) δ, ‖Λ' t x‖ ≤ B := by
  intro n ℓ φ ε K hφ
  obtain ⟨hε, hK, hsm, -, -, hfix⟩ := hφ
  -- Step 1. `Φ(t, y) = φ t y` is `C^∞` on the open set `U = (-ε, ε) × ℝ^{n+ℓ}`.
  set Φ : ℝ × Ambient n ℓ → Ambient n ℓ := fun q ↦ φ q.1 q.2
  set U : Set (ℝ × Ambient n ℓ) := Ioo (-ε) ε ×ˢ univ
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_univ
  have hmem : ∀ t ∈ Ioo (-ε) ε, ∀ y : Ambient n ℓ, ((t, y) : ℝ × Ambient n ℓ) ∈ U :=
    fun t ht y ↦ Set.mk_mem_prod ht (mem_univ y)
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hD1 : ContDiffOn ℝ ∞ (fderiv ℝ Φ) U := hsm.fderiv_of_isOpen hU (by simp)
  have hΦd : ∀ q ∈ U, HasFDerivAt Φ (fderiv ℝ Φ q) q := fun q hq ↦
    ((hsm.contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp)).hasFDerivAt
  have hD1d : ∀ q ∈ U, HasFDerivAt (fderiv ℝ Φ) (fderiv ℝ (fderiv ℝ Φ) q) q := fun q hq ↦
    ((hD1.contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp)).hasFDerivAt
  have hD2c : ContinuousOn (fderiv ℝ (fderiv ℝ Φ)) U :=
    hD1.continuousOn_fderiv_of_isOpen hU (by simp)
  -- Step 6(iii). Symmetry of `D²Φ` on `U`, from the mean value inequality and the continuity
  -- of `D²Φ` (`ContDiffAt.isSymmSndFDerivAt` is not reachable from the frozen imports).
  have hsymm : ∀ p ∈ U, ∀ a b : ℝ × Ambient n ℓ,
      fderiv ℝ (fderiv ℝ Φ) p a b = fderiv ℝ (fderiv ℝ Φ) p b a := by
    intro p hp a b
    rw [← sub_eq_zero, ← norm_le_zero_iff]
    refine le_of_forall_pos_le_add fun η hη ↦ ?_
    rw [zero_add]
    obtain ⟨η', hη'pos, hη'le⟩ : ∃ η' : ℝ, 0 < η' ∧ 2 * η' * (‖a‖ * ‖b‖) ≤ η := by
      have hm : 0 < ‖a‖ * ‖b‖ + 1 := by positivity
      refine ⟨η / 2 / (‖a‖ * ‖b‖ + 1), by positivity, ?_⟩
      calc 2 * (η / 2 / (‖a‖ * ‖b‖ + 1)) * (‖a‖ * ‖b‖)
          = η * (‖a‖ * ‖b‖) / (‖a‖ * ‖b‖ + 1) := by ring
        _ ≤ η := by rw [div_le_iff₀ hm]; nlinarith
    obtain ⟨r₁, hr₁, hr₁U⟩ := Metric.isOpen_iff.1 hU p hp
    have hball : ball (fderiv ℝ (fderiv ℝ Φ) p) η' ∈ 𝓝 (fderiv ℝ (fderiv ℝ Φ) p) :=
      ball_mem_nhds (fderiv ℝ (fderiv ℝ Φ) p) hη'pos
    obtain ⟨r₂, hr₂, hr₂c⟩ := Metric.mem_nhds_iff.1 (hD2c.continuousAt (hU.mem_nhds hp) hball)
    obtain ⟨r, hr0, hrU, hrc⟩ : ∃ r : ℝ, 0 < r ∧ ball p r ⊆ U ∧
        ∀ q ∈ ball p r, ‖fderiv ℝ (fderiv ℝ Φ) q - fderiv ℝ (fderiv ℝ Φ) p‖ ≤ η' := by
      refine ⟨min r₁ r₂, lt_min hr₁ hr₂, (ball_subset_ball (min_le_left _ _)).trans hr₁U,
        fun q hq ↦ ?_⟩
      have hq2 : fderiv ℝ (fderiv ℝ Φ) q ∈ ball (fderiv ℝ (fderiv ℝ Φ) p) η' :=
        hr₂c (ball_subset_ball (min_le_right _ _) hq)
      exact ((mem_ball_iff_norm (E := ℝ × Ambient n ℓ →L[ℝ] ℝ × Ambient n ℓ →L[ℝ] Ambient n ℓ)).1
        hq2).le
    have hmvt : ∀ y ∈ ball p r, ∀ z ∈ ball p r,
        ‖fderiv ℝ Φ z - fderiv ℝ Φ y - fderiv ℝ (fderiv ℝ Φ) p (z - y)‖ ≤ η' * ‖z - y‖ :=
      fun y hy z hz ↦ (convex_ball p r).norm_image_sub_le_of_norm_hasFDerivWithin_le'
        (fun q hq ↦ (hD1d q (hrU hq)).hasFDerivWithinAt) hrc hy hz
    -- second differences: `Φ(p+k+l) - Φ(p+k) - Φ(p+l) + Φ(p) = D²Φ(p) l k + O(η' |k| |l|)`
    have hstep : ∀ k l : ℝ × Ambient n ℓ, ‖k‖ < r / 2 → ‖l‖ < r / 2 →
        ‖Φ (p + k + l) - Φ (p + k) - (Φ (p + l) - Φ p) - fderiv ℝ (fderiv ℝ Φ) p l k‖ ≤
          η' * ‖l‖ * ‖k‖ := by
      intro k l hk hl
      have hsub : ∀ y ∈ ball p (r / 2), y ∈ ball p r ∧ y + l ∈ ball p r := by
        intro y hy
        rw [mem_ball_iff_norm] at hy
        refine ⟨mem_ball_iff_norm.2 (by linarith), mem_ball_iff_norm.2 ?_⟩
        calc ‖y + l - p‖ = ‖(y - p) + l‖ := by congr 1; abel
          _ ≤ ‖y - p‖ + ‖l‖ := norm_add_le _ _
          _ < r := by linarith
      have hψ : ∀ y ∈ ball p (r / 2), HasFDerivWithinAt (fun y ↦ Φ (y + l) - Φ y)
          (fderiv ℝ Φ (y + l) - fderiv ℝ Φ y) (ball p (r / 2)) y := by
        intro y hy
        have h1 : HasFDerivAt (fun y ↦ Φ (y + l)) (fderiv ℝ Φ (y + l)) y :=
          (hasFDerivAt_comp_add_right l).2 (hΦd (y + l) (hrU (hsub y hy).2))
        exact (h1.sub (hΦd y (hrU (hsub y hy).1))).hasFDerivWithinAt
      have hbd : ∀ y ∈ ball p (r / 2), ‖fderiv ℝ Φ (y + l) - fderiv ℝ Φ y -
          fderiv ℝ (fderiv ℝ Φ) p l‖ ≤ η' * ‖l‖ := by
        intro y hy
        have h := hmvt y (hsub y hy).1 (y + l) (hsub y hy).2
        rwa [add_sub_cancel_left] at h
      have hpk : p + k ∈ ball p (r / 2) := by
        rw [mem_ball_iff_norm, add_sub_cancel_left]
        exact hk
      have h := (convex_ball p (r / 2)).norm_image_sub_le_of_norm_hasFDerivWithin_le' hψ hbd
        (mem_ball_self (half_pos hr0)) hpk
      rwa [add_sub_cancel_left] at h
    -- rescale `a`, `b` into the ball and compare the two orders
    obtain ⟨c, hcpos, hca, hcb⟩ : ∃ c : ℝ, 0 < c ∧ ‖c • a‖ < r / 2 ∧ ‖c • b‖ < r / 2 := by
      have hs : 0 < ‖a‖ + ‖b‖ + 1 := by positivity
      have hc0 : 0 < r / 2 / (‖a‖ + ‖b‖ + 1) := by positivity
      refine ⟨r / 2 / (‖a‖ + ‖b‖ + 1), hc0, ?_, ?_⟩ <;>
        rw [norm_smul, Real.norm_of_nonneg hc0.le, div_mul_eq_mul_div, div_lt_iff₀ hs] <;>
        nlinarith [norm_nonneg a, norm_nonneg b, half_pos hr0]
    have h1 := hstep (c • a) (c • b) hca hcb
    have h2 := hstep (c • b) (c • a) hcb hca
    rw [add_right_comm p (c • b) (c • a)] at h2
    have hcc : 0 < c * c := mul_pos hcpos hcpos
    have e1 : fderiv ℝ (fderiv ℝ Φ) p (c • a) (c • b) - fderiv ℝ (fderiv ℝ Φ) p (c • b) (c • a) =
        (c * c) • (fderiv ℝ (fderiv ℝ Φ) p a b - fderiv ℝ (fderiv ℝ Φ) p b a) := by
      simp only [map_smul, smul_apply, smul_sub, smul_smul]
    have e2 : fderiv ℝ (fderiv ℝ Φ) p (c • a) (c • b) - fderiv ℝ (fderiv ℝ Φ) p (c • b) (c • a) =
        (Φ (p + c • a + c • b) - Φ (p + c • a) - (Φ (p + c • b) - Φ p) -
            fderiv ℝ (fderiv ℝ Φ) p (c • b) (c • a)) -
          (Φ (p + c • a + c • b) - Φ (p + c • b) - (Φ (p + c • a) - Φ p) -
            fderiv ℝ (fderiv ℝ Φ) p (c • a) (c • b)) := by
      abel
    have hle : c * c * ‖fderiv ℝ (fderiv ℝ Φ) p a b - fderiv ℝ (fderiv ℝ Φ) p b a‖ ≤
        c * c * (2 * η' * (‖a‖ * ‖b‖)) :=
      calc c * c * ‖fderiv ℝ (fderiv ℝ Φ) p a b - fderiv ℝ (fderiv ℝ Φ) p b a‖
          = ‖fderiv ℝ (fderiv ℝ Φ) p (c • a) (c • b) -
              fderiv ℝ (fderiv ℝ Φ) p (c • b) (c • a)‖ := by
            rw [e1, norm_smul, Real.norm_of_nonneg hcc.le]
        _ ≤ η' * ‖c • b‖ * ‖c • a‖ + η' * ‖c • a‖ * ‖c • b‖ := by
            rw [e2]
            exact (norm_sub_le _ _).trans (add_le_add h1 h2)
        _ = c * c * (2 * η' * (‖a‖ * ‖b‖)) := by
            rw [norm_smul, norm_smul, Real.norm_of_nonneg hcpos.le]
            ring
    exact (le_of_mul_le_mul_left hle hcc).trans hη'le
  -- Step 3. Time slices: `D(φ s)(y) = DΦ(s, y) ∘ ι₂` for `s ∈ (-ε, ε)`.
  have hslice : ∀ s ∈ Ioo (-ε) ε, ∀ y : Ambient n ℓ,
      fderiv ℝ (φ s) y = (fderiv ℝ Φ (s, y)).comp (ContinuousLinearMap.inr ℝ ℝ (Ambient n ℓ)) := by
    intro s hs y
    have h := (hΦd (s, y) (hmem s hs y)).comp y (hasFDerivAt_prodMk_right s y)
    exact h.fderiv
  -- Step 4. `Λ'(t, x) = D²Φ(t, x)(1, 0) ∘ ι₂`, i.e. `DG(t, x)(1, 0)` for `G(q) = DΦ(q) ∘ ι₂`.
  refine ⟨fun t x ↦ (fderiv ℝ (fderiv ℝ Φ) (t, x) ((1 : ℝ), (0 : Ambient n ℓ))).comp
      (ContinuousLinearMap.inr ℝ ℝ (Ambient n ℓ)), fun x ↦ ⟨?_, fun t ht ↦ ?_⟩, fun δ hδ hδε ↦ ?_⟩
  · -- Step 6. `Λ'(0, x) = DX(x)`, by the symmetry of `D²Φ(0, x)`.
    have hX : (fun y ↦ deriv (fun t ↦ φ t y) 0) =
        fun y ↦ fderiv ℝ Φ ((0 : ℝ), y) ((1 : ℝ), (0 : Ambient n ℓ)) := by
      funext y
      have hk : HasDerivAt (fun t : ℝ ↦ (t, y)) ((1 : ℝ), (0 : Ambient n ℓ)) 0 :=
        (hasDerivAt_id' (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) y)
      have h := HasFDerivAt.comp_hasDerivAt (l := Φ) (f := fun t : ℝ ↦ (t, y)) (0 : ℝ)
        (hΦd ((0 : ℝ), y) (hmem 0 h0 y)) hk
      exact h.deriv
    have hc : HasFDerivAt (fun y : Ambient n ℓ ↦ fderiv ℝ Φ ((0 : ℝ), y))
        ((fderiv ℝ (fderiv ℝ Φ) ((0 : ℝ), x)).comp
          (ContinuousLinearMap.inr ℝ ℝ (Ambient n ℓ))) x := by
      have h := (hD1d ((0 : ℝ), x) (hmem 0 h0 x)).comp x (hasFDerivAt_prodMk_right (0 : ℝ) x)
      exact h
    have hXd : HasFDerivAt (fun y ↦ deriv (fun t ↦ φ t y) 0)
        (((fderiv ℝ (fderiv ℝ Φ) ((0 : ℝ), x)).comp
          (ContinuousLinearMap.inr ℝ ℝ (Ambient n ℓ))).flip ((1 : ℝ), (0 : Ambient n ℓ))) x := by
      rw [hX]
      have h := hc.clm_apply (hasFDerivAt_const ((1 : ℝ), (0 : Ambient n ℓ)) x)
      rw [ContinuousLinearMap.comp_zero, zero_add] at h
      exact h
    rw [hXd.fderiv]
    ext1 v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.inr_apply]
    exact hsymm _ (hmem 0 h0 x) _ _
  · -- Step 5. `s ↦ D(φ s)(x)` has derivative `Λ'(t, x)` at `t`.
    have hk : HasDerivAt (fun s : ℝ ↦ (s, x)) ((1 : ℝ), (0 : Ambient n ℓ)) t :=
      (hasDerivAt_id' t).prodMk (hasDerivAt_const t x)
    have h1 : HasDerivAt (fun s ↦ fderiv ℝ Φ (s, x))
        (fderiv ℝ (fderiv ℝ Φ) (t, x) ((1 : ℝ), (0 : Ambient n ℓ))) t := by
      have h := HasFDerivAt.comp_hasDerivAt (l := fderiv ℝ Φ) (f := fun s : ℝ ↦ (s, x)) t
        (hD1d (t, x) (hmem t ht x)) hk
      exact h
    have h2 := h1.clm_comp (hasDerivAt_const t (ContinuousLinearMap.inr ℝ ℝ (Ambient n ℓ)))
    rw [ContinuousLinearMap.comp_zero, add_zero] at h2
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact hslice s hs x
  · -- Step 8. Uniform bound: compactness of `[-δ, δ] × K`, and `Λ' = 0` off `K`.
    have hcont : ContinuousOn (fun q : ℝ × Ambient n ℓ ↦
        (fderiv ℝ (fderiv ℝ Φ) q ((1 : ℝ), (0 : Ambient n ℓ))).comp
          (ContinuousLinearMap.inr ℝ ℝ (Ambient n ℓ))) U :=
      (hD2c.clm_apply continuousOn_const).clm_comp continuousOn_const
    have hQU : Icc (-δ) δ ×ˢ K ⊆ U := fun q hq ↦
      Set.mem_prod.2 ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, mem_univ _⟩
    obtain ⟨B, hB⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn (hcont.mono hQU)
    refine ⟨max B 0, fun x t ht ↦ ?_⟩
    have htε : t ∈ Ioo (-ε) ε := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    by_cases hx : x ∈ K
    · exact (hB (t, x) (Set.mk_mem_prod (Ioo_subset_Icc_self ht) hx)).trans (le_max_left _ _)
    · have hW : IsOpen (Ioo (-ε) ε ×ˢ Kᶜ) := isOpen_Ioo.prod hK.isClosed.isOpen_compl
      have hev : fderiv ℝ Φ =ᶠ[𝓝 (t, x)] fun _ ↦ ContinuousLinearMap.snd ℝ ℝ (Ambient n ℓ) := by
        filter_upwards [hW.mem_nhds (Set.mk_mem_prod htε (Set.mem_compl hx))] with q hq
        have hq' : Φ =ᶠ[𝓝 q] Prod.snd := by
          filter_upwards [hW.mem_nhds hq] with q' hq'
          exact hfix q'.1 hq'.1 q'.2 hq'.2
        rw [hq'.fderiv_eq, fderiv_snd]
      have hD0 : fderiv ℝ (fderiv ℝ Φ) (t, x) = 0 := by
        rw [hev.fderiv_eq, fderiv_const_apply]
      simp only [hD0, zero_apply, ContinuousLinearMap.zero_comp, norm_zero]
      exact le_max_right _ _

/-- Simon 2.1 (p. 87): for a family `{φ_t}` as in 2.1 with initial velocity
`X = ∂φ_t/∂t|_{t=0}`, `X` is `C¹` with `DX = 0` off `K`, each `φ_t` is Lipschitz and `C¹`, and
for `|t| < δ = ε/2` the derivatives `Dφ_t(x)`, their time derivatives
`Λ'(t, x) = ∂_s Dφ_s(x)|_{s=t}` (with `Λ'(0, x) = DX(x)`) and the inverses of `Dφ_t(x)` are
bounded uniformly by `B`. -/
theorem Submission.ts_fv_compact_variation_bounds : ∀ (n ℓ : ℕ) (φ : ℝ → Ambient n ℓ → Ambient n ℓ) (ε : ℝ) (K : Set (Ambient n ℓ)), IsCompactVariation φ ε K → ContDiff ℝ 1 (fun y ↦ deriv (fun t ↦ φ t y) 0) ∧ (∀ y ∉ K, fderiv ℝ (fun y ↦ deriv (fun t ↦ φ t y) 0) y = 0) ∧ (∀ t ∈ Ioo (-ε) ε, (∃ L : NNReal, LipschitzWith L (φ t)) ∧ ContDiff ℝ 1 (φ t)) ∧ ∃ δ B : ℝ, 0 < δ ∧ δ < ε ∧ ∃ Λ' : ℝ → Ambient n ℓ → (Ambient n ℓ →L[ℝ] Ambient n ℓ), ∀ x, Λ' 0 x = fderiv ℝ (fun y ↦ deriv (fun t ↦ φ t y) 0) x ∧ ∀ t ∈ Ioo (-δ) δ, HasDerivAt (fun s ↦ fderiv ℝ (φ s) x) (Λ' t x) t ∧ ‖fderiv ℝ (φ t) x‖ ≤ B ∧ ‖Λ' t x‖ ≤ B ∧ ∀ v, ‖v‖ ≤ B * ‖fderiv ℝ (φ t) x v‖ := by
  intro n ℓ φ ε K hφ
  -- Parts (a)–(c): `X` is `C¹` with `DX = 0` off `K`; each `φ_t` is Lipschitz and `C¹`.
  obtain ⟨hX, hDX, hslice⟩ := Submission.ts_fv_cv_first_order_regularity n ℓ φ ε K hφ
  -- `Λ'(t, x) = ∂_s Dφ_s(x)|_{s=t}` on `(-ε, ε)`, `Λ'(0, x) = DX(x)`, bounded on each `|t| < δ`.
  obtain ⟨Λ', hΛ', hΛ'B⟩ := Submission.ts_fv_cv_slice_fderiv_time_deriv n ℓ φ ε K hφ
  -- Part (d) with `δ = ε/2` and `B = max B₁ B₂`, where `B₁` bounds `Dφ_t` and its inverse and
  -- `B₂` bounds `Λ'` on `|t| < ε/2`.
  have hδ : 0 < ε / 2 := half_pos hφ.pos
  have hδε : ε / 2 < ε := half_lt_self hφ.pos
  obtain ⟨B₁, hB₁⟩ := Submission.ts_fv_cv_slice_fderiv_bounds n ℓ φ ε K hφ (ε / 2) hδ hδε
  obtain ⟨B₂, hB₂⟩ := hΛ'B (ε / 2) hδ hδε
  refine ⟨hX, hDX, hslice, ε / 2, max B₁ B₂, hδ, hδε, Λ', fun x ↦ ⟨(hΛ' x).1, fun t ht ↦ ?_⟩⟩
  have htε : t ∈ Ioo (-ε) ε := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨hb, hv⟩ := hB₁ x t ht
  exact ⟨(hΛ' x).2 t htε, hb.trans (le_max_left _ _), (hB₂ x t ht).trans (le_max_right _ _),
    fun v ↦ (hv v).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))⟩
/-- **Tangential Jacobian as a Gram determinant.** Let `P ⊆ ℝᴺ` be a subspace with orthogonal
projection `p` and orthonormal basis `b₁, …, b_k`, and let `Λ : ℝᴺ → ℝᴺ` be linear. Then
`det (⟪Λ p eᵢ, Λ p eⱼ⟫ + ⟪eᵢ - p eᵢ, eⱼ - p eⱼ⟫)ᵢⱼ = det (⟪Λ b_a, Λ b_c⟫)_{a c}`. With
`B i a = ⟪eᵢ, b_a⟫` the left matrix is `1 + B (G Bᵀ - Bᵀ)`, `G` the right Gram matrix, and
`Bᵀ B = 1`, so `det (1 + X W) = det (1 + W X)` gives `det (1 + G - 1) = det G`. -/
theorem Submission.ts_fv_det_tangential_gram_eq : ∀ (N k : ℕ) (P : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (b : OrthonormalBasis (Fin k) ℝ P) (Λ : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)), Matrix.det (Matrix.of fun i j : Fin N ↦ inner ℝ (Λ (P.starProjection (EuclideanSpace.single i (1 : ℝ)))) (Λ (P.starProjection (EuclideanSpace.single j (1 : ℝ)))) + inner ℝ (EuclideanSpace.single i (1 : ℝ) - P.starProjection (EuclideanSpace.single i (1 : ℝ))) (EuclideanSpace.single j (1 : ℝ) - P.starProjection (EuclideanSpace.single j (1 : ℝ)))) = Matrix.det (Matrix.of fun a c : Fin k ↦ inner ℝ (Λ (b a)) (Λ (b c))) := by
  intro N k P b Λ
  -- `B i a = ⟪eᵢ, b_a⟫` is the `i`-th coordinate of `b_a`; `G` is the Gram matrix of `Λ b`
  set B : Matrix (Fin N) (Fin k) ℝ :=
    Matrix.of fun i a ↦ inner ℝ (EuclideanSpace.single i (1 : ℝ)) (b a : EuclideanSpace ℝ (Fin N))
  set G : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun a c ↦ inner ℝ (Λ (b a)) (Λ (b c))
  have hBl : ∀ i a, inner ℝ (EuclideanSpace.single i (1 : ℝ)) (b a : EuclideanSpace ℝ (Fin N)) =
      B i a := fun _ _ ↦ rfl
  have hBr : ∀ i a, inner ℝ (b a : EuclideanSpace ℝ (Fin N)) (EuclideanSpace.single i (1 : ℝ)) =
      B i a := fun _ _ ↦ real_inner_comm _ _
  have hG : ∀ a c, inner ℝ (Λ (b a)) (Λ (b c)) = G a c := fun _ _ ↦ rfl
  -- `p eᵢ = ∑ₐ B i a • b_a`
  have hp : ∀ i, P.starProjection (EuclideanSpace.single i (1 : ℝ)) =
      ∑ a, B i a • (b a : EuclideanSpace ℝ (Fin N)) := fun i ↦ by
    rw [b.starProjection_eq_sum_rankOne, sum_apply]
    exact Finset.sum_congr rfl fun a _ ↦ by rw [InnerProductSpace.rankOne_apply, hBr]
  -- `⟪b_a, b_c⟫ = δ_ac` and `⟪eᵢ, eⱼ⟫ = δᵢⱼ`
  have hb : ∀ a c, inner ℝ (b a : EuclideanSpace ℝ (Fin N)) (b c : EuclideanSpace ℝ (Fin N)) =
      if a = c then (1 : ℝ) else 0 := fun a c ↦ by
    rw [← Submodule.coe_inner]
    exact orthonormal_iff_ite.mp b.orthonormal a c
  have he : ∀ i j, inner ℝ (EuclideanSpace.single i (1 : ℝ))
      (EuclideanSpace.single j (1 : ℝ) : EuclideanSpace ℝ (Fin N)) = if i = j then (1 : ℝ) else 0 :=
    orthonormal_iff_ite.mp EuclideanSpace.orthonormal_single
  -- `Bᵀ B = 1`: Parseval in the standard basis `eᵢ` of `ℝᴺ`
  have hBB : B.transpose * B = 1 := by
    ext a c
    rw [Matrix.mul_apply, Matrix.one_apply, ← hb,
      ← (EuclideanSpace.basisFun (Fin N) ℝ).sum_inner_mul_inner]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [EuclideanSpace.basisFun_apply, hBr, hBl]; rfl
  -- entrywise, the left matrix is `B G Bᵀ + (1 - B Bᵀ) = 1 + B (G Bᵀ - Bᵀ)`
  have hS : (Matrix.of fun i j : Fin N ↦
      inner ℝ (Λ (P.starProjection (EuclideanSpace.single i (1 : ℝ))))
        (Λ (P.starProjection (EuclideanSpace.single j (1 : ℝ)))) +
      inner ℝ (EuclideanSpace.single i (1 : ℝ) - P.starProjection (EuclideanSpace.single i (1 : ℝ)))
        (EuclideanSpace.single j (1 : ℝ) - P.starProjection (EuclideanSpace.single j (1 : ℝ)))) =
      1 + B * (G * B.transpose - B.transpose) := by
    ext i j
    rw [Matrix.of_apply, hp i, hp j]
    simp only [map_sum, map_smul, inner_sum, sum_inner, real_inner_smul_left,
      real_inner_smul_right, inner_sub_left, inner_sub_right, hb, he, hBl, hBr, hG,
      Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply, Matrix.sub_apply,
      Matrix.transpose_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true, sub_self, Finset.sum_const_zero, sub_zero, mul_sub, Finset.mul_sum,
      Finset.sum_sub_distrib]
    have hswap : ∑ c, ∑ a, B j c * (B i a * G a c) = ∑ a, ∑ c, B i a * (G a c * B j c) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
    rw [hswap]
    ring
  -- Weinstein–Aronszajn `det (1 + X W) = det (1 + W X)`, then `Bᵀ B = 1`
  rw [hS, Matrix.det_one_add_mul_comm, Matrix.sub_mul, Matrix.mul_assoc, hBB, Matrix.mul_one,
    add_sub_cancel]

/-- **Area formula on one piece.** Let `F : ℝⁿ → ℝ^{n+ℓ}` be differentiable and injective on the
Borel set `C`, let `A ⊆ F(C)` be Borel, let `f` be injective and differentiable on `A`, and let
`P(F v) = range DF(v)` whenever `v ∈ C` and `F v ∈ A` (`F` and `f` are also Lipschitz). Then
`∫_{f(A)} w dHⁿ = ∫_A jac(Df(y), P(y)) · w(f(y)) dHⁿ(y)` for every weight `w`, where
`jac(Λ, Q) = √det (⟪Λ p eᵢ, Λ p eⱼ⟫ + ⟪eᵢ - p eᵢ, eⱼ - p eⱼ⟫)` with `p` the projection onto `Q`.
Both sides are computed on `B = C ∩ F⁻¹(A)` by the area formula for `f ∘ F` and for `F`, whose
Jacobians satisfy `J(f ∘ F) = (jac ∘ F) · J F`. -/
theorem Submission.ts_fv_piece_image_area_formula : ∀ (n ℓ : ℕ) (C : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → Ambient n ℓ) (f : Ambient n ℓ → Ambient n ℓ) (A : Set (Ambient n ℓ)) (P : Ambient n ℓ → Submodule ℝ (Ambient n ℓ)) (w : Ambient n ℓ → ℝ≥0∞), MeasurableSet C → (∃ L : NNReal, LipschitzWith L F) → (∀ v ∈ C, DifferentiableAt ℝ F v) → Set.InjOn F C → (∃ L : NNReal, LipschitzWith L f) → Set.InjOn f A → (∀ y ∈ A, DifferentiableAt ℝ f y) → MeasurableSet A → A ⊆ F '' C → (∀ v ∈ C, F v ∈ A → P (F v) = LinearMap.range (fderiv ℝ F v).toLinearMap) → ∫⁻ y in f '' A, w y ∂μHE[n] = ∫⁻ y in A, ENNReal.ofReal (Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (n + ℓ) ↦ inner ℝ (fderiv ℝ f y ((P y).starProjection (EuclideanSpace.single i (1 : ℝ)))) (fderiv ℝ f y ((P y).starProjection (EuclideanSpace.single j (1 : ℝ)))) + inner ℝ (EuclideanSpace.single i (1 : ℝ) - (P y).starProjection (EuclideanSpace.single i (1 : ℝ))) (EuclideanSpace.single j (1 : ℝ) - (P y).starProjection (EuclideanSpace.single j (1 : ℝ)))))) * w (f y) ∂μHE[n] := by
  intro n ℓ C F f A P w hC hFL hFd hFi _ hfi hfd hA hAC hP
  classical
  have hvol : (μHE[n] : Measure (EuclideanSpace ℝ (Fin n))) = volume :=
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume n
  /- `Jl A = √det (⟪A eᵢ, A eⱼ⟫)` is the Gram-determinant Jacobian of a linear map
  `A : ℝⁿ → ℝ^{n+ℓ}`; it is continuous and nonnegative. -/
  obtain ⟨Jl, hJl⟩ : ∃ Jl : (EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ) → ℝ, Jl = fun A =>
      Real.sqrt (Matrix.det (Matrix.of fun i j : Fin n =>
        inner ℝ (A (EuclideanSpace.basisFun (Fin n) ℝ i))
          (A (EuclideanSpace.basisFun (Fin n) ℝ j)))) :=
    ⟨_, rfl⟩
  have hJl_cont : Continuous Jl := by
    rw [hJl]
    fun_prop
  have hJl_nonneg : ∀ A, 0 ≤ Jl A := fun A => by
    rw [hJl]
    exact Real.sqrt_nonneg _
  /- An injective `A` factors as an isometric embedding after an endomorphism `T` of `ℝⁿ`
  (so `‖A z‖ = ‖T z‖`), and then `Jl A = |det T|` since the Gram matrix of `A` is `Mᵀ M`. -/
  have LA1 : ∀ A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ, Function.Injective A →
      ∃ T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n), (∀ z, ‖A z‖ = ‖T z‖) ∧
        Jl A = |LinearMap.det T| := by
    intro A hA
    set A' : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] Ambient n ℓ :=
      (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] Ambient n ℓ)
    have hA' : Function.Injective A' := hA
    have hW : Module.finrank ℝ (LinearMap.range A') = n := by
      rw [LinearMap.finrank_range_of_inj hA', finrank_euclideanSpace_fin]
    let b := (stdOrthonormalBasis ℝ (LinearMap.range A')).reindex (finCongr hW)
    let T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
      b.repr.toLinearEquiv.toLinearMap ∘ₗ A'.rangeRestrict
    have hTapp : ∀ z, T z = b.repr (A'.rangeRestrict z) := fun z => rfl
    have hT : ∀ z, ‖A z‖ = ‖T z‖ := by
      intro z
      rw [hTapp, LinearIsometryEquiv.norm_map]
      rfl
    have hinner : ∀ x y, inner ℝ (A x) (A y) = inner ℝ (T x) (T y) := by
      intro x y
      rw [hTapp, hTapp, LinearIsometryEquiv.inner_map_map, Submodule.coe_inner]
      rfl
    refine ⟨T, hT, ?_⟩
    have hG : (Matrix.of fun i j : Fin n => inner ℝ (A (EuclideanSpace.basisFun (Fin n) ℝ i))
        (A (EuclideanSpace.basisFun (Fin n) ℝ j))) =
        (LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
          (EuclideanSpace.basisFun (Fin n) ℝ).toBasis T).transpose *
        LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
          (EuclideanSpace.basisFun (Fin n) ℝ).toBasis T := by
      ext i j
      simp only [Matrix.of_apply, hinner, Matrix.mul_apply, Matrix.transpose_apply,
        LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
        OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr, PiLp.inner_apply,
        RCLike.inner_apply, conj_trivial]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hJl]
    simp only
    rw [hG, Matrix.det_mul, Matrix.det_transpose, Real.sqrt_mul_self_eq_abs, LinearMap.det_toMatrix]
  /- A non-injective `A` has a kernel vector, which is a kernel vector of its Gram matrix. -/
  have hker : ∀ A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ, ¬ Function.Injective A →
      ∃ x, x ≠ 0 ∧ A x = 0 := by
    intro A hA
    by_contra h
    push Not at h
    apply hA
    intro a b hab
    by_contra hne
    exact h (a - b) (sub_ne_zero.mpr hne) (by rw [map_sub, hab, sub_self])
  have LA2 : ∀ A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ, ¬ Function.Injective A →
      Jl A = 0 := by
    intro A hA
    obtain ⟨x, hx0, hAx⟩ := hker A hA
    have hdet : Matrix.det (Matrix.of fun i j : Fin n =>
        inner ℝ (A (EuclideanSpace.basisFun (Fin n) ℝ i))
          (A (EuclideanSpace.basisFun (Fin n) ℝ j))) = 0 := by
      rw [← Matrix.exists_mulVec_eq_zero_iff]
      refine ⟨x.ofLp, fun h => hx0 ?_, ?_⟩
      · ext i
        simp [h]
      · ext i
        have hx : x = ∑ j, x j • EuclideanSpace.basisFun (Fin n) ℝ j := by
          conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr x]
          simp
        have key : ∑ j, inner ℝ (A (EuclideanSpace.basisFun (Fin n) ℝ i))
            (A (EuclideanSpace.basisFun (Fin n) ℝ j)) * x j =
            inner ℝ (A (EuclideanSpace.basisFun (Fin n) ℝ i)) (A x) := by
          conv_rhs => rw [hx]
          rw [map_sum, inner_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_smul, inner_smul_right, mul_comm]
        simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
        rw [key, hAx, inner_zero_right]
    rw [hJl]
    simp only
    rw [hdet, Real.sqrt_zero]
  have LA3 : ∀ A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ, Function.Injective A → 0 < Jl A := by
    intro A hA
    obtain ⟨T, hT, hJ⟩ := LA1 A hA
    have hTinj : Function.Injective T := by
      intro a b hab
      apply hA
      rw [← sub_eq_zero, ← map_sub, ← norm_eq_zero, hT, map_sub, hab, sub_self, norm_zero]
    rw [hJ, abs_pos]
    intro h0
    exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp h0) (LinearMap.ker_eq_bot.mpr hTinj)
  /- Zero-Jacobian pieces: if `A` has a unit kernel vector `u`, then for `G` close to `A`,
  `G = G' ∘ M_θ` with `M_θ` the contraction by `θ` along `u` and `G'` Lipschitz, so
  `Hⁿ(G(P)) ≤ (‖A‖+1)ⁿ |det M_θ| Lⁿ(P)`, which is small since `det M_θ → det M_0 = 0`. -/
  have B3 : ∀ A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ, ¬ Function.Injective A →
      ∀ η : NNReal, 0 < η → ∃ δ : NNReal, 0 < δ ∧
        ∀ (G : EuclideanSpace ℝ (Fin n) → Ambient n ℓ) (P : Set (EuclideanSpace ℝ (Fin n))),
          ApproximatesLinearOn G A P δ →
            (μHE[n] : Measure (Ambient n ℓ)) (G '' P) ≤ η * volume P := by
    intro A hA η hη
    obtain ⟨x, hx0, hAx⟩ := hker A hA
    set u : EuclideanSpace ℝ (Fin n) := ‖x‖⁻¹ • x with hu_def
    have hu1 : ‖u‖ = 1 := by
      rw [hu_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx0)]
    have hAu : A u = 0 := by rw [hu_def, map_smul, hAx, smul_zero]
    let M : ℝ → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) := fun θ =>
      ContinuousLinearMap.id ℝ _ - (1 - θ) • (innerSL ℝ u).smulRight u
    have hMapp : ∀ θ z, M θ z = z - ((1 - θ) * inner ℝ u z) • u := by
      intro θ z
      simp [M, smul_smul]
    have hAM : ∀ θ z, A (M θ z) = A z := by
      intro θ z
      rw [hMapp, map_sub, map_smul, hAu, smul_zero, sub_zero]
    have hMnorm : ∀ θ : ℝ, 0 < θ → θ ≤ 1 → ∀ z, θ * ‖z‖ ≤ ‖M θ z‖ := by
      intro θ h0 h1 z
      have h2 : ‖M θ z‖ ^ 2 = ‖z‖ ^ 2 - (1 - θ ^ 2) * inner ℝ u z ^ 2 := by
        rw [hMapp, @norm_sub_sq_real, norm_smul, inner_smul_right, hu1, Real.norm_eq_abs, mul_one,
          sq_abs, real_inner_comm z u]
        ring
      have hcs : inner ℝ u z ^ 2 ≤ ‖z‖ ^ 2 := by
        have h := abs_real_inner_le_norm u z
        rw [hu1, one_mul] at h
        have := sq_le_sq' (neg_le_of_abs_le h) (le_of_abs_le h)
        simpa using this
      have h3 : (θ * ‖z‖) ^ 2 ≤ ‖M θ z‖ ^ 2 := by
        have h4 : (1 - θ ^ 2) * inner ℝ u z ^ 2 ≤ (1 - θ ^ 2) * ‖z‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hcs (sub_nonneg.mpr (pow_le_one₀ h0.le h1))
        rw [h2, show (θ * ‖z‖) ^ 2 = ‖z‖ ^ 2 - (1 - θ ^ 2) * ‖z‖ ^ 2 by ring]
        exact sub_le_sub_left h4 _
      exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp h3
    have hdet0 : (M 0).det = 0 := by
      have hM0u : M 0 u = 0 := by
        rw [hMapp, real_inner_self_eq_norm_sq, hu1]
        simp
      rw [ContinuousLinearMap.det, LinearMap.det_eq_zero_iff_ker_ne_bot]
      intro hker0
      have hmem : u ∈ LinearMap.ker (M 0).toLinearMap := LinearMap.mem_ker.mpr hM0u
      rw [hker0, Submodule.mem_bot] at hmem
      rw [hmem, norm_zero] at hu1
      exact zero_ne_one hu1
    have hcontM : Continuous fun θ : ℝ => (M θ).det :=
      ContinuousLinearMap.continuous_det.comp (by fun_prop)
    have hlim : Tendsto (fun θ : ℝ => ((‖A‖₊ : ℝ) + 1) ^ n * |(M θ).det|) (𝓝 0) (𝓝 0) := by
      have h := (hcontM.tendsto 0).abs.const_mul (((‖A‖₊ : ℝ) + 1) ^ n)
      rwa [hdet0, abs_zero, mul_zero] at h
    obtain ⟨θ, hθ, hθ0, hθ1⟩ :
        ∃ θ : ℝ, ((‖A‖₊ : ℝ) + 1) ^ n * |(M θ).det| < η ∧ 0 < θ ∧ θ ≤ 1 := by
      have h1 : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ((‖A‖₊ : ℝ) + 1) ^ n * |(M θ).det| < η :=
        nhdsWithin_le_nhds (hlim.eventually (gt_mem_nhds (show (0 : ℝ) < η from hη)))
      have h2 : ∀ᶠ θ in 𝓝[>] (0 : ℝ), 0 < θ ∧ θ ≤ 1 := by
        filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with θ hθ
        exact ⟨hθ.1, hθ.2.le⟩
      exact (h1.and h2).exists.imp fun θ h => ⟨h.1, h.2⟩
    refine ⟨⟨θ, hθ0.le⟩, hθ0, fun G P hGP => ?_⟩
    have hMinj : Function.Injective (M θ).toLinearMap := by
      intro a b hab
      have h := hMnorm θ hθ0 hθ1 (a - b)
      have hab' : M θ (a - b) = 0 := by
        rw [map_sub]
        exact sub_eq_zero.mpr hab
      rw [hab', norm_zero, ← mul_zero θ] at h
      have : ‖a - b‖ = 0 := le_antisymm (le_of_mul_le_mul_left h hθ0) (norm_nonneg _)
      exact sub_eq_zero.mp (norm_eq_zero.mp this)
    let Me := LinearEquiv.ofInjectiveEndo (M θ).toLinearMap hMinj
    have hMe : ∀ z, Me.symm (M θ z) = z := fun z => Me.symm_apply_apply z
    let G' := G ∘ Me.symm
    have hG' : ∀ z, G' (M θ z) = G z := fun z => by simp only [G', Function.comp_apply, hMe]
    have himg : G '' P = G' '' (M θ '' P) := by
      rw [Set.image_image]
      exact Set.image_congr fun z _ => (hG' z).symm
    have hLip : LipschitzOnWith (‖A‖₊ + 1) G' (M θ '' P) := by
      apply LipschitzOnWith.of_dist_le_mul
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [hG', hG', dist_eq_norm, dist_eq_norm]
      have happ : ‖G x - G y - A (x - y)‖ ≤ θ * ‖x - y‖ := hGP x hx y hy
      have hA1 : ‖A (x - y)‖ ≤ ‖A‖ * ‖M θ x - M θ y‖ := by
        rw [← hAM θ (x - y), map_sub]
        exact A.le_opNorm _
      have hA2 : θ * ‖x - y‖ ≤ ‖M θ x - M θ y‖ := by
        rw [← map_sub]
        exact hMnorm θ hθ0 hθ1 (x - y)
      have htri : ‖G x - G y‖ ≤ ‖G x - G y - A (x - y)‖ + ‖A (x - y)‖ := by
        have := norm_add_le (G x - G y - A (x - y)) (A (x - y))
        rwa [sub_add_cancel] at this
      push_cast
      rw [add_mul, one_mul]
      linarith only [htri, happ, hA1, hA2]
    have hdetθ : ((‖A‖₊ + 1 : NNReal) : ℝ≥0∞) ^ n * ENNReal.ofReal |(M θ).det| ≤ η := by
      have h := ENNReal.ofReal_le_ofReal hθ.le
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
        ENNReal.ofReal_coe_nnreal] at h
      convert h using 3
      rw [← ENNReal.ofReal_coe_nnreal]
      push_cast
      rfl
    calc (μHE[n] : Measure (Ambient n ℓ)) (G '' P) = μHE[n] (G' '' (M θ '' P)) := by rw [himg]
      _ ≤ ((‖A‖₊ + 1 : NNReal) : ℝ≥0∞) ^ n * μHE[n] (M θ '' P) :=
        Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hLip
      _ = ((‖A‖₊ + 1 : NNReal) : ℝ≥0∞) ^ n * (ENNReal.ofReal |(M θ).det| * volume P) := by
        rw [hvol]
        congr 1
        exact Measure.addHaar_image_linearMap volume (M θ).toLinearMap P
      _ ≤ η * volume P := by
        rw [← mul_assoc]
        exact mul_le_mul_left hdetθ _
  /- Injective pieces: with `‖A z‖ = ‖T z‖` and `‖z‖ ≤ κ ‖T z‖`, a map `G` that is
  `δ`-close to `A` on `P` satisfies `G = G' ∘ T` with `G'` `(1+δκ)`-Lipschitz, and (if `G` is
  injective on `P`) `T = H ∘ G` with `H` `(1-δκ)⁻¹`-Lipschitz; `Hⁿ(T(P)) = Jl A · Lⁿ(P)`. -/
  have B12 : ∀ A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ, Function.Injective A →
      ∀ c : ℝ, 1 < c → ∃ δ : NNReal, 0 < δ ∧
        ∀ (G : EuclideanSpace ℝ (Fin n) → Ambient n ℓ) (P : Set (EuclideanSpace ℝ (Fin n))),
          ApproximatesLinearOn G A P δ →
          (μHE[n] : Measure (Ambient n ℓ)) (G '' P) ≤
              ENNReal.ofReal c * (ENNReal.ofReal (Jl A) * volume P) ∧
          (Set.InjOn G P → ENNReal.ofReal (Jl A) * volume P ≤
              ENNReal.ofReal c * (μHE[n] : Measure (Ambient n ℓ)) (G '' P)) := by
    intro A hA c hc
    obtain ⟨T, hT, hjT⟩ := LA1 A hA
    have hTinj : Function.Injective T := by
      intro a b hab
      apply hA
      rw [← sub_eq_zero, ← map_sub, ← norm_eq_zero, hT, map_sub, hab, sub_self, norm_zero]
    have hTimg : ∀ P : Set (EuclideanSpace ℝ (Fin n)),
        (μHE[n] : Measure (EuclideanSpace ℝ (Fin n))) (T '' P) =
          ENNReal.ofReal (Jl A) * volume P := by
      intro P
      rw [hvol, hjT]
      exact Measure.addHaar_image_linearMap volume T P
    obtain ⟨κ, hκ, hantiT⟩ := LinearMap.exists_antilipschitzWith T (LinearMap.ker_eq_bot.mpr hTinj)
    have hκT : ∀ x y, ‖x - y‖ ≤ κ * ‖T x - T y‖ := by
      intro x y
      have := hantiT.le_mul_dist x y
      rwa [dist_eq_norm, dist_eq_norm] at this
    obtain ⟨t, ht0, ht1, htc1, htc2⟩ :
        ∃ t : ℝ, 0 < t ∧ t < 1 ∧ (1 + t) ^ n < c ∧ ((1 - t)⁻¹) ^ n < c := by
      have h1 : Tendsto (fun t : ℝ => (1 + t) ^ n) (𝓝 0) (𝓝 1) := by
        have : Continuous (fun t : ℝ => (1 + t) ^ n) := by fun_prop
        simpa using this.tendsto 0
      have h2 : Tendsto (fun t : ℝ => ((1 - t)⁻¹) ^ n) (𝓝 0) (𝓝 1) := by
        have : ContinuousAt (fun t : ℝ => ((1 - t)⁻¹) ^ n) 0 :=
          ((continuousAt_const.sub continuousAt_id).inv₀ (by norm_num)).pow n
        simpa using this.tendsto
      have e1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), (1 + t) ^ n < c :=
        nhdsWithin_le_nhds (h1.eventually (gt_mem_nhds hc))
      have e2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), ((1 - t)⁻¹) ^ n < c :=
        nhdsWithin_le_nhds (h2.eventually (gt_mem_nhds hc))
      have e3 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t < 1 := by
        filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
        exact ⟨ht.1, ht.2⟩
      obtain ⟨t, h1t, h2t, h3t⟩ := (e1.and (e2.and e3)).exists
      exact ⟨t, h3t.1, h3t.2, h1t, h2t⟩
    set δ : NNReal := Real.toNNReal (t / κ) with hδ
    have hδκ : (δ : ℝ) * κ = t := by
      rw [hδ, Real.coe_toNNReal _ (by positivity)]
      field_simp
    refine ⟨δ, by rw [hδ]; exact Real.toNNReal_pos.mpr (by positivity), fun G P hGP => ?_⟩
    have happ : ∀ x ∈ P, ∀ y ∈ P, ‖G x - G y - A (x - y)‖ ≤ t * ‖T x - T y‖ := by
      intro x hx y hy
      calc ‖G x - G y - A (x - y)‖ ≤ δ * ‖x - y‖ := hGP x hx y hy
        _ ≤ δ * (κ * ‖T x - T y‖) := mul_le_mul_of_nonneg_left (hκT x y) δ.2
        _ = t * ‖T x - T y‖ := by rw [← mul_assoc, hδκ]
    have hAT : ∀ x y, ‖A (x - y)‖ = ‖T x - T y‖ := by
      intro x y
      rw [hT, map_sub]
    constructor
    · let Te := LinearEquiv.ofInjectiveEndo T hTinj
      let G' := G ∘ Te.symm
      have hG' : ∀ z, G' (T z) = G z := fun z => by
        simp only [G', Function.comp_apply]
        exact congrArg G (Te.symm_apply_apply z)
      have himg : G '' P = G' '' (T '' P) := by
        rw [Set.image_image]
        exact Set.image_congr fun z _ => (hG' z).symm
      have hLip : LipschitzOnWith (Real.toNNReal (1 + t)) G' (T '' P) := by
        apply LipschitzOnWith.of_dist_le_mul
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        rw [hG', hG', dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
        have h1 := happ x hx y hy
        have htri : ‖G x - G y‖ ≤ ‖G x - G y - A (x - y)‖ + ‖A (x - y)‖ := by
          have := norm_add_le (G x - G y - A (x - y)) (A (x - y))
          rwa [sub_add_cancel] at this
        rw [hAT] at htri
        rw [add_mul, one_mul]
        linarith only [h1, htri]
      calc (μHE[n] : Measure (Ambient n ℓ)) (G '' P) = μHE[n] (G' '' (T '' P)) := by rw [himg]
        _ ≤ ((Real.toNNReal (1 + t) : NNReal) : ℝ≥0∞) ^ n * μHE[n] (T '' P) :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hLip
        _ ≤ ENNReal.ofReal c * (ENNReal.ofReal (Jl A) * volume P) := by
          rw [hTimg]
          refine mul_le_mul' ?_ le_rfl
          rw [← ENNReal.ofReal.eq_def, ← ENNReal.ofReal_pow (by positivity)]
          exact ENNReal.ofReal_le_ofReal htc1.le
    · intro hinjG
      let H : Ambient n ℓ → EuclideanSpace ℝ (Fin n) := T ∘ Function.invFunOn G P
      have hH : ∀ z ∈ P, H (G z) = T z := fun z hz => by
        simp only [H, Function.comp_apply]
        rw [hinjG.leftInvOn_invFunOn hz]
      have himg : T '' P = H '' (G '' P) := by
        rw [Set.image_image]
        exact Set.image_congr fun z hz => (hH z hz).symm
      have h1t : 0 < 1 - t := sub_pos.mpr ht1
      have hLip : LipschitzOnWith (Real.toNNReal ((1 - t)⁻¹)) H (G '' P) := by
        apply LipschitzOnWith.of_dist_le_mul
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        rw [hH x hx, hH y hy, dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
        have h1 := happ x hx y hy
        have htri : ‖A (x - y)‖ ≤ ‖G x - G y‖ + ‖G x - G y - A (x - y)‖ := by
          have := norm_sub_le (G x - G y) (G x - G y - A (x - y))
          rwa [sub_sub_cancel] at this
        rw [hAT] at htri
        rw [le_inv_mul_iff₀ h1t, sub_mul, one_mul]
        linarith only [h1, htri]
      calc ENNReal.ofReal (Jl A) * volume P = μHE[n] (T '' P) := (hTimg P).symm
        _ = μHE[n] (H '' (G '' P)) := by rw [himg]
        _ ≤ ((Real.toNNReal ((1 - t)⁻¹) : NNReal) : ℝ≥0∞) ^ n * μHE[n] (G '' P) :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hLip
        _ ≤ ENNReal.ofReal c * (μHE[n] : Measure (Ambient n ℓ)) (G '' P) := by
          refine mul_le_mul' ?_ le_rfl
          rw [← ENNReal.ofReal.eq_def, ← ENNReal.ofReal_pow (by positivity)]
          exact ENNReal.ofReal_le_ofReal htc2.le
  /- Two limit principles in `ℝ≥0∞`. -/
  have zero_of : ∀ X Y : ℝ≥0∞, Y ≠ ⊤ → (∀ η : NNReal, 0 < η → X ≤ η * Y) → X = 0 := by
    intro X Y hY h
    have ht : Tendsto (fun η : NNReal => (η : ℝ≥0∞) * Y) (𝓝[>] 0) (𝓝 0) := by
      have h0 : Tendsto (fun η : NNReal => (η : ℝ≥0∞)) (𝓝[>] 0) (𝓝 0) :=
        (ENNReal.continuous_coe.tendsto 0).mono_left nhdsWithin_le_nhds |>.trans (by simp)
      simpa using ENNReal.Tendsto.mul_const h0 (Or.inr hY)
    exact le_antisymm (ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun η hη => h η hη))
      zero_le
  have lim_le : ∀ X Y : ℝ≥0∞,
      (∀ c : ℝ, 1 < c → X ≤ ENNReal.ofReal c * (ENNReal.ofReal c * Y)) → X ≤ Y := by
    intro X Y h
    rcases eq_or_ne Y ⊤ with hY | hY
    · rw [hY]
      exact le_top
    have ht : Tendsto (fun c : ℝ => ENNReal.ofReal c * (ENNReal.ofReal c * Y)) (𝓝[>] 1) (𝓝 Y) := by
      have h1 : Tendsto (fun c : ℝ => ENNReal.ofReal c) (𝓝[>] 1) (𝓝 1) := by
        have := ENNReal.continuous_ofReal.tendsto (1 : ℝ)
        rw [ENNReal.ofReal_one] at this
        exact this.mono_left nhdsWithin_le_nhds
      have h2 := ENNReal.Tendsto.mul h1 (Or.inl one_ne_zero)
        (ENNReal.Tendsto.mul_const h1 (Or.inr hY)) (Or.inr ENNReal.one_ne_top)
      simpa using h2
    exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun c hc => h c hc)
  /- (Z) Images of sets where `Jl ∘ DΦ = 0` are `Hⁿ`-null: partition into pieces where `Φ` is
  close to a non-injective `DΦ(y)` and apply `B3` on bounded parts. -/
  have hZ : ∀ (Φ : EuclideanSpace ℝ (Fin n) → Ambient n ℓ) (s : Set (EuclideanSpace ℝ (Fin n))),
      MeasurableSet s → (∀ x ∈ s, DifferentiableAt ℝ Φ x) → (∀ x ∈ s, Jl (fderiv ℝ Φ x) = 0) →
      (μHE[n] : Measure (Ambient n ℓ)) (Φ '' s) = 0 := by
    intro Φ s hs hsd hs0
    have key : ∀ m : ℕ, (μHE[n] : Measure (Ambient n ℓ)) (Φ '' (s ∩ ball 0 m)) = 0 := by
      intro m
      have hs'm : MeasurableSet (s ∩ ball (0 : EuclideanSpace ℝ (Fin n)) m) :=
        hs.inter measurableSet_ball
      apply zero_of _ (volume (ball (0 : EuclideanSpace ℝ (Fin n)) m)) measure_ball_lt_top.ne
      intro η hη
      let r : (EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ) → NNReal := fun A =>
        if h : Function.Injective A then 1 else (B3 A h η hη).choose
      have rpos : ∀ A, r A ≠ 0 := by
        intro A
        by_cases h : Function.Injective A
        · simp only [r, h, dite_true]
          exact one_ne_zero
        · simp only [r, h, dite_false]
          exact (B3 A h η hη).choose_spec.1.ne'
      obtain ⟨t, A, htd, htm, hcov, happ, hAy⟩ :=
        exists_partition_approximatesLinearOn_of_hasFDerivWithinAt Φ
          (s ∩ ball (0 : EuclideanSpace ℝ (Fin n)) m) (fderiv ℝ Φ)
          (fun x hx => (hsd x hx.1).hasFDerivAt.hasFDerivWithinAt) r rpos
      rcases (s ∩ ball (0 : EuclideanSpace ℝ (Fin n)) m).eq_empty_or_nonempty with he | hne
      · rw [he, image_empty, measure_empty]
        exact zero_le
      have hAni : ∀ k, ¬ Function.Injective (A k) := by
        intro k hk
        obtain ⟨y, hy, hAk⟩ := hAy hne k
        have h1 := LA3 _ hk
        rw [hAk, hs0 y hy.1] at h1
        exact lt_irrefl _ h1
      have hpiece : ∀ k, (μHE[n] : Measure (Ambient n ℓ)) (Φ '' (s ∩ ball 0 m ∩ t k)) ≤
          η * volume (s ∩ ball (0 : EuclideanSpace ℝ (Fin n)) m ∩ t k) := by
        intro k
        apply (B3 (A k) (hAni k) η hη).choose_spec.2 Φ
        have := happ k
        simp only [r, hAni k, dite_false] at this
        exact this
      calc (μHE[n] : Measure (Ambient n ℓ)) (Φ '' (s ∩ ball 0 m))
          ≤ μHE[n] (⋃ k, Φ '' (s ∩ ball 0 m ∩ t k)) := by
            apply measure_mono
            rw [← image_iUnion, ← inter_iUnion]
            exact image_mono (subset_inter subset_rfl hcov)
        _ ≤ ∑' k, μHE[n] (Φ '' (s ∩ ball 0 m ∩ t k)) := measure_iUnion_le _
        _ ≤ ∑' k, (η : ℝ≥0∞) * volume (s ∩ ball (0 : EuclideanSpace ℝ (Fin n)) m ∩ t k) :=
            ENNReal.tsum_le_tsum hpiece
        _ = η * volume (⋃ k, s ∩ ball (0 : EuclideanSpace ℝ (Fin n)) m ∩ t k) := by
            rw [ENNReal.tsum_mul_left, measure_iUnion]
            · exact htd.mono fun i j h => h.mono inter_subset_right inter_subset_right
            · exact fun k => hs'm.inter (htm k)
        _ ≤ η * volume (ball (0 : EuclideanSpace ℝ (Fin n)) m) :=
            mul_le_mul' le_rfl
              (measure_mono (iUnion_subset fun k => inter_subset_left.trans inter_subset_right))
    have hU : Φ '' s = ⋃ m : ℕ, Φ '' (s ∩ ball 0 m) := by
      rw [← image_iUnion, ← inter_iUnion, iUnion_ball_nat, inter_univ]
    rw [hU]
    exact measure_iUnion_null key
  /- (Pos) Where `Φ` is injective and `J = Jl ∘ DΦ > 0`, `Hⁿ(Φ(s)) = ∫_s J`: for `c > 1` split `s`
  into the level sets `c^k ≤ J < c^{k+1}` (`k ∈ ℤ`), partition each into pieces where `Φ` is
  close to an injective `DΦ(y)`, compare both sides on each piece with `B12` up to `c²`, and sum
  (the images of the pieces are disjoint and Borel by Lusin–Souslin). Then let `c → 1`. -/
  have hPos : ∀ (Φ : EuclideanSpace ℝ (Fin n) → Ambient n ℓ) (s : Set (EuclideanSpace ℝ (Fin n))),
      MeasurableSet s → (∀ x ∈ s, DifferentiableAt ℝ Φ x) → Set.InjOn Φ s →
      (∀ x ∈ s, 0 < Jl (fderiv ℝ Φ x)) →
      (μHE[n] : Measure (Ambient n ℓ)) (Φ '' s) =
        ∫⁻ x in s, ENNReal.ofReal (Jl (fderiv ℝ Φ x)) := by
    intro Φ s hs hsd hinjs hspos
    obtain ⟨J, hJ⟩ : ∃ J : EuclideanSpace ℝ (Fin n) → ℝ, J = fun v => Jl (fderiv ℝ Φ v) :=
      ⟨_, rfl⟩
    have hJv : ∀ v, J v = Jl (fderiv ℝ Φ v) := fun v => by rw [hJ]
    have hJm : Measurable J := by
      rw [hJ]
      exact hJl_cont.measurable.comp (measurable_fderiv ℝ Φ)
    simp only [← hJv] at hspos ⊢
    have hΦc : ContinuousOn Φ s := fun x hx => (hsd x hx).continuousAt.continuousWithinAt
    have himgd : ∀ a b : Set (EuclideanSpace ℝ (Fin n)), a ⊆ s → b ⊆ s → Disjoint a b →
        Disjoint (Φ '' a) (Φ '' b) := by
      intro a b ha hb hab
      rw [Set.disjoint_left]
      rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
      have hyx : y = x := hinjs (hb hy) (ha hx) hxy
      exact Set.disjoint_left.mp hab hx (hyx ▸ hy)
    have key : ∀ c : ℝ, 1 < c →
        (μHE[n] : Measure (Ambient n ℓ)) (Φ '' s) ≤
          ENNReal.ofReal c * (ENNReal.ofReal c * ∫⁻ x in s, ENNReal.ofReal (J x)) ∧
        ∫⁻ x in s, ENNReal.ofReal (J x) ≤
          ENNReal.ofReal c * (ENNReal.ofReal c * (μHE[n] : Measure (Ambient n ℓ)) (Φ '' s)) := by
      intro c hc
      have hc0 : 0 < c := zero_lt_one.trans hc
      let L : ℤ → Set (EuclideanSpace ℝ (Fin n)) := fun k => s ∩ J ⁻¹' Ico (c ^ k) (c ^ (k + 1))
      have hLm : ∀ k, MeasurableSet (L k) := fun k => hs.inter (hJm measurableSet_Ico)
      have hLs : ∀ k, L k ⊆ s := fun k => inter_subset_left
      have hLd : Pairwise (Function.onFun Disjoint L) := by
        intro k k' hkk'
        rw [Function.onFun, Set.disjoint_left]
        rintro x ⟨_, hx1, hx2⟩ ⟨_, hx1', hx2'⟩
        rcases lt_or_gt_of_ne hkk' with h | h
        · have : c ^ (k + 1) ≤ c ^ k' := zpow_le_zpow_right₀ hc.le (by omega)
          exact lt_irrefl _ ((this.trans hx1').trans_lt hx2)
        · have : c ^ (k' + 1) ≤ c ^ k := zpow_le_zpow_right₀ hc.le (by omega)
          exact lt_irrefl _ ((this.trans hx1).trans_lt hx2')
      have hLcov : s = ⋃ k, L k := by
        apply Subset.antisymm
        · intro x hx
          obtain ⟨k, hk⟩ := exists_mem_Ico_zpow (hspos x hx) hc
          exact mem_iUnion.mpr ⟨k, hx, hk⟩
        · exact iUnion_subset hLs
      let r : (EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ) → NNReal := fun A =>
        if h : Function.Injective A then (B12 A h c hc).choose else 1
      have rpos : ∀ A, r A ≠ 0 := by
        intro A
        by_cases h : Function.Injective A
        · simp only [r, h, dite_true]
          exact (B12 A h c hc).choose_spec.1.ne'
        · simp only [r, h, dite_false]
          exact one_ne_zero
      have hpart : ∀ k : ℤ, ∃ (t : ℕ → Set (EuclideanSpace ℝ (Fin n)))
          (A : ℕ → (EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ)),
          Pairwise (Function.onFun Disjoint t) ∧ (∀ j, MeasurableSet (t j)) ∧ L k ⊆ ⋃ j, t j ∧
          (∀ j, ApproximatesLinearOn Φ (A j) (L k ∩ t j) (r (A j))) ∧
          ((L k).Nonempty → ∀ j, ∃ y ∈ L k, A j = fderiv ℝ Φ y) := fun k =>
        exists_partition_approximatesLinearOn_of_hasFDerivWithinAt Φ (L k) (fderiv ℝ Φ)
          (fun x hx => (hsd x (hLs k hx)).hasFDerivAt.hasFDerivWithinAt) r rpos
      choose t A htd htm hcov happ hAy using hpart
      have hPm : ∀ k j, MeasurableSet (L k ∩ t k j) := fun k j => (hLm k).inter (htm k j)
      have hPs : ∀ k j, L k ∩ t k j ⊆ s := fun k j => inter_subset_left.trans (hLs k)
      have hPd : ∀ k, Pairwise (Function.onFun Disjoint fun j => L k ∩ t k j) := fun k j j' h =>
        (htd k h).mono inter_subset_right inter_subset_right
      have hLP : ∀ k, L k = ⋃ j, L k ∩ t k j := fun k => by
        rw [← inter_iUnion]
        exact (inter_eq_left.mpr (hcov k)).symm
      have hpiece : ∀ k j,
          (μHE[n] : Measure (Ambient n ℓ)) (Φ '' (L k ∩ t k j)) ≤
            ENNReal.ofReal c * (ENNReal.ofReal c * ∫⁻ x in L k ∩ t k j, ENNReal.ofReal (J x)) ∧
          ∫⁻ x in L k ∩ t k j, ENNReal.ofReal (J x) ≤
            ENNReal.ofReal c * (ENNReal.ofReal c *
              (μHE[n] : Measure (Ambient n ℓ)) (Φ '' (L k ∩ t k j))) := by
        intro k j
        rcases (L k ∩ t k j).eq_empty_or_nonempty with he | hne
        · simp [he]
        obtain ⟨y, hy, hAky⟩ := hAy k (hne.mono inter_subset_left) j
        have hJA : Jl (A k j) = J y := by rw [hAky, hJv]
        have hJy : J y ∈ Ico (c ^ k) (c ^ (k + 1)) := hy.2
        have hck : 0 < c ^ k := zpow_pos hc0 k
        have hstep : c ^ (k + 1) = c * c ^ k := by rw [zpow_add_one₀ hc0.ne', mul_comm]
        have hinjA : Function.Injective (A k j) := by
          by_contra h
          exact (hck.trans_le hJy.1).ne' (by rw [← hJA]; exact LA2 _ h)
        have happ' :
            ApproximatesLinearOn Φ (A k j) (L k ∩ t k j) (B12 (A k j) hinjA c hc).choose := by
          have := happ k j
          simp only [r, hinjA, dite_true] at this
          exact this
        have hB := (B12 (A k j) hinjA c hc).choose_spec.2 Φ (L k ∩ t k j) happ'
        have hcmp1 : ENNReal.ofReal (Jl (A k j)) * volume (L k ∩ t k j) ≤
            ENNReal.ofReal c * ∫⁻ x in L k ∩ t k j, ENNReal.ofReal (J x) := by
          calc ENNReal.ofReal (Jl (A k j)) * volume (L k ∩ t k j)
              = ∫⁻ _ in L k ∩ t k j, ENNReal.ofReal (Jl (A k j)) := (setLIntegral_const _ _).symm
            _ ≤ ∫⁻ x in L k ∩ t k j, ENNReal.ofReal c * ENNReal.ofReal (J x) := by
              apply setLIntegral_mono (hJm.ennreal_ofReal.const_mul _)
              intro x hx
              have hJx : J x ∈ Ico (c ^ k) (c ^ (k + 1)) := hx.1.2
              rw [← ENNReal.ofReal_mul hc0.le]
              apply ENNReal.ofReal_le_ofReal
              rw [hJA]
              exact (hJy.2.trans_eq hstep).le.trans (mul_le_mul_of_nonneg_left hJx.1 hc0.le)
            _ = ENNReal.ofReal c * ∫⁻ x in L k ∩ t k j, ENNReal.ofReal (J x) :=
              lintegral_const_mul _ hJm.ennreal_ofReal
        have hcmp2 : ∫⁻ x in L k ∩ t k j, ENNReal.ofReal (J x) ≤
            ENNReal.ofReal c * (ENNReal.ofReal (Jl (A k j)) * volume (L k ∩ t k j)) := by
          calc ∫⁻ x in L k ∩ t k j, ENNReal.ofReal (J x)
              ≤ ∫⁻ _ in L k ∩ t k j, ENNReal.ofReal c * ENNReal.ofReal (Jl (A k j)) := by
                apply setLIntegral_mono measurable_const
                intro x hx
                have hJx : J x ∈ Ico (c ^ k) (c ^ (k + 1)) := hx.1.2
                rw [← ENNReal.ofReal_mul hc0.le]
                apply ENNReal.ofReal_le_ofReal
                rw [hJA]
                exact (hJx.2.trans_eq hstep).le.trans (mul_le_mul_of_nonneg_left hJy.1 hc0.le)
            _ = ENNReal.ofReal c * (ENNReal.ofReal (Jl (A k j)) * volume (L k ∩ t k j)) := by
                rw [setLIntegral_const, mul_assoc]
        constructor
        · calc (μHE[n] : Measure (Ambient n ℓ)) (Φ '' (L k ∩ t k j))
              ≤ ENNReal.ofReal c * (ENNReal.ofReal (Jl (A k j)) * volume (L k ∩ t k j)) := hB.1
            _ ≤ ENNReal.ofReal c * (ENNReal.ofReal c * ∫⁻ x in L k ∩ t k j, ENNReal.ofReal (J x)) :=
              mul_le_mul' le_rfl hcmp1
        · calc ∫⁻ x in L k ∩ t k j, ENNReal.ofReal (J x)
              ≤ ENNReal.ofReal c * (ENNReal.ofReal (Jl (A k j)) * volume (L k ∩ t k j)) := hcmp2
            _ ≤ ENNReal.ofReal c * (ENNReal.ofReal c *
                (μHE[n] : Measure (Ambient n ℓ)) (Φ '' (L k ∩ t k j))) :=
              mul_le_mul' le_rfl (hB.2 (hinjs.mono (hPs k j)))
      have hFL : ∀ k, (μHE[n] : Measure (Ambient n ℓ)) (Φ '' L k) =
          ∑' j, μHE[n] (Φ '' (L k ∩ t k j)) := by
        intro k
        conv_lhs => rw [hLP k, image_iUnion]
        apply measure_iUnion
        · intro j j' hjj'
          exact himgd _ _ (hPs k j) (hPs k j') (hPd k hjj')
        · exact fun j => (hPm k j).image_of_continuousOn_injOn (hΦc.mono (hPs k j))
            (hinjs.mono (hPs k j))
      have hFs : (μHE[n] : Measure (Ambient n ℓ)) (Φ '' s) = ∑' k, μHE[n] (Φ '' L k) := by
        conv_lhs => rw [hLcov, image_iUnion]
        apply measure_iUnion
        · intro k k' hkk'
          exact himgd _ _ (hLs k) (hLs k') (hLd hkk')
        · exact fun k => (hLm k).image_of_continuousOn_injOn (hΦc.mono (hLs k))
            (hinjs.mono (hLs k))
      have hIL : ∀ k, ∫⁻ x in L k, ENNReal.ofReal (J x) =
          ∑' j, ∫⁻ x in L k ∩ t k j, ENNReal.ofReal (J x) := by
        intro k
        conv_lhs => rw [hLP k]
        exact lintegral_iUnion (hPm k) (hPd k) _
      have hIs : ∫⁻ x in s, ENNReal.ofReal (J x) = ∑' k, ∫⁻ x in L k, ENNReal.ofReal (J x) := by
        conv_lhs => rw [hLcov]
        exact lintegral_iUnion hLm hLd _
      rw [hFs, hIs]
      simp_rw [hFL, hIL]
      simp only [← ENNReal.tsum_mul_left]
      exact ⟨ENNReal.tsum_le_tsum fun k => ENNReal.tsum_le_tsum fun j => (hpiece k j).1,
        ENNReal.tsum_le_tsum fun k => ENNReal.tsum_le_tsum fun j => (hpiece k j).2⟩
    exact le_antisymm (lim_le _ _ fun c hc => (key c hc).1) (lim_le _ _ fun c hc => (key c hc).2)
  /- Area formula on Borel sets of injectivity and differentiability: `Hⁿ(Φ(s)) = ∫_s Jl ∘ DΦ`.
  Split `s` into the part where `Jl ∘ DΦ = 0` (null image by `hZ`) and where it is `> 0`. -/
  have hMI : ∀ (Φ : EuclideanSpace ℝ (Fin n) → Ambient n ℓ) (s : Set (EuclideanSpace ℝ (Fin n))),
      MeasurableSet s → (∀ x ∈ s, DifferentiableAt ℝ Φ x) → Set.InjOn Φ s →
      (μHE[n] : Measure (Ambient n ℓ)) (Φ '' s) =
        ∫⁻ x in s, ENNReal.ofReal (Jl (fderiv ℝ Φ x)) := by
    intro Φ s hs hsd hinjs
    have hJm : Measurable fun x => Jl (fderiv ℝ Φ x) :=
      hJl_cont.measurable.comp (measurable_fderiv ℝ Φ)
    have hs₀m : MeasurableSet (s ∩ (fun x => Jl (fderiv ℝ Φ x)) ⁻¹' {0}) :=
      hs.inter (hJm (measurableSet_singleton 0))
    have hs₁m : MeasurableSet (s ∩ (fun x => Jl (fderiv ℝ Φ x)) ⁻¹' Ioi 0) :=
      hs.inter (hJm measurableSet_Ioi)
    have hZ0 : (μHE[n] : Measure (Ambient n ℓ)) (Φ '' (s ∩ (fun x => Jl (fderiv ℝ Φ x)) ⁻¹' {0}))
        = 0 :=
      hZ Φ _ hs₀m (fun x hx => hsd x hx.1) (fun x hx => hx.2)
    have hP1 := hPos Φ _ hs₁m (fun x hx => hsd x hx.1) (hinjs.mono inter_subset_left)
      (fun x hx => hx.2)
    have hsplit : s = (s ∩ (fun x => Jl (fderiv ℝ Φ x)) ⁻¹' Ioi 0) ∪
        (s ∩ (fun x => Jl (fderiv ℝ Φ x)) ⁻¹' {0}) := by
      ext x
      simp only [mem_union, mem_inter_iff, mem_preimage, mem_Ioi, mem_singleton_iff]
      constructor
      · intro hx
        rcases (hJl_nonneg (fderiv ℝ Φ x)).eq_or_lt with h0 | hpos
        · exact Or.inr ⟨hx, h0.symm⟩
        · exact Or.inl ⟨hx, hpos⟩
      · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    have hdisj : Disjoint (s ∩ (fun x => Jl (fderiv ℝ Φ x)) ⁻¹' Ioi 0)
        (s ∩ (fun x => Jl (fderiv ℝ Φ x)) ⁻¹' {0}) := by
      rw [Set.disjoint_left]
      rintro x ⟨_, hx1⟩ ⟨_, hx2⟩
      simp only [mem_preimage, mem_Ioi, mem_singleton_iff] at hx1 hx2
      rw [hx2] at hx1
      exact lt_irrefl _ hx1
    have hint0 : ∫⁻ x in s ∩ (fun x => Jl (fderiv ℝ Φ x)) ⁻¹' {0},
        ENNReal.ofReal (Jl (fderiv ℝ Φ x)) = 0 := by
      rw [setLIntegral_congr_fun hs₀m (g := fun _ => 0) fun x hx => by
        rw [show Jl (fderiv ℝ Φ x) = 0 from hx.2, ENNReal.ofReal_zero]]
      exact lintegral_zero
    have hint : ∫⁻ x in s, ENNReal.ofReal (Jl (fderiv ℝ Φ x)) =
        ∫⁻ x in s ∩ (fun x => Jl (fderiv ℝ Φ x)) ⁻¹' Ioi 0, ENNReal.ofReal (Jl (fderiv ℝ Φ x)) := by
      conv_lhs => rw [hsplit]
      rw [lintegral_union hs₀m hdisj, hint0, add_zero]
    rw [hint, ← hP1]
    apply le_antisymm _ (measure_mono (image_mono inter_subset_left))
    calc (μHE[n] : Measure (Ambient n ℓ)) (Φ '' s)
        ≤ μHE[n] (Φ '' (s ∩ (fun x => Jl (fderiv ℝ Φ x)) ⁻¹' Ioi 0)) +
            μHE[n] (Φ '' (s ∩ (fun x => Jl (fderiv ℝ Φ x)) ⁻¹' {0})) := by
          conv_lhs => rw [hsplit, image_union]
          exact measure_union_le _ _
      _ = μHE[n] (Φ '' (s ∩ (fun x => Jl (fderiv ℝ Φ x)) ⁻¹' Ioi 0)) := by
          rw [hZ0, add_zero]
  /- Weighted area formula with an arbitrary (not necessarily measurable) weight `g`: the
  restriction of `Φ` to `s` is a measurable embedding carrying `(Jl ∘ DΦ) · Lⁿ ⌞ s` to
  `Hⁿ ⌞ Φ(s)` (by `hMI` on measurable subsets of `s`). -/
  have hW : ∀ (Φ : EuclideanSpace ℝ (Fin n) → Ambient n ℓ) (s : Set (EuclideanSpace ℝ (Fin n))),
      MeasurableSet s → (∀ x ∈ s, DifferentiableAt ℝ Φ x) → Set.InjOn Φ s →
      ∀ g : Ambient n ℓ → ℝ≥0∞, ∫⁻ y in Φ '' s, g y ∂μHE[n] =
        ∫⁻ x in s, ENNReal.ofReal (Jl (fderiv ℝ Φ x)) * g (Φ x) := by
    intro Φ s hs hsd hinjs g
    have hΦc : ContinuousOn Φ s := fun x hx => (hsd x hx).continuousAt.continuousWithinAt
    have hemb := hΦc.measurableEmbedding hs hinjs
    have hsub : MeasurableEmbedding (Subtype.val : s → EuclideanSpace ℝ (Fin n)) :=
      MeasurableEmbedding.subtype_coe hs
    have hJm : Measurable fun x => ENNReal.ofReal (Jl (fderiv ℝ Φ x)) :=
      (hJl_cont.measurable.comp (measurable_fderiv ℝ Φ)).ennreal_ofReal
    have hmap : Measure.map (s.domRestrict Φ)
        (((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
          fun x => ENNReal.ofReal (Jl (fderiv ℝ Φ x))).comap
          (Subtype.val : s → EuclideanSpace ℝ (Fin n))) =
        (μHE[n] : Measure (Ambient n ℓ)).restrict (Φ '' s) := by
      ext t ht
      rw [Measure.map_apply hemb.measurable ht, hsub.comap_apply]
      have hBm : MeasurableSet
          ((Subtype.val : s → EuclideanSpace ℝ (Fin n)) '' ((s.domRestrict Φ) ⁻¹' t)) :=
        hsub.measurableSet_image' (hemb.measurable ht)
      have hBs : (Subtype.val : s → EuclideanSpace ℝ (Fin n)) '' ((s.domRestrict Φ) ⁻¹' t) ⊆ s := by
        rintro x ⟨u, _, rfl⟩
        exact u.property
      rw [withDensity_apply _ hBm, ← hMI Φ _ hBm (fun x hx => hsd x (hBs hx)) (hinjs.mono hBs),
        Measure.restrict_apply ht]
      congr 1
      ext y
      constructor
      · rintro ⟨x, ⟨u, hu, rfl⟩, rfl⟩
        exact ⟨hu, ⟨u, u.property, rfl⟩⟩
      · rintro ⟨hy, x, hx, rfl⟩
        exact ⟨x, ⟨⟨x, hx⟩, hy, rfl⟩, rfl⟩
    rw [← hmap, hemb.lintegral_map]
    change (∫⁻ x : s, (fun x : EuclideanSpace ℝ (Fin n) => g (Φ x)) x ∂
      (((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        fun x => ENNReal.ofReal (Jl (fderiv ℝ Φ x))).comap
        (Subtype.val : s → EuclideanSpace ℝ (Fin n)))) = _
    rw [lintegral_subtype_comap hs (fun x : EuclideanSpace ℝ (Fin n) => g (Φ x)),
      setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀ _ hJm.aemeasurable _ hs]
    · rfl
    · exact Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  /- Chain rule for the Jacobian: `Jl (L ∘ T) = jac(L, range T) · Jl T`, where `jac` is the
  square-rooted determinant of the statement. For injective `T` write `T eᵢ = ∑ₐ Mₐᵢ bₐ` in an
  orthonormal basis `b` of `Q = range T`; then the Gram matrices of `T e` and `L T e` are `Mᵀ M`
  and `Mᵀ G M` with `G = (⟪L bₐ, L b_c⟫)`, and `det G = det S_Q(L)` by the sibling theorem. -/
  have hchain : ∀ (L : Ambient n ℓ →L[ℝ] Ambient n ℓ)
      (T : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ) (Q : Submodule ℝ (Ambient n ℓ)),
      Q = LinearMap.range T.toLinearMap →
      Jl (L.comp T) = Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (n + ℓ) ↦
        inner ℝ (L (Q.starProjection (EuclideanSpace.single i (1 : ℝ))))
          (L (Q.starProjection (EuclideanSpace.single j (1 : ℝ)))) +
        inner ℝ (EuclideanSpace.single i (1 : ℝ) - Q.starProjection (EuclideanSpace.single i (1 : ℝ)))
          (EuclideanSpace.single j (1 : ℝ) - Q.starProjection (EuclideanSpace.single j (1 : ℝ))))) *
        Jl T := by
    intro L T Q hQ
    by_cases hT : Function.Injective T
    · have hk : Module.finrank ℝ Q = n := by
        rw [hQ, LinearMap.finrank_range_of_inj hT, finrank_euclideanSpace_fin]
      let b : OrthonormalBasis (Fin n) ℝ Q := (stdOrthonormalBasis ℝ Q).reindex (finCongr hk)
      rw [Submission.ts_fv_det_tangential_gram_eq (n + ℓ) n Q b L]
      have hTQ : ∀ x, T x ∈ Q := fun x => by
        rw [hQ]
        exact LinearMap.mem_range_self _ x
      set M : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun a i =>
        inner ℝ (b a : Ambient n ℓ) (T (EuclideanSpace.basisFun (Fin n) ℝ i)) with hM
      have hexp : ∀ i, T (EuclideanSpace.basisFun (Fin n) ℝ i) =
          ∑ a, M a i • (b a : Ambient n ℓ) := by
        intro i
        have h := congrArg (fun x : Q => (x : Ambient n ℓ))
          (b.sum_repr' ⟨T (EuclideanSpace.basisFun (Fin n) ℝ i), hTQ _⟩)
        simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at h
        exact h.symm
      have hgram : ∀ L' : Ambient n ℓ →L[ℝ] Ambient n ℓ, (Matrix.of fun i j : Fin n =>
          inner ℝ (L' (T (EuclideanSpace.basisFun (Fin n) ℝ i)))
            (L' (T (EuclideanSpace.basisFun (Fin n) ℝ j)))) =
          M.transpose * (Matrix.of fun a c : Fin n => inner ℝ (L' (b a)) (L' (b c))) * M := by
        intro L'
        ext i j
        rw [Matrix.of_apply, hexp i, hexp j]
        simp only [map_sum, map_smul, inner_sum, sum_inner, real_inner_smul_left,
          real_inner_smul_right, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
          Finset.sum_mul]
        exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => by ring
      have hid : (Matrix.of fun a c : Fin n => inner ℝ (b a : Ambient n ℓ) (b c : Ambient n ℓ)) =
          1 := by
        ext a c
        rw [Matrix.of_apply, Matrix.one_apply, ← Submodule.coe_inner]
        exact orthonormal_iff_ite.mp b.orthonormal a c
      have hJT : Jl T = |M.det| := by
        have h := hgram (ContinuousLinearMap.id ℝ (Ambient n ℓ))
        simp only [ContinuousLinearMap.id_apply] at h
        rw [hJl]
        simp only
        rw [h, hid, Matrix.mul_one, Matrix.det_mul, Matrix.det_transpose, Real.sqrt_mul_self_eq_abs]
      rw [hJT, hJl]
      simp only [ContinuousLinearMap.comp_apply]
      rw [hgram L, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
        show M.det * (Matrix.of fun a c : Fin n => inner ℝ (L (b a)) (L (b c))).det * M.det =
          M.det ^ 2 * (Matrix.of fun a c : Fin n => inner ℝ (L (b a)) (L (b c))).det by ring,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
      ring
    · have hLT : ¬ Function.Injective (L.comp T) := fun h =>
        hT fun x y hxy => h (by rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
          hxy])
      rw [LA2 T hT, LA2 _ hLT, mul_zero]
  /- Assembly. `B = C ∩ F⁻¹(A)` is Borel with `F(B) = A`; `F` and `G = f ∘ F` are injective
  and differentiable on `B` with `G(B) = f(A)`. Apply `hW` to `G` with weight `w` and to `F` with
  weight `jac · (w ∘ f)`, and compare the integrands on `B` with `fderiv_comp` and `hchain`. -/
  obtain ⟨LF, hLF⟩ := hFL
  have hB : MeasurableSet (C ∩ F ⁻¹' A) := hC.inter (hLF.continuous.measurable hA)
  have hBA : F '' (C ∩ F ⁻¹' A) = A := by
    apply Subset.antisymm
    · rintro _ ⟨v, ⟨_, hv⟩, rfl⟩
      exact hv
    · intro y hy
      obtain ⟨v, hv, rfl⟩ := hAC hy
      exact ⟨v, ⟨hv, hy⟩, rfl⟩
  have hBd : ∀ v ∈ C ∩ F ⁻¹' A, DifferentiableAt ℝ F v := fun v hv => hFd v hv.1
  have hBi : Set.InjOn F (C ∩ F ⁻¹' A) := hFi.mono inter_subset_left
  have hGd : ∀ v ∈ C ∩ F ⁻¹' A, DifferentiableAt ℝ (f ∘ F) v := fun v hv =>
    (hfd _ hv.2).comp v (hFd v hv.1)
  have hGi : Set.InjOn (f ∘ F) (C ∩ F ⁻¹' A) := fun v hv v' hv' h =>
    hBi hv hv' (hfi hv.2 hv'.2 h)
  have hGB : (f ∘ F) '' (C ∩ F ⁻¹' A) = f '' A := by rw [image_comp, hBA]
  rw [← hGB, hW _ _ hB hGd hGi w]
  conv_rhs => rw [← hBA]
  rw [hW _ _ hB hBd hBi]
  apply setLIntegral_congr_fun hB
  intro v hv
  simp only [Function.comp_apply]
  rw [fderiv_comp v (hfd _ hv.2) (hFd v hv.1), hchain _ _ (P (F v)) (hP v hv.1 hv.2),
    ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  ring
/-- **Integral over the range of a linear map.** If a continuous linear `A : ℝⁿ → ℝ^{n+ℓ}` and
`j ≥ 0` satisfy `Hⁿ(A(S)) = j Lⁿ(S)` for every `S ⊆ ℝⁿ`, then `Hⁿ ⌞ range A = A_#(j Lⁿ)`, so
`∫_{range A} f dHⁿ = j ∫ f(Au) du` for every `f ∈ C_c(ℝ^{n+ℓ})`. -/
theorem Submission.ts_pdb_linear_range_integral : ∀ (n ℓ : ℕ) (A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ) (j : ℝ), 0 ≤ j → (∀ S : Set (EuclideanSpace ℝ (Fin n)), (μHE[n] : Measure (Ambient n ℓ)) (A '' S) = ENNReal.ofReal j * volume S) → ∀ f : C_c(Ambient n ℓ, ℝ), ∫ y in (LinearMap.range A.toLinearMap : Set (Ambient n ℓ)), f y ∂μHE[n] = j * ∫ u, f (A u) := by
  intro n ℓ A j hj hA f
  -- `Hⁿ ⌞ range A = A_#(j Lⁿ)`: for Borel `T`, `T ∩ range A = A(A⁻¹T)`; apply `hA` to `A⁻¹T`.
  have hmeas : (μHE[n] : Measure (Ambient n ℓ)).restrict (LinearMap.range A.toLinearMap) =
      (ENNReal.ofReal j • (volume : Measure (EuclideanSpace ℝ (Fin n)))).map A := by
    ext T hT
    rw [Measure.restrict_apply hT, Measure.map_apply A.measurable hT, Measure.smul_apply,
      smul_eq_mul, ← hA, LinearMap.coe_range, ContinuousLinearMap.coe_coe,
      Set.image_preimage_eq_inter_range]
  -- Change variables along `A`, then pull out the scalar `(ofReal j).toReal = j`.
  rw [hmeas, integral_map A.measurable.aemeasurable (map_continuous f).aestronglyMeasurable,
    integral_smul_measure, ENNReal.toReal_ofReal hj, smul_eq_mul]
/-- **Rescaled complement at a Lebesgue density point** (a step in the proof of `ApproxTangentAE`,
Simon Ch. 3, 1.9 and Ch. 4, 1.3). If `C ⊆ ℝⁿ` is Borel, `R > 0` and
`Lⁿ(C ∩ B_r(w)) / Lⁿ(B_r(w)) → 1` as `r ↓ 0`, then
`Lⁿ{u ∈ B_R(0) : w + tu ∉ C} → 0` as `t ↓ 0`: the set is the preimage of `B_{tR}(w) \ C` under
`u ↦ w + tu`, so its measure is
`t⁻ⁿ Lⁿ(B_{tR}(w) \ C) = Rⁿ Lⁿ(B_1(0)) (1 - Lⁿ(C ∩ B_{tR}(w)) / Lⁿ(B_{tR}(w))) → 0`. -/
theorem Submission.ts_pdb_density_complement_vanish : ∀ (n : ℕ) (C : Set (EuclideanSpace ℝ (Fin n))) (w : EuclideanSpace ℝ (Fin n)) (R : ℝ), MeasurableSet C → 0 < R → Tendsto (fun r : ℝ ↦ volume (C ∩ closedBall w r) / volume (closedBall w r)) (𝓝[>] 0) (𝓝 1) → Tendsto (fun t : ℝ ↦ volume {u : EuclideanSpace ℝ (Fin n) | u ∈ closedBall 0 R ∧ w + t • u ∉ C}) (𝓝[>] 0) (𝓝 0) := by
  intro n C w R hC hR hq
  -- `V = Lⁿ(B_1(0)) < ∞`.
  set V : ℝ≥0∞ := volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1)
  have hVfin : V ≠ ⊤ := measure_ball_lt_top.ne
  -- Step 1: the complementary ratio `1 - q(r)` tends to `0`.
  have h1 : Tendsto (fun r : ℝ ↦ 1 - volume (C ∩ closedBall w r) / volume (closedBall w r))
      (𝓝[>] 0) (𝓝 0) := by
    have := ENNReal.Tendsto.sub tendsto_const_nhds hq (Or.inl ENNReal.one_ne_top)
    simpa using this
  -- Step 5 (first half): `t ↦ t * R` maps `t ↓ 0` to `r ↓ 0`.
  have hmul : Tendsto (fun t : ℝ ↦ t * R) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h : Tendsto (fun t : ℝ ↦ t * R) (𝓝 0) (𝓝 (0 * R)) :=
        (continuous_id.mul continuous_const).tendsto 0
      rw [zero_mul] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      exact mul_pos ht hR
  have h2 : Tendsto (fun t : ℝ ↦ ENNReal.ofReal (R ^ n) * V *
      (1 - volume (C ∩ closedBall w (t * R)) / volume (closedBall w (t * R)))) (𝓝[>] 0) (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (h1.comp hmul)
      (Or.inr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVfin) :
        (0 : ℝ≥0∞) ≠ 0 ∨ ENNReal.ofReal (R ^ n) * V ≠ ⊤)
    simpa using this
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  -- Step 2: `B = B_{tR}(w)` has `0 < Lⁿ(B) = (tR)ⁿ Lⁿ(B_1(0)) < ∞`.
  have hr : 0 < t * R := mul_pos ht hR
  set B := closedBall w (t * R) with hB
  have hBpos : volume B ≠ 0 := (measure_closedBall_pos volume w hr).ne'
  have hBfin : volume B ≠ ⊤ := measure_closedBall_lt_top.ne
  have hBval : volume B = ENNReal.ofReal ((t * R) ^ n) * V := by
    rw [hB, Measure.addHaar_closedBall volume w hr.le, finrank_euclideanSpace_fin]
  -- Step 3: `Lⁿ(B \ C) = Lⁿ(B) (1 - q(tR))`.
  have hdiff : volume (B \ C) = volume B * (1 - volume (C ∩ B) / volume B) := by
    have hBC : B \ C = B \ (C ∩ B) := by
      ext x; simp only [Set.mem_sdiff, mem_inter_iff]; tauto
    rw [hBC, measure_sdiff inter_subset_right (hC.inter measurableSet_closedBall).nullMeasurableSet
      (ne_top_of_le_ne_top hBfin (measure_mono inter_subset_right)),
      ENNReal.mul_sub (fun _ _ ↦ hBfin), mul_one, ENNReal.mul_div_cancel hBpos hBfin]
  -- Step 4: the set is the preimage of `B \ C` under `u ↦ w + t • u`, so its measure is
  -- `t⁻ⁿ Lⁿ(B \ C) = Rⁿ Lⁿ(B_1(0)) (1 - q(tR))`.
  have hset : {u : EuclideanSpace ℝ (Fin n) | u ∈ closedBall 0 R ∧ w + t • u ∉ C} =
      (fun u ↦ t • u) ⁻¹' ((fun x ↦ w + x) ⁻¹' (B \ C)) := by
    ext u
    simp only [mem_ofPred_eq, mem_preimage, Set.mem_sdiff, hB, mem_closedBall, sub_zero,
      dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    constructor
    · rintro ⟨hu, hw⟩; exact ⟨mul_le_mul_of_nonneg_left hu ht.le, hw⟩
    · rintro ⟨hu, hw⟩; exact ⟨le_of_mul_le_mul_left hu ht, hw⟩
  rw [hset, Measure.addHaar_preimage_smul volume ht.ne', measure_preimage_add, hdiff, hBval,
    finrank_euclideanSpace_fin, ← mul_assoc, ← mul_assoc]
  congr 2
  rw [← ENNReal.ofReal_mul (abs_nonneg _), abs_of_pos (by positivity), mul_pow,
    ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero n ht.ne'), one_mul]

/-- **Blow-up of a weighted Lebesgue integral at a density point** (a step in the proof of
`ApproxTangentAE`, Simon Ch. 3, 1.9 and Ch. 4, 1.3). Let `C ⊆ ℝⁿ` be compact, `F` continuous with
injective derivative `A` at `w ∈ C`, `J` continuous on `C`, `c|v - w| ≤ |F(v) - F(w)|` on `C` and
`Lⁿ(C ∩ B_r(w)) / Lⁿ(B_r(w)) → 1` as `r ↓ 0`. Then for `f ∈ C_c`,
`t⁻ⁿ ∫_C J(v) f(t⁻¹(F(v) - F(w))) dv → J(w) ∫ f(Au) du` as `t ↓ 0`: after `v = w + tu` both
integrands vanish off `B_{R'}(0)`, they are uniformly close where `w + tu ∈ C`, and the rest of
`B_{R'}(0)` has measure `→ 0` by `Submission.ts_pdb_density_complement_vanish`. -/
theorem Submission.ts_pdb_density_point_rescaled_limit : ∀ (n ℓ : ℕ) (C : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → Ambient n ℓ) (J : EuclideanSpace ℝ (Fin n) → ℝ) (A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ) (w : EuclideanSpace ℝ (Fin n)) (c : ℝ), IsCompact C → Continuous F → ContinuousOn J C → w ∈ C → HasFDerivAt F A w → Function.Injective A → 0 < c → (∀ v ∈ C, c * ‖v - w‖ ≤ ‖F v - F w‖) → Tendsto (fun r : ℝ ↦ volume (C ∩ closedBall w r) / volume (closedBall w r)) (𝓝[>] 0) (𝓝 1) → ∀ f : C_c(Ambient n ℓ, ℝ), Tendsto (fun t : ℝ ↦ (t ^ n)⁻¹ * ∫ v in C, J v * f (t⁻¹ • (F v - F w))) (𝓝[>] 0) (𝓝 (J w * ∫ u, f (A u))) := by
  intro n ℓ C F J A w c hC hF hJ hw hA hAinj hc hlow hdens f
  -- Step 1: constants. `C` is closed, hence Borel; `f = 0` off `B_R(0)` and `|f| ≤ Mf`;
  -- `‖u‖ ≤ K ‖A u‖`; `R' = R (c⁻¹ + K)`.
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  obtain ⟨R₀, hR₀⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
  set R : ℝ := max R₀ 1 with hRdef
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hfR : ∀ z, R < ‖z‖ → f z = 0 := by
    intro z hz
    refine image_eq_zero_of_notMem_tsupport fun hz' ↦ ?_
    have h := hR₀ hz'
    rw [mem_closedBall, dist_zero_right] at h
    linarith [le_max_left R₀ 1]
  obtain ⟨Mf, hMf⟩ := (map_continuous f).bounded_above_of_compact_support f.hasCompactSupport
  have hMf0 : 0 ≤ Mf := (norm_nonneg _).trans (hMf 0)
  obtain ⟨K, -, hK⟩ := (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] Ambient n ℓ).exists_antilipschitzWith
    (LinearMap.ker_eq_bot.2 hAinj)
  have hKu : ∀ u, ‖u‖ ≤ K * ‖A u‖ := fun u ↦ by simpa using hK.le_mul_dist u 0
  set R' : ℝ := R * (c⁻¹ + K) with hR'eq
  have hR' : 0 < R' := by positivity
  have hcR' : R ≤ c * R' := by
    have h : c * R' = R + c * R * K := by rw [hR'eq]; field_simp
    nlinarith [mul_nonneg (mul_nonneg hc.le hR.le) (NNReal.coe_nonneg K)]
  have hKR' : K * R ≤ R' := by
    have h : R' = R * c⁻¹ + K * R := by rw [hR'eq]; ring
    nlinarith [mul_nonneg hR.le (inv_pos.2 hc).le]
  -- Step 2: notation. `G t u = 1_C(w + tu) J(w + tu) f(t⁻¹(F(w + tu) - F(w)))`,
  -- `H u = J(w) f(Au)`.
  set φ : ℝ → EuclideanSpace ℝ (Fin n) → ℝ := fun t v ↦ J v * f (t⁻¹ • (F v - F w)) with hφ
  set G : ℝ → EuclideanSpace ℝ (Fin n) → ℝ := fun t u ↦ C.indicator (φ t) (w + t • u) with hG
  set H : EuclideanSpace ℝ (Fin n) → ℝ := fun u ↦ J w * f (A u) with hH
  -- Step 3: rescaling `v = w + tu`.
  have hresc : ∀ t : ℝ, 0 < t →
      (t ^ n)⁻¹ * ∫ v in C, J v * f (t⁻¹ • (F v - F w)) = ∫ u, G t u := by
    intro t ht
    have h := Measure.integral_comp_smul (volume : Measure (EuclideanSpace ℝ (Fin n)))
      (fun x ↦ C.indicator (φ t) (w + x)) t
    rw [integral_add_left_eq_self (C.indicator (φ t)) w, integral_indicator hCm,
      finrank_euclideanSpace_fin, abs_of_pos (by positivity), smul_eq_mul] at h
    exact h.symm
  -- Step 4: integrability of `G t` (`t ≠ 0`).
  have hφint : ∀ t, IntegrableOn (φ t) C := fun t ↦ ContinuousOn.integrableOn_compact hC
    (hJ.mul ((map_continuous f).comp ((hF.sub continuous_const).const_smul t⁻¹)).continuousOn)
  have hGint : ∀ t, t ≠ 0 → Integrable (G t) := fun t ht ↦
    (((integrable_indicator_iff hCm).2 (hφint t)).comp_add_left w).comp_smul ht
  -- Step 5(b): `H` vanishes off `B_{R'}(0)`, hence is integrable.
  have hH0 : ∀ u, R' < ‖u‖ → H u = 0 := by
    intro u hu
    have hAu : R < ‖A u‖ := by
      by_contra h
      push Not at h
      have h1 : (K : ℝ) * ‖A u‖ ≤ K * R := mul_le_mul_of_nonneg_left h K.2
      linarith [hKu u]
    simp only [hH, hfR _ hAu, mul_zero]
  have hHint : Integrable H := by
    have hHc : Continuous H := continuous_const.mul ((map_continuous f).comp A.continuous)
    refine hHc.integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) R') ?_)
    intro u hu
    exact hH0 u (by simpa [mem_closedBall, dist_zero_right, not_le] using hu)
  -- Step 5(a): `G t` vanishes off `B_{R'}(0)` (`t > 0`).
  have hG0 : ∀ t, 0 < t → ∀ u, R' < ‖u‖ → G t u = 0 := by
    intro t ht u hu
    by_cases hmem : w + t • u ∈ C
    · have h1 := hlow _ hmem
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht] at h1
      have hQ : R < ‖t⁻¹ • (F (w + t • u) - F w)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht]
        have h2 : c * ‖u‖ ≤ t⁻¹ * ‖F (w + t • u) - F w‖ := by
          rw [le_inv_mul_iff₀ ht]
          linarith
        have h3 : c * R' < c * ‖u‖ := mul_lt_mul_of_pos_left hu hc
        linarith
      simp only [hG, indicator_of_mem hmem, hφ, hfR _ hQ, mul_zero]
    · simp only [hG, indicator_of_notMem hmem]
  -- Step 6: uniform estimate on the good set `{u ∈ B_{R'}(0) : w + tu ∈ C}`.
  have hunif : ∀ ε > 0, ∃ t₀ > 0, ∀ t, 0 < t → t < t₀ → ∀ u, ‖u‖ ≤ R' → w + t • u ∈ C →
      |G t u - H u| ≤ ε := by
    intro ε hε
    set ε₁ := ε / (2 * (|J w| + 1)) with hε₁def
    set ε₂ := ε / (2 * (Mf + 1)) with hε₂def
    have hε₁ : 0 < ε₁ := by positivity
    have hε₂ : 0 < ε₂ := by positivity
    obtain ⟨δf, hδf, hfδ⟩ := Metric.uniformContinuous_iff.1
      (CompactlySupportedContinuousMapClass.uniformContinuous f) ε₁ hε₁
    obtain ⟨δJ, hδJ, hJδ⟩ := Metric.continuousOn_iff.1 hJ w hw ε₂ hε₂
    set η := δf / (2 * (R' + 1)) with hηdef
    have hη : 0 < η := by positivity
    obtain ⟨δd, hδd, hdδ⟩ := Metric.eventually_nhds_iff.1
      (Asymptotics.isLittleO_iff.1 (hasFDerivAt_iff_isLittleO_nhds_zero.1 hA) hη)
    refine ⟨min δJ δd / (R' + 1), by positivity, ?_⟩
    intro t ht ht₀ u hu hmem
    have htu : ‖t • u‖ < min δJ δd := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      calc t * ‖u‖ ≤ t * R' := mul_le_mul_of_nonneg_left hu ht.le
        _ < t * (R' + 1) := by nlinarith
        _ < min δJ δd / (R' + 1) * (R' + 1) := mul_lt_mul_of_pos_right ht₀ (by positivity)
        _ = min δJ δd := by field_simp
    have hJe : |J (w + t • u) - J w| < ε₂ := by
      have h := hJδ (w + t • u) hmem
        (by rw [dist_eq_norm, add_sub_cancel_left]; exact htu.trans_le (min_le_left _ _))
      rwa [Real.dist_eq] at h
    have hde : ‖F (w + t • u) - F w - A (t • u)‖ ≤ η * ‖t • u‖ :=
      hdδ (by rw [dist_zero_right]; exact htu.trans_le (min_le_right _ _))
    have hQ : dist (t⁻¹ • (F (w + t • u) - F w)) (A u) < δf := by
      have h : t⁻¹ • (F (w + t • u) - F w) - A u =
          t⁻¹ • (F (w + t • u) - F w - A (t • u)) := by
        rw [map_smul, smul_sub t⁻¹ (F (w + t • u) - F w) (t • A u), inv_smul_smul₀ ht.ne']
      rw [dist_eq_norm, h, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht]
      calc t⁻¹ * ‖F (w + t • u) - F w - A (t • u)‖ ≤ t⁻¹ * (η * ‖t • u‖) :=
            mul_le_mul_of_nonneg_left hde (by positivity)
        _ = η * ‖u‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]; field_simp
        _ ≤ η * R' := mul_le_mul_of_nonneg_left hu hη.le
        _ < δf := by
          rw [hηdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith
    have hfe : |f (t⁻¹ • (F (w + t • u) - F w)) - f (A u)| < ε₁ := by
      have h := hfδ hQ
      rwa [Real.dist_eq] at h
    have hfQ : |f (t⁻¹ • (F (w + t • u) - F w))| ≤ Mf := by
      simpa [Real.norm_eq_abs] using hMf (t⁻¹ • (F (w + t • u) - F w))
    simp only [hG, hH, indicator_of_mem hmem, hφ]
    calc |J (w + t • u) * f (t⁻¹ • (F (w + t • u) - F w)) - J w * f (A u)|
        = |(J (w + t • u) - J w) * f (t⁻¹ • (F (w + t • u) - F w)) +
            J w * (f (t⁻¹ • (F (w + t • u) - F w)) - f (A u))| := by ring_nf
      _ ≤ |J (w + t • u) - J w| * |f (t⁻¹ • (F (w + t • u) - F w))| +
            |J w| * |f (t⁻¹ • (F (w + t • u) - F w)) - f (A u)| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ ε₂ * Mf + |J w| * ε₁ := by gcongr
      _ ≤ ε / 2 + ε / 2 := by
          gcongr
          · rw [hε₂def, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) two_pos]
            nlinarith
          · rw [hε₁def, mul_div_assoc', div_le_div_iff₀ (by positivity) two_pos]
            nlinarith [abs_nonneg (J w)]
      _ = ε := by ring
  -- Step 7: pointwise bound `|G t - H| ≤ ε 1_B + M 1_{S t}` with `B = B_{R'}(0)`,
  -- `S t = {u ∈ B : w + tu ∉ C}` and `M = |J(w)| Mf`.
  set B : Set (EuclideanSpace ℝ (Fin n)) := closedBall 0 R' with hBdef
  set S : ℝ → Set (EuclideanSpace ℝ (Fin n)) :=
    fun t ↦ {u | u ∈ closedBall 0 R' ∧ w + t • u ∉ C}
  set M : ℝ := |J w| * Mf with hMdef
  have hM : 0 ≤ M := by positivity
  have hpt : ∀ ε > 0, ∃ t₀ > 0, ∀ t, 0 < t → t < t₀ → ∀ u,
      ‖G t u - H u‖ ≤ B.indicator (fun _ ↦ ε) u + (S t).indicator (fun _ ↦ M) u := by
    intro ε hε
    obtain ⟨t₀, ht₀, h⟩ := hunif ε hε
    refine ⟨t₀, ht₀, fun t ht htt₀ u ↦ ?_⟩
    rw [Real.norm_eq_abs]
    by_cases hu : ‖u‖ ≤ R'
    · have huB : u ∈ B := by rwa [hBdef, mem_closedBall, dist_zero_right]
      rw [indicator_of_mem huB]
      by_cases hmem : w + t • u ∈ C
      · have hS : u ∉ S t := fun h ↦ h.2 hmem
        rw [indicator_of_notMem hS, add_zero]
        exact h t ht htt₀ u hu hmem
      · have hS : u ∈ S t := ⟨huB, hmem⟩
        have hG' : G t u = 0 := by simp only [hG, indicator_of_notMem hmem]
        have hH' : |H u| ≤ M := by
          simp only [hH, hMdef, abs_mul]
          exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hMf (A u))
            (abs_nonneg _)
        rw [indicator_of_mem hS, hG', zero_sub, abs_neg]
        linarith
    · push Not at hu
      rw [hG0 t ht u hu, hH0 u hu, sub_zero, abs_zero]
      exact add_nonneg (indicator_nonneg (fun _ _ ↦ hε.le) _) (indicator_nonneg (fun _ _ ↦ hM) _)
  -- Step 8: integral bound `|∫ G t - ∫ H| ≤ ε Lⁿ(B) + M Lⁿ(S t)`.
  have hint : ∀ ε > 0, ∃ t₀ > 0, ∀ t, 0 < t → t < t₀ →
      ‖(∫ u, G t u) - ∫ u, H u‖ ≤ ε * volume.real B + M * volume.real (S t) := by
    intro ε hε
    obtain ⟨t₀, ht₀, h⟩ := hpt ε hε
    refine ⟨t₀, ht₀, fun t ht htt₀ ↦ ?_⟩
    have hBm : MeasurableSet B := measurableSet_closedBall
    have hBfin : volume B ≠ ⊤ := measure_closedBall_lt_top.ne
    have hSm : MeasurableSet (S t) := measurableSet_closedBall.inter
      (hCm.compl.preimage (measurable_const.add (measurable_const_smul t)))
    have hSfin : volume (S t) ≠ ⊤ := ne_top_of_le_ne_top hBfin (measure_mono fun u hu ↦ hu.1)
    have hb1 : Integrable (B.indicator fun _ ↦ ε) :=
      (integrable_indicator_iff hBm).2 (integrableOn_const hBfin)
    have hb2 : Integrable ((S t).indicator fun _ ↦ M) :=
      (integrable_indicator_iff hSm).2 (integrableOn_const hSfin)
    rw [← integral_sub (hGint t ht.ne') hHint]
    calc ‖∫ u, G t u - H u‖
        ≤ ∫ u, (B.indicator (fun _ ↦ ε) u + (S t).indicator (fun _ ↦ M) u) :=
          norm_integral_le_of_norm_le (hb1.add hb2) (Eventually.of_forall (h t ht htt₀))
      _ = ε * volume.real B + M * volume.real (S t) := by
          rw [integral_add hb1 hb2, integral_indicator_const _ hBm, integral_indicator_const _ hSm,
            smul_eq_mul, smul_eq_mul, mul_comm (volume.real B), mul_comm (volume.real (S t))]
  -- Step 9: `Lⁿ(S t) → 0` by `Submission.ts_pdb_density_complement_vanish`, so
  -- `∫ G t → ∫ H = J(w) ∫ f(Au) du`, and `∫ G t` is the rescaled integral for `t > 0`.
  have hS0 : Tendsto (fun t ↦ volume.real (S t)) (𝓝[>] 0) (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (Submission.ts_pdb_density_complement_vanish n C w R' hCm hR' hdens)
    rw [ENNReal.toReal_zero] at h
    exact h
  have hlim : Tendsto (fun t ↦ ∫ u, G t u) (𝓝[>] 0) (𝓝 (∫ u, H u)) := by
    rw [Metric.tendsto_nhds]
    intro δ hδ
    set VB := volume.real B
    have hVB : 0 ≤ VB := measureReal_nonneg
    set ε := δ / (2 * (VB + 1)) with hεdef
    have hε : 0 < ε := by positivity
    obtain ⟨t₀, ht₀, h⟩ := hint ε hε
    have hεVB : ε * VB < δ / 2 := by
      rw [hεdef, div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) two_pos]
      nlinarith
    have hMS : Tendsto (fun t ↦ M * volume.real (S t)) (𝓝[>] 0) (𝓝 0) := by
      simpa using hS0.const_mul M
    filter_upwards [hMS.eventually (gt_mem_nhds (half_pos hδ)), Ioo_mem_nhdsGT ht₀]
      with t h1t h2t
    rw [dist_eq_norm]
    calc ‖(∫ u, G t u) - ∫ u, H u‖ ≤ ε * VB + M * volume.real (S t) := h t h2t.1 h2t.2
      _ < δ / 2 + δ / 2 := by linarith
      _ = δ := by ring
  have hHval : ∫ u, H u = J w * ∫ u, f (A u) := integral_const_mul _ _
  rw [← hHval]
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  exact (hresc t ht).symm

/-- **Blow-up of a Lipschitz piece at a Lebesgue density point** (Simon Ch. 3, proof of 1.6 `⇒`,
for a parametrized piece in place of the embedded `C¹` pieces of 1.2). Let `C ⊆ ℝⁿ` be compact and
`F : ℝⁿ → ℝ^{n+ℓ}` `K`-Lipschitz, differentiable at every `w ∈ C` with injective `DF(w)`, `DF`
continuous on `C`, and `c|v - w| ≤ |F(v) - F(w)|` on `C` with `c > 0`. Then (3b)
`Hⁿ(F(C) ∩ B_ρ(x)) ≤ Γρⁿ` for `x ∈ F(C)`, `ρ > 0`, with `Γ = Kⁿωₙ/cⁿ`; and (3a) at every Lebesgue
density point `w ∈ C` of `C` and for `f ∈ C_c`,
`t⁻ⁿ ∫_{F(C)} f(t⁻¹(y - F(w))) dHⁿ(y) → ∫_{DF(w)(ℝⁿ)} f dHⁿ` as `t ↓ 0`. -/
theorem Submission.ts_piece_density_blowup : ∀ (n ℓ : ℕ) (C : Set (EuclideanSpace ℝ (Fin n)))
    (F : EuclideanSpace ℝ (Fin n) → Ambient n ℓ), 0 < n →
    (IsCompact C ∧ (∃ K : NNReal, LipschitzWith K F) ∧
      (∀ w ∈ C, DifferentiableAt ℝ F w ∧ Function.Injective (fderiv ℝ F w)) ∧
      ContinuousOn (fderiv ℝ F) C ∧
      ∃ c : ℝ, 0 < c ∧ ∀ v ∈ C, ∀ w ∈ C, c * ‖v - w‖ ≤ ‖F v - F w‖) →
    (∃ Γ : ℝ, ∀ x ∈ F '' C, ∀ ρ : ℝ, 0 < ρ →
      (μHE[n] : Measure (Ambient n ℓ)) (F '' C ∩ closedBall x ρ) ≤ ENNReal.ofReal (Γ * ρ ^ n)) ∧
    ∀ w ∈ C, Tendsto (fun r : ℝ ↦ volume (C ∩ closedBall w r) / volume (closedBall w r))
      (𝓝[>] 0) (𝓝 1) →
    ∀ f : C_c(Ambient n ℓ, ℝ),
      Tendsto (fun t : ℝ ↦ (t ^ n)⁻¹ * ∫ y in F '' C, f (t⁻¹ • (y - F w)) ∂μHE[n]) (𝓝[>] 0)
        (𝓝 (∫ y in (LinearMap.range (fderiv ℝ F w).toLinearMap : Set (Ambient n ℓ)),
          f y ∂μHE[n])) := by
  rintro n ℓ C F - ⟨hC, ⟨K, hK⟩, hdiff, hcont, c, hc, hlow⟩
  -- Step 1(a): by the lower Lipschitz bound, `F` is injective on `C`.
  have hinj : Set.InjOn F C := fun v hv w hw hvw ↦ by
    have h := hlow v hv w hw
    rw [hvw, sub_self, norm_zero] at h
    have h' : ‖v - w‖ = 0 := le_antisymm (by nlinarith [norm_nonneg (v - w)]) (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp h')
  refine ⟨⟨(K : ℝ) ^ n * omega n / c ^ n, ?_⟩, ?_⟩
  -- Step 2, claim (3b): `F(C) ∩ B_ρ(F w) ⊆ F(C ∩ B_{ρ/c}(w))` and the Lipschitz image bound.
  · rintro x ⟨w, hw, rfl⟩ ρ hρ
    exact Submission.ts_pdb_image_closedBall_measure_le n ℓ C F K c w hK hc
      (fun v hv ↦ hlow v hv w hw) ρ hρ
  -- Steps 3–7, claim (3a).
  · intro w hw hdens f
    -- Steps 1(c) and 4: the area formula on the piece, with a Jacobian `J` continuous on `C`
    -- that is the area factor of each `DF(v)`, `v ∈ C`.
    obtain ⟨J, hJ, hJC, harea⟩ := Submission.ts_pdb_piece_area_formula n ℓ C F K
      hC.isClosed.measurableSet hK hinj hcont
    obtain ⟨hJw, hJwS⟩ := hJC w hw
    -- (4.1) for `g = f(t⁻¹(· - F(w)))`.
    have hN : ∀ t : ℝ, ∫ y in F '' C, f (t⁻¹ • (y - F w)) ∂μHE[n] =
        ∫ v in C, J v * f (t⁻¹ • (F v - F w)) := fun t ↦
      harea (fun y ↦ f (t⁻¹ • (y - F w))) (by fun_prop)
    -- Step 6: `∫_{range DF(w)} f dHⁿ = J(w) ∫ f(DF(w) u) du`.
    have hT : ∫ y in (LinearMap.range (fderiv ℝ F w).toLinearMap : Set (Ambient n ℓ)),
        f y ∂μHE[n] = J w * ∫ u, f (fderiv ℝ F w u) :=
      Submission.ts_pdb_linear_range_integral n ℓ (fderiv ℝ F w) (J w) hJw hJwS f
    -- Steps 5 and 7: `t⁻ⁿ ∫_C J(v) f(t⁻¹(F(v) - F(w))) dv → J(w) ∫ f(DF(w) u) du`.
    rw [hT]
    refine (Submission.ts_pdb_density_point_rescaled_limit n ℓ C F J (fderiv ℝ F w) w c hC
      hK.continuous hJ hw (hdiff w hw).1.hasFDerivAt (hdiff w hw).2 hc
      (fun v hv ↦ hlow v hv w hw) hdens f).congr fun t ↦ ?_
    rw [hN t]
/-- **Ch. 3, Remark 1.5(1) and Definition 1.7 (pp. 71, 74); Ch. 4, 1.3 (p. 86).** The approximate
tangent space `T_x V` is unique when it exists: if `P` and `Q` both satisfy `V.IsApproxTangentAt x`
(with possibly different multiplicities `c, c' > 0`), then `P = Q`. -/
theorem Submission.ts_approx_tangent_plane_unique : ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (x : Ambient n ℓ) (P Q : Submodule ℝ (Ambient n ℓ)), V.IsApproxTangentAt x P → V.IsApproxTangentAt x Q → P = Q := by
  intro n ℓ V x P Q ⟨hP, c, hc, hPlim⟩ ⟨hQ, c', hc', hQlim⟩
  -- `c Hⁿ ⌞ P` and `c' Hⁿ ⌞ Q` are regular with the same `C_c` integrals (uniqueness of the
  -- blow-up limit as `λ ↓ 0`), hence equal.
  have hmeas : ENNReal.ofReal c • (μHE[n] : Measure (Ambient n ℓ)).restrict P =
      ENNReal.ofReal c' • (μHE[n] : Measure (Ambient n ℓ)).restrict Q := by
    have := Poincare.SimonGMT.Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule hP
    have := Poincare.SimonGMT.Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule hQ
    have : (ENNReal.ofReal c • (μHE[n] : Measure (Ambient n ℓ)).restrict P).Regular :=
      .smul ENNReal.ofReal_ne_top
    have : (ENNReal.ofReal c' • (μHE[n] : Measure (Ambient n ℓ)).restrict Q).Regular :=
      .smul ENNReal.ofReal_ne_top
    refine Measure.ext_of_integral_eq_on_compactlySupported fun f ↦ ?_
    rw [integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal hc.le,
      ENNReal.toReal_ofReal hc'.le, smul_eq_mul, smul_eq_mul]
    exact tendsto_nhds_unique (hPlim f) (hQlim f)
  -- A nonzero multiple of a measure has the same support, and `spt (Hⁿ ⌞ P) = P`.
  have hsupp (a : ℝ≥0∞) (μ : Measure (Ambient n ℓ)) (ha : a ≠ 0) : (a • μ).support = μ.support :=
    Measure.smul_absolutelyContinuous.support_mono.antisymm
      (Measure.absolutelyContinuous_smul ha).support_mono
  apply SetLike.ext'
  calc (P : Set (Ambient n ℓ))
      = ((μHE[n] : Measure (Ambient n ℓ)).restrict P).support :=
        (Poincare.SimonGMT.Chapter03.support_euclideanHausdorffMeasure_restrict_submodule hP).symm
    _ = (ENNReal.ofReal c • (μHE[n] : Measure (Ambient n ℓ)).restrict P).support :=
        (hsupp _ _ (ENNReal.ofReal_pos.2 hc).ne').symm
    _ = (ENNReal.ofReal c' • (μHE[n] : Measure (Ambient n ℓ)).restrict Q).support := by
        rw [hmeas]
    _ = ((μHE[n] : Measure (Ambient n ℓ)).restrict Q).support :=
        hsupp _ _ (ENNReal.ofReal_pos.2 hc').ne'
    _ = Q := Poincare.SimonGMT.Chapter03.support_euclideanHausdorffMeasure_restrict_submodule hQ
/-- **`Hⁿ`-measure of balls in an `n`-plane.** If `P ⊆ ℝ^{n+ℓ}` is a linear subspace with
`dim P = n` and `s ≥ 0`, then `(Hⁿ ⌞ P)(B_s(0)) = Hⁿ(P ∩ B_s(0)) = ωₙ sⁿ`. -/
theorem Submission.ts_plane_closedBall_measure : ∀ (n ℓ : ℕ) (P : Submodule ℝ (Ambient n ℓ)) (s : ℝ), Module.finrank ℝ P = n → 0 ≤ s → ((μHE[n] : Measure (Ambient n ℓ)).restrict (P : Set (Ambient n ℓ))) (closedBall (0 : Ambient n ℓ) s) = ENNReal.ofReal (omega n * s ^ n) := by
  intro n ℓ P s hP hs
  -- `Hⁿ ⌞ P` is the push-forward of `Hⁿ` on `P` under the isometric inclusion `ι`, and
  -- `ι⁻¹(B_s(0))` is the closed ball `B_s(0)` of `P`.
  have hrange : Set.range (P.subtypeₗᵢ : P → Ambient n ℓ) = (P : Set (Ambient n ℓ)) := by
    ext x
    simp
  have hpre : (P.subtypeₗᵢ : P → Ambient n ℓ) ⁻¹' closedBall 0 s = closedBall (0 : P) s := by
    ext x
    simp [mem_closedBall, dist_eq_norm]
  have h1 : ((μHE[n] : Measure (Ambient n ℓ)).restrict (P : Set (Ambient n ℓ)))
      (closedBall (0 : Ambient n ℓ) s) = (μHE[n] : Measure P) (closedBall (0 : P) s) := by
    rw [← hrange, ← P.subtypeₗᵢ.isometry.map_euclideanHausdorffMeasure,
      Measure.map_apply P.subtypeₗᵢ.continuous.measurable measurableSet_closedBall, hpre]
  -- Orthonormal coordinates `e : P ≃ ℝⁿ` preserve `Hⁿ` and map `B_s(0)` onto `B_s(0)`.
  let e : P ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
    ((stdOrthonormalBasis ℝ P).reindex (finCongr hP)).repr
  have h2 : (μHE[n] : Measure P) (closedBall (0 : P) s) =
      (μHE[n] : Measure (EuclideanSpace ℝ (Fin n))) (closedBall 0 s) := by
    rw [← e.isometry.euclideanHausdorffMeasure_image, e.image_closedBall, map_zero]
  -- `Lⁿ(B_1(0))` is finite, so it equals `ofReal ωₙ`.
  have h3 : volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) = ENNReal.ofReal (omega n) := by
    rw [omega, ENNReal.ofReal_toReal measure_ball_lt_top.ne]
  -- `Hⁿ = Lⁿ` on `ℝⁿ`, and Haar scaling gives `Lⁿ(B_s(0)) = sⁿ Lⁿ(B_1(0))`.
  rw [h1, h2, EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
    Measure.addHaar_closedBall _ _ hs, finrank_euclideanSpace_fin, h3,
    ← ENNReal.ofReal_mul (pow_nonneg hs n), mul_comm]
/-- **Ball mass between blow-up integrals of cut-offs** (Simon Ch. 3, Remark 1.8(2)). Let `μ` be
finite on compact sets, `t > 0` and `f ∈ C_c`. If `f ≤ 1` everywhere and `f ≤ 0` off the closed
unit ball, then `∫ f(t⁻¹(y - x)) dμ(y) ≤ μ(B_t(x))`; if `f ≥ 0` everywhere and `f ≥ 1` on the
closed unit ball, then `μ(B_t(x)) ≤ ∫ f(t⁻¹(y - x)) dμ(y)`. Both follow by integrating a pointwise
comparison of `f(t⁻¹(y - x))` with the indicator of `B_t(x)`, as
`‖t⁻¹(y - x)‖ ≤ 1 ↔ y ∈ B_t(x)`. -/
theorem Submission.ts_blowup_cutoff_closedBall_bounds : ∀ (n ℓ : ℕ) (μ : Measure (Ambient n ℓ)) (x : Ambient n ℓ) (f : C_c(Ambient n ℓ, ℝ)) (t : ℝ), IsFiniteMeasureOnCompacts μ → 0 < t → ((∀ y : Ambient n ℓ, f y ≤ 1) → (∀ y : Ambient n ℓ, 1 < ‖y‖ → f y ≤ 0) → ∫ y, f (t⁻¹ • (y - x)) ∂μ ≤ μ.real (closedBall x t)) ∧ ((∀ y : Ambient n ℓ, 0 ≤ f y) → (∀ y : Ambient n ℓ, ‖y‖ ≤ 1 → 1 ≤ f y) → μ.real (closedBall x t) ≤ ∫ y, f (t⁻¹ • (y - x)) ∂μ) := by
  intro n ℓ μ x f t _ ht
  -- step 1: `η(y) = t⁻¹(y - x)` is a homeomorphism, so `f ∘ η` is continuous with compact
  -- support, hence `μ`-integrable
  let η : Ambient n ℓ ≃ₜ Ambient n ℓ :=
    (Homeomorph.subRight x).trans (Homeomorph.smulOfNeZero t⁻¹ (inv_ne_zero ht.ne'))
  have hF : Integrable (fun y ↦ f (t⁻¹ • (y - x))) μ :=
    ((map_continuous f).comp η.continuous).integrable_of_hasCompactSupport
      (f.hasCompactSupport.comp_homeomorph η)
  -- step 2: `B_t(x)` is compact, so `1_{B_t(x)}` is `μ`-integrable with integral `μ(B_t(x))`
  have hB : MeasurableSet (closedBall x t) := measurableSet_closedBall
  have hI : Integrable ((closedBall x t).indicator (1 : Ambient n ℓ → ℝ)) μ :=
    (integrable_indicator_iff hB).2 (integrableOn_const measure_closedBall_lt_top.ne)
  rw [← integral_indicator_one hB]
  -- step 3: `‖t⁻¹(y - x)‖ ≤ 1 ↔ y ∈ B_t(x)`
  have hmem : ∀ y, ‖t⁻¹ • (y - x)‖ ≤ 1 ↔ y ∈ closedBall x t := fun y ↦ by
    rw [mem_closedBall, dist_eq_norm, norm_smul_of_nonneg (inv_nonneg.2 ht.le),
      inv_mul_le_iff₀ ht, mul_one]
  -- steps 4 and 5: compare pointwise with `1_{B_t(x)}` and integrate
  refine ⟨fun hle hout ↦ integral_mono hF hI fun y ↦ ?_,
    fun hnn hin ↦ integral_mono hI hF fun y ↦ ?_⟩
  · by_cases hy : y ∈ closedBall x t
    · rw [indicator_of_mem hy]
      exact hle _
    · rw [indicator_of_notMem hy]
      exact hout _ (not_le.1 fun h ↦ hy ((hmem y).1 h))
  · by_cases hy : y ∈ closedBall x t
    · rw [indicator_of_mem hy]
      exact hin _ ((hmem y).2 hy)
    · rw [indicator_of_notMem hy]
      exact hnn _

/-- **Cut-offs approximating the unit ball of an `n`-plane.** If `P ⊆ ℝ^{n+ℓ}` is a linear
subspace with `dim P = n`, then `ωₙ = Hⁿ(P ∩ B_1(0))` is approximated from below by `∫_P g dHⁿ`
with `g ∈ C_c`, `g ≤ 1`, `g ≤ 0` off `B_1(0)`, and from above by `∫_P h dHⁿ` with `h ∈ C_c`,
`h ≥ 0`, `h ≥ 1` on `B_1(0)` (Simon Ch. 3, Remark 1.8(2)). -/
theorem Submission.ts_unit_ball_plane_cutoff_approx : ∀ (n ℓ : ℕ) (P : Submodule ℝ (Ambient n ℓ)), Module.finrank ℝ P = n → (∀ a : ℝ, a < omega n → ∃ g : C_c(Ambient n ℓ, ℝ), (∀ y : Ambient n ℓ, g y ≤ 1) ∧ (∀ y : Ambient n ℓ, 1 < ‖y‖ → g y ≤ 0) ∧ a < ∫ y in (P : Set (Ambient n ℓ)), g y ∂μHE[n]) ∧ (∀ b : ℝ, omega n < b → ∃ h : C_c(Ambient n ℓ, ℝ), (∀ y : Ambient n ℓ, 0 ≤ h y) ∧ (∀ y : Ambient n ℓ, ‖y‖ ≤ 1 → 1 ≤ h y) ∧ ∫ y in (P : Set (Ambient n ℓ)), h y ∂μHE[n] < b) := by
  intro n ℓ P hP
  set ν : Measure (Ambient n ℓ) := (μHE[n] : Measure (Ambient n ℓ)).restrict (P : Set (Ambient n ℓ))
  have hω : 0 ≤ omega n := ENNReal.toReal_nonneg
  -- `ν = Hⁿ ⌞ P` is finite on compact sets: a compact set lies in some `B_R(0)` with `R ≥ 0`,
  -- and `ν(B_R(0)) = ωₙ Rⁿ`. Hence every `f ∈ C_c` is `ν`-integrable.
  have hfin : IsFiniteMeasureOnCompacts ν := by
    refine ⟨fun K hK ↦ ?_⟩
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
    calc ν K ≤ ν (closedBall 0 (max R 0)) :=
          measure_mono (hR.trans (closedBall_subset_closedBall (le_max_left R 0)))
      _ = ENNReal.ofReal (omega n * max R 0 ^ n) :=
          Submission.ts_plane_closedBall_measure n ℓ P _ hP (le_max_right R 0)
      _ < ⊤ := ENNReal.ofReal_lt_top
  -- For `s ≥ 0`, `1_{B_s(0)}` is `ν`-integrable and `∫ 1_{B_s(0)} dν = ν(B_s(0)) = ωₙ sⁿ`.
  have hball : ∀ s : ℝ, 0 ≤ s →
      Integrable ((closedBall (0 : Ambient n ℓ) s).indicator (1 : Ambient n ℓ → ℝ)) ν ∧
        ∫ y, (closedBall (0 : Ambient n ℓ) s).indicator (1 : Ambient n ℓ → ℝ) y ∂ν =
          omega n * s ^ n := by
    intro s hs
    have hs' := Submission.ts_plane_closedBall_measure n ℓ P s hP hs
    refine ⟨(integrable_indicator_iff measurableSet_closedBall).2
      (integrableOn_const (by rw [hs']; exact ENNReal.ofReal_ne_top)), ?_⟩
    rw [integral_indicator_one measurableSet_closedBall, measureReal_def, hs',
      ENNReal.toReal_ofReal (mul_nonneg hω (pow_nonneg hs n))]
  refine ⟨fun a ha ↦ ?_, fun b hb ↦ ?_⟩
  · -- `δ ↦ ωₙ (1 - δ)ⁿ` is continuous with value `ωₙ > a` at `0`, so some `δ ∈ (0, 1)` has
    -- `a < ωₙ (1 - δ)ⁿ`.
    have hlim : Tendsto (fun δ : ℝ ↦ omega n * (1 - δ) ^ n) (𝓝[>] 0) (𝓝 (omega n)) := by
      have h0 : Tendsto (fun δ : ℝ ↦ omega n * (1 - δ) ^ n) (𝓝 0) (𝓝 (omega n * (1 - 0) ^ n)) :=
        (by fun_prop : Continuous fun δ : ℝ ↦ omega n * (1 - δ) ^ n).tendsto 0
      rw [sub_zero, one_pow, mul_one] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    obtain ⟨δ, hδa, hδ⟩ := ((hlim.eventually_const_lt ha).and (Ioo_mem_nhdsGT one_pos)).exists
    -- `g = min 1 (max 0 ((1 - ‖y‖) / δ))` vanishes off `B_1(0)` and is `1` on `B_{1-δ}(0)`.
    set φ : Ambient n ℓ → ℝ := fun y ↦ min 1 (max 0 ((1 - ‖y‖) / δ)) with hφ
    have hφ0 : ∀ y : Ambient n ℓ, 1 < ‖y‖ → φ y = 0 := by
      intro y hy
      have : (1 - ‖y‖) / δ < 0 := div_neg_of_neg_of_pos (by linarith) hδ.1
      simp only [hφ, max_eq_left this.le, min_eq_right zero_le_one]
    have hφs : HasCompactSupport φ :=
      HasCompactSupport.intro (isCompact_closedBall (0 : Ambient n ℓ) 1) fun y hy ↦
        hφ0 y (by simpa [mem_closedBall, dist_zero_right] using hy)
    let g : C_c(Ambient n ℓ, ℝ) := ⟨⟨φ, by fun_prop⟩, hφs⟩
    have hg : ∀ y, g y = φ y := fun y ↦ rfl
    have hle : (closedBall (0 : Ambient n ℓ) (1 - δ)).indicator (1 : Ambient n ℓ → ℝ) ≤ g := by
      intro y
      by_cases hy : y ∈ closedBall (0 : Ambient n ℓ) (1 - δ)
      · rw [Set.indicator_of_mem hy, Pi.one_apply, hg]
        have hy' : ‖y‖ ≤ 1 - δ := by simpa [mem_closedBall, dist_zero_right] using hy
        have h1 : 1 ≤ (1 - ‖y‖) / δ := by
          rw [le_div_iff₀ hδ.1]
          linarith
        simp only [hφ, max_eq_right (zero_le_one.trans h1), min_eq_left h1, le_refl]
      · rw [Set.indicator_of_notMem hy, hg]
        exact le_min zero_le_one (le_max_left _ _)
    have hδ1 : 0 ≤ 1 - δ := by linarith [hδ.2]
    refine ⟨g, fun y ↦ ?_, fun y hy ↦ ?_, ?_⟩
    · rw [hg]
      exact min_le_left _ _
    · rw [hg, hφ0 y hy]
    · calc a < omega n * (1 - δ) ^ n := hδa
        _ = ∫ y, (closedBall (0 : Ambient n ℓ) (1 - δ)).indicator 1 y ∂ν := (hball _ hδ1).2.symm
        _ ≤ ∫ y, g y ∂ν := integral_mono (hball _ hδ1).1 g.integrable hle
  · -- `δ ↦ ωₙ (1 + δ)ⁿ` is continuous with value `ωₙ < b` at `0`, so some `δ ∈ (0, 1)` has
    -- `ωₙ (1 + δ)ⁿ < b`.
    have hlim : Tendsto (fun δ : ℝ ↦ omega n * (1 + δ) ^ n) (𝓝[>] 0) (𝓝 (omega n)) := by
      have h0 : Tendsto (fun δ : ℝ ↦ omega n * (1 + δ) ^ n) (𝓝 0) (𝓝 (omega n * (1 + 0) ^ n)) :=
        (by fun_prop : Continuous fun δ : ℝ ↦ omega n * (1 + δ) ^ n).tendsto 0
      rw [add_zero, one_pow, mul_one] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    obtain ⟨δ, hδb, hδ⟩ := ((hlim.eventually_lt_const hb).and (Ioo_mem_nhdsGT one_pos)).exists
    -- `h = min 1 (max 0 ((1 + δ - ‖y‖) / δ))` vanishes off `B_{1+δ}(0)` and is `1` on `B_1(0)`.
    set φ : Ambient n ℓ → ℝ := fun y ↦ min 1 (max 0 ((1 + δ - ‖y‖) / δ)) with hφ
    have hφ0 : ∀ y : Ambient n ℓ, 1 + δ < ‖y‖ → φ y = 0 := by
      intro y hy
      have : (1 + δ - ‖y‖) / δ < 0 := div_neg_of_neg_of_pos (by linarith) hδ.1
      simp only [hφ, max_eq_left this.le, min_eq_right zero_le_one]
    have hφs : HasCompactSupport φ :=
      HasCompactSupport.intro (isCompact_closedBall (0 : Ambient n ℓ) (1 + δ)) fun y hy ↦
        hφ0 y (by simpa [mem_closedBall, dist_zero_right] using hy)
    let h : C_c(Ambient n ℓ, ℝ) := ⟨⟨φ, by fun_prop⟩, hφs⟩
    have hh : ∀ y, h y = φ y := fun y ↦ rfl
    have hle : (h : Ambient n ℓ → ℝ) ≤ (closedBall (0 : Ambient n ℓ) (1 + δ)).indicator 1 := by
      intro y
      by_cases hy : y ∈ closedBall (0 : Ambient n ℓ) (1 + δ)
      · rw [Set.indicator_of_mem hy, Pi.one_apply, hh]
        exact min_le_left _ _
      · rw [Set.indicator_of_notMem hy, hh,
          hφ0 y (by simpa [mem_closedBall, dist_zero_right] using hy)]
    have hδ1 : 0 ≤ 1 + δ := by linarith [hδ.1]
    refine ⟨h, fun y ↦ ?_, fun y hy ↦ ?_, ?_⟩
    · rw [hh]
      exact le_min zero_le_one (le_max_left _ _)
    · rw [hh]
      have h1 : 1 ≤ (1 + δ - ‖y‖) / δ := by
        rw [le_div_iff₀ hδ.1]
        linarith
      simp only [hφ, max_eq_right (zero_le_one.trans h1), min_eq_left h1, le_refl]
    · calc ∫ y, h y ∂ν ≤ ∫ y, (closedBall (0 : Ambient n ℓ) (1 + δ)).indicator 1 y ∂ν :=
            integral_mono h.integrable (hball _ hδ1).1 hle
        _ = omega n * (1 + δ) ^ n := (hball _ hδ1).2
        _ < b := hδb

/-- Simon Ch. 3, Remark 1.8(2) (p. 75), with closed balls: if `dim P = n`, `c > 0` and
`t⁻ⁿ ∫ f(t⁻¹(y - x)) dμ(y) → c ∫_P f dHⁿ` as `t ↓ 0` for every `f ∈ C_c`, then
`μ(B_ρ(x)) / (ωₙ ρⁿ) → c` as `ρ ↓ 0`. -/
theorem Submission.ts_blowup_closedBall_density : ∀ (n ℓ : ℕ) (μ : Measure (Ambient n ℓ)) (x : Ambient n ℓ) (P : Submodule ℝ (Ambient n ℓ)) (c : ℝ), 0 < n → IsFiniteMeasureOnCompacts μ → Module.finrank ℝ P = n → 0 < c → (∀ f : C_c(Ambient n ℓ, ℝ), Tendsto (fun t : ℝ ↦ (t ^ n)⁻¹ * ∫ y, f (t⁻¹ • (y - x)) ∂μ) (𝓝[>] 0) (𝓝 (c * ∫ y in (P : Set (Ambient n ℓ)), f y ∂μHE[n]))) → Tendsto (fun ρ : ℝ ↦ μ.real (closedBall x ρ) / (omega n * ρ ^ n)) (𝓝[>] 0) (𝓝 c) := by
  intro n ℓ μ x P c _ hμ hP hc hlim
  -- `ωₙ > 0`: the unit ball of `ℝⁿ` is nonempty, open and bounded.
  have hω : 0 < omega n :=
    ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne
  -- `t⁻ⁿ μ(B_t(x)) → c ωₙ`: it is squeezed between blow-up integrals of cut-offs.
  have hL : Tendsto (fun t : ℝ ↦ (t ^ n)⁻¹ * μ.real (closedBall x t)) (𝓝[>] 0)
      (𝓝 (c * omega n)) := by
    refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun b hb ↦ ?_⟩
    · -- A cut-off `g ≤ 1_{B_1(0)}` with `a < c ∫_P g dHⁿ`.
      obtain ⟨g, hg1, hg0, hgP⟩ := (Submission.ts_unit_ball_plane_cutoff_approx n ℓ P hP).1
        (a / c) ((div_lt_iff₀ hc).2 (by rwa [mul_comm]))
      rw [div_lt_iff₀ hc, mul_comm] at hgP
      filter_upwards [(hlim g).eventually (lt_mem_nhds hgP), self_mem_nhdsWithin]
        with t ht (ht0 : 0 < t)
      exact ht.trans_le (mul_le_mul_of_nonneg_left
        ((Submission.ts_blowup_cutoff_closedBall_bounds n ℓ μ x g t hμ ht0).1 hg1 hg0)
        (inv_nonneg.2 (pow_nonneg ht0.le n)))
    · -- A cut-off `h ≥ 1_{B_1(0)}` with `c ∫_P h dHⁿ < b`.
      obtain ⟨h, hh0, hh1, hhP⟩ := (Submission.ts_unit_ball_plane_cutoff_approx n ℓ P hP).2
        (b / c) ((lt_div_iff₀ hc).2 (by rwa [mul_comm]))
      rw [lt_div_iff₀ hc, mul_comm] at hhP
      filter_upwards [(hlim h).eventually (gt_mem_nhds hhP), self_mem_nhdsWithin]
        with t ht (ht0 : 0 < t)
      exact (mul_le_mul_of_nonneg_left
        ((Submission.ts_blowup_cutoff_closedBall_bounds n ℓ μ x h t hμ ht0).2 hh0 hh1)
        (inv_nonneg.2 (pow_nonneg ht0.le n))).trans_lt ht
  -- Divide by `ωₙ ≠ 0`.
  have hdiv := hL.div_const (omega n)
  rw [mul_div_cancel_right₀ c hω.ne'] at hdiv
  exact hdiv.congr fun ρ ↦ by ring
/-- Simon Ch. 3, 1.7 and Ch. 4, 1.3 (pp. 75, 86): for `V = v(M, θ)` and `λ > 0`, the change of
variables `y ↦ λ⁻¹(y - x)` gives
`λ⁻ⁿ ∫ f(λ⁻¹(y - x)) dμ_V(y) = ∫_{η_{x,λ}(M)} f(y) θ(x + λy) dHⁿ(y)`. So if `dim P = n` and the
left side tends to `θ(x) ∫_P f dHⁿ` for every `f ∈ C_c`, then `P` is the approximate tangent
space of `M` with respect to `θ` at `x`. -/
theorem Submission.ts_blowup_weighted_tangent : ∀ (n ℓ : ℕ) (a : RectifiablePair n ℓ) (x : Ambient n ℓ) (P : Submodule ℝ (Ambient n ℓ)), Module.finrank ℝ P = n → (∀ f : C_c(Ambient n ℓ, ℝ), Tendsto (fun t : ℝ ↦ (t ^ n)⁻¹ * ∫ y, f (t⁻¹ • (y - x)) ∂(mk a).weight) (𝓝[>] 0) (𝓝 (a.θ x * ∫ y in (P : Set (Ambient n ℓ)), f y ∂μHE[n]))) → Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n a.M a.θ x P := by
  intro n ℓ a x P hP hlim
  -- `θ` is a.e.-strongly measurable on `M = ⋃ₖ M ∩ B_k(0)`: it is integrable on each piece.
  have hθ : AEStronglyMeasurable a.θ ((μHE[n] : Measure (Ambient n ℓ)).restrict a.M) := by
    have hM : a.M = ⋃ k : ℕ, a.M ∩ closedBall (0 : Ambient n ℓ) k := by
      ext y
      simp only [mem_iUnion, mem_inter_iff, mem_closedBall, dist_zero_right]
      exact ⟨fun hy ↦ ⟨⌈‖y‖⌉₊, hy, Nat.le_ceil _⟩, fun ⟨_, hy, _⟩ ↦ hy⟩
    rw [hM, aestronglyMeasurable_iUnion_iff]
    exact fun k ↦
      (a.isRectifiablePair.locallyIntegrable _ (isCompact_closedBall 0 k)).aestronglyMeasurable
  -- `∫ h dμ_V = ∫_M h θ dHⁿ` for every `h`.
  have hweight : ∀ h : Ambient n ℓ → ℝ,
      ∫ y, h y ∂(mk a).weight = ∫ y in a.M, h y * a.θ y ∂μHE[n] := by
    intro h
    have hw : (mk a).weight = ((μHE[n] : Measure (Ambient n ℓ)).restrict a.M).withDensity
        fun y ↦ ENNReal.ofReal (a.θ y) := rfl
    rw [hw, integral_withDensity_eq_integral_toReal_smul₀ hθ.aemeasurable.ennreal_ofReal
      (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top) h]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem₀ a.isRectifiablePair.measurable] with y hy
    rw [ENNReal.toReal_ofReal (a.isRectifiablePair.pos y hy).le, smul_eq_mul, mul_comm]
  -- Change of variables under `η_{x,r} = e⁻¹`, where `e : y ↦ x + r y`.
  have hcov : ∀ r : ℝ, 0 < r → ∀ g : Ambient n ℓ → ℝ,
      ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' a.M, g y * a.θ (x + r • y) ∂μHE[n] =
        (r ^ n)⁻¹ * ∫ y, g (r⁻¹ • (y - x)) ∂(mk a).weight := by
    intro r hr g
    let e : Ambient n ℓ ≃ₜ Ambient n ℓ :=
      { toFun := fun y ↦ x + r • y
        invFun := fun y ↦ r⁻¹ • (y - x)
        left_inv := fun y ↦ by simp [smul_smul, hr.ne']
        right_inv := fun y ↦ by simp [smul_smul, hr.ne']
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    change ∫ y in e.symm '' a.M, g y * a.θ (e y) ∂μHE[n] = _
    -- `Hⁿ(η_{x,r}(S)) = r⁻ⁿ Hⁿ(S)`: a translation followed by the dilation by `r⁻¹`.
    have hshift : Isometry (fun y : Ambient n ℓ ↦ y - x) := by
      apply Isometry.of_dist_eq
      intro y z
      simp only [dist_eq_norm]
      congr 1
      abel
    have hscale : ∀ S : Set (Ambient n ℓ), (μHE[n] : Measure (Ambient n ℓ)) (e.symm '' S) =
        ENNReal.ofReal (r⁻¹) ^ n * (μHE[n] : Measure (Ambient n ℓ)) S := by
      intro S
      have himage : e.symm '' S =
          AffineMap.homothety (0 : Ambient n ℓ) r⁻¹ '' ((fun y ↦ y - x) '' S) := by
        rw [image_image]
        congr 1
        funext y
        simp [e, AffineMap.homothety_apply]
      rw [himage,
        euclideanHausdorffMeasure_homothety_image n (0 : Ambient n ℓ) (inv_ne_zero hr.ne'),
        hshift.euclideanHausdorffMeasure_image, ENNReal.smul_def, ENNReal.coe_pow,
        ← ENNReal.ofReal_coe_nnreal, coe_nnnorm, Real.norm_of_nonneg (inv_pos.mpr hr).le]
      rfl
    -- Pushing `Hⁿ ⌞ η_{x,r}(M)` forward by `e` gives `r⁻ⁿ Hⁿ ⌞ M`.
    have hmap : ((μHE[n] : Measure (Ambient n ℓ)).restrict (e.symm '' a.M)).map e =
        ENNReal.ofReal (r⁻¹) ^ n • (μHE[n] : Measure (Ambient n ℓ)).restrict a.M := by
      ext A hA
      rw [Measure.map_apply e.continuous.measurable hA,
        Measure.restrict_apply (e.continuous.measurable hA), Measure.smul_apply,
        Measure.restrict_apply hA, smul_eq_mul]
      have hset : e ⁻¹' A ∩ e.symm '' a.M = e.symm '' (A ∩ a.M) := by
        ext z
        constructor
        · rintro ⟨hz, y, hy, rfl⟩
          exact ⟨y, ⟨by simpa only [mem_preimage, e.apply_symm_apply] using hz, hy⟩, rfl⟩
        · rintro ⟨y, ⟨hyA, hyM⟩, rfl⟩
          exact ⟨by simpa only [mem_preimage, e.apply_symm_apply] using hyA, y, hyM, rfl⟩
      rw [hset, hscale]
    have hi := e.measurableEmbedding.integral_map
      (μ := (μHE[n] : Measure (Ambient n ℓ)).restrict (e.symm '' a.M))
      (fun z ↦ g (e.symm z) * a.θ z)
    rw [hmap, integral_smul_measure, ENNReal.toReal_pow, ENNReal.toReal_ofReal (inv_pos.mpr hr).le,
      smul_eq_mul] at hi
    simp only [e.symm_apply_apply] at hi
    rw [hweight, ← inv_pow]
    exact hi.symm
  -- The two blow-up functions agree on `(0, ∞) ∈ 𝓝[>] 0`.
  refine ⟨hP, fun f ↦ (hlim f).congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (hcov r hr f).symm
/-- **Countable gluing of image integrals.** Let `f : X → X` be injective and map `μ`-null sets to
`μ`-null sets and `μ`-null-measurable sets to `μ`-null-measurable sets. If the pairwise disjoint
measurable sets `D i` cover the `μ`-null-measurable set `Z` up to a `μ`-null set and
`∫_{f(Z ∩ D i)} u dμ = ∫_{Z ∩ D i} g dμ` for every `i`, then `∫_{f(Z)} u dμ = ∫_Z g dμ`. -/
theorem Submission.ts_fv_lintegral_image_eq_of_pieces : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (f : X → X) (Z : Set X) (D : ℕ → Set X) (u g : X → ℝ≥0∞), Function.Injective f → (∀ Y : Set X, μ Y = 0 → μ (f '' Y) = 0) → (∀ Y : Set X, NullMeasurableSet Y μ → NullMeasurableSet (f '' Y) μ) → NullMeasurableSet Z μ → (∀ i, MeasurableSet (D i)) → Pairwise (fun i j ↦ Disjoint (D i) (D j)) → μ (Z \ ⋃ i, D i) = 0 → (∀ i, ∫⁻ y in f '' (Z ∩ D i), u y ∂μ = ∫⁻ x in Z ∩ D i, g x ∂μ) → ∫⁻ y in f '' Z, u y ∂μ = ∫⁻ x in Z, g x ∂μ := by
  intro X _ μ f Z D u g hf hnull hnm hZ hD hdisj hrem hpiece
  -- `Z =ᵐ ⋃ i, Z ∩ D i`: the remainder `Z \ ⋃ i, (Z ∩ D i) = Z \ ⋃ i, D i` is null.
  have hrem' : Z \ ⋃ i, (Z ∩ D i) = Z \ ⋃ i, D i := by
    rw [← Set.inter_iUnion, Set.sdiff_self_inter]
  have hsub : ⋃ i, (Z ∩ D i) ⊆ Z := Set.iUnion_subset fun i ↦ Set.inter_subset_left
  have hZae : Z =ᵐ[μ] ⋃ i, (Z ∩ D i) := by
    refine ae_eq_set.2 ⟨by rw [hrem']; exact hrem, ?_⟩
    rw [Set.sdiff_eq_empty.2 hsub]
    exact measure_empty
  -- `f(Z) =ᵐ ⋃ i, f(Z ∩ D i)`: the remainder is `f(Z \ ⋃ i, D i)`, null since `f` keeps null sets.
  have hfZae : f '' Z =ᵐ[μ] ⋃ i, f '' (Z ∩ D i) := by
    rw [← Set.image_iUnion]
    refine ae_eq_set.2 ⟨?_, ?_⟩
    · rw [← Set.image_sdiff hf, hrem']
      exact hnull _ hrem
    · rw [Set.sdiff_eq_empty.2 (Set.image_mono hsub)]
      exact measure_empty
  -- The pieces are null-measurable and pairwise disjoint; so are their images (`f` injective).
  have hm : ∀ i, NullMeasurableSet (Z ∩ D i) μ := fun i ↦ hZ.inter (hD i).nullMeasurableSet
  have hd : ∀ i j, i ≠ j → Disjoint (Z ∩ D i) (Z ∩ D j) := fun i j hij ↦
    (hdisj hij).mono Set.inter_subset_right Set.inter_subset_right
  -- Sum the piecewise identities over both countable decompositions.
  calc ∫⁻ y in f '' Z, u y ∂μ = ∫⁻ y in ⋃ i, f '' (Z ∩ D i), u y ∂μ := setLIntegral_congr hfZae
    _ = ∑' i, ∫⁻ y in f '' (Z ∩ D i), u y ∂μ :=
        lintegral_iUnion₀ (fun i ↦ hnm _ (hm i))
          (fun i j hij ↦ (Set.disjoint_image_of_injective hf (hd i j hij)).aedisjoint) u
    _ = ∑' i, ∫⁻ x in Z ∩ D i, g x ∂μ := tsum_congr hpiece
    _ = ∫⁻ x in ⋃ i, (Z ∩ D i), g x ∂μ :=
        (lintegral_iUnion₀ hm (fun i j hij ↦ (hd i j hij).aedisjoint) g).symm
    _ = ∫⁻ x in Z, g x ∂μ := setLIntegral_congr hZae.symm

/-- **Image mass by the area formula on Lipschitz pieces (Simon Ch. 4, 1.5–1.7).** Let the carrier
`M` of `a = (M, θ)` be covered, up to the `Hⁿ`-null Borel set `N₀`, by the images `F i (C i)` of
compact sets under Lipschitz maps injective on `C i`, with `T_x V = range DF i (w)` whenever
`F i (w) = x`, for `Hⁿ`-a.e. `x ∈ M`. If `f` is injective, Lipschitz and differentiable, then
`M(f_#(V ⌞ K)) = ∫_{M ∩ K} θ jac(Df, T_x V) dHⁿ`, with
`jac(Λ, P) = √det(⟪Λ p eᵢ, Λ p eⱼ⟫ + ⟪q eᵢ, q eⱼ⟫)` the tangential Jacobian of `Λ` along `P`.
The cover is disjointified into the Borel sets `D i = F i (C i) \ (N₀ ∪ ⋃_{j < i} F j (C j))`;
`ts_fv_piece_image_area_formula` applies to a Borel hull of each piece `M ∩ K ∩ D i` inside `D i`,
and `ts_fv_lintegral_image_eq_of_pieces` glues the pieces. -/
theorem Submission.ts_fv_image_mass_area_formula : ∀ (n ℓ : ℕ) (a : RectifiablePair n ℓ) (N₀ : Set (Ambient n ℓ)) (C : ℕ → Set (EuclideanSpace ℝ (Fin n))) (F : ℕ → EuclideanSpace ℝ (Fin n) → Ambient n ℓ) (f : Ambient n ℓ → Ambient n ℓ) (K : Set (Ambient n ℓ)), 0 < n → MeasurableSet N₀ → (μHE[n] : Measure (Ambient n ℓ)) N₀ = 0 → a.M ⊆ N₀ ∪ ⋃ i, F i '' C i → (∀ i, IsCompact (C i) ∧ (∃ K : NNReal, LipschitzWith K (F i)) ∧ (∀ w ∈ C i, DifferentiableAt ℝ (F i) w ∧ Function.Injective (fderiv ℝ (F i) w)) ∧ ContinuousOn (fderiv ℝ (F i)) (C i) ∧ ∃ c : ℝ, 0 < c ∧ ∀ v ∈ C i, ∀ w ∈ C i, c * ‖v - w‖ ≤ ‖F i v - F i w‖) → (∀ᵐ x ∂(μHE[n] : Measure (Ambient n ℓ)).restrict a.M, ∀ i, ∀ w ∈ C i, F i w = x → (mk a).tangentSpace x = LinearMap.range (fderiv ℝ (F i) w).toLinearMap) → Function.Injective f → (∃ L : NNReal, LipschitzWith L f) → (∀ y, DifferentiableAt ℝ f y) → MeasurableSet K → imageMass a f K = ∫⁻ x in a.M ∩ K, ENNReal.ofReal (a.θ x * Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (n + ℓ) ↦ inner ℝ (fderiv ℝ f x (((mk a).tangentSpace x).starProjection (EuclideanSpace.single i (1 : ℝ)))) (fderiv ℝ f x (((mk a).tangentSpace x).starProjection (EuclideanSpace.single j (1 : ℝ)))) + inner ℝ (EuclideanSpace.single i (1 : ℝ) - ((mk a).tangentSpace x).starProjection (EuclideanSpace.single i (1 : ℝ))) (EuclideanSpace.single j (1 : ℝ) - ((mk a).tangentSpace x).starProjection (EuclideanSpace.single j (1 : ℝ)))))) ∂μHE[n] := by
  intro n ℓ a N₀ C F f K _hn hN₀ hN₀0 hcover hpieces htan hfinj hfLip hfdiff hK
  obtain ⟨L, hL⟩ := hfLip
  -- `jac P y = √det(⟪Df(y) p eᵢ, Df(y) p eⱼ⟫ + ⟪q eᵢ, q eⱼ⟫)`, `p = P.starProjection`, `q = 1 - p`
  let jac : Submodule ℝ (Ambient n ℓ) → Ambient n ℓ → ℝ := fun P y ↦
    Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (n + ℓ) ↦
      inner ℝ (fderiv ℝ f y (P.starProjection (EuclideanSpace.single i (1 : ℝ))))
          (fderiv ℝ f y (P.starProjection (EuclideanSpace.single j (1 : ℝ)))) +
        inner ℝ
          (EuclideanSpace.single i (1 : ℝ) - P.starProjection (EuclideanSpace.single i (1 : ℝ)))
          (EuclideanSpace.single j (1 : ℝ) - P.starProjection (EuclideanSpace.single j (1 : ℝ)))))
  -- the density `u = θ ∘ f⁻¹` of the image and the density `g = θ jac(Df, T)` on `M`
  let u : Ambient n ℓ → ℝ≥0∞ := fun y ↦ ENNReal.ofReal (a.θ (Function.invFun f y))
  let g : Ambient n ℓ → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (a.θ x * jac ((mk a).tangentSpace x) x)
  show ∫⁻ y in f '' (a.M ∩ K), u y ∂μHE[n] = ∫⁻ x in a.M ∩ K, g x ∂μHE[n]
  -- `f` maps `Hⁿ`-null sets to null sets (it is Lipschitz) and Borel sets to Borel sets
  -- (Lusin–Souslin), hence null-measurable sets to null-measurable sets
  have hnull : ∀ Y : Set (Ambient n ℓ), (μHE[n] : Measure (Ambient n ℓ)) Y = 0 →
      (μHE[n] : Measure (Ambient n ℓ)) (f '' Y) = 0 := fun Y hY ↦
    le_antisymm ((Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
      hL.lipschitzOnWith).trans (by rw [hY, mul_zero])) bot_le
  have hnm : ∀ Y : Set (Ambient n ℓ), NullMeasurableSet Y (μHE[n] : Measure (Ambient n ℓ)) →
      NullMeasurableSet (f '' Y) (μHE[n] : Measure (Ambient n ℓ)) := by
    intro Y hY
    obtain ⟨Y₀, hY₀Y, hY₀, hY₀ae⟩ := hY.exists_measurable_subset_ae_eq
    rw [← Set.union_sdiff_cancel hY₀Y, Set.image_union]
    exact (hY₀.image_of_continuousOn_injOn hL.continuous.continuousOn
      hfinj.injOn).nullMeasurableSet.union
        (NullMeasurableSet.of_null (hnull _ (ae_le_set.1 hY₀ae.symm.le)))
  -- disjointify the cover: the Borel sets `D i = F i (C i) \ (N₀ ∪ ⋃_{j < i} F j (C j))`
  have hFC : ∀ i, MeasurableSet (F i '' C i) := fun i ↦ by
    obtain ⟨hCc, ⟨LF, hLF⟩, -⟩ := hpieces i
    exact (hCc.image hLF.continuous).measurableSet
  let D : ℕ → Set (Ambient n ℓ) := fun i ↦ F i '' C i \ (N₀ ∪ ⋃ j : Fin i, F j '' C j)
  have hDm : ∀ i, MeasurableSet (D i) := fun i ↦
    (hFC i).diff (hN₀.union (MeasurableSet.iUnion fun j : Fin i ↦ hFC j))
  have hDsub : ∀ i, D i ⊆ F i '' C i := fun _ ↦ Set.sdiff_subset
  have hDdisj : Pairwise fun i j ↦ Disjoint (D i) (D j) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact Set.disjoint_left.2 fun x hxi hxj ↦ hxj.2 (Or.inr (Set.mem_iUnion.2 ⟨⟨i, h⟩, hxi.1⟩))
    · exact Set.disjoint_left.2 fun x hxi hxj ↦ hxi.2 (Or.inr (Set.mem_iUnion.2 ⟨⟨j, h⟩, hxj.1⟩))
  -- the `D i` cover `(M ∩ K) \ N₀`: a point of `M \ N₀` lies in `D i` for the least `i` with
  -- `x ∈ F i (C i)`
  have hrem : (μHE[n] : Measure (Ambient n ℓ)) ((a.M ∩ K) \ ⋃ i, D i) = 0 := by
    classical
    refine measure_mono_null (fun x hx ↦ ?_) hN₀0
    by_contra hxN
    have hex : ∃ i, x ∈ F i '' C i := Set.mem_iUnion.1 (Or.resolve_left (hcover hx.1.1) hxN)
    refine hx.2 (Set.mem_iUnion.2 ⟨Nat.find hex, Nat.find_spec hex, ?_⟩)
    rintro (h | h)
    · exact hxN h
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 h
      exact Nat.find_min hex j.2 hj
  refine Submission.ts_fv_lintegral_image_eq_of_pieces (Ambient n ℓ) μHE[n] f (a.M ∩ K) D u g
    hfinj hnull hnm (a.isRectifiablePair.measurable.inter hK.nullMeasurableSet) hDm hDdisj hrem
    fun i ↦ ?_
  -- the piece `M ∩ K ∩ D i`
  obtain ⟨hCc, ⟨LF, hLF⟩, hdiff, -, c, hc, hlow⟩ := hpieces i
  -- `F i` is injective on `C i` by the lower bound `c ‖v - w‖ ≤ ‖F i v - F i w‖`
  have hinj : Set.InjOn (F i) (C i) := fun v hv w hw hvw ↦ by
    by_contra hne
    have h := hlow v hv w hw
    rw [hvw, sub_self, norm_zero] at h
    exact not_le.2 (mul_pos hc (norm_pos_iff.2 (sub_ne_zero.2 hne))) h
  -- a Borel hull `A' ∩ D i` of the piece, which differs from it by an `Hⁿ`-null set
  have hZnm : NullMeasurableSet (a.M ∩ K ∩ D i) (μHE[n] : Measure (Ambient n ℓ)) :=
    (a.isRectifiablePair.measurable.inter hK.nullMeasurableSet).inter (hDm i).nullMeasurableSet
  obtain ⟨A', hA'Z, hA', hA'ae⟩ := hZnm.exists_measurable_superset_ae_eq
  have hZA : a.M ∩ K ∩ D i ⊆ A' ∩ D i := fun x hx ↦ ⟨hA'Z hx, hx.2⟩
  have hAZ : (μHE[n] : Measure (Ambient n ℓ)) ((A' ∩ D i) \ (a.M ∩ K ∩ D i)) = 0 :=
    measure_mono_null (Set.sdiff_subset_sdiff_left Set.inter_subset_left) (ae_le_set.1 hA'ae.le)
  have hAae : A' ∩ D i =ᵐ[(μHE[n] : Measure (Ambient n ℓ))] a.M ∩ K ∩ D i :=
    ae_eq_set.2 ⟨hAZ, by rw [Set.sdiff_eq_empty.2 hZA, measure_empty]⟩
  have hfAae : f '' (A' ∩ D i) =ᵐ[(μHE[n] : Measure (Ambient n ℓ))] f '' (a.M ∩ K ∩ D i) :=
    ae_eq_set.2 ⟨by rw [← Set.image_sdiff hfinj]; exact hnull _ hAZ,
      by rw [Set.sdiff_eq_empty.2 (Set.image_mono hZA), measure_empty]⟩
  -- the area formula on the hull, with the tangent planes `P y = range DF i (F i⁻¹ y)`
  let P : Ambient n ℓ → Submodule ℝ (Ambient n ℓ) := fun y ↦
    LinearMap.range (fderiv ℝ (F i) (Function.invFunOn (F i) (C i) y)).toLinearMap
  have harea : ∫⁻ y in f '' (A' ∩ D i), u y ∂μHE[n] =
      ∫⁻ y in A' ∩ D i, ENNReal.ofReal (jac (P y) y) * u (f y) ∂μHE[n] :=
    Submission.ts_fv_piece_image_area_formula n ℓ (C i) (F i) f (A' ∩ D i) P u hCc.measurableSet
      ⟨LF, hLF⟩ (fun v hv ↦ (hdiff v hv).1) hinj ⟨L, hL⟩ hfinj.injOn (fun y _ ↦ hfdiff y)
      (hA'.inter (hDm i)) (Set.inter_subset_right.trans (hDsub i)) fun v hv _ ↦ by
        show LinearMap.range
          (fderiv ℝ (F i) (Function.invFunOn (F i) (C i) (F i v))).toLinearMap = _
        rw [hinj.leftInvOn_invFunOn hv]
  rw [setLIntegral_congr hfAae.symm, harea, setLIntegral_congr hAae]
  -- on the piece, `P x = T_x V` a.e. by the tangent hypothesis, and `u (f x) = θ x`
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_mem₀ hZnm,
    ae_restrict_of_ae_restrict_of_subset (fun x hx ↦ hx.1.1 : a.M ∩ K ∩ D i ⊆ a.M) htan]
    with x hx htx
  have hxC : x ∈ F i '' C i := hDsub i hx.2
  have hT : (mk a).tangentSpace x = P x :=
    htx i _ (Function.invFunOn_mem hxC) (Function.invFunOn_eq hxC)
  have hjac : 0 ≤ jac (P x) x := Real.sqrt_nonneg _
  show ENNReal.ofReal (jac (P x) x) * ENNReal.ofReal (a.θ (Function.invFun f (f x))) =
    ENNReal.ofReal (a.θ x * jac ((mk a).tangentSpace x) x)
  rw [Function.leftInverse_invFun hfinj x, hT, ENNReal.ofReal_mul' hjac, mul_comm]
/-- **Determinant lower bound for a coercive symmetric matrix** (used for Simon Ch. 4, 2.2). If
`S` is a real symmetric `N × N` matrix and `c ∑ᵢ ξᵢ² ≤ ∑ᵢ ∑ⱼ ξᵢ Sᵢⱼ ξⱼ` for every `ξ`, with
`c ≥ 0`, then `cᴺ ≤ det S`. Induction on `N`: testing `ξ = e₀` gives `c ≤ S₀₀`; if `S₀₀ > 0`,
row operations give `det S = S₀₀ · det S'` for the Schur complement
`S'ᵢⱼ = S_{i+1,j+1} - S_{i+1,0} S_{0,j+1} / S₀₀`, which is again symmetric and `c`-coercive; if
`S₀₀ = 0`, then `c = 0` and the first row of `S` vanishes. -/
theorem Submission.ts_fv_det_ge_pow_of_quadForm_ge : (∀ (N : ℕ) (S : Matrix (Fin N) (Fin N) ℝ) (c : ℝ), 0 ≤ c → (∀ i j, S i j = S j i) → (∀ ξ : Fin N → ℝ, c * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, ξ i * S i j * ξ j) → c ^ N ≤ S.det) := by
  intro N
  induction N with
  | zero =>
    intro S c _ _ _
    simp [Matrix.det_isEmpty]
  | succ n ih =>
    intro S c hc hsym hq
    -- Split `ξ = (t, η)` along the first coordinate.
    have hnorm : ∀ (t : ℝ) (η : Fin n → ℝ),
        ∑ i, (Fin.cons t η : Fin (n + 1) → ℝ) i ^ 2 = t ^ 2 + ∑ i, η i ^ 2 := by
      intro t η
      simp [Fin.sum_univ_succ]
    have hexp : ∀ (t : ℝ) (η : Fin n → ℝ),
        ∑ i, ∑ j, (Fin.cons t η : Fin (n + 1) → ℝ) i * S i j * (Fin.cons t η : Fin (n + 1) → ℝ) j =
          S 0 0 * t ^ 2 + 2 * t * ∑ j, S 0 j.succ * η j +
            ∑ i, ∑ j, η i * S i.succ j.succ * η j := by
      intro t η
      simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      have h1 : ∑ i : Fin n, η i * S i.succ 0 * t = t * ∑ j, S 0 j.succ * η j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hsym]
        ring
      have h2 : ∑ j : Fin n, t * S 0 j.succ * η j = t * ∑ j, S 0 j.succ * η j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [Finset.sum_add_distrib, h1, h2]
      ring
    -- `ξ = e₀` gives `c ≤ S 0 0`.
    have hca : c ≤ S 0 0 := by
      have h := hq (Fin.cons 1 0)
      rw [hnorm, hexp] at h
      simpa using h
    rcases (hc.trans hca).lt_or_eq with hapos | ha0
    · -- `S 0 0 > 0`: pass to the Schur complement `S'` of the pivot `S 0 0`.
      have ha : S 0 0 ≠ 0 := hapos.ne'
      obtain ⟨S', hS'⟩ : ∃ S' : Matrix (Fin n) (Fin n) ℝ,
          S' = Matrix.of fun i j => S i.succ j.succ - S i.succ 0 * S 0 j.succ / S 0 0 := ⟨_, rfl⟩
      have hS'ij : ∀ i j, S' i j = S i.succ j.succ - S i.succ 0 * S 0 j.succ / S 0 0 := by
        intro i j
        rw [hS']
        rfl
      -- Row operations clear the first column below the pivot: `det S = S 0 0 * det S'`.
      have hdet : S.det = S 0 0 * S'.det := by
        let T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := Matrix.of fun i j =>
          S i j + (Fin.cons 0 fun i' => -(S i'.succ 0 / S 0 0) : Fin (n + 1) → ℝ) i * S 0 j
        have hT : T.det = S.det :=
          Matrix.det_eq_of_forall_row_eq_smul_add_const _ 0 (Fin.cons_zero _ _) fun _ _ => rfl
        have hcol : ∀ i : Fin n, T i.succ 0 = 0 := by
          intro i
          simp only [T, Matrix.of_apply, Fin.cons_succ]
          field_simp
          ring
        have hsub : T.submatrix (Fin.succAbove 0) Fin.succ = S' := by
          ext i j
          simp only [T, Matrix.submatrix_apply, Fin.succAbove_zero, Matrix.of_apply, Fin.cons_succ,
            hS'ij]
          ring
        rw [← hT, Matrix.det_succ_column_zero, Fin.sum_univ_succ]
        simp only [hcol, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, hsub]
        simp [T]
      -- `S'` is symmetric.
      have hS'sym : ∀ i j, S' i j = S' j i := by
        intro i j
        rw [hS'ij, hS'ij, hsym i.succ j.succ, hsym i.succ 0, hsym 0 j.succ]
        ring
      -- The quadratic form of `S'`.
      have hS'form : ∀ η : Fin n → ℝ, ∑ i, ∑ j, η i * S' i j * η j =
          ∑ i, ∑ j, η i * S i.succ j.succ * η j - (∑ j, S 0 j.succ * η j) ^ 2 / S 0 0 := by
        intro η
        have hb : ∑ i, η i * S i.succ 0 = ∑ j, S 0 j.succ * η j :=
          Finset.sum_congr rfl fun i _ => by rw [hsym]; ring
        calc ∑ i, ∑ j, η i * S' i j * η j
            = ∑ i, ∑ j, (η i * S i.succ j.succ * η j -
                η i * S i.succ 0 * (S 0 j.succ * η j) / S 0 0) := by
              refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
              rw [hS'ij]
              ring
          _ = ∑ i, ∑ j, η i * S i.succ j.succ * η j -
                (∑ i, η i * S i.succ 0) * (∑ j, S 0 j.succ * η j) / S 0 0 := by
              rw [Finset.sum_mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.sum_div, ← Finset.sum_sub_distrib]
          _ = _ := by rw [hb, sq]
      -- `S'` is again `c`-coercive: test the hypothesis on `ξ = (-b / S 0 0, η)`.
      have hS'q : ∀ η : Fin n → ℝ, c * ∑ i, η i ^ 2 ≤ ∑ i, ∑ j, η i * S' i j * η j := by
        intro η
        rw [hS'form]
        have h := hq (Fin.cons (-(∑ j, S 0 j.succ * η j) / S 0 0) η)
        rw [hnorm, hexp] at h
        have ht : S 0 0 * (-(∑ j, S 0 j.succ * η j) / S 0 0) ^ 2 +
            2 * (-(∑ j, S 0 j.succ * η j) / S 0 0) * ∑ j, S 0 j.succ * η j =
            -((∑ j, S 0 j.succ * η j) ^ 2 / S 0 0) := by
          field_simp
          ring
        have hct : 0 ≤ c * (-(∑ j, S 0 j.succ * η j) / S 0 0) ^ 2 :=
          mul_nonneg hc (sq_nonneg _)
        linarith
      have hih := ih S' c hc hS'sym hS'q
      rw [hdet, pow_succ]
      calc c ^ n * c ≤ S'.det * S 0 0 :=
            mul_le_mul hih hca hc ((pow_nonneg hc n).trans hih)
        _ = S 0 0 * S'.det := mul_comm _ _
    · -- `S 0 0 = 0`: then `c = 0` and the first row of `S` vanishes.
      have hc0 : c = 0 := le_antisymm (ha0 ▸ hca) hc
      have hrow : ∀ j, S 0 j = 0 := by
        intro j
        refine Fin.cases ha0.symm (fun j' => ?_) j
        by_contra hb
        have h := hq (Fin.cons
          (-(∑ i, ∑ j, (Pi.single j' 1 : Fin n → ℝ) i * S i.succ j.succ *
              (Pi.single j' 1 : Fin n → ℝ) j + 1) / (2 * S 0 j'.succ))
          (Pi.single j' 1))
        rw [hnorm, hexp, ← ha0, hc0] at h
        have hb' : ∑ j, S 0 j.succ * (Pi.single j' 1 : Fin n → ℝ) j = S 0 j'.succ := by
          simp [Pi.single_apply]
        rw [hb'] at h
        have key : 2 * (-(∑ i, ∑ j, (Pi.single j' 1 : Fin n → ℝ) i * S i.succ j.succ *
              (Pi.single j' 1 : Fin n → ℝ) j + 1) / (2 * S 0 j'.succ)) * S 0 j'.succ =
            -(∑ i, ∑ j, (Pi.single j' 1 : Fin n → ℝ) i * S i.succ j.succ *
              (Pi.single j' 1 : Fin n → ℝ) j + 1) := by
          field_simp
        linarith
      rw [Matrix.det_eq_zero_of_row_eq_zero 0 hrow, hc0, zero_pow (Nat.succ_ne_zero n)]
/-- **Jacobi's formula for an entrywise-differentiable matrix family** (Simon Ch. 2, 5.2–5.3;
used for `∂_t J = div_M X` in Ch. 4, 2.2). If every entry `s ↦ A(s)_{ij}` has derivative `A'_{ij}`
at `t`, `|A(t)_{ij}| ≤ M` and `|A'_{ij}| ≤ M'`, then `s ↦ det A(s)` has a derivative `D` at `t`
with `|D| ≤ N! N M' M^{N-1}`, and `D = trace A'` when `A(t) = I`. -/
theorem Submission.ts_fv_hasDerivAt_det_of_entries : ∀ (N : ℕ) (A : ℝ → Matrix (Fin N) (Fin N) ℝ) (A' : Matrix (Fin N) (Fin N) ℝ) (t M M' : ℝ), (∀ i j, HasDerivAt (fun s ↦ A s i j) (A' i j) t) → (∀ i j, |A t i j| ≤ M) → (∀ i j, |A' i j| ≤ M') → ∃ D : ℝ, HasDerivAt (fun s ↦ (A s).det) D t ∧ |D| ≤ (N.factorial : ℝ) * N * M' * M ^ (N - 1) ∧ (A t = 1 → D = A'.trace) := by
  intro N A A' t M M' hA hM hM'
  -- `D = ∑_σ ε(σ) ∑_k (∏_{i ≠ k} A(t)_{σ(i) i}) A'_{σ(k) k}`, the derivative of the Leibniz
  -- formula.
  refine ⟨∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
      ∑ k : Fin N, (∏ i ∈ Finset.univ.erase k, A t (σ i) i) * A' (σ k) k, ?_, ?_, ?_⟩
  · -- Product rule on each Leibniz term, then constant multiples and the finite sum.
    have hdet : (fun s ↦ (A s).det) = fun s ↦ ∑ σ : Equiv.Perm (Fin N),
        ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, A s (σ i) i := by
      funext s
      exact Matrix.det_apply' (A s)
    rw [hdet]
    refine HasDerivAt.fun_sum fun σ _ ↦ HasDerivAt.const_mul _ ?_
    simpa only [smul_eq_mul] using
      HasDerivAt.fun_finsetProd (u := Finset.univ) (f := fun i s ↦ A s (σ i) i)
        (f' := fun i ↦ A' (σ i) i) fun i _ ↦ hA (σ i) i
  · -- Each `∏_{i ≠ k}` has `N - 1` factors bounded by `M`; there are `N` indices `k` and `N!`
    -- permutations `σ`.
    calc |∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∑ k : Fin N, (∏ i ∈ Finset.univ.erase k, A t (σ i) i) * A' (σ k) k|
        ≤ ∑ σ : Equiv.Perm (Fin N), |((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∑ k : Fin N, (∏ i ∈ Finset.univ.erase k, A t (σ i) i) * A' (σ k) k| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _σ : Equiv.Perm (Fin N), ∑ _k : Fin N, M' * M ^ (N - 1) := by
          refine Finset.sum_le_sum fun σ _ ↦ ?_
          rw [abs_mul, abs_unit_intCast, one_mul]
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
          have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM k k)
          have hprod : ∏ i ∈ Finset.univ.erase k, |A t (σ i) i| ≤ M ^ (N - 1) := by
            calc ∏ i ∈ Finset.univ.erase k, |A t (σ i) i|
                ≤ ∏ _i ∈ Finset.univ.erase k, M :=
                  Finset.prod_le_prod₀ (fun i _ ↦ abs_nonneg _) fun i _ ↦ hM _ _
              _ = M ^ (N - 1) := by
                  rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _),
                    Finset.card_univ, Fintype.card_fin]
          rw [abs_mul, Finset.abs_prod, mul_comm M']
          exact mul_le_mul hprod (hM' _ _) (abs_nonneg _) (pow_nonneg hM0 _)
      _ = (N.factorial : ℝ) * N * M' * M ^ (N - 1) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
            nsmul_eq_mul]
          ring
  · -- At `A(t) = I` only `σ = id` contributes: for `σ ≠ id` pick `σ j ≠ j`; then every
    -- `∏_{i ≠ k}` contains the factor `I_{σ j, j} = 0` or `I_{σ (σ j), σ j} = 0`.
    intro h1
    have hAt1 : ∀ a, A t a a = 1 := fun a ↦
      (congrFun (congrFun h1 a) a).trans (Matrix.one_apply_eq a)
    have hAt0 : ∀ a b, a ≠ b → A t a b = 0 := fun a b hab ↦
      (congrFun (congrFun h1 a) b).trans (Matrix.one_apply_ne hab)
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin N))]
    · rw [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul, Matrix.trace]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      have hk : ∏ i ∈ Finset.univ.erase k, A t ((1 : Equiv.Perm (Fin N)) i) i = 1 :=
        Finset.prod_eq_one fun i _ ↦ hAt1 i
      rw [hk, one_mul]
      rfl
    · intro σ _ hσ
      obtain ⟨j, hj⟩ : ∃ j, σ j ≠ j := by
        by_contra h
        exact hσ (Equiv.ext fun x ↦ not_not.mp fun hx ↦ h ⟨x, hx⟩)
      have hzero : ∀ k, ∏ i ∈ Finset.univ.erase k, A t (σ i) i = 0 := by
        intro k
        by_cases hk : k = j
        · subst hk
          exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩)
            (hAt0 _ _ fun h ↦ hj (σ.injective h))
        · exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨fun h ↦ hk h.symm, Finset.mem_univ _⟩)
            (hAt0 _ _ hj)
      simp only [hzero, zero_mul, Finset.sum_const_zero, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
/-- **Tangential trace in the standard basis** (used for `∂_t J = div_M X`, Ch. 4, 2.2).
For a subspace `P` of `ℝ^N` with orthogonal projection `p_P`, a linear map `L` and the standard
basis `e_k`: `∑ₖ ⟨L(p_P eₖ), p_P eₖ⟩ = trace (L ∘ p_P)`. -/
theorem Submission.ts_fv_sum_inner_starProjection_eq_trace : ∀ (N : ℕ) (P : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (L : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)), ∑ k : Fin N, inner ℝ (L (P.starProjection (EuclideanSpace.single k (1 : ℝ)))) (P.starProjection (EuclideanSpace.single k (1 : ℝ))) = LinearMap.trace ℝ (EuclideanSpace ℝ (Fin N)) (L.toLinearMap ∘ₗ P.starProjection.toLinearMap) := by
  intro N P L
  -- `p_P ∘ p_P = p_P`, so `L ∘ p_P = (L ∘ p_P) ∘ p_P`.
  have hpp : L.toLinearMap ∘ₗ P.starProjection.toLinearMap =
      (L.toLinearMap ∘ₗ P.starProjection.toLinearMap) ∘ₗ P.starProjection.toLinearMap := by
    ext v : 1
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      Submodule.starProjection_eq_self_iff.mpr (P.starProjection_apply_mem v)]
  -- Cyclicity gives `trace (p_P ∘ L ∘ p_P)`; compute it in the orthonormal basis `eₖ`.
  rw [hpp, LinearMap.trace_comp_comm',
    LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis, Matrix.trace]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
  -- `⟨L(p_P eₖ), p_P eₖ⟩ = ⟨p_P eₖ, L(p_P eₖ)⟩ = ⟨eₖ, p_P(L(p_P eₖ))⟩` (`p_P` is self-adjoint).
  rw [real_inner_comm, Submodule.inner_starProjection_left_eq_right]
/-- **Entry bound and uniform ellipticity of the tangential matrix** (auxiliary to the Jacobian
computation behind Simon Ch. 4, 2.2, done as in Ch. 2, 5.2–5.3). Let `p` be the orthogonal
projection onto `P ⊆ ℝᴺ`, `eᵢ` the standard basis and `L` a linear map with `‖L‖ ≤ b`,
`‖v‖ ≤ b‖L v‖` and `b ≥ 1`. Then `S_ij = ⟨L(p eᵢ), L(p eⱼ)⟩ + ⟨eᵢ - p eᵢ, eⱼ - p eⱼ⟩` satisfies
`|S_ij| ≤ b² + 1` and `(b²)⁻¹ ∑ᵢ ξᵢ² ≤ ∑ᵢ ∑ⱼ ξᵢ S_ij ξⱼ`: for `v = ∑ᵢ ξᵢ eᵢ` the form equals
`‖L(p v)‖² + ‖v - p v‖²`, while `∑ᵢ ξᵢ² = ‖v‖² = ‖p v‖² + ‖v - p v‖²`. -/
theorem Submission.ts_fv_tangential_matrix_estimates : (∀ (N : ℕ) (P : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (L : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) (b : ℝ), 1 ≤ b → ‖L‖ ≤ b → (∀ v, ‖v‖ ≤ b * ‖L v‖) → (∀ i j : Fin N, |inner ℝ (L (P.starProjection (EuclideanSpace.single i (1 : ℝ)))) (L (P.starProjection (EuclideanSpace.single j (1 : ℝ)))) + inner ℝ (EuclideanSpace.single i (1 : ℝ) - P.starProjection (EuclideanSpace.single i (1 : ℝ))) (EuclideanSpace.single j (1 : ℝ) - P.starProjection (EuclideanSpace.single j (1 : ℝ)))| ≤ b ^ 2 + 1) ∧ ∀ ξ : Fin N → ℝ, (b ^ 2)⁻¹ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, ξ i * (inner ℝ (L (P.starProjection (EuclideanSpace.single i (1 : ℝ)))) (L (P.starProjection (EuclideanSpace.single j (1 : ℝ)))) + inner ℝ (EuclideanSpace.single i (1 : ℝ) - P.starProjection (EuclideanSpace.single i (1 : ℝ))) (EuclideanSpace.single j (1 : ℝ) - P.starProjection (EuclideanSpace.single j (1 : ℝ)))) * ξ j) := by
  intro N P L b hb hL hLinv
  have hb0 : 0 < b := one_pos.trans_le hb
  -- Pythagoras: `‖v‖² = ‖p v‖² + ‖v - p v‖²`, since `v - p v ⊥ P ∋ p v`.
  have pyth : ∀ v : EuclideanSpace ℝ (Fin N),
      ‖v‖ ^ 2 = ‖P.starProjection v‖ ^ 2 + ‖v - P.starProjection v‖ ^ 2 := by
    intro v
    have h0 : inner ℝ (P.starProjection v) (v - P.starProjection v) = 0 := by
      rw [real_inner_comm]
      exact Submodule.starProjection_inner_eq_zero v _ (P.starProjection_apply_mem v)
    have h := norm_add_sq_real (P.starProjection v) (v - P.starProjection v)
    rwa [add_sub_cancel, h0, mul_zero, add_zero] at h
  refine ⟨fun i j ↦ ?_, fun ξ ↦ ?_⟩
  · -- (a) Cauchy–Schwarz with `‖L(p eₖ)‖ ≤ ‖L‖‖p eₖ‖ ≤ b` and `‖eₖ - p eₖ‖ ≤ ‖eₖ‖ = 1`.
    have he : ∀ k : Fin N, ‖(EuclideanSpace.single k (1 : ℝ) : EuclideanSpace ℝ (Fin N))‖ = 1 :=
      fun k ↦ by simp
    have hA : ∀ k : Fin N, ‖L (P.starProjection (EuclideanSpace.single k (1 : ℝ)))‖ ≤ b := by
      intro k
      calc ‖L (P.starProjection (EuclideanSpace.single k (1 : ℝ)))‖
          ≤ ‖L‖ * ‖P.starProjection (EuclideanSpace.single k (1 : ℝ))‖ := L.le_opNorm _
        _ ≤ b * 1 := by
          gcongr
          exact (P.norm_starProjection_apply_le _).trans (he k).le
        _ = b := mul_one b
    have hB : ∀ k : Fin N, ‖EuclideanSpace.single k (1 : ℝ) -
        P.starProjection (EuclideanSpace.single k (1 : ℝ))‖ ≤ 1 := by
      intro k
      have h := pyth (EuclideanSpace.single k (1 : ℝ))
      rw [he k] at h
      nlinarith [norm_nonneg (EuclideanSpace.single k (1 : ℝ) -
        P.starProjection (EuclideanSpace.single k (1 : ℝ))),
        sq_nonneg ‖P.starProjection (EuclideanSpace.single k (1 : ℝ))‖]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (abs_real_inner_le_norm _ _).trans ?_
      rw [sq]
      exact mul_le_mul (hA i) (hA j) (norm_nonneg _) hb0.le
    · refine (abs_real_inner_le_norm _ _).trans ?_
      calc _ ≤ (1 : ℝ) * 1 := mul_le_mul (hB i) (hB j) (norm_nonneg _) zero_le_one
        _ = 1 := mul_one 1
  · -- (b) With `v = ∑ᵢ ξᵢ eᵢ` the form is `‖L(p v)‖² + ‖v - p v‖²`, and `∑ᵢ ξᵢ² = ‖v‖²`.
    set v : EuclideanSpace ℝ (Fin N) := ∑ i, ξ i • EuclideanSpace.single i (1 : ℝ) with hv
    -- bilinearity: `⟨∑ᵢ ξᵢ uᵢ, ∑ⱼ ξⱼ uⱼ⟩ = ∑ᵢ ∑ⱼ ξᵢ ⟨uᵢ, uⱼ⟩ ξⱼ`
    have bil : ∀ u : Fin N → EuclideanSpace ℝ (Fin N),
        inner ℝ (∑ i, ξ i • u i) (∑ j, ξ j • u j) = ∑ i, ∑ j, ξ i * inner ℝ (u i) (u j) * ξ j := by
      intro u
      rw [sum_inner]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [real_inner_smul_left, inner_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [real_inner_smul_right]
      ring
    have hLv : L (P.starProjection v) =
        ∑ i, ξ i • L (P.starProjection (EuclideanSpace.single i (1 : ℝ))) := by
      simp only [hv, map_sum, map_smul]
    have hQv : v - P.starProjection v = ∑ i, ξ i • (EuclideanSpace.single i (1 : ℝ) -
        P.starProjection (EuclideanSpace.single i (1 : ℝ))) := by
      simp only [hv, map_sum, map_smul, smul_sub, Finset.sum_sub_distrib]
    have hform : ∑ i, ∑ j, ξ i * (inner ℝ (L (P.starProjection (EuclideanSpace.single i (1 : ℝ))))
        (L (P.starProjection (EuclideanSpace.single j (1 : ℝ)))) +
        inner ℝ
          (EuclideanSpace.single i (1 : ℝ) - P.starProjection (EuclideanSpace.single i (1 : ℝ)))
          (EuclideanSpace.single j (1 : ℝ) - P.starProjection (EuclideanSpace.single j (1 : ℝ)))) *
          ξ j = ‖L (P.starProjection v)‖ ^ 2 + ‖v - P.starProjection v‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hLv, hQv,
        bil fun i ↦ L (P.starProjection (EuclideanSpace.single i (1 : ℝ))),
        bil fun i ↦ EuclideanSpace.single i (1 : ℝ) -
          P.starProjection (EuclideanSpace.single i (1 : ℝ))]
      simp only [mul_add, add_mul, Finset.sum_add_distrib]
    have hnv : ‖v‖ ^ 2 = ∑ i, ξ i ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, hv, bil fun i ↦ EuclideanSpace.single i (1 : ℝ)]
      simp [EuclideanSpace.inner_single_left, sq]
    -- `‖p v‖ ≤ b‖L(p v)‖` and `(b²)⁻¹ ≤ 1`
    have hlow : ‖P.starProjection v‖ ^ 2 ≤ b ^ 2 * ‖L (P.starProjection v)‖ ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hLinv _) 2
    rw [hform, ← hnv, pyth v, mul_add]
    exact add_le_add ((inv_mul_le_iff₀ (by positivity)).2 hlow)
      (mul_le_of_le_one_left (sq_nonneg _) (inv_le_one_of_one_le₀ (one_le_pow₀ hb)))

/-- **Derivative of the tangential Jacobian** (Ch. 4, 2.2 with Ch. 2, 5.2–5.3: Jacobi's formula).
Let `p_P` be the orthogonal projection onto a subspace `P ⊆ ℝ^N`, `q_P = I - p_P`, and let `Λ(t)`
be a family of linear maps with `Λ(0) = I`, derivative `Λ'(t)`, and `‖Λ(t)‖, ‖Λ'(t)‖ ≤ B`,
`|v| ≤ B |Λ(t) v|` for `|t| < δ`. Then the tangential Jacobian
`J(t) = (det [⟨Λ(t) p_P eᵢ, Λ(t) p_P eⱼ⟩ + ⟨q_P eᵢ, q_P eⱼ⟩])^{1/2}` satisfies `0 ≤ J ≤ C`,
`|J'| ≤ C` on `(-δ, δ)` with `C = C(N, B)`, and `J'(0) = trace (Λ'(0) ∘ p_P)`. -/
theorem Submission.ts_fv_tangential_jacobian_hasDerivAt : ∀ (N : ℕ) (B : ℝ), ∃ C : ℝ, ∀ (P : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (Λ Λ' : ℝ → (EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))) (J : ℝ → ℝ) (δ : ℝ), 0 < δ → Λ 0 = 1 → (∀ t ∈ Ioo (-δ) δ, HasDerivAt Λ (Λ' t) t ∧ ‖Λ t‖ ≤ B ∧ ‖Λ' t‖ ≤ B ∧ ∀ v, ‖v‖ ≤ B * ‖Λ t v‖) → (∀ t, J t = Real.sqrt (Matrix.det (Matrix.of fun i j : Fin N ↦ inner ℝ (Λ t (P.starProjection (EuclideanSpace.single i (1 : ℝ)))) (Λ t (P.starProjection (EuclideanSpace.single j (1 : ℝ)))) + inner ℝ (EuclideanSpace.single i (1 : ℝ) - P.starProjection (EuclideanSpace.single i (1 : ℝ))) (EuclideanSpace.single j (1 : ℝ) - P.starProjection (EuclideanSpace.single j (1 : ℝ)))))) → (∀ t ∈ Ioo (-δ) δ, 0 ≤ J t ∧ J t ≤ C ∧ ∃ d : ℝ, HasDerivAt J d t ∧ |d| ≤ C) ∧ HasDerivAt J (LinearMap.trace ℝ (EuclideanSpace ℝ (Fin N)) ((Λ' 0).toLinearMap ∘ₗ P.starProjection.toLinearMap)) 0 := by
  intro N B
  -- Step 0: `B₁ = max(B, 1)`, `M₀ = B₁² + 1` and `C = (N! M₀^N)^{1/2} + N! N B₁^{N+2} M₀^{N-1}`.
  obtain ⟨B₁, hBB₁, hB₁⟩ : ∃ B₁ : ℝ, B ≤ B₁ ∧ 1 ≤ B₁ :=
    ⟨max B 1, le_max_left _ _, le_max_right _ _⟩
  have hB₁0 : 0 < B₁ := zero_lt_one.trans_le hB₁
  obtain ⟨M₀, hM₀⟩ : ∃ M₀ : ℝ, M₀ = B₁ ^ 2 + 1 := ⟨_, rfl⟩
  have hM₀0 : 0 < M₀ := by rw [hM₀]; positivity
  refine ⟨Real.sqrt (N.factorial * M₀ ^ N) + N.factorial * N * B₁ ^ (N + 2) * M₀ ^ (N - 1), ?_⟩
  intro P Λ Λ' J δ hδ hΛ0 hΛ hJ
  -- `S t` is the matrix under the square root and `S' t` its entrywise derivative (step 4).
  obtain ⟨S, hS⟩ : ∃ S : ℝ → Matrix (Fin N) (Fin N) ℝ, ∀ t i j, S t i j =
      inner ℝ (Λ t (P.starProjection (EuclideanSpace.single i (1 : ℝ))))
          (Λ t (P.starProjection (EuclideanSpace.single j (1 : ℝ)))) +
        inner ℝ
          (EuclideanSpace.single i (1 : ℝ) - P.starProjection (EuclideanSpace.single i (1 : ℝ)))
          (EuclideanSpace.single j (1 : ℝ) - P.starProjection (EuclideanSpace.single j (1 : ℝ))) :=
    ⟨fun t ↦ Matrix.of fun i j ↦
      inner ℝ (Λ t (P.starProjection (EuclideanSpace.single i (1 : ℝ))))
          (Λ t (P.starProjection (EuclideanSpace.single j (1 : ℝ)))) +
        inner ℝ
          (EuclideanSpace.single i (1 : ℝ) - P.starProjection (EuclideanSpace.single i (1 : ℝ)))
          (EuclideanSpace.single j (1 : ℝ) - P.starProjection (EuclideanSpace.single j (1 : ℝ))),
      fun _ _ _ ↦ rfl⟩
  obtain ⟨S', hS'⟩ : ∃ S' : ℝ → Matrix (Fin N) (Fin N) ℝ, ∀ t i j, S' t i j =
      inner ℝ (Λ t (P.starProjection (EuclideanSpace.single i (1 : ℝ))))
          (Λ' t (P.starProjection (EuclideanSpace.single j (1 : ℝ)))) +
        inner ℝ (Λ' t (P.starProjection (EuclideanSpace.single i (1 : ℝ))))
          (Λ t (P.starProjection (EuclideanSpace.single j (1 : ℝ)))) :=
    ⟨fun t ↦ Matrix.of fun i j ↦
      inner ℝ (Λ t (P.starProjection (EuclideanSpace.single i (1 : ℝ))))
          (Λ' t (P.starProjection (EuclideanSpace.single j (1 : ℝ)))) +
        inner ℝ (Λ' t (P.starProjection (EuclideanSpace.single i (1 : ℝ))))
          (Λ t (P.starProjection (EuclideanSpace.single j (1 : ℝ)))),
      fun _ _ _ ↦ rfl⟩
  have hJS : ∀ t, J t = Real.sqrt (S t).det := by
    intro t
    rw [hJ t]
    congr 2
    ext i j
    rw [Matrix.of_apply, hS]
  -- On `(-δ, δ)` the hypotheses hold with `B₁` in place of `B`.
  have hbd : ∀ t ∈ Ioo (-δ) δ, ‖Λ t‖ ≤ B₁ ∧ ‖Λ' t‖ ≤ B₁ ∧ ∀ v, ‖v‖ ≤ B₁ * ‖Λ t v‖ := by
    intro t ht
    obtain ⟨-, h1, h2, h3⟩ := hΛ t ht
    exact ⟨h1.trans hBB₁, h2.trans hBB₁,
      fun v ↦ (h3 v).trans (mul_le_mul_of_nonneg_right hBB₁ (norm_nonneg _))⟩
  -- Steps 1 and 2(b): `S t` is symmetric, `|S t i j| ≤ M₀` and `ξᵀ (S t) ξ ≥ B₁⁻² |ξ|²`.
  have hsymm : ∀ t i j, S t i j = S t j i := by
    intro t i j
    rw [hS, hS]
    congr 1 <;> exact real_inner_comm _ _
  have hest : ∀ t ∈ Ioo (-δ) δ, (∀ i j, |S t i j| ≤ M₀) ∧
      ∀ ξ : Fin N → ℝ, (B₁ ^ 2)⁻¹ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, ξ i * S t i j * ξ j := by
    intro t ht
    obtain ⟨h1, -, h3⟩ := hbd t ht
    obtain ⟨hA, hQ⟩ := Submission.ts_fv_tangential_matrix_estimates N P (Λ t) B₁ hB₁ h1 h3
    refine ⟨fun i j ↦ ?_, fun ξ ↦ ?_⟩
    · rw [hS, hM₀]
      exact hA i j
    · simp only [hS]
      exact hQ ξ
  -- Step 2: `(det S t)^{1/2} ≥ B₁^{-N}` (spectral bound) and `|det S t| ≤ N! M₀^N` (Leibniz).
  have hdet : ∀ t ∈ Ioo (-δ) δ,
      (B₁ ^ N)⁻¹ ≤ Real.sqrt (S t).det ∧ |(S t).det| ≤ N.factorial * M₀ ^ N := by
    intro t ht
    obtain ⟨hA, hQ⟩ := hest t ht
    refine ⟨?_, ?_⟩
    · have hc := Submission.ts_fv_det_ge_pow_of_quadForm_ge N (S t) ((B₁ ^ 2)⁻¹) (by positivity)
        (hsymm t) hQ
      refine Real.le_sqrt_of_sq_le ?_
      calc ((B₁ ^ N)⁻¹) ^ 2 = ((B₁ ^ 2)⁻¹) ^ N := by ring
        _ ≤ (S t).det := hc
    · rw [Matrix.det_apply']
      calc |∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, S t (σ i) i|
          ≤ ∑ σ : Equiv.Perm (Fin N), |((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, S t (σ i) i| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _σ : Equiv.Perm (Fin N), ∏ _i : Fin N, M₀ := by
            gcongr with σ
            have hsign : |((Equiv.Perm.sign σ : ℤ) : ℝ)| = 1 := by
              rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
            rw [abs_mul, hsign, one_mul, Finset.abs_prod]
            exact Finset.prod_le_prod₀ (fun i _ ↦ abs_nonneg _) (fun i _ ↦ hA _ _)
        _ = N.factorial * M₀ ^ N := by
            simp [Finset.prod_const, Finset.sum_const, Fintype.card_perm]
  -- Steps 4–6: the entries are differentiable, `|S' t i j| ≤ 2 B₁²`, Jacobi's formula and the
  -- chain rule for the square root.
  have hderiv : ∀ t ∈ Ioo (-δ) δ, ∀ i j, HasDerivAt (fun s ↦ S s i j) (S' t i j) t := by
    intro t ht i j
    have hv : ∀ w, HasDerivAt (fun s ↦ Λ s w) (Λ' t w) t := fun w ↦ by
      simpa using (hΛ t ht).1.clm_apply (hasDerivAt_const t w)
    simp only [hS, hS']
    exact ((hv _).inner ℝ (hv _)).add_const _
  have hderiv_bd : ∀ t ∈ Ioo (-δ) δ, ∀ i j, |S' t i j| ≤ 2 * B₁ ^ 2 := by
    intro t ht i j
    obtain ⟨h1, h2, -⟩ := hbd t ht
    have hL : ∀ L : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N), ‖L‖ ≤ B₁ →
        ∀ k, ‖L (P.starProjection (EuclideanSpace.single k (1 : ℝ)))‖ ≤ B₁ := by
      intro L hL k
      have hp : ‖P.starProjection (EuclideanSpace.single k (1 : ℝ))‖ ≤ 1 :=
        (Submodule.norm_starProjection_apply_le (K := P) _).trans (by simp)
      calc ‖L (P.starProjection (EuclideanSpace.single k (1 : ℝ)))‖
          ≤ ‖L‖ * ‖P.starProjection (EuclideanSpace.single k (1 : ℝ))‖ := L.le_opNorm _
        _ ≤ B₁ * 1 := by gcongr
        _ = B₁ := mul_one _
    -- Cauchy–Schwarz on both terms of `S' t i j`.
    have hx := (abs_real_inner_le_norm _ _).trans
      (mul_le_mul (hL _ h1 i) (hL _ h2 j) (norm_nonneg _) hB₁0.le)
    have hy := (abs_real_inner_le_norm _ _).trans
      (mul_le_mul (hL _ h2 i) (hL _ h1 j) (norm_nonneg _) hB₁0.le)
    rw [hS']
    rw [abs_le] at hx hy ⊢
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hJd : ∀ t ∈ Ioo (-δ) δ, ∃ D : ℝ, HasDerivAt J (D / (2 * Real.sqrt (S t).det)) t ∧
      |D| ≤ N.factorial * N * (2 * B₁ ^ 2) * M₀ ^ (N - 1) ∧ (S t = 1 → D = (S' t).trace) := by
    intro t ht
    obtain ⟨D, hD, hDb, hD1⟩ := Submission.ts_fv_hasDerivAt_det_of_entries N S (S' t) t M₀
      (2 * B₁ ^ 2) (hderiv t ht) (hest t ht).1 (hderiv_bd t ht)
    have hpos : 0 < (S t).det :=
      Real.sqrt_pos.1 ((inv_pos.2 (pow_pos hB₁0 N)).trans_le (hdet t ht).1)
    refine ⟨D, ?_, hDb, hD1⟩
    rw [show J = fun s ↦ Real.sqrt (S s).det from funext hJS]
    exact hD.sqrt hpos.ne'
  refine ⟨fun t ht ↦ ?_, ?_⟩
  · -- Steps 3 and 6: `0 ≤ J t ≤ C` and `|J'(t)| ≤ C`.
    obtain ⟨hlow, hup⟩ := hdet t ht
    obtain ⟨D, hD, hDb, -⟩ := hJd t ht
    have hsq : 0 < Real.sqrt (S t).det := (inv_pos.2 (pow_pos hB₁0 N)).trans_le hlow
    have h2s : 0 < 2 * Real.sqrt (S t).det := mul_pos two_pos hsq
    have hK : 0 ≤ (N.factorial : ℝ) * N * B₁ ^ (N + 2) * M₀ ^ (N - 1) := by positivity
    have hpow : B₁ ^ (N + 2) * (B₁ ^ N)⁻¹ = B₁ ^ 2 := by
      rw [pow_add B₁ N 2, mul_assoc, mul_comm (B₁ ^ 2), ← mul_assoc,
        mul_inv_cancel₀ (pow_ne_zero _ hB₁0.ne'), one_mul]
    refine ⟨by rw [hJS t]; exact Real.sqrt_nonneg _, ?_, D / (2 * Real.sqrt (S t).det), hD, ?_⟩
    · rw [hJS t]
      calc Real.sqrt (S t).det ≤ Real.sqrt (N.factorial * M₀ ^ N) :=
            Real.sqrt_le_sqrt ((le_abs_self _).trans hup)
        _ ≤ _ := le_add_of_nonneg_right hK
    · rw [abs_div, abs_of_pos h2s, div_le_iff₀ h2s]
      calc |D| ≤ N.factorial * N * (2 * B₁ ^ 2) * M₀ ^ (N - 1) := hDb
        _ = N.factorial * N * B₁ ^ (N + 2) * M₀ ^ (N - 1) * (2 * (B₁ ^ N)⁻¹) := by
            rw [← hpow]
            ring
        _ ≤ N.factorial * N * B₁ ^ (N + 2) * M₀ ^ (N - 1) * (2 * Real.sqrt (S t).det) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlow zero_le_two) hK
        _ ≤ (Real.sqrt (N.factorial * M₀ ^ N) + N.factorial * N * B₁ ^ (N + 2) * M₀ ^ (N - 1)) *
              (2 * Real.sqrt (S t).det) :=
            mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (Real.sqrt_nonneg _)) h2s.le
  · -- Steps 7 and 8: `S 0 = I`, so `J'(0) = trace (S' 0) / 2 = ∑ₖ ⟨Λ'(0) p eₖ, p eₖ⟩`.
    have h0 : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_lt_zero.2 hδ, hδ⟩
    obtain ⟨D, hD, -, hD1⟩ := hJd 0 h0
    have hS0 : S 0 = 1 := by
      ext i j
      rw [hS, hΛ0, one_apply_eq_self, one_apply_eq_self]
      -- `q eᵢ ⊥ P`, so `⟨p eᵢ, p eⱼ⟩ + ⟨q eᵢ, q eⱼ⟩ = ⟨eᵢ, eⱼ⟩ = δᵢⱼ`.
      have h1 := Submodule.starProjection_inner_eq_zero (K := P) (EuclideanSpace.single i (1 : ℝ))
        (P.starProjection (EuclideanSpace.single j (1 : ℝ))) (P.starProjection_apply_mem _)
      have h2 := Submodule.starProjection_inner_eq_zero (K := P) (EuclideanSpace.single j (1 : ℝ))
        (P.starProjection (EuclideanSpace.single i (1 : ℝ))) (P.starProjection_apply_mem _)
      have he : inner ℝ (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) =
          (1 : Matrix (Fin N) (Fin N) ℝ) i j := by
        simp [EuclideanSpace.inner_single_left, Matrix.one_apply]
      rw [← he]
      simp only [inner_sub_left, inner_sub_right] at h1 h2 ⊢
      linarith [real_inner_comm (P.starProjection (EuclideanSpace.single i (1 : ℝ)))
          (EuclideanSpace.single j (1 : ℝ)),
        real_inner_comm (P.starProjection (EuclideanSpace.single i (1 : ℝ)))
          (P.starProjection (EuclideanSpace.single j (1 : ℝ)))]
    rw [hS0, Matrix.det_one, Real.sqrt_one, hD1 hS0] at hD
    refine hD.congr_deriv ?_
    rw [← Submission.ts_fv_sum_inner_starProjection_eq_trace N P (Λ' 0), Matrix.trace,
      Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Matrix.diag_apply, hS', hΛ0, one_apply_eq_self,
      real_inner_comm (P.starProjection (EuclideanSpace.single k (1 : ℝ)))]
    ring
/-- **Differentiation under the integral sign for `θ`-weighted integrals over `M ∩ K`** (used for
the first variation formula, Ch. 4, 2.2). Let `K` be compact and `δ > 0`. If for `|t| < δ`,
`m(t) = ∫_{M ∩ K} θ J(t, ·) dHⁿ` with `J(t, ·)` `Hⁿ ⌞ M`-measurable, and for `Hⁿ`-a.e. `x ∈ M ∩ K`
and all `|t| < δ`: `0 ≤ J(t, x) ≤ B`, `∂ₜJ(t, x) = J'(t, x)`, `|J'(t, x)| ≤ B`, and
`J'(0, x) = g(x)`, where `g` is `Hⁿ ⌞ M`-measurable and vanishes off `K`, then `t ↦ m(t)` has
derivative `∫ g dμ_V` at `t = 0`. -/
theorem Submission.ts_fv_hasDerivAt_of_weighted_jacobian : ∀ (n ℓ : ℕ) (a : RectifiablePair n ℓ) (K : Set (Ambient n ℓ)) (m : ℝ → ℝ≥0∞) (J J' : ℝ → Ambient n ℓ → ℝ) (g : Ambient n ℓ → ℝ) (δ B : ℝ), 0 < δ → IsCompact K → (∀ t ∈ Ioo (-δ) δ, m t = ∫⁻ x in a.M ∩ K, ENNReal.ofReal (a.θ x * J t x) ∂μHE[n]) → (∀ t ∈ Ioo (-δ) δ, AEStronglyMeasurable (J t) ((μHE[n] : Measure (Ambient n ℓ)).restrict a.M)) → AEStronglyMeasurable g ((μHE[n] : Measure (Ambient n ℓ)).restrict a.M) → (∀ x ∉ K, g x = 0) → (∀ᵐ x ∂(μHE[n] : Measure (Ambient n ℓ)).restrict a.M, x ∈ K → J' 0 x = g x ∧ ∀ t ∈ Ioo (-δ) δ, 0 ≤ J t x ∧ J t x ≤ B ∧ HasDerivAt (fun s ↦ J s x) (J' t x) t ∧ |J' t x| ≤ B) → HasDerivAt (fun t ↦ (m t).toReal) (∫ x, g x ∂(mk a).weight) 0 := by
  intro n ℓ a K m J J' g δ B hδ hK hm hJ hg hg0 hae
  -- Work with `ν = Hⁿ ⌞ (M ∩ K) = (Hⁿ ⌞ M) ⌞ K` on the neighbourhood `I = (-δ, δ)` of `0`.
  set ν : Measure (Ambient n ℓ) := (μHE[n] : Measure (Ambient n ℓ)).restrict (a.M ∩ K)
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hνK : ((μHE[n] : Measure (Ambient n ℓ)).restrict a.M).restrict K = ν := by
    rw [Measure.restrict_restrict hKm, Set.inter_comm]
  have hle : ν ≤ (μHE[n] : Measure (Ambient n ℓ)).restrict a.M :=
    Measure.restrict_mono Set.inter_subset_left le_rfl
  have hs : Ioo (-δ) δ ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by linarith) hδ
  -- `θ` is `ν`-integrable and `ν`-a.e. positive, and the pointwise hypotheses hold `ν`-a.e.
  have hθ : Integrable a.θ ν := a.isRectifiablePair.locallyIntegrable K hK
  have hθpos : ∀ᵐ x ∂ν, 0 < a.θ x :=
    (ae_restrict_mem₀ (a.isRectifiablePair.measurable.inter hKm.nullMeasurableSet)).mono
      fun x hx ↦ a.isRectifiablePair.pos x hx.1
  have hae' : ∀ᵐ x ∂ν, J' 0 x = g x ∧ ∀ t ∈ Ioo (-δ) δ, 0 ≤ J t x ∧ J t x ≤ B ∧
      HasDerivAt (fun s ↦ J s x) (J' t x) t ∧ |J' t x| ≤ B := by
    rw [← hνK]
    exact (ae_restrict_iff' hKm).2 hae
  -- For `t ∈ I`, `0 ≤ θ J(t, ·) ≤ B θ` `ν`-a.e., so `θ J(t, ·)` is `ν`-integrable and
  -- `(m t).toReal = ∫ θ J(t, ·) dν`.
  have hFint : ∀ t ∈ Ioo (-δ) δ, Integrable (fun x ↦ a.θ x * J t x) ν := by
    intro t ht
    refine (hθ.const_mul B).mono' (hθ.aestronglyMeasurable.mul ((hJ t ht).mono_measure hle)) ?_
    filter_upwards [hθpos, hae'] with x hx hx'
    obtain ⟨h0, h1, -, -⟩ := hx'.2 t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx.le h0), mul_comm B]
    exact mul_le_mul_of_nonneg_left h1 hx.le
  have hmt : ∀ t ∈ Ioo (-δ) δ, (m t).toReal = ∫ x, a.θ x * J t x ∂ν := by
    intro t ht
    have hnn : 0 ≤ᵐ[ν] fun x ↦ a.θ x * J t x := by
      filter_upwards [hθpos, hae'] with x hx hx'
      exact mul_nonneg hx.le (hx'.2 t ht).1
    rw [hm t ht, ← ofReal_integral_eq_lintegral_ofReal (hFint t ht) hnn,
      ENNReal.toReal_ofReal (integral_nonneg_of_ae hnn)]
  -- Differentiate under the integral sign, with the integrable bound `B θ`.
  obtain ⟨-, hD⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
    (F := fun t x ↦ a.θ x * J t x) (F' := fun t x ↦ a.θ x * J' t x)
    (bound := fun x ↦ B * a.θ x) hs
    (Filter.eventually_of_mem hs fun t ht ↦ (hFint t ht).aestronglyMeasurable)
    (hFint 0 ⟨by linarith, hδ⟩)
    ((hθ.aestronglyMeasurable.mul (hg.mono_measure hle)).congr (by
      filter_upwards [hae'] with x hx
      show a.θ x * g x = a.θ x * J' 0 x
      rw [hx.1]))
    (by
      filter_upwards [hθpos, hae'] with x hx hx' t ht
      show ‖a.θ x * J' t x‖ ≤ B * a.θ x
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos hx, mul_comm B]
      exact mul_le_mul_of_nonneg_left (hx'.2 t ht).2.2.2 hx.le)
    (hθ.const_mul B)
    (by
      filter_upwards [hae'] with x hx t ht
      exact (hx.2 t ht).2.2.1.const_mul (a.θ x))
  -- The derivative is `∫ θ g dν = ∫_K g dμ_V = ∫ g dμ_V`, as `μ_V ⌞ K = ν.withDensity θ`.
  have hval : ∫ x, a.θ x * J' 0 x ∂ν = ∫ x, g x ∂(mk a).weight := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hg0]
    show _ = ∫ x, g x ∂(((μHE[n] : Measure (Ambient n ℓ)).restrict a.M).withDensity
      fun x ↦ ENNReal.ofReal (a.θ x)).restrict K
    rw [restrict_withDensity hKm, hνK, integral_withDensity_eq_integral_toReal_smul₀
      hθ.aemeasurable.ennreal_ofReal (ae_of_all _ fun x ↦ ENNReal.ofReal_lt_top)]
    refine integral_congr_ae ?_
    filter_upwards [hθpos, hae'] with x hx hx'
    rw [hx'.1, ENNReal.toReal_ofReal hx.le, smul_eq_mul]
  rw [← hval]
  exact hD.congr_of_eventuallyEq (Filter.eventually_of_mem hs hmt)

/-- **Ch. 4, 2.1–2.2 (pp. 87–88), first variation via Lipschitz pieces** (with the area formula of
Ch. 3, 2.4–2.5 and the Jacobian computation of Ch. 2, 5.2–5.3). Let `M ⊆ N₀ ∪ ⋃ᵢ Fᵢ(Cᵢ)` with
`Hⁿ(N₀) = 0`, where the Lipschitz pieces `(Cᵢ, Fᵢ)` compute the tangent spaces
(`T_x V = DFᵢ(w)(ℝⁿ)` whenever `Fᵢ(w) = x`, for `Hⁿ`-a.e. `x ∈ M`), and let `x ↦ p_{T_x V}` be
`Hⁿ ⌞ M`-a.e. strongly measurable. Then for every compact variation `(φ, ε, K)` the mass
`t ↦ M(φ_t#(V ⌞ K))` has derivative `∫ div_M X dμ_V` at `t = 0`, where `X = ∂φ_t/∂t|_{t=0}`. -/
theorem Submission.ts_first_variation_of_pieces : ∀ (n ℓ : ℕ) (a : RectifiablePair n ℓ) (N₀ : Set (Ambient n ℓ)) (C : ℕ → Set (EuclideanSpace ℝ (Fin n))) (F : ℕ → EuclideanSpace ℝ (Fin n) → Ambient n ℓ) (φ : ℝ → Ambient n ℓ → Ambient n ℓ) (ε : ℝ) (K : Set (Ambient n ℓ)), 0 < n → MeasurableSet N₀ → (μHE[n] : Measure (Ambient n ℓ)) N₀ = 0 → a.M ⊆ N₀ ∪ ⋃ i, F i '' C i → (∀ i, IsCompact (C i) ∧ (∃ K : NNReal, LipschitzWith K (F i)) ∧ (∀ w ∈ C i, DifferentiableAt ℝ (F i) w ∧ Function.Injective (fderiv ℝ (F i) w)) ∧ ContinuousOn (fderiv ℝ (F i)) (C i) ∧ ∃ c : ℝ, 0 < c ∧ ∀ v ∈ C i, ∀ w ∈ C i, c * ‖v - w‖ ≤ ‖F i v - F i w‖) → (∀ᵐ x ∂(μHE[n] : Measure (Ambient n ℓ)).restrict a.M, ∀ i, ∀ w ∈ C i, F i w = x → (mk a).tangentSpace x = LinearMap.range (fderiv ℝ (F i) w).toLinearMap) → AEStronglyMeasurable (fun x ↦ ((mk a).tangentSpace x).starProjection) ((μHE[n] : Measure (Ambient n ℓ)).restrict a.M) → IsCompactVariation φ ε K → HasDerivAt (fun t ↦ (imageMass a (φ t) K).toReal) (∫ x, (mk a).tangentialDiv (fun y ↦ deriv (fun t ↦ φ t y) 0) x ∂(mk a).weight) 0 := by
  intro n ℓ a N₀ C F φ ε K hn hN₀ hN₀0 hcover hpieces htan hproj hV
  -- The variation: `X` is `C¹` with `DX = 0` off `K`, each `φ_t` is Lipschitz and `C¹`, and near
  -- `t = 0` the map `t ↦ Dφ_t(x)` is differentiable with `∂_t Dφ_t(x)|_{t=0} = DX(x)` and with
  -- uniform bounds on `Dφ_t(x)`, `∂_t Dφ_t(x)` and `Dφ_t(x)⁻¹`.
  obtain ⟨hX, hDX, hφ, δ, B, hδ, hδε, Λ', hΛ'⟩ :=
    Submission.ts_fv_compact_variation_bounds n ℓ φ ε K hV
  -- Jacobi's formula with a constant uniform in `x` and in the plane `T_x V`.
  obtain ⟨A, hA⟩ := Submission.ts_fv_tangential_jacobian_hasDerivAt (n + ℓ) B
  have hφ0 : ∀ x, fderiv ℝ (φ 0) x = 1 := fun x ↦ by
    rw [show φ 0 = fun y ↦ y from funext hV.init, fderiv_fun_id]
    rfl
  have hε : ∀ t ∈ Ioo (-δ) δ, t ∈ Ioo (-ε) ε := fun t ht ↦
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- `J^P(L) = (det (P L* L P + I - P))^{1/2}`, with the matrix taken in the standard basis; it is
  -- continuous in `(L, P)`.
  let G : (Ambient n ℓ →L[ℝ] Ambient n ℓ) → (Ambient n ℓ →L[ℝ] Ambient n ℓ) → ℝ := fun L P ↦
    Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (n + ℓ) ↦
      inner ℝ (L (P (EuclideanSpace.single i (1 : ℝ)))) (L (P (EuclideanSpace.single j (1 : ℝ)))) +
        inner ℝ (EuclideanSpace.single i (1 : ℝ) - P (EuclideanSpace.single i (1 : ℝ)))
          (EuclideanSpace.single j (1 : ℝ) - P (EuclideanSpace.single j (1 : ℝ)))))
  have hG : Continuous (Function.uncurry G) := by
    refine Real.continuous_sqrt.comp (Continuous.matrix_det (continuous_matrix fun i j ↦ ?_))
    simp only [Matrix.of_apply]
    fun_prop
  -- `trace (L ∘ P)` is continuous in `(L, P)`; at `(DX(x), p_{T_x V})` it is `div_M X(x)`.
  have hT : Continuous (Function.uncurry fun L P : Ambient n ℓ →L[ℝ] Ambient n ℓ ↦
      LinearMap.trace ℝ (Ambient n ℓ) (L.toLinearMap ∘ₗ P.toLinearMap)) :=
    ((LinearMap.trace ℝ (Ambient n ℓ)).comp
      (ContinuousLinearMap.coeLM ℝ)).continuous_of_finiteDimensional.comp
        (continuous_fst.clm_comp continuous_snd)
  -- The tangential Jacobian `J_t(x) = J^{T_x V}(Dφ_t(x))` and its `t`-derivative.
  let J : ℝ → Ambient n ℓ → ℝ := fun t x ↦
    G (fderiv ℝ (φ t) x) ((mk a).tangentSpace x).starProjection
  let J' : ℝ → Ambient n ℓ → ℝ := fun t x ↦ deriv (fun s ↦ J s x) t
  -- Differentiation under the integral sign, dominated by `A θ` on `M ∩ K`.
  refine Submission.ts_fv_hasDerivAt_of_weighted_jacobian n ℓ a K
    (fun t ↦ imageMass a (φ t) K) J J'
    (fun x ↦ (mk a).tangentialDiv (fun y ↦ deriv (fun t ↦ φ t y) 0) x) δ A hδ hV.compact
    (fun t ht ↦ ?_) (fun t ht ↦ ?_) ?_ (fun x hx ↦ ?_) (ae_of_all _ fun x _ ↦ ?_)
  · -- the area formula for the injective Lipschitz map `φ_t` on `M ∩ K`
    exact Submission.ts_fv_image_mass_area_formula n ℓ a N₀ C F (φ t) K hn hN₀ hN₀0 hcover
      hpieces htan (hV.diffeo t (hε t ht)).1.injective (hφ t (hε t ht)).1
      ((hφ t (hε t ht)).2.differentiable one_ne_zero) hV.compact.isClosed.measurableSet
  · exact hG.comp_aestronglyMeasurable₂
      (((hφ t (hε t ht)).2.continuous_fderiv one_ne_zero).aestronglyMeasurable) hproj
  · exact hT.comp_aestronglyMeasurable₂ ((hX.continuous_fderiv one_ne_zero).aestronglyMeasurable)
      hproj
  · show LinearMap.trace ℝ (Ambient n ℓ) ((fderiv ℝ (fun y ↦ deriv (fun t ↦ φ t y) 0) x).toLinearMap
      ∘ₗ ((mk a).tangentSpace x).starProjection.toLinearMap) = 0
    rw [hDX x hx, ContinuousLinearMap.toLinearMap_zero, LinearMap.zero_comp, map_zero]
  · -- Jacobi's formula along `t ↦ Dφ_t(x)` in the plane `T_x V`, for every `x`
    obtain ⟨hbd, hd0⟩ := hA ((mk a).tangentSpace x) (fun s ↦ fderiv ℝ (φ s) x) (fun s ↦ Λ' s x)
      (fun s ↦ J s x) δ hδ (hφ0 x) (fun t ht ↦ (hΛ' x).2 t ht) fun t ↦ rfl
    refine ⟨?_, fun t ht ↦ ?_⟩
    · rw [show J' 0 x = _ from hd0.deriv]
      beta_reduce
      rw [(hΛ' x).1]
      rfl
    · obtain ⟨hJ0, hJA, d, hd, hdA⟩ := hbd t ht
      have hJ' : J' t x = d := hd.deriv
      exact ⟨hJ0, hJA, hJ' ▸ hd, hJ' ▸ hdA⟩

/-- Simon Ch. 3, proof of Theorem 1.6 (⇒) with Remark 1.8(1), and Ch. 4, 1.1 (pp. 71–72, 75, 86):
the weighted blow-up at a good point of a Lusin piece. Let `μ = μ_V` for `V = v(M, θ)`, let
`N` be Borel with `Hⁿ(N) < ∞`, `K ⊆ M ∩ N` compact, `θ|K` continuous at `x`, and `f ∈ C_c`.
If `Hⁿ(N ∩ B_ρ(x)) ≤ Γρⁿ` for `ρ > 0`, `μ(B_r(x) \ K) / rⁿ → 0`, `Hⁿ(N ∩ B_r(x) \ K) / rⁿ → 0`
and `t⁻ⁿ ∫_N f(t⁻¹(y - x)) dHⁿ(y) → L`, then `t⁻ⁿ ∫ f(t⁻¹(y - x)) dμ(y) → θ(x) L` as `t ↓ 0`.
With `g_t = f(t⁻¹(· - x))`, which vanishes off `B_{Rt}(x)` when `f` vanishes off `B_R(0)`,
`t⁻ⁿ ∫ g_t dμ = θ(x) t⁻ⁿ ∫_N g_t - θ(x) t⁻ⁿ ∫_{N \ K} g_t + t⁻ⁿ ∫_K (θ - θ(x)) g_t
  + t⁻ⁿ ∫_{Kᶜ} g_t dμ`, and the last three terms tend to `0`. -/
theorem Submission.ts_pwb_blowup_at_good_point : ∀ (n ℓ : ℕ) (a : RectifiablePair n ℓ) (N K : Set (Ambient n ℓ)) (x : Ambient n ℓ) (f : C_c(Ambient n ℓ, ℝ)) (Γ L : ℝ), MeasurableSet N → (μHE[n] : Measure (Ambient n ℓ)) N ≠ ⊤ → IsCompact K → K ⊆ a.M ∩ N → x ∈ K → ContinuousWithinAt a.θ K x → (∀ ρ : ℝ, 0 < ρ → (μHE[n] : Measure (Ambient n ℓ)) (N ∩ closedBall x ρ) ≤ ENNReal.ofReal (Γ * ρ ^ n)) → Tendsto (fun r : ℝ ↦ (mk a).weight.real (Kᶜ ∩ closedBall x r) / r ^ n) (𝓝[>] 0) (𝓝 0) → Tendsto (fun r : ℝ ↦ ((μHE[n] : Measure (Ambient n ℓ)).restrict N).real (Kᶜ ∩ closedBall x r) / r ^ n) (𝓝[>] 0) (𝓝 0) → Tendsto (fun t : ℝ ↦ (t ^ n)⁻¹ * ∫ y in N, f (t⁻¹ • (y - x)) ∂μHE[n]) (𝓝[>] 0) (𝓝 L) → Tendsto (fun t : ℝ ↦ (t ^ n)⁻¹ * ∫ y, f (t⁻¹ • (y - x)) ∂(mk a).weight) (𝓝[>] 0) (𝓝 (a.θ x * L)) := by
  intro n ℓ a N K x f Γ L hNm hNfin hKc hKMN _ hθc hΓ hA hB hI1
  -- `μ_V` is finite on compact sets and `∫ h dμ_V = ∫_M θ h dHⁿ` for every `h`.
  obtain ⟨hfin, hint⟩ := Submission.ts_pwb_pair_weight_integral n ℓ a
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hKM : K ⊆ a.M := fun y hy ↦ (hKMN hy).1
  have hKN : K ⊆ N := fun y hy ↦ (hKMN hy).2
  have hMm := a.isRectifiablePair.measurable
  -- `|f| ≤ m`, and `f = 0` off `B_R(0)`.
  obtain ⟨m, hm⟩ : ∃ m, ∀ z, ‖f z‖ ≤ m :=
    f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  have hm0 : 0 ≤ m := (norm_nonneg _).trans (hm 0)
  obtain ⟨R, hR, hRs⟩ : ∃ R : ℝ, 0 < R ∧ ∀ z, R < ‖z‖ → f z = 0 := by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 f.hasCompactSupport.isCompact.isBounded
    refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun z hz ↦ ?_⟩
    apply image_eq_zero_of_notMem_tsupport
    intro hzs
    exact absurd (hC z hzs) (not_le.2 (lt_of_le_of_lt (le_max_left _ _) hz))
  -- `g_t = f(t⁻¹(· - x))` is continuous, bounded by `m`, and vanishes off `B_{Rt}(x)`.
  set g : ℝ → Ambient n ℓ → ℝ := fun t y ↦ f (t⁻¹ • (y - x)) with hg
  have hgc : ∀ t, Continuous (g t) := fun t ↦
    f.continuous.comp (by fun_prop)
  have hgb : ∀ t y, ‖g t y‖ ≤ m := fun t y ↦ hm _
  have hgs : ∀ t, 0 < t → ∀ y, y ∉ closedBall x (R * t) → g t y = 0 := by
    intro t ht y hy
    apply hRs
    rw [mem_closedBall, dist_eq_norm, not_le] at hy
    rw [norm_smul, norm_inv, Real.norm_of_nonneg ht.le, lt_inv_mul_iff₀ ht]
    linarith [mul_comm R t]
  -- Integrability: `g_t` on `N` (as `Hⁿ(N) < ∞`), and `θ g_t` on `M` (it vanishes off the
  -- compact ball `B_{Rt}(x)`, on which `θ` is integrable).
  have hgN : ∀ t, IntegrableOn (g t) N μHE[n] := fun t ↦
    IntegrableOn.of_bound (lt_top_iff_ne_top.2 hNfin) (hgc t).aestronglyMeasurable m
      (Eventually.of_forall (hgb t))
  have hθg : ∀ t, 0 < t → IntegrableOn (fun y ↦ a.θ y * g t y) a.M μHE[n] := by
    intro t ht
    have h1 : IntegrableOn a.θ (a.M ∩ closedBall x (R * t)) μHE[n] :=
      a.isRectifiablePair.locallyIntegrable _ (isCompact_closedBall _ _)
    have h2 : IntegrableOn (fun y ↦ a.θ y * g t y) (a.M ∩ closedBall x (R * t)) μHE[n] :=
      Integrable.mul_bdd h1 (hgc t).aestronglyMeasurable (Eventually.of_forall (hgb t))
    refine h2.of_ae_sdiff_eq_zero hMm (Eventually.of_forall fun y hy ↦ ?_)
    rw [hgs t ht y (fun hyB ↦ hy.2 ⟨hy.1, hyB⟩), mul_zero]
  -- The four-term decomposition `t⁻ⁿ ∫ g_t dμ = θ(x) T₁ - θ(x) T₂ + T₃ + T₄`.
  have hdec : ∀ t, 0 < t → (t ^ n)⁻¹ * ∫ y, g t y ∂(mk a).weight =
      a.θ x * ((t ^ n)⁻¹ * ∫ y in N, g t y ∂μHE[n]) -
        a.θ x * ((t ^ n)⁻¹ * ∫ y in N \ K, g t y ∂μHE[n]) +
        (t ^ n)⁻¹ * ∫ y in K, (a.θ y - a.θ x) * g t y ∂μHE[n] +
        (t ^ n)⁻¹ * ∫ y in Kᶜ, g t y ∂(mk a).weight := by
    intro t ht
    have e1 : ∫ y, g t y ∂(mk a).weight = ∫ y in a.M, a.θ y * g t y ∂μHE[n] := hint (g t)
    have e2 : ∫ y in a.M, a.θ y * g t y ∂μHE[n] =
        ∫ y in K, a.θ y * g t y ∂μHE[n] + ∫ y in a.M \ K, a.θ y * g t y ∂μHE[n] := by
      rw [← integral_inter_add_sdiff hKm (hθg t ht), inter_eq_right.2 hKM]
    have e3 : ∫ y in a.M \ K, a.θ y * g t y ∂μHE[n] = ∫ y in Kᶜ, g t y ∂(mk a).weight := by
      rw [← integral_indicator hKm.compl, hint, sdiff_eq, ← setIntegral_indicator hKm.compl]
      congr 1
      ext y
      by_cases hy : y ∈ Kᶜ <;> simp [indicator, hy]
    have hgK : IntegrableOn (g t) K μHE[n] := (hgN t).mono_set hKN
    have hθgK : IntegrableOn (fun y ↦ a.θ y * g t y) K μHE[n] := (hθg t ht).mono_set hKM
    have e4 : ∫ y in K, a.θ y * g t y ∂μHE[n] =
        a.θ x * ∫ y in K, g t y ∂μHE[n] + ∫ y in K, (a.θ y - a.θ x) * g t y ∂μHE[n] := by
      have : (fun y ↦ (a.θ y - a.θ x) * g t y) = fun y ↦ a.θ y * g t y - a.θ x * g t y := by
        ext y; ring
      rw [this, integral_sub hθgK (hgK.const_mul _), integral_const_mul]
      ring
    have e5 : ∫ y in K, g t y ∂μHE[n] = ∫ y in N, g t y ∂μHE[n] - ∫ y in N \ K, g t y ∂μHE[n] := by
      rw [← integral_inter_add_sdiff hKm (hgN t), inter_eq_right.2 hKN]
      ring
    rw [e1, e2, e3, e4, e5]
    ring
  -- Rescaling the excess-density hypotheses by `r = Rt`.
  have hRt : Tendsto (fun t : ℝ ↦ R * t) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun t : ℝ ↦ R * t) (𝓝 0) (𝓝 (R * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_pos hR ht
  have hA' := hA.comp hRt
  have hB' := hB.comp hRt
  -- `|T₂(t)| ≤ m Rⁿ (Hⁿ ⌞ N)(Kᶜ ∩ B_{Rt}(x)) / (Rt)ⁿ → 0`.
  have hT2 : Tendsto (fun t ↦ (t ^ n)⁻¹ * ∫ y in N \ K, g t y ∂μHE[n]) (𝓝[>] 0) (𝓝 0) := by
    have hlim : Tendsto (fun t ↦ m * R ^ n * (((μHE[n] : Measure (Ambient n ℓ)).restrict N).real
        (Kᶜ ∩ closedBall x (R * t)) / (R * t) ^ n)) (𝓝[>] 0) (𝓝 0) := by
      simpa using hB'.const_mul (m * R ^ n)
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : (0 : ℝ) < t := ht
    have hsplit : ∫ y in N \ K, g t y ∂μHE[n] =
        ∫ y in (N \ K) ∩ closedBall x (R * t), g t y ∂μHE[n] :=
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hNm.diff hKm) inter_subset_left
        (fun y hy ↦ hgs t ht' y (fun hyB ↦ hy.2 ⟨hy.1, hyB⟩))
    have hmeas : (μHE[n] : Measure (Ambient n ℓ)) ((N \ K) ∩ closedBall x (R * t)) < ⊤ :=
      (measure_mono (inter_subset_left.trans sdiff_subset)).trans_lt (lt_top_iff_ne_top.2 hNfin)
    have hbound := norm_setIntegral_le_of_norm_le_const hmeas (fun y _ ↦ hgb t y)
    have hreal : (μHE[n] : Measure (Ambient n ℓ)).real ((N \ K) ∩ closedBall x (R * t)) =
        ((μHE[n] : Measure (Ambient n ℓ)).restrict N).real (Kᶜ ∩ closedBall x (R * t)) := by
      rw [Measure.real, Measure.real,
        Measure.restrict_apply (hKm.compl.inter measurableSet_closedBall)]
      congr 2
      ext y
      simp only [mem_inter_iff, Set.mem_sdiff, mem_compl_iff]
      tauto
    rw [norm_mul, hsplit, norm_inv, norm_pow, Real.norm_of_nonneg ht'.le]
    calc (t ^ n)⁻¹ * ‖∫ y in (N \ K) ∩ closedBall x (R * t), g t y ∂μHE[n]‖
        ≤ (t ^ n)⁻¹ * (m * (μHE[n] : Measure (Ambient n ℓ)).real
            ((N \ K) ∩ closedBall x (R * t))) := by gcongr
      _ = m * R ^ n * (((μHE[n] : Measure (Ambient n ℓ)).restrict N).real
            (Kᶜ ∩ closedBall x (R * t)) / (R * t) ^ n) := by
        rw [hreal, mul_pow]
        field_simp
  -- `|T₄(t)| ≤ m Rⁿ μ_V(Kᶜ ∩ B_{Rt}(x)) / (Rt)ⁿ → 0`.
  have hT4 : Tendsto (fun t ↦ (t ^ n)⁻¹ * ∫ y in Kᶜ, g t y ∂(mk a).weight) (𝓝[>] 0) (𝓝 0) := by
    have hlim : Tendsto (fun t ↦ m * R ^ n * ((mk a).weight.real
        (Kᶜ ∩ closedBall x (R * t)) / (R * t) ^ n)) (𝓝[>] 0) (𝓝 0) := by
      simpa using hA'.const_mul (m * R ^ n)
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : (0 : ℝ) < t := ht
    have hsplit : ∫ y in Kᶜ, g t y ∂(mk a).weight =
        ∫ y in Kᶜ ∩ closedBall x (R * t), g t y ∂(mk a).weight :=
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hKm.compl inter_subset_left
        (fun y hy ↦ hgs t ht' y (fun hyB ↦ hy.2 ⟨hy.1, hyB⟩))
    have hmeas : (mk a).weight (Kᶜ ∩ closedBall x (R * t)) < ⊤ :=
      (measure_mono inter_subset_right).trans_lt (isCompact_closedBall _ _).measure_lt_top
    rw [norm_mul, hsplit, norm_inv, norm_pow, Real.norm_of_nonneg ht'.le]
    calc (t ^ n)⁻¹ * ‖∫ y in Kᶜ ∩ closedBall x (R * t), g t y ∂(mk a).weight‖
        ≤ (t ^ n)⁻¹ * (m * (mk a).weight.real (Kᶜ ∩ closedBall x (R * t))) := by
          gcongr
          exact norm_setIntegral_le_of_norm_le_const hmeas (fun y _ ↦ hgb t y)
      _ = m * R ^ n * ((mk a).weight.real (Kᶜ ∩ closedBall x (R * t)) / (R * t) ^ n) := by
        rw [mul_pow]
        field_simp
  -- `|T₃(t)| ≤ (ε / c) m Rⁿ max(Γ, 0) < ε` for `0 < t < δ / R`, by continuity of `θ|K` at `x`
  -- and the bound `Hⁿ(K ∩ B_{Rt}(x)) ≤ Hⁿ(N ∩ B_{Rt}(x)) ≤ Γ (Rt)ⁿ`.
  have hT3 : Tendsto (fun t ↦ (t ^ n)⁻¹ * ∫ y in K, (a.θ y - a.θ x) * g t y ∂μHE[n])
      (𝓝[>] 0) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    set c := m * max Γ 0 * R ^ n + 1 with hc
    have hc0 : 0 < c := by positivity
    obtain ⟨δ, hδ, hδθ⟩ := Metric.continuousWithinAt_iff.1 hθc (ε / c) (div_pos hε hc0)
    filter_upwards [Ioo_mem_nhdsGT (div_pos hδ hR)] with t ht
    obtain ⟨ht0, htδ⟩ := ht
    have hRtδ : R * t < δ := by
      rw [lt_div_iff₀ hR] at htδ
      linarith [mul_comm R t]
    have hsplit : ∫ y in K, (a.θ y - a.θ x) * g t y ∂μHE[n] =
        ∫ y in K ∩ closedBall x (R * t), (a.θ y - a.θ x) * g t y ∂μHE[n] :=
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hKm inter_subset_left
        (fun y hy ↦ by rw [hgs t ht0 y (fun hyB ↦ hy.2 ⟨hy.1, hyB⟩), mul_zero])
    have hmeasN : (μHE[n] : Measure (Ambient n ℓ)) (N ∩ closedBall x (R * t)) < ⊤ :=
      (measure_mono inter_subset_left).trans_lt (lt_top_iff_ne_top.2 hNfin)
    have hmeasK : (μHE[n] : Measure (Ambient n ℓ)) (K ∩ closedBall x (R * t)) < ⊤ :=
      (measure_mono (inter_subset_inter_left _ hKN)).trans_lt hmeasN
    have hpt : ∀ y ∈ K ∩ closedBall x (R * t), ‖(a.θ y - a.θ x) * g t y‖ ≤ ε / c * m := by
      intro y hy
      rw [norm_mul]
      have h1 : dist y x < δ := lt_of_le_of_lt (mem_closedBall.1 hy.2) hRtδ
      have h2 := hδθ hy.1 h1
      rw [Real.dist_eq] at h2
      exact mul_le_mul (le_of_lt (by simpa [Real.norm_eq_abs] using h2)) (hgb t y)
        (norm_nonneg _) (div_pos hε hc0).le
    have hbound := norm_setIntegral_le_of_norm_le_const hmeasK hpt
    have hKreal : (μHE[n] : Measure (Ambient n ℓ)).real (K ∩ closedBall x (R * t)) ≤
        max Γ 0 * (R * t) ^ n := by
      calc (μHE[n] : Measure (Ambient n ℓ)).real (K ∩ closedBall x (R * t))
          ≤ (μHE[n] : Measure (Ambient n ℓ)).real (N ∩ closedBall x (R * t)) :=
            measureReal_mono (inter_subset_inter_left _ hKN) hmeasN.ne
        _ ≤ (ENNReal.ofReal (Γ * (R * t) ^ n)).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top (hΓ _ (mul_pos hR ht0))
        _ = max (Γ * (R * t) ^ n) 0 := ENNReal.toReal_ofReal'
        _ ≤ max Γ 0 * (R * t) ^ n := by
          have hp : 0 ≤ (R * t) ^ n := by positivity
          rcases le_total Γ 0 with h | h
          · rw [max_eq_right h, max_eq_right (mul_nonpos_of_nonpos_of_nonneg h hp), zero_mul]
          · rw [max_eq_left h, max_eq_left (mul_nonneg h hp)]
    rw [dist_zero_right, norm_mul, hsplit, norm_inv, norm_pow, Real.norm_of_nonneg ht0.le]
    have hεc : 0 ≤ ε / c * m := mul_nonneg (div_pos hε hc0).le hm0
    calc (t ^ n)⁻¹ * ‖∫ y in K ∩ closedBall x (R * t), (a.θ y - a.θ x) * g t y ∂μHE[n]‖
        ≤ (t ^ n)⁻¹ * (ε / c * m * (μHE[n] : Measure (Ambient n ℓ)).real
            (K ∩ closedBall x (R * t))) := by gcongr
      _ ≤ (t ^ n)⁻¹ * (ε / c * m * (max Γ 0 * (R * t) ^ n)) := by gcongr
      _ = ε / c * (m * max Γ 0 * R ^ n) := by
        rw [mul_pow]
        field_simp
      _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ hc0, hc]
        nlinarith
  -- Sum the four limits: `θ(x) L - θ(x) · 0 + 0 + 0 = θ(x) L`.
  have hsum := (((hI1.const_mul (a.θ x)).sub (hT2.const_mul (a.θ x))).add hT3).add hT4
  rw [mul_zero, sub_zero, add_zero, add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (hdec t ht).symm

/-- **Weighted blow-up on one Lipschitz piece (Simon Ch. 3, 1.9 via 1.6 and 1.8(1)).** For a
Lipschitz piece `(C, F)` and `Hⁿ`-a.e. `x ∈ M`, at every `w ∈ C` with `F(w) = x` the blow-ups of
`μ_V` converge: `t⁻ⁿ ∫ f(t⁻¹(y - x)) dμ_V(y) → θ(x) ∫_{DF(w)(ℝⁿ)} f dHⁿ` as `t ↓ 0`. -/
theorem Submission.ts_piece_weighted_blowup_ae : ∀ (n ℓ : ℕ) (a : RectifiablePair n ℓ) (C : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → Ambient n ℓ), 0 < n → (IsCompact C ∧ (∃ K : NNReal, LipschitzWith K F) ∧ (∀ w ∈ C, DifferentiableAt ℝ F w ∧ Function.Injective (fderiv ℝ F w)) ∧ ContinuousOn (fderiv ℝ F) C ∧ ∃ c : ℝ, 0 < c ∧ ∀ v ∈ C, ∀ w ∈ C, c * ‖v - w‖ ≤ ‖F v - F w‖) → ∀ᵐ x ∂(μHE[n] : Measure (Ambient n ℓ)).restrict a.M, ∀ w ∈ C, F w = x → ∀ f : C_c(Ambient n ℓ, ℝ), Tendsto (fun t : ℝ ↦ (t ^ n)⁻¹ * ∫ y, f (t⁻¹ • (y - x)) ∂(mk a).weight) (𝓝[>] 0) (𝓝 (a.θ x * ∫ y in (LinearMap.range (fderiv ℝ F w).toLinearMap : Set (Ambient n ℓ)), f y ∂μHE[n])) := by
  intro n ℓ a C F hn hpiece
  have hC : IsCompact C := hpiece.1
  obtain ⟨κ, hF⟩ := hpiece.2.1
  have hM := a.isRectifiablePair.measurable
  -- the sibling: `Hⁿ(F(C) ∩ B_ρ(z)) ≤ Γρⁿ` on `F(C)`, and the blow-up of `Hⁿ ⌞ F(C)` at the
  -- image of every density point of `C`
  obtain ⟨⟨Γ, hΓ⟩, hblow⟩ := Submission.ts_piece_density_blowup n ℓ C F hn hpiece
  -- `F(C)` is compact, hence Borel, and `Hⁿ(F(C)) < ∞`
  have hNc : IsCompact (F '' C) := hC.image hF.continuous
  have hNm : MeasurableSet (F '' C) := hNc.isClosed.measurableSet
  have hNfin : (μHE[n] : Measure (Ambient n ℓ)) (F '' C) ≠ ⊤ := by
    rcases (F '' C).eq_empty_or_nonempty with h | ⟨z, hz⟩
    · rw [h, measure_empty]
      exact ENNReal.zero_ne_top
    obtain ⟨r, hr⟩ := hNc.isBounded.subset_closedBall z
    have h := hΓ z hz (max r 1) (one_pos.trans_le (le_max_right r 1))
    rw [inter_eq_left.2 (hr.trans (closedBall_subset_closedBall (le_max_left r 1)))] at h
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  -- Lusin: compact `K k ⊆ M ∩ F(C)`, with `θ` continuous on each, cover `M ∩ F(C)` up to an
  -- `Hⁿ`-null set
  obtain ⟨K, hK, hKnull⟩ := Submission.ts_pwb_lusin_compact_cover n ℓ μHE[n] (a.M ∩ F '' C) a.θ
    (hM.inter hNm.nullMeasurableSet)
    (ne_top_of_le_ne_top hNfin (measure_mono inter_subset_right))
    (Integrable.aestronglyMeasurable (a.isRectifiablePair.locallyIntegrable _ hNc))
  -- upper densities of `μ_V ⌞ (K k)ᶜ` and of `Hⁿ ⌞ (F(C) \ K k)` vanish `Hⁿ`-a.e. on `K k`
  have hfin : IsFiniteMeasureOnCompacts ((μHE[n] : Measure (Ambient n ℓ)).restrict (F '' C)) := by
    have : IsFiniteMeasure ((μHE[n] : Measure (Ambient n ℓ)).restrict (F '' C)) :=
      isFiniteMeasure_restrict.2 hNfin
    infer_instance
  have hA := fun k ↦ Submission.ts_pwb_upper_density_vanish_ae n ℓ (mk a).weight (K k)ᶜ
    (Submission.ts_pwb_pair_weight_integral n ℓ a).1 (hK k).1.isClosed.measurableSet.compl
  have hB := fun k ↦ Submission.ts_pwb_upper_density_vanish_ae n ℓ _ (K k)ᶜ hfin
    (hK k).1.isClosed.measurableSet.compl
  -- `Hⁿ`-a.e. point of `F(C)` is the image of density points of `C` only
  have hD := Submission.ts_pwb_density_points_of_image_ae n ℓ C F hC.isClosed.measurableSet ⟨κ, hF⟩
  filter_upwards [ae_restrict_mem₀ hM, ae_restrict_of_ae (ae_all_iff.2 hA),
    ae_restrict_of_ae (ae_all_iff.2 hB), ae_restrict_of_ae hD,
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hKnull)] with x hxM hxA hxB hxD hxK
  intro w hw hFw f
  have hxN : x ∈ F '' C := ⟨w, hw, hFw⟩
  obtain ⟨k, hk⟩ := mem_iUnion.1 (not_not.1 fun h ↦ hxK ⟨⟨hxM, hxN⟩, h⟩)
  have hL := hblow w hw (hxD w hw hFw) f
  rw [hFw] at hL
  exact Submission.ts_pwb_blowup_at_good_point n ℓ a (F '' C) (K k) x f Γ _ hNm hNfin (hK k).1
    (hK k).2.1 hk ((hK k).2.2 x hk) (hΓ x hxN) (hxA k fun h ↦ h hk) (hxB k fun h ↦ h hk) hL
/-- **Continuity of the projection onto the range** (used for the tangent field of a `C¹` piece,
Ch. 4, 1.3). On injective `A ∈ L(ℝⁿ, ℝ^{n+ℓ})`, `A ↦ p_{A(ℝⁿ)}` is continuous: there
`p_{A(ℝⁿ)} = A (A*A)⁻¹ A*`, with `A*A` invertible, and inversion is continuous at units. -/
theorem Submission.ts_starProjection_range_continuousOn_injective : ∀ (n ℓ : ℕ), ContinuousOn (fun (A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ) ↦ (LinearMap.range A.toLinearMap).starProjection) {A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ | Function.Injective A} := by
  intro n ℓ
  -- Riesz construction of the adjoint `A ↦ A*` (Mathlib's `adjointAux`, rebuilt from
  -- `toDual` and `toSesqForm`, which the frozen imports provide).
  set adj : (EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ) →L⋆[ℝ]
      (Ambient n ℓ →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
    (ContinuousLinearMap.compSL _ _ _ _ _
      ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm :
        StrongDual ℝ (EuclideanSpace ℝ (Fin n)) →L⋆[ℝ] EuclideanSpace ℝ (Fin n))).comp
      (ContinuousLinearMap.toSesqForm :
        (EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ) →L[ℝ]
          Ambient n ℓ →L⋆[ℝ] StrongDual ℝ (EuclideanSpace ℝ (Fin n))) with hadj
  have hadj_inner : ∀ (A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ) (y : Ambient n ℓ)
      (x : EuclideanSpace ℝ (Fin n)), inner ℝ (adj A y) x = inner ℝ y (A x) := by
    intro A y x
    change inner ℝ ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
      (ContinuousLinearMap.toSesqForm A y)) x = _
    rw [InnerProductSpace.toDual_symm_apply, ContinuousLinearMap.toSesqForm_apply_coe]
    rfl
  -- `Φ(A) = A ∘ (A*A)⁻¹ ∘ A*`
  set Φ : (EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ) → (Ambient n ℓ →L[ℝ] Ambient n ℓ) :=
    fun A ↦ A ∘L (Ring.inverse (adj A ∘L A) ∘L adj A) with hΦ
  -- `A*A` is a unit for injective `A`: `⟪A*Av, v⟫ = ‖Av‖²`, and injective means bijective in
  -- finite dimension
  have hunit : ∀ A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ, Function.Injective A →
      IsUnit (adj A ∘L A) := by
    intro A hA
    have hinj : Function.Injective (adj A ∘L A) := by
      intro v w hvw
      have h0 : (adj A ∘L A) (v - w) = 0 := by
        rw [map_sub, hvw, sub_self]
      have h1 : ‖A (v - w)‖ ^ 2 = 0 := by
        rw [← real_inner_self_eq_norm_sq, ← hadj_inner]
        simp only [ContinuousLinearMap.comp_apply] at h0
        rw [h0, inner_zero_left]
      have h2 : A (v - w) = 0 := by
        simpa using h1
      have h3 : v - w = 0 := hA (by rw [h2, map_zero])
      exact sub_eq_zero.mp h3
    refine ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hinj, ?_⟩
    exact (LinearMap.injective_iff_surjective (f := (adj A ∘L A).toLinearMap)).mp hinj
  -- the projection formula `p_{A(ℝⁿ)} = Φ(A)`: `Φ(A)z ∈ A(ℝⁿ)` and `z - Φ(A)z ⊥ A(ℝⁿ)`
  have hformula : ∀ A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ, Function.Injective A →
      (LinearMap.range A.toLinearMap).starProjection = Φ A := by
    intro A hA
    ext1 z
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact ⟨_, rfl⟩
    · rintro _ ⟨v, rfl⟩
      rw [ContinuousLinearMap.coe_coe, ← hadj_inner, map_sub]
      have hcancel : adj A (Φ A z) = adj A z := by
        have := Ring.mul_inverse_cancel _ (hunit A hA)
        calc adj A (Φ A z)
            = ((adj A ∘L A) * Ring.inverse (adj A ∘L A)) (adj A z) := by
              simp only [hΦ, ContinuousLinearMap.comp_apply, mul_apply_eq_comp]
          _ = adj A z := by rw [this, one_apply_eq_self]
      rw [hcancel, sub_self, inner_zero_left]
  -- continuity of `Φ` at injective maps: `A ↦ A*` is continuous, `Ring.inverse` is continuous
  -- at units, and composition is continuous
  have hcont : ∀ A₀ : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ, Function.Injective A₀ →
      ContinuousAt Φ A₀ := by
    intro A₀ hA₀
    have hadjc : Continuous fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ ↦ adj A :=
      adj.continuous
    have hgram : Continuous fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ ↦
        adj A ∘L A := hadjc.clm_comp continuous_id
    have hinv : ContinuousAt (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ ↦
        Ring.inverse (adj A ∘L A)) A₀ := by
      have := NormedRing.inverse_continuousAt (hunit A₀ hA₀).unit
      exact ContinuousAt.comp (f := fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ ↦
        adj A ∘L A) (by simpa using this) hgram.continuousAt
    exact continuousAt_id.clm_comp (hinv.clm_comp hadjc.continuousAt)
  -- `p_{A(ℝⁿ)}` agrees with `Φ` on the injective maps, so it is continuous there
  intro A₀ hA₀
  exact ((hcont A₀ hA₀).continuousWithinAt).congr (fun A hA ↦ hformula A hA) (hformula A₀ hA₀)

/-- **The tangent projection of a `C¹` piece, as a function on its image** (Ch. 4, 1.3). If
`c‖v - w‖ ≤ ‖F v - F w‖` on `C` with `c > 0`, and `DF` is injective and continuous on `C`, then
`y ↦ p_{DF(ψ y)(ℝⁿ)}` is continuous on `F(C)`, where `ψ` inverts `F` on `C` and is
`c⁻¹`-Lipschitz on `F(C)`. -/
theorem Submission.ts_piece_projection_continuousOn_image : ∀ (n ℓ : ℕ) (C : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → Ambient n ℓ) (c : ℝ), 0 < c → (∀ v ∈ C, ∀ w ∈ C, c * ‖v - w‖ ≤ ‖F v - F w‖) → (∀ w ∈ C, Function.Injective (fderiv ℝ F w)) → ContinuousOn (fderiv ℝ F) C → ∃ G : Ambient n ℓ → (Ambient n ℓ →L[ℝ] Ambient n ℓ), ContinuousOn G (F '' C) ∧ ∀ w ∈ C, G (F w) = (LinearMap.range (fderiv ℝ F w).toLinearMap).starProjection := by
  intro n ℓ C F c hc hlow hinj hcont
  classical
  -- `F` is injective on `C`: `F v = F w` forces `c‖v - w‖ ≤ 0`
  have hInjOn : Set.InjOn F C := by
    intro v hv w hw hvw
    have h := hlow v hv w hw
    rw [hvw, sub_self, norm_zero] at h
    have h' : ‖v - w‖ ≤ 0 := by
      by_contra hpos
      exact absurd h (not_le.mpr (mul_pos hc (lt_of_not_ge hpos)))
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h')
  -- the inverse `ψ` of `F` on `C`
  set ψ : Ambient n ℓ → EuclideanSpace ℝ (Fin n) := Function.invFunOn F C with hψ
  have hψmaps : Set.MapsTo ψ (F '' C) C := fun y hy ↦ Function.invFunOn_mem hy
  have hFψ : ∀ y ∈ F '' C, F (ψ y) = y := fun y hy ↦ Function.invFunOn_eq hy
  have hψF : ∀ w ∈ C, ψ (F w) = w := fun w hw ↦ hInjOn.leftInvOn_invFunOn hw
  -- `ψ` is `c⁻¹`-Lipschitz, hence continuous, on `F(C)`
  have hψcont : ContinuousOn ψ (F '' C) := by
    refine (LipschitzOnWith.of_dist_le_mul (K := Real.toNNReal c⁻¹) fun y hy y' hy' ↦ ?_).continuousOn
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (inv_nonneg.mpr hc.le)]
    have h := hlow (ψ y) (hψmaps hy) (ψ y') (hψmaps hy')
    rw [hFψ y hy, hFψ y' hy'] at h
    rw [inv_mul_eq_div, le_div_iff₀ hc, mul_comm]
    exact h
  -- `G = p ∘ DF ∘ ψ`: `ψ` maps `F(C)` into `C`, where `DF` is continuous with injective values,
  -- and `A ↦ p_{A(ℝⁿ)}` is continuous on the injective maps
  refine ⟨fun y ↦ (LinearMap.range (fderiv ℝ F (ψ y)).toLinearMap).starProjection, ?_, ?_⟩
  · exact (Submission.ts_starProjection_range_continuousOn_injective n ℓ).comp
      (hcont.comp hψcont hψmaps) (fun y hy ↦ hinj (ψ y) (hψmaps hy))
  · intro w hw
    simp only [hψF w hw]
/-- **Borel pasting of relatively continuous operator fields** (the field on the disjointified
pieces `N_i \ ⋃_{j<i} N_j`). If every `N_i ⊆ ℝ^{n+ℓ}` is measurable and every
`G_i : ℝ^{n+ℓ} → L(ℝ^{n+ℓ}, ℝ^{n+ℓ})` is continuous on `N_i`, then some strongly measurable `g`
equals `G_i` on `N_i \ ⋃_{j<i} N_j` for every `i`: `g y = G_{i(y)} y` for the least `i(y)` with
`y ∈ N_{i(y)}`, and `g = 0` off `⋃_i N_i`. -/
theorem Submission.ts_stronglyMeasurable_paste_continuousOn : ∀ (n ℓ : ℕ) (N : ℕ → Set (Ambient n ℓ)) (G : ℕ → Ambient n ℓ → (Ambient n ℓ →L[ℝ] Ambient n ℓ)), (∀ i, MeasurableSet (N i)) → (∀ i, ContinuousOn (G i) (N i)) → ∃ g : Ambient n ℓ → (Ambient n ℓ →L[ℝ] Ambient n ℓ), StronglyMeasurable g ∧ ∀ i, ∀ y ∈ N i, (∀ j < i, y ∉ N j) → g y = G i y := by
  intro n ℓ N G hN hG
  classical
  -- `G' i` extends `G i` by `0` off `N i`; it is Borel as `G i` is continuous on the Borel `N i`.
  set G' : ℕ → Ambient n ℓ → (Ambient n ℓ →L[ℝ] Ambient n ℓ) :=
    fun i ↦ (N i).piecewise (G i) 0 with hG'
  have hG'meas : ∀ i, Measurable (G' i) := fun i ↦
    (hG i).measurable_piecewise continuousOn_const (hN i)
  -- The index `i` is admissible at `y` if `y ∈ N i` or `y` lies in no piece.
  set p : ℕ → Ambient n ℓ → Prop := fun i y ↦ y ∈ N i ∨ y ∉ ⋃ j, N j
  have hpex : ∀ y, ∃ i, p i y := by
    intro y
    by_cases hy : y ∈ ⋃ j, N j
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hy
      exact ⟨j, Or.inl hj⟩
    · exact ⟨0, Or.inr hy⟩
  have hpmeas : ∀ i, MeasurableSet {y | p i y} := fun i ↦
    (hN i).union (MeasurableSet.iUnion hN).compl
  -- `g y = G' i y` for the least admissible `i` is Borel (`Measurable.find`), hence strongly
  -- measurable since `L(ℝ^{n+ℓ}, ℝ^{n+ℓ})` is finite-dimensional.
  refine ⟨fun y ↦ G' (Nat.find (hpex y)) y, ?_, ?_⟩
  · exact (Measurable.find hG'meas hpmeas hpex).stronglyMeasurable
  · -- On `N i \ ⋃_{j<i} N j` the least admissible index is `i`.
    intro i y hy hfirst
    have hfind : Nat.find (hpex y) = i := by
      rw [Nat.find_eq_iff]
      refine ⟨Or.inl hy, fun j hj ↦ ?_⟩
      rintro (hjy | hnot)
      · exact hfirst j hj hjy
      · exact hnot (mem_iUnion.mpr ⟨i, hy⟩)
    simp only [hfind, hG', Set.piecewise_eq_of_mem _ _ _ hy]

/-- **Tangent projection field of a sequence of Lipschitz pieces** (measurability of
`x ↦ p_{T_x V}`, Ch. 4, 1.3). Let `C_i ⊆ ℝⁿ` be compact and `F_i : ℝⁿ → ℝ^{n+ℓ}` Lipschitz,
differentiable on `C_i` with injective `DF_i` continuous on `C_i`, and
`c_i|v - w| ≤ |F_i(v) - F_i(w)|` on `C_i` with `c_i > 0`. Then some strongly measurable
`g : ℝ^{n+ℓ} → L(ℝ^{n+ℓ}, ℝ^{n+ℓ})` is the orthogonal projection onto `DF_i(w)(ℝⁿ)` at `F_i(w)`
whenever `F_i(w) ∉ F_j(C_j)` for all `j < i`: the projection field of each piece is continuous
on the compact image `F_i(C_i)` (`ts_piece_projection_continuousOn_image`), and these fields are
pasted along `F_i(C_i) \ ⋃_{j<i} F_j(C_j)` (`ts_stronglyMeasurable_paste_continuousOn`). -/
theorem Submission.ts_piece_tangent_projection_field : ∀ (n ℓ : ℕ) (C : ℕ → Set (EuclideanSpace ℝ (Fin n))) (F : ℕ → EuclideanSpace ℝ (Fin n) → Ambient n ℓ), (∀ i, IsCompact (C i) ∧ (∃ K : NNReal, LipschitzWith K (F i)) ∧ (∀ w ∈ C i, DifferentiableAt ℝ (F i) w ∧ Function.Injective (fderiv ℝ (F i) w)) ∧ ContinuousOn (fderiv ℝ (F i)) (C i) ∧ ∃ c : ℝ, 0 < c ∧ ∀ v ∈ C i, ∀ w ∈ C i, c * ‖v - w‖ ≤ ‖F i v - F i w‖) → ∃ g : Ambient n ℓ → (Ambient n ℓ →L[ℝ] Ambient n ℓ), StronglyMeasurable g ∧ ∀ i, ∀ w ∈ C i, (∀ j < i, F i w ∉ F j '' C j) → g (F i w) = (LinearMap.range (fderiv ℝ (F i) w).toLinearMap).starProjection := by
  intro n ℓ C F hpiece
  -- Step 3: on each piece `N_i = F_i(C_i)` the projection field `G_i` is continuous, with
  -- `G_i(F_i(w)) = p_{DF_i(w)(ℝⁿ)}` for `w ∈ C_i`.
  have hG : ∀ i, ∃ G : Ambient n ℓ → (Ambient n ℓ →L[ℝ] Ambient n ℓ),
      ContinuousOn G (F i '' C i) ∧
        ∀ w ∈ C i, G (F i w) = (LinearMap.range (fderiv ℝ (F i) w).toLinearMap).starProjection := by
    intro i
    obtain ⟨-, -, hdiff, hcont, c, hc, hlow⟩ := hpiece i
    exact Submission.ts_piece_projection_continuousOn_image n ℓ (C i) (F i) c hc hlow
      (fun w hw ↦ (hdiff w hw).2) hcont
  choose G hGcont hGval using hG
  -- Step 4: `N_i` is compact, as the image of the compact `C_i` under the Lipschitz `F_i`, hence
  -- Borel.
  have hN : ∀ i, MeasurableSet (F i '' C i) := fun i ↦ by
    obtain ⟨hC, ⟨K, hK⟩, -⟩ := hpiece i
    exact (hC.image hK.continuous).measurableSet
  -- Step 5: paste the `G_i` along the disjointified pieces `N_i \ ⋃_{j<i} N_j`.
  obtain ⟨g, hgmeas, hg⟩ :=
    Submission.ts_stronglyMeasurable_paste_continuousOn n ℓ (fun i ↦ F i '' C i) G hN hGcont
  -- Step 6: at `F_i(w)` outside the earlier pieces, `g = G_i = p_{DF_i(w)(ℝⁿ)}`.
  refine ⟨g, hgmeas, fun i w hw hfirst ↦ ?_⟩
  rw [hg i (F i w) (mem_image_of_mem (F i) hw) hfirst, hGval i w hw]
/-- **Local lower bound at a regular point.** If `f : ℝⁿ → F` is differentiable at `w` and
`Df(w)` is injective, then for some `c > 0`, `c |u| ≤ |f(w + u) - f(w)|` whenever `|u| ≤ c`
(the pointwise step of the Lipschitz-piece replacement for Simon Ch. 3, Lemma 1.2). -/
theorem Submission.injective_fderiv_local_lower_bound : ∀ (n : ℕ) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : EuclideanSpace ℝ (Fin n) → F) (w : EuclideanSpace ℝ (Fin n)), DifferentiableAt ℝ f w → Function.Injective (fderiv ℝ f w) → ∃ c : ℝ, 0 < c ∧ ∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ ≤ c → c * ‖u‖ ≤ ‖f (w + u) - f w‖ := by
  intro n F _ _ f w hf hinj
  -- `L = Df(w)` is injective on the finite-dimensional `ℝⁿ`, so `‖u‖ ≤ K ‖L u‖` with `K > 0`.
  obtain ⟨K, hK, hKL⟩ :=
    (fderiv ℝ f w : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] F).exists_antilipschitzWith
      (LinearMap.ker_eq_bot.2 hinj)
  have hK' : (0 : ℝ) < K := hK
  -- With `m = K⁻¹`: `m ‖u‖ ≤ ‖L u‖` for all `u`.
  have hm : ∀ u, (K : ℝ)⁻¹ * ‖u‖ ≤ ‖fderiv ℝ f w u‖ := fun u ↦
    (inv_mul_le_iff₀ hK').2 (ZeroHomClass.bound_of_antilipschitz _ hKL u)
  have hm2 : 0 < (K : ℝ)⁻¹ / 2 := half_pos (inv_pos.2 hK')
  -- Differentiability: `‖f(w + u) - f(w) - L u‖ ≤ (m/2) ‖u‖` for `‖u‖ < r`.
  obtain ⟨r, hr, hfr⟩ := Metric.eventually_nhds_iff.1
    ((hasFDerivAt_iff_isLittleO_nhds_zero.1 hf.hasFDerivAt).bound hm2)
  -- `c = min(m/2, r/2)`.
  refine ⟨min ((K : ℝ)⁻¹ / 2) (r / 2), lt_min hm2 (half_pos hr), fun u hu ↦ ?_⟩
  have hur : dist u 0 < r := by
    rw [dist_zero_right]
    exact hu.trans_lt ((min_le_right _ _).trans_lt (half_lt_self hr))
  have h2 : ‖f (w + u) - f w - fderiv ℝ f w u‖ ≤ (K : ℝ)⁻¹ / 2 * ‖u‖ := hfr hur
  -- Triangle inequality: `‖L u‖ ≤ ‖f(w + u) - f(w)‖ + ‖f(w + u) - f(w) - L u‖`.
  have h3 : ‖fderiv ℝ f w u‖ ≤ ‖f (w + u) - f w‖ + ‖f (w + u) - f w - fderiv ℝ f w u‖ := by
    simpa only [sub_sub_cancel] using
      norm_sub_le (f (w + u) - f w) (f (w + u) - f w - fderiv ℝ f w u)
  calc min ((K : ℝ)⁻¹ / 2) (r / 2) * ‖u‖ ≤ (K : ℝ)⁻¹ / 2 * ‖u‖ :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg u)
    _ ≤ ‖f (w + u) - f w‖ := by linarith [hm u]
/-- **Lower Lipschitz pieces from pointwise local lower bounds.** If `f : ℝⁿ → F` is continuous
and every point `w` of the Borel set `R` has some `c > 0` with `c|u| ≤ |f(w + u) - f(w)|` for
`|u| ≤ c`, then `R` is covered by countably many bounded Borel sets `T_p ⊆ R`, on each of which
`f` satisfies a uniform lower Lipschitz bound `c_p|v - w| ≤ |f(v) - f(w)|`. -/
theorem Submission.lower_lipschitz_cover_of_local_bound : ∀ (n : ℕ) {F : Type} [NormedAddCommGroup F] (f : EuclideanSpace ℝ (Fin n) → F) (R : Set (EuclideanSpace ℝ (Fin n))), Continuous f → MeasurableSet R → (∀ w ∈ R, ∃ c : ℝ, 0 < c ∧ ∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ ≤ c → c * ‖u‖ ≤ ‖f (w + u) - f w‖) → ∃ T : ℕ → Set (EuclideanSpace ℝ (Fin n)), R ⊆ ⋃ p, T p ∧ ∀ p, MeasurableSet (T p) ∧ Bornology.IsBounded (T p) ∧ T p ⊆ R ∧ ∃ c : ℝ, 0 < c ∧ ∀ v ∈ T p, ∀ w ∈ T p, c * ‖v - w‖ ≤ ‖f v - f w‖ := by
  intro n F _ f R hf hR hloc
  -- Scales `r_k = 1/(k+1)` and the closed sets `G_k` of points with the lower bound at scale `r_k`.
  obtain ⟨r, hr, hrc⟩ : ∃ r : ℕ → ℝ, (∀ k, 0 < r k) ∧ ∀ c : ℝ, 0 < c → ∃ k, r k < c :=
    ⟨fun k ↦ 1 / ((k : ℝ) + 1), fun _ ↦ Nat.one_div_pos_of_nat, fun _ hc ↦ exists_nat_one_div_lt hc⟩
  obtain ⟨G, hG, hGmem⟩ : ∃ G : ℕ → Set (EuclideanSpace ℝ (Fin n)), (∀ k, IsClosed (G k)) ∧
      ∀ k w, w ∈ G k ↔ ∀ u, ‖u‖ ≤ r k → r k * ‖u‖ ≤ ‖f (w + u) - f w‖ :=
    ⟨fun k ↦ ⋂ u ∈ closedBall 0 (r k), {w | r k * ‖u‖ ≤ ‖f (w + u) - f w‖},
      fun k ↦ isClosed_biInter fun u _ ↦ isClosed_le continuous_const
        ((hf.comp (continuous_id.add continuous_const)).sub hf).norm,
      fun k w ↦ by simp only [mem_iInter₂, mem_closedBall_zero_iff, mem_ofPred_eq]⟩
  -- Every point of `R` lies in some `G_k`.
  have hRG : ∀ w ∈ R, ∃ k, w ∈ G k := fun w hw ↦ by
    obtain ⟨c, hc, hcw⟩ := hloc w hw
    obtain ⟨k, hk⟩ := hrc c hc
    exact ⟨k, (hGmem k w).2 fun u hu ↦
      (mul_le_mul_of_nonneg_right hk.le (norm_nonneg u)).trans (hcw u (hu.trans hk.le))⟩
  -- A dense sequence `q`: balls of radius `r_k / 2` around the `q_m` cover `ℝⁿ` for each `k`.
  obtain ⟨q, hq⟩ := TopologicalSpace.exists_dense_seq (EuclideanSpace ℝ (Fin n))
  refine ⟨fun p ↦ R ∩ G p.unpair.1 ∩ closedBall (q p.unpair.2) (r p.unpair.1 / 2), ?_,
    fun p ↦ ⟨?_, ?_, ?_, ?_⟩⟩
  · intro w hw
    obtain ⟨k, hk⟩ := hRG w hw
    obtain ⟨m, hm⟩ := hq.exists_dist_lt w (half_pos (hr k))
    refine mem_iUnion.2 ⟨Nat.pair k m, ?_⟩
    rw [Nat.unpair_pair]
    exact ⟨⟨hw, hk⟩, mem_closedBall.2 hm.le⟩
  · exact (hR.inter (hG _).measurableSet).inter measurableSet_closedBall
  · exact isBounded_closedBall.subset inter_subset_right
  · exact inter_subset_left.trans inter_subset_left
  · -- Two points of `T_p` are within `r_k` of each other, so the bound of `G_k` applies to `v - w`.
    refine ⟨r p.unpair.1, hr _, fun v hv w hw ↦ ?_⟩
    have hvw : ‖v - w‖ ≤ r p.unpair.1 := by
      rw [← dist_eq_norm]
      calc dist v w ≤ dist v (q p.unpair.2) + dist w (q p.unpair.2) := dist_triangle_right _ _ _
        _ ≤ r p.unpair.1 / 2 + r p.unpair.1 / 2 :=
          add_le_add (mem_closedBall.1 hv.2) (mem_closedBall.1 hw.2)
        _ = r p.unpair.1 := add_halves _
    simpa only [add_sub_cancel] using (hGmem _ w).1 hw.1.2 (v - w) hvw
/-- **Regular points of a continuous map.** If `f : ℝⁿ → ℝ^{n+ℓ}` is continuous, the set `R` of
points where `f` is differentiable with injective derivative is covered by countably many bounded
Borel sets `T_p ⊆ R`, on each of which `f` has a lower Lipschitz bound. `R` is SimonGMT's
`Chapter02.areaRegularSet f`, hence Borel. Each `w ∈ R` has a local lower bound
`c|u| ≤ |f(w + u) - f(w)|` for `|u| ≤ c` (`injective_fderiv_local_lower_bound`), and
`lower_lipschitz_cover_of_local_bound` makes these bounds uniform on countably many pieces. -/
theorem Submission.regular_set_lower_lipschitz_cover : ∀ (n ℓ : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → Ambient n ℓ), Continuous f →
    ∃ T : ℕ → Set (EuclideanSpace ℝ (Fin n)),
      {w | DifferentiableAt ℝ f w ∧ Function.Injective (fderiv ℝ f w)} ⊆ ⋃ p, T p ∧
      ∀ p, MeasurableSet (T p) ∧ Bornology.IsBounded (T p) ∧
        (∀ w ∈ T p, DifferentiableAt ℝ f w ∧ Function.Injective (fderiv ℝ f w)) ∧
        ∃ c : ℝ, 0 < c ∧ ∀ v ∈ T p, ∀ w ∈ T p, c * ‖v - w‖ ≤ ‖f v - f w‖ := by
  intro n ℓ f hf
  -- Every regular point has a pointwise lower bound; the cover makes the bounds uniform.
  obtain ⟨T, hRT, hT⟩ := Submission.lower_lipschitz_cover_of_local_bound n f
    {w | DifferentiableAt ℝ f w ∧ Function.Injective (fderiv ℝ f w)} hf
    (Poincare.SimonGMT.Chapter02.measurableSet_areaRegularSet f)
    (fun w hw ↦ Submission.injective_fderiv_local_lower_bound n f w hw.1 hw.2)
  refine ⟨T, hRT, fun p ↦ ?_⟩
  obtain ⟨hmeas, hbdd, hsub, hlower⟩ := hT p
  exact ⟨hmeas, hbdd, fun w hw ↦ hsub hw, hlower⟩
/-- **Lusin exhaustion (Simon Ch. 1, 1.17).** If `Y` is a finite-dimensional real normed space,
`g : ℝⁿ → Y` is Borel and `S ⊆ ℝⁿ` is Borel with `Lⁿ(S) < ∞`, then `S` is covered up to an
`Lⁿ`-null set by countably many compact sets `C_j ⊆ S` on each of which `g` is continuous. -/
theorem Submission.lusin_compact_exhaustion_of_measurable : ∀ {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] [MeasurableSpace Y] [BorelSpace Y] (n : ℕ) (g : EuclideanSpace ℝ (Fin n) → Y) (S : Set (EuclideanSpace ℝ (Fin n))), Measurable g → MeasurableSet S → volume S ≠ ⊤ → ∃ C : ℕ → Set (EuclideanSpace ℝ (Fin n)), (∀ j, IsCompact (C j) ∧ C j ⊆ S ∧ ContinuousOn g (C j)) ∧ volume (S \ ⋃ j, C j) = 0 := by
  intro Y _ _ _ _ _ n g S hg hS hSfin
  -- `Lⁿ ⌞ S` is finite, hence outer regular; `Y` has a countable topological basis.
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.2 hSfin
  have hb := TopologicalSpace.isBasis_countableBasis Y
  have : Countable (TopologicalSpace.countableBasis Y) :=
    (TopologicalSpace.countable_countableBasis Y).to_subtype
  -- One compact set: `K ⊆ S` with `g` continuous on `K` and `Lⁿ(S \ K) < ε`.
  have key : ∀ ε : ℝ≥0∞, ε ≠ 0 →
      ∃ K, IsCompact K ∧ K ⊆ S ∧ ContinuousOn g K ∧ volume (S \ K) < ε := by
    intro ε hε
    obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_pos_sum_of_countable (ENNReal.half_pos hε).ne'
      (TopologicalSpace.countableBasis Y)
    -- Open `O_U ⊇ g⁻¹(U)` with `(Lⁿ ⌞ S)(O_U \ g⁻¹(U)) < δ_U` for each basic open `U`.
    choose O hgO hO _ hOδ using fun U : TopologicalSpace.countableBasis Y ↦
      (hg (hb.isOpen U.2).measurableSet).exists_isOpen_sdiff_lt (μ := volume.restrict S)
        (measure_ne_top _ _) (ENNReal.coe_ne_zero.2 (hδ U).ne')
    -- The bad set `B = ⋃_U (O_U \ g⁻¹(U))` has `Lⁿ(S ∩ B) < ε/2`.
    set B := ⋃ U, (O U \ g ⁻¹' U)
    have hBm : MeasurableSet B :=
      MeasurableSet.iUnion fun U ↦ (hO U).measurableSet.diff (hg (hb.isOpen U.2).measurableSet)
    have hSB : volume (S ∩ B) < ε / 2 :=
      calc volume (S ∩ B) = volume.restrict S B := by rw [Measure.restrict_apply hBm, inter_comm]
        _ ≤ ∑' U, volume.restrict S (O U \ g ⁻¹' U) := measure_iUnion_le _
        _ ≤ ∑' U, (δ U : ℝ≥0∞) := ENNReal.tsum_le_tsum fun U ↦ (hOδ U).le
        _ < ε / 2 := hδε
    -- Inner regularity: compact `K ⊆ S \ B` with `Lⁿ((S \ B) \ K) < ε/2`.
    obtain ⟨K, hKSB, hK, hKε⟩ := (hS.diff hBm).exists_isCompact_sdiff_lt
      (ne_top_of_le_ne_top hSfin (measure_mono sdiff_subset)) (ENNReal.half_pos hε).ne'
    refine ⟨K, hK, hKSB.trans sdiff_subset, fun x _ ↦ ?_, ?_⟩
    · -- On `K`, `g⁻¹(U) ∩ K = O_U ∩ K` is relatively open, so `g` is continuous on `K`.
      refine hb.nhds_hasBasis.tendsto_right_iff.2 fun U ⟨hUb, hxU⟩ ↦
        mem_nhdsWithin.2 ⟨O ⟨U, hUb⟩, hO _, hgO _ hxU, fun y ⟨hyO, hyK⟩ ↦ ?_⟩
      by_contra hyU
      exact (hKSB hyK).2 (mem_iUnion.2 ⟨⟨U, hUb⟩, hyO, hyU⟩)
    · calc volume (S \ K) ≤ volume (S ∩ B) + volume ((S \ B) \ K) :=
            (measure_mono (show S \ K ⊆ (S ∩ B) ∪ ((S \ B) \ K) from fun y ⟨hyS, hyK⟩ ↦ by
              by_cases hyB : y ∈ B
              · exact Or.inl ⟨hyS, hyB⟩
              · exact Or.inr ⟨⟨hyS, hyB⟩, hyK⟩)).trans (measure_union_le _ _)
        _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hSB hKε
        _ = ε := ENNReal.add_halves ε
  -- Exhaustion: `C_j` with `Lⁿ(S \ C_j) < 1/j`, so `Lⁿ(S \ ⋃ C_j) = 0`.
  choose C hC hCS hCg hCε using fun j : ℕ ↦
    key (j : ℝ≥0∞)⁻¹ (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top j))
  refine ⟨C, fun j ↦ ⟨hC j, hCS j, hCg j⟩, ?_⟩
  by_contra h
  obtain ⟨j, hj⟩ := ENNReal.exists_inv_nat_lt h
  exact lt_asymm hj
    ((measure_mono (sdiff_subset_sdiff_right (subset_iUnion C j))).trans_lt (hCε j))
/-- **Compact pieces of one Lipschitz image.** If `f : ℝⁿ → ℝ^{n+ℓ}` is Lipschitz, then up to an
`Hⁿ`-null set `Y`, `f(ℝⁿ)` is covered by images `f(C_i)` of compact sets on which `f` is
differentiable with injective derivative, `Df` is continuous, and `f` has a lower Lipschitz
bound. The bounded Borel pieces `T_p` of the regular set (`regular_set_lower_lipschitz_cover`)
are exhausted by Lusin compacta `D_{p,q}` for `Df` (`lusin_compact_exhaustion_of_measurable`);
`Y` is the image of the non-regular set (null by the area formula, Ch. 2 §3) together with the
image of the null remainders `T_p \ ⋃_q D_{p,q}` (null by Ch. 2, 1.8(i)). -/
theorem Submission.lipschitz_range_piece_cover : ∀ (n ℓ : ℕ) (K : NNReal)
    (f : EuclideanSpace ℝ (Fin n) → Ambient n ℓ), LipschitzWith K f →
    ∃ (Y : Set (Ambient n ℓ)) (C : ℕ → Set (EuclideanSpace ℝ (Fin n))),
      (μHE[n] : Measure (Ambient n ℓ)) Y = 0 ∧ Set.range f ⊆ Y ∪ ⋃ i, f '' C i ∧
      ∀ i, IsCompact (C i) ∧
        (∀ w ∈ C i, DifferentiableAt ℝ f w ∧ Function.Injective (fderiv ℝ f w)) ∧
        ContinuousOn (fderiv ℝ f) (C i) ∧
        ∃ c : ℝ, 0 < c ∧ ∀ v ∈ C i, ∀ w ∈ C i, c * ‖v - w‖ ≤ ‖f v - f w‖ := by
  intro n ℓ K f hf
  -- Bounded Borel pieces `T_p` of the regular set `R`, with lower Lipschitz bounds.
  obtain ⟨T, hRT, hT⟩ := Submission.regular_set_lower_lipschitz_cover n ℓ f hf.continuous
  -- `T_p` has finite measure and `Df` is Borel, so Lusin gives compacta `D_{p,q} ⊆ T_p` on
  -- which `Df` is continuous, exhausting `T_p` up to a Lebesgue-null set.
  choose D hD hDnull using fun p ↦
    Submission.lusin_compact_exhaustion_of_measurable n (fderiv ℝ f) (T p)
      (measurable_fderiv ℝ f) (hT p).1 (hT p).2.1.measure_lt_top.ne
  -- `Y = f(ℝⁿ \ R) ∪ f(Z)` with `Z = ⋃_p (T_p \ ⋃_q D_{p,q})`; the pieces are `D_{Nat.unpair i}`.
  refine ⟨f '' (univ \ {w | DifferentiableAt ℝ f w ∧ Function.Injective (fderiv ℝ f w)}) ∪
      f '' ⋃ p, (T p \ ⋃ q, D p q), fun i ↦ D (Nat.unpair i).1 (Nat.unpair i).2, ?_, ?_,
      fun i ↦ ?_⟩
  · refine measure_union_null ?_ ?_
    · -- The area formula: the image of the non-regular set is `Hⁿ`-null.
      have h := Poincare.SimonGMT.Chapter02.area_image_compl_regularSet_eq_zero hf univ
      rwa [finrank_euclideanSpace_fin] at h
    · -- Ch. 2, 1.8(i): `Hⁿ(f(Z)) ≤ Kⁿ Hⁿ(Z) = Kⁿ Lⁿ(Z) = 0`.
      have h := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
        (hf.lipschitzOnWith (s := ⋃ p, (T p \ ⋃ q, D p q)))
      rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume n, measure_iUnion_null hDnull,
        mul_zero] at h
      exact nonpos_iff_eq_zero.1 h
  · rintro _ ⟨w, rfl⟩
    by_cases hw : w ∈ {w | DifferentiableAt ℝ f w ∧ Function.Injective (fderiv ℝ f w)}
    · obtain ⟨p, hp⟩ := mem_iUnion.1 (hRT hw)
      by_cases hq : w ∈ ⋃ q, D p q
      · obtain ⟨q, hq⟩ := mem_iUnion.1 hq
        refine mem_union_right _ (mem_iUnion.2 ⟨Nat.pair p q, ?_⟩)
        simpa only [Nat.unpair_pair] using mem_image_of_mem f hq
      · exact mem_union_left _ (mem_union_right _
          (mem_image_of_mem f (mem_iUnion.2 ⟨p, mem_sdiff_of_mem hp hq⟩)))
    · exact mem_union_left _ (mem_union_left _
        (mem_image_of_mem f (mem_sdiff_of_mem (mem_univ w) hw)))
  · -- Each piece inherits the properties of `D_{p,q} ⊆ T_p`.
    obtain ⟨hcpt, hsub, hcont⟩ := hD (Nat.unpair i).1 (Nat.unpair i).2
    obtain ⟨-, -, hreg, c, hc, hlow⟩ := hT (Nat.unpair i).1
    exact ⟨hcpt, fun w hw ↦ hreg w (hsub hw), hcont, c, hc,
      fun v hv w hw ↦ hlow v (hsub hv) w (hsub hw)⟩

theorem main_theorem : ApproxTangentAE ∧ FirstVariationFormula ∧ StationaryIffVariational ∧ StationaryMonotonicity ∧ StationaryDensity ∧ CanonicalRepresentative ∧ BoundedCurvatureMonotonicity ∧ LogarithmicMonotonicityError ∧ LpMonotonicity ∧ LpDensity ∧ LpSupportRepresentation ∧ PoincareInequality ∧ SobolevInequality ∧ SupportInBall ∧ ConvexHullProperty ∧ ClassicalTangent := by sorry

/-- **Lipschitz pieces of a countably `n`-rectifiable set** (Ch. 3, 1.1, with Rademacher, the
area formula and Lusin in place of the `C¹` cover of Ch. 3, 1.2). Up to a Borel `Hⁿ`-null set
`N₀`, `M` is covered by countably many images `F_i(C_i)` of compact sets under Lipschitz maps
that are differentiable on `C_i` with injective, continuous derivative and satisfy a lower
Lipschitz bound there. Each parametrization of 1.1 is split by `lipschitz_range_piece_cover`;
the pieces are re-indexed by `Nat.pair`. -/
theorem Submission.rectifiable_lipschitz_piece_cover : ∀ (n ℓ : ℕ) (M : Set (Ambient n ℓ)),
    0 < n → Poincare.SimonGMT.Chapter03.CountablyRectifiable n M →
    ∃ (N₀ : Set (Ambient n ℓ)) (C : ℕ → Set (EuclideanSpace ℝ (Fin n)))
      (F : ℕ → EuclideanSpace ℝ (Fin n) → Ambient n ℓ),
      MeasurableSet N₀ ∧ (μHE[n] : Measure (Ambient n ℓ)) N₀ = 0 ∧ M ⊆ N₀ ∪ ⋃ i, F i '' C i ∧
      ∀ i, IsCompact (C i) ∧ (∃ K : NNReal, LipschitzWith K (F i)) ∧
        (∀ w ∈ C i, DifferentiableAt ℝ (F i) w ∧ Function.Injective (fderiv ℝ (F i) w)) ∧
        ContinuousOn (fderiv ℝ (F i)) (C i) ∧
        ∃ c : ℝ, 0 < c ∧ ∀ v ∈ C i, ∀ w ∈ C i, c * ‖v - w‖ ≤ ‖F i v - F i w‖ := by
  intro n ℓ M _hn hM
  -- 1.1: `M ⊆ M₀ ∪ ⋃_j G_j(ℝⁿ)` with `Hⁿ(M₀) = 0` and `G_j` Lipschitz with constant `K_j`.
  obtain ⟨M₀, hM₀, G, hG, hMcover⟩ := hM
  choose K hK using hG
  -- Every `G_j(ℝⁿ)` lies in `Y_j ∪ ⋃_q G_j(D_{j,q})` with `Hⁿ(Y_j) = 0`.
  choose Y D hY hrange hD using fun j ↦
    Submission.lipschitz_range_piece_cover n ℓ (K j) (G j) (hK j)
  -- A Borel `Hⁿ`-null hull `N₀` of `M₀ ∪ ⋃_j Y_j`.
  obtain ⟨N₀, hN₀sub, hN₀meas, hN₀null⟩ :=
    exists_measurable_superset_of_null (measure_union_null hM₀ (measure_iUnion_null hY))
  refine ⟨N₀, fun i ↦ D (Nat.unpair i).1 (Nat.unpair i).2, fun i ↦ G (Nat.unpair i).1,
    hN₀meas, hN₀null, ?_, fun i ↦ ?_⟩
  · intro x hx
    rcases hMcover hx with hx₀ | hx
    · exact mem_union_left _ (hN₀sub (mem_union_left _ hx₀))
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    rcases hrange j hj with hxY | hxD
    · exact mem_union_left _ (hN₀sub (mem_union_right _ (mem_iUnion.2 ⟨j, hxY⟩)))
    obtain ⟨q, hq⟩ := mem_iUnion.mp hxD
    refine mem_union_right _ (mem_iUnion.2 ⟨Nat.pair j q, ?_⟩)
    simpa only [Nat.unpair_pair] using hq
  · obtain ⟨hcpt, hdiff, hcont, hlower⟩ := hD (Nat.unpair i).1 (Nat.unpair i).2
    exact ⟨hcpt, ⟨K _, hK _⟩, hdiff, hcont, hlower⟩

/-- **Ch. 4, 1.3 and 2.2, with Ch. 3, 1.6–1.9.** `ApproxTangentAE`; for every `V`, `μ_V` is finite
on compact sets, `dim T_x V = n` `μ_V`-a.e. and `x ↦ p_{T_x V}` is `μ_V`-measurable; and the first
variation formula `FirstVariationFormula`. Up to an `Hⁿ`-null set, `M` is covered by the Lipschitz
pieces `F_i(C_i)` of `rectifiable_lipschitz_piece_cover`. At `Hⁿ`-a.e. `x = F_i(w) ∈ M` the
weighted blow-up of `μ_V` is `θ(x) Hⁿ ⌞ DF_i(w)(ℝⁿ)` (`ts_piece_weighted_blowup_ae`), so the
approximate tangent plane at `x` is `DF_i(w)(ℝⁿ)` for every piece through `x`. -/
theorem Submission.tangent_structure_first_variation : ApproxTangentAE ∧
    (∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ), 0 < n →
      IsFiniteMeasureOnCompacts V.weight ∧
        (∀ᵐ x ∂V.weight, Module.finrank ℝ (V.tangentSpace x) = n) ∧
        AEStronglyMeasurable (fun x ↦ (V.tangentSpace x).starProjection) V.weight) ∧
    FirstVariationFormula := by
  classical
  -- Step 6(i): `μ_V(K) = ∫_{M ∩ K} θ dHⁿ < ∞` for compact `K`.
  have hfin : ∀ (n ℓ : ℕ) (a : RectifiablePair n ℓ),
      IsFiniteMeasureOnCompacts (mk a).weight := by
    intro n ℓ a
    refine ⟨fun K hK ↦ ?_⟩
    change pairWeight n a.M a.θ K < ⊤
    rw [pairWeight, withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
    exact (a.isRectifiablePair.locallyIntegrable K hK).setLIntegral_lt_top
  -- Steps 1–6 for one pair `a = (M, θ)`: a piece cover such that, `Hⁿ`-a.e. on `M`, `T_x V` is
  -- the tangent plane of every piece through `x`, the conclusions of `ApproxTangentAE` hold and
  -- `dim T_x V = n`; and `x ↦ p_{T_x V}` is `Hⁿ ⌞ M`-measurable.
  have hpair : ∀ (n ℓ : ℕ) (a : RectifiablePair n ℓ), 0 < n →
      ∃ (N₀ : Set (Ambient n ℓ)) (C : ℕ → Set (EuclideanSpace ℝ (Fin n)))
        (F : ℕ → EuclideanSpace ℝ (Fin n) → Ambient n ℓ),
        MeasurableSet N₀ ∧ (μHE[n] : Measure (Ambient n ℓ)) N₀ = 0 ∧
        a.M ⊆ N₀ ∪ ⋃ i, F i '' C i ∧
        (∀ i, IsCompact (C i) ∧ (∃ K : NNReal, LipschitzWith K (F i)) ∧
          (∀ w ∈ C i, DifferentiableAt ℝ (F i) w ∧ Function.Injective (fderiv ℝ (F i) w)) ∧
          ContinuousOn (fderiv ℝ (F i)) (C i) ∧
          ∃ c : ℝ, 0 < c ∧ ∀ v ∈ C i, ∀ w ∈ C i, c * ‖v - w‖ ≤ ‖F i v - F i w‖) ∧
        (∀ᵐ x ∂(μHE[n] : Measure (Ambient n ℓ)).restrict a.M,
          (∀ i, ∀ w ∈ C i, F i w = x →
            (mk a).tangentSpace x = LinearMap.range (fderiv ℝ (F i) w).toLinearMap) ∧
          ((∃! P, (mk a).IsApproxTangentAt x P) ∧
            Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n a.M a.θ x
              ((mk a).tangentSpace x) ∧
            (mk a).HasDensityAt x (a.θ x)) ∧
          Module.finrank ℝ ((mk a).tangentSpace x) = n) ∧
        AEStronglyMeasurable (fun x ↦ ((mk a).tangentSpace x).starProjection)
          ((μHE[n] : Measure (Ambient n ℓ)).restrict a.M) := by
    intro n ℓ a hn
    -- Step 1: the Lipschitz pieces `N_i = F_i(C_i)`.
    obtain ⟨N₀, C, F, hN₀, hN₀null, hcover, hpiece⟩ :=
      Submission.rectifiable_lipschitz_piece_cover n ℓ a.M hn
        a.isRectifiablePair.countablyRectifiable
    -- `T_i(F_i(w)) = DF_i(w)(ℝⁿ)` is `n`-dimensional.
    have hrank : ∀ i, ∀ w ∈ C i,
        Module.finrank ℝ (LinearMap.range (fderiv ℝ (F i) w).toLinearMap) = n := fun i w hw ↦
      (LinearMap.finrank_range_of_inj (f := (fderiv ℝ (F i) w).toLinearMap)
        ((hpiece i).2.2.1 w hw).2).trans finrank_euclideanSpace_fin
    -- Step 4 on every piece: the weighted blow-up `(★)` at `x = F_i(w)`.
    have hblow : ∀ᵐ x ∂(μHE[n] : Measure (Ambient n ℓ)).restrict a.M, ∀ i, ∀ w ∈ C i,
        F i w = x → ∀ f : C_c(Ambient n ℓ, ℝ),
          Tendsto (fun t : ℝ ↦ (t ^ n)⁻¹ * ∫ y, f (t⁻¹ • (y - x)) ∂(mk a).weight) (𝓝[>] 0)
            (𝓝 (a.θ x * ∫ y in (LinearMap.range (fderiv ℝ (F i) w).toLinearMap :
              Set (Ambient n ℓ)), f y ∂μHE[n])) :=
      ae_all_iff.2 fun i ↦ Submission.ts_piece_weighted_blowup_ae n ℓ a (C i) (F i) hn (hpiece i)
    -- `Hⁿ ⌞ M`-a.e. `x` lies in `M \ N₀`, hence on some piece.
    have hon : ∀ᵐ x ∂(μHE[n] : Measure (Ambient n ℓ)).restrict a.M,
        x ∈ a.M ∧ ∃ i, x ∈ F i '' C i := by
      filter_upwards [ae_restrict_mem₀ a.isRectifiablePair.measurable,
        ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hN₀null)] with x hxM hxN₀
      exact ⟨hxM, mem_iUnion.1 ((hcover hxM).resolve_left hxN₀)⟩
    -- Step 5.
    have hae : ∀ᵐ x ∂(μHE[n] : Measure (Ambient n ℓ)).restrict a.M,
        (∀ i, ∀ w ∈ C i, F i w = x →
          (mk a).tangentSpace x = LinearMap.range (fderiv ℝ (F i) w).toLinearMap) ∧
        ((∃! P, (mk a).IsApproxTangentAt x P) ∧
          Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n a.M a.θ x
            ((mk a).tangentSpace x) ∧
          (mk a).HasDensityAt x (a.θ x)) ∧
        Module.finrank ℝ ((mk a).tangentSpace x) = n := by
      filter_upwards [hblow, hon] with x hx hxon
      obtain ⟨hxM, i, w, hw, hFw⟩ := hxon
      -- 5(i): each piece plane through `x` is an approximate tangent plane, with `c = θ(x) > 0`.
      have happrox : ∀ i, ∀ w ∈ C i, F i w = x →
          (mk a).IsApproxTangentAt x (LinearMap.range (fderiv ℝ (F i) w).toLinearMap) :=
        fun i w hw hFw ↦ ⟨hrank i w hw, a.θ x, a.isRectifiablePair.pos x hxM, hx i w hw hFw⟩
      -- 5(ii): the approximate tangent plane is unique, so `T_x V` is the piece plane.
      have hP := happrox i w hw hFw
      have hT : (mk a).tangentSpace x = LinearMap.range (fderiv ℝ (F i) w).toLinearMap := by
        have hex : ∃ P, (mk a).IsApproxTangentAt x P := ⟨_, hP⟩
        rw [RectifiableVarifold.tangentSpace, dite_eq_left hex]
        exact Submission.ts_approx_tangent_plane_unique n ℓ (mk a) x _ _ hex.choose_spec hP
      refine ⟨fun j v hv hFv ↦ hT.trans
          (Submission.ts_approx_tangent_plane_unique n ℓ (mk a) x _ _ hP (happrox j v hv hFv)),
        ⟨⟨_, hP, fun Q hQ ↦ Submission.ts_approx_tangent_plane_unique n ℓ (mk a) x _ _ hQ hP⟩,
          ?_, ?_⟩, ?_⟩
      · -- 5(iii): `T_x V` is the approximate tangent space of Ch. 3, 1.7.
        rw [hT]
        exact Submission.ts_blowup_weighted_tangent n ℓ a x _ hP.1 (hx i w hw hFw)
      · -- 5(iv): `Θⁿ(μ_V, x) = θ(x)`.
        exact Submission.ts_blowup_closedBall_density n ℓ (mk a).weight x _ (a.θ x) hn
          (hfin n ℓ a) hP.1 (a.isRectifiablePair.pos x hxM) (hx i w hw hFw)
      · rw [hT]
        exact hP.1
    -- Step 6(iii): `p_{T_x V} = g(x)`, evaluated at the first piece through `x`.
    obtain ⟨g, hg, hgF⟩ := Submission.ts_piece_tangent_projection_field n ℓ C F hpiece
    refine ⟨N₀, C, F, hN₀, hN₀null, hcover, hpiece, hae, hg.aestronglyMeasurable.congr ?_⟩
    filter_upwards [hae, hon] with x hx hxon
    obtain ⟨i, ⟨w, hw, hFw⟩, hmin⟩ : ∃ i, x ∈ F i '' C i ∧ ∀ j < i, x ∉ F j '' C j :=
      ⟨Nat.find hxon.2, Nat.find_spec hxon.2, fun j hj ↦ Nat.find_min hxon.2 hj⟩
    rw [hx.1 i w hw hFw]
    subst hFw
    exact hgF i w hw hmin
  refine ⟨fun n ℓ a hn ↦ ?_, fun n ℓ V hn ↦ ?_, fun n ℓ a φ ε K hn hφ ↦ ?_⟩
  · -- `ApproxTangentAE`.
    obtain ⟨_, _, _, _, _, _, _, hae, _⟩ := hpair n ℓ a hn
    exact hae.mono fun x hx ↦ hx.2.1
  · -- Step 6, (GF), for `V = v(M, θ)`, using `μ_V ≪ Hⁿ ⌞ M`.
    obtain ⟨a, rfl⟩ : ∃ a : RectifiablePair n ℓ, mk a = V := Quot.exists_rep V
    obtain ⟨_, _, _, _, _, _, _, hae, hproj⟩ := hpair n ℓ a hn
    have hac : (mk a).weight ≪ (μHE[n] : Measure (Ambient n ℓ)).restrict a.M :=
      withDensity_absolutelyContinuous _ _
    exact ⟨hfin n ℓ a, hac.ae_le (hae.mono fun x hx ↦ hx.2.2), hproj.mono_ac hac⟩
  · -- Steps 7–10, `FirstVariationFormula`, on the piece cover.
    obtain ⟨N₀, C, F, hN₀, hN₀null, hcover, hpiece, hae, hproj⟩ := hpair n ℓ a hn
    exact Submission.ts_first_variation_of_pieces n ℓ a N₀ C F φ ε K hn hN₀ hN₀null hcover
      hpiece (hae.mono fun x hx ↦ hx.1) hproj hφ

end

end GMT.Ch04
