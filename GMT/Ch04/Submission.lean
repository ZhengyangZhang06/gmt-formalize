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

/-- **Continuity in the scale** (Simon Ch. 4, 3.3–3.5, p. 90: `I(τ) = ∫ g ψ(r/τ) dμ` is continuous in
`τ`). If `0 < σ`, `0 < c`, `c ρ < R`, `g` is `μ`-integrable on `B_R(ξ)`, `ψ` is continuous and
`ψ(t) = 0` for `t > c`, then for `τ ∈ [σ, ρ]` the integrand vanishes off `B = B_R(ξ)` (there
`|x - ξ| / τ > R / τ > c`), so it equals `1_B g · ψ(|x - ξ| / τ)`. It is bounded by `1_B M |g|`,
where `|ψ| ≤ M` on `[0, R / σ]`, and it is continuous in `τ`. Hence `τ ↦ ∫ g ψ(|x - ξ| / τ) dμ`
is continuous on `[σ, ρ]` (`continuousOn_of_dominated`). -/
theorem Submission.wm_smoothed_scale_integral_continuousOn : ∀ (n ℓ : ℕ) (μ : Measure (Ambient n ℓ)) (g : Ambient n ℓ → ℝ) (ψ : ℝ → ℝ) (ξ : Ambient n ℓ) (c σ ρ R : ℝ), 0 < σ → 0 < c → c * ρ < R → IntegrableOn g (closedBall ξ R) μ → Continuous ψ → (∀ t, c < t → ψ t = 0) → ContinuousOn (fun τ ↦ ∫ x, g x * ψ (‖x - ξ‖ / τ) ∂μ) (Icc σ ρ) := by
  intro n ℓ μ g ψ ξ c σ ρ R hσ hc hcρ hg hψ hψ0
  -- step 1: every `τ ∈ [σ, ρ]` has `τ > 0` and `c τ < R`
  have hτ : ∀ τ ∈ Icc σ ρ, 0 < τ ∧ c * τ < R := fun τ hτ ↦
    ⟨hσ.trans_le hτ.1, (mul_le_mul_of_nonneg_left hτ.2 hc.le).trans_lt hcρ⟩
  -- step 2: off `B = B_R(ξ)`, `|x - ξ| / τ > c`, so `ψ` vanishes and the integrand is `1_B g ψ`
  have hvan : ∀ τ ∈ Icc σ ρ, ∀ x ∉ closedBall ξ R, ψ (‖x - ξ‖ / τ) = 0 := by
    intro τ hτσ x hx
    rw [mem_closedBall, dist_eq_norm, not_le] at hx
    exact hψ0 _ ((lt_div_iff₀ (hτ τ hτσ).1).2 ((hτ τ hτσ).2.trans hx))
  have hF : ∀ τ ∈ Icc σ ρ, ∀ x,
      (closedBall ξ R).indicator g x * ψ (‖x - ξ‖ / τ) = g x * ψ (‖x - ξ‖ / τ) := by
    intro τ hτσ x
    by_cases hx : x ∈ closedBall ξ R
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, hvan τ hτσ x hx, mul_zero, mul_zero]
  -- step 3: `|ψ| ≤ M` on the compact interval `[0, R / σ]`
  obtain ⟨M, hM⟩ :=
    (isCompact_Icc : IsCompact (Icc 0 (R / σ))).exists_bound_of_continuousOn hψ.continuousOn
  -- step 4: `1_B g` and the majorant `1_B (M |g|)` are integrable
  have hgi : Integrable ((closedBall ξ R).indicator g) μ :=
    hg.integrable_indicator measurableSet_closedBall
  have hbi : Integrable ((closedBall ξ R).indicator fun x ↦ M * ‖g x‖) μ :=
    IntegrableOn.integrable_indicator (hg.norm.const_mul M) measurableSet_closedBall
  -- step 8: `continuousOn_of_dominated`, whose hypotheses are steps 5, 6, 4 and 7
  refine continuousOn_of_dominated (fun τ hτσ ↦ ?_) (fun τ hτσ ↦ ?_) hbi ?_
  · -- step 5: `1_B g · ψ(|x - ξ| / τ)` is a.e. strongly measurable
    exact (hgi.aestronglyMeasurable.mul
      (hψ.comp ((continuous_id.sub continuous_const).norm.div_const τ)).aestronglyMeasurable).congr
      (Eventually.of_forall (hF τ hτσ))
  · -- step 6: domination by `1_B (M |g|)`
    filter_upwards with x
    by_cases hx : x ∈ closedBall ξ R
    · have hxR : ‖x - ξ‖ ≤ R := by rwa [mem_closedBall, dist_eq_norm] at hx
      have hτ0 := (hτ τ hτσ).1
      have hs : ‖x - ξ‖ / τ ∈ Icc 0 (R / σ) :=
        ⟨div_nonneg (norm_nonneg _) hτ0.le,
          calc ‖x - ξ‖ / τ ≤ R / τ := div_le_div_of_nonneg_right hxR hτ0.le
            _ ≤ R / σ := div_le_div_of_nonneg_left ((norm_nonneg _).trans hxR) hσ hτσ.1⟩
      rw [indicator_of_mem hx, norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hM _ hs) (norm_nonneg _)
    · simp [indicator_of_notMem hx, hvan τ hτσ x hx]
  · -- step 7: `τ ↦ g x ψ(|x - ξ| / τ)` is continuous on `[σ, ρ]` for every `x`
    filter_upwards with x
    exact continuousOn_const.mul (hψ.comp_continuousOn
      (continuousOn_const.div continuousOn_id fun τ hτσ ↦ (hτ τ hτσ).1.ne'))
/-- **Fubini for the smoothed monotonicity kernel** (Simon Ch. 4, 3.3–3.5, p. 90). Put
`r = |x - ξ|`, `κ(τ, x) = -(r / τ²) χ(r / τ) / τᵏ` and `B = B_R(ξ)`. If `0 < σ`, `0 < c`,
`c ρ < R`, `μ` is finite on compact sets, `w` is a.e. strongly measurable and bounded by `A` on
`B`, `χ` is continuous and `χ(t) = 0` for `t > c`, then `κ(τ, x) = 0` for `τ ∈ (σ, ρ]` and
`x ∉ B`. So both sides are iterated integrals of `f(τ, x) = 1_B w(x) κ(τ, x)`. With `|χ| ≤ M` on
`[0, R / σ]`, `|f| ≤ A (R / σ²) M / σᵏ 1_B` for a.e. `(τ, x)`, which is integrable for
`λ⌞(σ, ρ] ⊗ μ` since `μ(B) < ∞`; Fubini (`integral_integral_swap`) gives the identity. -/
theorem Submission.wm_smoothed_kernel_fubini : ∀ (n ℓ k : ℕ) (μ : Measure (Ambient n ℓ)) (w : Ambient n ℓ → ℝ) (χ : ℝ → ℝ) (ξ : Ambient n ℓ) (c σ ρ R A : ℝ), IsFiniteMeasureOnCompacts μ → 0 < σ → 0 < c → c * ρ < R → AEStronglyMeasurable w (μ.restrict (closedBall ξ R)) → (∀ x ∈ closedBall ξ R, |w x| ≤ A) → Continuous χ → (∀ t, c < t → χ t = 0) → ∫ τ in Ioc σ ρ, (∫ x, w x * (-(‖x - ξ‖ / τ ^ 2) * χ (‖x - ξ‖ / τ)) ∂μ) / τ ^ k = ∫ x, w x * (∫ τ in Ioc σ ρ, -(‖x - ξ‖ / τ ^ 2) * χ (‖x - ξ‖ / τ) / τ ^ k) ∂μ := by
  intro n ℓ k μ w χ ξ c σ ρ R A hμ hσ hc hcρ hw hwA hχ hχ0
  -- step 1: for `τ ∈ (σ, ρ]` and `x ∉ B`, `|x - ξ| / τ > c`, so `χ(|x - ξ| / τ) = 0`
  have hvan : ∀ τ ∈ Ioc σ ρ, ∀ x ∉ closedBall ξ R, χ (‖x - ξ‖ / τ) = 0 := by
    intro τ hτ x hx
    rw [mem_closedBall, dist_eq_norm, not_le] at hx
    exact hχ0 _ ((lt_div_iff₀ (hσ.trans hτ.1)).2
      ((mul_le_mul_of_nonneg_left hτ.2 hc.le).trans_lt (hcρ.trans hx)))
  -- step 2: `|χ| ≤ M` on the compact interval `[0, R / σ]`
  obtain ⟨M, hM⟩ :=
    (isCompact_Icc : IsCompact (Icc 0 (R / σ))).exists_bound_of_continuousOn hχ.continuousOn
  -- steps 3–4: the left side is `∫_{(σ,ρ]} ∫ f(τ, x) dμ dτ`
  have hL : ∫ τ in Ioc σ ρ, (∫ x, w x * (-(‖x - ξ‖ / τ ^ 2) * χ (‖x - ξ‖ / τ)) ∂μ) / τ ^ k =
      ∫ τ in Ioc σ ρ, ∫ x, (closedBall ξ R).indicator w x *
        (-(‖x - ξ‖ / τ ^ 2) * χ (‖x - ξ‖ / τ) / τ ^ k) ∂μ := by
    refine setIntegral_congr_fun measurableSet_Ioc fun τ hτ ↦ ?_
    rw [← integral_div]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    by_cases hx : x ∈ closedBall ξ R
    · simp only [indicator_of_mem hx]
      ring
    · simp only [indicator_of_notMem hx, hvan τ hτ x hx]
      ring
  -- step 5: the right side is `∫ ∫_{(σ,ρ]} f(τ, x) dτ dμ`
  have hR : ∫ x, (∫ τ in Ioc σ ρ, (closedBall ξ R).indicator w x *
        (-(‖x - ξ‖ / τ ^ 2) * χ (‖x - ξ‖ / τ) / τ ^ k)) ∂μ =
      ∫ x, w x * (∫ τ in Ioc σ ρ, -(‖x - ξ‖ / τ ^ 2) * χ (‖x - ξ‖ / τ) / τ ^ k) ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    dsimp only
    rw [integral_const_mul]
    by_cases hx : x ∈ closedBall ξ R
    · rw [indicator_of_mem hx]
    · have h0 : ∫ τ in Ioc σ ρ, -(‖x - ξ‖ / τ ^ 2) * χ (‖x - ξ‖ / τ) / τ ^ k = 0 :=
        setIntegral_eq_zero_of_forall_eq_zero fun τ hτ ↦ by rw [hvan τ hτ x hx, mul_zero, zero_div]
      rw [indicator_of_notMem hx, h0, zero_mul, mul_zero]
  -- steps 6–8: `f` is integrable for `λ⌞(σ, ρ] ⊗ μ`
  have hμB : μ (closedBall ξ R) < ⊤ := (isCompact_closedBall ξ R).measure_lt_top
  have hg : Integrable ((closedBall ξ R).indicator fun _ ↦ A * (R / σ ^ 2 * M / σ ^ k)) μ :=
    (integrableOn_const hμB.ne).integrable_indicator measurableSet_closedBall
  have hint : Integrable (Function.uncurry fun τ x ↦ (closedBall ξ R).indicator w x *
      (-(‖x - ξ‖ / τ ^ 2) * χ (‖x - ξ‖ / τ) / τ ^ k)) ((volume.restrict (Ioc σ ρ)).prod μ) := by
    refine (hg.comp_snd (volume.restrict (Ioc σ ρ))).mono' ?_ ?_
    · -- step 6: `1_B w` is a.e. strongly measurable and the kernel is Borel
      have hr : Measurable fun p : ℝ × Ambient n ℓ ↦ ‖p.2 - ξ‖ := (measurable_snd.sub_const ξ).norm
      exact ((aestronglyMeasurable_indicator_iff measurableSet_closedBall).2 hw).comp_snd.mul
        (((hr.div (measurable_fst.pow_const 2)).neg.mul
          (hχ.measurable.comp (hr.div measurable_fst))).div
            (measurable_fst.pow_const k)).aestronglyMeasurable
    · -- step 7: `|f(τ, x)| ≤ A (R / σ²) M / σᵏ 1_B(x)` for a.e. `(τ, x)`, as `τ ∈ (σ, ρ]`
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)]
      rintro ⟨τ, x⟩ hτ
      have hστ : σ < τ := hτ.1
      have hτ0 : 0 < τ := hσ.trans hστ
      simp only [Function.uncurry_apply_pair]
      by_cases hx : x ∈ closedBall ξ R
      · have hxR : ‖x - ξ‖ ≤ R := by rwa [mem_closedBall, dist_eq_norm] at hx
        have hR0 : 0 ≤ R := (norm_nonneg _).trans hxR
        have hA0 : 0 ≤ A := (abs_nonneg _).trans (hwA x hx)
        have hs : ‖x - ξ‖ / τ ∈ Icc 0 (R / σ) :=
          ⟨by positivity, (div_le_div_of_nonneg_right hxR hτ0.le).trans
            (div_le_div_of_nonneg_left hR0 hσ hστ.le)⟩
        have hχM : |χ (‖x - ξ‖ / τ)| ≤ M := by rw [← Real.norm_eq_abs]; exact hM _ hs
        have hM0 : 0 ≤ M := (abs_nonneg _).trans hχM
        have h1 : ‖x - ξ‖ / τ ^ 2 ≤ R / σ ^ 2 :=
          (div_le_div_of_nonneg_right hxR (by positivity)).trans
            (div_le_div_of_nonneg_left hR0 (by positivity) (pow_le_pow_left₀ hσ.le hστ.le 2))
        have h2 : ‖x - ξ‖ / τ ^ 2 * |χ (‖x - ξ‖ / τ)| / τ ^ k ≤ R / σ ^ 2 * M / σ ^ k :=
          div_le_div₀ (by positivity) (mul_le_mul h1 hχM (abs_nonneg _) (by positivity))
            (by positivity) (pow_le_pow_left₀ hσ.le hστ.le k)
        simp only [indicator_of_mem hx, norm_mul, norm_div, norm_neg, norm_pow, Real.norm_eq_abs,
          abs_norm, abs_of_pos hτ0]
        exact mul_le_mul (hwA x hx) h2 (by positivity) hA0
      · simp only [indicator_of_notMem hx, zero_mul, norm_zero, le_refl]
  -- step 9: Fubini
  exact hL.trans ((integral_integral_swap hint).trans hR)
/-- **Scaled FTC** (Simon Ch. 4, 3.4–3.5, p. 90: `d/dρ (ρ⁻ⁿ I(ρ)) = ρ⁻ⁿ J'(ρ)`, integrated, with
an extra term `L`). If `I' = I₁` and `n I - τ I₁ + τ J₁ + L = 0` on `[σ, ρ]`, `0 < σ ≤ ρ`, then by the
quotient rule `(I / tⁿ)' = J₁ / τⁿ + L / τⁿ⁺¹` on `[σ, ρ]` (for `n = m + 1`, clearing denominators
leaves `τ^{3m+3}` times the identity). For continuous `J₁`, `L` the FTC on `[σ, ρ]` then gives
`I ρ / ρⁿ - I σ / σⁿ = ∫_{(σ,ρ]} J₁ / τⁿ + ∫_{(σ,ρ]} L / τⁿ⁺¹`. -/
theorem Submission.wm_smoothed_scaled_ftc : ∀ (n : ℕ) (I I₁ J₁ L : ℝ → ℝ) (σ ρ : ℝ), 0 < σ → σ ≤ ρ → (∀ τ ∈ Icc σ ρ, HasDerivAt I (I₁ τ) τ) → (∀ τ ∈ Icc σ ρ, (n : ℝ) * I τ - τ * I₁ τ + τ * J₁ τ + L τ = 0) → ContinuousOn J₁ (Icc σ ρ) → ContinuousOn L (Icc σ ρ) → I ρ / ρ ^ n - I σ / σ ^ n = (∫ τ in Ioc σ ρ, J₁ τ / τ ^ n) + ∫ τ in Ioc σ ρ, L τ / τ ^ (n + 1) := by
  intro n I I₁ J₁ L σ ρ hσ hσρ hI hE hJ hL
  have hpos : ∀ τ ∈ Icc σ ρ, 0 < τ := fun τ hτ ↦ hσ.trans_le hτ.1
  -- quotient rule, and the identity turns `(I / tⁿ)'` into `J₁ / τⁿ + L / τⁿ⁺¹`
  have hderiv : ∀ τ ∈ uIcc σ ρ,
      HasDerivAt (fun t ↦ I t / t ^ n) (J₁ τ / τ ^ n + L τ / τ ^ (n + 1)) τ := by
    intro τ hτ
    rw [uIcc_of_le hσρ] at hτ
    have hτ0 : τ ≠ 0 := (hpos τ hτ).ne'
    have hEτ := hE τ hτ
    convert (hI τ hτ).fun_div (hasDerivAt_pow n τ) (pow_ne_zero n hτ0) using 1
    rcases n with _ | m
    · have h₁ : τ ^ 0 ≠ 0 := pow_ne_zero _ hτ0
      have h₂ : τ ^ (0 + 1) ≠ 0 := pow_ne_zero _ hτ0
      rw [div_add_div _ _ h₁ h₂, div_eq_div_iff (mul_ne_zero h₁ h₂) (pow_ne_zero 2 h₁)]
      push_cast at hEτ ⊢
      linear_combination hEτ
    · rw [Nat.add_sub_cancel]
      have h₁ : τ ^ (m + 1) ≠ 0 := pow_ne_zero _ hτ0
      have h₂ : τ ^ (m + 1 + 1) ≠ 0 := pow_ne_zero _ hτ0
      rw [div_add_div _ _ h₁ h₂, div_eq_div_iff (mul_ne_zero h₁ h₂) (pow_ne_zero 2 h₁)]
      push_cast at hEτ ⊢
      linear_combination τ ^ (3 * m + 3) * hEτ
  -- both quotients are continuous on `[σ, ρ]`
  have hc₁ : ContinuousOn (fun τ ↦ J₁ τ / τ ^ n) (Icc σ ρ) :=
    hJ.div₀ (continuousOn_pow n) fun τ hτ ↦ pow_ne_zero n (hpos τ hτ).ne'
  have hc₂ : ContinuousOn (fun τ ↦ L τ / τ ^ (n + 1)) (Icc σ ρ) :=
    hL.div₀ (continuousOn_pow (n + 1)) fun τ hτ ↦ pow_ne_zero (n + 1) (hpos τ hτ).ne'
  -- FTC on `[σ, ρ]`, then split the integral over `(σ, ρ]`
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((hc₁.fun_add hc₂).intervalIntegrable_of_Icc hσρ)
  rw [intervalIntegral.integral_of_le hσρ,
    integral_add (hc₁.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      (hc₂.integrableOn_Icc.mono_set Ioc_subset_Icc_self)] at hftc
  exact hftc.symm

theorem main_theorem : ApproxTangentAE ∧ FirstVariationFormula ∧ StationaryIffVariational ∧ StationaryMonotonicity ∧ StationaryDensity ∧ CanonicalRepresentative ∧ BoundedCurvatureMonotonicity ∧ LogarithmicMonotonicityError ∧ LpMonotonicity ∧ LpDensity ∧ LpSupportRepresentation ∧ PoincareInequality ∧ SobolevInequality ∧ SupportInBall ∧ ConvexHullProperty ∧ ClassicalTangent := by sorry

end

end GMT.Ch04
