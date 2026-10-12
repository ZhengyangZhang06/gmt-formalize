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

/-- **Ch. 4, 6.3(1) (p. 101), uniform lower density.** Under the hypotheses of 6.3 there is
`ρ₀ > 0` with `μ_V(B_s(ζ)) ≥ (ωₙ/2) sⁿ` for all `ζ ∈ spt V ∩ B_{ρ₀}(x)` and `0 < s ≤ ρ₀`. One `Λ`
bounds the `Lᵖ` quantity of 4.2 at every centre `ζ ∈ B_R(x)`; letting `σ ↓ 0` in 4.7–4.8 gives
`F(s) s⁻ⁿ μ_V(B_s(ζ)) + F(s) - 1 ≥ ωₙ Θⁿ(μ_V, ζ) ≥ ωₙ` (4.9, 4.10(1)), and `F(s) → 1`. -/
theorem Submission.classical_tangent_uniform_lower_density : LpMonotonicity → LpDensity →
    LpSupportRepresentation → ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ))
    (H : Ambient n ℓ → Ambient n ℓ) (p : ℝ) (x : Ambient n ℓ), 0 < n → IsOpen U →
    V.HasMeanCurvatureIn U H → V.MultiplicityGE 1 U → (n : ℝ) < p → V.IsLocallyLp U H p →
    x ∈ U → ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ζ ∈ V.support ∩ closedBall x ρ₀, ∀ s : ℝ, 0 < s → s ≤ ρ₀ →
      omega n / 2 * s ^ n ≤ V.weight.real (closedBall ζ s) := by
  intro hMono hDensity hSupport n ℓ V U H p x hn hU hH hθ hp hLp hx
  -- Step 1: `p > 0`, `κ = (p - n)/(4p) > 0`, `e = 1 - n/p > 0` and `ωₙ > 0`.
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp0 : 0 < p := by linarith
  have hκ : 0 < lpKappa n p := by
    unfold lpKappa
    apply div_pos <;> linarith
  have he : 0 < 1 - (n : ℝ) / p := sub_pos.mpr ((div_lt_one hp0).mpr hp)
  have hω : 0 < omega n := by
    unfold omega
    exact ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne
  -- Step 2: `R > 0` with `B_{2R}(x) ⊆ U`.
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU x hx
  obtain ⟨R, rfl⟩ : ∃ R : ℝ, r = 4 * R := ⟨r / 4, by ring⟩
  have hR : 0 < R := by linarith
  have h2R : closedBall x (2 * R) ⊆ U := (closedBall_subset_ball (by linarith)).trans hrU
  -- Step 3: with `I₀ = ∫_{B_{2R}(x)} |H|^p dμ_V` and `Λ = (R^{p-n} I₀)^{1/p} / κ`,
  -- `(R^{p-n} ∫_{B_R(ζ)} |H|^p dμ_V)^{1/p} ≤ κΛ` for every `ζ ∈ B_R(x)`.
  have hint : IntegrableOn (fun y ↦ ‖H y‖ ^ p) (closedBall x (2 * R)) V.weight := by
    have := (hLp _ (isCompact_closedBall x (2 * R)) h2R).integrable_norm_rpow
      (by simpa using hp0) ENNReal.ofReal_ne_top
    rwa [ENNReal.toReal_ofReal hp0.le] at this
  have hI : ∀ s : Set (Ambient n ℓ), 0 ≤ R ^ (p - n) * ∫ y in s, ‖H y‖ ^ p ∂V.weight := fun s ↦
    mul_nonneg (Real.rpow_nonneg hR.le _)
      (integral_nonneg fun y ↦ Real.rpow_nonneg (norm_nonneg _) _)
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ : ℝ, Λ = (R ^ (p - n) *
      ∫ y in closedBall x (2 * R), ‖H y‖ ^ p ∂V.weight) ^ (1 / p) / lpKappa n p := ⟨_, rfl⟩
  have hΛ : 0 ≤ Λ := by
    rw [hΛdef]
    exact div_nonneg (Real.rpow_nonneg (hI _) _) hκ.le
  have hball : ∀ ζ ∈ closedBall x R, closedBall ζ R ⊆ closedBall x (2 * R) := by
    intro ζ hζ y hy
    rw [mem_closedBall] at hζ hy ⊢
    linarith [dist_triangle y ζ x]
  have hbound : ∀ ζ ∈ closedBall x R,
      (R ^ (p - n) * ∫ y in closedBall ζ R, ‖H y‖ ^ p ∂V.weight) ^ (1 / p) ≤
        lpKappa n p * Λ := by
    intro ζ hζ
    rw [hΛdef, mul_div_cancel₀ _ hκ.ne']
    refine Real.rpow_le_rpow (hI _) (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hR.le _))
      (by positivity)
    exact setIntegral_mono_set hint
      (Eventually.of_forall fun y ↦ Real.rpow_nonneg (norm_nonneg _) _)
      (Eventually.of_forall (hball ζ hζ))
  -- Steps 4–6: at `ζ ∈ spt V ∩ B_R(x)` and `0 < s ≤ R`, 4.5 and 4.8 give `F(s)` with
  -- `e^{-Λt/2} ≤ F(s) ≤ e^{Λt/2}` and `F(s) a_ζ(s) ≥ ωₙ - C t`, where `a_ζ(s) = s⁻ⁿ μ_V(B_s(ζ))`,
  -- `t = (s/R)^e` and `C = e^{Λ/2} Λ / 2`.
  have key : ∀ ζ ∈ V.support ∩ closedBall x R, ∀ s : ℝ, 0 < s → s ≤ R →
      ∃ F : ℝ, Real.exp (-(Λ / 2 * (s / R) ^ (1 - (n : ℝ) / p))) ≤ F ∧
        F ≤ Real.exp (Λ / 2 * (s / R) ^ (1 - (n : ℝ) / p)) ∧
        omega n - Real.exp (Λ / 2) / 2 * Λ * (s / R) ^ (1 - (n : ℝ) / p) ≤
          F * (V.weight.real (closedBall ζ s) / s ^ n) := by
    intro ζ hζ s hs hsR
    have hζU : ζ ∈ U := h2R (closedBall_subset_closedBall (by linarith) hζ.2)
    obtain ⟨F, -, hF, -, hFmono⟩ := hMono n ℓ V U H p ζ R Λ hn hU hH hp hLp hR
      ((hball ζ hζ.2).trans h2R) (hbound ζ hζ.2)
    have hdens : V.HasDensityAt ζ (V.density ζ) :=
      (hDensity n ℓ V U H p hn hU hH hp hLp).1 ζ hζU
    have hΘ : 1 ≤ V.density ζ := (hSupport n ℓ V U H p hn hU hH hp hLp hθ).1 ζ ⟨hζ.1, hζU⟩
    -- (a) `a_ζ(t) → ωₙ Θⁿ(μ_V, ζ)` as `t ↓ 0`.
    have ha : Tendsto (fun t ↦ V.weight.real (closedBall ζ t) / t ^ n) (𝓝[>] 0)
        (𝓝 (omega n * V.density ζ)) := by
      refine (hdens.const_mul (omega n)).congr' ?_
      filter_upwards with t
      rw [mul_div_assoc', mul_div_mul_left _ _ hω.ne']
    -- (b) `F(t) → 1` as `t ↓ 0`, since `|F(t) - 1| ≤ C (t/R)^e` on `(0, R]`.
    have htR : Tendsto (fun t : ℝ ↦ (t / R) ^ (1 - (n : ℝ) / p)) (𝓝[>] 0) (𝓝 0) := by
      have hc : ContinuousAt (fun t : ℝ ↦ (t / R) ^ (1 - (n : ℝ) / p)) 0 :=
        (continuousAt_id.div_const R).rpow_const (Or.inr he.le)
      have := hc.tendsto
      simp only [zero_div, Real.zero_rpow he.ne'] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioc 0 R := by
      filter_upwards [Ioo_mem_nhdsGT hR] with t ht
      exact ⟨ht.1, ht.2.le⟩
    have hF1 : Tendsto F (𝓝[>] 0) (𝓝 1) := by
      have hup := (htR.const_mul (Real.exp (Λ / 2) / 2 * Λ)).const_add 1
      have hlo := (htR.const_mul (Real.exp (Λ / 2) / 2 * Λ)).const_sub 1
      simp only [mul_zero, add_zero, sub_zero] at hup hlo
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup ?_ ?_
      · filter_upwards [hev] with t ht
        linarith [(abs_le.mp (hF t ht).2.2).1]
      · filter_upwards [hev] with t ht
        linarith [(abs_le.mp (hF t ht).2.2).2]
    -- (c) `Ψ(t) = F(t) a_ζ(t) + (F(t) - 1) → ωₙ Θⁿ(μ_V, ζ)` as `t ↓ 0`.
    have hΨ : Tendsto (fun t ↦ F t * (V.weight.real (closedBall ζ t) / t ^ n) + (F t - 1))
        (𝓝[>] 0) (𝓝 (omega n * V.density ζ)) := by
      simpa using (hF1.mul ha).add (hF1.sub_const 1)
    -- Step 6: `Ψ` is monotone on `(0, R]`, so `ωₙ ≤ ωₙ Θⁿ(μ_V, ζ) ≤ Ψ(s)`.
    have hle : omega n * V.density ζ ≤
        F s * (V.weight.real (closedBall ζ s) / s ^ n) + (F s - 1) := by
      refine le_of_tendsto hΨ ?_
      filter_upwards [Ioo_mem_nhdsGT hs] with t ht
      exact hFmono ⟨ht.1, ht.2.le.trans hsR⟩ ⟨hs, hsR⟩ ht.2.le
    have hωΘ : omega n ≤ omega n * V.density ζ := le_mul_of_one_le_right hω.le hΘ
    obtain ⟨hF₁, hF₂, hF₃⟩ := hF s ⟨hs, hsR⟩
    refine ⟨F s, hF₁, hF₂, ?_⟩
    linarith [(abs_le.mp hF₃).2]
  -- Step 7: `t₀ ∈ (0, 1]` with `C t₀ ≤ ωₙ/4` and `e^{Λt₀/2} ≤ 3/2`, and `ρ₀ = R t₀^{1/e} ≤ R`,
  -- so that `(s/R)^e ≤ t₀` for `0 < s ≤ ρ₀`.
  have hlog : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  have hC : 0 ≤ Real.exp (Λ / 2) / 2 * Λ := by positivity
  obtain ⟨t₀, ht₀def⟩ : ∃ t₀ : ℝ, t₀ = min (min 1 (omega n / (4 * (Real.exp (Λ / 2) / 2 * Λ + 1))))
      (Real.log (3 / 2) / (Λ / 2 + 1)) := ⟨_, rfl⟩
  have ht₀ : 0 < t₀ := by
    rw [ht₀def]
    exact lt_min (lt_min one_pos (by positivity)) (by positivity)
  have ht₀1 : t₀ ≤ 1 := by
    rw [ht₀def]
    exact (min_le_left _ _).trans (min_le_left _ _)
  have ht₀C : Real.exp (Λ / 2) / 2 * Λ * t₀ ≤ omega n / 4 := by
    have h : t₀ ≤ omega n / (4 * (Real.exp (Λ / 2) / 2 * Λ + 1)) := by
      rw [ht₀def]
      exact (min_le_left _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have ht₀Λ : Real.exp (Λ / 2 * t₀) ≤ 3 / 2 := by
    have h : t₀ ≤ Real.log (3 / 2) / (Λ / 2 + 1) := by
      rw [ht₀def]
      exact min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h
    calc Real.exp (Λ / 2 * t₀) ≤ Real.exp (Real.log (3 / 2)) := Real.exp_le_exp.mpr (by linarith)
      _ = 3 / 2 := Real.exp_log (by norm_num)
  obtain ⟨ρ₀, hρ₀def⟩ : ∃ ρ₀ : ℝ, ρ₀ = R * t₀ ^ (1 / (1 - (n : ℝ) / p)) := ⟨_, rfl⟩
  have hρ₀ : 0 < ρ₀ := by
    rw [hρ₀def]
    exact mul_pos hR (Real.rpow_pos_of_pos ht₀ _)
  have hρ₀R : ρ₀ ≤ R := by
    rw [hρ₀def]
    exact mul_le_of_le_one_right hR.le (Real.rpow_le_one ht₀.le ht₀1 (by positivity))
  have hts : ∀ s, 0 < s → s ≤ ρ₀ → (s / R) ^ (1 - (n : ℝ) / p) ≤ t₀ := by
    intro s hs hsρ
    have h : s / R ≤ t₀ ^ (1 / (1 - (n : ℝ) / p)) := by
      rw [div_le_iff₀ hR, mul_comm _ R, ← hρ₀def]
      exact hsρ
    calc (s / R) ^ (1 - (n : ℝ) / p) ≤ (t₀ ^ (1 / (1 - (n : ℝ) / p))) ^ (1 - (n : ℝ) / p) :=
          Real.rpow_le_rpow (by positivity) h he.le
      _ = t₀ := by rw [← Real.rpow_mul ht₀.le, one_div_mul_cancel he.ne', Real.rpow_one]
  -- Step 8: `F(s) a_ζ(s) ≥ ωₙ - C t₀ ≥ 3ωₙ/4` and `0 < F(s) ≤ e^{Λt₀/2} ≤ 3/2`, so
  -- `a_ζ(s) ≥ ωₙ/2`.
  refine ⟨ρ₀, hρ₀, ?_⟩
  rintro ζ ⟨hζs, hζx⟩ s hs hsρ
  obtain ⟨F, hF₁, hF₂, hF₃⟩ :=
    key ζ ⟨hζs, closedBall_subset_closedBall hρ₀R hζx⟩ s hs (hsρ.trans hρ₀R)
  have htt := hts s hs hsρ
  have hF0 : 0 < F := (Real.exp_pos _).trans_le hF₁
  have hF32 : F ≤ 3 / 2 :=
    hF₂.trans ((Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htt (by positivity))).trans ht₀Λ)
  have hFa : 3 / 4 * omega n ≤ F * (V.weight.real (closedBall ζ s) / s ^ n) := by
    linarith [mul_le_mul_of_nonneg_left htt hC]
  have ha0 : 0 < V.weight.real (closedBall ζ s) / s ^ n :=
    pos_of_mul_pos_right (by linarith) hF0.le
  have ha2 : omega n / 2 ≤ V.weight.real (closedBall ζ s) / s ^ n := by nlinarith
  have hsn : 0 < s ^ n := pow_pos hs n
  calc omega n / 2 * s ^ n ≤ V.weight.real (closedBall ζ s) / s ^ n * s ^ n :=
        mul_le_mul_of_nonneg_right ha2 hsn.le
    _ = V.weight.real (closedBall ζ s) := div_mul_cancel₀ _ hsn.ne'
/-- **Blow-up step of Ch. 4, 6.3 (p. 101).** If `μ_V` is finite on compact sets and `P` is an
approximate tangent space of `V` at `x`, then for every `ε > 0` the `μ_V`-mass of `B_ρ(x)` at
distance `≥ ερ` from `x + P` is `o(ρⁿ)` as `ρ ↓ 0`: test the blow-up limit against a cutoff
`f ∈ C_c` with `f = 0` on `P` and `f = 1` on `{z : |z| ≤ 1, dist(z, P) ≥ ε}`. -/
theorem Submission.classical_tangent_off_plane_mass_decay : ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (x : Ambient n ℓ) (P : Submodule ℝ (Ambient n ℓ)) (ε : ℝ), IsFiniteMeasureOnCompacts V.weight → V.IsApproxTangentAt x P → 0 < ε → Tendsto (fun ρ : ℝ ↦ (ρ ^ n)⁻¹ * V.weight.real (closedBall x ρ \ {y | infDist (y - x) (P : Set (Ambient n ℓ)) < ε * ρ})) (𝓝[>] 0) (𝓝 0) := by
  intro n ℓ V x P ε hfin hP hε
  obtain ⟨-, c, -, hc⟩ := hP
  -- The cutoff `f = g₁ g₂`, `g₁ = min 1 (max 0 (2 - |z|))`, `g₂ = min 1 (max 0 (2 dist(z, P)/ε - 1))`.
  obtain ⟨f, hf0, hfn, hfP, hf1⟩ : ∃ f : C_c(Ambient n ℓ, ℝ), (∀ z, 2 < ‖z‖ → f z = 0) ∧
      (∀ z, 0 ≤ f z) ∧ (∀ z ∈ (P : Set (Ambient n ℓ)), f z = 0) ∧
      ∀ z, ‖z‖ ≤ 1 → ε ≤ infDist z (P : Set (Ambient n ℓ)) → f z = 1 := by
    let f₀ : Ambient n ℓ → ℝ := fun z ↦ min 1 (max 0 (2 - ‖z‖)) *
      min 1 (max 0 (2 * infDist z (P : Set (Ambient n ℓ)) / ε - 1))
    have hf₀0 : ∀ z, 2 < ‖z‖ → f₀ z = 0 := fun z hz ↦ by
      simp only [f₀, max_eq_left (by linarith : 2 - ‖z‖ ≤ 0), min_eq_right zero_le_one, zero_mul]
    refine ⟨⟨⟨f₀, ?_⟩, ?_⟩, hf₀0, fun z ↦ ?_, fun z hz ↦ ?_, fun z hz1 hzP ↦ ?_⟩
    · exact (continuous_const.min (continuous_const.max (continuous_const.sub continuous_norm))).mul
        (continuous_const.min (continuous_const.max
          (((continuous_const.mul (continuous_infDist_pt _)).div_const ε).sub continuous_const)))
    · refine HasCompactSupport.intro (isCompact_closedBall 0 2) fun z hz ↦ hf₀0 z ?_
      rwa [mem_closedBall, dist_zero_right, not_le] at hz
    · exact mul_nonneg (le_min zero_le_one (le_max_left _ _)) (le_min zero_le_one (le_max_left _ _))
    · show f₀ z = 0
      simp only [f₀, infDist_zero_of_mem hz, mul_zero, zero_div, zero_sub,
        max_eq_left (by norm_num : (-1 : ℝ) ≤ 0), min_eq_right zero_le_one]
    · show f₀ z = 1
      have h2 : 1 ≤ 2 * infDist z (P : Set (Ambient n ℓ)) / ε - 1 := by
        rw [le_sub_iff_add_le, le_div_iff₀ hε]
        linarith
      simp only [f₀]
      rw [min_eq_left (le_max_of_le_right (by linarith)), min_eq_left (le_max_of_le_right h2),
        one_mul]
  -- `f = 0` on `P`, so the blow-up limit `c ∫_P f dHⁿ` is `0`.
  have hlim := hc f
  rw [setIntegral_eq_zero_of_forall_eq_zero hfP, mul_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
    exact mul_nonneg (inv_nonneg.2 (pow_nonneg hρ.le n)) measureReal_nonneg
  · filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (pow_nonneg hρ.le n))
    have hmeas : MeasurableSet
        (closedBall x ρ \ {y | infDist (y - x) (P : Set (Ambient n ℓ)) < ε * ρ}) :=
      measurableSet_closedBall.diff (isOpen_lt
        ((continuous_infDist_pt _).comp (continuous_id.sub continuous_const))
        continuous_const).measurableSet
    -- `y ↦ f(ρ⁻¹(y - x))` is continuous and vanishes off `B_{2ρ}(x)`, so it is integrable.
    have hsupp : HasCompactSupport fun y ↦ f (ρ⁻¹ • (y - x)) := by
      refine HasCompactSupport.intro (isCompact_closedBall x (2 * ρ)) fun y hy ↦ hf0 _ ?_
      rw [mem_closedBall, dist_eq_norm, not_le] at hy
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hρ, lt_inv_mul_iff₀ hρ]
      linarith
    have hint : Integrable (fun y ↦ f (ρ⁻¹ • (y - x))) V.weight :=
      (f.continuous.comp (by fun_prop)).integrable_of_hasCompactSupport hsupp
    -- `1_{A_ρ} ≤ f(ρ⁻¹(· - x))`, where `A_ρ = B_ρ(x) \ {dist(· - x, P) < ερ}`.
    rw [← integral_indicator_one hmeas]
    refine integral_mono_of_nonneg (Eventually.of_forall fun y ↦ ?_) hint
      (Eventually.of_forall fun y ↦ ?_)
    · exact indicator_nonneg (fun _ _ ↦ zero_le_one) y
    · by_cases hy : y ∈ closedBall x ρ \ {y | infDist (y - x) (P : Set (Ambient n ℓ)) < ε * ρ}
      · rw [indicator_of_mem hy, Pi.one_apply]
        obtain ⟨hyB, hyP⟩ := hy
        rw [mem_closedBall, dist_eq_norm] at hyB
        replace hyP : ε * ρ ≤ infDist (y - x) (P : Set (Ambient n ℓ)) := not_lt.1 hyP
        refine (hf1 _ ?_ ?_).ge
        · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hρ, inv_mul_le_iff₀ hρ]
          linarith
        -- `dist(ρ⁻¹(y - x), P) ≥ ε`, since `ρw ∈ P` for `w ∈ P`.
        · refine (le_infDist ⟨0, P.zero_mem⟩).2 fun w hw ↦ ?_
          have h1 := infDist_le_dist_of_mem (x := y - x) (P.smul_mem ρ hw)
          have h2 : y - x - ρ • w = ρ • (ρ⁻¹ • (y - x) - w) := by
            rw [smul_sub, smul_inv_smul₀ hρ.ne']
          rw [dist_eq_norm, h2, norm_smul, Real.norm_eq_abs, abs_of_pos hρ] at h1
          rw [dist_eq_norm]
          exact le_of_mul_le_mul_left (by linarith) hρ
      · rw [indicator_of_notMem hy]
        exact hfn _

theorem main_theorem : ApproxTangentAE ∧ FirstVariationFormula ∧ StationaryIffVariational ∧ StationaryMonotonicity ∧ StationaryDensity ∧ CanonicalRepresentative ∧ BoundedCurvatureMonotonicity ∧ LogarithmicMonotonicityError ∧ LpMonotonicity ∧ LpDensity ∧ LpSupportRepresentation ∧ PoincareInequality ∧ SobolevInequality ∧ SupportInBall ∧ ConvexHullProperty ∧ ClassicalTangent := by sorry

end

end GMT.Ch04
