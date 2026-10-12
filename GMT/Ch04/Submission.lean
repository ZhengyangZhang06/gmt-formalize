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

/-- **Cutoff, radial profile and radial test field outside a ball** (Simon Ch. 4, 6.1, proof
steps 2–4). A bump function `ζ` centred at `ξ` is `1` near the compact set `K`; the profile
`γ(t) = g(t² - (R + ε)²)`, `g = expNegInvGlue`, vanishes on `[0, R + ε]`, is positive beyond and
nondecreasing on `[0, ∞)`; and `X(x) = (ζ(x)γ(|x - ξ|))(x - ξ)` is a `C¹` field with compact
support in `ℝ^{n+ℓ} \ B_R(ξ)` (`γ(|x - ξ|) = g(|x - ξ|² - (R + ε)²)` is smooth even at `ξ`). -/
theorem Submission.exists_radial_cutoff_test_field : ∀ (n ℓ : ℕ) (K : Set (Ambient n ℓ)) (ξ : Ambient n ℓ) (R ε : ℝ), IsCompact K → 0 ≤ R → 0 < ε → ∃ (ζ : Ambient n ℓ → ℝ) (γ : ℝ → ℝ), ContDiff ℝ 1 ζ ∧ (∀ x ∈ K, ζ x = 1 ∧ gradient ζ x = 0) ∧ ContDiff ℝ 1 γ ∧ (∀ t : ℝ, 0 ≤ t → 0 ≤ γ t ∧ 0 ≤ deriv γ t) ∧ (∀ t : ℝ, 0 ≤ t → t ≤ R + ε → γ t = 0) ∧ (∀ t : ℝ, R + ε < t → 0 < γ t) ∧ IsTestField (closedBall ξ R)ᶜ (fun x ↦ (ζ x * γ ‖x - ξ‖) • (x - ξ)) := by
  intro n ℓ K ξ R ε hK hR hε
  -- step 1: `K ⊆ W = B(ξ, ρ₀)` with `ρ₀ = |ρ| + 1 > 0`
  obtain ⟨ρ, hρ⟩ := hK.isBounded.subset_ball ξ
  have hρ₀ : 0 < |ρ| + 1 := by positivity
  have hKW : K ⊆ ball ξ (|ρ| + 1) := hρ.trans (ball_subset_ball (by linarith [le_abs_self ρ]))
  -- step 2: `ζ` is the bump function at `ξ` with `rIn = ρ₀`, `rOut = ρ₀ + 1`
  let f : ContDiffBump ξ := ⟨|ρ| + 1, |ρ| + 2, hρ₀, by linarith⟩
  -- steps 4 and 6: `γ(t) = g(t² - (R + ε)²)` vanishes for `0 ≤ t ≤ R + ε`
  have hc : 0 < R + ε := by linarith
  have hzero : ∀ t : ℝ, 0 ≤ t → t ≤ R + ε → expNegInvGlue (t ^ 2 - (R + ε) ^ 2) = 0 :=
    fun t ht htc ↦ expNegInvGlue.zero_of_nonpos (by nlinarith)
  refine ⟨f, fun t ↦ expNegInvGlue (t ^ 2 - (R + ε) ^ 2), f.contDiff, fun x hx ↦ ?_,
    expNegInvGlue.contDiff.comp ((contDiff_id.pow 2).sub contDiff_const), fun t ht ↦ ?_, hzero,
    fun t ht ↦ expNegInvGlue.pos_of_pos (by nlinarith), ?_, ?_, ?_⟩
  · -- step 3: `ζ ≡ 1` on a neighbourhood of `x ∈ K`, so `ζ(x) = 1` and `∇ζ(x) = 0`
    have h1 : (f : Ambient n ℓ → ℝ) =ᶠ[𝓝 x] fun _ ↦ 1 := f.eventuallyEq_one_of_mem_ball (hKW hx)
    exact ⟨h1.eq_of_nhds, h1.gradient_eq.trans (gradient_fun_const x 1)⟩
  · -- step 5: `γ'(t) = g'(t² - (R + ε)²) · 2t` with `g' ≥ 0` since `g` is monotone
    refine ⟨expNegInvGlue.nonneg _, ?_⟩
    have hin : HasDerivAt (fun t : ℝ ↦ t ^ 2 - (R + ε) ^ 2) (2 * t) t := by
      simpa using (hasDerivAt_pow 2 t).sub_const ((R + ε) ^ 2)
    have hg : HasDerivAt expNegInvGlue (deriv expNegInvGlue (t ^ 2 - (R + ε) ^ 2))
        (t ^ 2 - (R + ε) ^ 2) :=
      ((expNegInvGlue.contDiff (n := 1)).differentiable one_ne_zero _).hasDerivAt
    have hd := hg.comp t hin
    rw [Function.comp_def] at hd
    rw [hd.deriv]
    exact mul_nonneg expNegInvGlue.monotone.deriv_nonneg (by linarith)
  · -- step 8: `x ↦ γ(|x - ξ|) = g(|x - ξ|² - (R + ε)²)` is smooth, hence `X` is `C¹`
    have hγ : ContDiff ℝ 1 fun x : Ambient n ℓ ↦ expNegInvGlue (‖x - ξ‖ ^ 2 - (R + ε) ^ 2) :=
      expNegInvGlue.contDiff.comp (((contDiff_id.sub contDiff_const).norm_sq ℝ).sub contDiff_const)
    exact (f.contDiff.mul hγ).smul (contDiff_id.sub contDiff_const)
  · -- step 9: `supp X ⊆ supp ζ`, which is compact
    exact f.hasCompactSupport.mono fun x hx hfx ↦ hx (by simp [hfx])
  · -- step 10: `supp X ⊆ {|x - ξ| ≥ R + ε}`, a closed set inside `(B_R(ξ))ᶜ`
    have hcl : IsClosed {x : Ambient n ℓ | R + ε ≤ ‖x - ξ‖} :=
      isClosed_le continuous_const (continuous_id.sub continuous_const).norm
    refine (closure_minimal (fun x hx ↦ ?_) hcl).trans fun x hx ↦ ?_
    · by_contra hlt
      exact hx (by simp [hzero ‖x - ξ‖ (norm_nonneg _) (not_le.1 hlt).le])
    · simp only [mem_compl_iff, mem_closedBall, dist_eq_norm, not_le]
      exact lt_of_lt_of_le (by linarith) hx
/-- **Measurability and unit bounds of `|D^⊥r|²` (Simon Ch. 4, 6.1, step 7(b); cf. 3.2–3.3).**
If `x ↦ p_{T_x V}` is `μ_V`-a.e. strongly measurable, then so is
`q(x) = |p_{(T_x V)^⊥}(x - ξ)|² / |x - ξ|²` (`q(ξ) = 0 / 0 = 0`), and `0 ≤ q ≤ 1` everywhere. -/
theorem Submission.aestronglyMeasurable_normalRadialSq_and_bounds : (∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (ξ : Ambient n ℓ), AEStronglyMeasurable (fun x ↦ (V.tangentSpace x).starProjection) V.weight → AEStronglyMeasurable (fun x ↦ V.normalRadialSq ξ x) V.weight ∧ ∀ x, 0 ≤ V.normalRadialSq ξ x ∧ V.normalRadialSq ξ x ≤ 1) := by
  intro n ℓ V ξ hP
  -- `p_{(T_x V)^⊥} = 1 - p_{T_x V}`, so `x ↦ p_{(T_x V)^⊥}` is a.e. strongly measurable.
  have hQ : AEStronglyMeasurable (fun x ↦ (V.tangentSpace x)ᗮ.starProjection) V.weight := by
    simp_rw [Submodule.starProjection_orthogonal']
    exact aestronglyMeasurable_const.sub hP
  -- Evaluation `(L, v) ↦ L v` is continuous bilinear, and `x ↦ x - ξ` is continuous.
  have hQv : AEStronglyMeasurable (fun x ↦ (V.tangentSpace x)ᗮ.starProjection (x - ξ)) V.weight :=
    (ContinuousLinearMap.id ℝ (Ambient n ℓ →L[ℝ] Ambient n ℓ)).aestronglyMeasurable_comp₂
      (f := fun x ↦ (V.tangentSpace x)ᗮ.starProjection) (g := fun x ↦ x - ξ) hQ
      (continuous_id.sub continuous_const).aestronglyMeasurable
  -- `x ↦ (|x - ξ|²)⁻¹` is Borel measurable, and `ℝ` is second countable.
  have hden : AEStronglyMeasurable (fun x : Ambient n ℓ ↦ (‖x - ξ‖ ^ 2)⁻¹) V.weight :=
    ((continuous_id.sub continuous_const).norm.pow 2).measurable.inv.aestronglyMeasurable
  refine ⟨?_, fun x ↦ ⟨?_, ?_⟩⟩
  · -- `a / b = a * b⁻¹` for all real `a, b` (also for `b = 0`).
    simp only [RectifiableVarifold.normalRadialSq, div_eq_mul_inv]
    exact (hQv.norm.pow 2).mul hden
  · exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  · -- `|p_{(T_x V)^⊥} v| ≤ |v|`; `a / b ≤ 1` needs only `a ≤ b` and `0 ≤ b`.
    exact div_le_one_of_le₀
      (pow_le_pow_left₀ (norm_nonneg _) (Submodule.norm_starProjection_apply_le _ _) 2)
      (sq_nonneg _)
/-- Positivity argument of Simon 6.1 (p. 100), for an abstract measure `μ` and weight `q` (applied
with `μ = μ_V` and `q = |D^⊥r|²`). Let `μ` be finite on compact sets with compact support,
`U = ℝ^{n+ℓ} \ B_R(ξ)`, `r = |x - ξ|`, `H` locally `μ`-integrable on `U` with `|H · (x - ξ)| < n`
`μ`-a.e. in `U`, `q` a.e. strongly measurable with `0 ≤ q ≤ 1`, and `γ ∈ C¹` with `γ, γ' ≥ 0` on
`[0, ∞)`, `γ = 0` on `[0, R + ε]` and `γ > 0` on `(R + ε, ∞)`. If
`∫_U (nγ(r) + rγ'(r)(1 - q)) dμ = -∫_U γ(r)(x - ξ) · H dμ`, then `spt μ ⊆ B_{R+ε}(ξ)`.
Both integrands are integrable (`μ` is finite and the left one is bounded on `spt μ`; the right one
vanishes off the compact `spt μ ∩ {r ≥ R + ε} ⊆ U`, on which `H` is integrable), so
`∫_U (F + G) dμ = 0` with `F + G ≥ γ(r)(n - |(x - ξ) · H|) ≥ 0` `μ`-a.e. in `U`; hence `γ(r) = 0`
`μ`-a.e. in `U`, and the open set `{r > R + ε} ⊆ U` is `μ`-null, so it misses `spt μ`. -/
theorem Submission.support_subset_closedBall_of_radial_identity : ∀ (n ℓ : ℕ) (μ : Measure (Ambient n ℓ)) (H : Ambient n ℓ → Ambient n ℓ) (q : Ambient n ℓ → ℝ) (γ : ℝ → ℝ) (ξ : Ambient n ℓ) (R ε : ℝ), 0 < n → 0 ≤ R → 0 < ε → IsFiniteMeasureOnCompacts μ → IsCompact μ.support → LocallyIntegrableOn H (closedBall ξ R)ᶜ μ → AEStronglyMeasurable q μ → (∀ x, 0 ≤ q x ∧ q x ≤ 1) → ContDiff ℝ 1 γ → (∀ t : ℝ, 0 ≤ t → 0 ≤ γ t ∧ 0 ≤ deriv γ t) → (∀ t : ℝ, 0 ≤ t → t ≤ R + ε → γ t = 0) → (∀ t : ℝ, R + ε < t → 0 < γ t) → (∀ᵐ x ∂μ, x ∈ (closedBall ξ R)ᶜ → |inner ℝ (H x) (x - ξ)| < (n : ℝ)) → ∫ x in (closedBall ξ R)ᶜ, ((n : ℝ) * γ ‖x - ξ‖ + ‖x - ξ‖ * deriv γ ‖x - ξ‖ * (1 - q x)) ∂μ = -∫ x in (closedBall ξ R)ᶜ, γ ‖x - ξ‖ * inner ℝ (x - ξ) (H x) ∂μ → μ.support ⊆ closedBall ξ (R + ε) := by
  intro n ℓ μ H q γ ξ R ε hn hR hε hfin hcpt hHloc hq hq01 hγ hγnn hγ0 hγpos hC hId
  have hUm : MeasurableSet (closedBall ξ R)ᶜ := measurableSet_closedBall.compl
  have hγc : Continuous γ := hγ.continuous
  have hγ'c : Continuous (deriv γ) := hγ.continuous_deriv le_rfl
  have hrc : Continuous fun x : Ambient n ℓ ↦ ‖x - ξ‖ := (continuous_id.sub continuous_const).norm
  have hr0 : ∀ x : Ambient n ℓ, 0 ≤ ‖x - ξ‖ := fun x ↦ norm_nonneg _
  have hmemU : ∀ x : Ambient n ℓ, R < ‖x - ξ‖ → x ∈ (closedBall ξ R)ᶜ := fun x hx ↦ by
    rwa [mem_compl_iff, mem_closedBall, dist_eq_norm, not_le]
  -- step 1: `μ(E \ spt μ) = 0`, so `μ` is a finite measure
  have hae : ∀ᵐ x ∂μ, x ∈ μ.support := Measure.support_mem_ae
  have : IsFiniteMeasure μ := ⟨(measure_univ_le_add_compl μ.support).trans_lt
    (by rw [Measure.measure_compl_support, add_zero]; exact hcpt.measure_lt_top)⟩
  -- steps 2–4: `F = nγ(r) + rγ'(r)(1 - q)` is a.e. strongly measurable and bounded on `spt μ`
  set F : Ambient n ℓ → ℝ := fun x ↦
    (n : ℝ) * γ ‖x - ξ‖ + ‖x - ξ‖ * deriv γ ‖x - ξ‖ * (1 - q x) with hFdef
  set G : Ambient n ℓ → ℝ := fun x ↦ γ ‖x - ξ‖ * inner ℝ (x - ξ) (H x) with hGdef
  have hFlow : ∀ x, (n : ℝ) * γ ‖x - ξ‖ ≤ F x := fun x ↦ by
    have := mul_nonneg (mul_nonneg (hr0 x) (hγnn _ (hr0 x)).2) (sub_nonneg.2 (hq01 x).2)
    simp only [hFdef]
    linarith
  have hFle : ∀ x, F x ≤ (n : ℝ) * γ ‖x - ξ‖ + ‖x - ξ‖ * deriv γ ‖x - ξ‖ := fun x ↦ by
    have := mul_le_of_le_one_right (mul_nonneg (hr0 x) (hγnn _ (hr0 x)).2)
      (sub_le_self 1 (hq01 x).1)
    simp only [hFdef]
    linarith
  have hFnn : ∀ x, 0 ≤ F x := fun x ↦
    (mul_nonneg (Nat.cast_nonneg n) (hγnn _ (hr0 x)).1).trans (hFlow x)
  obtain ⟨C₁, hC₁⟩ := hcpt.exists_bound_of_continuousOn
    (f := fun x : Ambient n ℓ ↦ (n : ℝ) * γ ‖x - ξ‖ + ‖x - ξ‖ * deriv γ ‖x - ξ‖)
    ((continuous_const.mul (hγc.comp hrc)).add (hrc.mul (hγ'c.comp hrc))).continuousOn
  have hFmeas : AEStronglyMeasurable F μ :=
    (continuous_const.mul (hγc.comp hrc)).aestronglyMeasurable.add
      ((hrc.mul (hγ'c.comp hrc)).aestronglyMeasurable.mul (aestronglyMeasurable_const.sub hq))
  have hFint : Integrable F μ := by
    refine Integrable.of_bound hFmeas C₁ ?_
    filter_upwards [hae] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hFnn x)]
    exact (hFle x).trans ((le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC₁ x hx))
  -- step 5: `G = γ(r)(x - ξ) · H` is integrable on `S = spt μ ∩ {r ≥ R + ε} ⊆ U`, and `G = 0`
  -- `μ`-a.e. on `U \ S`
  set S : Set (Ambient n ℓ) := μ.support ∩ {x | R + ε ≤ ‖x - ξ‖}
  have hSc : IsCompact S := hcpt.inter_right (isClosed_le continuous_const hrc)
  have hSU : S ⊆ (closedBall ξ R)ᶜ := fun x hx ↦
    hmemU x (by have : R + ε ≤ ‖x - ξ‖ := hx.2; linarith)
  have hHS : IntegrableOn H S μ := hHloc.integrableOn_compact_subset hSU hSc
  obtain ⟨C₂, hC₂⟩ := hcpt.exists_bound_of_continuousOn
    (f := fun x : Ambient n ℓ ↦ γ ‖x - ξ‖ * ‖x - ξ‖) ((hγc.comp hrc).mul hrc).continuousOn
  have hGmeas : AEStronglyMeasurable G (μ.restrict S) :=
    (hγc.comp hrc).aestronglyMeasurable.mul (continuous_inner.comp_aestronglyMeasurable
      ((continuous_id.sub continuous_const).aestronglyMeasurable.prodMk hHS.aestronglyMeasurable))
  have hGS : IntegrableOn G S μ := by
    refine Integrable.mono' (hHS.norm.const_mul C₂) hGmeas ?_
    filter_upwards [ae_restrict_mem hSc.isClosed.measurableSet] with x hx
    have hg := (hγnn ‖x - ξ‖ (hr0 x)).1
    have hb := hC₂ x hx.1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hg (hr0 x))] at hb
    calc ‖G x‖ = γ ‖x - ξ‖ * |inner ℝ (x - ξ) (H x)| := by
          simp only [hGdef, norm_mul, Real.norm_eq_abs, abs_of_nonneg hg]
      _ ≤ γ ‖x - ξ‖ * (‖x - ξ‖ * ‖H x‖) :=
          mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) hg
      _ = γ ‖x - ξ‖ * ‖x - ξ‖ * ‖H x‖ := by ring
      _ ≤ C₂ * ‖H x‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg _)
  have hGU : IntegrableOn G (closedBall ξ R)ᶜ μ := by
    refine hGS.of_ae_sdiff_eq_zero hUm.nullMeasurableSet ?_
    filter_upwards [hae] with x hx hxUS
    have hlt : ‖x - ξ‖ < R + ε := lt_of_not_ge fun h ↦ hxUS.2 ⟨hx, h⟩
    simp only [hGdef, hγ0 _ (hr0 x) hlt.le, zero_mul]
  -- step 6: `∫_U (F + G) dμ = 0` and `F + G ≥ γ(r)(n - |(x - ξ) · H|) ≥ 0` `μ`-a.e. on `U`
  have hsum : ∫ x in (closedBall ξ R)ᶜ, (F x + G x) ∂μ = 0 := by
    rw [integral_add hFint.integrableOn hGU]
    have h : ∫ x in (closedBall ξ R)ᶜ, F x ∂μ = -∫ x in (closedBall ξ R)ᶜ, G x ∂μ := hId
    linarith
  have hkey : ∀ x, γ ‖x - ξ‖ * ((n : ℝ) - |inner ℝ (x - ξ) (H x)|) ≤ F x + G x := fun x ↦ by
    have h1 : γ ‖x - ξ‖ * -|inner ℝ (x - ξ) (H x)| ≤ G x :=
      mul_le_mul_of_nonneg_left (neg_abs_le _) (hγnn ‖x - ξ‖ (hr0 x)).1
    have h2 := hFlow x
    linarith
  have hCU : ∀ᵐ x ∂μ, x ∈ (closedBall ξ R)ᶜ → |inner ℝ (x - ξ) (H x)| < (n : ℝ) := by
    filter_upwards [hC] with x hx hxU
    rw [real_inner_comm]
    exact hx hxU
  have hnn : 0 ≤ᵐ[μ.restrict (closedBall ξ R)ᶜ] fun x ↦ F x + G x := by
    rw [EventuallyLE, ae_restrict_iff' hUm]
    filter_upwards [hCU] with x hx hxU
    exact (mul_nonneg (hγnn _ (hr0 x)).1 (sub_nonneg.2 (hx hxU).le)).trans (hkey x)
  have hzero : (fun x ↦ F x + G x) =ᵐ[μ.restrict (closedBall ξ R)ᶜ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnn (hFint.integrableOn.add hGU)).1 hsum
  have hγU : ∀ᵐ x ∂μ, x ∈ (closedBall ξ R)ᶜ → γ ‖x - ξ‖ = 0 := by
    rw [EventuallyEq, ae_restrict_iff' hUm] at hzero
    filter_upwards [hzero, hCU] with x hx hCx hxU
    have hk := hkey x
    have h0 : F x + G x = 0 := hx hxU
    by_contra hne
    have hpos := mul_pos (lt_of_le_of_ne (hγnn _ (hr0 x)).1 (Ne.symm hne)) (sub_pos.2 (hCx hxU))
    linarith
  -- step 7: the open set `{r > R + ε} ⊆ U` is `μ`-null, hence disjoint from `spt μ`
  have hO : IsOpen {x : Ambient n ℓ | R + ε < ‖x - ξ‖} := isOpen_lt continuous_const hrc
  have hμO : μ {x : Ambient n ℓ | R + ε < ‖x - ξ‖} = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hγU] with x hx hxO
    have hxO' : R + ε < ‖x - ξ‖ := hxO
    exact (hγpos _ hxO').ne' (hx (hmemU x (by linarith)))
  intro x hx
  have hxO : x ∉ {x : Ambient n ℓ | R + ε < ‖x - ξ‖} := fun h ↦
    Measure.subset_compl_support_of_isOpen hO hμO h hx
  rw [mem_closedBall, dist_eq_norm]
  exact not_lt.1 hxO

/-- **Ch. 4, 6.1 (p. 100) from the radial first variation.** Assume the radial first variation
identity (3.2–3.3, 3.14) for `X(x) = h(x)γ(|x - ξ|)(x - ξ)`, and that for `n ≥ 1` the weight `μ_V`
is finite on compact sets, `dim T_x V = n` `μ_V`-a.e. and `x ↦ p_{T_x V}` is `μ_V`-a.e. strongly
measurable. Then `SupportInBall`: for `ε > 0`, the identity with `h = ζ`, `ζ = 1` and `∇ζ = 0` on
`spt V`, and `γ = 0` on `[0, R + ε]`, `γ > 0` beyond, reads
`n ∫_U γ(r) dμ_V + ∫_U rγ'(r)(1 - |D^⊥r|²) dμ_V = -∫_U γ(r)(x - ξ)·H dμ_V`, and with
`|H·(x - ξ)| < n` it forces `spt V ⊆ B_{R+ε}(ξ)`. -/
theorem Submission.support_in_ball_of_radial_first_variation : (∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)) (H : Ambient n ℓ → Ambient n ℓ) (h : Ambient n ℓ → ℝ) (γ : ℝ → ℝ) (ξ : Ambient n ℓ), (∀ᵐ x ∂V.weight, Module.finrank ℝ (V.tangentSpace x) = n) → IsOpen U → V.HasMeanCurvatureIn U H → ContDiffOn ℝ 1 h U → ContDiff ℝ 1 γ → IsTestField U (fun x ↦ (h x * γ ‖x - ξ‖) • (x - ξ)) → ∫ x in U, (h x * ((n : ℝ) * γ ‖x - ξ‖ + ‖x - ξ‖ * deriv γ ‖x - ξ‖ * (1 - V.normalRadialSq ξ x)) + γ ‖x - ξ‖ * inner ℝ (x - ξ) (V.tangentialGradient h x)) ∂V.weight = -∫ x in U, h x * γ ‖x - ξ‖ * inner ℝ (x - ξ) (H x) ∂V.weight) → (∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ), 0 < n → IsFiniteMeasureOnCompacts V.weight ∧ (∀ᵐ x ∂V.weight, Module.finrank ℝ (V.tangentSpace x) = n) ∧ AEStronglyMeasurable (fun x ↦ (V.tangentSpace x).starProjection) V.weight) → SupportInBall := by
  intro hRFV hGF n ℓ V H ξ R hn hR hH hcurv hcpt
  obtain ⟨hfin, hdim, hproj⟩ := hGF n ℓ V hn
  -- `|H(x)·(x - ξ)| < n` for `μ_V`-a.e. `x ∈ U = ℝ^{n+ℓ} \ B_R(ξ)`.
  have hC : ∀ᵐ x ∂V.weight, x ∈ (closedBall ξ R)ᶜ → |inner ℝ (H x) (x - ξ)| < (n : ℝ) := by
    filter_upwards [hcurv] with x hx hxU
    have h := (inv_mul_lt_iff₀ (Nat.cast_pos.mpr hn : (0 : ℝ) < n)).1 (hx hxU)
    rwa [mul_one] at h
  -- `|D^⊥r|²` is `μ_V`-a.e. strongly measurable with values in `[0, 1]`.
  obtain ⟨hqm, hq⟩ := Submission.aestronglyMeasurable_normalRadialSq_and_bounds n ℓ V ξ hproj
  have hball : ∀ ε : ℝ, 0 < ε → V.support ⊆ closedBall ξ (R + ε) := by
    intro ε hε
    -- `X(x) = ζ(x)γ(|x - ξ|)(x - ξ)` is a test field in `U`, with `ζ = 1`, `∇ζ = 0` on `spt V`,
    -- so (RFV) applies with `h = ζ`.
    obtain ⟨ζ, γ, hζ, hζK, hγ, hγnn, hγ0, hγpos, hX⟩ :=
      Submission.exists_radial_cutoff_test_field n ℓ V.support ξ R ε hcpt hR hε
    have hstar := hRFV n ℓ V (closedBall ξ R)ᶜ H ζ γ ξ hdim isClosed_closedBall.isOpen_compl hH
      hζ.contDiffOn hγ hX
    -- `μ_V`-a.e. `x` lies in `spt V`, where `ζ = 1` and `∇^M ζ = p_{T_x V}(∇ζ) = 0`, so `ζ` drops
    -- out of both sides of (RFV).
    have hae : ∀ᵐ x ∂V.weight.restrict (closedBall ξ R)ᶜ, ζ x = 1 ∧ gradient ζ x = 0 := by
      refine ae_restrict_of_ae ?_
      filter_upwards [V.weight.support_mem_ae] with x hx using hζK x hx
    have hL : ∫ x in (closedBall ξ R)ᶜ, (ζ x * ((n : ℝ) * γ ‖x - ξ‖ + ‖x - ξ‖ * deriv γ ‖x - ξ‖ *
          (1 - V.normalRadialSq ξ x)) + γ ‖x - ξ‖ * inner ℝ (x - ξ) (V.tangentialGradient ζ x))
          ∂V.weight =
        ∫ x in (closedBall ξ R)ᶜ, ((n : ℝ) * γ ‖x - ξ‖ + ‖x - ξ‖ * deriv γ ‖x - ξ‖ *
          (1 - V.normalRadialSq ξ x)) ∂V.weight := by
      refine integral_congr_ae ?_
      filter_upwards [hae] with x hx
      simp only [RectifiableVarifold.tangentialGradient, hx.1, hx.2, map_zero, inner_zero_right,
        mul_zero, add_zero, one_mul]
    have hR' : ∫ x in (closedBall ξ R)ᶜ, ζ x * γ ‖x - ξ‖ * inner ℝ (x - ξ) (H x) ∂V.weight =
        ∫ x in (closedBall ξ R)ᶜ, γ ‖x - ξ‖ * inner ℝ (x - ξ) (H x) ∂V.weight := by
      refine integral_congr_ae ?_
      filter_upwards [hae] with x hx
      simp only [hx.1, one_mul]
    rw [hL, hR'] at hstar
    -- The identity and `|H·(x - ξ)| < n` force `γ(|x - ξ|) = 0` `μ_V`-a.e. on `U`.
    exact Submission.support_subset_closedBall_of_radial_identity n ℓ V.weight H
      (V.normalRadialSq ξ) γ ξ R ε hn hR hε hfin hcpt hH.1 hqm hq hγ hγnn hγ0 hγpos hC hstar
  -- `spt V ⊆ ⋂_{ε > 0} B_{R+ε}(ξ) = B_R(ξ)`.
  intro x hx
  rw [mem_closedBall]
  exact le_of_forall_pos_le_add fun ε hε ↦ mem_closedBall.1 (hball ε hε hx)
/-- **Ch. 4, 6.2 from 6.1 (p. 101).** Assume `SupportInBall` (6.1). If `spt V` is compact and `V`
is stationary in `ℝ^{n+ℓ} \ K` with `K` compact, then `spt V ⊆ conv K`: for `y ∉ conv K` there is
a closed ball `B_R(c) ⊇ K` with `R ≥ 0` and `y ∉ B_R(c)` (`conv K` is compact by Carathéodory), `V`
has generalized mean curvature `0` in `ℝ^{n+ℓ} \ B_R(c) ⊆ ℝ^{n+ℓ} \ K`, and 6.1 gives
`spt V ⊆ B_R(c)`. -/
theorem Submission.convex_hull_property_of_support_in_ball : SupportInBall → ConvexHullProperty := by
  intro hBall n ℓ V K hn hK hV hstat
  classical
  -- Ball Lemma: every `y ∉ conv K` lies outside some closed ball `B_R(c) ⊇ K` with `R ≥ 0`.
  have hsep : ∀ y ∉ convexHull ℝ K, ∃ (c : Ambient n ℓ) (R : ℝ),
      0 ≤ R ∧ K ⊆ closedBall c R ∧ y ∉ closedBall c R := by
    intro y hy
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · -- `K = ∅`: `dim ℝ^{n+ℓ} = n + ℓ ≥ 1`, so there is `c ≠ y`; take `R = 0`.
      have : Nontrivial (Ambient n ℓ) :=
        Module.nontrivial_of_finrank_pos (by rw [finrank_euclideanSpace_fin]; omega)
      obtain ⟨c, hc⟩ := exists_ne y
      refine ⟨c, 0, le_rfl, by simp [hKe], ?_⟩
      rw [closedBall_zero, mem_singleton_iff]
      exact hc.symm
    -- `K ≠ ∅`: `conv K` is compact. By Carathéodory every point of `conv K` is a convex
    -- combination of at most `dim ℝ^{n+ℓ} + 1` points of `K`, so `conv K` is a finite union of
    -- continuous images `W j` of the compact sets `{w ∈ [0,1]^j : ∑ w = 1} × K^j`.
    have hcomp : IsCompact (convexHull ℝ K) := by
      let W : ℕ → Set (Ambient n ℓ) := fun j ↦
        (fun p : (Fin j → ℝ) × (Fin j → Ambient n ℓ) ↦ ∑ i, p.1 i • p.2 i) ''
          ((Icc (0 : Fin j → ℝ) 1 ∩ {w | ∑ i, w i = 1}) ×ˢ univ.pi fun _ ↦ K)
      have hW : ∀ j, IsCompact (W j) := fun j ↦
        ((isCompact_Icc.inter_right (isClosed_eq (by fun_prop) continuous_const)).prod
          (isCompact_univ_pi fun _ ↦ hK)).image (by fun_prop)
      suffices h : convexHull ℝ K =
          ⋃ j ∈ Finset.range (Module.finrank ℝ (Ambient n ℓ) + 2), W j by
        rw [h]
        exact (Finset.finite_toSet _).isCompact_biUnion fun j _ ↦ hW j
      refine subset_antisymm (fun x hx ↦ ?_) ?_
      · -- A finset `t ⊆ K` of minimal cardinality with `x ∈ conv t`.
        have hex : ∃ m, ∃ t : Finset (Ambient n ℓ), ↑t ⊆ K ∧
            x ∈ convexHull ℝ (t : Set (Ambient n ℓ)) ∧ t.card = m := by
          rw [convexHull_eq_union_convexHull_finite_subsets] at hx
          simp only [mem_iUnion, exists_prop] at hx
          obtain ⟨t, htK, hxt⟩ := hx
          exact ⟨_, t, htK, hxt, rfl⟩
        obtain ⟨t, htK, hxt, htm⟩ := Nat.find_spec hex
        obtain ⟨w, hw0, hw1, hwx⟩ := Finset.mem_convexHull'.1 hxt
        -- Carathéodory: `#t ≤ dim ℝ^{n+ℓ} + 1`. Otherwise an affine relation `∑ g z • z = 0`,
        -- `∑ g z = 0`, `g ≠ 0` on `t` lets us remove a point of `t`, contradicting minimality.
        have hcard : t.card ≤ Module.finrank ℝ (Ambient n ℓ) + 1 := by
          by_contra hlt
          obtain ⟨g, hgx, hg1, hg0⟩ :=
            Module.exists_nontrivial_relation_sum_zero_of_finrank_succ_lt_card (not_le.mp hlt)
          obtain ⟨i₁, hi₁, hgi₁⟩ := Finset.exists_pos_of_sum_zero_of_exists_nonzero g hg1 hg0
          obtain ⟨i₀, hi₀, hmin⟩ := (t.filter fun z ↦ 0 < g z).exists_min_image
            (fun z ↦ w z / g z) ⟨i₁, Finset.mem_filter.2 ⟨hi₁, hgi₁⟩⟩
          rw [Finset.mem_filter] at hi₀
          let k : Ambient n ℓ → ℝ := fun z ↦ w z - w i₀ / g i₀ * g z
          have hk : k i₀ = 0 := by simp [k, hi₀.2.ne']
          have hxe : x ∈ convexHull ℝ (↑(t.erase i₀) : Set (Ambient n ℓ)) := by
            refine Finset.mem_convexHull'.2 ⟨k, fun z hz ↦ ?_, ?_, ?_⟩
            · have hzt := Finset.mem_of_mem_erase hz
              simp only [k, sub_nonneg]
              by_cases hgz : 0 < g z
              · exact (le_div_iff₀ hgz).1 (hmin z (Finset.mem_filter.2 ⟨hzt, hgz⟩))
              · exact (mul_nonpos_of_nonneg_of_nonpos (div_nonneg (hw0 _ hi₀.1) hi₀.2.le)
                  (not_lt.mp hgz)).trans (hw0 z hzt)
            · rw [Finset.sum_erase t hk]
              simp only [k, Finset.sum_sub_distrib, ← Finset.mul_sum, hw1, hg1, mul_zero, sub_zero]
            · rw [Finset.sum_erase t (f := fun z ↦ k z • z) (by simp [hk])]
              simp only [k, sub_smul, mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum, hgx,
                smul_zero, sub_zero, hwx]
          exact Nat.find_min hex
            (show (t.erase i₀).card < Nat.find hex by
              rw [Finset.card_erase_of_mem hi₀.1]; omega)
            ⟨t.erase i₀, (Finset.coe_subset.2 (Finset.erase_subset _ _)).trans htK, hxe, rfl⟩
        -- Reindex the convex combination by `Fin #t`.
        let e := t.equivFin
        let a : Fin t.card → ℝ := fun i ↦ w (e.symm i)
        let z : Fin t.card → Ambient n ℓ := fun i ↦ (e.symm i : Ambient n ℓ)
        have hsum : ∑ i, a i = 1 :=
          (Equiv.sum_comp e.symm fun j : t ↦ w j).trans ((Finset.sum_coe_sort t w).trans hw1)
        have hsumx : ∑ i, a i • z i = x :=
          (Equiv.sum_comp e.symm fun j : t ↦ w j • (j : Ambient n ℓ)).trans
            ((Finset.sum_coe_sort t fun y ↦ w y • y).trans hwx)
        have ha0 : ∀ i, 0 ≤ a i := fun i ↦ hw0 _ (e.symm i).2
        have ha1 : ∀ i, a i ≤ 1 := fun i ↦
          hsum ▸ Finset.single_le_sum (fun j _ ↦ ha0 j) (Finset.mem_univ i)
        exact mem_iUnion₂.2 ⟨t.card, Finset.mem_range.2 (by omega),
          (a, z), ⟨⟨⟨ha0, ha1⟩, hsum⟩, fun i _ ↦ htK (e.symm i).2⟩, hsumx⟩
      · -- Conversely, convex combinations of points of `K` lie in `conv K`.
        simp only [iUnion_subset_iff]
        rintro j - _ ⟨⟨a, z⟩, ⟨⟨⟨ha0, -⟩, hsum⟩, hz⟩, rfl⟩
        exact (convex_convexHull ℝ K).sum_mem (fun i _ ↦ ha0 i) hsum
          fun i _ ↦ subset_convexHull ℝ K (hz i (mem_univ i))
    -- Nearest point `z₀ ∈ conv K` to `y`: `⟪y - z₀, x - z₀⟫ ≤ 0` for `x ∈ conv K`, and
    -- `η = |y - z₀| > 0`.
    obtain ⟨z₀, hz₀, hmin⟩ := exists_norm_eq_iInf_of_complete_convex hKne.convexHull
      hcomp.isComplete (convex_convexHull ℝ K) y
    have hvar := (norm_eq_iInf_iff_real_inner_le_zero (convex_convexHull ℝ K) hz₀).1 hmin
    have hη : 0 < ‖y - z₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr fun h ↦ hy (h ▸ hz₀))
    -- `K ⊆ B_D(z₀)`; with `t η² = D² + 1`, the ball `B_R(c)`, `c = z₀ - t (y - z₀)`,
    -- `R² = D² + t² η²`, contains `K` and `|y - c| = (1 + t) η > R`.
    obtain ⟨D, hD, hKD⟩ := hK.isBounded.subset_ball_lt 0 z₀
    set t : ℝ := (D ^ 2 + 1) / ‖y - z₀‖ ^ 2
    have ht : 0 < t := by positivity
    have htη : t * ‖y - z₀‖ ^ 2 = D ^ 2 + 1 := div_mul_cancel₀ _ (by positivity)
    set R : ℝ := Real.sqrt (D ^ 2 + t ^ 2 * ‖y - z₀‖ ^ 2)
    have hR : 0 ≤ R := Real.sqrt_nonneg _
    have hR2 : R ^ 2 = D ^ 2 + t ^ 2 * ‖y - z₀‖ ^ 2 := Real.sq_sqrt (by positivity)
    refine ⟨z₀ - t • (y - z₀), R, hR, fun x hx ↦ ?_, ?_⟩
    · have hxD : ‖x - z₀‖ < D := by simpa only [mem_ball, dist_eq_norm] using hKD hx
      have hi : inner ℝ (x - z₀) (y - z₀) ≤ 0 := by
        rw [real_inner_comm]
        exact hvar x (subset_convexHull ℝ K hx)
      have heq : x - (z₀ - t • (y - z₀)) = (x - z₀) + t • (y - z₀) := by abel
      have hsq : ‖x - (z₀ - t • (y - z₀))‖ ^ 2 ≤ R ^ 2 := by
        rw [heq, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos ht, hR2]
        nlinarith [mul_nonpos_of_nonneg_of_nonpos ht.le hi, norm_nonneg (x - z₀)]
      rw [mem_closedBall, dist_eq_norm]
      nlinarith [norm_nonneg (x - (z₀ - t • (y - z₀)))]
    · have heq : y - (z₀ - t • (y - z₀)) = (1 + t) • (y - z₀) := by module
      rw [mem_closedBall, dist_eq_norm, heq, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by linarith), not_le]
      nlinarith [sq_nonneg ((1 + t) * ‖y - z₀‖ + R)]
  intro y hy
  by_contra hyK
  obtain ⟨c, R, hR, hKc, hyc⟩ := hsep y hyK
  -- `V` has generalized mean curvature `0` in `ℝ^{n+ℓ} \ B_R(c) ⊆ ℝ^{n+ℓ} \ K`.
  have hmc : V.HasMeanCurvatureIn (closedBall c R)ᶜ fun _ ↦ 0 := by
    refine ⟨locallyIntegrableOn_zero, fun X hX ↦ ?_⟩
    rw [hstat X ⟨hX.1, hX.2.1, hX.2.2.trans (compl_subset_compl.mpr hKc)⟩]
    simp
  -- 6.1 with `H = 0`, `ξ = c`: `spt V ⊆ B_R(c)`, contradicting `y ∈ spt V \ B_R(c)`.
  exact hyc (hBall n ℓ V (fun _ ↦ 0) c R hn hR hmc
    (Filter.Eventually.of_forall fun x _ ↦ by simp) hV hy)
/-- **Derivative of the radial field, including the centre** (Simon Ch. 4, 3.2). For `γ ∈ C¹`
and `r = |x - ξ|`, the field `g(y) = γ(|y - ξ|)(y - ξ)` is differentiable at `x` with
`Dg(x)v = γ(r)v + (γ'(r)/r)⟨x - ξ, v⟩(x - ξ)` (with `γ'(r)/r = 0` when `r = 0`). At `x = ξ`
this is `γ(0)·I`, since `g(ξ + v) - g(ξ) - γ(0)v = (γ(|v|) - γ(0))v = o(|v|)` by continuity of
`γ`; for `x ≠ ξ`, `|y - ξ| = √(|y - ξ|²)` has derivative `r⁻¹⟨x - ξ, ·⟩` and the chain and
product rules give the formula. -/
theorem Submission.radial_vector_field_hasFDerivAt : ∀ (n ℓ : ℕ) (γ : ℝ → ℝ) (ξ x : Ambient n ℓ), ContDiff ℝ 1 γ → HasFDerivAt (fun y : Ambient n ℓ ↦ γ ‖y - ξ‖ • (y - ξ)) (γ ‖x - ξ‖ • ContinuousLinearMap.id ℝ (Ambient n ℓ) + (deriv γ ‖x - ξ‖ / ‖x - ξ‖) • (innerSL ℝ (x - ξ)).smulRight (x - ξ)) x := by
  intro n ℓ γ ξ x hγ
  have hγd : Differentiable ℝ γ := hγ.differentiable one_ne_zero
  rcases eq_or_ne x ξ with rfl | hx
  · -- the centre: the claimed derivative is `γ(0)·I` and the remainder is `(γ(|v|) - γ(0))v`
    simp only [sub_self, norm_zero, div_zero, zero_smul, add_zero]
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    have h1 : Tendsto (fun v : Ambient n ℓ ↦ γ ‖v‖ - γ 0) (𝓝 0) (𝓝 0) := by
      have h := (hγd.continuous.tendsto (‖(0 : Ambient n ℓ)‖)).comp (continuous_norm.tendsto 0)
      simpa [Function.comp_def] using h.sub_const (γ 0)
    have h2 : (fun v : Ambient n ℓ ↦ (γ ‖v‖ - γ 0) • v) =o[𝓝 0] fun v ↦ v := by
      have h := ((Asymptotics.isLittleO_one_iff ℝ).2 h1).smul_isBigO
        (Asymptotics.isBigO_refl (fun v : Ambient n ℓ ↦ v) (𝓝 0))
      simpa only [one_smul] using h
    refine h2.congr_left fun v ↦ ?_
    simp [sub_smul]
  · -- off the centre: `|y - ξ| = √(|y - ξ|²)`, then the chain and product rules
    have hr : 0 < ‖x - ξ‖ := norm_pos_iff.2 (sub_ne_zero.2 hx)
    have hsub : HasFDerivAt (fun y : Ambient n ℓ ↦ y - ξ) (ContinuousLinearMap.id ℝ (Ambient n ℓ)) x :=
      (hasFDerivAt_id x).sub_const ξ
    have hnorm : HasFDerivAt (fun y : Ambient n ℓ ↦ ‖y - ξ‖) (‖x - ξ‖⁻¹ • innerSL ℝ (x - ξ)) x := by
      have h := hsub.norm_sq.sqrt (pow_ne_zero 2 hr.ne')
      simp only [Real.sqrt_sq_eq_abs, abs_norm] at h
      refine h.congr_fderiv ?_
      ext v
      simp
      field_simp
    have hφ : HasFDerivAt (fun y : Ambient n ℓ ↦ γ ‖y - ξ‖)
        (deriv γ ‖x - ξ‖ • ‖x - ξ‖⁻¹ • innerSL ℝ (x - ξ)) x :=
      (hγd ‖x - ξ‖).hasDerivAt.comp_hasFDerivAt x hnorm
    refine (hφ.fun_smul hsub).congr_fderiv ?_
    ext v
    simp [smul_smul, div_eq_mul_inv]
/-- **Trace of `(c I + F(·) v) ∘ p_P`** (used for `div_M` of radial fields, Ch. 4, 3.2 and 5.1).
For a subspace `P` with orthogonal projection `p_P`, `c ∈ ℝ`, a continuous linear functional `F`
and `v ∈ ℝ^{n+ℓ}`: `trace((c I + F(·) v) ∘ p_P) = c dim P + F(p_P v)`. -/
theorem Submission.trace_scalar_add_rankOne_comp_starProjection : ∀ (n ℓ : ℕ) (P : Submodule ℝ (Ambient n ℓ)) (c : ℝ) (F : Ambient n ℓ →L[ℝ] ℝ) (v : Ambient n ℓ), LinearMap.trace ℝ (Ambient n ℓ) ((c • ContinuousLinearMap.id ℝ (Ambient n ℓ) + F.smulRight v).toLinearMap ∘ₗ P.starProjection.toLinearMap) = c * (Module.finrank ℝ P : ℝ) + F (P.starProjection v) := by
  intro n ℓ P c F v
  -- `trace p_P = dim P`: `p_P = ι ∘ π`, and `trace (ι ∘ π) = trace (π ∘ ι) = trace id_P`.
  have hp : LinearMap.trace ℝ (Ambient n ℓ) P.starProjection.toLinearMap =
      (Module.finrank ℝ P : ℝ) := by
    rw [Submodule.starProjection, ContinuousLinearMap.toLinearMap_comp,
      LinearMap.trace_comp_comm']
    have hπι : P.orthogonalProjectionOnto.toLinearMap ∘ₗ P.subtypeL.toLinearMap =
        LinearMap.id := by
      ext x
      simp
    rw [hπι, LinearMap.trace_id]
  -- `(c I + F(·) v) ∘ p_P = c p_P + (F ∘ p_P)(·) v`; the rank-one part has trace `F(p_P v)`.
  have hA : (c • ContinuousLinearMap.id ℝ (Ambient n ℓ) + F.smulRight v).toLinearMap ∘ₗ
      P.starProjection.toLinearMap = c • P.starProjection.toLinearMap +
        (F.toLinearMap ∘ₗ P.starProjection.toLinearMap).smulRight v := by
    ext w
    simp
  rw [hA, map_add, map_smul, LinearMap.trace_smulRight, hp, smul_eq_mul]
  rfl

theorem main_theorem : ApproxTangentAE ∧ FirstVariationFormula ∧ StationaryIffVariational ∧ StationaryMonotonicity ∧ StationaryDensity ∧ CanonicalRepresentative ∧ BoundedCurvatureMonotonicity ∧ LogarithmicMonotonicityError ∧ LpMonotonicity ∧ LpDensity ∧ LpSupportRepresentation ∧ PoincareInequality ∧ SobolevInequality ∧ SupportInBall ∧ ConvexHullProperty ∧ ClassicalTangent := by sorry

/-- **Pointwise tangential divergence of the weighted radial field** (Simon Ch. 4, 3.2 and 5.1).
If `dim T_x V = n`, `h` is differentiable at `x` and `γ` is `C¹`, then for
`X(y) = h(y) γ(|y - ξ|)(y - ξ)` and `r = |x - ξ|`,
`div_M X(x) = h(x)(n γ(r) + r γ'(r)(1 - |D^⊥r|²)) + γ(r) (x - ξ) · ∇^M h(x)`. -/
theorem Submission.tangentialDiv_weighted_radial_field : ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (h : Ambient n ℓ → ℝ) (γ : ℝ → ℝ) (ξ x : Ambient n ℓ), Module.finrank ℝ (V.tangentSpace x) = n → DifferentiableAt ℝ h x → ContDiff ℝ 1 γ → V.tangentialDiv (fun y ↦ (h y * γ ‖y - ξ‖) • (y - ξ)) x = h x * ((n : ℝ) * γ ‖x - ξ‖ + ‖x - ξ‖ * deriv γ ‖x - ξ‖ * (1 - V.normalRadialSq ξ x)) + γ ‖x - ξ‖ * inner ℝ (x - ξ) (V.tangentialGradient h x) := by
  intro n ℓ V h γ ξ x hdim hh hγ
  -- `X = h • g` with `g(y) = γ(|y - ξ|)(y - ξ)`; by the product rule and the derivative of `g`,
  -- `DX(x) = c I + F(·)(x - ξ)` with `c = h(x)γ(r)` and `F = h(x)(γ'(r)/r)⟨x - ξ, ·⟩ + γ(r) Dh(x)`.
  have hX : (fun y ↦ (h y * γ ‖y - ξ‖) • (y - ξ)) = fun y ↦ h y • γ ‖y - ξ‖ • (y - ξ) := by
    funext y
    exact mul_smul _ _ _
  have hDX : fderiv ℝ (fun y ↦ (h y * γ ‖y - ξ‖) • (y - ξ)) x =
      (h x * γ ‖x - ξ‖) • ContinuousLinearMap.id ℝ (Ambient n ℓ) +
        ((h x * (deriv γ ‖x - ξ‖ / ‖x - ξ‖)) • innerSL ℝ (x - ξ) +
          γ ‖x - ξ‖ • fderiv ℝ h x).smulRight (x - ξ) := by
    rw [hX, (hh.hasFDerivAt.fun_smul
      (Submission.radial_vector_field_hasFDerivAt n ℓ γ ξ x hγ)).fderiv]
    refine ContinuousLinearMap.ext fun u ↦ ?_
    simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_eq_mul]
    module
  -- Hence `div_M X(x) = c dim T_x V + F(p(x - ξ))`, with `p` the projection onto `T_x V`.
  rw [RectifiableVarifold.tangentialDiv, hDX,
    Submission.trace_scalar_add_rankOne_comp_starProjection n ℓ (V.tangentSpace x), hdim]
  set P := V.tangentSpace x
  -- Gradient term: `Dh(x)(p(x - ξ)) = ⟨∇h(x), p(x - ξ)⟩ = ⟨x - ξ, p ∇h(x)⟩ = ⟨x - ξ, ∇^M h(x)⟩`.
  have hgrad : fderiv ℝ h x (P.starProjection (x - ξ)) =
      inner ℝ (x - ξ) (V.tangentialGradient h x) := by
    rw [← inner_gradient_left, ← P.inner_starProjection_left_eq_right, real_inner_comm]
    rfl
  -- Projection term: `⟨x - ξ, p(x - ξ)⟩ = |p(x - ξ)|²`.
  have hpw : inner ℝ (x - ξ) (P.starProjection (x - ξ)) = ‖P.starProjection (x - ξ)‖ ^ 2 := by
    calc inner ℝ (x - ξ) (P.starProjection (x - ξ))
        = inner ℝ (x - ξ) (P.starProjection (P.starProjection (x - ξ))) := by
          rw [Submodule.starProjection_eq_self_iff.mpr (P.starProjection_apply_mem _)]
      _ = inner ℝ (P.starProjection (x - ξ)) (P.starProjection (x - ξ)) :=
          (P.inner_starProjection_left_eq_right _ _).symm
      _ = ‖P.starProjection (x - ξ)‖ ^ 2 := real_inner_self_eq_norm_sq _
  -- Pythagoras: `r² = |p(x - ξ)|² + |p^⊥(x - ξ)|²`, so `(γ'(r)/r)|p(x - ξ)|² = rγ'(r)(1 - q_ξ(x))`
  -- (both sides vanish when `r = 0`).
  have key : deriv γ ‖x - ξ‖ / ‖x - ξ‖ * ‖P.starProjection (x - ξ)‖ ^ 2 =
      ‖x - ξ‖ * deriv γ ‖x - ξ‖ * (1 - V.normalRadialSq ξ x) := by
    have hpy := P.norm_sq_eq_add_norm_sq_starProjection (x - ξ)
    rw [RectifiableVarifold.normalRadialSq]
    generalize ‖P.starProjection (x - ξ)‖ = a at hpy ⊢
    generalize ‖Pᗮ.starProjection (x - ξ)‖ = b at hpy ⊢
    generalize ‖x - ξ‖ = r at hpy ⊢
    rcases eq_or_ne r 0 with hr | hr
    · simp [hr]
    · rw [show a ^ 2 = r ^ 2 - b ^ 2 by linarith]
      field_simp
  simp only [add_apply, smul_apply, innerSL_apply_apply, smul_eq_mul, hgrad, hpw]
  linear_combination h x * key

/-- Simon 3.2–3.3 and 5.1 (pp. 89–90, 96) with Definition 3.14 (p. 92): the first variation
formula for the radial field `X(x) = h(x) γ(r) (x - ξ)`, `r = |x - ξ|`. If `dim T_x V = n` for
`μ_V`-a.e. `x`, `V` has generalized mean curvature `H` in the open set `U`, `h ∈ C¹(U)`,
`γ ∈ C¹(ℝ)` and `X ∈ C¹_c(U; ℝ^{n+ℓ})`, then `∫_U (h (n γ(r) + r γ'(r) (1 - |D^⊥ r|²)) +
γ(r) (x - ξ) · ∇^M h) dμ_V = -∫_U h γ(r) (x - ξ) · H dμ_V`. -/
theorem Submission.radial_first_variation : ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)) (H : Ambient n ℓ → Ambient n ℓ) (h : Ambient n ℓ → ℝ) (γ : ℝ → ℝ) (ξ : Ambient n ℓ), (∀ᵐ x ∂V.weight, Module.finrank ℝ (V.tangentSpace x) = n) → IsOpen U → V.HasMeanCurvatureIn U H → ContDiffOn ℝ 1 h U → ContDiff ℝ 1 γ → IsTestField U (fun x ↦ (h x * γ ‖x - ξ‖) • (x - ξ)) → ∫ x in U, (h x * ((n : ℝ) * γ ‖x - ξ‖ + ‖x - ξ‖ * deriv γ ‖x - ξ‖ * (1 - V.normalRadialSq ξ x)) + γ ‖x - ξ‖ * inner ℝ (x - ξ) (V.tangentialGradient h x)) ∂V.weight = -∫ x in U, h x * γ ‖x - ξ‖ * inner ℝ (x - ξ) (H x) ∂V.weight := by
  intro n ℓ V U H h γ ξ hdim hU hH hh hγ hX
  -- `X` vanishes near every point off `U`, since `tsupport X ⊆ U`.
  have hout : ∀ x ∉ U, x ∉ tsupport fun y ↦ (h y * γ ‖y - ξ‖) • (y - ξ) :=
    fun x hxU hx ↦ hxU (hX.2.2 hx)
  have hX0 : ∀ x ∉ U, (h x * γ ‖x - ξ‖) • (x - ξ) = 0 :=
    fun x hxU ↦ (image_eq_zero_of_notMem_tsupport (hout x hxU) :)
  calc _ = ∫ x in U, V.tangentialDiv (fun y ↦ (h y * γ ‖y - ξ‖) • (y - ξ)) x ∂V.weight := by
        -- Simon 3.2 and 5.1: the integrand is `div_M X` wherever `dim T_x V = n`.
        refine setIntegral_congr_ae hU.measurableSet ?_
        filter_upwards [hdim] with x hx hxU
        exact (Submission.tangentialDiv_weighted_radial_field n ℓ V h γ ξ x hx
          (hh.differentiableOn_one.differentiableAt (hU.mem_nhds hxU)) hγ).symm
    _ = ∫ x, V.tangentialDiv (fun y ↦ (h y * γ ‖y - ξ‖) • (y - ξ)) x ∂V.weight :=
        setIntegral_eq_integral_of_forall_compl_eq_zero fun x hxU ↦ by
          rw [tangentialDiv, fderiv_of_notMem_tsupport ℝ (hout x hxU)]
          simp
    _ = -∫ x, inner ℝ ((h x * γ ‖x - ξ‖) • (x - ξ)) (H x) ∂V.weight := hH.2 _ hX
    _ = _ := by
        rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := U) fun x hxU ↦ ?_]
        · simp_rw [real_inner_smul_left]
        · rw [hX0 x hxU, inner_zero_left]

/-- Simon 6.1–6.2 (pp. 100–101): if for every `n ≥ 1` and every `V` the weight `μ_V` is finite
on compact sets, `dim T_x V = n` for `μ_V`-a.e. `x` and `x ↦ p_{T_x V}` is `μ_V`-a.e. strongly
measurable, then `spt V ⊆ B_R(ξ)` whenever `n⁻¹|H(x)·(x - ξ)| < 1` in `ℝ^{n+ℓ} \ B_R(ξ)` and
`spt V` is compact (6.1), and `spt V ⊆ conv K` whenever `spt V` is compact and `V` is stationary
in `ℝ^{n+ℓ} \ K` with `K` compact (6.2). -/
theorem Submission.support_in_ball_convex_hull : (∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ), 0 < n → IsFiniteMeasureOnCompacts V.weight ∧ (∀ᵐ x ∂V.weight, Module.finrank ℝ (V.tangentSpace x) = n) ∧ AEStronglyMeasurable (fun x ↦ (V.tangentSpace x).starProjection) V.weight) → SupportInBall ∧ ConvexHullProperty := by
  intro hGF
  -- 6.1: the radial first variation identity (3.2–3.3, 3.14) for `X(x) = ζ(x) γ(r) (x - ξ)`,
  -- with `ζ ≡ 1` near `spt V` and `γ = 0` on `(-∞, R + ε]`, forces `γ(r) = 0` `μ_V`-a.e.
  have hBall : SupportInBall :=
    Submission.support_in_ball_of_radial_first_variation Submission.radial_first_variation hGF
  -- 6.2: `conv K` is the intersection of the closed balls containing `K`, and `V` has
  -- generalized mean curvature `0` outside each of them.
  exact ⟨hBall, Submission.convex_hull_property_of_support_in_ball hBall⟩

end

end GMT.Ch04
