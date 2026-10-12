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

theorem main_theorem : ApproxTangentAE ∧ FirstVariationFormula ∧ StationaryIffVariational ∧ StationaryMonotonicity ∧ StationaryDensity ∧ CanonicalRepresentative ∧ BoundedCurvatureMonotonicity ∧ LogarithmicMonotonicityError ∧ LpMonotonicity ∧ LpDensity ∧ LpSupportRepresentation ∧ PoincareInequality ∧ SobolevInequality ∧ SupportInBall ∧ ConvexHullProperty ∧ ClassicalTangent := by sorry

end

end GMT.Ch04
