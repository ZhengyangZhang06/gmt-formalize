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

/-- **Sobolev preliminaries (Simon Ch. 4, 5.7–5.9, Step 1).** If `μ_V` is finite on compact
sets, `x ↦ p_{T_x V}` is `μ_V`-a.e. strongly measurable, `U` is open, `H` is locally
`μ_V`-integrable on `U`, and `g ∈ C¹(U)` has compact support in `U`, then `g ∈ C¹(ℝ^{n+ℓ})`,
`∇^M g = 0` off `tsupport g`, and `|∇^M g|` and `g|H|` are `μ_V`-integrable. -/
theorem Submission.sobolev_energy_integrable : ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)) (H : Ambient n ℓ → Ambient n ℓ) (g : Ambient n ℓ → ℝ), IsFiniteMeasureOnCompacts V.weight → AEStronglyMeasurable (fun x ↦ (V.tangentSpace x).starProjection) V.weight → IsOpen U → LocallyIntegrableOn H U V.weight → ContDiffOn ℝ 1 g U → HasCompactSupport g → tsupport g ⊆ U → ContDiff ℝ 1 g ∧ (∀ x, x ∉ tsupport g → V.tangentialGradient g x = 0) ∧ Integrable (fun x ↦ ‖V.tangentialGradient g x‖) V.weight ∧ Integrable (fun x ↦ g x * ‖H x‖) V.weight := by
  intro n ℓ V U H g hfin hproj hU hH hg hgc hgU
  -- (1) `g` is `C¹` at points of the open set `U`, and `g = 0` near points off `tsupport g ⊆ U`.
  have hC1 : ContDiff ℝ 1 g := contDiff_iff_contDiffAt.2 fun x ↦ by
    by_cases hx : x ∈ U
    · exact hg.contDiffAt (hU.mem_nhds hx)
    · exact contDiffAt_const.congr_of_eventuallyEq
        (notMem_tsupport_iff_eventuallyEq.1 fun h ↦ hx (hgU h))
  -- (2) `∇g`, hence `∇^M g = p_{T_x V}(∇g)`, vanishes off `tsupport g`.
  have hgrad0 : ∀ x, x ∉ tsupport g → gradient g x = 0 := fun x hx ↦ by
    simp [gradient, fderiv_of_notMem_tsupport ℝ hx]
  have hzero : ∀ x, x ∉ tsupport g → V.tangentialGradient g x = 0 := fun x hx ↦ by
    simp [tangentialGradient, hgrad0 x hx]
  -- `∇g` is continuous with compact support, hence `μ_V`-integrable.
  have hgradc : Continuous (gradient g) :=
    (InnerProductSpace.toDual ℝ (Ambient n ℓ)).symm.continuous.comp
      (hC1.continuous_fderiv one_ne_zero)
  have hgradi : Integrable (gradient g) V.weight :=
    hgradc.integrable_of_hasCompactSupport (hgc.mono' fun x hx ↦ of_not_not fun h ↦ hx (hgrad0 x h))
  refine ⟨hC1, hzero, ?_, ?_⟩
  · -- (3) `∇^M g` is a.e. strongly measurable and `|∇^M g| ≤ |∇g|`.
    refine hgradi.mono ?_ (ae_of_all _ fun x ↦ ?_)
    · exact (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
        (hproj.prodMk hgradc.aestronglyMeasurable)).norm
    · rw [norm_norm]
      exact Submodule.norm_starProjection_apply_le _ _
  · -- (4) `H` is integrable on the compact set `tsupport g ⊆ U`, and `g|H|` vanishes off it.
    have hHK : IntegrableOn H (tsupport g) V.weight := hH.integrableOn_compact_subset hgU hgc
    exact (integrableOn_iff_integrable_of_support_subset fun x hx ↦
      subset_tsupport g (left_ne_zero_of_mul hx)).1
      (IntegrableOn.continuousOn_mul hC1.continuous.continuousOn hHK.norm hgc)
/-- **Ch. 4, opening of §5 (statement (1.1) of the Sobolev proof).** Assume `ApproxTangentAE`.
If `U` is open and `θ ≥ 1` `μ_V`-a.e. in `U`, then for `μ_V`-a.e. `x ∈ U` the density
`Θⁿ(μ_V, x)` exists and `Θⁿ(μ_V, x) ≥ 1`: for a representative `(M, θ)` of `V`,
`Θⁿ(μ_V, x) = θ(x) ≥ 1` for `Hⁿ`-a.e. `x ∈ M ∩ U`, and `μ_V = Hⁿ ⌞ θ ≪ Hⁿ ⌞ M`. -/
theorem Submission.sobolev_density_ge_one_ae : ApproxTangentAE → ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)), 0 < n → IsOpen U → V.MultiplicityGE 1 U → ∀ᵐ x ∂V.weight, x ∈ U → V.HasDensityAt x (V.density x) ∧ 1 ≤ V.density x := by
  intro hAT n ℓ V U hn hU hθ
  -- A representative `a = (M, θ)` of `V` with `θ ≥ 1` `Hⁿ`-a.e. on `M ∩ U`.
  obtain ⟨a, rfl, ha⟩ := hθ
  -- `Hⁿ ⌞ (M ∩ U) = (Hⁿ ⌞ M) ⌞ U` (`U` is Borel), so `x ∈ U → 1 ≤ θ x` `Hⁿ ⌞ M`-a.e.
  have hge : ∀ᵐ x ∂(μHE[n] : Measure (Ambient n ℓ)).restrict a.M, x ∈ U → 1 ≤ a.θ x := by
    rw [← ae_restrict_iff' hU.measurableSet, Measure.restrict_restrict hU.measurableSet,
      Set.inter_comm U a.M]
    exact ha
  -- `μ_V = (Hⁿ ⌞ M).withDensity θ ≪ Hⁿ ⌞ M`, so `Hⁿ ⌞ M`-a.e. statements hold `μ_V`-a.e.
  have hac : (mk a).weight ≪ (μHE[n] : Measure (Ambient n ℓ)).restrict a.M :=
    withDensity_absolutelyContinuous _ _
  refine hac.ae_le ?_
  -- `ApproxTangentAE`: `HasDensityAt x (θ x)` for `Hⁿ ⌞ M`-a.e. `x`.
  filter_upwards [hge, hAT n ℓ a hn] with x hx hT hxU
  -- The limit along `𝓝[>] 0` is unique, so `Θⁿ(μ_V, x) = θ x`.
  have hd : (mk a).density x = a.θ x := hT.2.2.limUnder_eq
  rw [hd]
  exact ⟨hT.2.2, hx hxU⟩
/-- **Corrected Simon Lemma 5.8 (good radius), `n ≥ 2`.** Let `f, k` be nondecreasing on `(0, ∞)`
with `0 ≤ f ≤ F` and `0 ≤ k`, such that `s⁻ⁿf(s) ≤ r⁻ⁿf(r) + ∫_{(s,r]} τ⁻ⁿk(τ) dτ` for
`0 < s ≤ r` and `limsup_{s↓0} s⁻ⁿf(s) ≥ 1`. Then `F > 0` and some `r ∈ (0, 2F^{1/n})` satisfies
`f(5r) ≤ 5ⁿF^{1/n}k(r)`. Otherwise, with `r₀ = 2F^{1/n}`, `S = sup_{[s,r₀]} τ⁻ⁿf(τ)` for a small
`s` with `s⁻ⁿf(s) > 2/3`, the substitution `u = 5τ` gives `S ≤ (7/5)2⁻ⁿ + (2/5)S`, so
`S ≤ 7/12`. (The printed lemma's lower bound `1 ≤ σ⁻ⁿf(σ)` for all `σ` contradicts `f ≤ F`.) -/
theorem Submission.sobolev_good_radius_calculus : ∀ (n : ℕ) (f k : ℝ → ℝ) (F : ℝ), 2 ≤ n →
    MonotoneOn f (Ioi 0) → MonotoneOn k (Ioi 0) → (∀ τ : ℝ, 0 < τ → 0 ≤ f τ ∧ f τ ≤ F) →
    (∀ τ : ℝ, 0 < τ → 0 ≤ k τ) →
    (∀ s r : ℝ, 0 < s → s ≤ r → f s / s ^ n ≤ f r / r ^ n + ∫ τ in Ioc s r, k τ / τ ^ n) →
    (∀ η : ℝ, η < 1 → ∃ᶠ s in 𝓝[>] (0 : ℝ), η < f s / s ^ n) →
    0 < F ∧ ∃ r : ℝ, 0 < r ∧ r < 2 * F ^ (n : ℝ)⁻¹ ∧ f (5 * r) ≤ 5 ^ n * F ^ (n : ℝ)⁻¹ * k r := by
  intro n f k F hn hf hk hfb hk0 ha hb
  -- Step 1: `F > 0`, from a radius `s₀ > 0` with `f(s₀)/s₀ⁿ > 0`.
  have hF : 0 < F := by
    obtain ⟨s₀, hpos, hs₀⟩ := ((hb 0 (by norm_num)).and_eventually self_mem_nhdsWithin).exists
    have hs₀' : (0 : ℝ) < s₀ := hs₀
    have h1 : 0 < f s₀ := (div_pos_iff_of_pos_right (pow_pos hs₀' n)).mp hpos
    linarith [(hfb s₀ hs₀').2]
  refine ⟨hF, ?_⟩
  -- Step 2: `r₀ = 2F^{1/n}`, so `r₀ⁿ = 2ⁿF` and `P = F/r₀ⁿ = 2⁻ⁿ ≤ 1/4`.
  obtain ⟨r₀, hr₀⟩ : ∃ r₀ : ℝ, r₀ = 2 * F ^ (n : ℝ)⁻¹ := ⟨_, rfl⟩
  have hFr : F ^ (n : ℝ)⁻¹ = r₀ / 2 := by rw [hr₀]; ring
  have hr₀pos : 0 < r₀ := by rw [hr₀]; positivity
  have hr₀n : r₀ ^ n = 2 ^ n * F := by
    rw [hr₀, mul_pow, Real.rpow_inv_natCast_pow hF.le (by omega)]
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = F / r₀ ^ n := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  have hP4 : P ≤ 1 / 4 := by
    have h4 : (4 : ℝ) ≤ 2 ^ n := by
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
    have hPe : P = 1 / 2 ^ n := by rw [hP, hr₀n]; field_simp
    rw [hPe]
    exact one_div_le_one_div_of_le (by norm_num) h4
  rw [hFr]
  -- Step 4: suppose no radius in `(0, r₀)` is good.
  by_contra hcon
  have hbad : ∀ τ : ℝ, 0 < τ → τ < r₀ → 5 ^ n * (r₀ / 2) * k τ < f (5 * τ) := by
    intro τ hτ hτr
    by_contra hle
    exact hcon ⟨τ, hτ, by linarith, not_lt.mp hle⟩
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = fun u ↦ f u / u ^ n := ⟨_, rfl⟩
  have hgv : ∀ u, g u = f u / u ^ n := fun u ↦ by rw [hg]
  have hg0 : ∀ u, 0 < u → 0 ≤ g u := fun u hu ↦ by
    rw [hgv]; exact div_nonneg (hfb u hu).1 (pow_pos hu n).le
  -- So `τ⁻ⁿk(τ) ≤ (2/r₀) g(5τ)` on `(0, r₀)`.
  have hkey : ∀ τ : ℝ, 0 < τ → τ < r₀ → k τ / τ ^ n ≤ 2 / r₀ * g (5 * τ) := by
    intro τ hτ hτr
    have h := hbad τ hτ hτr
    have hτn : 0 < τ ^ n := pow_pos hτ n
    rw [hgv, mul_pow, div_le_iff₀ hτn]
    have e : 2 / r₀ * (f (5 * τ) / (5 ^ n * τ ^ n)) * τ ^ n = 2 * f (5 * τ) / (r₀ * 5 ^ n) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    have e2 : k τ * (r₀ * 5 ^ n) = 2 * (5 ^ n * (r₀ / 2) * k τ) := by ring
    linarith
  -- Step 3: integrability on compact subintervals of `(0, ∞)`.
  have hint : ∀ φ : ℝ → ℝ, MonotoneOn φ (Ioi 0) → ∀ a b : ℝ, 0 < a → 0 < b →
      IntervalIntegrable (fun τ ↦ φ τ / τ ^ n) volume a b := by
    intro φ hφ a b ha hb
    have hsub : uIcc a b ⊆ Ioi 0 := by
      intro x hx
      rcases mem_uIcc.mp hx with h | h
      · exact lt_of_lt_of_le ha h.1
      · exact lt_of_lt_of_le hb h.1
    have h1 : IntervalIntegrable φ volume a b := (hφ.mono hsub).intervalIntegrable
    have h2 : ContinuousOn (fun τ : ℝ ↦ (τ ^ n)⁻¹) (uIcc a b) :=
      (continuous_pow n).continuousOn.inv₀ fun x hx ↦ pow_ne_zero n (ne_of_gt (hsub hx))
    simpa only [div_eq_mul_inv] using h1.mul_continuousOn h2
  have hgint : ∀ a b : ℝ, 0 < a → 0 < b → IntervalIntegrable g volume a b := by
    intro a b ha hb; rw [hg]; exact hint f hf a b ha hb
  -- Step 5: a radius `s ∈ (0, r₀)` with `f(s)/sⁿ > 2/3`.
  obtain ⟨s, hs2, hs⟩ :=
    ((hb (2 / 3) (by norm_num)).and_eventually (Ioo_mem_nhdsGT hr₀pos)).exists
  have hs0 : 0 < s := hs.1
  -- Step 6: `S = sup_{[s, r₀]} g`.
  have hbdd : BddAbove (g '' Icc s r₀) := by
    refine ⟨F / s ^ n, ?_⟩
    rintro _ ⟨τ, hτ, rfl⟩
    have hτ0 : 0 < τ := lt_of_lt_of_le hs.1 hτ.1
    rw [hgv]
    calc f τ / τ ^ n ≤ F / τ ^ n := by gcongr; exact (hfb τ hτ0).2
      _ ≤ F / s ^ n := by gcongr; exact hτ.1
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = sSup (g '' Icc s r₀) := ⟨_, rfl⟩
  have hgS : ∀ τ ∈ Icc s r₀, g τ ≤ S := fun τ hτ ↦ hS ▸ le_csSup hbdd (mem_image_of_mem g hτ)
  have hS23 : 2 / 3 < S := lt_of_lt_of_le (by rw [hgv]; exact hs2) (hgS s ⟨le_rfl, hs.2.le⟩)
  -- Step 10: `∫_s^{r₀} g ≤ r₀S` and `∫_{r₀}^{5r₀} g ≤ F r₀^{1-n} = r₀P`.
  have hJ1 : ∫ u in s..r₀, g u ≤ r₀ * S := by
    calc ∫ u in s..r₀, g u ≤ ∫ _ in s..r₀, S :=
          intervalIntegral.integral_mono_on hs.2.le (hgint s r₀ hs.1 hr₀pos)
            intervalIntegrable_const hgS
      _ = (r₀ - s) * S := by rw [intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ r₀ * S := by nlinarith [hs.1]
  have hJ2 : ∫ u in r₀..5 * r₀, g u ≤ r₀ * P := by
    have hFint : IntervalIntegrable (fun u ↦ F / u ^ n) volume r₀ (5 * r₀) :=
      hint (fun _ ↦ F) monotoneOn_const r₀ (5 * r₀) hr₀pos (by positivity)
    have hfun : (fun u : ℝ ↦ F / u ^ n) = fun u ↦ F * u ^ (-(n : ℤ)) := by
      funext u; rw [zpow_neg, zpow_natCast, div_eq_mul_inv]
    have hA : r₀ ^ (-(n : ℤ) + 1) = r₀ / r₀ ^ n := by
      rw [zpow_add₀ hr₀pos.ne', zpow_neg, zpow_natCast, zpow_one]; ring
    have hB : 0 < (5 * r₀) ^ (-(n : ℤ) + 1) := zpow_pos (by positivity) _
    have hD : ((-(n : ℤ) : ℤ) : ℝ) + 1 ≤ -1 := by
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      push_cast; linarith
    have hq : ((5 * r₀) ^ (-(n : ℤ) + 1) - r₀ / r₀ ^ n) / (((-(n : ℤ) : ℤ) : ℝ) + 1) ≤
        r₀ / r₀ ^ n := by
      rw [div_le_iff_of_neg (by linarith)]
      have : 0 < r₀ / r₀ ^ n := by positivity
      nlinarith
    calc ∫ u in r₀..5 * r₀, g u ≤ ∫ u in r₀..5 * r₀, F / u ^ n := by
          refine intervalIntegral.integral_mono_on (by linarith)
            (hgint r₀ (5 * r₀) hr₀pos (by positivity)) hFint fun u hu ↦ ?_
          have hu0 : 0 < u := lt_of_lt_of_le hr₀pos hu.1
          rw [hgv]; gcongr; exact (hfb u hu0).2
      _ = F * ∫ u in r₀..5 * r₀, u ^ (-(n : ℤ)) := by
          rw [hfun, intervalIntegral.integral_const_mul]
      _ = F * (((5 * r₀) ^ (-(n : ℤ) + 1) - r₀ ^ (-(n : ℤ) + 1)) / (((-(n : ℤ) : ℤ) : ℝ) + 1)) := by
          rw [integral_zpow (Or.inr ⟨by omega, notMem_uIcc_of_lt hr₀pos (by positivity)⟩)]
      _ ≤ F * (r₀ / r₀ ^ n) := by rw [hA]; gcongr
      _ = r₀ * P := by rw [hP]; ring
  -- Steps 7–11: for every `s' ∈ [s, r₀]`, `g(s') ≤ (7/5)P + (2/5)S`.
  have hstep : ∀ s' ∈ Icc s r₀, g s' ≤ 7 / 5 * P + 2 / 5 * S := by
    intro s' hs'
    have hs'pos : 0 < s' := lt_of_lt_of_le hs.1 hs'.1
    have h1 := ha s' r₀ hs'pos hs'.2
    rw [← intervalIntegral.integral_of_le hs'.2] at h1
    have h2 : f r₀ / r₀ ^ n ≤ P := by rw [hP]; gcongr; exact (hfb r₀ hr₀pos).2
    have h3 : ∫ τ in s'..r₀, k τ / τ ^ n ≤ ∫ τ in s'..r₀, 2 / r₀ * g (5 * τ) := by
      refine intervalIntegral.integral_mono_on_of_le_Ioo hs'.2 (hint k hk s' r₀ hs'pos hr₀pos)
        ?_ fun τ hτ ↦ hkey τ (hs'pos.trans hτ.1) hτ.2
      have h := (hgint (5 * s') (5 * r₀) (by positivity) (by positivity)).comp_mul_left (c := 5)
      rw [mul_div_cancel_left₀ _ (by norm_num : (5 : ℝ) ≠ 0),
        mul_div_cancel_left₀ _ (by norm_num : (5 : ℝ) ≠ 0)] at h
      exact h.const_mul (2 / r₀)
    have h4 : ∫ τ in s'..r₀, 2 / r₀ * g (5 * τ) =
        2 / r₀ * (5⁻¹ * ∫ u in 5 * s'..5 * r₀, g u) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_mul_left g (by norm_num : (5 : ℝ) ≠ 0), smul_eq_mul]
    have h5 : ∫ u in 5 * s'..5 * r₀, g u ≤ r₀ * S + r₀ * P := by
      have e1 := intervalIntegral.integral_add_adjacent_intervals
        (hgint s (5 * s') hs.1 (by positivity)) (hgint (5 * s') (5 * r₀) (by positivity) (by positivity))
      have e2 := intervalIntegral.integral_add_adjacent_intervals
        (hgint s r₀ hs.1 hr₀pos) (hgint r₀ (5 * r₀) hr₀pos (by positivity))
      have e3 : 0 ≤ ∫ u in s..5 * s', g u :=
        intervalIntegral.integral_nonneg (by linarith [hs'.1])
          fun u hu ↦ hg0 u (lt_of_lt_of_le hs.1 hu.1)
      linarith
    have h6 : 2 / r₀ * (5⁻¹ * ∫ u in 5 * s'..5 * r₀, g u) ≤ 2 / 5 * (S + P) := by
      calc 2 / r₀ * (5⁻¹ * ∫ u in 5 * s'..5 * r₀, g u) ≤ 2 / r₀ * (5⁻¹ * (r₀ * S + r₀ * P)) := by
            gcongr
        _ = 2 / 5 * (S + P) := by field_simp
    rw [hgv]
    linarith
  -- Step 12: `S ≤ (7/5)P + (2/5)S`, so `S ≤ (7/3)P ≤ 7/12 < 2/3`.
  have hSle : S ≤ 7 / 5 * P + 2 / 5 * S := by
    rw [hS]
    refine csSup_le ⟨g s, mem_image_of_mem g ⟨le_rfl, hs.2.le⟩⟩ ?_
    rintro _ ⟨τ, hτ, rfl⟩
    rw [← hS]
    exact hstep τ hτ
  linarith

/-- Simon 5.5 for `g ∈ C¹_c(U)`, `g ≥ 0`, at every pair of radii `0 < s ≤ r` (node
`monotonicity_inequality`): assuming the weighted monotonicity identity (W),
`s⁻ⁿ ∫_{B_s(ζ)} g dμ_V ≤ r⁻ⁿ ∫_{B_r(ζ)} g dμ_V + ∫_{(s,r]} τ⁻ⁿ ∫_{B_τ(ζ)} (|∇^M g| + g|H|) dμ_V dτ`.
The annulus term of (W) is nonnegative, and by Cauchy–Schwarz its radial term is bounded below
by `-∫_{(s,r]} τ⁻ⁿ Φ(τ) dτ`, where `Φ(τ) = ∫_{B_τ(ζ)} (|∇^M g| + g|H|) dμ_V` is monotone and
bounded (the energy is integrable by `sobolev_energy_integrable`). -/
theorem Submission.sobolev_monotonicity_inequality : (∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)) (H : Ambient n ℓ → Ambient n ℓ) (h : Ambient n ℓ → ℝ) (ξ : Ambient n ℓ) (σ ρ : ℝ), 0 < n → IsFiniteMeasureOnCompacts V.weight → (∀ᵐ x ∂V.weight, Module.finrank ℝ (V.tangentSpace x) = n) → AEStronglyMeasurable (fun x ↦ (V.tangentSpace x).starProjection) V.weight → IsOpen U → V.HasMeanCurvatureIn U H → ContDiffOn ℝ 1 h U → tsupport h ∩ closedBall ξ ρ ⊆ U → 0 < σ → σ ≤ ρ → IntegrableOn (fun τ ↦ (∫ x in closedBall ξ τ, inner ℝ (x - ξ) (V.tangentialGradient h x + h x • H x) ∂V.weight) / τ ^ (n + 1)) (Ioc σ ρ) ∧ IntegrableOn (fun x ↦ h x * (V.normalRadialSq ξ x / ‖x - ξ‖ ^ n)) (closedBall ξ ρ \ closedBall ξ σ) V.weight ∧ (∫ x in closedBall ξ ρ, h x ∂V.weight) / ρ ^ n - (∫ x in closedBall ξ σ, h x ∂V.weight) / σ ^ n = ∫ x in closedBall ξ ρ \ closedBall ξ σ, h x * (V.normalRadialSq ξ x / ‖x - ξ‖ ^ n) ∂V.weight + ∫ τ in Ioc σ ρ, (∫ x in closedBall ξ τ, inner ℝ (x - ξ) (V.tangentialGradient h x + h x • H x) ∂V.weight) / τ ^ (n + 1)) → ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)) (H : Ambient n ℓ → Ambient n ℓ) (g : Ambient n ℓ → ℝ) (ζ : Ambient n ℓ) (s r : ℝ), 0 < n → IsFiniteMeasureOnCompacts V.weight → (∀ᵐ x ∂V.weight, Module.finrank ℝ (V.tangentSpace x) = n) → AEStronglyMeasurable (fun x ↦ (V.tangentSpace x).starProjection) V.weight → IsOpen U → V.HasMeanCurvatureIn U H → ContDiffOn ℝ 1 g U → HasCompactSupport g → tsupport g ⊆ U → (∀ x, 0 ≤ g x) → 0 < s → s ≤ r → (∫ x in closedBall ζ s, g x ∂V.weight) / s ^ n ≤ (∫ x in closedBall ζ r, g x ∂V.weight) / r ^ n + ∫ τ in Ioc s r, (∫ x in closedBall ζ τ, (‖V.tangentialGradient g x‖ + g x * ‖H x‖) ∂V.weight) / τ ^ n := by
  intro hW n ℓ V U H g ζ s r hn hfin hdim hmeas hU hH hg hgc hgU hg0 hs hsr
  obtain ⟨hLint, -, hid⟩ :=
    hW n ℓ V U H g ζ s r hn hfin hdim hmeas hU hH hg (fun x hx ↦ hgU hx.1) hs hsr
  obtain ⟨-, -, hgrad, hgH⟩ :=
    Submission.sobolev_energy_integrable n ℓ V U H g hfin hmeas hU hH.1 hg hgc hgU
  have hφ : Integrable (fun x ↦ ‖V.tangentialGradient g x‖ + g x * ‖H x‖) V.weight :=
    hgrad.add hgH
  have hφ0 : ∀ x, 0 ≤ ‖V.tangentialGradient g x‖ + g x * ‖H x‖ := fun x ↦
    add_nonneg (norm_nonneg _) (mul_nonneg (hg0 x) (norm_nonneg _))
  -- `Φ(τ) = ∫_{B_τ(ζ)} (|∇^M g| + g|H|) dμ_V` is monotone, so `Φ(τ)/τⁿ` is integrable on `(s, r]`.
  have hΦmono : Monotone fun τ : ℝ ↦
      ∫ x in closedBall ζ τ, (‖V.tangentialGradient g x‖ + g x * ‖H x‖) ∂V.weight :=
    fun τ τ' hττ' ↦ setIntegral_mono_set hφ.integrableOn (ae_of_all _ hφ0)
      (Eventually.of_forall (closedBall_subset_closedBall hττ'))
  have hΦint : IntegrableOn (fun τ ↦ (∫ x in closedBall ζ τ,
      (‖V.tangentialGradient g x‖ + g x * ‖H x‖) ∂V.weight) / τ ^ n) (Ioc s r) := by
    refine Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
      (hΦmono.measurable.div (continuous_pow n).measurable).aestronglyMeasurable
      (M := (∫ x, (‖V.tangentialGradient g x‖ + g x * ‖H x‖) ∂V.weight) / s ^ n)
      (ae_restrict_of_forall_mem measurableSet_Ioc fun τ hτ ↦ ?_)
    have hτ0 : 0 < τ := hs.trans hτ.1
    have hΦ0 : 0 ≤ ∫ x in closedBall ζ τ, (‖V.tangentialGradient g x‖ + g x * ‖H x‖) ∂V.weight :=
      setIntegral_nonneg measurableSet_closedBall fun x _ ↦ hφ0 x
    rw [Real.norm_of_nonneg (div_nonneg hΦ0 (pow_nonneg hτ0.le n))]
    exact div_le_div₀ (integral_nonneg hφ0) (setIntegral_le_integral hφ (ae_of_all _ hφ0))
      (pow_pos hs n) (pow_le_pow_left₀ hs.le hτ.1.le n)
  -- The annulus term of (W) is nonnegative.
  have hA : 0 ≤ ∫ x in closedBall ζ r \ closedBall ζ s,
      g x * (V.normalRadialSq ζ x / ‖x - ζ‖ ^ n) ∂V.weight :=
    integral_nonneg fun x ↦ mul_nonneg (hg0 x)
      (div_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _)) (pow_nonneg (norm_nonneg _) n))
  -- Cauchy–Schwarz on `B_τ(ζ)`: `-L(τ)/τ^{n+1} ≤ |L(τ)|/τ^{n+1} ≤ Φ(τ)/τⁿ` for `τ ∈ (s, r]`.
  have hbound : ∀ τ ∈ Ioc s r,
      -((∫ x in closedBall ζ τ, inner ℝ (x - ζ) (V.tangentialGradient g x + g x • H x)
          ∂V.weight) / τ ^ (n + 1)) ≤
        (∫ x in closedBall ζ τ, (‖V.tangentialGradient g x‖ + g x * ‖H x‖) ∂V.weight) /
          τ ^ n := by
    intro τ hτ
    have hτ0 : 0 < τ := hs.trans hτ.1
    have hL : ‖∫ x in closedBall ζ τ, inner ℝ (x - ζ) (V.tangentialGradient g x + g x • H x)
        ∂V.weight‖ ≤
        τ * ∫ x in closedBall ζ τ, (‖V.tangentialGradient g x‖ + g x * ‖H x‖) ∂V.weight := by
      rw [← integral_const_mul]
      refine norm_integral_le_of_norm_le (hφ.const_mul τ).integrableOn
        (ae_restrict_of_forall_mem measurableSet_closedBall fun x hx ↦ ?_)
      calc ‖inner ℝ (x - ζ) (V.tangentialGradient g x + g x • H x)‖
          ≤ ‖x - ζ‖ * ‖V.tangentialGradient g x + g x • H x‖ := norm_inner_le_norm _ _
        _ ≤ τ * (‖V.tangentialGradient g x‖ + g x * ‖H x‖) := by
          refine mul_le_mul (mem_closedBall_iff_norm.mp hx)
            ((norm_add_le _ _).trans_eq ?_) (norm_nonneg _) hτ0.le
          rw [norm_smul, Real.norm_of_nonneg (hg0 x)]
    have hτn : 0 < τ ^ (n + 1) := pow_pos hτ0 _
    calc -((∫ x in closedBall ζ τ, inner ℝ (x - ζ) (V.tangentialGradient g x + g x • H x)
          ∂V.weight) / τ ^ (n + 1))
        ≤ ‖∫ x in closedBall ζ τ, inner ℝ (x - ζ) (V.tangentialGradient g x + g x • H x)
          ∂V.weight‖ / τ ^ (n + 1) := by
          rw [← neg_div, Real.norm_eq_abs]
          exact div_le_div_of_nonneg_right (neg_le_abs _) hτn.le
      _ ≤ (τ * ∫ x in closedBall ζ τ, (‖V.tangentialGradient g x‖ + g x * ‖H x‖) ∂V.weight) /
          τ ^ (n + 1) := div_le_div_of_nonneg_right hL hτn.le
      _ = (∫ x in closedBall ζ τ, (‖V.tangentialGradient g x‖ + g x * ‖H x‖) ∂V.weight) /
          τ ^ n := by rw [pow_succ', mul_div_mul_left _ _ hτ0.ne']
  -- Integrate the bound over `(s, r]` and rearrange (W).
  have hJ : ∫ τ in Ioc s r, -((∫ x in closedBall ζ τ, inner ℝ (x - ζ)
        (V.tangentialGradient g x + g x • H x) ∂V.weight) / τ ^ (n + 1)) ≤
      ∫ τ in Ioc s r, (∫ x in closedBall ζ τ, (‖V.tangentialGradient g x‖ + g x * ‖H x‖)
        ∂V.weight) / τ ^ n :=
    setIntegral_mono_on hLint.neg hΦint measurableSet_Ioc hbound
  rw [integral_neg] at hJ
  linarith

theorem main_theorem : ApproxTangentAE ∧ FirstVariationFormula ∧ StationaryIffVariational ∧ StationaryMonotonicity ∧ StationaryDensity ∧ CanonicalRepresentative ∧ BoundedCurvatureMonotonicity ∧ LogarithmicMonotonicityError ∧ LpMonotonicity ∧ LpDensity ∧ LpSupportRepresentation ∧ PoincareInequality ∧ SobolevInequality ∧ SupportInBall ∧ ConvexHullProperty ∧ ClassicalTangent := by sorry

end

end GMT.Ch04
