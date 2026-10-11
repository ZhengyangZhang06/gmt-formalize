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

set_option maxHeartbeats 400000 in
/-- **Poincaré inequality** (Simon Ch. 4, 5.1–5.6, with 4.10(1), 4.10(2) and 4.11), given
`ApproxTangentAE` and the structure facts of §1 for every varifold. For `n, α, Γ` we fix
`β ∈ (0, ½)` with `(1 - α²)(1 - β)⁻ⁿ ≤ 1 - α²/2` and `c = 8Γ/(α²ωₙ)` before `ℓ` and the data.
Bounded `H` is `L^{n+1}_loc`, so `Θⁿ(μ_V, ·)` exists on `U` (4.9) and is `≥ 1` on `spt V ∩ U`
(4.10(1)). The ball-average estimate 5.4 with `g ≡ 1` gives `μ_V(B_s(y)) ≤ 2Γsⁿ`, hence
`∫_{B_s(y)} |x - y|^{1-n} dμ_V ≤ 2nΓs` (4.10(2) for full balls). At `μ_V`-a.e. `ζ ∈ B_{βρ}(ξ)`
with `h(ζ) > t + ε`, the mean-value estimate for `ψ(h - t)` on `B_{(1-β)ρ}(ζ)` gives
`α²nωₙ/4 ≤ ∫ ψ'(h - t)|∇^M h||x - ζ|^{1-n} dμ_V`; integrating in `ζ` and `t` (Tonelli and the
layer-cake formula 4.11) gives `∫_{B_{βρ}(ξ)} (h - ε)⁺ dμ_V ≤ cρ ∫_{B_ρ(ξ)} |∇^M h| dμ_V`, and
`ε ↓ 0`. -/
theorem Submission.poincare_inequality : ApproxTangentAE → (∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ), 0 < n → IsFiniteMeasureOnCompacts V.weight ∧ (∀ᵐ x ∂V.weight, Module.finrank ℝ (V.tangentSpace x) = n) ∧ AEStronglyMeasurable (fun x ↦ (V.tangentSpace x).starProjection) V.weight) → PoincareInequality := by
  intro hAT hGF
  obtain ⟨-, -, -, hLpDensity⟩ := Submission.mean_curvature_monotonicity hGF
  obtain ⟨-, hLpSupp⟩ := Submission.canonical_representatives hAT hGF
  have hWMI := @Submission.weighted_monotonicity_identity
  intro n hn α Γ hα0 hα1 hΓ
  have hω : 0 < omega n := by
    unfold omega
    exact ENNReal.toReal_pos (Metric.measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨β, hβ0, hβ1, hβkey⟩ : ∃ β : ℝ, 0 < β ∧ β < 1 / 2 ∧
      (1 - α ^ 2) * ((1 - β) ^ n)⁻¹ ≤ 1 - α ^ 2 / 2 := by
    refine ⟨min (1 / 4) (α ^ 2 / (4 * n)), lt_min (by norm_num) (by positivity),
      (min_le_left _ _).trans_lt (by norm_num), ?_⟩
    set β := min (1 / 4 : ℝ) (α ^ 2 / (4 * n)) with hβ
    have hβ14 : β ≤ 1 / 4 := min_le_left _ _
    have hb : (1 : ℝ) - α ^ 2 / 4 ≤ (1 - β) ^ n := by
      have h1 := one_add_mul_le_pow (a := -β) (by linarith) n
      have h2 : (n : ℝ) * β ≤ α ^ 2 / 4 := by
        have : β ≤ α ^ 2 / (4 * n) := min_le_right _ _
        calc (n : ℝ) * β ≤ n * (α ^ 2 / (4 * n)) := by gcongr
          _ = α ^ 2 / 4 := by field_simp
      calc (1 : ℝ) - α ^ 2 / 4 ≤ 1 + n * (-β) := by linarith
        _ ≤ (1 + -β) ^ n := h1
        _ = (1 - β) ^ n := by ring
    have hα2 : α ^ 2 < 1 := pow_lt_one₀ hα0.le hα1 two_ne_zero
    have hpos : (0 : ℝ) < 1 - α ^ 2 / 4 := by linarith
    have hpos' : (0 : ℝ) < (1 - β) ^ n := hpos.trans_le hb
    rw [← div_eq_mul_inv, div_le_iff₀ hpos']
    calc 1 - α ^ 2 ≤ (1 - α ^ 2 / 2) * (1 - α ^ 2 / 4) := by
          linarith [sq_nonneg α, sq_nonneg (α ^ 2)]
      _ ≤ (1 - α ^ 2 / 2) * (1 - β) ^ n := mul_le_mul_of_nonneg_left hb (by linarith)
  refine ⟨β, 8 * Γ / (α ^ 2 * omega n), hβ0, hβ1, by positivity, ?_⟩
  intro ℓ V U H Λ h ξ ρ hU hH hHΛ hθ hh hh0 hρ hball hmeas hexp hΓρ
  classical
  obtain ⟨hFV1, hFV2, hFV3⟩ := hGF n ℓ V hn
  set μ := V.weight with hμ
  set Λ' := max Λ 0 with hΛ'
  have hΛ'0 : 0 ≤ Λ' := le_max_right _ _
  have hHΛ' : ∀ᵐ x ∂μ, x ∈ U → ‖H x‖ ≤ Λ' :=
    hHΛ.mono fun x hx hxU => (hx hxU).trans (le_max_left _ _)
  have hexp' : Real.exp (Λ' * ρ) ≤ 1 + α := by
    rcases le_total 0 Λ with hΛ0 | hΛ0
    · rw [hΛ', max_eq_left hΛ0]; exact hexp
    · rw [hΛ', max_eq_right hΛ0, zero_mul, Real.exp_zero]; linarith
  have hLp : V.IsLocallyLp U H ((n : ℝ) + 1) := by
    intro K hK hKU
    have : IsFiniteMeasure (μ.restrict K) := ⟨by
      rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
    have hint : IntegrableOn H K μ := hH.1.integrableOn_compact_subset hKU hK
    refine MemLp.of_bound hint.aestronglyMeasurable Λ' ?_
    rw [ae_restrict_iff' hK.measurableSet]
    exact hHΛ'.mono fun x hx hxK => hx (hKU hxK)
  have hn1 : (n : ℝ) < (n : ℝ) + 1 := by linarith
  have hDens : ∀ ζ ∈ U, V.HasDensityAt ζ (V.density ζ) :=
    (hLpDensity n ℓ V U H _ hn hU hH hn1 hLp).1
  have hΘ : ∀ x ∈ V.support ∩ U, 1 ≤ V.density x :=
    (hLpSupp n ℓ V U H _ hn hU hH hn1 hLp hθ).1
  have hBU : closedBall ξ ρ ⊆ U :=
    (closedBall_subset_closedBall (by linarith : ρ ≤ 2 * ρ)).trans hball
  -- growth bound (5.4 with g ≡ 1)
  have hgrowth : ∀ y ∈ closedBall ξ ρ, ∀ s : ℝ, 0 < s → s ≤ ρ →
      μ (closedBall y s) ≤ ENNReal.ofReal (2 * Γ * s ^ n) := by
    intro y hy s hs hsρ
    have hyξ : dist y ξ ≤ ρ := mem_closedBall.1 hy
    have hy2 : closedBall y ρ ⊆ closedBall ξ (2 * ρ) := closedBall_subset_closedBall' (by linarith)
    have hyball : closedBall y ρ ⊆ U := hy2.trans hball
    have hzero : ∀ x, V.tangentialGradient (fun _ => (1 : ℝ)) x = 0 := by
      intro x
      simp [RectifiableVarifold.tangentialGradient, gradient_fun_const]
    have key := Submission.bounded_curvature_ball_average_estimate hWMI n ℓ V U H Λ'
      (fun _ => 1) y ρ s hn hFV1 hFV2 hFV3 hU hH hΛ'0 hHΛ' contDiffOn_const
      (fun _ _ => zero_le_one) hyball hs hsρ (by simp [hzero])
    simp only [hzero, norm_zero, zero_mul, integral_zero, mul_zero, add_zero,
      setIntegral_const, smul_eq_mul, mul_one] at key
    have hfin : μ (closedBall y s) ≠ ⊤ := (isCompact_closedBall y s).measure_lt_top.ne
    have hfin2 : μ (closedBall ξ (2 * ρ)) ≠ ⊤ := (isCompact_closedBall ξ (2 * ρ)).measure_lt_top.ne
    have h1 : μ.real (closedBall y ρ) ≤ Γ * ρ ^ n :=
      (measureReal_mono hy2 hfin2).trans hΓρ
    have h2 : Real.exp (Λ' * (ρ - s)) ≤ 1 + α :=
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith) hΛ'0)).trans hexp'
    have hsn : (0 : ℝ) < s ^ n := pow_pos hs n
    have hρn : (0 : ℝ) < ρ ^ n := pow_pos hρ n
    have h3 : μ.real (closedBall y s) ≤ Real.exp (Λ' * (ρ - s)) * (μ.real (closedBall y ρ) / ρ ^ n) * s ^ n := by
      rwa [div_le_iff₀ hsn] at key
    have h4 : μ.real (closedBall y ρ) / ρ ^ n ≤ Γ := by rwa [div_le_iff₀ hρn]
    have h5 : 0 ≤ μ.real (closedBall y ρ) / ρ ^ n := by positivity
    rw [← ENNReal.ofReal_toReal hfin]
    apply ENNReal.ofReal_le_ofReal
    change μ.real (closedBall y s) ≤ 2 * Γ * s ^ n
    calc μ.real (closedBall y s) ≤ Real.exp (Λ' * (ρ - s)) * (μ.real (closedBall y ρ) / ρ ^ n) * s ^ n := h3
      _ ≤ (1 + α) * Γ * s ^ n := by gcongr
      _ ≤ 2 * Γ * s ^ n := by gcongr; linarith
  have hkernel : ∀ x ∈ closedBall ξ ρ, ∀ s : ℝ, 0 < s → s ≤ ρ →
      ∫⁻ z in closedBall x s, ENNReal.ofReal (‖z - x‖ ^ (1 - (n : ℝ))) ∂μ ≤
        ENNReal.ofReal (n * (2 * Γ) * s) := fun x hx =>
    Submission.closedBall_rpow_kernel_lintegral_le_of_growth μ n x ρ (2 * Γ) hn (hgrowth x hx)
  set c := 8 * Γ / (α ^ 2 * omega n) with hc
  set A := closedBall ξ (β * ρ) with hA
  set B := closedBall ξ ρ with hB
  set r₀ := (1 - β) * ρ with hr₀
  have hr₀pos : 0 < r₀ := mul_pos (by linarith) hρ
  have hr₀ρ : r₀ ≤ ρ := by rw [hr₀]; exact mul_le_of_le_one_left hρ.le (by linarith)
  have hAB : A ⊆ B := closedBall_subset_closedBall (mul_le_of_le_one_left hρ.le (by linarith))
  have hball₀ : ∀ ζ ∈ A, closedBall ζ r₀ ⊆ B := fun ζ hζ =>
    closedBall_subset_closedBall' (by rw [mem_closedBall] at hζ; linarith)
  have hTGmeas_of : ∀ f : Ambient n ℓ → ℝ, AEStronglyMeasurable (V.tangentialGradient f) μ := by
    intro f
    have hgm : Measurable (gradient f) :=
      (InnerProductSpace.toDual ℝ (Ambient n ℓ)).symm.continuous.measurable.comp (measurable_fderiv ℝ f)
    exact (ContinuousLinearMap.id ℝ (Ambient n ℓ →L[ℝ] Ambient n ℓ)).aestronglyMeasurable_comp₂
      hFV3 hgm.aestronglyMeasurable
  have hgradcont : ContinuousOn (gradient h) U :=
    (InnerProductSpace.toDual ℝ (Ambient n ℓ)).symm.continuous.comp_continuousOn
      (hh.continuousOn_fderiv_of_isOpen hU le_rfl)
  obtain ⟨Cg, hCg⟩ : ∃ C, ∀ x ∈ B, ‖gradient h x‖ ≤ C :=
    (isCompact_closedBall ξ ρ).exists_bound_of_continuousOn (hgradcont.mono hBU)
  have hTGbound : ∀ x ∈ B, ‖V.tangentialGradient h x‖ ≤ Cg := fun x hx =>
    (Submodule.norm_starProjection_apply_le _ _).trans (hCg x hx)
  have : IsFiniteMeasure (μ.restrict B) := ⟨by
    rw [Measure.restrict_apply_univ]; exact (isCompact_closedBall ξ ρ).measure_lt_top⟩
  have hTGint : IntegrableOn (fun x => ‖V.tangentialGradient h x‖) B μ :=
    Integrable.of_bound (hTGmeas_of h).norm.restrict Cg
      ((ae_restrict_iff' measurableSet_closedBall).2 (Eventually.of_forall fun x hx => by
        rw [norm_norm]; exact hTGbound x hx))
  have hSmeas : MeasurableSet {x | x ∈ closedBall ξ ρ ∧ 0 < h x} := by
    have : {x | x ∈ closedBall ξ ρ ∧ 0 < h x} = closedBall ξ ρ ∩ (U ∩ h ⁻¹' Ioi 0) := by
      ext x; constructor
      · rintro ⟨hx1, hx2⟩; exact ⟨hx1, hBU hx1, hx2⟩
      · rintro ⟨hx1, -, hx2⟩; exact ⟨hx1, hx2⟩
    rw [this]
    exact measurableSet_closedBall.inter
      (hh.continuousOn.isOpen_inter_preimage hU isOpen_Ioi).measurableSet
  have main : ∀ ε : ℝ, 0 < ε → ∫ x in A, h x ∂μ ≤
      c * ρ * ∫ x in B, ‖V.tangentialGradient h x‖ ∂μ + ε * μ.real A := by
    intro ε hε
    obtain ⟨ψ, hψC, hψ01, hψ0, hψ1, hψ'0, ⟨M, hM⟩, hψint⟩ :=
      Submission.smooth_step_truncation_exists ε hε
    set h' : Ambient n ℓ → ℝ := U.piecewise h 0 with hh'
    have hh'meas : Measurable h' :=
      hh.continuousOn.measurable_piecewise continuousOn_const hU.measurableSet
    have hh'eq : ∀ x ∈ U, h' x = h x := fun x hx => Set.piecewise_eq_of_mem _ _ _ hx
    set G0 : Ambient n ℓ → ℝ≥0∞ := fun x => ENNReal.ofReal ‖V.tangentialGradient h x‖ with hG0
    have hG0meas : AEMeasurable G0 (μ.restrict B) :=
      (ENNReal.measurable_ofReal.comp_aemeasurable (hTGmeas_of h).norm.aemeasurable).restrict
    set G' := hG0meas.mk G0 with hG'
    have hG'meas : Measurable G' := hG0meas.measurable_mk
    have hG'eq : G0 =ᵐ[μ.restrict B] G' := hG0meas.ae_eq_mk
    set φ : ℝ → Ambient n ℓ → ℝ≥0∞ := fun t x => ENNReal.ofReal (deriv ψ (h' x - t)) with hφ
    have hφmeas : Measurable (Function.uncurry φ) :=
      ENNReal.measurable_ofReal.comp ((measurable_deriv ψ).comp
        ((hh'meas.comp measurable_snd).sub measurable_fst))
    set k : Ambient n ℓ → Ambient n ℓ → ℝ≥0∞ := fun x ζ =>
      (closedBall x r₀).indicator (fun z => ENNReal.ofReal (‖z - x‖ ^ (1 - (n : ℝ)))) ζ with hk
    have hkmeas : Measurable (Function.uncurry k) := by
      have : Function.uncurry k = {p : Ambient n ℓ × Ambient n ℓ | dist p.2 p.1 ≤ r₀}.indicator
          (fun p => ENNReal.ofReal (‖p.2 - p.1‖ ^ (1 - (n : ℝ)))) := by
        ext ⟨x, ζ⟩
        simp only [Function.uncurry_apply_pair, hk, Set.indicator, mem_closedBall, Set.mem_ofPred_eq]
      rw [this]
      refine Measurable.indicator ?_ (measurableSet_le (by fun_prop) measurable_const)
      exact ENNReal.measurable_ofReal.comp ((measurable_snd.sub measurable_fst).norm.pow_const _)
    set κ : ℝ≥0∞ := ENNReal.ofReal (α ^ 2 * n * omega n / 4) with hκ
    set L : ℝ≥0∞ := ENNReal.ofReal (n * (2 * Γ) * ρ) with hL
    have hi : ∀ x ∈ B, ∫⁻ t in Ioi 0, φ t x ≤ 1 := fun x _ => hψint (h' x)
    have hii : ∀ x ∈ B, ∫⁻ ζ in A, k x ζ ∂μ ≤ L := by
      intro x hx
      calc ∫⁻ ζ in A, k x ζ ∂μ
          = ∫⁻ ζ in A ∩ closedBall x r₀, ENNReal.ofReal (‖ζ - x‖ ^ (1 - (n : ℝ))) ∂μ := by
            simp only [hk]
            rw [lintegral_indicator measurableSet_closedBall, Measure.restrict_restrict measurableSet_closedBall,
              Set.inter_comm]
        _ ≤ ∫⁻ ζ in closedBall x r₀, ENNReal.ofReal (‖ζ - x‖ ^ (1 - (n : ℝ))) ∂μ :=
            lintegral_mono_set Set.inter_subset_right
        _ ≤ ENNReal.ofReal (n * (2 * Γ) * r₀) := hkernel x hx r₀ hr₀pos hr₀ρ
        _ ≤ L := ENNReal.ofReal_le_ofReal (by gcongr)
    have hiii : ∀ t : ℝ, 0 < t → ∀ᵐ ζ ∂μ, ζ ∈ A → t + ε < h' ζ →
        κ ≤ ∫⁻ x in B, φ t x * G' x * k x ζ ∂μ := by
      intro t ht
      filter_upwards [Measure.support_mem_ae (μ := μ)] with ζ hζsupp hζA hζh
      have hζB : ζ ∈ B := hAB hζA
      have hζU : ζ ∈ U := hBU hζB
      rw [hh'eq ζ hζU] at hζh
      have hb0 : closedBall ζ r₀ ⊆ B := hball₀ ζ hζA
      have hb0U : closedBall ζ r₀ ⊆ U := hb0.trans hBU
      set g : Ambient n ℓ → ℝ := fun y => ψ (h y - t) with hg
      have hgC : ContDiffOn ℝ 1 g U := hψC.comp_contDiffOn (hh.sub contDiffOn_const)
      have hg0 : ∀ x ∈ U, 0 ≤ g x := fun x _ => (hψ01 _).1
      have hchain : ∀ x ∈ U, V.tangentialGradient g x =
          deriv ψ (h x - t) • V.tangentialGradient h x := by
        intro x hx
        have hdx : DifferentiableAt ℝ h x :=
          (hh.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hx)
        have := Submission.tangentialGradient_comp_of_differentiableAt n ℓ V (fun y => h y - t) ψ x
          (hdx.sub_const t) (hψC.differentiable one_ne_zero _)
        rw [this]
        congr 1
        simp only [RectifiableVarifold.tangentialGradient, gradient, fderiv_sub_const]
      have hnormchain : ∀ x ∈ U, ‖V.tangentialGradient g x‖ =
          deriv ψ (h x - t) * ‖V.tangentialGradient h x‖ := by
        intro x hx
        rw [hchain x hx, norm_smul, Real.norm_of_nonneg (hψ'0 _)]
      have hkerfin := hkernel ζ hζB r₀ hr₀pos hr₀ρ
      have hkermeas : AEStronglyMeasurable (fun x => ‖x - ζ‖ ^ (1 - (n : ℝ))) (μ.restrict (closedBall ζ r₀)) :=
        ((measurable_id.sub measurable_const).norm.pow_const _).aestronglyMeasurable
      have hkerint : IntegrableOn (fun x => ‖x - ζ‖ ^ (1 - (n : ℝ))) (closedBall ζ r₀) μ := by
        refine (lintegral_ofReal_ne_top_iff_integrable hkermeas
          (Eventually.of_forall fun x => by positivity)).1 ?_
        exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hkerfin
      have hgint : IntegrableOn (fun x => ‖V.tangentialGradient g x‖ * ‖x - ζ‖ ^ (1 - (n : ℝ)))
          (closedBall ζ r₀) μ := by
        refine Integrable.bdd_mul (c := M * Cg) hkerint (hTGmeas_of g).norm.restrict ?_
        refine (ae_restrict_iff' measurableSet_closedBall).2 (Eventually.of_forall fun x hx => ?_)
        rw [norm_norm, hnormchain x (hb0U hx)]
        have hM0 : 0 ≤ M := (hψ'0 0).trans (hM 0)
        exact mul_le_mul (hM _) (hTGbound x (hb0 hx)) (norm_nonneg _) hM0
      have hmv := Submission.density_point_mean_value_estimate hWMI n ℓ V U H Λ' g ζ r₀
        (V.density ζ) hn hFV1 hFV2 hFV3 hU hH hΛ'0 hHΛ' hgC hg0 hr₀pos hb0U (hDens ζ hζU)
        (hΘ ζ ⟨hζsupp, hζU⟩) hgint
      have hgζ : g ζ = 1 := hψ1 _ (by linarith)
      rw [hgζ, mul_one] at hmv
      -- the average term
      have hgcont : ContinuousOn g U := hgC.continuousOn
      have : IsFiniteMeasure (μ.restrict (closedBall ζ r₀)) := ⟨by
        rw [Measure.restrict_apply_univ]; exact (isCompact_closedBall ζ r₀).measure_lt_top⟩
      have hgintB : IntegrableOn g (closedBall ζ r₀) μ := by
        refine Integrable.of_bound ((hgcont.mono hb0U).aestronglyMeasurable measurableSet_closedBall) 1
          (Eventually.of_forall fun x => ?_)
        rw [Real.norm_of_nonneg (hψ01 _).1]; exact (hψ01 _).2
      set S := {x | x ∈ closedBall ξ ρ ∧ 0 < h x} with hS
      have hSfin : μ S ≠ ⊤ := ne_top_of_le_ne_top (isCompact_closedBall ξ ρ).measure_lt_top.ne
        (measure_mono fun x hx => hx.1)
      have hX : ∫ x in closedBall ζ r₀, g x ∂μ ≤ (1 - α) * omega n * ρ ^ n := by
        have hind : IntegrableOn (S.indicator (fun _ => (1 : ℝ))) (closedBall ζ r₀) μ :=
          (integrable_const (1 : ℝ)).indicator hSmeas
        calc ∫ x in closedBall ζ r₀, g x ∂μ
            ≤ ∫ x in closedBall ζ r₀, S.indicator (fun _ => (1 : ℝ)) x ∂μ := by
              refine setIntegral_mono_on hgintB hind measurableSet_closedBall fun x hx => ?_
              by_cases hxS : x ∈ S
              · rw [Set.indicator_of_mem hxS]; exact (hψ01 _).2
              · rw [Set.indicator_of_notMem hxS]
                have hxB : x ∈ closedBall ξ ρ := hb0 hx
                have : ¬ 0 < h x := fun hpos => hxS ⟨hxB, hpos⟩
                exact (hψ0 _ (by linarith [not_lt.1 this])).le
          _ = μ.real (closedBall ζ r₀ ∩ S) := by
              rw [setIntegral_indicator hSmeas, setIntegral_const, smul_eq_mul, mul_one]
          _ ≤ μ.real S := measureReal_mono Set.inter_subset_right hSfin
          _ ≤ (1 - α) * omega n * ρ ^ n := hmeas
      set I := ∫ x in closedBall ζ r₀, ‖V.tangentialGradient g x‖ * ‖x - ζ‖ ^ (1 - (n : ℝ)) ∂μ with hI
      have hI0 : 0 ≤ I := setIntegral_nonneg measurableSet_closedBall fun x _ => by positivity
      have hX0 : 0 ≤ ∫ x in closedBall ζ r₀, g x ∂μ :=
        setIntegral_nonneg measurableSet_closedBall fun x hx => hg0 x (hb0U hx)
      have hE : Real.exp (Λ' * r₀) ≤ 1 + α :=
        (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hr₀ρ hΛ'0)).trans hexp'
      have hr₀n : r₀ ^ n = (1 - β) ^ n * ρ ^ n := by rw [hr₀, mul_pow]
      have h1β : (0 : ℝ) < (1 - β) ^ n := pow_pos (by linarith) n
      have hρn : (0 : ℝ) < ρ ^ n := pow_pos hρ n
      have hXr : (∫ x in closedBall ζ r₀, g x ∂μ) / r₀ ^ n ≤ (1 - α) * omega n * ((1 - β) ^ n)⁻¹ := by
        rw [div_le_iff₀ (by rw [hr₀n]; positivity), hr₀n]
        calc ∫ x in closedBall ζ r₀, g x ∂μ ≤ (1 - α) * omega n * ρ ^ n := hX
          _ = (1 - α) * omega n * ((1 - β) ^ n)⁻¹ * ((1 - β) ^ n * ρ ^ n) := by
            field_simp
      have hIn : 0 ≤ (n : ℝ)⁻¹ * I := by positivity
      have hbr0 : 0 ≤ (∫ x in closedBall ζ r₀, g x ∂μ) / r₀ ^ n + (n : ℝ)⁻¹ * I := by positivity
      have hstep : omega n ≤ (1 + α) * ((1 - α) * omega n * ((1 - β) ^ n)⁻¹ + (n : ℝ)⁻¹ * I) :=
        calc omega n ≤ Real.exp (Λ' * r₀) * ((∫ x in closedBall ζ r₀, g x ∂μ) / r₀ ^ n + (n : ℝ)⁻¹ * I) := hmv
          _ ≤ (1 + α) * ((∫ x in closedBall ζ r₀, g x ∂μ) / r₀ ^ n + (n : ℝ)⁻¹ * I) :=
            mul_le_mul_of_nonneg_right hE hbr0
          _ ≤ (1 + α) * ((1 - α) * omega n * ((1 - β) ^ n)⁻¹ + (n : ℝ)⁻¹ * I) := by
            gcongr
      have hkeyω : (1 + α) * ((1 - α) * omega n * ((1 - β) ^ n)⁻¹) ≤ (1 - α ^ 2 / 2) * omega n := by
        have : (1 + α) * ((1 - α) * omega n * ((1 - β) ^ n)⁻¹) =
            ((1 - α ^ 2) * ((1 - β) ^ n)⁻¹) * omega n := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_right hβkey hω.le
      have hIbound : α ^ 2 * n * omega n / 4 ≤ I := by
        have h2 : α ^ 2 / 2 * omega n ≤ (1 + α) * ((n : ℝ)⁻¹ * I) := by
          rw [mul_add] at hstep
          linarith
        have h3 : (1 + α) * ((n : ℝ)⁻¹ * I) ≤ 2 * ((n : ℝ)⁻¹ * I) :=
          mul_le_mul_of_nonneg_right (by linarith) hIn
        have h4 : α ^ 2 / 2 * omega n ≤ 2 * ((n : ℝ)⁻¹ * I) := h2.trans h3
        have h5 : α ^ 2 / 2 * omega n * n ≤ 2 * I := by
          have := mul_le_mul_of_nonneg_right h4 hn'.le
          calc α ^ 2 / 2 * omega n * n ≤ 2 * ((n : ℝ)⁻¹ * I) * n := this
            _ = 2 * I := by field_simp
        linarith
      -- convert to the lintegral form
      have hconv : ∫⁻ x in B, φ t x * G' x * k x ζ ∂μ = ENNReal.ofReal I := by
        calc ∫⁻ x in B, φ t x * G' x * k x ζ ∂μ = ∫⁻ x in B, φ t x * G0 x * k x ζ ∂μ := by
              refine lintegral_congr_ae ?_
              filter_upwards [hG'eq] with x hx
              rw [hx]
          _ = ∫⁻ x in B, (closedBall ζ r₀).indicator
                (fun x => ENNReal.ofReal (‖V.tangentialGradient g x‖ * ‖x - ζ‖ ^ (1 - (n : ℝ)))) x ∂μ := by
              refine setLIntegral_congr_fun measurableSet_closedBall fun x hxB => ?_
              by_cases hx : x ∈ closedBall ζ r₀
              · have hζx : ζ ∈ closedBall x r₀ := mem_closedBall_comm.1 hx
                have hxU : x ∈ U := hb0U hx
                rw [Set.indicator_of_mem hx]
                simp only [hk, hφ, hG0, Set.indicator_of_mem hζx, hh'eq x hxU, norm_sub_rev ζ x,
                  hnormchain x hxU]
                rw [← ENNReal.ofReal_mul (hψ'0 _), ← ENNReal.ofReal_mul (mul_nonneg (hψ'0 _) (norm_nonneg _))]
              · have hζx : ζ ∉ closedBall x r₀ := fun h' => hx (mem_closedBall_comm.1 h')
                rw [Set.indicator_of_notMem hx]
                simp only [hk, Set.indicator_of_notMem hζx, mul_zero]
          _ = ∫⁻ x in closedBall ζ r₀, ENNReal.ofReal (‖V.tangentialGradient g x‖ * ‖x - ζ‖ ^ (1 - (n : ℝ))) ∂μ := by
              rw [lintegral_indicator measurableSet_closedBall, Measure.restrict_restrict measurableSet_closedBall,
                Set.inter_eq_left.2 hb0]
          _ = ENNReal.ofReal I := by
              rw [hI, ofReal_integral_eq_lintegral_ofReal hgint
                (Eventually.of_forall fun x => by positivity)]
      rw [hconv]
      exact ENNReal.ofReal_le_ofReal hIbound
    have hK4 := Submission.layer_cake_tonelli_truncation_bound μ A B h' φ G' k κ L ε
      measurableSet_closedBall measurableSet_closedBall hh'meas hφmeas hG'meas hkmeas hi hii hiii
    have hAU : A ⊆ U := hAB.trans hBU
    have hhintA : IntegrableOn h A μ :=
      (hh.continuousOn.mono hAU).integrableOn_compact (isCompact_closedBall ξ (β * ρ))
    have hposint : IntegrableOn (fun x => max (h x - ε) 0) A μ :=
      (hhintA.sub (integrableOn_const (isCompact_closedBall ξ (β * ρ)).measure_lt_top.ne)).pos_part
    have hYeq : ∫⁻ x in B, G' x ∂μ = ENNReal.ofReal (∫ x in B, ‖V.tangentialGradient h x‖ ∂μ) := by
      rw [lintegral_congr_ae hG'eq.symm, ofReal_integral_eq_lintegral_ofReal hTGint
        (Eventually.of_forall fun x => norm_nonneg _)]
    have hXeq : ∫⁻ ζ in A, ENNReal.ofReal (h' ζ - ε) ∂μ = ENNReal.ofReal (∫ x in A, max (h x - ε) 0 ∂μ) := by
      rw [ofReal_integral_eq_lintegral_ofReal hposint (Eventually.of_forall fun x => le_max_right _ _)]
      refine setLIntegral_congr_fun measurableSet_closedBall fun x hx => ?_
      rw [hh'eq x (hAU hx)]
      rcases le_total 0 (h x - ε) with hpos | hneg
      · rw [max_eq_left hpos]
      · rw [max_eq_right hneg, ENNReal.ofReal_of_nonpos hneg, ENNReal.ofReal_zero]
    rw [hXeq, hYeq, hκ, hL, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)] at hK4
    have hK4' := (ENNReal.ofReal_le_ofReal_iff (by
      have := setIntegral_nonneg (μ := μ) measurableSet_closedBall
        (fun x (_ : x ∈ B) => norm_nonneg (V.tangentialGradient h x))
      positivity)).1 hK4
    set X := ∫ x in A, max (h x - ε) 0 ∂μ with hXdef
    set Y := ∫ x in B, ‖V.tangentialGradient h x‖ ∂μ with hYdef
    have hκpos : 0 < α ^ 2 * n * omega n / 4 := by positivity
    have hXY : X ≤ c * ρ * Y := by
      have : X = (α ^ 2 * n * omega n / 4 * X) / (α ^ 2 * n * omega n / 4) := by
        field_simp
      rw [this, div_le_iff₀ hκpos]
      calc α ^ 2 * n * omega n / 4 * X ≤ n * (2 * Γ) * ρ * Y := hK4'
        _ = c * ρ * Y * (α ^ 2 * n * omega n / 4) := by
          rw [hc]; field_simp; ring
    have hAle : ∫ x in A, h x ∂μ ≤ X + ε * μ.real A := by
      have h1 : ∫ x in A, h x ∂μ ≤ ∫ x in A, (max (h x - ε) 0 + ε) ∂μ :=
        setIntegral_mono_on hhintA (hposint.add (integrableOn_const
          (isCompact_closedBall ξ (β * ρ)).measure_lt_top.ne)) measurableSet_closedBall
          fun x _ => by linarith [le_max_left (h x - ε) 0]
      rw [integral_add hposint (integrableOn_const (isCompact_closedBall ξ (β * ρ)).measure_lt_top.ne),
        setIntegral_const, smul_eq_mul, mul_comm (μ.real A)] at h1
      exact h1
    linarith
  apply le_of_forall_pos_le_add
  intro ε hε
  have hA0 : 0 ≤ μ.real A := measureReal_nonneg
  have := main (ε / (μ.real A + 1)) (by positivity)
  calc ∫ x in A, h x ∂μ ≤ c * ρ * ∫ x in B, ‖V.tangentialGradient h x‖ ∂μ +
        ε / (μ.real A + 1) * μ.real A := this
    _ ≤ c * ρ * ∫ x in B, ‖V.tangentialGradient h x‖ ∂μ + ε := by
      have : ε / (μ.real A + 1) * μ.real A ≤ ε := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        exact mul_le_mul_of_nonneg_left (by linarith) hε.le
      linarith

theorem main_theorem : ApproxTangentAE ∧ FirstVariationFormula ∧ StationaryIffVariational ∧ StationaryMonotonicity ∧ StationaryDensity ∧ CanonicalRepresentative ∧ BoundedCurvatureMonotonicity ∧ LogarithmicMonotonicityError ∧ LpMonotonicity ∧ LpDensity ∧ LpSupportRepresentation ∧ PoincareInequality ∧ SobolevInequality ∧ SupportInBall ∧ ConvexHullProperty ∧ ClassicalTangent := by sorry

end

end GMT.Ch04
