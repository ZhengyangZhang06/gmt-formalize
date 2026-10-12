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

/-- **Local data for the weighted monotonicity identity (Simon Ch. 4, 3.1–3.3 and 5.1).** Let `μ_V`
be finite on compacts with `x ↦ p_{T_x V}` `μ_V`-a.e. strongly measurable, `U` open, `H` locally
`μ_V`-integrable on `U`, `h ∈ C¹(U)`, `ρ > 0` and `tsupport h ∩ B_ρ(ξ) ⊆ U`. Then there are `R > ρ`
and `A` such that `tsupport h ∩ B_R(ξ) ⊆ U`, `h` and `|D^⊥r|²` are a.e. strongly measurable for
`μ_V ⌞ B_R(ξ)`, `|h| ≤ A` and `|D^⊥r|² ≤ 1` on `B_R(ξ)`, and `(x - ξ) · ∇^M h` and
`(x - ξ) · (∇^M h + hH)` are `μ_V`-integrable on `B_R(ξ)`. -/
theorem Submission.weighted_mono_local_data : (∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)) (H : Ambient n ℓ → Ambient n ℓ) (h : Ambient n ℓ → ℝ) (ξ : Ambient n ℓ) (ρ : ℝ), IsFiniteMeasureOnCompacts V.weight → AEStronglyMeasurable (fun x ↦ (V.tangentSpace x).starProjection) V.weight → IsOpen U → LocallyIntegrableOn H U V.weight → ContDiffOn ℝ 1 h U → tsupport h ∩ closedBall ξ ρ ⊆ U → 0 < ρ → ∃ R A : ℝ, ρ < R ∧ tsupport h ∩ closedBall ξ R ⊆ U ∧ AEStronglyMeasurable h (V.weight.restrict (closedBall ξ R)) ∧ AEStronglyMeasurable (V.normalRadialSq ξ) (V.weight.restrict (closedBall ξ R)) ∧ (∀ x ∈ closedBall ξ R, |h x| ≤ A ∧ |V.normalRadialSq ξ x| ≤ 1) ∧ IntegrableOn (fun x ↦ inner ℝ (x - ξ) (V.tangentialGradient h x)) (closedBall ξ R) V.weight ∧ IntegrableOn (fun x ↦ inner ℝ (x - ξ) (V.tangentialGradient h x + h x • H x)) (closedBall ξ R) V.weight) := by
  intro n ℓ V U H h ξ ρ hμ hP hU hH hh hsub hρ
  -- Step 1 (room): `B_ρ(ξ)` lies in the open set `(tsupport h)ᶜ ∪ U`, hence so does a
  -- closed thickening `B_R(ξ)`, `R = δ + ρ > ρ`; then `tsupport h ∩ B_R(ξ) ⊆ U`.
  have hW : IsOpen ((tsupport h)ᶜ ∪ U) := (isClosed_tsupport h).isOpen_compl.union hU
  have hBW : closedBall ξ ρ ⊆ (tsupport h)ᶜ ∪ U := by
    intro x hx
    by_cases hxt : x ∈ tsupport h
    · exact Or.inr (hsub ⟨hxt, hx⟩)
    · exact Or.inl hxt
  obtain ⟨δ, hδ, hδW⟩ := (isCompact_closedBall ξ ρ).exists_cthickening_subset_open hW hBW
  rw [cthickening_closedBall hδ.le hρ.le ξ] at hδW
  obtain ⟨R, hR⟩ : ∃ R, R = δ + ρ := ⟨_, rfl⟩
  rw [← hR] at hδW
  have hρR : ρ < R := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hsubR : tsupport h ∩ closedBall ξ R ⊆ U := by
    rintro x ⟨hxt, hxB⟩
    rcases hδW hxB with hx | hx
    · exact absurd hxt hx
    · exact hx
  -- Step 2: `h` and `∇h` are continuous at every point of `B_R(ξ)`: on `U` by `C¹`, and off `U`
  -- they vanish near the point, which lies outside `tsupport h`.
  have hcont : ∀ x ∈ closedBall ξ R, ContinuousAt h x ∧ ContinuousAt (gradient h) x := by
    intro x hx
    by_cases hxU : x ∈ U
    · have hUx : U ∈ 𝓝 x := hU.mem_nhds hxU
      have hDh : ContinuousAt (fderiv ℝ h) x :=
        (hh.continuousOn_fderiv_of_isOpen hU le_rfl).continuousAt hUx
      exact ⟨hh.continuousOn.continuousAt hUx,
        (InnerProductSpace.toDual ℝ (Ambient n ℓ)).symm.continuous.continuousAt.comp hDh⟩
    · have hxt : x ∉ tsupport h := fun hxt ↦ hxU (hsubR ⟨hxt, hx⟩)
      have hxn : (tsupport h)ᶜ ∈ 𝓝 x := (isClosed_tsupport h).isOpen_compl.mem_nhds hxt
      have h0 : h =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := by
        filter_upwards [hxn] with y hy
        exact image_eq_zero_of_notMem_tsupport hy
      have g0 : gradient h =ᶠ[𝓝 x] fun _ ↦ (0 : Ambient n ℓ) := by
        filter_upwards [hxn] with y hy
        rw [gradient, fderiv_of_notMem_tsupport ℝ hy, map_zero]
      exact ⟨h0.continuousAt, g0.continuousAt⟩
  have hhc : ContinuousOn h (closedBall ξ R) := fun x hx ↦ (hcont x hx).1.continuousWithinAt
  have hgc : ContinuousOn (gradient h) (closedBall ξ R) :=
    fun x hx ↦ (hcont x hx).2.continuousWithinAt
  -- Step 3: bounds `A`, `A₁` for `h`, `∇h` on the compact ball, measurability for `μ ⌞ B_R(ξ)`,
  -- and `μ(B_R(ξ)) < ∞`.
  obtain ⟨A, hA⟩ := (isCompact_closedBall ξ R).exists_bound_of_continuousOn hhc
  obtain ⟨A₁, hA₁⟩ := (isCompact_closedBall ξ R).exists_bound_of_continuousOn hgc
  have hBm : MeasurableSet (closedBall ξ R) := measurableSet_closedBall
  have hhm : AEStronglyMeasurable h (V.weight.restrict (closedBall ξ R)) :=
    hhc.aestronglyMeasurable hBm
  have hgm : AEStronglyMeasurable (gradient h) (V.weight.restrict (closedBall ξ R)) :=
    hgc.aestronglyMeasurable hBm
  have hBfin : V.weight (closedBall ξ R) < ⊤ := (isCompact_closedBall ξ R).measure_lt_top
  -- Step 4: `∇^M h = p_x (∇h)` is measurable (continuous evaluation) and bounded by `A₁`.
  have happ : Continuous (Function.uncurry
      fun (L : Ambient n ℓ →L[ℝ] Ambient n ℓ) (v : Ambient n ℓ) ↦ L v) :=
    isBoundedBilinearMap_apply.continuous
  have hTm : AEStronglyMeasurable (V.tangentialGradient h)
      (V.weight.restrict (closedBall ξ R)) :=
    happ.comp_aestronglyMeasurable₂ hP.restrict hgm
  have hTb : ∀ x ∈ closedBall ξ R, ‖V.tangentialGradient h x‖ ≤ A₁ := fun x hx ↦
    ((V.tangentSpace x).norm_starProjection_apply_le (gradient h x)).trans (hA₁ x hx)
  -- Step 5: `q = |(1 - p_x)(x - ξ)|² / |x - ξ|²` is measurable and `0 ≤ q ≤ 1`.
  have hdisp : Continuous fun x : Ambient n ℓ ↦ x - ξ := continuous_id.sub continuous_const
  have hPperp : AEStronglyMeasurable (fun x ↦ (V.tangentSpace x)ᗮ.starProjection) V.weight := by
    have : (fun x ↦ (V.tangentSpace x)ᗮ.starProjection) =
        fun x ↦ 1 - (V.tangentSpace x).starProjection := by
      funext x
      exact Submodule.starProjection_orthogonal' (V.tangentSpace x)
    rw [this]
    exact aestronglyMeasurable_const.sub hP
  have hqm : AEStronglyMeasurable (V.normalRadialSq ξ) V.weight := by
    have hnum : AEStronglyMeasurable
        (fun x ↦ (V.tangentSpace x)ᗮ.starProjection (x - ξ)) V.weight :=
      happ.comp_aestronglyMeasurable₂ hPperp hdisp.aestronglyMeasurable
    have h1 : AEMeasurable
        (fun x ↦ ‖(V.tangentSpace x)ᗮ.starProjection (x - ξ)‖ ^ 2) V.weight :=
      (hnum.norm.pow 2).aemeasurable
    have h2 : AEMeasurable (fun x : Ambient n ℓ ↦ ‖x - ξ‖ ^ 2) V.weight :=
      (hdisp.norm.pow 2).measurable.aemeasurable
    exact (h1.div h2).aestronglyMeasurable
  have hqb : ∀ x, |V.normalRadialSq ξ x| ≤ 1 := by
    intro x
    have h0 : 0 ≤ V.normalRadialSq ξ x := div_nonneg (sq_nonneg _) (sq_nonneg _)
    have h1 : V.normalRadialSq ξ x ≤ 1 := div_le_one_of_le₀
      (pow_le_pow_left₀ (norm_nonneg _) (Submodule.norm_starProjection_apply_le _ _) 2)
      (sq_nonneg _)
    rw [abs_of_nonneg h0]
    exact h1
  -- Step 6: `⟨x - ξ, ∇^M h⟩` is measurable and bounded by `R A₁` on `B_R(ξ)`.
  have hF₁ : IntegrableOn (fun x ↦ inner ℝ (x - ξ) (V.tangentialGradient h x))
      (closedBall ξ R) V.weight := by
    refine IntegrableOn.of_bound hBfin ?_ (R * A₁) ?_
    · exact continuous_inner.comp_aestronglyMeasurable₂ hdisp.aestronglyMeasurable hTm
    · refine ae_restrict_of_forall_mem hBm fun x hx ↦ ?_
      have hxR : ‖x - ξ‖ ≤ R := by rw [← dist_eq_norm]; exact hx
      rw [Real.norm_eq_abs]
      exact (abs_real_inner_le_norm _ _).trans (mul_le_mul hxR (hTb x hx) (norm_nonneg _) hR0)
  -- Step 7: `H` is integrable on the compact `K = tsupport h ∩ B_R(ξ) ⊆ U`; `⟨x - ξ, h H⟩` is
  -- dominated by `R A |H|` on `K` and vanishes on `B_R(ξ) \ K`.
  have hK : IsCompact (tsupport h ∩ closedBall ξ R) :=
    (isCompact_closedBall ξ R).inter_left (isClosed_tsupport h)
  have hKm : MeasurableSet (tsupport h ∩ closedBall ξ R) := hK.isClosed.measurableSet
  have hHK : IntegrableOn H (tsupport h ∩ closedBall ξ R) V.weight :=
    hH.integrableOn_compact_subset hsubR hK
  have hF₂K : IntegrableOn (fun x ↦ inner ℝ (x - ξ) (h x • H x))
      (tsupport h ∩ closedBall ξ R) V.weight := by
    refine Integrable.mono' (hHK.norm.const_mul (R * A)) ?_ ?_
    · have hhK : AEStronglyMeasurable h (V.weight.restrict (tsupport h ∩ closedBall ξ R)) :=
        hhm.mono_set inter_subset_right
      exact continuous_inner.comp_aestronglyMeasurable₂ hdisp.aestronglyMeasurable
        (hhK.smul hHK.aestronglyMeasurable)
    · refine ae_restrict_of_forall_mem hKm fun x hx ↦ ?_
      have hxR : ‖x - ξ‖ ≤ R := by rw [← dist_eq_norm]; exact hx.2
      have hhx : ‖h x‖ ≤ A := hA x hx.2
      rw [Real.norm_eq_abs]
      calc |inner ℝ (x - ξ) (h x • H x)| ≤ ‖x - ξ‖ * ‖h x • H x‖ := abs_real_inner_le_norm _ _
        _ = ‖x - ξ‖ * (‖h x‖ * ‖H x‖) := by rw [norm_smul]
        _ ≤ R * (A * ‖H x‖) :=
          mul_le_mul hxR (mul_le_mul_of_nonneg_right hhx (norm_nonneg _)) (by positivity) hR0
        _ = R * A * ‖H x‖ := by ring
  have hF₂ : IntegrableOn (fun x ↦ inner ℝ (x - ξ) (h x • H x)) (closedBall ξ R) V.weight := by
    refine hF₂K.of_forall_sdiff_eq_zero hBm fun x hx ↦ ?_
    have hxt : x ∉ tsupport h := fun hxt ↦ hx.2 ⟨hxt, hx.1⟩
    simp [image_eq_zero_of_notMem_tsupport hxt]
  -- Step 8: `G = ⟨x - ξ, ∇^M h⟩ + ⟨x - ξ, h H⟩` is integrable on `B_R(ξ)`.
  refine ⟨R, A, hρR, hsubR, hhm, hqm.restrict, fun x hx ↦ ⟨?_, hqb x⟩, hF₁, ?_⟩
  · rw [← Real.norm_eq_abs]
    exact hA x hx
  · exact (hF₁.add hF₂).congr_fun (fun x _ ↦ (inner_add_right _ _ _).symm) hBm
/-- **Cutoff identity (Simon Ch. 4, 3.1–3.3 and 5.1).** The first variation identity tested with
the radial field `h(x) γ(r)(x - ξ)`, `γ(t) = φ(t/τ)`, `r = |x - ξ|` (the last hypothesis, an
identity of integrals over `U`), rewritten over the whole space. Assume `μ` is finite on compacts,
`tsupport h ∩ B_R(ξ) ⊆ U`, `g = 0` off `tsupport h`, `h` and `q` are a.e. strongly measurable for
`μ ⌞ B_R(ξ)` with `|h| ≤ A` and `|q| ≤ 1` on `B_R(ξ)`, `(x - ξ) · g` and `(x - ξ) · (g + hH)` are
`μ`-integrable on `B_R(ξ)`, `φ ∈ C¹` vanishes on `[c, ∞)`, `τ > 0` and `cτ ≤ R`. Then
`n ∫ h φ(r/τ) dμ + ∫ h (1 - q) (r/τ) φ'(r/τ) dμ + ∫ φ(r/τ) (x - ξ) · (g + hH) dμ = 0`. -/
theorem Submission.weighted_mono_cutoff_identity : (∀ (n ℓ : ℕ) (μ : Measure (Ambient n ℓ)) (U : Set (Ambient n ℓ)) (h q : Ambient n ℓ → ℝ) (g H : Ambient n ℓ → Ambient n ℓ) (φ : ℝ → ℝ) (ξ : Ambient n ℓ) (c τ R A : ℝ), IsFiniteMeasureOnCompacts μ → tsupport h ∩ closedBall ξ R ⊆ U → (∀ x, x ∉ tsupport h → g x = 0) → AEStronglyMeasurable h (μ.restrict (closedBall ξ R)) → AEStronglyMeasurable q (μ.restrict (closedBall ξ R)) → (∀ x ∈ closedBall ξ R, |h x| ≤ A ∧ |q x| ≤ 1) → IntegrableOn (fun x ↦ inner ℝ (x - ξ) (g x)) (closedBall ξ R) μ → IntegrableOn (fun x ↦ inner ℝ (x - ξ) (g x + h x • H x)) (closedBall ξ R) μ → ContDiff ℝ 1 φ → (∀ t, c ≤ t → φ t = 0) → 0 < τ → c * τ ≤ R → ∫ x in U, (h x * ((n : ℝ) * φ (‖x - ξ‖ / τ) + ‖x - ξ‖ * deriv (fun t ↦ φ (t / τ)) ‖x - ξ‖ * (1 - q x)) + φ (‖x - ξ‖ / τ) * inner ℝ (x - ξ) (g x)) ∂μ = -∫ x in U, h x * φ (‖x - ξ‖ / τ) * inner ℝ (x - ξ) (H x) ∂μ → (n : ℝ) * ∫ x, h x * φ (‖x - ξ‖ / τ) ∂μ + ∫ x, h x * (1 - q x) * (‖x - ξ‖ / τ * deriv φ (‖x - ξ‖ / τ)) ∂μ + ∫ x, φ (‖x - ξ‖ / τ) * inner ℝ (x - ξ) (g x + h x • H x) ∂μ = 0) := by
  intro n ℓ μ U h q g H φ ξ c τ R A hμ hU hg hhm hqm hbd hgi hGi hφ hφc hτ hcR hRFV
  -- Step 1: `φ` is differentiable, `φ'` is continuous, and `φ' = 0` on `(c, ∞)`.
  have hφd : Differentiable ℝ φ := hφ.differentiable_one
  have hφ'c : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  have hφ'0 : ∀ t, c < t → deriv φ t = 0 := by
    intro t ht
    have hev : φ =ᶠ[𝓝 t] fun _ ↦ (0 : ℝ) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      exact hφc s (le_of_lt hs)
    rw [hev.deriv_eq, deriv_const]
  -- Step 2: off `B = B_R(ξ)` we have `r/τ > c`, so `φ(r/τ) = φ'(r/τ) = 0`.
  have hout : ∀ x, x ∉ closedBall ξ R →
      φ (‖x - ξ‖ / τ) = 0 ∧ deriv φ (‖x - ξ‖ / τ) = 0 := by
    intro x hx
    have hr : R < ‖x - ξ‖ := by
      rw [mem_closedBall, dist_eq_norm, not_le] at hx
      exact hx
    have hct : c < ‖x - ξ‖ / τ := by
      rw [lt_div_iff₀ hτ]
      linarith
    exact ⟨hφc _ hct.le, hφ'0 _ hct⟩
  -- Step 3: chain rule, `γ'(s) = φ'(s/τ)/τ` for `γ(t) = φ(t/τ)`.
  have hchain : ∀ s, deriv (fun t ↦ φ (t / τ)) s = deriv φ (s / τ) / τ := by
    intro s
    have h1 : HasDerivAt (fun t : ℝ ↦ t / τ) (1 / τ) s := (hasDerivAt_id s).div_const τ
    have h2 : HasDerivAt φ (deriv φ (s / τ)) (s / τ) := (hφd (s / τ)).hasDerivAt
    have h3 : HasDerivAt (fun t ↦ φ (t / τ)) (deriv φ (s / τ) * (1 / τ)) s := h2.comp s h1
    rw [h3.deriv]
    ring
  -- Steps 4–5: off `U`, either `x ∉ tsupport h` (so `h x = 0` and `g x = 0`) or `x ∉ B`; in
  -- both cases the two integrands of the hypothesis vanish, so `∫_U = ∫`.
  have hoff : ∀ x, x ∉ U → x ∉ tsupport h ∨ x ∉ closedBall ξ R :=
    fun x hx ↦ not_and_or.mp fun hx' ↦ hx (hU hx')
  have hLU : ∫ x in U, (h x * ((n : ℝ) * φ (‖x - ξ‖ / τ) +
          ‖x - ξ‖ * deriv (fun t ↦ φ (t / τ)) ‖x - ξ‖ * (1 - q x)) +
        φ (‖x - ξ‖ / τ) * inner ℝ (x - ξ) (g x)) ∂μ =
      ∫ x, (h x * ((n : ℝ) * φ (‖x - ξ‖ / τ) +
          ‖x - ξ‖ * deriv (fun t ↦ φ (t / τ)) ‖x - ξ‖ * (1 - q x)) +
        φ (‖x - ξ‖ / τ) * inner ℝ (x - ξ) (g x)) ∂μ := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ ?_
    rcases hoff x hx with hx' | hx'
    · simp [image_eq_zero_of_notMem_tsupport hx', hg x hx']
    · simp [hchain, (hout x hx').1, (hout x hx').2]
  have hQU : ∫ x in U, h x * φ (‖x - ξ‖ / τ) * inner ℝ (x - ξ) (H x) ∂μ =
      ∫ x, h x * φ (‖x - ξ‖ / τ) * inner ℝ (x - ξ) (H x) ∂μ := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ ?_
    rcases hoff x hx with hx' | hx'
    · simp [image_eq_zero_of_notMem_tsupport hx']
    · simp [(hout x hx').1]
  -- Step 6: `μ(B) < ∞`, and the continuous radial factors are bounded on the compact set `B`.
  have hBfin : μ (closedBall ξ R) < ⊤ := (isCompact_closedBall ξ R).measure_lt_top
  have hr : Continuous fun x : Ambient n ℓ ↦ ‖x - ξ‖ / τ :=
    (continuous_id.sub continuous_const).norm.div_const τ
  have hc0 : Continuous fun x : Ambient n ℓ ↦ φ (‖x - ξ‖ / τ) := hφd.continuous.comp hr
  have hc1 : Continuous fun x : Ambient n ℓ ↦ ‖x - ξ‖ / τ * deriv φ (‖x - ξ‖ / τ) :=
    hr.mul (hφ'c.comp hr)
  obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall ξ R).exists_bound_of_continuousOn hc0.continuousOn
  obtain ⟨M₁, hM₁⟩ := (isCompact_closedBall ξ R).exists_bound_of_continuousOn hc1.continuousOn
  have hA : ∀ x ∈ closedBall ξ R, 0 ≤ A := fun x hx ↦ (abs_nonneg _).trans (hbd x hx).1
  -- Step 7: the four pieces `T₁, …, T₄` are integrable on `B` and vanish off `B`.
  have hT1 : Integrable (fun x ↦ h x * φ (‖x - ξ‖ / τ)) μ := by
    refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := closedBall ξ R) ?_ ?_
    · refine IntegrableOn.of_bound hBfin (hhm.mul hc0.aestronglyMeasurable) (A * M₀) ?_
      filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
      rw [norm_mul, Real.norm_eq_abs (h x)]
      exact mul_le_mul (hbd x hx).1 (hM₀ x hx) (norm_nonneg _) (hA x hx)
    · intro x hx
      simp [(hout x hx).1]
  have hT2 : Integrable (fun x ↦ h x * (1 - q x) * (‖x - ξ‖ / τ * deriv φ (‖x - ξ‖ / τ))) μ := by
    refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := closedBall ξ R) ?_ ?_
    · refine IntegrableOn.of_bound hBfin
        ((hhm.mul (aestronglyMeasurable_const.sub hqm)).mul hc1.aestronglyMeasurable)
        (A * 2 * M₁) ?_
      filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
      have hq := abs_le.mp (hbd x hx).2
      have hq1 : |1 - q x| ≤ 2 := abs_le.mpr ⟨by linarith [hq.2], by linarith [hq.1]⟩
      rw [norm_mul (h x * (1 - q x)), norm_mul (h x), Real.norm_eq_abs (h x),
        Real.norm_eq_abs (1 - q x)]
      exact mul_le_mul (mul_le_mul (hbd x hx).1 hq1 (abs_nonneg _) (hA x hx)) (hM₁ x hx)
        (norm_nonneg _) (mul_nonneg (hA x hx) zero_le_two)
    · intro x hx
      simp [(hout x hx).2]
  have hT3 : Integrable (fun x ↦ φ (‖x - ξ‖ / τ) * inner ℝ (x - ξ) (g x)) μ := by
    refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := closedBall ξ R) ?_ ?_
    · exact hgi.bdd_mul hc0.aestronglyMeasurable
        (ae_restrict_of_forall_mem measurableSet_closedBall hM₀)
    · intro x hx
      simp [(hout x hx).1]
  have hT4 : Integrable (fun x ↦ φ (‖x - ξ‖ / τ) * inner ℝ (x - ξ) (g x + h x • H x)) μ := by
    refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := closedBall ξ R) ?_ ?_
    · exact hGi.bdd_mul hc0.aestronglyMeasurable
        (ae_restrict_of_forall_mem measurableSet_closedBall hM₀)
    · intro x hx
      simp [(hout x hx).1]
  -- Step 8: pointwise `L = n T₁ + T₂ + T₃` and `Q = T₄ - T₃`; integrate and rearrange.
  have hL : (fun x ↦ h x * ((n : ℝ) * φ (‖x - ξ‖ / τ) +
          ‖x - ξ‖ * deriv (fun t ↦ φ (t / τ)) ‖x - ξ‖ * (1 - q x)) +
        φ (‖x - ξ‖ / τ) * inner ℝ (x - ξ) (g x)) =
      fun x ↦ (n : ℝ) * (h x * φ (‖x - ξ‖ / τ)) +
        h x * (1 - q x) * (‖x - ξ‖ / τ * deriv φ (‖x - ξ‖ / τ)) +
        φ (‖x - ξ‖ / τ) * inner ℝ (x - ξ) (g x) := by
    funext x
    rw [hchain]
    ring
  have hQ : (fun x ↦ h x * φ (‖x - ξ‖ / τ) * inner ℝ (x - ξ) (H x)) =
      fun x ↦ φ (‖x - ξ‖ / τ) * inner ℝ (x - ξ) (g x + h x • H x) -
        φ (‖x - ξ‖ / τ) * inner ℝ (x - ξ) (g x) := by
    funext x
    rw [inner_add_right, real_inner_smul_right]
    ring
  have hT12 : Integrable (fun x ↦ (n : ℝ) * (h x * φ (‖x - ξ‖ / τ)) +
      h x * (1 - q x) * (‖x - ξ‖ / τ * deriv φ (‖x - ξ‖ / τ))) μ :=
    (hT1.const_mul (n : ℝ)).add hT2
  rw [hLU, hQU, hL, hQ, integral_add hT12 hT3, integral_add (hT1.const_mul (n : ℝ)) hT2,
    integral_const_mul, integral_sub hT4 hT3] at hRFV
  linarith
/-- Simon §5 (p. 96), the weighted radial field `X(x) = h(x) γ(r) (x - ξ)`, `r = |x - ξ|`: if
`h ∈ C¹(U)`, the profile `γ ∈ C¹(ℝ)` is constant on `(-∞, a]` (`a > 0`) and vanishes on
`[b, ∞)`, and `spt h ∩ B_b(ξ) ⊆ U`, then `X ∈ C¹_c(U; ℝ^{n+ℓ})`; in fact
`tsupport X ⊆ spt h ∩ B_b(ξ)`. -/
theorem Submission.weighted_mono_radial_test_field : ∀ (n ℓ : ℕ) (U : Set (Ambient n ℓ)) (h : Ambient n ℓ → ℝ) (γ : ℝ → ℝ) (ξ : Ambient n ℓ) (a b : ℝ), IsOpen U → ContDiffOn ℝ 1 h U → ContDiff ℝ 1 γ → 0 < a → (∀ t, t ≤ a → γ t = γ 0) → (∀ t, b ≤ t → γ t = 0) → tsupport h ∩ closedBall ξ b ⊆ U → IsTestField U (fun x ↦ (h x * γ ‖x - ξ‖) • (x - ξ)) := by
  intro n ℓ U h γ ξ a b hU hh hγ ha hγa hγb hKU
  -- `K = spt h ∩ B_b(ξ)` is compact: a closed subset of the compact ball `B_b(ξ)`.
  have hK : IsCompact (tsupport h ∩ closedBall ξ b) :=
    (isCompact_closedBall ξ b).inter_left (isClosed_tsupport h)
  -- `X = 0` off `K`: off `spt h` since `h = 0`, outside `B_b(ξ)` since `γ(|x - ξ|) = 0`.
  have hzero : ∀ x, x ∉ tsupport h ∩ closedBall ξ b → (h x * γ ‖x - ξ‖) • (x - ξ) = 0 := by
    intro x hx
    by_cases hxh : x ∈ tsupport h
    · have hxb : b < ‖x - ξ‖ := by
        rw [← dist_eq_norm, ← not_le, ← mem_closedBall]
        exact fun hb ↦ hx ⟨hxh, hb⟩
      rw [hγb _ hxb.le, mul_zero, zero_smul]
    · rw [image_eq_zero_of_notMem_tsupport hxh, zero_mul, zero_smul]
  have hsupp : tsupport (fun x ↦ (h x * γ ‖x - ξ‖) • (x - ξ)) ⊆ tsupport h ∩ closedBall ξ b :=
    closure_minimal (fun x hx ↦ by_contra fun hxK ↦ hx (hzero x hxK)) hK.isClosed
  refine ⟨?_, HasCompactSupport.intro hK hzero, hsupp.trans hKU⟩
  rw [contDiff_iff_contDiffAt]
  intro x₀
  by_cases hx₀ : x₀ ∈ tsupport h ∩ closedBall ξ b
  · -- At `x₀ ∈ K ⊆ U`: `h` is `C¹` near `x₀`, and so is `γ(|x - ξ|)`.
    have hh₀ : ContDiffAt ℝ 1 h x₀ := hh.contDiffAt (hU.mem_nhds (hKU hx₀))
    have hγ₀ : ContDiffAt ℝ 1 (fun x ↦ γ ‖x - ξ‖) x₀ := by
      by_cases hξ : x₀ = ξ
      · -- Near `ξ`, `|x - ξ| < a`, so `γ(|x - ξ|) = γ(0)` is constant.
        subst hξ
        refine (contDiffAt_const (c := γ 0)).congr_of_eventuallyEq ?_
        filter_upwards [ball_mem_nhds x₀ ha] with x hx
        rw [mem_ball, dist_eq_norm] at hx
        exact hγa _ hx.le
      · -- Away from `ξ` the norm is smooth at `x - ξ ≠ 0`.
        have hr : ContDiffAt ℝ 1 (fun x ↦ ‖x - ξ‖) x₀ :=
          (contDiffAt_norm ℝ (sub_ne_zero.mpr hξ)).comp x₀ (contDiffAt_id.sub contDiffAt_const)
        exact hγ.contDiffAt.comp x₀ hr
    exact (hh₀.mul hγ₀).smul (contDiffAt_id.sub contDiffAt_const)
  · -- Off the closed set `K`, `X` vanishes on a neighbourhood of `x₀`.
    refine (contDiffAt_const (c := (0 : Ambient n ℓ))).congr_of_eventuallyEq ?_
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx₀] with x hx
    exact hzero x hx

/-- Simon 3.3 (p. 90) in the weighted form of 5.1 (p. 96), with `γ(r) = φ(r/τ)`: from the first
variation identity (RFV) for the fields `h(x) γ(r) (x - ξ)`, `r = |x - ξ|`, there is a radius
`R > ρ` on which `h` and `|D^⊥r|²` are bounded and measurable and
`G = (x - ξ) · (∇^M h + h H)` is integrable, and for every cutoff `φ` (`φ = 1` on `(-∞, 1]`,
`φ = 0` on `[1 + ε, ∞)`, `(1 + ε) ρ < R`) and `0 < τ ≤ ρ`,
`n ∫ h φ(r/τ) dμ_V + ∫ h (1 - |D^⊥r|²) (r/τ) φ'(r/τ) dμ_V + ∫ φ(r/τ) G dμ_V = 0`. -/
theorem Submission.weighted_mono_cutoff_first_variation : ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)) (H : Ambient n ℓ → Ambient n ℓ) (h : Ambient n ℓ → ℝ) (ξ : Ambient n ℓ) (ρ : ℝ), IsFiniteMeasureOnCompacts V.weight → AEStronglyMeasurable (fun x ↦ (V.tangentSpace x).starProjection) V.weight → IsOpen U → V.HasMeanCurvatureIn U H → ContDiffOn ℝ 1 h U → tsupport h ∩ closedBall ξ ρ ⊆ U → 0 < ρ → (∀ γ : ℝ → ℝ, ContDiff ℝ 1 γ → IsTestField U (fun x ↦ (h x * γ ‖x - ξ‖) • (x - ξ)) → ∫ x in U, (h x * ((n : ℝ) * γ ‖x - ξ‖ + ‖x - ξ‖ * deriv γ ‖x - ξ‖ * (1 - V.normalRadialSq ξ x)) + γ ‖x - ξ‖ * inner ℝ (x - ξ) (V.tangentialGradient h x)) ∂V.weight = -∫ x in U, h x * γ ‖x - ξ‖ * inner ℝ (x - ξ) (H x) ∂V.weight) → ∃ R A : ℝ, ρ < R ∧ AEStronglyMeasurable h (V.weight.restrict (closedBall ξ R)) ∧ AEStronglyMeasurable (V.normalRadialSq ξ) (V.weight.restrict (closedBall ξ R)) ∧ (∀ x ∈ closedBall ξ R, |h x| ≤ A ∧ |V.normalRadialSq ξ x| ≤ 1) ∧ IntegrableOn (fun x ↦ inner ℝ (x - ξ) (V.tangentialGradient h x + h x • H x)) (closedBall ξ R) V.weight ∧ ∀ (ε : ℝ) (φ : ℝ → ℝ), 0 < ε → (1 + ε) * ρ < R → ContDiff ℝ 1 φ → (∀ t, t ≤ 1 → φ t = 1) → (∀ t, 1 + ε ≤ t → φ t = 0) → ∀ τ, 0 < τ → τ ≤ ρ → (n : ℝ) * ∫ x, h x * φ (‖x - ξ‖ / τ) ∂V.weight + ∫ x, h x * (1 - V.normalRadialSq ξ x) * (‖x - ξ‖ / τ * deriv φ (‖x - ξ‖ / τ)) ∂V.weight + ∫ x, φ (‖x - ξ‖ / τ) * inner ℝ (x - ξ) (V.tangentialGradient h x + h x • H x) ∂V.weight = 0 := by
  intro n ℓ V U H h ξ ρ hfin hP hU hH hh hsupp hρ hRFV
  -- A radius `R > ρ` with `spt h ∩ B_R(ξ) ⊆ U`, and the bounds and integrability on `B_R(ξ)`.
  obtain ⟨R, A, hρR, hsuppR, hhm, hqm, hbd, hI1, hG⟩ :=
    Submission.weighted_mono_local_data n ℓ V U H h ξ ρ hfin hP hU hH.1 hh hsupp hρ
  refine ⟨R, A, hρR, hhm, hqm, hbd, hG, ?_⟩
  intro ε φ hε hεR hφ h1 h0 τ hτ hτρ
  -- `γ(t) = φ(t/τ)` is `C¹`, equals `1 = γ(0)` for `t ≤ τ` and `0` for `t ≥ (1 + ε)τ`, and
  -- `(1 + ε)τ ≤ (1 + ε)ρ < R`; so `h(x) γ(r) (x - ξ)` is a test field in `U` and (RFV) applies.
  have hcR : (1 + ε) * τ ≤ R := (mul_le_mul_of_nonneg_left hτρ (by linarith)).trans hεR.le
  have hγ : ContDiff ℝ 1 (fun t : ℝ ↦ φ (t / τ)) := hφ.comp (contDiff_id.div_const τ)
  have hX : IsTestField U (fun x ↦ (h x * (fun t : ℝ ↦ φ (t / τ)) ‖x - ξ‖) • (x - ξ)) :=
    Submission.weighted_mono_radial_test_field n ℓ U h (fun t ↦ φ (t / τ)) ξ τ ((1 + ε) * τ)
      hU hh hγ hτ
      (fun t ht ↦ by
        show φ (t / τ) = φ (0 / τ)
        rw [h1 _ ((div_le_one₀ hτ).2 ht), zero_div, h1 0 zero_le_one])
      (fun t ht ↦ h0 _ ((le_div_iff₀ hτ).2 ht))
      ((Set.inter_subset_inter_right _ (closedBall_subset_closedBall hcR)).trans hsuppR)
  -- `∇^M h = p_{T_x V}(∇h) = 0` off `spt h`, where `Dh = 0`.
  have hg0 : ∀ x, x ∉ tsupport h → V.tangentialGradient h x = 0 := fun x hx ↦ by
    simp [tangentialGradient, gradient, fderiv_of_notMem_tsupport ℝ hx]
  -- The integrands vanish off `U`, and the identity regroups into the three integrals over `E`.
  exact Submission.weighted_mono_cutoff_identity n ℓ V.weight U h (V.normalRadialSq ξ)
    (V.tangentialGradient h) H φ ξ (1 + ε) τ R A hfin hsuppR hg0 hhm hqm hbd hI1 hG hφ h0 hτ hcR
    (hRFV _ hγ hX)
/-- **Differentiating radial cutoff integrals in the scale** (Simon Ch. 4, 3.3–3.4: `I'(ρ)` and
`J'(ρ)` for `I(ρ) = ∫ φ(r/ρ) dμ_V`, `J(ρ) = ∫ φ(r/ρ)|D^⊥r|² dμ_V`, `r = |x - ξ|`). If `φ ∈ C¹`
vanishes on `[c, ∞)`, `0 < c`, `0 < τ`, `cτ < R`, and `f` is `μ ⌞ B_R(ξ)`-a.e. strongly measurable
with `|f| ≤ A` on `B_R(ξ)`, then `f φ(r/τ)` and `f · (-(r/τ²) φ'(r/τ))` are `μ`-integrable and
`d/dt ∫ f φ(r/t) dμ = ∫ f · (-(r/τ²) φ'(r/τ)) dμ` at `t = τ`. For `t ∈ (τ/2, R/c)` both integrands
vanish off `B_R(ξ)` (there `r/t > c`), and on it `|f · (-(r/t²) φ'(r/t))| ≤ A (4R/τ²) M₁` with
`M₁ = max_{[0, 2R/τ]} |φ'|`, so dominated differentiation under the integral sign applies. -/
theorem Submission.weighted_mono_cutoff_hasDerivAt : ∀ (n ℓ : ℕ) (μ : Measure (Ambient n ℓ)) (f : Ambient n ℓ → ℝ) (φ : ℝ → ℝ) (ξ : Ambient n ℓ) (c R A τ : ℝ), IsFiniteMeasureOnCompacts μ → ContDiff ℝ 1 φ → (∀ t, c ≤ t → φ t = 0) → 0 < c → 0 < τ → c * τ < R → AEStronglyMeasurable f (μ.restrict (closedBall ξ R)) → (∀ x ∈ closedBall ξ R, |f x| ≤ A) → Integrable (fun x ↦ f x * φ (‖x - ξ‖ / τ)) μ ∧ Integrable (fun x ↦ f x * (-(‖x - ξ‖ / τ ^ 2) * deriv φ (‖x - ξ‖ / τ))) μ ∧ HasDerivAt (fun t ↦ ∫ x, f x * φ (‖x - ξ‖ / t) ∂μ) (∫ x, f x * (-(‖x - ξ‖ / τ ^ 2) * deriv φ (‖x - ξ‖ / τ)) ∂μ) τ := by
  intro n ℓ μ f φ ξ c R A τ hμ hφ hφc hc hτ hcτR hf hfA
  -- `φ` is differentiable with continuous derivative, and `φ' = 0` on the open set `(c, ∞)`
  have hφd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have hφ'c : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  have hφ' : ∀ s, c < s → deriv φ s = 0 := by
    intro s hs
    have h : φ =ᶠ[𝓝 s] fun _ ↦ 0 :=
      Filter.eventually_of_mem (Ioi_mem_nhds hs) fun u hu ↦ hφc u (le_of_lt hu)
    rw [h.deriv_eq, deriv_const]
  have hR : 0 < R := lt_trans (mul_pos hc hτ) hcτR
  have hBm : MeasurableSet (closedBall ξ R) := measurableSet_closedBall
  have hBμ : μ (closedBall ξ R) < ⊤ := (isCompact_closedBall ξ R).measure_lt_top
  have hA : 0 ≤ A := (abs_nonneg _).trans (hfA ξ (mem_closedBall_self hR.le))
  -- the neighbourhood `N = (τ/2, R/c)` of `τ`: there `t > 0` and `c t < R`
  have hτN : τ ∈ Ioo (τ / 2) (R / c) := ⟨by linarith, by rw [lt_div_iff₀ hc]; linarith⟩
  have hNnhds : Ioo (τ / 2) (R / c) ∈ 𝓝 τ := Ioo_mem_nhds hτN.1 hτN.2
  have hNpos : ∀ t ∈ Ioo (τ / 2) (R / c), 0 < t := fun t ht ↦ by linarith [ht.1]
  -- off `B_R(ξ)` the radial quotient `r / t` exceeds `c`
  have hout : ∀ t ∈ Ioo (τ / 2) (R / c), ∀ x, x ∉ closedBall ξ R → c < ‖x - ξ‖ / t := by
    intro t ht x hx
    have ht0 : 0 < t := hNpos t ht
    have hctR : t * c < R := (lt_div_iff₀ hc).1 ht.2
    have hxR : R < ‖x - ξ‖ := by
      rw [mem_closedBall, dist_eq_norm, not_le] at hx
      exact hx
    rw [lt_div_iff₀ ht0]
    linarith
  -- on `B_R(ξ)`: `0 ≤ r / t ≤ 2R/τ` and `r / t² ≤ 4R/τ²`
  have hin : ∀ t ∈ Ioo (τ / 2) (R / c), ∀ x ∈ closedBall ξ R,
      ‖x - ξ‖ / t ∈ Icc 0 (2 * R / τ) ∧ ‖x - ξ‖ / t ^ 2 ≤ 4 * R / τ ^ 2 := by
    intro t ht x hx
    have ht0 : 0 < t := hNpos t ht
    have hxR : ‖x - ξ‖ ≤ R := by
      rw [mem_closedBall, dist_eq_norm] at hx
      exact hx
    have h2t : τ < 2 * t := by linarith [ht.1]
    have hr : 0 ≤ ‖x - ξ‖ := norm_nonneg _
    refine ⟨⟨by positivity, ?_⟩, ?_⟩
    · rw [div_le_div_iff₀ ht0 hτ]
      nlinarith
    · have h1 : ‖x - ξ‖ * τ ^ 2 ≤ R * τ ^ 2 := mul_le_mul_of_nonneg_right hxR (sq_nonneg τ)
      have h2 : τ ^ 2 ≤ 4 * t ^ 2 := by nlinarith
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
  -- bounds for `|φ|` and `|φ'|` on the compact interval `[0, 2R/τ]`
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * R / τ)).exists_bound_of_continuousOn
    hφd.continuous.continuousOn
  obtain ⟨M₁, hM₁⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * R / τ)).exists_bound_of_continuousOn
    hφ'c.continuousOn
  have hM₁0 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ 0 ⟨le_rfl, by positivity⟩)
  -- a product `f h` with `h` continuous and vanishing off `B_R(ξ)` is a.e. strongly measurable
  have hmeas : ∀ h : Ambient n ℓ → ℝ, Continuous h → (∀ x, x ∉ closedBall ξ R → h x = 0) →
      AEStronglyMeasurable (fun x ↦ f x * h x) μ := by
    intro h hcont h0
    have heq : (fun x ↦ f x * h x) = (closedBall ξ R).indicator (fun x ↦ f x * h x) := by
      funext x
      by_cases hx : x ∈ closedBall ξ R
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx, h0 x hx, mul_zero]
    rw [heq, aestronglyMeasurable_indicator_iff hBm]
    exact hf.fun_mul hcont.aestronglyMeasurable
  -- and if `|h| ≤ C` on `B_R(ξ)`, then `|f h| ≤ A C 1_{B_R(ξ)}`
  have hptw : ∀ (h : Ambient n ℓ → ℝ) (C : ℝ), (∀ x, x ∉ closedBall ξ R → h x = 0) →
      (∀ x ∈ closedBall ξ R, |h x| ≤ C) →
      ∀ x, ‖f x * h x‖ ≤ (closedBall ξ R).indicator (fun _ ↦ A * C) x := by
    intro h C h0 hC x
    by_cases hx : x ∈ closedBall ξ R
    · rw [Set.indicator_of_mem hx, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul (hfA x hx) (hC x hx) (abs_nonneg _) hA
    · rw [Set.indicator_of_notMem hx, h0 x hx, mul_zero, norm_zero]
  have hind : ∀ C : ℝ, Integrable ((closedBall ξ R).indicator fun _ ↦ C) μ := fun C ↦
    (integrable_indicator_iff hBm).2 (integrableOn_const hBμ.ne)
  have hcr : ∀ t : ℝ, Continuous fun x : Ambient n ℓ ↦ ‖x - ξ‖ / t := fun t ↦
    (continuous_id.sub continuous_const).norm.div_const t
  -- the integrand `F t x = f x φ (r / t)`
  have hF_meas : ∀ᶠ t in 𝓝 τ, AEStronglyMeasurable (fun x ↦ f x * φ (‖x - ξ‖ / t)) μ :=
    Filter.eventually_of_mem hNnhds fun t ht ↦
      hmeas _ (hφd.continuous.comp (hcr t)) fun x hx ↦ hφc _ (hout t ht x hx).le
  have hF_int : Integrable (fun x ↦ f x * φ (‖x - ξ‖ / τ)) μ :=
    (hind (A * M₀)).mono' (hmeas _ (hφd.continuous.comp (hcr τ))
      fun x hx ↦ hφc _ (hout τ hτN x hx).le)
      (ae_of_all _ (hptw (fun x ↦ φ (‖x - ξ‖ / τ)) M₀ (fun x hx ↦ hφc _ (hout τ hτN x hx).le)
        fun x hx ↦ by simpa only [Real.norm_eq_abs] using hM₀ _ (hin τ hτN x hx).1))
  -- the `t`-derivative `F' t x = f x (-(r / t²) φ' (r / t))`
  have hF'0 : ∀ t ∈ Ioo (τ / 2) (R / c), ∀ x, x ∉ closedBall ξ R →
      -(‖x - ξ‖ / t ^ 2) * deriv φ (‖x - ξ‖ / t) = 0 := fun t ht x hx ↦ by
    rw [hφ' _ (hout t ht x hx), mul_zero]
  have hF'C : ∀ t ∈ Ioo (τ / 2) (R / c), ∀ x ∈ closedBall ξ R,
      |-(‖x - ξ‖ / t ^ 2) * deriv φ (‖x - ξ‖ / t)| ≤ 4 * R / τ ^ 2 * M₁ := by
    intro t ht x hx
    have ht0 : 0 < t := hNpos t ht
    rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖x - ξ‖ / t ^ 2)]
    have h := hM₁ _ (hin t ht x hx).1
    rw [Real.norm_eq_abs] at h
    exact mul_le_mul (hin t ht x hx).2 h (abs_nonneg _) (by positivity)
  have hF'_meas : AEStronglyMeasurable
      (fun x ↦ f x * (-(‖x - ξ‖ / τ ^ 2) * deriv φ (‖x - ξ‖ / τ))) μ :=
    hmeas _ ((hcr (τ ^ 2)).neg.mul (hφ'c.comp (hcr τ))) (hF'0 τ hτN)
  have h_bound : ∀ᵐ x ∂μ, ∀ t ∈ Ioo (τ / 2) (R / c),
      ‖f x * (-(‖x - ξ‖ / t ^ 2) * deriv φ (‖x - ξ‖ / t))‖ ≤
        (closedBall ξ R).indicator (fun _ ↦ A * (4 * R / τ ^ 2 * M₁)) x :=
    ae_of_all _ fun x t ht ↦
      hptw (fun x ↦ -(‖x - ξ‖ / t ^ 2) * deriv φ (‖x - ξ‖ / t)) _ (hF'0 t ht) (hF'C t ht) x
  -- pointwise chain rule: `∂_t φ (r / t) = φ' (r / t) · (-(r / t²))`
  have h_diff : ∀ᵐ x ∂μ, ∀ t ∈ Ioo (τ / 2) (R / c),
      HasDerivAt (fun t ↦ f x * φ (‖x - ξ‖ / t))
        (f x * (-(‖x - ξ‖ / t ^ 2) * deriv φ (‖x - ξ‖ / t))) t := by
    refine ae_of_all _ fun x t ht ↦ ?_
    have ht0 : t ≠ 0 := (hNpos t ht).ne'
    have h1 : HasDerivAt (fun t ↦ ‖x - ξ‖ / t) (-(‖x - ξ‖ / t ^ 2)) t := by
      have h := (hasDerivAt_inv ht0).const_mul ‖x - ξ‖
      convert h using 1
      · funext y
        rw [div_eq_mul_inv]
      · rw [div_eq_mul_inv, mul_neg]
    have h2 := ((hφd (‖x - ξ‖ / t)).hasDerivAt.comp t h1).const_mul (f x)
    convert h2 using 1
    · rfl
    · ring
  obtain ⟨hint', hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le hNnhds hF_meas
    hF_int hF'_meas h_bound (hind _) h_diff
  exact ⟨hF_int, hint', hderiv⟩
/-- **Kernel bounds for the monotonicity identity** (Simon Ch. 4, 3.5, with the corrected
prefactors). For `φ` `C¹` and nonincreasing with `φ = 1` on `(-∞, 1]` and `φ = 0` on `[1 + ε, ∞)`,
`g τ = φ (s / τ)` has `g' τ = -(s / τ ^ 2) φ' (s / τ) ≥ 0` and `∫_{(σ,ρ]} g' = φ (s / ρ) - φ (s / σ)`;
where `φ' (s / τ) ≠ 0` we have `τ ≤ s ≤ (1 + ε) τ`, so `s⁻ⁿ ≤ τ⁻ⁿ ≤ (1 + ε)ⁿ s⁻ⁿ`, and integrating
`g'` against this squeeze over `(σ, ρ]` gives both bounds. -/
theorem Submission.weighted_mono_kernel_bounds : ∀ (n : ℕ) (φ : ℝ → ℝ) (ε σ ρ s : ℝ), ContDiff ℝ 1 φ → Antitone φ → (∀ t, t ≤ 1 → φ t = 1) → (∀ t, 1 + ε ≤ t → φ t = 0) → 0 < ε → 0 < σ → σ ≤ ρ → 0 < s → (φ (s / ρ) - φ (s / σ)) / s ^ n ≤ ∫ τ in Ioc σ ρ, -(s / τ ^ 2) * deriv φ (s / τ) / τ ^ n ∧ ∫ τ in Ioc σ ρ, -(s / τ ^ 2) * deriv φ (s / τ) / τ ^ n ≤ (1 + ε) ^ n * ((φ (s / ρ) - φ (s / σ)) / s ^ n) := by
  intro n φ ε σ ρ s hφ hanti hφ1 hφ0 hε hσ hσρ hs
  -- `φ'` is continuous, `φ' ≤ 0`, and `φ'` vanishes off `[1, 1 + ε]`
  have hφd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have hφc : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  have hφn : ∀ t, deriv φ t ≤ 0 := fun t ↦ hanti.deriv_nonpos
  have hlt : ∀ t, t < 1 → deriv φ t = 0 := by
    intro t ht
    have h : φ =ᶠ[𝓝 t] fun _ ↦ (1 : ℝ) := by
      filter_upwards [Iio_mem_nhds ht] with u hu using hφ1 u hu.le
    rw [h.deriv_eq, deriv_const]
  have hgt : ∀ t, 1 + ε < t → deriv φ t = 0 := by
    intro t ht
    have h : φ =ᶠ[𝓝 t] fun _ ↦ (0 : ℝ) := by
      filter_upwards [Ioi_mem_nhds ht] with u hu using hφ0 u hu.le
    rw [h.deriv_eq, deriv_const]
  -- `g τ = φ (s / τ)` has derivative `g' τ = -(s / τ ^ 2) * φ' (s / τ)` for `τ > 0`
  have hderiv : ∀ τ : ℝ, 0 < τ →
      HasDerivAt (fun τ ↦ φ (s / τ)) (-(s / τ ^ 2) * deriv φ (s / τ)) τ := by
    intro τ hτ
    have h1 : HasDerivAt (fun y : ℝ ↦ s / y) (-(s / τ ^ 2)) τ := by
      have h := (hasDerivAt_inv hτ.ne').const_mul s
      simp only [← div_eq_mul_inv] at h
      convert h using 1
      ring
    exact ((hφd (s / τ)).hasDerivAt.comp τ h1).congr_deriv (mul_comm _ _)
  -- continuity of the integrands on `[σ, ρ]`
  have hne : ∀ τ ∈ Icc σ ρ, τ ≠ 0 := fun τ hτ ↦ (hσ.trans_le hτ.1).ne'
  have hg'c : ContinuousOn (fun τ : ℝ ↦ -(s / τ ^ 2) * deriv φ (s / τ)) (Icc σ ρ) :=
    ((continuousOn_const.div (continuousOn_id.pow 2) fun τ hτ ↦ pow_ne_zero 2 (hne τ hτ)).neg).mul
      (hφc.comp_continuousOn (continuousOn_const.div continuousOn_id hne))
  have hkc : ContinuousOn (fun τ : ℝ ↦ -(s / τ ^ 2) * deriv φ (s / τ) / τ ^ n) (Icc σ ρ) :=
    hg'c.div (continuousOn_id.pow n) fun τ hτ ↦ pow_ne_zero n (hne τ hτ)
  have hg'i : IntegrableOn (fun τ : ℝ ↦ -(s / τ ^ 2) * deriv φ (s / τ)) (Ioc σ ρ) :=
    hg'c.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hki : IntegrableOn (fun τ : ℝ ↦ -(s / τ ^ 2) * deriv φ (s / τ) / τ ^ n) (Ioc σ ρ) :=
    hkc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  -- fundamental theorem of calculus
  have hFTC : ∫ τ in Ioc σ ρ, -(s / τ ^ 2) * deriv φ (s / τ) = φ (s / ρ) - φ (s / σ) := by
    rw [← intervalIntegral.integral_of_le hσρ]
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun τ ↦ φ (s / τ))
      (f' := fun τ ↦ -(s / τ ^ 2) * deriv φ (s / τ)) (fun τ hτ ↦ ?_) ?_
    · rw [uIcc_of_le hσρ] at hτ
      exact hderiv τ (hσ.trans_le hτ.1)
    · exact ContinuousOn.intervalIntegrable (by rwa [uIcc_of_le hσρ])
  -- pointwise bounds: where `φ' (s / τ) ≠ 0`, `τ ≤ s ≤ (1 + ε) τ`
  have hpt : ∀ τ ∈ Ioc σ ρ,
      -(s / τ ^ 2) * deriv φ (s / τ) / s ^ n ≤ -(s / τ ^ 2) * deriv φ (s / τ) / τ ^ n ∧
      -(s / τ ^ 2) * deriv φ (s / τ) / τ ^ n ≤
        (1 + ε) ^ n * (-(s / τ ^ 2) * deriv φ (s / τ) / s ^ n) := by
    intro τ hτ
    have hτ0 : 0 < τ := hσ.trans hτ.1
    have hg0 : 0 ≤ -(s / τ ^ 2) * deriv φ (s / τ) :=
      mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.2 (div_pos hs (pow_pos hτ0 2)).le) (hφn _)
    by_cases hd : deriv φ (s / τ) = 0
    · simp [hd]
    have ha : 1 ≤ s / τ := not_lt.1 fun h ↦ hd (hlt _ h)
    have hb : s / τ ≤ 1 + ε := not_lt.1 fun h ↦ hd (hgt _ h)
    rw [le_div_iff₀ hτ0, one_mul] at ha
    rw [div_le_iff₀ hτ0] at hb
    have hτn : 0 < τ ^ n := pow_pos hτ0 n
    have hsn : 0 < s ^ n := pow_pos hs n
    have hA : τ ^ n ≤ s ^ n := pow_le_pow_left₀ hτ0.le ha n
    have hB : s ^ n ≤ (1 + ε) ^ n * τ ^ n := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ hs.le hb n
    refine ⟨div_le_div_of_nonneg_left hg0 hτn hA, ?_⟩
    rw [← mul_div_assoc, div_le_div_iff₀ hτn hsn]
    calc -(s / τ ^ 2) * deriv φ (s / τ) * s ^ n
        ≤ -(s / τ ^ 2) * deriv φ (s / τ) * ((1 + ε) ^ n * τ ^ n) :=
          mul_le_mul_of_nonneg_left hB hg0
      _ = (1 + ε) ^ n * (-(s / τ ^ 2) * deriv φ (s / τ)) * τ ^ n := by ring
  -- integrate the pointwise squeeze over `(σ, ρ]`
  refine ⟨?_, ?_⟩
  · calc (φ (s / ρ) - φ (s / σ)) / s ^ n
        = ∫ τ in Ioc σ ρ, -(s / τ ^ 2) * deriv φ (s / τ) / s ^ n := by
          rw [integral_div, hFTC]
      _ ≤ ∫ τ in Ioc σ ρ, -(s / τ ^ 2) * deriv φ (s / τ) / τ ^ n :=
          setIntegral_mono_on (hg'i.div_const _) hki measurableSet_Ioc fun τ hτ ↦ (hpt τ hτ).1
  · calc ∫ τ in Ioc σ ρ, -(s / τ ^ 2) * deriv φ (s / τ) / τ ^ n
        ≤ ∫ τ in Ioc σ ρ, (1 + ε) ^ n * (-(s / τ ^ 2) * deriv φ (s / τ) / s ^ n) :=
          setIntegral_mono_on hki ((hg'i.div_const _).const_mul _) measurableSet_Ioc
            fun τ hτ ↦ (hpt τ hτ).2
      _ = (1 + ε) ^ n * ((φ (s / ρ) - φ (s / σ)) / s ^ n) := by
          rw [integral_const_mul, integral_div, hFTC]

theorem main_theorem : ApproxTangentAE ∧ FirstVariationFormula ∧ StationaryIffVariational ∧ StationaryMonotonicity ∧ StationaryDensity ∧ CanonicalRepresentative ∧ BoundedCurvatureMonotonicity ∧ LogarithmicMonotonicityError ∧ LpMonotonicity ∧ LpDensity ∧ LpSupportRepresentation ∧ PoincareInequality ∧ SobolevInequality ∧ SupportInBall ∧ ConvexHullProperty ∧ ClassicalTangent := by sorry

end

end GMT.Ch04
