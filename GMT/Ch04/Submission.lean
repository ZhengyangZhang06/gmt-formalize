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

theorem main_theorem : ApproxTangentAE ∧ FirstVariationFormula ∧ StationaryIffVariational ∧ StationaryMonotonicity ∧ StationaryDensity ∧ CanonicalRepresentative ∧ BoundedCurvatureMonotonicity ∧ LogarithmicMonotonicityError ∧ LpMonotonicity ∧ LpDensity ∧ LpSupportRepresentation ∧ PoincareInequality ∧ SobolevInequality ∧ SupportInBall ∧ ConvexHullProperty ∧ ClassicalTangent := by sorry

end

end GMT.Ch04
