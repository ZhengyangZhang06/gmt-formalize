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

/-- **Unweighted monotonicity identity (Simon Ch. 4, 5.1 with `h ≡ 1`; cf. 3.16–3.18).** Given
the weighted identity (first antecedent) and the standing facts on `μ_V` (second antecedent): if
`V` has generalized mean curvature `H` in the open set `U`, `B_ρ(ξ) ⊆ U` and `0 < σ ≤ ρ`, then
`τ ↦ τ⁻ⁿ⁻¹ ∫_{B_τ(ξ)} (x - ξ) · H dμ_V` is integrable on `(σ, ρ]`, `r⁻ⁿ|D^⊥r|²` is
`μ_V`-integrable on `B_ρ(ξ) \ B_σ(ξ)`, and
`ρ⁻ⁿμ_V(B_ρ(ξ)) - σ⁻ⁿμ_V(B_σ(ξ)) = ∫_{B_ρ(ξ) \ B_σ(ξ)} r⁻ⁿ|D^⊥r|² dμ_V
  + ∫_σ^ρ τ⁻ⁿ⁻¹ ∫_{B_τ(ξ)} (x - ξ) · H dμ_V dτ`. -/
theorem Submission.mcm_unit_weight_identity : (∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)) (H : Ambient n ℓ → Ambient n ℓ) (h : Ambient n ℓ → ℝ) (ξ : Ambient n ℓ) (σ ρ : ℝ), 0 < n → IsFiniteMeasureOnCompacts V.weight → (∀ᵐ x ∂V.weight, Module.finrank ℝ (V.tangentSpace x) = n) → AEStronglyMeasurable (fun x ↦ (V.tangentSpace x).starProjection) V.weight → IsOpen U → V.HasMeanCurvatureIn U H → ContDiffOn ℝ 1 h U → tsupport h ∩ closedBall ξ ρ ⊆ U → 0 < σ → σ ≤ ρ → IntegrableOn (fun τ ↦ (∫ x in closedBall ξ τ, inner ℝ (x - ξ) (V.tangentialGradient h x + h x • H x) ∂V.weight) / τ ^ (n + 1)) (Ioc σ ρ) ∧ IntegrableOn (fun x ↦ h x * (V.normalRadialSq ξ x / ‖x - ξ‖ ^ n)) (closedBall ξ ρ \ closedBall ξ σ) V.weight ∧ (∫ x in closedBall ξ ρ, h x ∂V.weight) / ρ ^ n - (∫ x in closedBall ξ σ, h x ∂V.weight) / σ ^ n = ∫ x in closedBall ξ ρ \ closedBall ξ σ, h x * (V.normalRadialSq ξ x / ‖x - ξ‖ ^ n) ∂V.weight + ∫ τ in Ioc σ ρ, (∫ x in closedBall ξ τ, inner ℝ (x - ξ) (V.tangentialGradient h x + h x • H x) ∂V.weight) / τ ^ (n + 1)) → (∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ), 0 < n → IsFiniteMeasureOnCompacts V.weight ∧ (∀ᵐ x ∂V.weight, Module.finrank ℝ (V.tangentSpace x) = n) ∧ AEStronglyMeasurable (fun x ↦ (V.tangentSpace x).starProjection) V.weight) → ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)) (H : Ambient n ℓ → Ambient n ℓ) (ξ : Ambient n ℓ) (σ ρ : ℝ), 0 < n → IsOpen U → V.HasMeanCurvatureIn U H → closedBall ξ ρ ⊆ U → 0 < σ → σ ≤ ρ → IntegrableOn (fun τ ↦ (∫ x in closedBall ξ τ, inner ℝ (x - ξ) (H x) ∂V.weight) / τ ^ (n + 1)) (Ioc σ ρ) ∧ IntegrableOn (fun x ↦ V.normalRadialSq ξ x / ‖x - ξ‖ ^ n) (closedBall ξ ρ \ closedBall ξ σ) V.weight ∧ V.weight.real (closedBall ξ ρ) / ρ ^ n - V.weight.real (closedBall ξ σ) / σ ^ n = ∫ x in closedBall ξ ρ \ closedBall ξ σ, V.normalRadialSq ξ x / ‖x - ξ‖ ^ n ∂V.weight + ∫ τ in Ioc σ ρ, (∫ x in closedBall ξ τ, inner ℝ (x - ξ) (H x) ∂V.weight) / τ ^ (n + 1) := by
  intro WMI GF n ℓ V U H ξ σ ρ hn hU hH hball hσ hσρ
  -- (GF) supplies the geometric hypotheses of (WMI) for `V`.
  obtain ⟨hfin, hdim, hmeas⟩ := GF n ℓ V hn
  -- Apply (WMI) to `h ≡ 1`: it is `C¹` on `U`, and `tsupport h ∩ B_ρ(ξ) ⊆ B_ρ(ξ) ⊆ U`.
  obtain ⟨h1, h2, h3⟩ := WMI n ℓ V U H (fun _ ↦ 1) ξ σ ρ hn hfin hdim hmeas hU hH contDiffOn_const
    (fun x hx ↦ hball hx.2) hσ hσρ
  -- `∇^M 1 = p_{T_x V}(∇1) = p_{T_x V}(0) = 0`.
  have hgrad : ∀ x, V.tangentialGradient (fun _ ↦ (1 : ℝ)) x = 0 := fun x ↦ by
    simp [RectifiableVarifold.tangentialGradient, gradient_fun_const]
  -- Simplify `0 + 1 • H = H`, `1 * w = w` and `∫_{B_t} 1 dμ_V = μ_V(B_t)`.
  simp only [hgrad, zero_add, one_smul, one_mul, setIntegral_const, smul_eq_mul, mul_one]
    at h1 h2 h3
  exact ⟨h1, h2, h3⟩
/-- **Fubini exchange for a primitive along a measurable radius** (common core of the annulus
integration by parts in Simon Ch. 4, 3.17 and 4.4/4.7). Put `μ = λ ⌞ (σ, ρ]`, `ν_S = ν ⌞ S` and
`Φ (t, x) = 1_{t < r x} F' t g x`; then `Φ` is `μ ⊗ ν_S`-integrable (`Integrable.mul_prod`, the
set `{t < r x}` is product-measurable). Its `t`-sections integrate to
`F' t ∫_{S ∩ {t < r}} g dν`, and for `x ∈ S` (where `(σ, ρ] ∩ (-∞, r x) = (σ, r x)`) its
`x`-sections integrate to `g x ∫_{(σ, r x]} F' = g x (F (r x) - F σ)`; Fubini
(`integral_integral_swap`, valid for s-finite factors) gives all three claims. -/
theorem Submission.mcm_primitive_radial_fubini : ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) (S : Set X) (r g : X → ℝ) (F F' : ℝ → ℝ) (σ ρ : ℝ), SFinite ν → MeasurableSet S → Measurable r → (∀ x ∈ S, r x ∈ Ioc σ ρ) → IntegrableOn g S ν → IntegrableOn F' (Ioc σ ρ) → (∀ t ∈ Icc σ ρ, F t = F σ + ∫ τ in Ioc σ t, F' τ) → IntegrableOn (fun x ↦ g x * (F (r x) - F σ)) S ν ∧ IntegrableOn (fun t ↦ F' t * ∫ x in S ∩ {x | t < r x}, g x ∂ν) (Ioc σ ρ) ∧ ∫ t in Ioc σ ρ, F' t * ∫ x in S ∩ {x | t < r x}, g x ∂ν = ∫ x in S, g x * (F (r x) - F σ) ∂ν := by
  intro X _ ν S r g F F' σ ρ hν hS hr hrS hg hF' hF
  -- the product integrand `Φ (t, x) = 1_{t < r x} F' t g x` on `(σ, ρ] × S`
  obtain ⟨Φ, hΦ_def⟩ : ∃ Φ : ℝ × X → ℝ,
      Φ = {z : ℝ × X | z.1 < r z.2}.indicator fun z ↦ F' z.1 * g z.2 := ⟨_, rfl⟩
  have hT : MeasurableSet {z : ℝ × X | z.1 < r z.2} :=
    measurableSet_lt measurable_fst (hr.comp measurable_snd)
  have hΦ : Integrable Φ ((volume.restrict (Ioc σ ρ)).prod (ν.restrict S)) := by
    rw [hΦ_def]
    exact (Integrable.mul_prod hF' hg).indicator hT
  -- sections at fixed `t`
  have ht : ∀ t : ℝ,
      ∫ x, Φ (t, x) ∂ν.restrict S = F' t * ∫ x in S ∩ {x | t < r x}, g x ∂ν := by
    intro t
    have h : ∀ x, Φ (t, x) = F' t * {x | t < r x}.indicator g x := by
      intro x
      rw [hΦ_def]
      by_cases htx : t < r x
      · simp [htx]
      · simp [htx]
    simp_rw [h]
    rw [integral_const_mul, setIntegral_indicator (measurableSet_lt measurable_const hr)]
  -- sections at fixed `x ∈ S`
  have hx : ∀ x ∈ S,
      ∫ t, Φ (t, x) ∂volume.restrict (Ioc σ ρ) = g x * (F (r x) - F σ) := by
    intro x hxS
    obtain ⟨h1, h2⟩ := hrS x hxS
    have h : ∀ t, Φ (t, x) = (Iio (r x)).indicator F' t * g x := by
      intro t
      rw [hΦ_def]
      by_cases htx : t < r x
      · simp [htx]
      · simp [htx]
    simp_rw [h]
    have hset : Ioc σ ρ ∩ Iio (r x) = Ioo σ (r x) := by
      ext t
      simp only [mem_inter_iff, mem_Ioc, mem_Iio, mem_Ioo]
      constructor
      · rintro ⟨⟨h3, -⟩, h4⟩
        exact ⟨h3, h4⟩
      · rintro ⟨h3, h4⟩
        exact ⟨⟨h3, (h4.trans_le h2).le⟩, h4⟩
    rw [integral_mul_const, setIntegral_indicator measurableSet_Iio, hset,
      ← integral_Ioc_eq_integral_Ioo, hF (r x) ⟨h1.le, h2⟩]
    ring
  refine ⟨?_, ?_, ?_⟩
  · -- (a): the `x`-integrals are `ν ⌞ S`-integrable and agree with the integrand on `S`
    refine hΦ.integral_prod_right.congr ?_
    filter_upwards [ae_restrict_mem hS] with x hxS
    exact hx x hxS
  · -- (b): the `t`-integrals are `λ ⌞ (σ, ρ]`-integrable
    have h := hΦ.integral_prod_left
    simp only [ht] at h
    exact h
  · -- (c): Fubini
    calc ∫ t in Ioc σ ρ, F' t * ∫ x in S ∩ {x | t < r x}, g x ∂ν
        = ∫ t in Ioc σ ρ, ∫ x in S, Φ (t, x) ∂ν := by simp only [ht]
      _ = ∫ x in S, (∫ t in Ioc σ ρ, Φ (t, x)) ∂ν :=
          integral_integral_swap (f := fun t x ↦ Φ (t, x)) hΦ
      _ = ∫ x in S, g x * (F (r x) - F σ) ∂ν := setIntegral_congr_fun hS hx
/-- **Integrating-factor FTC** (Simon Ch. 4, 3.17 and 4.4/4.7: `F = exp (-∫_{(0,τ]} g)` is
absolutely continuous with `F' = -gF`). For `g` integrable on `(0, R]`, `-gF` is integrable on
`(0, R]` and `F t = F σ + ∫_{(σ,t]} -gF` for `0 ≤ σ ≤ t ≤ R`. `F` is continuous on `[0, R]`; if
`|F - F x| ≤ c` on `[x, z]`, then with `a = ∫_x^z g` and `0 ≤ e^{-a} - 1 + a ≤ a (1 - e^{-a})`,
`|F z - F x + ∫_x^z gF| ≤ 2c ∫_x^z |g|`, and real induction on `[σ, t]` gives
`|F t - F σ + ∫_σ^t gF| ≤ 2c ∫_σ^t |g|` for every `c > 0`. -/
theorem Submission.mcm_exp_neg_integral_ftc : ∀ (g : ℝ → ℝ) (R : ℝ), IntegrableOn g (Ioc 0 R) → IntegrableOn (fun τ ↦ -(g τ * Real.exp (-∫ s in Ioc 0 τ, g s))) (Ioc 0 R) ∧ ∀ σ t : ℝ, 0 ≤ σ → σ ≤ t → t ≤ R → Real.exp (-∫ s in Ioc 0 t, g s) = Real.exp (-∫ s in Ioc 0 σ, g s) + ∫ τ in Ioc σ t, -(g τ * Real.exp (-∫ s in Ioc 0 τ, g s)) := by
  intro g R hg
  -- `Φ τ = ∫_{(0,τ]} g` and the integrating factor `F = exp (-Φ)`
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℝ → ℝ, Φ = fun τ ↦ ∫ s in Ioc 0 τ, g s := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ, F = fun τ ↦ Real.exp (-Φ τ) := ⟨_, rfl⟩
  have hFτ : ∀ τ, Real.exp (-∫ s in Ioc 0 τ, g s) = F τ := fun τ ↦ by rw [hF, hΦ]
  simp only [hFτ]
  have hgIcc : IntegrableOn g (Icc 0 R) :=
    (integrableOn_Icc_iff_integrableOn_Ioc (f := g) (a := 0) (b := R) (μ := volume)).2 hg
  -- `Φ`, hence `F`, is continuous on `[0, R]`, so `g F` is integrable there
  have hΦc : ContinuousOn Φ (Icc 0 R) := by
    rw [hΦ]
    exact intervalIntegral.continuousOn_primitive hgIcc
  have hFc : ContinuousOn F (Icc 0 R) := by
    rw [hF]
    exact Real.continuous_exp.comp_continuousOn hΦc.neg
  have hgF : IntegrableOn (fun τ ↦ g τ * F τ) (Icc 0 R) :=
    hgIcc.mul_continuousOn hFc isCompact_Icc
  refine ⟨(hgF.mono_set Ioc_subset_Icc_self).fun_neg, ?_⟩
  intro σ t hσ hσt htR
  have hag : IntegrableOn (fun τ ↦ |g τ|) (Icc 0 R) := Integrable.abs hgIcc
  have hII : ∀ f : ℝ → ℝ, IntegrableOn f (Icc 0 R) → ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ R →
      IntervalIntegrable f volume u v := fun f hf u v hu huv hv ↦
    (intervalIntegrable_iff_integrableOn_Icc_of_le huv).2 (hf.mono_set (Icc_subset_Icc hu hv))
  have hΦi : ∀ x, 0 ≤ x → Φ x = ∫ s in (0)..x, g s := fun x hx ↦ by
    rw [hΦ, intervalIntegral.integral_of_le hx]
  -- convexity of `exp`: `0 ≤ e^{-a} - 1 + a ≤ a (1 - e^{-a})`
  have hconv : ∀ a : ℝ, |Real.exp (-a) - 1 + a| ≤ |a| * |1 - Real.exp (-a)| := by
    intro a
    have h1 := Real.add_one_le_exp (-a)
    have h2 := Real.add_one_le_exp a
    have h3 : Real.exp (-a) * Real.exp a = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have h4 := mul_le_mul_of_nonneg_left h2 (Real.exp_pos (-a)).le
    rw [abs_of_nonneg (show (0 : ℝ) ≤ Real.exp (-a) - 1 + a by linarith)]
    calc Real.exp (-a) - 1 + a ≤ a * (1 - Real.exp (-a)) := by nlinarith
      _ ≤ |a * (1 - Real.exp (-a))| := le_abs_self _
      _ = |a| * |1 - Real.exp (-a)| := abs_mul _ _
  -- local estimate: if `F` is `c`-close to `F x` on `[x, z]`, the defect over `[x, z]` is small
  have hstep : ∀ c : ℝ, 0 < c → ∀ x z : ℝ, σ ≤ x → x ≤ z → z ≤ t →
      (∀ τ ∈ Icc x z, |F τ - F x| ≤ c) →
      |F z - F x + ∫ τ in x..z, g τ * F τ| ≤ 2 * c * ∫ τ in x..z, |g τ| := by
    intro c hc x z hσx hxz hzt hFxz
    have hx0 : 0 ≤ x := hσ.trans hσx
    have hzR : z ≤ R := hzt.trans htR
    have hgxz := hII g hgIcc x z hx0 hxz hzR
    have hgFxz := hII _ hgF x z hx0 hxz hzR
    have hagxz := hII _ hag x z hx0 hxz hzR
    set a := ∫ τ in x..z, g τ with ha
    have hFz : F z = F x * Real.exp (-a) := by
      have h1 : Φ z = Φ x + a := by
        rw [hΦi z (hx0.trans hxz), hΦi x hx0, ha,
          intervalIntegral.integral_add_adjacent_intervals
            (hII g hgIcc 0 x le_rfl hx0 (hxz.trans hzR)) hgxz]
      simp only [hF]
      rw [h1, neg_add, Real.exp_add]
    have hsplit : ∫ τ in x..z, g τ * F τ = (∫ τ in x..z, g τ * (F τ - F x)) + F x * a := by
      have h : ∫ τ in x..z, g τ * (F τ - F x) = (∫ τ in x..z, g τ * F τ) - a * F x := by
        simp_rw [mul_sub]
        rw [intervalIntegral.integral_sub hgFxz (hgxz.mul_const _),
          intervalIntegral.integral_mul_const]
      rw [h]
      ring
    have hbound1 : |∫ τ in x..z, g τ * (F τ - F x)| ≤ c * ∫ τ in x..z, |g τ| := by
      rw [← intervalIntegral.integral_const_mul]
      show ‖∫ τ in x..z, g τ * (F τ - F x)‖ ≤ ∫ τ in x..z, c * |g τ|
      refine intervalIntegral.norm_integral_le_of_norm_le hxz
        (ae_of_all _ fun τ hτ ↦ ?_) (hagxz.const_mul c)
      rw [Real.norm_eq_abs, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hFxz τ (Ioc_subset_Icc_self hτ)) (abs_nonneg _)
    have hbound2 : |a| ≤ ∫ τ in x..z, |g τ| := by
      have h := intervalIntegral.norm_integral_le_integral_norm (f := g) (μ := volume) hxz
      simpa only [Real.norm_eq_abs] using h
    have hFx : 0 < F x := by
      rw [hF]
      exact Real.exp_pos _
    have hbound3 : |F z - F x + F x * a| ≤ |a| * c := by
      have hFzx : |F x - F z| ≤ c := by
        rw [abs_sub_comm]
        exact hFxz z ⟨hxz, le_rfl⟩
      calc |F z - F x + F x * a| = F x * |Real.exp (-a) - 1 + a| := by
            rw [hFz, show F x * Real.exp (-a) - F x + F x * a
                = F x * (Real.exp (-a) - 1 + a) by ring, abs_mul, abs_of_pos hFx]
        _ ≤ F x * (|a| * |1 - Real.exp (-a)|) := mul_le_mul_of_nonneg_left (hconv a) hFx.le
        _ = |a| * |F x - F z| := by
            rw [hFz, show F x - F x * Real.exp (-a) = F x * (1 - Real.exp (-a)) by ring, abs_mul,
              abs_of_pos hFx]
            ring
        _ ≤ |a| * c := mul_le_mul_of_nonneg_left hFzx (abs_nonneg _)
    calc |F z - F x + ∫ τ in x..z, g τ * F τ|
        = |(F z - F x + F x * a) + ∫ τ in x..z, g τ * (F τ - F x)| := by
          rw [hsplit]
          congr 1
          ring
      _ ≤ |F z - F x + F x * a| + |∫ τ in x..z, g τ * (F τ - F x)| := abs_add_le _ _
      _ ≤ |a| * c + c * ∫ τ in x..z, |g τ| := add_le_add hbound3 hbound1
      _ ≤ 2 * c * ∫ τ in x..z, |g τ| := by nlinarith
  -- the defect `D x = F x - F σ + ∫_σ^x g F` and the weight `J x = ∫_σ^x |g|`
  obtain ⟨D, hD⟩ : ∃ D : ℝ → ℝ, D = fun x ↦ F x - F σ + ∫ τ in σ..x, g τ * F τ := ⟨_, rfl⟩
  obtain ⟨J, hJ⟩ : ∃ J : ℝ → ℝ, J = fun x ↦ ∫ τ in σ..x, |g τ| := ⟨_, rfl⟩
  have hsub : Icc σ t ⊆ Icc 0 R := Icc_subset_Icc hσ htR
  have huIcc : uIcc σ t = Icc σ t := uIcc_of_le hσt
  have hDc : ContinuousOn D (Icc σ t) := by
    have h1 : IntegrableOn (fun τ ↦ g τ * F τ) (uIcc σ t) := by
      rw [huIcc]
      exact hgF.mono_set hsub
    have h := intervalIntegral.continuousOn_primitive_interval h1
    rw [huIcc] at h
    rw [hD]
    exact ((hFc.mono hsub).sub continuousOn_const).add h
  have hJc : ContinuousOn J (Icc σ t) := by
    have h1 : IntegrableOn (fun τ ↦ |g τ|) (uIcc σ t) := by
      rw [huIcc]
      exact hag.mono_set hsub
    have h := intervalIntegral.continuousOn_primitive_interval h1
    rw [huIcc] at h
    rw [hJ]
    exact h
  have hDσ : D σ = 0 := by
    rw [hD]
    simp
  have hJσ : J σ = 0 := by
    rw [hJ]
    simp
  -- real induction on `[σ, t]`: `|D| ≤ 2 c J` for every `c > 0`
  have hmain : ∀ c : ℝ, 0 < c → |D t| ≤ 2 * c * J t := by
    intro c hc
    let s : Set ℝ := (fun x ↦ 2 * c * J x - |D x|) ⁻¹' Ici 0
    have hs : IsClosed (s ∩ Icc σ t) := by
      rw [inter_comm]
      exact ContinuousOn.preimage_isClosed_of_isClosed
        ((continuousOn_const.mul hJc).sub hDc.abs) isClosed_Icc isClosed_Ici
    have hmem : t ∈ s := by
      refine hs.mem_of_ge_of_forall_exists_gt ?_ hσt ?_
      · show 0 ≤ 2 * c * J σ - |D σ|
        rw [hDσ, hJσ]
        simp
      · rintro x ⟨hxs, hσx, hxt⟩
        have hxs' : |D x| ≤ 2 * c * J x := by
          have h : 0 ≤ 2 * c * J x - |D x| := hxs
          linarith
        have hx0 : 0 ≤ x := hσ.trans hσx
        obtain ⟨δ, hδ, hFδ⟩ :=
          Metric.continuousWithinAt_iff.1 (hFc x ⟨hx0, hxt.le.trans htR⟩) c hc
        obtain ⟨z, hz⟩ : ∃ z : ℝ, z = min t (x + δ / 2) := ⟨_, rfl⟩
        have hxz : x < z := by
          rw [hz]
          exact lt_min hxt (by linarith)
        have hzt : z ≤ t := by
          rw [hz]
          exact min_le_left _ _
        have hzδ : z ≤ x + δ / 2 := by
          rw [hz]
          exact min_le_right _ _
        refine ⟨z, ?_, hxz, hzt⟩
        have hloc := hstep c hc x z hσx hxz.le hzt (fun τ hτ ↦ by
          have hτR : τ ∈ Icc 0 R := ⟨hx0.trans hτ.1, hτ.2.trans (hzt.trans htR)⟩
          have hd : dist τ x < δ := by
            rw [Real.dist_eq, abs_of_nonneg (by linarith [hτ.1])]
            linarith [hτ.2]
          have h := hFδ hτR hd
          rw [Real.dist_eq] at h
          exact h.le)
        have hDz : D z = D x + (F z - F x + ∫ τ in x..z, g τ * F τ) := by
          simp only [hD]
          rw [← intervalIntegral.integral_add_adjacent_intervals
            (hII _ hgF σ x hσ hσx (hxt.le.trans htR)) (hII _ hgF x z hx0 hxz.le (hzt.trans htR))]
          ring
        have hJz : J z = J x + ∫ τ in x..z, |g τ| := by
          simp only [hJ]
          rw [intervalIntegral.integral_add_adjacent_intervals
            (hII _ hag σ x hσ hσx (hxt.le.trans htR)) (hII _ hag x z hx0 hxz.le (hzt.trans htR))]
        show 0 ≤ 2 * c * J z - |D z|
        rw [hDz, hJz]
        have h := abs_add_le (D x) (F z - F x + ∫ τ in x..z, g τ * F τ)
        nlinarith
    have h : 0 ≤ 2 * c * J t - |D t| := hmem
    linarith
  have hJt : 0 ≤ J t := by
    rw [hJ]
    exact intervalIntegral.integral_nonneg hσt fun τ _ ↦ abs_nonneg _
  have hDt : D t = 0 := by
    by_contra hne
    have hpos : 0 < |D t| := abs_pos.2 hne
    have h4 : 0 < 4 * (J t + 1) := by linarith
    obtain ⟨c, hc⟩ : ∃ c : ℝ, c = |D t| / (4 * (J t + 1)) := ⟨_, rfl⟩
    have hc0 : 0 < c := by
      rw [hc]
      exact div_pos hpos h4
    have hcJ : c * (4 * (J t + 1)) = |D t| := by
      rw [hc]
      exact div_mul_cancel₀ _ h4.ne'
    have h := hmain c hc0
    nlinarith
  rw [← intervalIntegral.integral_of_le hσt, intervalIntegral.integral_neg]
  rw [hD] at hDt
  simp only at hDt
  linarith
/-- **Density from uniformly almost-monotone ratios (Simon 3.17 remark, 4.9).** Let `μ_V` be finite
on compact sets. If every `ξ ∈ U` has `r > 0` and `c(ρ) → 0` (`ρ ↓ 0`) such that for every centre
`η` with `|η - ξ| < r`, some `F ∈ [e^{-c}, e^{c}]` and `|E| ≤ c` make
`ρ ↦ F(ρ) μ_V(B_ρ(η))/ρⁿ + E(ρ)` nondecreasing on `(0, r)`, then `Θⁿ(μ_V, ξ)` exists at every
`ξ ∈ U` and `Θⁿ(μ_V, ·)` is upper semicontinuous on `U`. -/
theorem Submission.mcm_density_usc_of_monotone : ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)), IsFiniteMeasureOnCompacts V.weight → (∀ ξ ∈ U, ∃ r : ℝ, 0 < r ∧ ∃ c : ℝ → ℝ, Tendsto c (𝓝[>] 0) (𝓝 0) ∧ ∀ η ∈ ball ξ r, ∃ F E : ℝ → ℝ, (∀ ρ ∈ Ioo 0 r, F ρ ∈ Icc (Real.exp (-c ρ)) (Real.exp (c ρ)) ∧ |E ρ| ≤ c ρ) ∧ MonotoneOn (fun ρ ↦ F ρ * (V.weight.real (closedBall η ρ) / ρ ^ n) + E ρ) (Ioo 0 r)) → (∀ ξ ∈ U, V.HasDensityAt ξ (V.density ξ)) ∧ UpperSemicontinuousOn V.density U := by
  intro n ℓ V U _ hU
  -- `ωₙ > 0`: the open unit ball of `ℝⁿ` is nonempty and bounded.
  have hω : 0 < omega n :=
    ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne
  -- Step 1: from the data at a centre `η`, `a_η(ρ) = μ_V(B_ρ(η))/ρⁿ → ωₙ Θ(η)`, the density
  -- exists at `η`, and `ωₙ Θ(η) ≤ e^{c(ρ)} a_η(ρ) + c(ρ)` for `0 < ρ < r`.
  have key : ∀ (η : Ambient n ℓ) (r : ℝ) (c F E : ℝ → ℝ), 0 < r → Tendsto c (𝓝[>] 0) (𝓝 0) →
      (∀ ρ ∈ Ioo 0 r, F ρ ∈ Icc (Real.exp (-c ρ)) (Real.exp (c ρ)) ∧ |E ρ| ≤ c ρ) →
      MonotoneOn (fun ρ ↦ F ρ * (V.weight.real (closedBall η ρ) / ρ ^ n) + E ρ) (Ioo 0 r) →
      V.HasDensityAt η (V.density η) ∧
      Tendsto (fun ρ ↦ V.weight.real (closedBall η ρ) / ρ ^ n) (𝓝[>] 0)
        (𝓝 (omega n * V.density η)) ∧
      ∀ ρ ∈ Ioo 0 r, omega n * V.density η ≤
        Real.exp (c ρ) * (V.weight.real (closedBall η ρ) / ρ ^ n) + c ρ := by
    intro η r c F E hr hc hFE hmono
    set a : ℝ → ℝ := fun ρ ↦ V.weight.real (closedBall η ρ) / ρ ^ n
    set Ψ : ℝ → ℝ := fun ρ ↦ F ρ * a ρ + E ρ
    have hΨm : MonotoneOn Ψ (Ioo 0 r) := hmono
    have ha0 : ∀ ρ, 0 < ρ → 0 ≤ a ρ := fun ρ hρ ↦ div_nonneg measureReal_nonneg (pow_nonneg hρ.le n)
    have hIoo : Ioo 0 r ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hr
    -- `Ψ ≥ -c` on `(0, r)`, since `F > 0`, `a ≥ 0` and `E ≥ -|E| ≥ -c`.
    have hΨc : ∀ ρ ∈ Ioo 0 r, -c ρ ≤ Ψ ρ := fun ρ hρ ↦ by
      have h1 : 0 ≤ F ρ * a ρ :=
        mul_nonneg ((Real.exp_pos _).le.trans (hFE ρ hρ).1.1) (ha0 ρ hρ.1)
      have h2 := neg_abs_le (E ρ)
      have h3 := (hFE ρ hρ).2
      show -c ρ ≤ F ρ * a ρ + E ρ
      linarith
    -- `Ψ ≥ -1` on `(0, r)`: below `ρ` there is `σ` with `c(σ) ≤ 1`, and `Ψ` is monotone.
    have hbdd : BddBelow (Ψ '' Ioo 0 r) := by
      refine ⟨-1, ?_⟩
      rintro _ ⟨ρ, hρ, rfl⟩
      obtain ⟨σ, hσc, hσ⟩ :=
        ((hc.eventually (Iic_mem_nhds zero_lt_one)).and (Ioo_mem_nhdsGT hρ.1)).exists
      have hσr : σ ∈ Ioo 0 r := ⟨hσ.1, hσ.2.trans hρ.2⟩
      calc (-1 : ℝ) ≤ -c σ := neg_le_neg hσc
        _ ≤ Ψ σ := hΨc σ hσr
        _ ≤ Ψ ρ := hΨm hσr hρ hσ.2.le
    -- (a) the monotone function `Ψ` converges as `ρ ↓ 0`.
    have hΨlim := hΨm.tendsto_nhdsWithin_Ioo_right (nonempty_Ioo.2 hr) hbdd
    set L := sInf (Ψ '' Ioo 0 r)
    -- (b) `F → 1`, `E → 0`, hence `a = (Ψ - E)/F → L`.
    have hF1 : Tendsto F (𝓝[>] 0) (𝓝 1) := by
      have h1 : Tendsto (fun ρ ↦ Real.exp (-c ρ)) (𝓝[>] 0) (𝓝 1) := by
        simpa [Function.comp_def] using (Real.continuous_exp.tendsto _).comp hc.neg
      have h2 : Tendsto (fun ρ ↦ Real.exp (c ρ)) (𝓝[>] 0) (𝓝 1) := by
        simpa [Function.comp_def] using (Real.continuous_exp.tendsto _).comp hc
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h1 h2 ?_ ?_
      · filter_upwards [hIoo] with ρ hρ using (hFE ρ hρ).1.1
      · filter_upwards [hIoo] with ρ hρ using (hFE ρ hρ).1.2
    have hE0 : Tendsto E (𝓝[>] 0) (𝓝 0) := by
      refine squeeze_zero_norm' ?_ hc
      filter_upwards [hIoo] with ρ hρ
      rw [Real.norm_eq_abs]
      exact (hFE ρ hρ).2
    have ha : Tendsto a (𝓝[>] 0) (𝓝 L) := by
      have h := (hΨlim.sub hE0).div hF1 one_ne_zero
      rw [sub_zero, div_one] at h
      refine h.congr' ?_
      filter_upwards [hIoo] with ρ hρ
      have hFpos : 0 < F ρ := (Real.exp_pos _).trans_le (hFE ρ hρ).1.1
      show (F ρ * a ρ + E ρ - E ρ) / F ρ = a ρ
      rw [add_sub_cancel_right, mul_div_cancel_left₀ _ hFpos.ne']
    -- (c) `μ_V(B_ρ(η))/(ωₙρⁿ) = a(ρ)/ωₙ → L/ωₙ`, so `Θ(η) = L/ωₙ` exists.
    have hdens : Tendsto (fun ρ ↦ V.weight.real (closedBall η ρ) / (omega n * ρ ^ n)) (𝓝[>] 0)
        (𝓝 (L / omega n)) := by
      refine (ha.div_const (omega n)).congr fun ρ ↦ ?_
      show V.weight.real (closedBall η ρ) / ρ ^ n / omega n =
        V.weight.real (closedBall η ρ) / (omega n * ρ ^ n)
      rw [div_mul_eq_div_div_swap]
    have hdeq : V.density η = L / omega n := hdens.limUnder_eq
    have hωd : omega n * V.density η = L := by rw [hdeq, mul_div_cancel₀ _ hω.ne']
    refine ⟨?_, ?_, ?_⟩
    · show Tendsto _ _ _
      rw [hdeq]
      exact hdens
    · rw [hωd]
      exact ha
    · -- (d) `ωₙ Θ(η) = L ≤ Ψ(ρ) ≤ e^{c(ρ)} a(ρ) + c(ρ)`.
      intro ρ hρ
      rw [hωd]
      have hLΨ : L ≤ Ψ ρ := by
        refine le_of_tendsto hΨlim ?_
        filter_upwards [Ioo_mem_nhdsGT hρ.1] with σ hσ
        exact hΨm ⟨hσ.1, hσ.2.trans hρ.2⟩ hρ hσ.2.le
      calc L ≤ Ψ ρ := hLΨ
        _ = F ρ * a ρ + E ρ := rfl
        _ ≤ Real.exp (c ρ) * a ρ + c ρ :=
          add_le_add (mul_le_mul_of_nonneg_right (hFE ρ hρ).1.2 (ha0 ρ hρ.1))
            ((le_abs_self _).trans (hFE ρ hρ).2)
  refine ⟨fun ξ hξ ↦ ?_, upperSemicontinuousOn_iff.2 fun ξ hξ ↦
    upperSemicontinuousWithinAt_iff.2 fun t ht ↦ ?_⟩
  · -- Step 2: existence of the density at `ξ ∈ U` (take `η = ξ`).
    obtain ⟨r, hr, c, hc, hη⟩ := hU ξ hξ
    obtain ⟨F, E, hFE, hmono⟩ := hη ξ (mem_ball_self hr)
    exact (key ξ r c F E hr hc hFE hmono).1
  · -- Step 3: upper semicontinuity at `ξ ∈ U`; fix `t > Θ(ξ)`.
    obtain ⟨r, hr, c, hc, hη⟩ := hU ξ hξ
    obtain ⟨F, E, hFE, hmono⟩ := hη ξ (mem_ball_self hr)
    have ha := (key ξ r c F E hr hc hFE hmono).2.1
    -- `e^{c(ρ)} a_ξ(ρ) + c(ρ) → ωₙ Θ(ξ) < ωₙ t`: fix such a `ρ ∈ (0, r)`.
    have h1 : Tendsto (fun ρ ↦ Real.exp (c ρ) * (V.weight.real (closedBall ξ ρ) / ρ ^ n) + c ρ)
        (𝓝[>] 0) (𝓝 (omega n * V.density ξ)) := by
      simpa using (((Real.continuous_exp.tendsto 0).comp hc).mul ha).add hc
    obtain ⟨ρ, hρt, hρ⟩ := ((h1.eventually (gt_mem_nhds (mul_lt_mul_of_pos_left ht hω))).and
      (Ioo_mem_nhdsGT hr)).exists
    -- Continuity from above: `μ_V(B_{ρ+δ}(ξ)) → μ_V(B_ρ(ξ))` as `δ ↓ 0`.
    have h2 : Tendsto (fun δ ↦ V.weight.real (closedBall ξ (ρ + δ))) (𝓝[>] 0)
        (𝓝 (V.weight.real (closedBall ξ ρ))) := by
      have hinter : ⋂ δ > (0 : ℝ), closedBall ξ (ρ + δ) = closedBall ξ ρ := by
        ext x
        simp only [mem_iInter, mem_closedBall]
        exact ⟨fun h ↦ le_of_forall_pos_le_add h, fun hx δ hδ ↦ by linarith⟩
      have h := tendsto_measure_biInter_gt (μ := V.weight) (s := fun δ ↦ closedBall ξ (ρ + δ))
        (a := (0 : ℝ)) (fun _ _ ↦ measurableSet_closedBall.nullMeasurableSet)
        (fun _ _ _ hij ↦ closedBall_subset_closedBall (by linarith))
        ⟨1, one_pos, measure_closedBall_lt_top.ne⟩
      rw [hinter] at h
      exact (ENNReal.tendsto_toReal measure_closedBall_lt_top.ne).comp h
    have h3 : Tendsto (fun δ ↦ Real.exp (c ρ) * (V.weight.real (closedBall ξ (ρ + δ)) / ρ ^ n) +
        c ρ) (𝓝[>] 0) (𝓝 (Real.exp (c ρ) * (V.weight.real (closedBall ξ ρ) / ρ ^ n) + c ρ)) :=
      ((h2.div_const _).const_mul _).add_const _
    obtain ⟨δ, hδt, hδ⟩ := ((h3.eventually (gt_mem_nhds hρt)).and (Ioo_mem_nhdsGT hr)).exists
    -- Every `η` with `|η - ξ| < δ` has `Θ(η) < t`, by step 1(d) and `B_ρ(η) ⊆ B_{ρ+δ}(ξ)`.
    filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds ξ hδ.1)] with η hηδ
    obtain ⟨F', E', hFE', hmono'⟩ := hη η (ball_subset_ball hδ.2.le hηδ)
    have hsub : closedBall η ρ ⊆ closedBall ξ (ρ + δ) :=
      closedBall_subset_closedBall' (by rw [mem_ball] at hηδ; linarith)
    have hlt : omega n * V.density η < omega n * t :=
      calc omega n * V.density η
          ≤ Real.exp (c ρ) * (V.weight.real (closedBall η ρ) / ρ ^ n) + c ρ :=
            (key η r c F' E' hr hc hFE' hmono').2.2 ρ hρ
        _ ≤ Real.exp (c ρ) * (V.weight.real (closedBall ξ (ρ + δ)) / ρ ^ n) + c ρ :=
            add_le_add (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
              (measureReal_mono hsub measure_closedBall_lt_top.ne) (pow_nonneg hρ.1.le n))
              (Real.exp_pos _).le) le_rfl
        _ < omega n * t := hδt
    exact lt_of_mul_lt_mul_left hlt hω.le
/-- **Ch. 4, 3.18 (p. 93) from the unit-weight identity.** Assume, for `0 < σ ≤ ρ` with
`B_ρ(ξ) ⊆ U`, the identity
`ρ⁻ⁿμ_V(B_ρ(ξ)) - σ⁻ⁿμ_V(B_σ(ξ)) = ∫_{B_ρ(ξ) \ B_σ(ξ)} r⁻ⁿ|D^⊥r|² dμ_V + ∫_σ^ρ e(τ) dτ`,
`e(τ) = τ^{-n-1} ∫_{B_τ(ξ)} (x - ξ) · H dμ_V`. Since `|(x - ξ) · H| ≤ τ|H|` on `B_τ(ξ)`,
`|e(τ)| ≤ τ⁻¹ · τ^{1-n} ∫_{B_τ(ξ)} |H| dμ_V ≤ δ/τ`, and `∫_σ^ρ δ/τ dτ = δ log(ρ/σ)`. -/
theorem Submission.mcm_log_error_of_identity : (∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)) (H : Ambient n ℓ → Ambient n ℓ) (ξ : Ambient n ℓ) (σ ρ : ℝ), 0 < n → IsOpen U → V.HasMeanCurvatureIn U H → closedBall ξ ρ ⊆ U → 0 < σ → σ ≤ ρ → IntegrableOn (fun τ ↦ (∫ x in closedBall ξ τ, inner ℝ (x - ξ) (H x) ∂V.weight) / τ ^ (n + 1)) (Ioc σ ρ) ∧ IntegrableOn (fun x ↦ V.normalRadialSq ξ x / ‖x - ξ‖ ^ n) (closedBall ξ ρ \ closedBall ξ σ) V.weight ∧ V.weight.real (closedBall ξ ρ) / ρ ^ n - V.weight.real (closedBall ξ σ) / σ ^ n = ∫ x in closedBall ξ ρ \ closedBall ξ σ, V.normalRadialSq ξ x / ‖x - ξ‖ ^ n ∂V.weight + ∫ τ in Ioc σ ρ, (∫ x in closedBall ξ τ, inner ℝ (x - ξ) (H x) ∂V.weight) / τ ^ (n + 1)) → LogarithmicMonotonicityError := by
  intro hUI n ℓ V U H ξ σ ρ δ hn hU hH hρU hσ hσρ hδ
  obtain ⟨-, -, hid⟩ := hUI n ℓ V U H ξ σ ρ hn hU hH hρU hσ hσρ.le
  -- Step 1: by the identity, the quantity inside the absolute value is `∫_{(σ,ρ]} e`.
  have key : V.weight.real (closedBall ξ ρ) / ρ ^ n - V.weight.real (closedBall ξ σ) / σ ^ n -
      ∫ x in closedBall ξ ρ \ closedBall ξ σ, V.normalRadialSq ξ x / ‖x - ξ‖ ^ n ∂V.weight =
      ∫ τ in Ioc σ ρ, (∫ x in closedBall ξ τ, inner ℝ (x - ξ) (H x) ∂V.weight) / τ ^ (n + 1) := by
    rw [hid]; ring
  rw [key]
  -- Step 2: `|e(τ)| ≤ δ / τ` for `τ ∈ (σ, ρ]`.
  have hbound : ∀ τ ∈ Ioc σ ρ,
      ‖(∫ x in closedBall ξ τ, inner ℝ (x - ξ) (H x) ∂V.weight) / τ ^ (n + 1)‖ ≤ δ * τ⁻¹ := by
    intro τ hτ
    have hτpos : 0 < τ := hσ.trans hτ.1
    have hsub : closedBall ξ τ ⊆ U := (closedBall_subset_closedBall hτ.2).trans hρU
    have hHint : IntegrableOn H (closedBall ξ τ) V.weight :=
      hH.1.integrableOn_compact_subset hsub (isCompact_closedBall ξ τ)
    have h1 : ‖∫ x in closedBall ξ τ, inner ℝ (x - ξ) (H x) ∂V.weight‖ ≤
        τ * ∫ x in closedBall ξ τ, ‖H x‖ ∂V.weight := by
      rw [← integral_const_mul]
      refine norm_integral_le_of_norm_le (hHint.norm.const_mul τ) ?_
      filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
      calc ‖inner ℝ (x - ξ) (H x)‖ ≤ ‖x - ξ‖ * ‖H x‖ := norm_inner_le_norm _ _
        _ ≤ τ * ‖H x‖ := by
          gcongr
          exact mem_closedBall_iff_norm.1 hx
    have h2 := hδ τ ⟨hτ.1.le, hτ.2⟩
    rw [Real.rpow_sub hτpos, Real.rpow_one, Real.rpow_natCast] at h2
    have hτn : 0 < τ ^ n := pow_pos hτpos n
    rw [norm_div, norm_pow, Real.norm_of_nonneg hτpos.le]
    calc ‖∫ x in closedBall ξ τ, inner ℝ (x - ξ) (H x) ∂V.weight‖ / τ ^ (n + 1)
        ≤ (τ * ∫ x in closedBall ξ τ, ‖H x‖ ∂V.weight) / τ ^ (n + 1) := by gcongr
      _ = (τ / τ ^ n * ∫ x in closedBall ξ τ, ‖H x‖ ∂V.weight) * τ⁻¹ := by
          rw [pow_succ]; field_simp
      _ ≤ δ * τ⁻¹ := by gcongr
  -- Step 3: `τ ↦ δ / τ` is continuous on `[σ, ρ]`, hence integrable on `(σ, ρ]`.
  have hint : IntegrableOn (fun τ : ℝ ↦ δ * τ⁻¹) (Ioc σ ρ) := by
    have hc : ContinuousOn (fun τ : ℝ ↦ δ * τ⁻¹) (Icc σ ρ) :=
      continuousOn_const.mul (continuousOn_inv₀.mono fun x hx ↦ (hσ.trans_le hx.1).ne')
    exact hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  -- Step 4: `|∫_{(σ,ρ]} e| ≤ ∫_{(σ,ρ]} δ / τ dτ = δ log (ρ / σ)`.
  calc |∫ τ in Ioc σ ρ, (∫ x in closedBall ξ τ, inner ℝ (x - ξ) (H x) ∂V.weight) / τ ^ (n + 1)|
      = ‖∫ τ in Ioc σ ρ, (∫ x in closedBall ξ τ, inner ℝ (x - ξ) (H x) ∂V.weight) / τ ^ (n + 1)‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∫ τ in Ioc σ ρ, δ * τ⁻¹ :=
        norm_integral_le_of_norm_le hint (ae_restrict_of_forall_mem measurableSet_Ioc hbound)
    _ = δ * Real.log (ρ / σ) := by
        rw [integral_const_mul, ← intervalIntegral.integral_of_le hσρ.le,
          integral_inv_of_pos hσ (hσ.trans hσρ)]

theorem main_theorem : ApproxTangentAE ∧ FirstVariationFormula ∧ StationaryIffVariational ∧ StationaryMonotonicity ∧ StationaryDensity ∧ CanonicalRepresentative ∧ BoundedCurvatureMonotonicity ∧ LogarithmicMonotonicityError ∧ LpMonotonicity ∧ LpDensity ∧ LpSupportRepresentation ∧ PoincareInequality ∧ SobolevInequality ∧ SupportInBall ∧ ConvexHullProperty ∧ ClassicalTangent := by sorry

/-- **Fubini on the annulus** `A = B_ρ(ξ) \ B_σ(ξ)` (the radial integration by parts behind the
integrating factors of Simon Ch. 4, 3.17 and 4.7). If `μ` is finite on compact sets, `w` is
`μ`-integrable on `A`, `F'` is integrable on `(σ, ρ]` and `F(t) = F(σ) + ∫_{(σ,t]} F'` for
`t ∈ [σ, ρ]`, then `w (F(|x - ξ|) - F(σ))` is `μ`-integrable on `A`,
`t ↦ F'(t) ∫_{B_ρ(ξ) \ B_t(ξ)} w dμ` is integrable on `(σ, ρ]`, and
`∫_{(σ,ρ]} F'(t) ∫_{B_ρ(ξ) \ B_t(ξ)} w dμ dt = ∫_A w (F(|x - ξ|) - F(σ)) dμ`. This is
`mcm_primitive_radial_fubini` for `S = A` and `r = |· - ξ|`, since
`A ∩ {x | t < r x} = B_ρ(ξ) \ B_t(ξ)` for `t ∈ (σ, ρ]`. -/
theorem Submission.mcm_annulus_primitive_fubini : ∀ (n ℓ : ℕ) (μ : Measure (Ambient n ℓ)) (ξ : Ambient n ℓ) (w : Ambient n ℓ → ℝ) (F F' : ℝ → ℝ) (σ ρ : ℝ), IsFiniteMeasureOnCompacts μ → IntegrableOn w (closedBall ξ ρ \ closedBall ξ σ) μ → IntegrableOn F' (Ioc σ ρ) → (∀ t ∈ Icc σ ρ, F t = F σ + ∫ τ in Ioc σ t, F' τ) → IntegrableOn (fun x ↦ w x * (F ‖x - ξ‖ - F σ)) (closedBall ξ ρ \ closedBall ξ σ) μ ∧ IntegrableOn (fun t ↦ F' t * ∫ x in closedBall ξ ρ \ closedBall ξ t, w x ∂μ) (Ioc σ ρ) ∧ ∫ t in Ioc σ ρ, F' t * ∫ x in closedBall ξ ρ \ closedBall ξ t, w x ∂μ = ∫ x in closedBall ξ ρ \ closedBall ξ σ, w x * (F ‖x - ξ‖ - F σ) ∂μ := by
  intro n ℓ μ ξ w F F' σ ρ hμ hw hF' hF
  -- `ℝ^{n+ℓ}` is σ-compact and `μ` is finite on compact sets: `μ` is σ-finite, hence s-finite
  have hμs : SFinite μ := inferInstance
  -- `A` is Borel and the radius `r = |· - ξ|` is continuous, hence Borel measurable
  have hA : MeasurableSet (closedBall ξ ρ \ closedBall ξ σ) :=
    measurableSet_closedBall.diff measurableSet_closedBall
  have hr : Measurable fun x : Ambient n ℓ ↦ ‖x - ξ‖ :=
    (continuous_id.sub continuous_const).norm.measurable
  -- `r` maps `A` into `(σ, ρ]`
  have hrA : ∀ x ∈ closedBall ξ ρ \ closedBall ξ σ, ‖x - ξ‖ ∈ Ioc σ ρ := by
    rintro x ⟨hxρ, hxσ⟩
    rw [mem_closedBall_iff_norm] at hxρ hxσ
    exact ⟨not_le.1 hxσ, hxρ⟩
  obtain ⟨ha, hb, hc⟩ := Submission.mcm_primitive_radial_fubini (Ambient n ℓ) μ
    (closedBall ξ ρ \ closedBall ξ σ) (fun x ↦ ‖x - ξ‖) w F F' σ ρ hμs hA hr hrA hw hF' hF
  -- for `t ∈ (σ, ρ]`: `A ∩ {x | t < r x} = B_ρ(ξ) \ B_t(ξ)`, as `t < r x` forces `σ < r x`
  have hAt : ∀ t ∈ Ioc σ ρ, (closedBall ξ ρ \ closedBall ξ σ) ∩ {x | t < ‖x - ξ‖} =
      closedBall ξ ρ \ closedBall ξ t := by
    intro t ht
    ext x
    simp only [mem_inter_iff, Set.mem_sdiff, mem_closedBall_iff_norm, mem_ofPred_eq, not_le]
    exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, ht.1.trans h.2⟩, h.2⟩⟩
  -- so the two `t`-integrands agree on `(σ, ρ]`, which carries over integrability and integral
  have hEq : EqOn
      (fun t ↦ F' t * ∫ x in (closedBall ξ ρ \ closedBall ξ σ) ∩ {x | t < ‖x - ξ‖}, w x ∂μ)
      (fun t ↦ F' t * ∫ x in closedBall ξ ρ \ closedBall ξ t, w x ∂μ) (Ioc σ ρ) :=
    fun t ht ↦ by simp only [hAt t ht]
  exact ⟨ha, hb.congr_fun hEq measurableSet_Ioc,
    (setIntegral_congr_fun measurableSet_Ioc hEq).symm.trans hc⟩
/-- **Fubini on the triangle `σ < t < s ≤ ρ`** (the `e`-part of the annulus integration by parts
behind Simon Ch. 4, 3.17 and 4.7). If `e` and `F'` are integrable on `(σ, ρ]` and
`F(t) = F(σ) + ∫_{(σ,t]} F'` for `t ∈ [σ, ρ]`, then `s ↦ e(s)(F(s) - F(σ))` and
`t ↦ F'(t) ∫_{(t,ρ]} e` are integrable on `(σ, ρ]` and
`∫_{(σ,ρ]} F'(t) ∫_{(t,ρ]} e(τ) dτ dt = ∫_{(σ,ρ]} e(s)(F(s) - F(σ)) ds`. -/
theorem Submission.mcm_interval_primitive_fubini : ∀ (e F F' : ℝ → ℝ) (σ ρ : ℝ), IntegrableOn e (Ioc σ ρ) → IntegrableOn F' (Ioc σ ρ) → (∀ t ∈ Icc σ ρ, F t = F σ + ∫ τ in Ioc σ t, F' τ) → IntegrableOn (fun s ↦ e s * (F s - F σ)) (Ioc σ ρ) ∧ IntegrableOn (fun t ↦ F' t * ∫ τ in Ioc t ρ, e τ) (Ioc σ ρ) ∧ ∫ t in Ioc σ ρ, F' t * ∫ τ in Ioc t ρ, e τ = ∫ s in Ioc σ ρ, e s * (F s - F σ) := by
  intro e F F' σ ρ he hF' hF
  -- Steps 1–2: apply `mcm_primitive_radial_fubini` to `(X, ν, S, r, g) = (ℝ, λ, (σ, ρ], id, e)`.
  -- Lebesgue measure is s-finite, `(σ, ρ]` is Borel, and `id` is measurable and maps `S` into
  -- `(σ, ρ]`. Part (a) is then verbatim (`id s` is `s`).
  obtain ⟨ha, hb, hc⟩ := Submission.mcm_primitive_radial_fubini ℝ volume (Ioc σ ρ) id e F F' σ ρ
    inferInstance measurableSet_Ioc measurable_id (fun _ hs ↦ hs) he hF' hF
  -- Step 3: `(σ, ρ] ∩ {s : t < s} = (max σ t, ρ] = (t, ρ]` for `t ∈ (σ, ρ]`.
  have hset : ∀ t ∈ Ioc σ ρ, Ioc σ ρ ∩ {s | t < id s} = Ioc t ρ := fun t ht ↦ by
    rw [show {s | t < id s} = Ioi t from rfl, Ioc_inter_Ioi, sup_eq_right.2 ht.1.le]
  -- Step 4: the `t`-integrands of (b′), (c′) and of (b), (c) agree on the Borel set `(σ, ρ]`.
  have heq : EqOn (fun t ↦ F' t * ∫ s in Ioc σ ρ ∩ {s | t < id s}, e s)
      (fun t ↦ F' t * ∫ τ in Ioc t ρ, e τ) (Ioc σ ρ) := fun t ht ↦ by
    simp only [hset t ht]
  exact ⟨ha, hb.congr_fun heq measurableSet_Ioc,
    (setIntegral_congr_fun measurableSet_Ioc heq).symm.trans hc⟩

/-- **Integration by parts on the annulus** `A = B_ρ(ξ) \ B_σ(ξ)` (the integrating-factor step of
Simon Ch. 4, 3.17 and 4.7). If `μ` is finite on compact sets, `w` is `μ`-integrable on `A`, `e`
and `F'` are integrable on `(σ, ρ]`, `a(t) - a(s) = ∫_{B_t(ξ) \ B_s(ξ)} w dμ + ∫_{(s,t]} e` for
`σ ≤ s ≤ t ≤ ρ` and `F(t) = F(σ) + ∫_{(σ,t]} F'` for `t ∈ [σ, ρ]`, then `F(|x - ξ|) w(x)` is
`μ`-integrable on `A` and
`F(ρ)a(ρ) - F(σ)a(σ) = ∫_A F(|x - ξ|) w(x) dμ + ∫_{(σ,ρ]} (F e + F' a)`.
With `D(t) = ∫_{B_ρ(ξ) \ B_t(ξ)} w dμ` and `P(t) = ∫_{(t,ρ]} e` we have `a = a(ρ) - D - P` on
`(σ, ρ]`; `mcm_annulus_primitive_fubini` and `mcm_interval_primitive_fubini` evaluate `∫ F' D`
and `∫ F' P`, and the `F(σ)`-terms cancel. -/
theorem Submission.mcm_annulus_integration_by_parts : ∀ (n ℓ : ℕ) (μ : Measure (Ambient n ℓ)) (ξ : Ambient n ℓ) (w : Ambient n ℓ → ℝ) (a e F F' : ℝ → ℝ) (σ ρ : ℝ), IsFiniteMeasureOnCompacts μ → 0 < σ → σ ≤ ρ → (∀ x, 0 ≤ w x) → IntegrableOn w (closedBall ξ ρ \ closedBall ξ σ) μ → IntegrableOn e (Ioc σ ρ) → (∀ s t : ℝ, σ ≤ s → s ≤ t → t ≤ ρ → a t - a s = ∫ x in closedBall ξ t \ closedBall ξ s, w x ∂μ + ∫ τ in Ioc s t, e τ) → IntegrableOn F' (Ioc σ ρ) → (∀ t ∈ Icc σ ρ, F t = F σ + ∫ τ in Ioc σ t, F' τ) → IntegrableOn (fun x ↦ F ‖x - ξ‖ * w x) (closedBall ξ ρ \ closedBall ξ σ) μ ∧ F ρ * a ρ - F σ * a σ = ∫ x in closedBall ξ ρ \ closedBall ξ σ, F ‖x - ξ‖ * w x ∂μ + ∫ τ in Ioc σ ρ, (F τ * e τ + F' τ * a τ) := by
  intro n ℓ μ ξ w a e F F' σ ρ hμ _ hσρ _ hw he ha hF' hF
  -- Step 8: Fubini on `(σ, ρ] × A`, i.e. `∫ F' D = ∫_A w (F(|x - ξ|) - F(σ)) dμ`
  obtain ⟨hwF, hF'D, hD⟩ :=
    Submission.mcm_annulus_primitive_fubini n ℓ μ ξ w F F' σ ρ hμ hw hF' hF
  -- Step 9: Fubini on the triangle `σ < t < s ≤ ρ`, i.e. `∫ F' P = ∫ e (F - F(σ))`
  obtain ⟨heF, hF'P, hP⟩ := Submission.mcm_interval_primitive_fubini e F F' σ ρ he hF' hF
  -- Step 2: `a t = a ρ - D t - P t` for `t ∈ (σ, ρ]` (the hypothesis on `a` at `(t, ρ)`)
  have haDP : ∀ t ∈ Ioc σ ρ, F' t * a ρ - F' t * (∫ x in closedBall ξ ρ \ closedBall ξ t, w x ∂μ) -
      F' t * (∫ τ in Ioc t ρ, e τ) = F' t * a t := fun t ht ↦ by
    linear_combination F' t * ha t ρ ht.1.le ht.2 le_rfl
  -- Step 4: integrability, from `F(|x - ξ|) w = w (F(|x - ξ|) - F(σ)) + F(σ) w` on `A`, and
  -- `F e = e (F - F(σ)) + F(σ) e`, `F' a = F' a(ρ) - F' D - F' P` on `(σ, ρ]`
  have hFw : IntegrableOn (fun x ↦ F ‖x - ξ‖ * w x) (closedBall ξ ρ \ closedBall ξ σ) μ := by
    have h : (fun x ↦ F ‖x - ξ‖ * w x) = fun x ↦ w x * (F ‖x - ξ‖ - F σ) + F σ * w x := by
      funext x
      ring
    rw [h]
    exact hwF.add (hw.const_mul (F σ))
  have hFe : IntegrableOn (fun τ ↦ F τ * e τ) (Ioc σ ρ) := by
    have h : (fun τ ↦ F τ * e τ) = fun τ ↦ e τ * (F τ - F σ) + F σ * e τ := by
      funext τ
      ring
    rw [h]
    exact heF.add (he.const_mul (F σ))
  have hF'aD : IntegrableOn
      (fun t ↦ F' t * a ρ - F' t * ∫ x in closedBall ξ ρ \ closedBall ξ t, w x ∂μ) (Ioc σ ρ) :=
    (hF'.mul_const (a ρ)).sub hF'D
  have hF'a : IntegrableOn (fun τ ↦ F' τ * a τ) (Ioc σ ρ) :=
    (hF'aD.sub hF'P).congr_fun haDP measurableSet_Ioc
  refine ⟨hFw, ?_⟩
  -- Steps 5–9 as identities between the integrals
  have h1 : ∫ x in closedBall ξ ρ \ closedBall ξ σ, F ‖x - ξ‖ * w x ∂μ =
      (∫ x in closedBall ξ ρ \ closedBall ξ σ, w x * (F ‖x - ξ‖ - F σ) ∂μ) +
        F σ * ∫ x in closedBall ξ ρ \ closedBall ξ σ, w x ∂μ := by
    rw [← integral_const_mul, ← integral_add hwF (hw.const_mul (F σ))]
    congr 1 with x
    ring
  have h2 : ∫ τ in Ioc σ ρ, F τ * e τ =
      (∫ s in Ioc σ ρ, e s * (F s - F σ)) + F σ * ∫ τ in Ioc σ ρ, e τ := by
    rw [← integral_const_mul, ← integral_add heF (he.const_mul (F σ))]
    congr 1 with τ
    ring
  have h3 : ∫ τ in Ioc σ ρ, F' τ * a τ =
      (∫ τ in Ioc σ ρ, F' τ) * a ρ -
        (∫ t in Ioc σ ρ, F' t * ∫ x in closedBall ξ ρ \ closedBall ξ t, w x ∂μ) -
          ∫ t in Ioc σ ρ, F' t * ∫ τ in Ioc t ρ, e τ := by
    rw [← setIntegral_congr_fun measurableSet_Ioc haDP, integral_sub hF'aD hF'P,
      integral_sub (hF'.mul_const (a ρ)) hF'D, integral_mul_const]
  -- Step 10: add up with `a(ρ) - a(σ) = ∫_A w dμ + ∫ e` and `F(ρ) = F(σ) + ∫ F'`; the
  -- `F(σ)`-terms cancel
  rw [integral_add hFe hF'a]
  linear_combination -h1 - h2 - h3 + hD + hP + F σ * ha σ ρ le_rfl hσρ le_rfl +
    a ρ * hF ρ ⟨hσρ, le_rfl⟩

/-- **Ch. 4, 3.15–3.17 (pp. 92–93) and the remark after 3.17, from the unit-weight identity.**
Assume the structure facts of §1 and, for `0 < σ ≤ ρ` with `B_ρ(ξ) ⊆ U`, the identity
`a(ρ) - a(σ) = ∫_{B_ρ(ξ) \ B_σ(ξ)} w dμ_V + ∫_σ^ρ e(τ) dτ`, where `a(τ) = τ⁻ⁿμ_V(B_τ(ξ))`,
`w = r⁻ⁿ|D^⊥r|²` and `e(τ) = τ^{-n-1} ∫_{B_τ(ξ)} (x - ξ) · H dμ_V`. If `|H| ≤ Λ`, then
`|e| ≤ Λa` on `(0, R]` (3.15), so `E = e / a` satisfies `|E| ≤ Λ` and `e = Ea`. Integrating the
identity by parts against the integrating factor `F(ρ) = exp(-∫_0^ρ E) ∈ [e^{-Λρ}, e^{Λρ}]`,
whose derivative `-EF` cancels the error term, gives
`F(ρ)a(ρ) - F(σ)a(σ) = ∫_{B_ρ(ξ) \ B_σ(ξ)} F(r) w dμ_V = G(σ, ρ) ∫_{B_ρ(ξ) \ B_σ(ξ)} w dμ_V`
with `G(σ, ρ) ∈ [e^{-ΛR}, e^{ΛR}]`. Hence `F(ρ)a(ρ)` is increasing, with bounds on `F` that are
uniform for centres near `ξ`; this gives the existence and upper semicontinuity of
`Θⁿ(μ_V, ·)` on `U`. -/
theorem Submission.mcm_bounded_curvature_of_identity : (∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ), 0 < n → IsFiniteMeasureOnCompacts V.weight ∧ (∀ᵐ x ∂V.weight, Module.finrank ℝ (V.tangentSpace x) = n) ∧ AEStronglyMeasurable (fun x ↦ (V.tangentSpace x).starProjection) V.weight) → (∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)) (H : Ambient n ℓ → Ambient n ℓ) (ξ : Ambient n ℓ) (σ ρ : ℝ), 0 < n → IsOpen U → V.HasMeanCurvatureIn U H → closedBall ξ ρ ⊆ U → 0 < σ → σ ≤ ρ → IntegrableOn (fun τ ↦ (∫ x in closedBall ξ τ, inner ℝ (x - ξ) (H x) ∂V.weight) / τ ^ (n + 1)) (Ioc σ ρ) ∧ IntegrableOn (fun x ↦ V.normalRadialSq ξ x / ‖x - ξ‖ ^ n) (closedBall ξ ρ \ closedBall ξ σ) V.weight ∧ V.weight.real (closedBall ξ ρ) / ρ ^ n - V.weight.real (closedBall ξ σ) / σ ^ n = ∫ x in closedBall ξ ρ \ closedBall ξ σ, V.normalRadialSq ξ x / ‖x - ξ‖ ^ n ∂V.weight + ∫ τ in Ioc σ ρ, (∫ x in closedBall ξ τ, inner ℝ (x - ξ) (H x) ∂V.weight) / τ ^ (n + 1)) → BoundedCurvatureMonotonicity := by
  intro hGF hUI n ℓ V U H Λ hn hU hHU hΛ hHb
  have hfin : IsFiniteMeasureOnCompacts V.weight := (hGF n ℓ V hn).1
  -- The annular weight `w_ξ = r⁻ⁿ|D^⊥r|²` is nonnegative everywhere.
  have hw0 : ∀ ξ x : Ambient n ℓ, 0 ≤ V.normalRadialSq ξ x / ‖x - ξ‖ ^ n := by
    intro ξ x
    unfold RectifiableVarifold.normalRadialSq
    positivity
  -- Part (A): the identity 3.17 on a ball `B_R(ξ) ⊆ U`.
  have partA : ∀ (ξ : Ambient n ℓ) (R : ℝ), closedBall ξ R ⊆ U →
      ∃ (F : ℝ → ℝ) (G : ℝ → ℝ → ℝ),
        (∀ ρ ∈ Ioo 0 R, F ρ ∈ Icc (Real.exp (-(Λ * ρ))) (Real.exp (Λ * ρ))) ∧
        ∀ σ ρ : ℝ, 0 < σ → σ ≤ ρ → ρ < R →
          G σ ρ ∈ Icc (Real.exp (-(Λ * R))) (Real.exp (Λ * R)) ∧
          F ρ * (V.weight.real (closedBall ξ ρ) / ρ ^ n) -
              F σ * (V.weight.real (closedBall ξ σ) / σ ^ n) =
            G σ ρ * ∫ x in closedBall ξ ρ \ closedBall ξ σ,
              V.normalRadialSq ξ x / ‖x - ξ‖ ^ n ∂V.weight := by
    intro ξ R hball
    -- A0: for `R ≤ 0` the conditions are vacuous.
    rcases le_or_gt R 0 with hR | hR
    · refine ⟨fun _ ↦ 1, fun _ _ ↦ 1, ?_, ?_⟩
      · intro ρ hρ
        exact absurd (hρ.1.trans hρ.2) (not_lt.2 hR)
      · intro σ ρ hσ hσρ hρR
        exact absurd ((hσ.trans_le hσρ).trans hρR) (not_lt.2 hR)
    set a : ℝ → ℝ := fun τ ↦ V.weight.real (closedBall ξ τ) / τ ^ n with ha
    set e : ℝ → ℝ := fun τ ↦
      (∫ x in closedBall ξ τ, inner ℝ (x - ξ) (H x) ∂V.weight) / τ ^ (n + 1) with he
    set w : Ambient n ℓ → ℝ := fun x ↦ V.normalRadialSq ξ x / ‖x - ξ‖ ^ n with hw
    -- The unit-weight identity at the centre `ξ`, for radii up to `R`.
    have hUIξ : ∀ s t : ℝ, 0 < s → s ≤ t → t ≤ R →
        IntegrableOn e (Ioc s t) ∧ IntegrableOn w (closedBall ξ t \ closedBall ξ s) V.weight ∧
        a t - a s = (∫ x in closedBall ξ t \ closedBall ξ s, w x ∂V.weight) +
          ∫ τ in Ioc s t, e τ := by
      intro s t hs hst htR
      exact hUI n ℓ V U H ξ s t hn hU hHU ((closedBall_subset_closedBall htR).trans hball) hs hst
    have ha0 : ∀ τ, 0 < τ → 0 ≤ a τ := fun τ hτ ↦
      div_nonneg measureReal_nonneg (pow_nonneg hτ.le _)
    -- A1 (3.15): `|e(τ)| ≤ Λ a(τ)`, as `|(x - ξ) · H(x)| ≤ τΛ` for `μ_V`-a.e. `x ∈ B_τ(ξ)`.
    have hA1 : ∀ τ ∈ Ioc 0 R, |e τ| ≤ Λ * a τ := by
      intro τ hτ
      have hτpos : 0 < τ := hτ.1
      have hsub : closedBall ξ τ ⊆ U := (closedBall_subset_closedBall hτ.2).trans hball
      have hbound : ‖∫ x in closedBall ξ τ, inner ℝ (x - ξ) (H x) ∂V.weight‖ ≤
          (τ * Λ) * V.weight.real (closedBall ξ τ) := by
        apply norm_setIntegral_le_of_norm_le_const_ae' measure_closedBall_lt_top
        filter_upwards [hHb] with x hx hxB
        have h1 : ‖x - ξ‖ ≤ τ := by rw [← dist_eq_norm]; exact mem_closedBall.1 hxB
        calc ‖inner ℝ (x - ξ) (H x)‖ ≤ ‖x - ξ‖ * ‖H x‖ := norm_inner_le_norm _ _
          _ ≤ τ * Λ := mul_le_mul h1 (hx (hsub hxB)) (norm_nonneg _) hτpos.le
      rw [Real.norm_eq_abs] at hbound
      simp only [he, ha]
      rw [abs_div, abs_of_pos (pow_pos hτpos _), div_le_iff₀ (pow_pos hτpos _)]
      calc _ ≤ τ * Λ * V.weight.real (closedBall ξ τ) := hbound
        _ = Λ * (V.weight.real (closedBall ξ τ) / τ ^ n) * τ ^ (n + 1) := by
          rw [pow_succ]; field_simp
    -- A2: `E = e / a` (with `x / 0 = 0`) has `|E| ≤ Λ` and `E a = e` on `(0, R]`.
    set E : ℝ → ℝ := fun τ ↦ e τ / a τ with hE
    have hA2 : ∀ τ ∈ Ioc 0 R, |E τ| ≤ Λ ∧ E τ * a τ = e τ := by
      intro τ hτ
      have h1 := hA1 τ hτ
      rcases (ha0 τ hτ.1).lt_or_eq with hpos | hzero
      · refine ⟨?_, div_mul_cancel₀ _ hpos.ne'⟩
        simp only [hE]
        rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
        exact h1
      · simp only [hE]
        rw [← hzero] at h1 ⊢
        rw [mul_zero] at h1
        rw [div_zero, abs_zero, zero_mul]
        exact ⟨hΛ, (abs_nonpos_iff.1 h1).symm⟩
    -- A3: `E` is integrable on `(0, R]`: `a` is Borel since `τ ↦ μ_V(B_τ(ξ))` is monotone, `e`
    -- is integrable on every `(R/(k+1), R]` by the identity, and `|E| ≤ Λ`.
    have hmono : Monotone (fun τ ↦ V.weight.real (closedBall ξ τ)) := fun s t hst ↦
      measureReal_mono (closedBall_subset_closedBall hst) measure_closedBall_lt_top.ne
    have ha_meas : Measurable a := hmono.measurable.div (continuous_pow n).measurable
    have he_aesm : AEStronglyMeasurable e (volume.restrict (Ioc 0 R)) := by
      have hUn : (⋃ k : ℕ, Ioc (R / (k + 1)) R) = Ioc 0 R := by
        ext τ
        simp only [mem_iUnion, mem_Ioc]
        constructor
        · rintro ⟨k, hk1, hk2⟩
          exact ⟨lt_trans (div_pos hR (by positivity)) hk1, hk2⟩
        · rintro ⟨h1, h2⟩
          obtain ⟨k, hk⟩ := exists_nat_gt (R / τ)
          refine ⟨k, ?_, h2⟩
          rw [div_lt_iff₀ (by positivity)]
          rw [div_lt_iff₀ h1] at hk
          nlinarith
      rw [← hUn, aestronglyMeasurable_iUnion_iff]
      intro k
      have hk : (0 : ℝ) < k + 1 := by positivity
      have hle : R / (k + 1) ≤ R := (div_le_iff₀ hk).2 (by nlinarith [k.cast_nonneg (α := ℝ)])
      exact (hUIξ _ _ (div_pos hR hk) hle le_rfl).1.aestronglyMeasurable
    have hE_int : IntegrableOn E (Ioc 0 R) := by
      refine IntegrableOn.of_bound measure_Ioc_lt_top (he_aesm.div₀ ha_meas.aestronglyMeasurable)
        Λ ?_
      exact (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun τ hτ ↦ by
        rw [Real.norm_eq_abs]; exact (hA2 τ hτ).1)
    -- A4: the integrating factor `F(ρ) = exp(-∫_{(0,ρ]} E) ∈ [e^{-Λρ}, e^{Λρ}]`, with
    -- `F(t) = F(σ) + ∫_{(σ,t]} F'` for `F' = -E F`.
    set F : ℝ → ℝ := fun τ ↦ Real.exp (-∫ s in Ioc 0 τ, E s) with hF
    have hFTC := Submission.mcm_exp_neg_integral_ftc E R hE_int
    have hFbound : ∀ ρ ∈ Ioc 0 R, F ρ ∈ Icc (Real.exp (-(Λ * ρ))) (Real.exp (Λ * ρ)) := by
      intro ρ hρ
      have hI : |∫ s in Ioc 0 ρ, E s| ≤ Λ * ρ := by
        have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc 0 ρ) (f := E) (C := Λ)
          measure_Ioc_lt_top (fun τ hτ ↦ by
            rw [Real.norm_eq_abs]; exact (hA2 τ ⟨hτ.1, hτ.2.trans hρ.2⟩).1)
        rwa [Real.norm_eq_abs, Real.volume_real_Ioc_of_le hρ.1.le, sub_zero] at this
      exact ⟨Real.exp_le_exp.2 (by linarith [le_abs_self (∫ s in Ioc 0 ρ, E s)]),
        Real.exp_le_exp.2 (by linarith [neg_le_abs (∫ s in Ioc 0 ρ, E s)])⟩
    -- A5–A7, with `D(σ, ρ) = ∫_{B_ρ \ B_σ} w dμ_V` and `I(σ, ρ) = ∫_{B_ρ \ B_σ} F(r) w dμ_V`.
    set D : ℝ → ℝ → ℝ := fun s t ↦ ∫ x in closedBall ξ t \ closedBall ξ s, w x ∂V.weight with hD
    set I : ℝ → ℝ → ℝ := fun s t ↦
      ∫ x in closedBall ξ t \ closedBall ξ s, F ‖x - ξ‖ * w x ∂V.weight with hI
    refine ⟨F, fun s t ↦ if D s t = 0 then 1 else I s t / D s t,
      fun ρ hρ ↦ hFbound ρ ⟨hρ.1, hρ.2.le⟩, ?_⟩
    intro σ ρ hσ hσρ hρR
    obtain ⟨he_int, hw_int, -⟩ := hUIξ σ ρ hσ hσρ hρR.le
    have hsub : Ioc σ ρ ⊆ Ioc 0 R := Ioc_subset_Ioc hσ.le hρR.le
    -- A5: integration by parts against `F`.
    obtain ⟨hFw_int, hid⟩ := Submission.mcm_annulus_integration_by_parts n ℓ V.weight ξ w a e F
      (fun τ ↦ -(E τ * F τ)) σ ρ hfin hσ hσρ (fun x ↦ hw0 ξ x) hw_int he_int
      (fun s t hs hst ht ↦ (hUIξ s t (hσ.trans_le hs) hst (ht.trans hρR.le)).2.2)
      (hFTC.1.mono_set hsub)
      (fun t ht ↦ hFTC.2 σ t hσ.le ht.1 (ht.2.trans hρR.le))
    -- A6: the error term vanishes, `F e + F' a = F (e - E a) = 0`.
    have hzero : ∫ τ in Ioc σ ρ, (F τ * e τ + -(E τ * F τ) * a τ) = 0 := by
      rw [setIntegral_congr_fun measurableSet_Ioc (g := fun _ ↦ (0 : ℝ)) ?_]
      · simp
      intro τ hτ
      have h2 := (hA2 τ (hsub hτ)).2
      simp only
      rw [← h2]; ring
    have hmain : F ρ * a ρ - F σ * a σ = I σ ρ := by
      rw [hid, hzero, add_zero]
    -- A7: `e^{-ΛR} D ≤ I ≤ e^{ΛR} D`, since `F(r) ∈ [e^{-ΛR}, e^{ΛR}]` on `B_ρ(ξ) \ B_σ(ξ)`.
    have hA_meas : MeasurableSet (closedBall ξ ρ \ closedBall ξ σ) :=
      measurableSet_closedBall.diff measurableSet_closedBall
    have hFx : ∀ x ∈ closedBall ξ ρ \ closedBall ξ σ,
        F ‖x - ξ‖ ∈ Icc (Real.exp (-(Λ * R))) (Real.exp (Λ * R)) := by
      intro x hx
      have h1 : ‖x - ξ‖ ≤ ρ := by rw [← dist_eq_norm]; exact mem_closedBall.1 hx.1
      have h2 : σ < ‖x - ξ‖ := by
        rw [← dist_eq_norm]; exact not_le.1 (fun h ↦ hx.2 (mem_closedBall.2 h))
      have hb := hFbound ‖x - ξ‖ ⟨hσ.trans h2, h1.trans hρR.le⟩
      have hΛx : Λ * ‖x - ξ‖ ≤ Λ * R := mul_le_mul_of_nonneg_left (h1.trans hρR.le) hΛ
      exact ⟨(Real.exp_le_exp.2 (by linarith)).trans hb.1, hb.2.trans (Real.exp_le_exp.2 hΛx)⟩
    have hlow : Real.exp (-(Λ * R)) * D σ ρ ≤ I σ ρ := by
      simp only [hD, hI]
      rw [← integral_const_mul]
      exact setIntegral_mono_on (hw_int.const_mul _) hFw_int hA_meas fun x hx ↦
        mul_le_mul_of_nonneg_right (hFx x hx).1 (hw0 ξ x)
    have hup : I σ ρ ≤ Real.exp (Λ * R) * D σ ρ := by
      simp only [hD, hI]
      rw [← integral_const_mul]
      exact setIntegral_mono_on hFw_int (hw_int.const_mul _) hA_meas fun x hx ↦
        mul_le_mul_of_nonneg_right (hFx x hx).2 (hw0 ξ x)
    have hD0 : 0 ≤ D σ ρ := setIntegral_nonneg hA_meas fun x _ ↦ hw0 ξ x
    have hΛR : 0 ≤ Λ * R := mul_nonneg hΛ hR.le
    -- `G = I / D`, or `G = 1` when `D = 0` (then also `I = 0`).
    by_cases hDz : D σ ρ = 0
    · have hI0 : I σ ρ = 0 := by
        rw [hDz, mul_zero] at hlow hup
        exact le_antisymm hup hlow
      simp only [hDz, ite_true, one_mul]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [Real.exp_le_one_iff]; linarith
      · exact Real.one_le_exp_iff.2 hΛR
      · rw [hmain, hI0]; exact hDz.symm
    · have hDpos : 0 < D σ ρ := lt_of_le_of_ne hD0 (Ne.symm hDz)
      simp only [hDz, ite_false]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [le_div_iff₀ hDpos]; exact hlow
      · rw [div_le_iff₀ hDpos]; exact hup
      · rw [hmain, div_mul_cancel₀ _ hDz]
  -- Parts (B) and (C): take `r` with `B_{3r}(ξ) ⊆ U`. For `|η - ξ| < r`, (A) on `B_r(η)` makes
  -- `F_η(ρ) a_η(ρ)` nondecreasing on `(0, r)` with `F_η(ρ) ∈ [e^{-Λρ}, e^{Λρ}]`, so the density
  -- criterion applies with `c(ρ) = Λρ` and `E_η = 0`.
  refine ⟨partA, ?_⟩
  apply Submission.mcm_density_usc_of_monotone n ℓ V U hfin
  intro ξ hξ
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU ξ hξ
  refine ⟨ε / 3, by positivity, fun ρ ↦ Λ * ρ, ?_, ?_⟩
  · have h : Tendsto (fun ρ : ℝ ↦ Λ * ρ) (𝓝 0) (𝓝 (Λ * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  · intro η hη
    have hball : closedBall η (ε / 3) ⊆ U := by
      intro y hy
      apply hεU
      rw [mem_ball]
      have h1 := mem_closedBall.1 hy
      have h2 := mem_ball.1 hη
      calc dist y ξ ≤ dist y η + dist η ξ := dist_triangle _ _ _
        _ < ε := by linarith
    obtain ⟨F, G, hF, hFG⟩ := partA η (ε / 3) hball
    refine ⟨F, fun _ ↦ 0, fun ρ hρ ↦ ⟨hF ρ hρ, ?_⟩, ?_⟩
    · rw [abs_zero]; exact mul_nonneg hΛ hρ.1.le
    · intro s hs ρ hρ hsρ
      obtain ⟨hG, hid⟩ := hFG s ρ hs.1 hsρ hρ.2
      have hD0 : 0 ≤ ∫ x in closedBall η ρ \ closedBall η s,
          V.normalRadialSq η x / ‖x - η‖ ^ n ∂V.weight :=
        setIntegral_nonneg (measurableSet_closedBall.diff measurableSet_closedBall)
          fun x _ ↦ hw0 η x
      have hGpos : 0 ≤ G s ρ := (Real.exp_pos _).le.trans hG.1
      simp only [add_zero]
      nlinarith [mul_nonneg hGpos hD0]

end

end GMT.Ch04
