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

theorem main_theorem : ApproxTangentAE ∧ FirstVariationFormula ∧ StationaryIffVariational ∧ StationaryMonotonicity ∧ StationaryDensity ∧ CanonicalRepresentative ∧ BoundedCurvatureMonotonicity ∧ LogarithmicMonotonicityError ∧ LpMonotonicity ∧ LpDensity ∧ LpSupportRepresentation ∧ PoincareInequality ∧ SobolevInequality ∧ SupportInBall ∧ ConvexHullProperty ∧ ClassicalTangent := by sorry

end

end GMT.Ch04
