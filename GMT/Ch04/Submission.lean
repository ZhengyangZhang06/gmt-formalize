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

/-- **Cutoff sequence** (the `C¹` cutoffs `φ(r/ρ)` of Simon Ch. 4, 3.3–3.6, with widths `→ 0`).
With `ψ = Real.smoothTransition`, `ε_m = a / (m + 2)` and `φ_m t = 1 - ψ ((t - 1) / ε_m)`:
`0 < ε_m < a`, `ε_m → 0`, `φ_m` is `C¹` and nonincreasing, `φ_m = 1` on `(-∞, 1]`,
`φ_m = 0` on `[1 + ε_m, ∞)`, and `0 ≤ φ_m ≤ 1`. -/
theorem Submission.weighted_mono_cutoff_seq_exists : ∀ (a : ℝ), 0 < a → ∃ (φ : ℕ → ℝ → ℝ) (ε : ℕ → ℝ), Tendsto ε atTop (𝓝 0) ∧ ∀ m, 0 < ε m ∧ ε m < a ∧ ContDiff ℝ 1 (φ m) ∧ Antitone (φ m) ∧ (∀ t, t ≤ 1 → φ m t = 1) ∧ (∀ t, 1 + ε m ≤ t → φ m t = 0) ∧ (∀ t, 0 ≤ φ m t ∧ φ m t ≤ 1) := by
  intro a ha
  refine ⟨fun m t ↦ 1 - Real.smoothTransition ((t - 1) / (a / ((m : ℝ) + 2))),
    fun m ↦ a / ((m : ℝ) + 2), ?_, fun m ↦ ?_⟩
  -- `ε_m = a / (m + 2) → 0` since `m + 2 → ∞`
  · exact (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop).const_div_atTop a
  dsimp only
  have hm : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  have hε : 0 < a / ((m : ℝ) + 2) := div_pos ha hm
  refine ⟨hε, ?_, ?_, fun s t hst ↦ ?_, fun t ht ↦ ?_, fun t ht ↦ ?_, fun t ↦ ?_⟩
  · -- `a < a (m + 2)` because `a (m + 1) > 0`
    rw [div_lt_iff₀ hm]
    nlinarith [mul_pos ha (show (0 : ℝ) < (m : ℝ) + 1 by positivity)]
  · exact contDiff_const.sub (Real.smoothTransition.contDiff.comp
      ((contDiff_id.sub contDiff_const).div_const _))
  · -- `t ↦ (t - 1) / ε_m` is increasing and `ψ` is monotone
    have h : (s - 1) / (a / ((m : ℝ) + 2)) ≤ (t - 1) / (a / ((m : ℝ) + 2)) := by gcongr
    linarith [Real.smoothTransition.monotone h]
  · -- `(t - 1) / ε_m ≤ 0`, so `ψ = 0` there
    rw [Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 ht) hε.le), sub_zero]
  · -- `(t - 1) / ε_m ≥ 1`, so `ψ = 1` there
    rw [Real.smoothTransition.one_of_one_le ((one_le_div₀ hε).2 (le_sub_iff_add_le'.2 ht)),
      sub_self]
  · exact ⟨sub_nonneg.2 (Real.smoothTransition.le_one _),
      sub_le_self _ (Real.smoothTransition.nonneg _)⟩
/-- **Radial cutoff limit (dominated convergence; Simon Ch. 4, 3.4–3.5 and 5.1, letting the cutoff
`φ` tend to the indicator of `(-∞, 1]`).** If `f` is `μ`-integrable on `B_R(ξ)`, `t > 0`,
`ε_m → 0` with `(1 + ε_m) t ≤ R`, and the measurable `φ_m : ℝ → [0, 1]` satisfy `φ_m = 1` on
`(-∞, 1]` and `φ_m = 0` on `[1 + ε_m, ∞)`, then `∫ φ_m(|x - ξ|/t) f(x) dμ → ∫_{B_t(ξ)} f dμ`. -/
theorem Submission.weighted_mono_cutoff_integral_tendsto : ∀ (n ℓ : ℕ) (μ : Measure (Ambient n ℓ)) (f : Ambient n ℓ → ℝ) (ξ : Ambient n ℓ) (t R : ℝ) (φ : ℕ → ℝ → ℝ) (ε : ℕ → ℝ), 0 < t → IntegrableOn f (closedBall ξ R) μ → Tendsto ε atTop (𝓝 0) → (∀ m, (1 + ε m) * t ≤ R) → (∀ m, Measurable (φ m)) → (∀ m s, 0 ≤ φ m s ∧ φ m s ≤ 1) → (∀ m s, s ≤ 1 → φ m s = 1) → (∀ m s, 1 + ε m ≤ s → φ m s = 0) → Tendsto (fun m ↦ ∫ x, φ m (‖x - ξ‖ / t) * f x ∂μ) atTop (𝓝 (∫ x in closedBall ξ t, f x ∂μ)) := by
  intro n ℓ μ f ξ t R φ ε ht hf hε hR hφm hφ01 hφ1 hφ0
  -- Step 1: `φ_m(r/t) = 0` off `B_R(ξ)`, since `(1 + ε_m) t ≤ R < r` and `t > 0`.
  have hoff : ∀ m x, x ∉ closedBall ξ R → φ m (‖x - ξ‖ / t) = 0 := by
    intro m x hx
    rw [mem_closedBall, dist_eq_norm, not_le] at hx
    exact hφ0 m _ ((le_div_iff₀ ht).2 ((hR m).trans hx.le))
  -- Hence `F_m = 1_{B_R(ξ)} F_m`, where `F_m(x) = φ_m(r/t) f(x)`.
  have hind : ∀ m, (fun x ↦ φ m (‖x - ξ‖ / t) * f x) =
      (closedBall ξ R).indicator (fun x ↦ φ m (‖x - ξ‖ / t) * f x) := by
    intro m
    funext x
    by_cases hx : x ∈ closedBall ξ R
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, hoff m x hx, zero_mul]
  -- Step 2: `F_m` is `μ`-a.e. strongly measurable.
  have hmeas : ∀ m, AEStronglyMeasurable (fun x ↦ φ m (‖x - ξ‖ / t) * f x) μ := by
    intro m
    rw [hind m, aestronglyMeasurable_indicator_iff measurableSet_closedBall]
    have hc : Measurable (fun x : Ambient n ℓ ↦ φ m (‖x - ξ‖ / t)) :=
      (hφm m).comp ((continuous_norm.comp (continuous_id.sub continuous_const)).div_const t).measurable
    exact hc.aestronglyMeasurable.mul hf.aestronglyMeasurable
  -- Step 3: `|F_m| ≤ 1_{B_R(ξ)} |f|`, which is `μ`-integrable.
  have hbound : ∀ m, ∀ᵐ x ∂μ,
      ‖φ m (‖x - ξ‖ / t) * f x‖ ≤ (closedBall ξ R).indicator (fun x ↦ ‖f x‖) x := by
    intro m
    refine Filter.Eventually.of_forall fun x ↦ ?_
    by_cases hx : x ∈ closedBall ξ R
    · rw [indicator_of_mem hx, norm_mul, Real.norm_of_nonneg (hφ01 m _).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (hφ01 m _).2
    · rw [indicator_of_notMem hx, hoff m x hx, zero_mul, norm_zero]
  have hbi : Integrable ((closedBall ξ R).indicator (fun x ↦ ‖f x‖)) μ :=
    (integrable_indicator_iff measurableSet_closedBall).2 hf.norm
  -- Step 4: `F_m → 1_{B_t(ξ)} f` pointwise: `F_m(x) = f(x)` for all `m` if `r ≤ t`, and
  -- `F_m(x) = 0` once `ε_m < r/t - 1` if `r > t`.
  have hlim : ∀ x, Tendsto (fun m ↦ φ m (‖x - ξ‖ / t) * f x) atTop
      (𝓝 ((closedBall ξ t).indicator f x)) := by
    intro x
    by_cases hx : x ∈ closedBall ξ t
    · rw [indicator_of_mem hx]
      have hle : ‖x - ξ‖ / t ≤ 1 := by
        rw [div_le_one ht, ← dist_eq_norm]
        exact hx
      simp only [hφ1 _ _ hle, one_mul]
      exact tendsto_const_nhds
    · rw [indicator_of_notMem hx]
      rw [mem_closedBall, dist_eq_norm, not_le] at hx
      have hδ : 0 < ‖x - ξ‖ / t - 1 := by
        rw [sub_pos, one_lt_div ht]
        exact hx
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hε.eventually (gt_mem_nhds hδ)] with m hm
      rw [hφ0 m _ (by linarith), zero_mul]
  -- Step 5: dominated convergence, and `∫ 1_{B_t(ξ)} f dμ = ∫_{B_t(ξ)} f dμ`.
  have h := tendsto_integral_of_dominated_convergence _ hmeas hbi hbound
    (Filter.Eventually.of_forall hlim)
  rwa [integral_indicator measurableSet_closedBall] at h
/-- **Monotonicity kernels: measurability, uniform bound, support and pointwise limit.**
Let `0 < σ ≤ ρ`, `εₘ → 0` with `0 < εₘ ≤ 1`, and let `φₘ` be nonincreasing with `φₘ = 1` on
`(-∞, 1]` and `φₘ = 0` on `[1 + εₘ, ∞)`. Put
`kₘ(s) = ∫_{(σ,ρ]} -(s/τ²) φₘ'(s/τ) / τⁿ dτ` and `Dₘ(s) = φₘ(s/ρ) - φₘ(s/σ)`. If
`Dₘ(s)/sⁿ ≤ kₘ(s) ≤ (1 + εₘ)ⁿ Dₘ(s)/sⁿ` for `s > 0`, then each `kₘ` is measurable,
`|kₘ(s)| ≤ 2ⁿ/σⁿ` for `s ≥ 0`, `kₘ(s) = 0` for `s > (1 + εₘ)ρ`, and
`kₘ(s) → 1_{(σ,ρ]}(s) s⁻ⁿ` for every `s ≥ 0`. -/
theorem Submission.weighted_mono_kernel_limit : ∀ (n : ℕ) (σ ρ : ℝ) (φ : ℕ → ℝ → ℝ) (ε : ℕ → ℝ), 0 < σ → σ ≤ ρ → Tendsto ε atTop (𝓝 0) → (∀ m, 0 < ε m ∧ ε m ≤ 1) → (∀ m, Antitone (φ m)) → (∀ m t, t ≤ 1 → φ m t = 1) → (∀ m t, 1 + ε m ≤ t → φ m t = 0) → (∀ m s, 0 < s → (φ m (s / ρ) - φ m (s / σ)) / s ^ n ≤ ∫ τ in Ioc σ ρ, -(s / τ ^ 2) * deriv (φ m) (s / τ) / τ ^ n ∧ ∫ τ in Ioc σ ρ, -(s / τ ^ 2) * deriv (φ m) (s / τ) / τ ^ n ≤ (1 + ε m) ^ n * ((φ m (s / ρ) - φ m (s / σ)) / s ^ n)) → (∀ m, Measurable (fun s ↦ ∫ τ in Ioc σ ρ, -(s / τ ^ 2) * deriv (φ m) (s / τ) / τ ^ n)) ∧ (∀ m s, 0 ≤ s → |∫ τ in Ioc σ ρ, -(s / τ ^ 2) * deriv (φ m) (s / τ) / τ ^ n| ≤ 2 ^ n / σ ^ n) ∧ (∀ m s, (1 + ε m) * ρ < s → ∫ τ in Ioc σ ρ, -(s / τ ^ 2) * deriv (φ m) (s / τ) / τ ^ n = 0) ∧ (∀ s, 0 ≤ s → Tendsto (fun m ↦ ∫ τ in Ioc σ ρ, -(s / τ ^ 2) * deriv (φ m) (s / τ) / τ ^ n) atTop (𝓝 ((Ioc σ ρ).indicator (fun s ↦ (s ^ n)⁻¹) s))) := by
  intro n σ ρ φ ε hσ hσρ hε hε01 hanti hone hzero hbd
  have hρ : 0 < ρ := hσ.trans_le hσρ
  -- Step 0: `0 ≤ φₘ ≤ 1`, by antitonicity and the boundary values.
  have hφ1 : ∀ m t, φ m t ≤ 1 := fun m t ↦
    (hanti m (min_le_left t 1)).trans_eq (hone m _ (min_le_right t 1))
  have hφ0 : ∀ m t, 0 ≤ φ m t := fun m t ↦
    (hzero m _ (le_max_right t (1 + ε m))).symm.le.trans (hanti m (le_max_left t (1 + ε m)))
  -- Step 1: `0 ≤ Dₘ(s) ≤ 1` for `s > 0`, and `Dₘ(s) = 0` for `0 < s ≤ σ`.
  have hdiv : ∀ s, 0 < s → s / ρ ≤ s / σ := fun s hs ↦ div_le_div_of_nonneg_left hs.le hσ hσρ
  have hD0 : ∀ m s, 0 < s → 0 ≤ φ m (s / ρ) - φ m (s / σ) := fun m s hs ↦
    sub_nonneg.2 (hanti m (hdiv s hs))
  have hD1 : ∀ m s, φ m (s / ρ) - φ m (s / σ) ≤ 1 := fun m s ↦ by
    linarith [hφ1 m (s / ρ), hφ0 m (s / σ)]
  have hDlo : ∀ m s, 0 < s → s ≤ σ → φ m (s / ρ) - φ m (s / σ) = 0 := by
    intro m s hs hsσ
    rw [hone m (s / ρ) ((div_le_one₀ hρ).2 (hsσ.trans hσρ)), hone m (s / σ) ((div_le_one₀ hσ).2 hsσ),
      sub_self]
  -- Step 2: where `Dₘ(s) = 0` (and `s > 0`), the assumed two-sided bound forces `kₘ(s) = 0`.
  have hsq : ∀ m s, 0 < s → φ m (s / ρ) - φ m (s / σ) = 0 →
      ∫ τ in Ioc σ ρ, -(s / τ ^ 2) * deriv (φ m) (s / τ) / τ ^ n = 0 := by
    intro m s hs hD
    obtain ⟨h1, h2⟩ := hbd m s hs
    rw [hD, zero_div] at h1
    rw [hD, zero_div, mul_zero] at h2
    exact le_antisymm h2 h1
  -- Step 3: `kₘ(s) = 0` for `0 ≤ s ≤ σ` (for `s = 0` the integrand vanishes).
  have hklo : ∀ m s, 0 ≤ s → s ≤ σ →
      ∫ τ in Ioc σ ρ, -(s / τ ^ 2) * deriv (φ m) (s / τ) / τ ^ n = 0 := by
    intro m s hs hsσ
    rcases hs.eq_or_lt with rfl | hs
    · simp
    · exact hsq m s hs (hDlo m s hs hsσ)
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (1) The integrand is Borel on `ℝ × ℝ` (`measurable_deriv`), so the parametric integral is
    -- measurable.
    intro m
    have hm : Measurable (fun p : ℝ × ℝ ↦ -(p.1 / p.2 ^ 2) * deriv (φ m) (p.1 / p.2) / p.2 ^ n) := by
      fun_prop
    exact (hm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc σ ρ))).measurable
  · -- (2) For `s > σ`: `0 ≤ kₘ(s) ≤ (1 + εₘ)ⁿ Dₘ(s)/sⁿ ≤ 2ⁿ · (1/σⁿ)`.
    intro m s hs
    rcases le_or_gt s σ with hsσ | hsσ
    · rw [hklo m s hs hsσ, abs_zero]
      positivity
    have hs0 : 0 < s := hσ.trans hsσ
    obtain ⟨h1, h2⟩ := hbd m s hs0
    have hDs : 0 ≤ (φ m (s / ρ) - φ m (s / σ)) / s ^ n :=
      div_nonneg (hD0 m s hs0) (pow_nonneg hs0.le n)
    rw [abs_of_nonneg (hDs.trans h1)]
    refine h2.trans ?_
    rw [div_eq_mul_one_div (2 ^ n) (σ ^ n)]
    refine mul_le_mul ?_ ?_ hDs (by positivity)
    · exact pow_le_pow_left₀ (by linarith [(hε01 m).1]) (by linarith [(hε01 m).2]) n
    · calc (φ m (s / ρ) - φ m (s / σ)) / s ^ n ≤ 1 / s ^ n :=
            div_le_div_of_nonneg_right (hD1 m s) (pow_nonneg hs0.le n)
        _ ≤ 1 / σ ^ n := one_div_le_one_div_of_le (pow_pos hσ n) (pow_le_pow_left₀ hσ.le hsσ.le n)
  · -- (3) For `s > (1 + εₘ)ρ`: `s/σ ≥ s/ρ ≥ 1 + εₘ`, so `Dₘ(s) = 0 - 0`.
    intro m s hs
    have hs0 : 0 < s := (mul_pos (by linarith [(hε01 m).1]) hρ).trans hs
    have h1 : 1 + ε m ≤ s / ρ := (le_div_iff₀ hρ).2 hs.le
    refine hsq m s hs0 ?_
    rw [hzero m _ h1, hzero m _ (h1.trans (hdiv s hs0)), sub_self]
  · -- (4) Pointwise limit, by cases on the position of `s`.
    intro s hs
    rcases le_or_gt s σ with hsσ | hsσ
    · -- `s ≤ σ`: `kₘ(s) = 0` for all `m`, and `s ∉ (σ, ρ]`.
      rw [indicator_of_notMem (fun h : s ∈ Ioc σ ρ ↦ (not_lt.2 hsσ) h.1)]
      exact tendsto_const_nhds.congr fun m ↦ (hklo m s hs hsσ).symm
    have hs0 : 0 < s := hσ.trans hsσ
    rcases le_or_gt s ρ with hsρ | hsρ
    · -- `σ < s ≤ ρ`: eventually `Dₘ(s) = 1 - 0`; squeeze between `s⁻ⁿ` and `(1 + εₘ)ⁿ s⁻ⁿ`.
      rw [indicator_of_mem (show s ∈ Ioc σ ρ from ⟨hsσ, hsρ⟩)]
      have hev : ∀ᶠ m in atTop, ε m < s / σ - 1 :=
        hε.eventually_lt_const (by rw [sub_pos, one_lt_div₀ hσ]; exact hsσ)
      have hD : ∀ᶠ m in atTop, φ m (s / ρ) - φ m (s / σ) = 1 := by
        filter_upwards [hev] with m hm
        rw [hone m _ ((div_le_one₀ hρ).2 hsρ), hzero m _ (by linarith), sub_zero]
      have hup : Tendsto (fun m ↦ (1 + ε m) ^ n * (s ^ n)⁻¹) atTop (𝓝 ((s ^ n)⁻¹)) := by
        have h := ((tendsto_const_nhds (x := (1 : ℝ))).add hε).pow n |>.mul_const (s ^ n)⁻¹
        rwa [add_zero, one_pow, one_mul] at h
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
      · filter_upwards [hD] with m hm
        have h := (hbd m s hs0).1
        rwa [hm, one_div] at h
      · filter_upwards [hD] with m hm
        have h := (hbd m s hs0).2
        rwa [hm, one_div] at h
    · -- `s > ρ`: eventually `s/σ ≥ s/ρ ≥ 1 + εₘ`, so `kₘ(s) = 0`; and `s ∉ (σ, ρ]`.
      rw [indicator_of_notMem (fun h : s ∈ Ioc σ ρ ↦ (not_le.2 hsρ) h.2)]
      have hev : ∀ᶠ m in atTop, ε m < s / ρ - 1 :=
        hε.eventually_lt_const (by rw [sub_pos, one_lt_div₀ hρ]; exact hsρ)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with m hm
      have h1 : 1 + ε m ≤ s / ρ := by linarith
      refine (hsq m s hs0 ?_).symm
      rw [hzero m _ h1, hzero m _ (h1.trans (hdiv s hs0)), sub_self]
/-- **Annulus term of the limit 3.5 → 3.6** (Simon Ch. 4, p. 90: letting the cutoff decrease to
the indicator of `(-∞, 1]`). With `r = ‖x - ξ‖`, `x ∈ B_ρ(ξ) \ B_σ(ξ)` iff `r ∈ (σ, ρ]`, and there
`|u (q / rⁿ)| ≤ A / σⁿ`, so the limit integrand is integrable on the annulus. The integrands
`u q k_m(r)` vanish off `B_R(ξ)`, are dominated by `A C 1_{B_R(ξ)}`, and converge pointwise to
`1_{B_ρ(ξ) \ B_σ(ξ)} u (q / rⁿ)`; dominated convergence and `integral_indicator` give the limit. -/
theorem Submission.weighted_mono_kernel_term_tendsto : ∀ (n ℓ : ℕ) (μ : Measure (Ambient n ℓ)) (u q : Ambient n ℓ → ℝ) (ξ : Ambient n ℓ) (σ ρ R A C : ℝ) (k : ℕ → ℝ → ℝ), IsFiniteMeasureOnCompacts μ → 0 < σ → ρ ≤ R → AEStronglyMeasurable u (μ.restrict (closedBall ξ R)) → AEStronglyMeasurable q (μ.restrict (closedBall ξ R)) → (∀ x ∈ closedBall ξ R, |u x| ≤ A ∧ |q x| ≤ 1) → (∀ m, Measurable (k m)) → (∀ m s, 0 ≤ s → |k m s| ≤ C) → (∀ m s, R < s → k m s = 0) → (∀ s, 0 ≤ s → Tendsto (fun m ↦ k m s) atTop (𝓝 ((Ioc σ ρ).indicator (fun s ↦ (s ^ n)⁻¹) s))) → IntegrableOn (fun x ↦ u x * (q x / ‖x - ξ‖ ^ n)) (closedBall ξ ρ \ closedBall ξ σ) μ ∧ Tendsto (fun m ↦ ∫ x, u x * q x * k m ‖x - ξ‖ ∂μ) atTop (𝓝 (∫ x in closedBall ξ ρ \ closedBall ξ σ, u x * (q x / ‖x - ξ‖ ^ n) ∂μ)) := by
  intro n ℓ μ u q ξ σ ρ R A C k hμ hσ hρR hu hq hbd hk hkC hk0 hlim
  -- `μ (B_R(ξ)) < ∞`, the annulus lies in `B_R(ξ)`, and `x` is in it iff `‖x - ξ‖ ∈ (σ, ρ]`
  have hBfin : μ (closedBall ξ R) < ⊤ := measure_closedBall_lt_top
  have hAB : closedBall ξ ρ \ closedBall ξ σ ⊆ closedBall ξ R :=
    fun x hx ↦ closedBall_subset_closedBall hρR hx.1
  have hAm : MeasurableSet (closedBall ξ ρ \ closedBall ξ σ) :=
    measurableSet_closedBall.diff measurableSet_closedBall
  have hmemA : ∀ x, x ∈ closedBall ξ ρ \ closedBall ξ σ ↔ ‖x - ξ‖ ∈ Ioc σ ρ := by
    intro x
    simp only [Set.mem_sdiff, mem_closedBall, dist_eq_norm, mem_Ioc, not_le]
    tauto
  have hnotB : ∀ x, x ∉ closedBall ξ R → R < ‖x - ξ‖ := by
    intro x hx
    simpa [mem_closedBall, dist_eq_norm] using hx
  -- integrability on the annulus, where the integrand is bounded by `A / σⁿ`
  have hint : IntegrableOn (fun x ↦ u x * (q x / ‖x - ξ‖ ^ n))
      (closedBall ξ ρ \ closedBall ξ σ) μ := by
    have hmono : μ.restrict (closedBall ξ ρ \ closedBall ξ σ) ≤ μ.restrict (closedBall ξ R) :=
      Measure.restrict_mono hAB le_rfl
    have hrc : Continuous fun x : Ambient n ℓ ↦ ‖x - ξ‖ ^ n := by fun_prop
    refine IntegrableOn.of_bound ((measure_mono hAB).trans_lt hBfin)
      ((hu.mono_measure hmono).mul ((hq.mono_measure hmono).div₀ hrc.aestronglyMeasurable))
      (A / σ ^ n) ?_
    filter_upwards [ae_restrict_mem hAm] with x hx
    obtain ⟨hux, hqx⟩ := hbd x (hAB hx)
    have hA : 0 ≤ A := (abs_nonneg _).trans hux
    have hσn : 0 < σ ^ n := pow_pos hσ n
    have hrn : σ ^ n ≤ ‖x - ξ‖ ^ n := pow_le_pow_left₀ hσ.le ((hmemA x).1 hx).1.le n
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos (hσn.trans_le hrn)]
    calc |u x| * (|q x| / ‖x - ξ‖ ^ n) ≤ A * (1 / ‖x - ξ‖ ^ n) := by gcongr
      _ ≤ A * (1 / σ ^ n) := by gcongr
      _ = A / σ ^ n := by ring
  refine ⟨hint, ?_⟩
  -- dominated convergence with bound `A C 1_{B_R(ξ)}`
  rw [← integral_indicator hAm]
  refine tendsto_integral_filter_of_dominated_convergence
    ((closedBall ξ R).indicator fun _ ↦ A * C) ?_ ?_ ?_ ?_
  · -- `u q k_m(r)` vanishes off `B_R(ξ)` and is a.e. strongly measurable on `B_R(ξ)`
    refine Eventually.of_forall fun m ↦ ?_
    have hF : (fun x ↦ u x * q x * k m ‖x - ξ‖) =
        (closedBall ξ R).indicator fun x ↦ u x * q x * k m ‖x - ξ‖ := by
      funext x
      by_cases hx : x ∈ closedBall ξ R
      · rw [indicator_of_mem hx]
      · rw [indicator_of_notMem hx, hk0 m _ (hnotB x hx), mul_zero]
    rw [hF, aestronglyMeasurable_indicator_iff measurableSet_closedBall]
    have hkm : Measurable fun x : Ambient n ℓ ↦ k m ‖x - ξ‖ :=
      (hk m).comp (continuous_norm.comp (continuous_id.sub continuous_const)).measurable
    exact (hu.mul hq).mul hkm.aestronglyMeasurable
  · -- `|u q k_m(r)| ≤ A C` on `B_R(ξ)` and `= 0` off it
    refine Eventually.of_forall fun m ↦ Eventually.of_forall fun x ↦ ?_
    by_cases hx : x ∈ closedBall ξ R
    · rw [indicator_of_mem hx]
      obtain ⟨hux, hqx⟩ := hbd x hx
      have hA : 0 ≤ A := (abs_nonneg _).trans hux
      have hkx := hkC m ‖x - ξ‖ (norm_nonneg _)
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      calc |u x| * |q x| * |k m ‖x - ξ‖| ≤ A * 1 * C := by gcongr
        _ = A * C := by ring
    · rw [indicator_of_notMem hx, hk0 m _ (hnotB x hx), mul_zero, norm_zero]
  · exact (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const hBfin.ne)
  · -- pointwise limit `u q 1_{(σ, ρ]}(r) r⁻ⁿ = 1_{B_ρ(ξ) \ B_σ(ξ)} u (q / rⁿ)`
    refine Eventually.of_forall fun x ↦ ?_
    convert (hlim ‖x - ξ‖ (norm_nonneg _)).const_mul (u x * q x) using 2
    by_cases hx : x ∈ closedBall ξ ρ \ closedBall ξ σ
    · rw [indicator_of_mem hx, indicator_of_mem ((hmemA x).1 hx)]
      ring
    · rw [indicator_of_notMem hx, indicator_of_notMem fun h ↦ hx ((hmemA x).2 h)]
      ring

/-- **Curvature term of the `h`-weighted monotonicity identity** (Simon Ch. 4, 5.1, p. 96:
integrate 5.1 over `(σ, ρ]` and let `φ` increase to `1_{(-∞, 1]}`; `G` stands for
`(x - ξ) · (∇^M h + hH)`). Let `G` be `μ`-integrable on `B_R(ξ)`, `0 < σ ≤ ρ`, and let `φ_m` be
continuous with `0 ≤ φ_m ≤ 1`, `φ_m = 1` on `(-∞, 1]` and `φ_m = 0` on `[1 + ε_m, ∞)`, where
`ε_m > 0`, `ε_m → 0` and `(1 + ε_m)ρ ≤ R`. Then `τ ↦ τ^{-n-1} ∫_{B_τ(ξ)} G dμ` is integrable on
`(σ, ρ]` and `∫_{(σ,ρ]} τ^{-n-1} ∫ φ_m(|x - ξ|/τ) G(x) dμ(x) dτ` converges to its integral.
For `0 < τ ≤ ρ` the `x`-integrand vanishes off `B_R(ξ)` and is dominated by `g = 1_{B_R(ξ)} |G|`,
so `L_m(τ) = ∫ φ_m(|x - ξ|/τ) G dμ` is continuous on `[σ, ρ]` with `|L_m| ≤ C = ∫ g dμ`;
`weighted_mono_cutoff_integral_tendsto` gives `L_m(τ) → ∫_{B_τ(ξ)} G dμ` on `(σ, ρ]`, and dominated
convergence with the constant bound `C/σ^{n+1}` concludes. -/
theorem Submission.weighted_mono_curvature_term_tendsto : ∀ (n ℓ : ℕ) (μ : Measure (Ambient n ℓ)) (G : Ambient n ℓ → ℝ) (ξ : Ambient n ℓ) (σ ρ R : ℝ) (φ : ℕ → ℝ → ℝ) (ε : ℕ → ℝ), 0 < σ → σ ≤ ρ → IntegrableOn G (closedBall ξ R) μ → Tendsto ε atTop (𝓝 0) → (∀ m, 0 < ε m) → (∀ m, (1 + ε m) * ρ ≤ R) → (∀ m, Continuous (φ m)) → (∀ m s, 0 ≤ φ m s ∧ φ m s ≤ 1) → (∀ m s, s ≤ 1 → φ m s = 1) → (∀ m s, 1 + ε m ≤ s → φ m s = 0) → IntegrableOn (fun τ ↦ (∫ x in closedBall ξ τ, G x ∂μ) / τ ^ (n + 1)) (Ioc σ ρ) ∧ Tendsto (fun m ↦ ∫ τ in Ioc σ ρ, (∫ x, φ m (‖x - ξ‖ / τ) * G x ∂μ) / τ ^ (n + 1)) atTop (𝓝 (∫ τ in Ioc σ ρ, (∫ x in closedBall ξ τ, G x ∂μ) / τ ^ (n + 1))) := by
  intro n ℓ μ G ξ σ ρ R φ ε hσ hσρ hG hε hεpos hεR hφc hφ01 hφ1 hφ0
  -- Step 1: for `0 < τ ≤ ρ` the cutoff vanishes off `B_R(ξ)`, as `(1 + ε_m)τ ≤ R < |x - ξ|`
  have hvan : ∀ m τ x, 0 < τ → τ ≤ ρ → x ∉ closedBall ξ R → φ m (‖x - ξ‖ / τ) = 0 := by
    intro m τ x hτ hτρ hx
    rw [mem_closedBall, dist_eq_norm, not_le] at hx
    refine hφ0 m _ ((le_div_iff₀ hτ).2 ?_)
    have := mul_le_mul_of_nonneg_left hτρ (by linarith [hεpos m] : (0 : ℝ) ≤ 1 + ε m)
    linarith [hεR m]
  -- Step 2: the `x`-integrands are a.e. strongly measurable and dominated by `g = 1_{B_R(ξ)} |G|`
  obtain ⟨g, hg⟩ : ∃ g : Ambient n ℓ → ℝ, g = (closedBall ξ R).indicator fun x ↦ ‖G x‖ :=
    ⟨_, rfl⟩
  have hg_int : Integrable g μ := by
    rw [hg]
    exact IntegrableOn.integrable_indicator (Integrable.norm hG) measurableSet_closedBall
  have hg0 : ∀ x, 0 ≤ g x := by
    rw [hg]
    exact indicator_nonneg fun x _ ↦ norm_nonneg _
  have hdom : ∀ m τ x, 0 < τ → τ ≤ ρ → ‖φ m (‖x - ξ‖ / τ) * G x‖ ≤ g x := by
    intro m τ x hτ hτρ
    by_cases hx : x ∈ closedBall ξ R
    · rw [hg, indicator_of_mem hx, norm_mul, Real.norm_of_nonneg (hφ01 m _).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (hφ01 m _).2
    · rw [hvan m τ x hτ hτρ hx, zero_mul, norm_zero]
      exact hg0 x
  have hmeas : ∀ m τ, 0 < τ → τ ≤ ρ →
      AEStronglyMeasurable (fun x ↦ φ m (‖x - ξ‖ / τ) * G x) μ := by
    intro m τ hτ hτρ
    have hc : Continuous fun x : Ambient n ℓ ↦ φ m (‖x - ξ‖ / τ) :=
      (hφc m).comp ((continuous_id.sub continuous_const).norm.div_const τ)
    have hind : (closedBall ξ R).indicator (fun x ↦ φ m (‖x - ξ‖ / τ) * G x) =
        fun x ↦ φ m (‖x - ξ‖ / τ) * G x := by
      funext x
      by_cases hx : x ∈ closedBall ξ R
      · rw [indicator_of_mem hx]
      · rw [indicator_of_notMem hx, hvan m τ x hτ hτρ hx, zero_mul]
    rw [← hind]
    exact (aestronglyMeasurable_indicator_iff measurableSet_closedBall).2
      (hc.aestronglyMeasurable.mul hG.aestronglyMeasurable)
  -- Step 3: `|L_m(τ)| ≤ C = ∫ g dμ` for `0 < τ ≤ ρ`
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = ∫ x, g x ∂μ := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by
    rw [hC]
    exact integral_nonneg hg0
  have hLbd : ∀ m τ, 0 < τ → τ ≤ ρ → ‖∫ x, φ m (‖x - ξ‖ / τ) * G x ∂μ‖ ≤ C := by
    intro m τ hτ hτρ
    rw [hC]
    exact norm_integral_le_of_norm_le hg_int (Eventually.of_forall fun x ↦ hdom m τ x hτ hτρ)
  -- Step 4: `L_m` is continuous on `[σ, ρ]` (continuity of dominated parameter integrals)
  have hLcont : ∀ m, ContinuousOn (fun τ ↦ ∫ x, φ m (‖x - ξ‖ / τ) * G x ∂μ) (Icc σ ρ) := by
    intro m
    refine continuousOn_of_dominated (fun τ hτ ↦ hmeas m τ (hσ.trans_le hτ.1) hτ.2)
      (fun τ hτ ↦ Eventually.of_forall fun x ↦ hdom m τ x (hσ.trans_le hτ.1) hτ.2) hg_int
      (Eventually.of_forall fun x ↦ ?_)
    refine ContinuousOn.mul ((hφc m).comp_continuousOn ?_) continuousOn_const
    exact continuousOn_const.div continuousOn_id fun τ hτ ↦ (hσ.trans_le hτ.1).ne'
  -- Step 5: `h_m(τ) = L_m(τ)/τ^{n+1}` is continuous on `[σ, ρ]`, so a.e. strongly measurable on
  -- `(σ, ρ]`
  have hhmeas : ∀ m, AEStronglyMeasurable
      (fun τ ↦ (∫ x, φ m (‖x - ξ‖ / τ) * G x ∂μ) / τ ^ (n + 1)) (volume.restrict (Ioc σ ρ)) := by
    intro m
    have hcont : ContinuousOn (fun τ ↦ (∫ x, φ m (‖x - ξ‖ / τ) * G x ∂μ) / τ ^ (n + 1))
        (Icc σ ρ) :=
      (hLcont m).div (continuous_pow (n + 1)).continuousOn fun τ hτ ↦
        pow_ne_zero _ (hσ.trans_le hτ.1).ne'
    exact (hcont.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  -- Step 6: pointwise convergence on `(σ, ρ]`, by the sibling lemma at `t = τ`
  have hlim : ∀ τ ∈ Ioc σ ρ, Tendsto (fun m ↦ (∫ x, φ m (‖x - ξ‖ / τ) * G x ∂μ) / τ ^ (n + 1))
      atTop (𝓝 ((∫ x in closedBall ξ τ, G x ∂μ) / τ ^ (n + 1))) := by
    intro τ hτ
    have hτR : ∀ m, (1 + ε m) * τ ≤ R := fun m ↦
      (mul_le_mul_of_nonneg_left hτ.2 (by linarith [hεpos m])).trans (hεR m)
    exact (Submission.weighted_mono_cutoff_integral_tendsto n ℓ μ G ξ τ R φ ε (hσ.trans hτ.1) hG
      hε hτR (fun m ↦ (hφc m).measurable) hφ01 hφ1 hφ0).div_const _
  -- Step 7: `|h_m(τ)| ≤ C/σ^{n+1}` on `(σ, ρ]`
  have hhbd : ∀ m, ∀ τ ∈ Ioc σ ρ,
      ‖(∫ x, φ m (‖x - ξ‖ / τ) * G x ∂μ) / τ ^ (n + 1)‖ ≤ C / σ ^ (n + 1) := by
    intro m τ hτ
    have hτ0 : 0 < τ := hσ.trans hτ.1
    rw [norm_div, norm_pow, Real.norm_of_nonneg hτ0.le]
    exact (div_le_div_of_nonneg_right (hLbd m τ hτ0 hτ.2) (pow_nonneg hτ0.le _)).trans
      (div_le_div_of_nonneg_left hC0 (pow_pos hσ _) (pow_le_pow_left₀ hσ.le hτ.1.le _))
  -- Step 8: the limit is a.e. strongly measurable and bounded by `C/σ^{n+1}`, so integrable
  have hlim_ae := ae_restrict_of_forall_mem (μ := volume) measurableSet_Ioc hlim
  have hint : IntegrableOn (fun τ ↦ (∫ x in closedBall ξ τ, G x ∂μ) / τ ^ (n + 1)) (Ioc σ ρ) :=
    IntegrableOn.of_bound measure_Ioc_lt_top
      (aestronglyMeasurable_of_tendsto_ae atTop hhmeas hlim_ae) (C / σ ^ (n + 1))
      (ae_restrict_of_forall_mem measurableSet_Ioc fun τ hτ ↦
        le_of_tendsto (hlim τ hτ).norm (Eventually.of_forall fun m ↦ hhbd m τ hτ))
  -- Step 9: dominated convergence on `(σ, ρ]` with the constant bound `C/σ^{n+1}`
  exact ⟨hint, tendsto_integral_filter_of_dominated_convergence (fun _ ↦ C / σ ^ (n + 1))
    (Eventually.of_forall hhmeas)
    (Eventually.of_forall fun m ↦ ae_restrict_of_forall_mem measurableSet_Ioc (hhbd m))
    (integrableOn_const measure_Ioc_lt_top.ne) hlim_ae⟩
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

/-- **Removing the cutoff from the weighted monotonicity identity** (Simon Ch. 4, p. 90, 3.5 → 3.6,
and the same limit before 3.17: letting `ε ↓ 0`, so that `φ` decreases to the indicator of
`(-∞, 1]`). If the smoothed identity `(S_φ)` holds for every `C¹` nonincreasing cutoff `φ` of width
`ε` with `(1 + ε)ρ < R`, apply it to the cutoffs `φₘ` of `weighted_mono_cutoff_seq_exists` with
widths `εₘ < min(1, (R - ρ)/ρ)`. Each term converges: the cutoff integrals of `u` by
`weighted_mono_cutoff_integral_tendsto`, the kernel term by `weighted_mono_kernel_term_tendsto`
(kernel facts from `weighted_mono_kernel_bounds` and `weighted_mono_kernel_limit`) and the
curvature term by `weighted_mono_curvature_term_tendsto`; these two also give (ii) and (i).
Uniqueness of limits gives the identity (iii). -/
theorem Submission.weighted_mono_cutoff_limit : ∀ (n ℓ : ℕ) (μ : Measure (Ambient n ℓ)) (u q G : Ambient n ℓ → ℝ) (ξ : Ambient n ℓ) (σ ρ R A : ℝ), IsFiniteMeasureOnCompacts μ → 0 < σ → σ ≤ ρ → ρ < R → AEStronglyMeasurable u (μ.restrict (closedBall ξ R)) → AEStronglyMeasurable q (μ.restrict (closedBall ξ R)) → (∀ x ∈ closedBall ξ R, |u x| ≤ A ∧ |q x| ≤ 1) → IntegrableOn G (closedBall ξ R) μ → (∀ (ε : ℝ) (φ : ℝ → ℝ), 0 < ε → (1 + ε) * ρ < R → ContDiff ℝ 1 φ → Antitone φ → (∀ t, t ≤ 1 → φ t = 1) → (∀ t, 1 + ε ≤ t → φ t = 0) → (∫ x, u x * φ (‖x - ξ‖ / ρ) ∂μ) / ρ ^ n - (∫ x, u x * φ (‖x - ξ‖ / σ) ∂μ) / σ ^ n = ∫ x, u x * q x * (∫ τ in Ioc σ ρ, -(‖x - ξ‖ / τ ^ 2) * deriv φ (‖x - ξ‖ / τ) / τ ^ n) ∂μ + ∫ τ in Ioc σ ρ, (∫ x, φ (‖x - ξ‖ / τ) * G x ∂μ) / τ ^ (n + 1)) → IntegrableOn (fun τ ↦ (∫ x in closedBall ξ τ, G x ∂μ) / τ ^ (n + 1)) (Ioc σ ρ) ∧ IntegrableOn (fun x ↦ u x * (q x / ‖x - ξ‖ ^ n)) (closedBall ξ ρ \ closedBall ξ σ) μ ∧ (∫ x in closedBall ξ ρ, u x ∂μ) / ρ ^ n - (∫ x in closedBall ξ σ, u x ∂μ) / σ ^ n = ∫ x in closedBall ξ ρ \ closedBall ξ σ, u x * (q x / ‖x - ξ‖ ^ n) ∂μ + ∫ τ in Ioc σ ρ, (∫ x in closedBall ξ τ, G x ∂μ) / τ ^ (n + 1) := by
  intro n ℓ μ u q G ξ σ ρ R A hμ hσ hσρ hρR hu hq hbd hG hS
  have hρ : 0 < ρ := hσ.trans_le hσρ
  -- Step 1: cutoffs `φₘ` with widths `εₘ < min(1, (R - ρ)/ρ)`, so `εₘ ≤ 1` and `(1 + εₘ)ρ < R`;
  -- hence `(S_{φₘ})` holds for every `m`.
  obtain ⟨φ, ε, hε, hφ⟩ :=
    Submission.weighted_mono_cutoff_seq_exists _ (lt_min one_pos (div_pos (sub_pos.2 hρR) hρ))
  have hε0 : ∀ m, 0 < ε m := fun m ↦ (hφ m).1
  have hε1 : ∀ m, ε m ≤ 1 := fun m ↦ ((hφ m).2.1.trans_le (min_le_left _ _)).le
  have hC1 : ∀ m, ContDiff ℝ 1 (φ m) := fun m ↦ (hφ m).2.2.1
  have hanti : ∀ m, Antitone (φ m) := fun m ↦ (hφ m).2.2.2.1
  have hone : ∀ m t, t ≤ 1 → φ m t = 1 := fun m ↦ (hφ m).2.2.2.2.1
  have hzero : ∀ m t, 1 + ε m ≤ t → φ m t = 0 := fun m ↦ (hφ m).2.2.2.2.2.1
  have h01 : ∀ m t, 0 ≤ φ m t ∧ φ m t ≤ 1 := fun m ↦ (hφ m).2.2.2.2.2.2
  have hεR : ∀ m, (1 + ε m) * ρ < R := by
    intro m
    have h := (hφ m).2.1.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ hρ] at h
    linarith
  have hSm := fun m ↦ hS (ε m) (φ m) (hε0 m) (hεR m) (hC1 m) (hanti m) (hone m) (hzero m)
  -- Step 2: the kernels `kₘ(s) = ∫_{(σ,ρ]} -(s/τ²) φₘ'(s/τ) / τⁿ dτ` are measurable, bounded by
  -- `2ⁿ/σⁿ`, vanish for `s > (1 + εₘ)ρ` (so for `s > R`), and tend to `1_{(σ,ρ]}(s) s⁻ⁿ`.
  obtain ⟨hkm, hkC, hk0, hklim⟩ := Submission.weighted_mono_kernel_limit n σ ρ φ ε hσ hσρ hε
    (fun m ↦ ⟨hε0 m, hε1 m⟩) hanti hone hzero fun m s hs ↦
      Submission.weighted_mono_kernel_bounds n (φ m) (ε m) σ ρ s (hC1 m) (hanti m) (hone m)
        (hzero m) (hε0 m) hσ hσρ hs
  -- Step 3: (ii) and the limit of the kernel term `∫ u q kₘ(r) dμ`.
  obtain ⟨hii, hK⟩ := Submission.weighted_mono_kernel_term_tendsto n ℓ μ u q ξ σ ρ R A
    (2 ^ n / σ ^ n) (fun m s ↦ ∫ τ in Ioc σ ρ, -(s / τ ^ 2) * deriv (φ m) (s / τ) / τ ^ n) hμ hσ
    hρR.le hu hq hbd hkm hkC (fun m s hs ↦ hk0 m s ((hεR m).trans hs)) hklim
  -- Step 4: (i) and the limit of the curvature term `∫_{(σ,ρ]} (∫ φₘ(r/τ) G dμ) / τⁿ⁺¹ dτ`.
  obtain ⟨hi, hT⟩ := Submission.weighted_mono_curvature_term_tendsto n ℓ μ G ξ σ ρ R φ ε hσ hσρ hG
    hε hε0 (fun m ↦ (hεR m).le) (fun m ↦ (hC1 m).continuous) h01 hone hzero
  -- Step 5: the cutoff integrals of `u` (integrable on `B_R(ξ)`, being bounded there) at the radii
  -- `ρ` and `σ`, using `(1 + εₘ)σ ≤ (1 + εₘ)ρ < R`.
  have huR : IntegrableOn u (closedBall ξ R) μ := by
    refine IntegrableOn.of_bound measure_closedBall_lt_top hu A ?_
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
    exact (hbd x hx).1
  have hmeas : ∀ m, Measurable (φ m) := fun m ↦ (hC1 m).continuous.measurable
  have hUρ := Submission.weighted_mono_cutoff_integral_tendsto n ℓ μ u ξ ρ R φ ε hρ huR hε
    (fun m ↦ (hεR m).le) hmeas h01 hone hzero
  have hUσ := Submission.weighted_mono_cutoff_integral_tendsto n ℓ μ u ξ σ R φ ε hσ huR hε
    (fun m ↦ (mul_le_mul_of_nonneg_left hσρ (by linarith [hε0 m])).trans (hεR m).le) hmeas h01
    hone hzero
  have hcomm : ∀ m (t : ℝ), ∫ x, φ m (‖x - ξ‖ / t) * u x ∂μ = ∫ x, u x * φ m (‖x - ξ‖ / t) ∂μ :=
    fun m t ↦ integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)
  -- Step 6: both sides of `(S_{φₘ})` converge, so their limits (iii) agree.
  refine ⟨hi, hii, tendsto_nhds_unique (((hUρ.div_const (ρ ^ n)).sub
    (hUσ.div_const (σ ^ n))).congr fun m ↦ ?_) ((hK.add hT).congr fun m ↦ (hSm m).symm)⟩
  rw [hcomm, hcomm]

theorem main_theorem : ApproxTangentAE ∧ FirstVariationFormula ∧ StationaryIffVariational ∧ StationaryMonotonicity ∧ StationaryDensity ∧ CanonicalRepresentative ∧ BoundedCurvatureMonotonicity ∧ LogarithmicMonotonicityError ∧ LpMonotonicity ∧ LpDensity ∧ LpSupportRepresentation ∧ PoincareInequality ∧ SobolevInequality ∧ SupportInBall ∧ ConvexHullProperty ∧ ClassicalTangent := by sorry

end

end GMT.Ch04
