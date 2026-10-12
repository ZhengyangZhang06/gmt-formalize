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

/-- **Image-ball bound for a lower-Lipschitz piece.** If `F : ℝⁿ → ℝ^{n+ℓ}` is `K`-Lipschitz and
`c ‖v - w‖ ≤ ‖F v - F w‖` for every `v ∈ C`, then `Hⁿ(F(C) ∩ B_ρ(F w)) ≤ Kⁿ ωₙ c⁻ⁿ ρⁿ` for all
`ρ > 0` (the uniform upper density bound in the blow-up of a Lipschitz piece). -/
theorem Submission.ts_pdb_image_closedBall_measure_le : ∀ (n ℓ : ℕ) (C : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → Ambient n ℓ) (K : NNReal) (c : ℝ) (w : EuclideanSpace ℝ (Fin n)), LipschitzWith K F → 0 < c → (∀ v ∈ C, c * ‖v - w‖ ≤ ‖F v - F w‖) → ∀ ρ : ℝ, 0 < ρ → (μHE[n] : Measure (Ambient n ℓ)) (F '' C ∩ closedBall (F w) ρ) ≤ ENNReal.ofReal ((K : ℝ) ^ n * omega n / c ^ n * ρ ^ n) := by
  intro n ℓ C F K c w hF hc hCw ρ hρ
  -- `F(C) ∩ B_ρ(F w) ⊆ F(S)` with `S = C ∩ B_{ρ/c}(w)`, by the lower bound at `w`.
  have hsub : F '' C ∩ closedBall (F w) ρ ⊆ F '' (C ∩ closedBall w (ρ / c)) := by
    rintro _ ⟨⟨v, hv, rfl⟩, hvρ⟩
    refine ⟨v, ⟨hv, ?_⟩, rfl⟩
    rw [mem_closedBall, dist_eq_norm] at hvρ
    rw [mem_closedBall, dist_eq_norm, le_div_iff₀ hc]
    linarith [hCw v hv]
  -- `Hⁿ(S) ≤ Lⁿ(B_{ρ/c}(w)) = (ρ/c)ⁿ ωₙ`, as `Hⁿ = Lⁿ` on `ℝⁿ`.
  have hS : μHE[n] (C ∩ closedBall w (ρ / c)) ≤
      ENNReal.ofReal ((ρ / c) ^ n) * ENNReal.ofReal (omega n) := by
    rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume, omega,
      ENNReal.ofReal_toReal measure_ball_lt_top.ne]
    refine (measure_mono inter_subset_right).trans_eq ?_
    rw [Measure.addHaar_closedBall _ _ (div_pos hρ hc).le, finrank_euclideanSpace_fin]
  -- Lipschitz image bound `Hⁿ(F(S)) ≤ Kⁿ Hⁿ(S)`, then `Kⁿ (ρ/c)ⁿ ωₙ = Kⁿ ωₙ / cⁿ ρⁿ`.
  have hω : 0 ≤ omega n := ENNReal.toReal_nonneg
  calc (μHE[n] : Measure (Ambient n ℓ)) (F '' C ∩ closedBall (F w) ρ)
      ≤ μHE[n] (F '' (C ∩ closedBall w (ρ / c))) := measure_mono hsub
    _ ≤ (K : ℝ≥0∞) ^ n * μHE[n] (C ∩ closedBall w (ρ / c)) :=
        Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
          hF.lipschitzOnWith
    _ ≤ (K : ℝ≥0∞) ^ n * (ENNReal.ofReal ((ρ / c) ^ n) * ENNReal.ofReal (omega n)) := by
        gcongr
    _ = ENNReal.ofReal ((K : ℝ) ^ n * omega n / c ^ n * ρ ^ n) := by
        rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_pow K.coe_nonneg,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
/-- **Area formula on a Lipschitz piece.** Let `C ⊆ ℝⁿ` be Borel and `F : ℝⁿ → ℝ^{n+ℓ}` be
Lipschitz, injective on `C`, with `DF` continuous on `C`. Then the Gram-determinant Jacobian
`J = √det (⟪DF eᵢ, DF eⱼ⟫)` is continuous on `C`, satisfies `Hⁿ(DF(v)(S)) = J(v) Lⁿ(S)` for
`v ∈ C`, and `∫_{F(C)} g dHⁿ = ∫_C J(v) g(F(v)) dv` for every continuous `g`. -/
theorem Submission.ts_pdb_piece_area_formula : ∀ (n ℓ : ℕ) (C : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → Ambient n ℓ) (K : NNReal), MeasurableSet C → LipschitzWith K F → Set.InjOn F C → ContinuousOn (fderiv ℝ F) C → ∃ J : EuclideanSpace ℝ (Fin n) → ℝ, ContinuousOn J C ∧ (∀ v ∈ C, 0 ≤ J v ∧ ∀ S : Set (EuclideanSpace ℝ (Fin n)), (μHE[n] : Measure (Ambient n ℓ)) (fderiv ℝ F v '' S) = ENNReal.ofReal (J v) * volume S) ∧ ∀ g : Ambient n ℓ → ℝ, Continuous g → ∫ y in F '' C, g y ∂μHE[n] = ∫ v in C, J v * g (F v) := by
  intro n ℓ C F K hC hF hinj hcont
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
  /- Linear area factor: `Hⁿ(A(S)) = Jl A · Lⁿ(S)` for every `S`. -/
  have hlin : ∀ (A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ)
      (S : Set (EuclideanSpace ℝ (Fin n))),
      (μHE[n] : Measure (Ambient n ℓ)) (A '' S) = ENNReal.ofReal (Jl A) * volume S := by
    intro A S
    by_cases hA : Function.Injective A
    · obtain ⟨T, hT, hjT⟩ := LA1 A hA
      have hTinj : Function.Injective T := by
        intro a b hab
        apply hA
        rw [← sub_eq_zero, ← map_sub, ← norm_eq_zero, hT, map_sub, hab, sub_self, norm_zero]
      let Te := LinearEquiv.ofInjectiveEndo T hTinj
      let Φ : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] Ambient n ℓ :=
        (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] Ambient n ℓ) ∘ₗ Te.symm.toLinearMap
      have hTe : ∀ y, T (Te.symm y) = y := fun y => Te.apply_symm_apply y
      have hΦ : Isometry Φ := AddMonoidHomClass.isometry_of_norm Φ fun y => by
        simp only [Φ, LinearMap.comp_apply, LinearEquiv.coe_coe, ContinuousLinearMap.coe_coe]
        rw [hT, hTe]
      have himg : A '' S = Φ '' (T '' S) := by
        rw [Set.image_image]
        refine Set.image_congr fun z _ => ?_
        simp only [Φ, LinearMap.comp_apply, LinearEquiv.coe_coe, ContinuousLinearMap.coe_coe]
        exact (congrArg A (Te.symm_apply_apply z)).symm
      rw [himg, hΦ.euclideanHausdorffMeasure_image, hvol, hjT]
      exact Measure.addHaar_image_linearMap volume T S
    · rw [LA2 A hA, ENNReal.ofReal_zero, zero_mul]
      have hball : ∀ m : ℕ, (μHE[n] : Measure (Ambient n ℓ)) (A '' (S ∩ ball 0 m)) = 0 := by
        intro m
        apply zero_of _ (volume (ball (0 : EuclideanSpace ℝ (Fin n)) m)) measure_ball_lt_top.ne
        intro η hη
        obtain ⟨δ, -, hB⟩ := B3 A hA η hη
        calc (μHE[n] : Measure (Ambient n ℓ)) (A '' (S ∩ ball 0 m))
            ≤ η * volume (S ∩ ball (0 : EuclideanSpace ℝ (Fin n)) m) :=
              hB A _ fun x _ y _ => by rw [map_sub, sub_self, norm_zero]; positivity
          _ ≤ η * volume (ball (0 : EuclideanSpace ℝ (Fin n)) m) :=
              mul_le_mul' le_rfl (measure_mono inter_subset_right)
      have hU : A '' S = ⋃ m : ℕ, A '' (S ∩ ball 0 m) := by
        rw [← image_iUnion, ← inter_iUnion, iUnion_ball_nat, inter_univ]
      rw [hU]
      exact measure_iUnion_null hball
  /- From here on we work with `F`. `D` is its (Borel) differentiability set, of full measure by
  Rademacher's theorem, and `J = Jl ∘ DF` is Borel and nonnegative. -/
  have hFc : Continuous F := hF.continuous
  have hFm : Measurable F := hFc.measurable
  obtain ⟨D, hD⟩ : ∃ D : Set (EuclideanSpace ℝ (Fin n)), D = {x | DifferentiableAt ℝ F x} :=
    ⟨_, rfl⟩
  have hDm : MeasurableSet D := by
    rw [hD]
    exact measurableSet_of_differentiableAt ℝ F
  have hDc : volume Dᶜ = 0 := by
    have h := hF.ae_differentiableAt (μ := volume)
    rw [ae_iff] at h
    rw [hD]
    exact h
  have hderiv : ∀ s ⊆ D, ∀ x ∈ s, HasFDerivWithinAt F (fderiv ℝ F x) s x := by
    intro s hs x hx
    have hxD : x ∈ D := hs hx
    rw [hD] at hxD
    exact hxD.hasFDerivAt.hasFDerivWithinAt
  obtain ⟨J, hJ⟩ : ∃ J : EuclideanSpace ℝ (Fin n) → ℝ, J = fun v => Jl (fderiv ℝ F v) := ⟨_, rfl⟩
  have hJv : ∀ v, J v = Jl (fderiv ℝ F v) := fun v => by rw [hJ]
  have hJm : Measurable J := by
    rw [hJ]
    exact hJl_cont.measurable.comp (measurable_fderiv ℝ F)
  have hJnn : ∀ v, 0 ≤ J v := fun v => by
    rw [hJv]
    exact hJl_nonneg _
  /- (Z) Sets where `J = 0` have `Hⁿ`-null images: partition into pieces where `F` is close to a
  non-injective `DF(y)` and apply `B3` on bounded parts. -/
  have hZ : ∀ s : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet s → s ⊆ D → (∀ x ∈ s, J x = 0) →
      (μHE[n] : Measure (Ambient n ℓ)) (F '' s) = 0 := by
    intro s hs hsD hs0
    have key : ∀ m : ℕ, (μHE[n] : Measure (Ambient n ℓ)) (F '' (s ∩ ball 0 m)) = 0 := by
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
        exists_partition_approximatesLinearOn_of_hasFDerivWithinAt F
          (s ∩ ball (0 : EuclideanSpace ℝ (Fin n)) m) (fderiv ℝ F)
          (hderiv _ (inter_subset_left.trans hsD)) r rpos
      rcases (s ∩ ball (0 : EuclideanSpace ℝ (Fin n)) m).eq_empty_or_nonempty with he | hne
      · rw [he, image_empty, measure_empty]
        exact zero_le
      have hAni : ∀ k, ¬ Function.Injective (A k) := by
        intro k hk
        obtain ⟨y, hy, hAk⟩ := hAy hne k
        have h1 := LA3 _ hk
        rw [hAk, ← hJv, hs0 y hy.1] at h1
        exact lt_irrefl _ h1
      have hpiece : ∀ k, (μHE[n] : Measure (Ambient n ℓ)) (F '' (s ∩ ball 0 m ∩ t k)) ≤
          η * volume (s ∩ ball (0 : EuclideanSpace ℝ (Fin n)) m ∩ t k) := by
        intro k
        apply (B3 (A k) (hAni k) η hη).choose_spec.2 F
        have := happ k
        simp only [r, hAni k, dite_false] at this
        exact this
      calc (μHE[n] : Measure (Ambient n ℓ)) (F '' (s ∩ ball 0 m))
          ≤ μHE[n] (⋃ k, F '' (s ∩ ball 0 m ∩ t k)) := by
            apply measure_mono
            rw [← image_iUnion, ← inter_iUnion]
            exact image_mono (subset_inter subset_rfl hcov)
        _ ≤ ∑' k, μHE[n] (F '' (s ∩ ball 0 m ∩ t k)) := measure_iUnion_le _
        _ ≤ ∑' k, (η : ℝ≥0∞) * volume (s ∩ ball (0 : EuclideanSpace ℝ (Fin n)) m ∩ t k) :=
            ENNReal.tsum_le_tsum hpiece
        _ = η * volume (⋃ k, s ∩ ball (0 : EuclideanSpace ℝ (Fin n)) m ∩ t k) := by
            rw [ENNReal.tsum_mul_left, measure_iUnion]
            · exact htd.mono fun i j h => h.mono inter_subset_right inter_subset_right
            · exact fun k => hs'm.inter (htm k)
        _ ≤ η * volume (ball (0 : EuclideanSpace ℝ (Fin n)) m) :=
            mul_le_mul' le_rfl
              (measure_mono (iUnion_subset fun k => inter_subset_left.trans inter_subset_right))
    have hU : F '' s = ⋃ m : ℕ, F '' (s ∩ ball 0 m) := by
      rw [← image_iUnion, ← inter_iUnion, iUnion_ball_nat, inter_univ]
    rw [hU]
    exact measure_iUnion_null key
  /- (Pos) On sets where `J > 0` and `F` is injective, `Hⁿ(F(s)) = ∫_s J`: for `c > 1` split `s`
  into the level sets `c^k ≤ J < c^{k+1}` (`k ∈ ℤ`), partition each into pieces where `F` is close
  to an injective `DF(y)`, compare both sides on each piece with `B12` up to `c²`, and sum (the
  images of the pieces are disjoint and Borel by Lusin–Souslin). Then let `c → 1`. -/
  have hPos : ∀ s : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet s → s ⊆ D → Set.InjOn F s →
      (∀ x ∈ s, 0 < J x) →
      (μHE[n] : Measure (Ambient n ℓ)) (F '' s) = ∫⁻ x in s, ENNReal.ofReal (J x) := by
    intro s hs hsD hinjs hspos
    have himgd : ∀ a b : Set (EuclideanSpace ℝ (Fin n)), a ⊆ s → b ⊆ s → Disjoint a b →
        Disjoint (F '' a) (F '' b) := by
      intro a b ha hb hab
      rw [Set.disjoint_left]
      rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
      have hyx : y = x := hinjs (hb hy) (ha hx) hxy
      exact Set.disjoint_left.mp hab hx (hyx ▸ hy)
    have key : ∀ c : ℝ, 1 < c →
        (μHE[n] : Measure (Ambient n ℓ)) (F '' s) ≤
          ENNReal.ofReal c * (ENNReal.ofReal c * ∫⁻ x in s, ENNReal.ofReal (J x)) ∧
        ∫⁻ x in s, ENNReal.ofReal (J x) ≤
          ENNReal.ofReal c * (ENNReal.ofReal c * (μHE[n] : Measure (Ambient n ℓ)) (F '' s)) := by
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
          (∀ j, ApproximatesLinearOn F (A j) (L k ∩ t j) (r (A j))) ∧
          ((L k).Nonempty → ∀ j, ∃ y ∈ L k, A j = fderiv ℝ F y) := fun k =>
        exists_partition_approximatesLinearOn_of_hasFDerivWithinAt F (L k) (fderiv ℝ F)
          (hderiv _ ((hLs k).trans hsD)) r rpos
      choose t A htd htm hcov happ hAy using hpart
      have hPm : ∀ k j, MeasurableSet (L k ∩ t k j) := fun k j => (hLm k).inter (htm k j)
      have hPs : ∀ k j, L k ∩ t k j ⊆ s := fun k j => inter_subset_left.trans (hLs k)
      have hPd : ∀ k, Pairwise (Function.onFun Disjoint fun j => L k ∩ t k j) := fun k j j' h =>
        (htd k h).mono inter_subset_right inter_subset_right
      have hLP : ∀ k, L k = ⋃ j, L k ∩ t k j := fun k => by
        rw [← inter_iUnion]
        exact (inter_eq_left.mpr (hcov k)).symm
      have hpiece : ∀ k j,
          (μHE[n] : Measure (Ambient n ℓ)) (F '' (L k ∩ t k j)) ≤
            ENNReal.ofReal c * (ENNReal.ofReal c * ∫⁻ x in L k ∩ t k j, ENNReal.ofReal (J x)) ∧
          ∫⁻ x in L k ∩ t k j, ENNReal.ofReal (J x) ≤
            ENNReal.ofReal c * (ENNReal.ofReal c *
              (μHE[n] : Measure (Ambient n ℓ)) (F '' (L k ∩ t k j))) := by
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
            ApproximatesLinearOn F (A k j) (L k ∩ t k j) (B12 (A k j) hinjA c hc).choose := by
          have := happ k j
          simp only [r, hinjA, dite_true] at this
          exact this
        have hB := (B12 (A k j) hinjA c hc).choose_spec.2 F (L k ∩ t k j) happ'
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
        · calc (μHE[n] : Measure (Ambient n ℓ)) (F '' (L k ∩ t k j))
              ≤ ENNReal.ofReal c * (ENNReal.ofReal (Jl (A k j)) * volume (L k ∩ t k j)) := hB.1
            _ ≤ ENNReal.ofReal c * (ENNReal.ofReal c * ∫⁻ x in L k ∩ t k j, ENNReal.ofReal (J x)) :=
              mul_le_mul' le_rfl hcmp1
        · calc ∫⁻ x in L k ∩ t k j, ENNReal.ofReal (J x)
              ≤ ENNReal.ofReal c * (ENNReal.ofReal (Jl (A k j)) * volume (L k ∩ t k j)) := hcmp2
            _ ≤ ENNReal.ofReal c * (ENNReal.ofReal c *
                (μHE[n] : Measure (Ambient n ℓ)) (F '' (L k ∩ t k j))) :=
              mul_le_mul' le_rfl (hB.2 (hinjs.mono (hPs k j)))
      have hFL : ∀ k, (μHE[n] : Measure (Ambient n ℓ)) (F '' L k) =
          ∑' j, μHE[n] (F '' (L k ∩ t k j)) := by
        intro k
        conv_lhs => rw [hLP k, image_iUnion]
        apply measure_iUnion
        · intro j j' hjj'
          exact himgd _ _ (hPs k j) (hPs k j') (hPd k hjj')
        · exact fun j => (hPm k j).image_of_continuousOn_injOn hFc.continuousOn
            (hinjs.mono (hPs k j))
      have hFs : (μHE[n] : Measure (Ambient n ℓ)) (F '' s) = ∑' k, μHE[n] (F '' L k) := by
        conv_lhs => rw [hLcov, image_iUnion]
        apply measure_iUnion
        · intro k k' hkk'
          exact himgd _ _ (hLs k) (hLs k') (hLd hkk')
        · exact fun k => (hLm k).image_of_continuousOn_injOn hFc.continuousOn (hinjs.mono (hLs k))
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
  /- Area formula on Borel sets of injectivity: `Hⁿ(F(s)) = ∫_s J`. Split `s` into the part
  outside `D` (null, with null image since `F` is Lipschitz), the part where `J = 0` (null image
  by `hZ`) and the part where `J > 0` (`hPos`). -/
  have hMI : ∀ s : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet s → Set.InjOn F s →
      (μHE[n] : Measure (Ambient n ℓ)) (F '' s) = ∫⁻ x in s, ENNReal.ofReal (J x) := by
    intro s hs hinjs
    have hsDnull : volume (s \ D) = 0 := measure_mono_null (fun x hx => hx.2) hDc
    have hnull : (μHE[n] : Measure (Ambient n ℓ)) (F '' (s \ D)) = 0 := by
      have h := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
        (hF.lipschitzOnWith (s := s \ D))
      rw [hvol, hsDnull, mul_zero] at h
      exact le_antisymm h zero_le
    have hs₀m : MeasurableSet (s ∩ D ∩ J ⁻¹' {0}) :=
      (hs.inter hDm).inter (hJm (measurableSet_singleton 0))
    have hs₁m : MeasurableSet (s ∩ D ∩ J ⁻¹' Ioi 0) := (hs.inter hDm).inter (hJm measurableSet_Ioi)
    have hZ0 : (μHE[n] : Measure (Ambient n ℓ)) (F '' (s ∩ D ∩ J ⁻¹' {0})) = 0 :=
      hZ _ hs₀m (fun x hx => hx.1.2) (fun x hx => hx.2)
    have hP1 := hPos _ hs₁m (fun x hx => hx.1.2) (hinjs.mono fun x hx => hx.1.1) (fun x hx => hx.2)
    have hmeas_eq : (μHE[n] : Measure (Ambient n ℓ)) (F '' s) =
        μHE[n] (F '' (s ∩ D ∩ J ⁻¹' Ioi 0)) := by
      apply le_antisymm _ (measure_mono (image_mono fun x hx => hx.1.1))
      have hsub : F '' s ⊆ F '' (s ∩ D ∩ J ⁻¹' Ioi 0) ∪
          (F '' (s ∩ D ∩ J ⁻¹' {0}) ∪ F '' (s \ D)) := by
        rintro _ ⟨x, hx, rfl⟩
        by_cases hxD : x ∈ D
        · rcases (hJnn x).eq_or_lt with h0 | hpos
          · exact Or.inr (Or.inl ⟨x, ⟨⟨hx, hxD⟩, h0.symm⟩, rfl⟩)
          · exact Or.inl ⟨x, ⟨⟨hx, hxD⟩, hpos⟩, rfl⟩
        · exact Or.inr (Or.inr ⟨x, ⟨hx, hxD⟩, rfl⟩)
      calc (μHE[n] : Measure (Ambient n ℓ)) (F '' s)
          ≤ μHE[n] (F '' (s ∩ D ∩ J ⁻¹' Ioi 0) ∪
              (F '' (s ∩ D ∩ J ⁻¹' {0}) ∪ F '' (s \ D))) := measure_mono hsub
        _ ≤ μHE[n] (F '' (s ∩ D ∩ J ⁻¹' Ioi 0)) +
              μHE[n] (F '' (s ∩ D ∩ J ⁻¹' {0}) ∪ F '' (s \ D)) := measure_union_le _ _
        _ = μHE[n] (F '' (s ∩ D ∩ J ⁻¹' Ioi 0)) := by
            rw [measure_union_null hZ0 hnull, add_zero]
    have hint_eq : ∫⁻ x in s, ENNReal.ofReal (J x) =
        ∫⁻ x in s ∩ D ∩ J ⁻¹' Ioi 0, ENNReal.ofReal (J x) := by
      have h0 : ∫⁻ x in s \ (s ∩ D ∩ J ⁻¹' Ioi 0), ENNReal.ofReal (J x) = 0 := by
        apply le_antisymm _ zero_le
        calc ∫⁻ x in s \ (s ∩ D ∩ J ⁻¹' Ioi 0), ENNReal.ofReal (J x)
            ≤ ∫⁻ x in (s \ D) ∪ (s ∩ D ∩ J ⁻¹' {0}), ENNReal.ofReal (J x) := by
              apply lintegral_mono_set
              rintro x ⟨hx, hx'⟩
              by_cases hxD : x ∈ D
              · refine Or.inr ⟨⟨hx, hxD⟩, ?_⟩
                rcases (hJnn x).eq_or_lt with h0 | hpos
                · exact h0.symm
                · exact absurd ⟨⟨hx, hxD⟩, hpos⟩ hx'
              · exact Or.inl ⟨hx, hxD⟩
          _ ≤ (∫⁻ x in s \ D, ENNReal.ofReal (J x)) +
                ∫⁻ x in s ∩ D ∩ J ⁻¹' {0}, ENNReal.ofReal (J x) := lintegral_union_le _ _ _
          _ = 0 := by
              rw [setLIntegral_measure_zero _ _ hsDnull, zero_add]
              rw [setLIntegral_congr_fun hs₀m (g := fun _ => 0) fun x hx => by
                rw [show J x = 0 from hx.2, ENNReal.ofReal_zero]]
              exact lintegral_zero
      have hsub : s = (s ∩ D ∩ J ⁻¹' Ioi 0) ∪ (s \ (s ∩ D ∩ J ⁻¹' Ioi 0)) :=
        (union_sdiff_cancel fun x hx => hx.1.1).symm
      conv_lhs => rw [hsub]
      rw [lintegral_union (hs.diff hs₁m) disjoint_sdiff_right, h0, add_zero]
    rw [hmeas_eq, hint_eq]
    exact hP1
  refine ⟨J, ?_, ?_, ?_⟩
  · -- `J = Jl ∘ DF` is continuous on `C` since `DF` is.
    rw [hJ]
    exact hJl_cont.comp_continuousOn hcont
  · -- nonnegativity and the linear area factor
    intro v _
    refine ⟨hJnn v, fun S => ?_⟩
    rw [hJv]
    exact hlin _ S
  · -- `Hⁿ ⌞ F(C) = F_#((J · Lⁿ) ⌞ C)`, then change variables.
    intro g hg
    have hmeasure : (μHE[n] : Measure (Ambient n ℓ)).restrict (F '' C) =
        Measure.map F ((volume.restrict C).withDensity fun v => ENNReal.ofReal (J v)) := by
      ext T hT
      rw [Measure.restrict_apply hT, Measure.map_apply hFm hT, withDensity_apply _ (hFm hT),
        Measure.restrict_restrict (hFm hT)]
      have hset : T ∩ F '' C = F '' (F ⁻¹' T ∩ C) := by
        ext y
        constructor
        · rintro ⟨hyT, v, hvC, rfl⟩
          exact ⟨v, ⟨hyT, hvC⟩, rfl⟩
        · rintro ⟨v, ⟨hvT, hvC⟩, rfl⟩
          exact ⟨hvT, v, hvC, rfl⟩
      rw [hset]
      exact hMI _ ((hFm hT).inter hC) (hinj.mono inter_subset_right)
    rw [hmeasure, integral_map hFm.aemeasurable hg.aestronglyMeasurable,
      integral_withDensity_eq_integral_toReal_smul (f := fun v => ENNReal.ofReal (J v))
        (ENNReal.measurable_ofReal.comp hJm) (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only [ENNReal.toReal_ofReal (hJnn v), smul_eq_mul]
/-- **Integral over the range of a linear map.** If a continuous linear `A : ℝⁿ → ℝ^{n+ℓ}` and
`j ≥ 0` satisfy `Hⁿ(A(S)) = j Lⁿ(S)` for every `S ⊆ ℝⁿ`, then `Hⁿ ⌞ range A = A_#(j Lⁿ)`, so
`∫_{range A} f dHⁿ = j ∫ f(Au) du` for every `f ∈ C_c(ℝ^{n+ℓ})`. -/
theorem Submission.ts_pdb_linear_range_integral : ∀ (n ℓ : ℕ) (A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ) (j : ℝ), 0 ≤ j → (∀ S : Set (EuclideanSpace ℝ (Fin n)), (μHE[n] : Measure (Ambient n ℓ)) (A '' S) = ENNReal.ofReal j * volume S) → ∀ f : C_c(Ambient n ℓ, ℝ), ∫ y in (LinearMap.range A.toLinearMap : Set (Ambient n ℓ)), f y ∂μHE[n] = j * ∫ u, f (A u) := by
  intro n ℓ A j hj hA f
  -- `Hⁿ ⌞ range A = A_#(j Lⁿ)`: for Borel `T`, `T ∩ range A = A(A⁻¹T)`; apply `hA` to `A⁻¹T`.
  have hmeas : (μHE[n] : Measure (Ambient n ℓ)).restrict (LinearMap.range A.toLinearMap) =
      (ENNReal.ofReal j • (volume : Measure (EuclideanSpace ℝ (Fin n)))).map A := by
    ext T hT
    rw [Measure.restrict_apply hT, Measure.map_apply A.measurable hT, Measure.smul_apply,
      smul_eq_mul, ← hA, LinearMap.coe_range, ContinuousLinearMap.coe_coe,
      Set.image_preimage_eq_inter_range]
  -- Change variables along `A`, then pull out the scalar `(ofReal j).toReal = j`.
  rw [hmeas, integral_map A.measurable.aemeasurable (map_continuous f).aestronglyMeasurable,
    integral_smul_measure, ENNReal.toReal_ofReal hj, smul_eq_mul]
/-- **Rescaled complement at a Lebesgue density point** (a step in the proof of `ApproxTangentAE`,
Simon Ch. 3, 1.9 and Ch. 4, 1.3). If `C ⊆ ℝⁿ` is Borel, `R > 0` and
`Lⁿ(C ∩ B_r(w)) / Lⁿ(B_r(w)) → 1` as `r ↓ 0`, then
`Lⁿ{u ∈ B_R(0) : w + tu ∉ C} → 0` as `t ↓ 0`: the set is the preimage of `B_{tR}(w) \ C` under
`u ↦ w + tu`, so its measure is
`t⁻ⁿ Lⁿ(B_{tR}(w) \ C) = Rⁿ Lⁿ(B_1(0)) (1 - Lⁿ(C ∩ B_{tR}(w)) / Lⁿ(B_{tR}(w))) → 0`. -/
theorem Submission.ts_pdb_density_complement_vanish : ∀ (n : ℕ) (C : Set (EuclideanSpace ℝ (Fin n))) (w : EuclideanSpace ℝ (Fin n)) (R : ℝ), MeasurableSet C → 0 < R → Tendsto (fun r : ℝ ↦ volume (C ∩ closedBall w r) / volume (closedBall w r)) (𝓝[>] 0) (𝓝 1) → Tendsto (fun t : ℝ ↦ volume {u : EuclideanSpace ℝ (Fin n) | u ∈ closedBall 0 R ∧ w + t • u ∉ C}) (𝓝[>] 0) (𝓝 0) := by
  intro n C w R hC hR hq
  -- `V = Lⁿ(B_1(0)) < ∞`.
  set V : ℝ≥0∞ := volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1)
  have hVfin : V ≠ ⊤ := measure_ball_lt_top.ne
  -- Step 1: the complementary ratio `1 - q(r)` tends to `0`.
  have h1 : Tendsto (fun r : ℝ ↦ 1 - volume (C ∩ closedBall w r) / volume (closedBall w r))
      (𝓝[>] 0) (𝓝 0) := by
    have := ENNReal.Tendsto.sub tendsto_const_nhds hq (Or.inl ENNReal.one_ne_top)
    simpa using this
  -- Step 5 (first half): `t ↦ t * R` maps `t ↓ 0` to `r ↓ 0`.
  have hmul : Tendsto (fun t : ℝ ↦ t * R) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h : Tendsto (fun t : ℝ ↦ t * R) (𝓝 0) (𝓝 (0 * R)) :=
        (continuous_id.mul continuous_const).tendsto 0
      rw [zero_mul] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      exact mul_pos ht hR
  have h2 : Tendsto (fun t : ℝ ↦ ENNReal.ofReal (R ^ n) * V *
      (1 - volume (C ∩ closedBall w (t * R)) / volume (closedBall w (t * R)))) (𝓝[>] 0) (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (h1.comp hmul)
      (Or.inr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVfin) :
        (0 : ℝ≥0∞) ≠ 0 ∨ ENNReal.ofReal (R ^ n) * V ≠ ⊤)
    simpa using this
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  -- Step 2: `B = B_{tR}(w)` has `0 < Lⁿ(B) = (tR)ⁿ Lⁿ(B_1(0)) < ∞`.
  have hr : 0 < t * R := mul_pos ht hR
  set B := closedBall w (t * R) with hB
  have hBpos : volume B ≠ 0 := (measure_closedBall_pos volume w hr).ne'
  have hBfin : volume B ≠ ⊤ := measure_closedBall_lt_top.ne
  have hBval : volume B = ENNReal.ofReal ((t * R) ^ n) * V := by
    rw [hB, Measure.addHaar_closedBall volume w hr.le, finrank_euclideanSpace_fin]
  -- Step 3: `Lⁿ(B \ C) = Lⁿ(B) (1 - q(tR))`.
  have hdiff : volume (B \ C) = volume B * (1 - volume (C ∩ B) / volume B) := by
    have hBC : B \ C = B \ (C ∩ B) := by
      ext x; simp only [Set.mem_sdiff, mem_inter_iff]; tauto
    rw [hBC, measure_sdiff inter_subset_right (hC.inter measurableSet_closedBall).nullMeasurableSet
      (ne_top_of_le_ne_top hBfin (measure_mono inter_subset_right)),
      ENNReal.mul_sub (fun _ _ ↦ hBfin), mul_one, ENNReal.mul_div_cancel hBpos hBfin]
  -- Step 4: the set is the preimage of `B \ C` under `u ↦ w + t • u`, so its measure is
  -- `t⁻ⁿ Lⁿ(B \ C) = Rⁿ Lⁿ(B_1(0)) (1 - q(tR))`.
  have hset : {u : EuclideanSpace ℝ (Fin n) | u ∈ closedBall 0 R ∧ w + t • u ∉ C} =
      (fun u ↦ t • u) ⁻¹' ((fun x ↦ w + x) ⁻¹' (B \ C)) := by
    ext u
    simp only [mem_ofPred_eq, mem_preimage, Set.mem_sdiff, hB, mem_closedBall, sub_zero,
      dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    constructor
    · rintro ⟨hu, hw⟩; exact ⟨mul_le_mul_of_nonneg_left hu ht.le, hw⟩
    · rintro ⟨hu, hw⟩; exact ⟨le_of_mul_le_mul_left hu ht, hw⟩
  rw [hset, Measure.addHaar_preimage_smul volume ht.ne', measure_preimage_add, hdiff, hBval,
    finrank_euclideanSpace_fin, ← mul_assoc, ← mul_assoc]
  congr 2
  rw [← ENNReal.ofReal_mul (abs_nonneg _), abs_of_pos (by positivity), mul_pow,
    ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero n ht.ne'), one_mul]

/-- **Blow-up of a weighted Lebesgue integral at a density point** (a step in the proof of
`ApproxTangentAE`, Simon Ch. 3, 1.9 and Ch. 4, 1.3). Let `C ⊆ ℝⁿ` be compact, `F` continuous with
injective derivative `A` at `w ∈ C`, `J` continuous on `C`, `c|v - w| ≤ |F(v) - F(w)|` on `C` and
`Lⁿ(C ∩ B_r(w)) / Lⁿ(B_r(w)) → 1` as `r ↓ 0`. Then for `f ∈ C_c`,
`t⁻ⁿ ∫_C J(v) f(t⁻¹(F(v) - F(w))) dv → J(w) ∫ f(Au) du` as `t ↓ 0`: after `v = w + tu` both
integrands vanish off `B_{R'}(0)`, they are uniformly close where `w + tu ∈ C`, and the rest of
`B_{R'}(0)` has measure `→ 0` by `Submission.ts_pdb_density_complement_vanish`. -/
theorem Submission.ts_pdb_density_point_rescaled_limit : ∀ (n ℓ : ℕ) (C : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → Ambient n ℓ) (J : EuclideanSpace ℝ (Fin n) → ℝ) (A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ) (w : EuclideanSpace ℝ (Fin n)) (c : ℝ), IsCompact C → Continuous F → ContinuousOn J C → w ∈ C → HasFDerivAt F A w → Function.Injective A → 0 < c → (∀ v ∈ C, c * ‖v - w‖ ≤ ‖F v - F w‖) → Tendsto (fun r : ℝ ↦ volume (C ∩ closedBall w r) / volume (closedBall w r)) (𝓝[>] 0) (𝓝 1) → ∀ f : C_c(Ambient n ℓ, ℝ), Tendsto (fun t : ℝ ↦ (t ^ n)⁻¹ * ∫ v in C, J v * f (t⁻¹ • (F v - F w))) (𝓝[>] 0) (𝓝 (J w * ∫ u, f (A u))) := by
  intro n ℓ C F J A w c hC hF hJ hw hA hAinj hc hlow hdens f
  -- Step 1: constants. `C` is closed, hence Borel; `f = 0` off `B_R(0)` and `|f| ≤ Mf`;
  -- `‖u‖ ≤ K ‖A u‖`; `R' = R (c⁻¹ + K)`.
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  obtain ⟨R₀, hR₀⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
  set R : ℝ := max R₀ 1 with hRdef
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hfR : ∀ z, R < ‖z‖ → f z = 0 := by
    intro z hz
    refine image_eq_zero_of_notMem_tsupport fun hz' ↦ ?_
    have h := hR₀ hz'
    rw [mem_closedBall, dist_zero_right] at h
    linarith [le_max_left R₀ 1]
  obtain ⟨Mf, hMf⟩ := (map_continuous f).bounded_above_of_compact_support f.hasCompactSupport
  have hMf0 : 0 ≤ Mf := (norm_nonneg _).trans (hMf 0)
  obtain ⟨K, -, hK⟩ := (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] Ambient n ℓ).exists_antilipschitzWith
    (LinearMap.ker_eq_bot.2 hAinj)
  have hKu : ∀ u, ‖u‖ ≤ K * ‖A u‖ := fun u ↦ by simpa using hK.le_mul_dist u 0
  set R' : ℝ := R * (c⁻¹ + K) with hR'eq
  have hR' : 0 < R' := by positivity
  have hcR' : R ≤ c * R' := by
    have h : c * R' = R + c * R * K := by rw [hR'eq]; field_simp
    nlinarith [mul_nonneg (mul_nonneg hc.le hR.le) (NNReal.coe_nonneg K)]
  have hKR' : K * R ≤ R' := by
    have h : R' = R * c⁻¹ + K * R := by rw [hR'eq]; ring
    nlinarith [mul_nonneg hR.le (inv_pos.2 hc).le]
  -- Step 2: notation. `G t u = 1_C(w + tu) J(w + tu) f(t⁻¹(F(w + tu) - F(w)))`,
  -- `H u = J(w) f(Au)`.
  set φ : ℝ → EuclideanSpace ℝ (Fin n) → ℝ := fun t v ↦ J v * f (t⁻¹ • (F v - F w)) with hφ
  set G : ℝ → EuclideanSpace ℝ (Fin n) → ℝ := fun t u ↦ C.indicator (φ t) (w + t • u) with hG
  set H : EuclideanSpace ℝ (Fin n) → ℝ := fun u ↦ J w * f (A u) with hH
  -- Step 3: rescaling `v = w + tu`.
  have hresc : ∀ t : ℝ, 0 < t →
      (t ^ n)⁻¹ * ∫ v in C, J v * f (t⁻¹ • (F v - F w)) = ∫ u, G t u := by
    intro t ht
    have h := Measure.integral_comp_smul (volume : Measure (EuclideanSpace ℝ (Fin n)))
      (fun x ↦ C.indicator (φ t) (w + x)) t
    rw [integral_add_left_eq_self (C.indicator (φ t)) w, integral_indicator hCm,
      finrank_euclideanSpace_fin, abs_of_pos (by positivity), smul_eq_mul] at h
    exact h.symm
  -- Step 4: integrability of `G t` (`t ≠ 0`).
  have hφint : ∀ t, IntegrableOn (φ t) C := fun t ↦ ContinuousOn.integrableOn_compact hC
    (hJ.mul ((map_continuous f).comp ((hF.sub continuous_const).const_smul t⁻¹)).continuousOn)
  have hGint : ∀ t, t ≠ 0 → Integrable (G t) := fun t ht ↦
    (((integrable_indicator_iff hCm).2 (hφint t)).comp_add_left w).comp_smul ht
  -- Step 5(b): `H` vanishes off `B_{R'}(0)`, hence is integrable.
  have hH0 : ∀ u, R' < ‖u‖ → H u = 0 := by
    intro u hu
    have hAu : R < ‖A u‖ := by
      by_contra h
      push Not at h
      have h1 : (K : ℝ) * ‖A u‖ ≤ K * R := mul_le_mul_of_nonneg_left h K.2
      linarith [hKu u]
    simp only [hH, hfR _ hAu, mul_zero]
  have hHint : Integrable H := by
    have hHc : Continuous H := continuous_const.mul ((map_continuous f).comp A.continuous)
    refine hHc.integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) R') ?_)
    intro u hu
    exact hH0 u (by simpa [mem_closedBall, dist_zero_right, not_le] using hu)
  -- Step 5(a): `G t` vanishes off `B_{R'}(0)` (`t > 0`).
  have hG0 : ∀ t, 0 < t → ∀ u, R' < ‖u‖ → G t u = 0 := by
    intro t ht u hu
    by_cases hmem : w + t • u ∈ C
    · have h1 := hlow _ hmem
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht] at h1
      have hQ : R < ‖t⁻¹ • (F (w + t • u) - F w)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht]
        have h2 : c * ‖u‖ ≤ t⁻¹ * ‖F (w + t • u) - F w‖ := by
          rw [le_inv_mul_iff₀ ht]
          linarith
        have h3 : c * R' < c * ‖u‖ := mul_lt_mul_of_pos_left hu hc
        linarith
      simp only [hG, indicator_of_mem hmem, hφ, hfR _ hQ, mul_zero]
    · simp only [hG, indicator_of_notMem hmem]
  -- Step 6: uniform estimate on the good set `{u ∈ B_{R'}(0) : w + tu ∈ C}`.
  have hunif : ∀ ε > 0, ∃ t₀ > 0, ∀ t, 0 < t → t < t₀ → ∀ u, ‖u‖ ≤ R' → w + t • u ∈ C →
      |G t u - H u| ≤ ε := by
    intro ε hε
    set ε₁ := ε / (2 * (|J w| + 1)) with hε₁def
    set ε₂ := ε / (2 * (Mf + 1)) with hε₂def
    have hε₁ : 0 < ε₁ := by positivity
    have hε₂ : 0 < ε₂ := by positivity
    obtain ⟨δf, hδf, hfδ⟩ := Metric.uniformContinuous_iff.1
      (CompactlySupportedContinuousMapClass.uniformContinuous f) ε₁ hε₁
    obtain ⟨δJ, hδJ, hJδ⟩ := Metric.continuousOn_iff.1 hJ w hw ε₂ hε₂
    set η := δf / (2 * (R' + 1)) with hηdef
    have hη : 0 < η := by positivity
    obtain ⟨δd, hδd, hdδ⟩ := Metric.eventually_nhds_iff.1
      (Asymptotics.isLittleO_iff.1 (hasFDerivAt_iff_isLittleO_nhds_zero.1 hA) hη)
    refine ⟨min δJ δd / (R' + 1), by positivity, ?_⟩
    intro t ht ht₀ u hu hmem
    have htu : ‖t • u‖ < min δJ δd := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      calc t * ‖u‖ ≤ t * R' := mul_le_mul_of_nonneg_left hu ht.le
        _ < t * (R' + 1) := by nlinarith
        _ < min δJ δd / (R' + 1) * (R' + 1) := mul_lt_mul_of_pos_right ht₀ (by positivity)
        _ = min δJ δd := by field_simp
    have hJe : |J (w + t • u) - J w| < ε₂ := by
      have h := hJδ (w + t • u) hmem
        (by rw [dist_eq_norm, add_sub_cancel_left]; exact htu.trans_le (min_le_left _ _))
      rwa [Real.dist_eq] at h
    have hde : ‖F (w + t • u) - F w - A (t • u)‖ ≤ η * ‖t • u‖ :=
      hdδ (by rw [dist_zero_right]; exact htu.trans_le (min_le_right _ _))
    have hQ : dist (t⁻¹ • (F (w + t • u) - F w)) (A u) < δf := by
      have h : t⁻¹ • (F (w + t • u) - F w) - A u =
          t⁻¹ • (F (w + t • u) - F w - A (t • u)) := by
        rw [map_smul, smul_sub t⁻¹ (F (w + t • u) - F w) (t • A u), inv_smul_smul₀ ht.ne']
      rw [dist_eq_norm, h, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht]
      calc t⁻¹ * ‖F (w + t • u) - F w - A (t • u)‖ ≤ t⁻¹ * (η * ‖t • u‖) :=
            mul_le_mul_of_nonneg_left hde (by positivity)
        _ = η * ‖u‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]; field_simp
        _ ≤ η * R' := mul_le_mul_of_nonneg_left hu hη.le
        _ < δf := by
          rw [hηdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith
    have hfe : |f (t⁻¹ • (F (w + t • u) - F w)) - f (A u)| < ε₁ := by
      have h := hfδ hQ
      rwa [Real.dist_eq] at h
    have hfQ : |f (t⁻¹ • (F (w + t • u) - F w))| ≤ Mf := by
      simpa [Real.norm_eq_abs] using hMf (t⁻¹ • (F (w + t • u) - F w))
    simp only [hG, hH, indicator_of_mem hmem, hφ]
    calc |J (w + t • u) * f (t⁻¹ • (F (w + t • u) - F w)) - J w * f (A u)|
        = |(J (w + t • u) - J w) * f (t⁻¹ • (F (w + t • u) - F w)) +
            J w * (f (t⁻¹ • (F (w + t • u) - F w)) - f (A u))| := by ring_nf
      _ ≤ |J (w + t • u) - J w| * |f (t⁻¹ • (F (w + t • u) - F w))| +
            |J w| * |f (t⁻¹ • (F (w + t • u) - F w)) - f (A u)| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ ε₂ * Mf + |J w| * ε₁ := by gcongr
      _ ≤ ε / 2 + ε / 2 := by
          gcongr
          · rw [hε₂def, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) two_pos]
            nlinarith
          · rw [hε₁def, mul_div_assoc', div_le_div_iff₀ (by positivity) two_pos]
            nlinarith [abs_nonneg (J w)]
      _ = ε := by ring
  -- Step 7: pointwise bound `|G t - H| ≤ ε 1_B + M 1_{S t}` with `B = B_{R'}(0)`,
  -- `S t = {u ∈ B : w + tu ∉ C}` and `M = |J(w)| Mf`.
  set B : Set (EuclideanSpace ℝ (Fin n)) := closedBall 0 R' with hBdef
  set S : ℝ → Set (EuclideanSpace ℝ (Fin n)) :=
    fun t ↦ {u | u ∈ closedBall 0 R' ∧ w + t • u ∉ C}
  set M : ℝ := |J w| * Mf with hMdef
  have hM : 0 ≤ M := by positivity
  have hpt : ∀ ε > 0, ∃ t₀ > 0, ∀ t, 0 < t → t < t₀ → ∀ u,
      ‖G t u - H u‖ ≤ B.indicator (fun _ ↦ ε) u + (S t).indicator (fun _ ↦ M) u := by
    intro ε hε
    obtain ⟨t₀, ht₀, h⟩ := hunif ε hε
    refine ⟨t₀, ht₀, fun t ht htt₀ u ↦ ?_⟩
    rw [Real.norm_eq_abs]
    by_cases hu : ‖u‖ ≤ R'
    · have huB : u ∈ B := by rwa [hBdef, mem_closedBall, dist_zero_right]
      rw [indicator_of_mem huB]
      by_cases hmem : w + t • u ∈ C
      · have hS : u ∉ S t := fun h ↦ h.2 hmem
        rw [indicator_of_notMem hS, add_zero]
        exact h t ht htt₀ u hu hmem
      · have hS : u ∈ S t := ⟨huB, hmem⟩
        have hG' : G t u = 0 := by simp only [hG, indicator_of_notMem hmem]
        have hH' : |H u| ≤ M := by
          simp only [hH, hMdef, abs_mul]
          exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hMf (A u))
            (abs_nonneg _)
        rw [indicator_of_mem hS, hG', zero_sub, abs_neg]
        linarith
    · push Not at hu
      rw [hG0 t ht u hu, hH0 u hu, sub_zero, abs_zero]
      exact add_nonneg (indicator_nonneg (fun _ _ ↦ hε.le) _) (indicator_nonneg (fun _ _ ↦ hM) _)
  -- Step 8: integral bound `|∫ G t - ∫ H| ≤ ε Lⁿ(B) + M Lⁿ(S t)`.
  have hint : ∀ ε > 0, ∃ t₀ > 0, ∀ t, 0 < t → t < t₀ →
      ‖(∫ u, G t u) - ∫ u, H u‖ ≤ ε * volume.real B + M * volume.real (S t) := by
    intro ε hε
    obtain ⟨t₀, ht₀, h⟩ := hpt ε hε
    refine ⟨t₀, ht₀, fun t ht htt₀ ↦ ?_⟩
    have hBm : MeasurableSet B := measurableSet_closedBall
    have hBfin : volume B ≠ ⊤ := measure_closedBall_lt_top.ne
    have hSm : MeasurableSet (S t) := measurableSet_closedBall.inter
      (hCm.compl.preimage (measurable_const.add (measurable_const_smul t)))
    have hSfin : volume (S t) ≠ ⊤ := ne_top_of_le_ne_top hBfin (measure_mono fun u hu ↦ hu.1)
    have hb1 : Integrable (B.indicator fun _ ↦ ε) :=
      (integrable_indicator_iff hBm).2 (integrableOn_const hBfin)
    have hb2 : Integrable ((S t).indicator fun _ ↦ M) :=
      (integrable_indicator_iff hSm).2 (integrableOn_const hSfin)
    rw [← integral_sub (hGint t ht.ne') hHint]
    calc ‖∫ u, G t u - H u‖
        ≤ ∫ u, (B.indicator (fun _ ↦ ε) u + (S t).indicator (fun _ ↦ M) u) :=
          norm_integral_le_of_norm_le (hb1.add hb2) (Eventually.of_forall (h t ht htt₀))
      _ = ε * volume.real B + M * volume.real (S t) := by
          rw [integral_add hb1 hb2, integral_indicator_const _ hBm, integral_indicator_const _ hSm,
            smul_eq_mul, smul_eq_mul, mul_comm (volume.real B), mul_comm (volume.real (S t))]
  -- Step 9: `Lⁿ(S t) → 0` by `Submission.ts_pdb_density_complement_vanish`, so
  -- `∫ G t → ∫ H = J(w) ∫ f(Au) du`, and `∫ G t` is the rescaled integral for `t > 0`.
  have hS0 : Tendsto (fun t ↦ volume.real (S t)) (𝓝[>] 0) (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (Submission.ts_pdb_density_complement_vanish n C w R' hCm hR' hdens)
    rw [ENNReal.toReal_zero] at h
    exact h
  have hlim : Tendsto (fun t ↦ ∫ u, G t u) (𝓝[>] 0) (𝓝 (∫ u, H u)) := by
    rw [Metric.tendsto_nhds]
    intro δ hδ
    set VB := volume.real B
    have hVB : 0 ≤ VB := measureReal_nonneg
    set ε := δ / (2 * (VB + 1)) with hεdef
    have hε : 0 < ε := by positivity
    obtain ⟨t₀, ht₀, h⟩ := hint ε hε
    have hεVB : ε * VB < δ / 2 := by
      rw [hεdef, div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) two_pos]
      nlinarith
    have hMS : Tendsto (fun t ↦ M * volume.real (S t)) (𝓝[>] 0) (𝓝 0) := by
      simpa using hS0.const_mul M
    filter_upwards [hMS.eventually (gt_mem_nhds (half_pos hδ)), Ioo_mem_nhdsGT ht₀]
      with t h1t h2t
    rw [dist_eq_norm]
    calc ‖(∫ u, G t u) - ∫ u, H u‖ ≤ ε * VB + M * volume.real (S t) := h t h2t.1 h2t.2
      _ < δ / 2 + δ / 2 := by linarith
      _ = δ := by ring
  have hHval : ∫ u, H u = J w * ∫ u, f (A u) := integral_const_mul _ _
  rw [← hHval]
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  exact (hresc t ht).symm

theorem main_theorem : ApproxTangentAE ∧ FirstVariationFormula ∧ StationaryIffVariational ∧ StationaryMonotonicity ∧ StationaryDensity ∧ CanonicalRepresentative ∧ BoundedCurvatureMonotonicity ∧ LogarithmicMonotonicityError ∧ LpMonotonicity ∧ LpDensity ∧ LpSupportRepresentation ∧ PoincareInequality ∧ SobolevInequality ∧ SupportInBall ∧ ConvexHullProperty ∧ ClassicalTangent := by sorry

end

end GMT.Ch04
