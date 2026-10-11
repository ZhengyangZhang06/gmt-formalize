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

/-- Simon 2.1, 2.4 (pp. 87–88): the initial velocity `X = ∂φ_t/∂t|_{t=0}` of a family as in 2.1
with `K ⊆ U` is a test field, `X ∈ C¹_c(U; ℝ^{n+ℓ})`; in fact `tsupport X ⊆ K`. -/
theorem Submission.compactVariation_velocity_isTestField : ∀ (n ℓ : ℕ) (U : Set (Ambient n ℓ)) (φ : ℝ → Ambient n ℓ → Ambient n ℓ) (ε : ℝ) (K : Set (Ambient n ℓ)), IsCompactVariation φ ε K → K ⊆ U → IsTestField U (fun y ↦ deriv (fun t ↦ φ t y) 0) := by
  intro n ℓ U φ ε K hφ hKU
  -- `Φ(q) = φ q.1 q.2` is `C^∞` on the open set `S = (-ε, ε) × ℝ^{n+ℓ}`, and `(0, y) ∈ S`.
  have hS : IsOpen (Ioo (-ε) ε ×ˢ (univ : Set (Ambient n ℓ))) := isOpen_Ioo.prod isOpen_univ
  have hmem : ∀ y : Ambient n ℓ, ((0 : ℝ), y) ∈ Ioo (-ε) ε ×ˢ (univ : Set (Ambient n ℓ)) :=
    fun y ↦ ⟨⟨neg_lt_zero.mpr hφ.pos, hφ.pos⟩, mem_univ _⟩
  -- Chain rule along `t ↦ (t, y)`: `X(y) = DΦ(0, y)(1, 0)`.
  have hvel : ∀ y, deriv (fun t ↦ φ t y) 0 =
      fderiv ℝ (fun q : ℝ × Ambient n ℓ ↦ φ q.1 q.2) (0, y) (1, 0) := by
    intro y
    have hdiff : DifferentiableAt ℝ (fun q : ℝ × Ambient n ℓ ↦ φ q.1 q.2) (0, y) :=
      (hφ.smooth.contDiffAt (hS.mem_nhds (hmem y))).differentiableAt (by simp)
    have hg : HasDerivAt (fun t : ℝ ↦ (t, y)) ((1 : ℝ), (0 : Ambient n ℓ)) 0 :=
      (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) y)
    exact (hdiff.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hg).deriv
  -- `DΦ` is `C¹` on the open set `S`, so `y ↦ DΦ(0, y)(1, 0)` is `C¹`.
  have hcd : ContDiff ℝ 1 (fun y ↦ deriv (fun t ↦ φ t y) 0) := by
    have h1 : ContDiffOn ℝ 1 (fun q ↦ fderiv ℝ (fun q : ℝ × Ambient n ℓ ↦ φ q.1 q.2) q)
        (Ioo (-ε) ε ×ˢ univ) :=
      hφ.smooth.fderiv_of_isOpen hS (WithTop.coe_le_coe.mpr le_top)
    have h2 : ContDiff ℝ 1
        (fun y : Ambient n ℓ ↦ fderiv ℝ (fun q : ℝ × Ambient n ℓ ↦ φ q.1 q.2) (0, y)) := by
      rw [← contDiffOn_univ]
      exact h1.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun y _ ↦ hmem y)
    simp_rw [hvel]
    exact h2.clm_apply contDiff_const
  -- Off `K`, `t ↦ φ t y` is constant near `0`, so `X(y) = 0`.
  have hzero : ∀ y, y ∉ K → deriv (fun t ↦ φ t y) 0 = 0 := by
    intro y hy
    have : (fun t ↦ φ t y) =ᶠ[𝓝 0] fun _ ↦ y := by
      filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr hφ.pos) hφ.pos] with t ht
      exact hφ.fixed t ht y hy
    rw [this.deriv_eq]; simp
  -- `K` is compact, hence closed: `tsupport X ⊆ K ⊆ U` and `X` has compact support.
  have hsupp : tsupport (fun y ↦ deriv (fun t ↦ φ t y) 0) ⊆ K :=
    closure_minimal (fun y hy ↦ by_contra fun h ↦ hy (hzero y h)) hφ.compact.isClosed
  exact ⟨hcd, HasCompactSupport.intro hφ.compact hzero, hsupp.trans hKU⟩
/-- **Ch. 4, 2.1 and 2.4 (pp. 87–88), linear variations.** If `X` is `C^∞` with compact support,
then `φ_t(y) = y + tX(y)` is a family as in 2.1 with `K = spt X` and initial velocity
`∂φ_t/∂t|_{t=0} = X`, as used in the equivalence of 2.4. With `L ≥ sup |DX|` and
`ε = 1/(L + 1)`: for `|t| < ε`, `φ_t - id = tX` is `|t|L`-Lipschitz with `|t|L < 1`, so `φ_t` is a
homeomorphism, and `Dφ_t = I + t DX` is invertible (Neumann series), so `φ_t⁻¹` is smooth by the
inverse function theorem. -/
theorem Submission.exists_isCompactVariation_add_smul : ∀ (n ℓ : ℕ) (X : Ambient n ℓ → Ambient n ℓ), ContDiff ℝ ∞ X → HasCompactSupport X → ∃ ε : ℝ, IsCompactVariation (fun t y ↦ y + t • X y) ε (tsupport X) ∧ (fun y ↦ deriv (fun t : ℝ ↦ y + t • X y) 0) = X := by
  intro n ℓ X hX hXc
  have hX1 : ContDiff ℝ 1 X := hX.of_le (WithTop.coe_le_coe.mpr le_top)
  -- `DX` is continuous with compact support, so `‖DX‖ ≤ L` for some `L ≥ 0`, and `X` is
  -- `L`-Lipschitz.
  obtain ⟨C, hC⟩ := (hXc.fderiv ℝ).exists_bound_of_continuous (hX1.continuous_fderiv one_ne_zero)
  obtain ⟨L, hL0, hDX⟩ : ∃ L : ℝ, 0 ≤ L ∧ ∀ y, ‖fderiv ℝ X y‖ ≤ L :=
    ⟨max C 0, le_max_right _ _, fun y ↦ (hC y).trans (le_max_left _ _)⟩
  have hLip : ∀ x y, ‖X x - X y‖ ≤ L * ‖x - y‖ := fun x y ↦
    convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun z _ ↦ hX1.differentiable one_ne_zero z)
      (fun z _ ↦ hDX z) (mem_univ y) (mem_univ x)
  refine ⟨1 / (L + 1), ⟨by positivity, hXc.isCompact, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact (contDiff_snd.add (contDiff_fst.smul (hX.comp contDiff_snd))).contDiffOn
  · intro t ht
    have htL : |t| * L < 1 := by
      calc |t| * L ≤ 1 / (L + 1) * L := by gcongr; exact (abs_lt.mpr ⟨ht.1, ht.2⟩).le
        _ < 1 := by
          rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]; linarith
    -- `φ_t - id = tX` is `c`-Lipschitz with `c = |t|L < 1`, so `φ_t` is a homeomorphism `h`.
    let c : NNReal := ⟨|t| * L, by positivity⟩
    have hcR : (c : ℝ) = |t| * L := rfl
    have hA : ApproximatesLinearOn (fun y ↦ y + t • X y)
        ((ContinuousLinearEquiv.refl ℝ (Ambient n ℓ) : Ambient n ℓ →L[ℝ] Ambient n ℓ)) univ c := by
      intro x _ y _
      have hxy : x + t • X x - (y + t • X y) -
          (ContinuousLinearEquiv.refl ℝ (Ambient n ℓ) : Ambient n ℓ →L[ℝ] Ambient n ℓ) (x - y)
            = t • (X x - X y) := by
        simp only [ContinuousLinearEquiv.coe_refl, ContinuousLinearMap.id_apply, smul_sub]
        abel
      rw [hxy, norm_smul, Real.norm_eq_abs, hcR, mul_assoc]
      gcongr
      exact hLip x y
    have hc : Subsingleton (Ambient n ℓ) ∨ c < ‖((ContinuousLinearEquiv.refl ℝ (Ambient n ℓ)).symm :
        Ambient n ℓ →L[ℝ] Ambient n ℓ)‖₊⁻¹ := by
      rcases subsingleton_or_nontrivial (Ambient n ℓ) with h | h
      · exact Or.inl h
      · right
        rw [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl,
          ContinuousLinearMap.nnnorm_id, inv_one, ← NNReal.coe_lt_coe, hcR, NNReal.coe_one]
        exact htL
    let h := hA.toHomeomorph _ hc
    have hbij : Function.Bijective (fun y : Ambient n ℓ ↦ y + t • X y) := h.bijective
    refine ⟨hbij, ?_⟩
    have hinv : Function.invFun (fun y : Ambient n ℓ ↦ y + t • X y) = h.symm := by
      funext z
      apply hbij.1
      exact (Function.invFun_eq (hbij.2 z)).trans (h.apply_symm_apply z).symm
    rw [hinv]
    -- `Dφ_t(a) = I + t DX(a) = 1 - (-t DX(a))` is a unit since `‖t DX(a)‖ ≤ |t|L < 1`.
    have hsmall : ∀ a, ‖-(t • fderiv ℝ X a)‖ < 1 := fun a ↦ by
      rw [norm_neg, norm_smul, Real.norm_eq_abs]
      calc |t| * ‖fderiv ℝ X a‖ ≤ |t| * L := by gcongr; exact hDX a
        _ < 1 := htL
    refine h.contDiff_symm
      (f₀' := fun a ↦ ContinuousLinearEquiv.unitsEquiv ℝ _ (Units.oneSub _ (hsmall a))) ?_ ?_
    · intro a
      have hd : HasFDerivAt (fun y : Ambient n ℓ ↦ y + t • X y)
          (ContinuousLinearMap.id ℝ _ + t • fderiv ℝ X a) a :=
        (hasFDerivAt_id a).add (((hX1.differentiable one_ne_zero) a).hasFDerivAt.const_smul t)
      rw [show (⇑h : Ambient n ℓ → Ambient n ℓ) = fun y ↦ y + t • X y from rfl]
      convert hd using 1
      refine ContinuousLinearMap.ext fun v ↦ ?_
      show ((1 : Ambient n ℓ →L[ℝ] Ambient n ℓ) - -(t • fderiv ℝ X a)) v =
        ((ContinuousLinearMap.id ℝ (Ambient n ℓ) + t • fderiv ℝ X a :
          Ambient n ℓ →L[ℝ] Ambient n ℓ) v)
      simp
    · exact contDiff_id.add (hX.const_smul t)
  · intro x
    simp
  · intro t _ x hx
    simp [image_eq_zero_of_notMem_tsupport hx]
  · funext y
    have : HasDerivAt (fun t : ℝ ↦ y + t • X y) (X y) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (X y)).const_add y
    exact this.deriv
/-- **Smooth approximation of test fields (for Simon 2.4).** If `U` is open and
`X ∈ C¹_c(U; ℝ^{n+ℓ})`, there are a compact `K` with `tsupport X ⊆ K ⊆ U` and `C^∞` fields `Y_k`
with compact support in `K` such that `DY_k → DX` uniformly: `Y_k = ψ_k ⋆ X` for mollifiers
`ψ_k` supported in `B_{r_k}(0)`, `r_k ↓ 0`. -/
theorem Submission.exists_smooth_approx_testField_fderiv : ∀ (n ℓ : ℕ) (U : Set (Ambient n ℓ)) (X : Ambient n ℓ → Ambient n ℓ), IsOpen U → IsTestField U X → ∃ (K : Set (Ambient n ℓ)) (Y : ℕ → Ambient n ℓ → Ambient n ℓ), IsCompact K ∧ K ⊆ U ∧ tsupport X ⊆ K ∧ (∀ k, ContDiff ℝ ∞ (Y k) ∧ HasCompactSupport (Y k) ∧ tsupport (Y k) ⊆ K) ∧ TendstoUniformly (fun k ↦ fderiv ℝ (Y k)) (fderiv ℝ X) atTop := by
  intro n ℓ U X hU hXT
  obtain ⟨hX, hXc, hXU⟩ := hXT
  -- `K = cthickening δ (tsupport X) ⊆ U` is compact and contains `tsupport X`.
  obtain ⟨δ, hδ, hδU⟩ := hXc.exists_cthickening_subset_open hU hXU
  -- Radii `r k = δ / (k + 2) ∈ (0, δ)`, tending to `0`.
  set r : ℕ → ℝ := fun k ↦ δ / (k + 2) with hrdef
  have hr : ∀ k, 0 < r k := fun k ↦ by simp only [hrdef]; positivity
  have hrδ : ∀ k, r k < δ := fun k ↦ by
    simp only [hrdef]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  -- Mollifiers `ψ k = φ k / ∫ φ k` with `φ k` a smooth bump supported in `ball 0 (r k)`.
  let φ : ℕ → ContDiffBump (0 : Ambient n ℓ) := fun k ↦
    ⟨r k / 2, r k, half_pos (hr k), half_lt_self (hr k)⟩
  have hφint : ∀ k, 0 < ∫ x, φ k x := fun k ↦ by
    refine (integral_pos_iff_support_of_nonneg (φ k).nonneg'
      ((φ k).continuous.integrable_of_hasCompactSupport (φ k).hasCompactSupport)).mpr ?_
    rw [(φ k).support_eq]
    exact measure_ball_pos _ _ (hr k)
  set ψ : ℕ → Ambient n ℓ → ℝ := fun k x ↦ φ k x / ∫ y, φ k y with hψdef
  have hψsupp : ∀ k, Function.support (ψ k) = ball 0 (r k) := fun k ↦ by
    simp only [hψdef]
    rw [Function.support_div, (φ k).support_eq, Function.support_const (hφint k).ne', inter_univ]
  have hψc : ∀ k, HasCompactSupport (ψ k) := fun k ↦ by
    rw [HasCompactSupport, tsupport, hψsupp, closure_ball _ (hr k).ne']
    exact isCompact_closedBall _ _
  have hψnn : ∀ k x, 0 ≤ ψ k x := fun k x ↦ div_nonneg (φ k).nonneg (hφint k).le
  have hψ1 : ∀ k, ∫ x, ψ k x = 1 := fun k ↦ by
    simp only [hψdef]
    rw [integral_div, div_self (hφint k).ne']
  have hψsmooth : ∀ k, ContDiff ℝ ∞ (ψ k) := fun k ↦ (φ k).contDiff.div_const _
  -- `Y k = ψ k ⋆ X`.
  set Y : ℕ → Ambient n ℓ → Ambient n ℓ := fun k ↦
    convolution (ψ k) X (ContinuousLinearMap.lsmul ℝ ℝ) volume
  refine ⟨cthickening δ (tsupport X), Y, hXc.cthickening, hδU, self_subset_cthickening _,
    fun k ↦ ⟨?_, ?_, ?_⟩, ?_⟩
  · exact (hψc k).contDiff_convolution_left _ (hψsmooth k) hX.continuous.locallyIntegrable
  · exact (hψc k).convolution _ hXc
  · -- `support (ψ k ⋆ X) ⊆ ball 0 (r k) + tsupport X ⊆ cthickening δ (tsupport X)`.
    apply closure_minimal _ isClosed_cthickening
    refine (support_convolution_subset _).trans ?_
    rintro _ ⟨a, ha, b, hb, rfl⟩
    rw [hψsupp, mem_ball_zero_iff] at ha
    refine mem_cthickening_of_dist_le _ b δ _ (subset_tsupport _ hb) ?_
    rw [dist_eq_norm, add_sub_cancel_right]
    exact (ha.trans (hrδ k)).le
  · -- `DY_k = ψ k ⋆ DX`, and `DX` is uniformly continuous.
    rw [Metric.tendstoUniformly_iff]
    intro η hη
    have hDX : Continuous (fderiv ℝ X) := hX.continuous_fderiv one_ne_zero
    have huc : UniformContinuous (fderiv ℝ X) :=
      (hXc.fderiv ℝ).uniformContinuous_of_continuous hDX
    obtain ⟨ρ, hρ, hρη⟩ := Metric.uniformContinuous_iff.mp huc (η / 2) (half_pos hη)
    obtain ⟨N, hN⟩ := exists_nat_gt (δ / ρ)
    have hev : ∀ᶠ k in atTop, r k < ρ := by
      refine eventually_atTop.mpr ⟨N, fun k hk ↦ ?_⟩
      simp only [hrdef]
      rw [div_lt_iff₀ (by positivity)]
      have hkN : (N : ℝ) ≤ k := by exact_mod_cast hk
      rw [div_lt_iff₀ hρ] at hN
      nlinarith
    -- `(lsmul ℝ ℝ).precompR` is again scalar multiplication, now on `E →L[ℝ] E`.
    have hpre : (ContinuousLinearMap.lsmul ℝ ℝ :
        ℝ →L[ℝ] Ambient n ℓ →L[ℝ] Ambient n ℓ).precompR (Ambient n ℓ) =
          ContinuousLinearMap.lsmul ℝ ℝ := by
      ext c A v; simp
    filter_upwards [hev] with k hk x
    have hderiv : fderiv ℝ (Y k) x =
        convolution (ψ k) (fderiv ℝ X) (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
      rw [(hXc.hasFDerivAt_convolution_right _
        (hψsmooth k).continuous.locallyIntegrable hX x).fderiv, hpre]
    rw [hderiv, dist_comm]
    calc dist (convolution (ψ k) (fderiv ℝ X) (ContinuousLinearMap.lsmul ℝ ℝ) volume x)
          (fderiv ℝ X x) ≤ η / 2 :=
        dist_convolution_le (half_pos hη).le (hψsupp k).le (hψnn k) (hψ1 k)
          hDX.aestronglyMeasurable fun y hy ↦ (hρη ((mem_ball.mp hy).trans hk)).le
      _ < η := half_lt_self hη
namespace Submission

theorem tendsto_integral_tangentialDiv_of_tendstoUniformly_fderiv : ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (K : Set (Ambient n ℓ)) (X : Ambient n ℓ → Ambient n ℓ) (Y : ℕ → Ambient n ℓ → Ambient n ℓ), IsFiniteMeasureOnCompacts V.weight → AEStronglyMeasurable (fun x ↦ (V.tangentSpace x).starProjection) V.weight → IsCompact K → ContDiff ℝ 1 X → tsupport X ⊆ K → (∀ k, ContDiff ℝ 1 (Y k) ∧ tsupport (Y k) ⊆ K) → TendstoUniformly (fun k ↦ fderiv ℝ (Y k)) (fderiv ℝ X) atTop → Tendsto (fun k ↦ ∫ x, V.tangentialDiv (Y k) x ∂V.weight) atTop (𝓝 (∫ x, V.tangentialDiv X x ∂V.weight)) := by
  intro n ℓ V K X Y hfin hP hK hX hXK hY hconv
  -- Step 1: `|trace (A ∘ P)| ≤ (n + ℓ) ‖A‖` when `‖P‖ ≤ 1`, expanding the trace in the
  -- standard orthonormal basis `eᵢ` and bounding each `⟪eᵢ, A P eᵢ⟫` by Cauchy–Schwarz.
  set d : ℝ := ((n + ℓ : ℕ) : ℝ)
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have htrace : ∀ A P : Ambient n ℓ →L[ℝ] Ambient n ℓ, ‖P‖ ≤ 1 →
      |LinearMap.trace ℝ (Ambient n ℓ) (A.comp P).toLinearMap| ≤ d * ‖A‖ := by
    intro A P hP
    set b := EuclideanSpace.basisFun (Fin (n + ℓ)) ℝ
    rw [LinearMap.trace_eq_matrix_trace ℝ b.toBasis, Matrix.trace]
    simp only [Matrix.diag, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
    calc |∑ i, inner ℝ (b i) ((A.comp P).toLinearMap (b i))|
        ≤ ∑ i, |inner ℝ (b i) ((A.comp P).toLinearMap (b i))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin (n + ℓ), ‖A‖ := by
          gcongr with i
          have hb : ‖b i‖ = 1 := b.orthonormal.1 i
          calc |inner ℝ (b i) ((A.comp P).toLinearMap (b i))|
              ≤ ‖b i‖ * ‖(A.comp P) (b i)‖ := abs_real_inner_le_norm _ _
            _ ≤ ‖b i‖ * (‖A.comp P‖ * ‖b i‖) := by gcongr; exact (A.comp P).le_opNorm (b i)
            _ = ‖A.comp P‖ := by rw [hb]; ring
            _ ≤ ‖A‖ * ‖P‖ := A.opNorm_comp_le P
            _ ≤ ‖A‖ * 1 := by gcongr
            _ = ‖A‖ := mul_one _
      _ = d * ‖A‖ := by simp [d]
  -- Step 2: `div_M Z x = T (DZ(x) ∘ p_x)` for the continuous linear functional `T = trace`,
  -- so `div_M Z` is a continuous function of `(DZ(x), p_x)`, hence a.e. strongly measurable.
  set T : (Ambient n ℓ →L[ℝ] Ambient n ℓ) →ₗ[ℝ] ℝ :=
    (LinearMap.trace ℝ (Ambient n ℓ)).comp (ContinuousLinearMap.coeLM ℝ) with hT
  have hTc : Continuous T := T.continuous_of_finiteDimensional
  have hdiv : ∀ Z x, V.tangentialDiv Z x =
      T ((fderiv ℝ Z x).comp (V.tangentSpace x).starProjection) := fun Z x ↦ rfl
  have hcomp : Continuous (fun q : (Ambient n ℓ →L[ℝ] Ambient n ℓ) × (Ambient n ℓ →L[ℝ] Ambient n ℓ) ↦
      q.1.comp q.2) := isBoundedBilinearMap_comp.continuous
  have hmeas : ∀ Z : Ambient n ℓ → Ambient n ℓ, ContDiff ℝ 1 Z →
      AEStronglyMeasurable (fun x ↦ V.tangentialDiv Z x) V.weight := by
    intro Z hZ
    have h1 : Continuous (fun x ↦ fderiv ℝ Z x) := hZ.continuous_fderiv one_ne_zero
    exact (hTc.comp hcomp).comp_aestronglyMeasurable (h1.aestronglyMeasurable.prodMk hP)
  have hbound : ∀ (A : Ambient n ℓ →L[ℝ] Ambient n ℓ) x,
      |T (A.comp (V.tangentSpace x).starProjection)| ≤ d * ‖A‖ := fun A x ↦
    htrace A _ (Submodule.starProjection_norm_le _)
  -- Step 3: `div_M Z` vanishes off `K` when `tsupport Z ⊆ K`.
  have hvan : ∀ Z : Ambient n ℓ → Ambient n ℓ, tsupport Z ⊆ K → ∀ x ∉ K,
      V.tangentialDiv Z x = 0 := by
    intro Z hZK x hx
    rw [hdiv, fderiv_of_notMem_tsupport ℝ (fun h ↦ hx (hZK h))]
    simp
  -- Step 4: `div_M Z` is integrable, being bounded by `d B 1_K` with `μ(K) < ∞`.
  have hμK : V.weight K < ⊤ := hK.measure_lt_top
  have hint : ∀ Z : Ambient n ℓ → Ambient n ℓ, ContDiff ℝ 1 Z → tsupport Z ⊆ K →
      Integrable (fun x ↦ V.tangentialDiv Z x) V.weight := by
    intro Z hZ hZK
    have hZc : HasCompactSupport Z := hK.of_isClosed_subset (isClosed_tsupport Z) hZK
    obtain ⟨B, hB⟩ := (hZc.fderiv ℝ).exists_bound_of_continuous (hZ.continuous_fderiv one_ne_zero)
    refine Integrable.mono' ((integrableOn_const (C := d * B) hμK.ne).integrable_indicator
      hK.isClosed.measurableSet) (hmeas Z hZ) (Eventually.of_forall fun x ↦ ?_)
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx, Real.norm_eq_abs, hdiv]
      exact (hbound _ x).trans (by gcongr; exact hB x)
    · rw [indicator_of_notMem hx, hvan Z hZK x hx, norm_zero]
  have hIX := hint X hX hXK
  -- Steps 5–6: `|∫ div_M Y_k - ∫ div_M X| ≤ d sup ‖DY_k - DX‖ μ(K) → 0`.
  rw [Metric.tendsto_atTop]
  intro η hη
  set m : ℝ := V.weight.real K
  have hm0 : 0 ≤ m := measureReal_nonneg
  obtain ⟨N, hN⟩ := (Metric.tendstoUniformly_iff.mp hconv (η / (2 * (d * m + 1)))
    (by positivity)).exists_forall_of_atTop
  refine ⟨N, fun k hk ↦ ?_⟩
  have hIY := hint (Y k) (hY k).1 (hY k).2
  rw [Real.dist_eq, ← integral_sub hIY hIX]
  calc |∫ x, V.tangentialDiv (Y k) x - V.tangentialDiv X x ∂V.weight|
      ≤ ∫ x, K.indicator (fun _ ↦ d * (η / (2 * (d * m + 1)))) x ∂V.weight := by
        rw [← Real.norm_eq_abs]
        refine norm_integral_le_of_norm_le
          ((integrableOn_const (C := d * (η / (2 * (d * m + 1)))) hμK.ne).integrable_indicator
          hK.isClosed.measurableSet)
          (Eventually.of_forall fun x ↦ ?_)
        by_cases hx : x ∈ K
        · rw [indicator_of_mem hx, Real.norm_eq_abs, hdiv, hdiv, ← map_sub,
            ← ContinuousLinearMap.sub_comp]
          refine (hbound _ x).trans ?_
          gcongr
          rw [← dist_eq_norm, dist_comm]
          exact (hN k hk x).le
        · rw [indicator_of_notMem hx, hvan _ (hY k).2 x hx, hvan X hXK x hx, sub_zero, norm_zero]
    _ = d * (η / (2 * (d * m + 1))) * m := by
        rw [integral_indicator hK.isClosed.measurableSet, setIntegral_const, smul_eq_mul, mul_comm]
    _ < η := by
        have h1 : 0 < d * m + 1 := by positivity
        have he : d * (η / (2 * (d * m + 1))) * m = η * (d * m) / (2 * (d * m + 1)) := by ring
        rw [he, div_lt_iff₀ (by positivity)]
        nlinarith [mul_nonneg hd0 hm0]

end Submission

/-- **Stationarity** (Ch. 4, 2.4). Given (GF) and the first variation formula 2.2, the integral
and variational forms of stationarity agree: the initial velocity of a compact variation with
`K ⊆ U` is a test field in `U`; a smooth compactly supported `X` is the initial velocity of the
compact variation `y + tX(y)`; and a `C¹` test field is the `C¹` limit of smooth fields supported
in one compact subset of `U`, along which `∫ div_M` converges by (GF). -/
theorem Submission.stationary_iff_variational_of_first_variation :
    (∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ), 0 < n → IsFiniteMeasureOnCompacts V.weight ∧
      (∀ᵐ x ∂V.weight, Module.finrank ℝ (V.tangentSpace x) = n) ∧
      AEStronglyMeasurable (fun x ↦ (V.tangentSpace x).starProjection) V.weight) →
    FirstVariationFormula → StationaryIffVariational := by
  intro hGF hFVF n ℓ a U hn hU
  refine ⟨fun hstat φ ε K hφ hKU ↦ ?_, fun hvar ↦ ?_⟩
  · -- (⇒) The initial velocity of `φ` is a test field in `U`, so the first variation vanishes.
    exact (hFVF n ℓ a φ ε K hn hφ).congr_deriv
      (hstat _ (Submission.compactVariation_velocity_isTestField n ℓ U φ ε K hφ hKU))
  · -- (⇐), smooth fields: `Z` is the initial velocity of `y + t • Z y`, and derivatives are unique.
    have hsmooth : ∀ Z : Ambient n ℓ → Ambient n ℓ, ContDiff ℝ ∞ Z → HasCompactSupport Z →
        tsupport Z ⊆ U → ∫ x, (mk a).tangentialDiv Z x ∂(mk a).weight = 0 := by
      intro Z hZ hZc hZU
      obtain ⟨ε, hφ, hvel⟩ := Submission.exists_isCompactVariation_add_smul n ℓ Z hZ hZc
      calc ∫ x, (mk a).tangentialDiv Z x ∂(mk a).weight
          = ∫ x, (mk a).tangentialDiv (fun y ↦ deriv (fun t : ℝ ↦ y + t • Z y) 0) x
              ∂(mk a).weight :=
            congrArg (fun W ↦ ∫ x, (mk a).tangentialDiv W x ∂(mk a).weight) hvel.symm
        _ = 0 := (hFVF n ℓ a _ ε _ hn hφ).unique (hvar _ ε _ hφ hZU)
    -- (⇐), `C¹` fields: approximate `X` in `C¹` by smooth `Y k` supported in a compact `K ⊆ U`.
    intro X hX
    obtain ⟨K, Y, hK, hKU, hXK, hY, hYX⟩ :=
      Submission.exists_smooth_approx_testField_fderiv n ℓ U X hU hX
    obtain ⟨hfin, -, hmeas⟩ := hGF n ℓ (mk a) hn
    refine tendsto_nhds_unique
      (Submission.tendsto_integral_tangentialDiv_of_tendstoUniformly_fderiv n ℓ (mk a) K X Y
        hfin hmeas hK hX.1 hXK
        (fun k ↦ ⟨(hY k).1.of_le (WithTop.coe_le_coe.mpr le_top), (hY k).2.2⟩) hYX) ?_
    exact tendsto_const_nhds.congr fun k ↦
      (hsmooth (Y k) (hY k).1 (hY k).2.1 ((hY k).2.2.trans hKU)).symm

theorem main_theorem : ApproxTangentAE ∧ FirstVariationFormula ∧ StationaryIffVariational ∧ StationaryMonotonicity ∧ StationaryDensity ∧ CanonicalRepresentative ∧ BoundedCurvatureMonotonicity ∧ LogarithmicMonotonicityError ∧ LpMonotonicity ∧ LpDensity ∧ LpSupportRepresentation ∧ PoincareInequality ∧ SobolevInequality ∧ SupportInBall ∧ ConvexHullProperty ∧ ClassicalTangent := by sorry

end

end GMT.Ch04
