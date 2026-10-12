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

/-- **Backward integral Gronwall inequality** (the Gronwall form of Simon Ch. 4, 5.4, used in the
proof of 5.6). If `a ≤ b`, `Λ ≥ 0`, `f` is integrable on `[a, b]` and
`f(s) ≤ C + Λ ∫_{(s,b]} f` for every `s ∈ [a, b]`, then `f(s) ≤ C e^{Λ(b - s)}` on `[a, b]`; no sign
condition on `C` or `f` is needed. The continuous majorant `F(s) = C + Λ ∫_s^b f` of `f` satisfies
`F ≤ G := C + Λ ∫_s^b F` by monotonicity of the integral, and by the fundamental theorem of calculus
for the continuous `F`, `e^{Λs} G(s)` has derivative `Λ e^{Λs} (G(s) - F(s)) ≥ 0` on `(a, b)`. Hence
it is nondecreasing on `[a, b]`, so `e^{Λs} G(s) ≤ e^{Λb} G(b) = e^{Λb} C` and
`f(s) ≤ F(s) ≤ G(s) ≤ C e^{Λ(b - s)}`. -/
theorem Submission.backward_integral_gronwall_Ioc : ∀ (a b Λ C : ℝ) (f : ℝ → ℝ), a ≤ b → 0 ≤ Λ → IntegrableOn f (Icc a b) → (∀ s ∈ Icc a b, f s ≤ C + Λ * ∫ τ in Ioc s b, f τ) → ∀ s ∈ Icc a b, f s ≤ C * Real.exp (Λ * (b - s)) := by
  intro a b Λ C f hab hΛ hf hineq
  have hsub : ∀ s ∈ Icc a b, uIcc s b ⊆ Icc a b := fun s hs ↦ by
    rw [uIcc_of_le hs.2]
    exact Icc_subset_Icc hs.1 le_rfl
  -- Step 1: `F(s) = C + Λ ∫_s^b f` majorizes `f` on `[a, b]` (for `s ≤ b`, `∫_s^b = ∫_{(s,b]}`)
  set F : ℝ → ℝ := fun s ↦ C + Λ * ∫ τ in s..b, f τ
  have hfF : ∀ s ∈ Icc a b, f s ≤ F s := fun s hs ↦ by
    have h := hineq s hs
    rwa [← intervalIntegral.integral_of_le hs.2] at h
  -- Step 2: `F` is continuous on `[a, b]` (continuity of the primitive of an integrable function)
  have hFcont : ContinuousOn F (Icc a b) := by
    have h := intervalIntegral.continuousOn_primitive_interval_left (μ := volume) (f := f)
      (a := a) (b := b) (by rwa [uIcc_of_le hab])
    rw [uIcc_of_le hab] at h
    exact continuousOn_const.add (continuousOn_const.mul h)
  have hFint : IntegrableOn F (Icc a b) := hFcont.integrableOn_Icc
  -- Step 3: `F ≤ G := C + Λ ∫_s^b F` on `[a, b]` (monotonicity of the integral, `Λ ≥ 0`)
  set G : ℝ → ℝ := fun s ↦ C + Λ * ∫ τ in s..b, F τ with hG
  have hFG : ∀ s ∈ Icc a b, F s ≤ G s := by
    intro s hs
    have hmono : ∫ τ in s..b, f τ ≤ ∫ τ in s..b, F τ :=
      intervalIntegral.integral_mono_on hs.2 (hf.mono_set (hsub s hs)).intervalIntegrable
        (hFint.mono_set (hsub s hs)).intervalIntegrable
        fun x hx ↦ hfF x (Icc_subset_Icc hs.1 le_rfl hx)
    show C + Λ * ∫ τ in s..b, f τ ≤ C + Λ * ∫ τ in s..b, F τ
    gcongr
  -- Step 4: `G` is continuous on `[a, b]` with `G'(s) = -Λ F(s)` on `(a, b)` (FTC, `F` continuous)
  have hGcont : ContinuousOn G (Icc a b) := by
    have h := intervalIntegral.continuousOn_primitive_interval_left (μ := volume) (f := F)
      (a := a) (b := b) (by rwa [uIcc_of_le hab])
    rw [uIcc_of_le hab] at h
    exact continuousOn_const.add (continuousOn_const.mul h)
  have hGderiv : ∀ s ∈ Ioo a b, HasDerivAt G (Λ * -F s) s := by
    intro s hs
    have hFi : IntervalIntegrable F volume s b :=
      (hFint.mono_set (hsub s (Ioo_subset_Icc_self hs))).intervalIntegrable
    have hmeas : StronglyMeasurableAtFilter F (𝓝 s) :=
      (hFcont.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo s hs
    have hcont : ContinuousAt F s := hFcont.continuousAt (Icc_mem_nhds hs.1 hs.2)
    exact ((intervalIntegral.integral_hasDerivAt_left hFi hmeas hcont).const_mul Λ).const_add C
  -- Step 5: `Φ(s) = e^{Λs} G(s)` has `Φ' = Λ e^{Λs} (G - F) ≥ 0` on `(a, b)`, so it is monotone
  set Φ : ℝ → ℝ := fun s ↦ Real.exp (Λ * s) * G s with hΦ
  have hΦderiv : ∀ s ∈ Ioo a b,
      HasDerivAt Φ (Real.exp (Λ * s) * Λ * G s + Real.exp (Λ * s) * (Λ * -F s)) s := by
    intro s hs
    have hexp : HasDerivAt (fun y ↦ Real.exp (Λ * y)) (Real.exp (Λ * s) * Λ) s := by
      simpa using ((hasDerivAt_id s).const_mul Λ).exp
    exact hexp.mul (hGderiv s hs)
  have hΦmono : MonotoneOn Φ (Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b) ?_ ?_ ?_
    · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul
        hGcont
    · rw [interior_Icc]
      exact fun s hs ↦ (hΦderiv s hs).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro s hs
      rw [(hΦderiv s hs).deriv]
      have hFGs := hFG s (Ioo_subset_Icc_self hs)
      have hexp := Real.exp_pos (Λ * s)
      have h : Real.exp (Λ * s) * Λ * G s + Real.exp (Λ * s) * (Λ * -F s) =
          Real.exp (Λ * s) * Λ * (G s - F s) := by ring
      rw [h]
      exact mul_nonneg (mul_nonneg hexp.le hΛ) (by linarith)
  -- Step 6: `e^{Λs} G(s) ≤ e^{Λb} G(b) = e^{Λb} C`, i.e. `G(s) ≤ C e^{Λ(b - s)}`
  intro s hs
  have hGb : G b = C := by simp [hG]
  have h1 : Real.exp (Λ * s) * G s ≤ Real.exp (Λ * b) * C := by
    simpa [hΦ, hGb] using hΦmono hs (right_mem_Icc.2 hab) hs.2
  have h2 : G s ≤ C * Real.exp (Λ * (b - s)) := by
    have h : Real.exp (Λ * b) = Real.exp (Λ * s) * Real.exp (Λ * (b - s)) := by
      rw [← Real.exp_add]
      ring_nf
    rw [h, mul_assoc, mul_comm (Real.exp (Λ * (b - s)))] at h1
    exact le_of_mul_le_mul_left h1 (Real.exp_pos (Λ * s))
  -- Step 7: `f(s) ≤ F(s) ≤ G(s) ≤ C e^{Λ(b - s)}`
  exact (hfF s hs).trans ((hFG s hs).trans h2)
/-- **`C¹` step function for the truncations `γ(h - t)`** (Simon Ch. 4, proof of 5.6, pp. 97–98).
For `ε > 0`, `ψ(x) = S(x / ε)` with `S = Real.smoothTransition` is `C¹`, nondecreasing,
`[0, 1]`-valued, `0` on `(-∞, 0]` and `1` on `[ε, ∞)`. `ψ'` is continuous and vanishes off
`[0, ε]`, hence bounded, and with `T = max a 0`,
`∫_{(0,∞)} ψ'(a - t) dt = ∫_0^T ψ'(a - t) dt = ψ(a) - ψ(a - T) = ψ(a) ≤ 1`. -/
theorem Submission.smooth_step_truncation_exists : ∀ ε : ℝ, 0 < ε → ∃ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ ∧ (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) ∧ (∀ x, x ≤ 0 → ψ x = 0) ∧ (∀ x, ε ≤ x → ψ x = 1) ∧ (∀ x, 0 ≤ deriv ψ x) ∧ (∃ M : ℝ, ∀ x, deriv ψ x ≤ M) ∧ ∀ a : ℝ, ∫⁻ t in Ioi 0, ENNReal.ofReal (deriv ψ (a - t)) ≤ 1 := by
  intro ε hε
  -- `ψ(x) = S(x / ε)`: `C¹`, nondecreasing, `0` on `(-∞, 0]`, `1` on `[ε, ∞)`
  set ψ : ℝ → ℝ := fun x ↦ Real.smoothTransition (x / ε) with hψdef
  have hψC : ContDiff ℝ 1 ψ :=
    (Real.smoothTransition.contDiff (n := 1)).comp (contDiff_id.div_const ε)
  have hψmono : Monotone ψ := fun x y hxy ↦
    Real.smoothTransition.monotone (div_le_div_of_nonneg_right hxy hε.le)
  have hψ0 : ∀ x, x ≤ 0 → ψ x = 0 := fun x hx ↦
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hx hε.le)
  have hψ1 : ∀ x, ε ≤ x → ψ x = 1 := fun x hx ↦
    Real.smoothTransition.one_of_one_le ((one_le_div hε).2 hx)
  -- `ψ'` vanishes off `[0, ε]`, since `ψ` is locally constant there
  have hd0 : ∀ x, x < 0 → deriv ψ x = 0 := by
    intro x hx
    have : ψ =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) :=
      (eventually_lt_nhds hx).mono fun y hy ↦ hψ0 y hy.le
    rw [this.deriv_eq, deriv_const]
  have hd1 : ∀ x, ε < x → deriv ψ x = 0 := by
    intro x hx
    have : ψ =ᶠ[𝓝 x] fun _ ↦ (1 : ℝ) :=
      (eventually_gt_nhds hx).mono fun y hy ↦ hψ1 y hy.le
    rw [this.deriv_eq, deriv_const]
  -- `ψ'` is continuous with support in `[0, ε]`
  have hdcont : Continuous (deriv ψ) := hψC.continuous_deriv le_rfl
  have hdsupp : HasCompactSupport (deriv ψ) := by
    refine HasCompactSupport.of_support_subset_isCompact (K := Icc 0 ε) isCompact_Icc ?_
    intro x hx
    by_contra hxI
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hxI
    rcases hxI with h | h
    · exact hx (hd0 x h)
    · exact hx (hd1 x h)
  have hdnn : ∀ x, 0 ≤ deriv ψ x := fun x ↦ hψmono.deriv_nonneg
  refine ⟨ψ, hψC, fun x ↦ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩,
    hψ0, hψ1, hdnn, ?_, ?_⟩
  · obtain ⟨M, hM⟩ := hdcont.bddAbove_range_of_hasCompactSupport hdsupp
    exact ⟨M, fun x ↦ hM ⟨x, rfl⟩⟩
  · intro a
    -- split `(0, ∞) = (0, T] ∪ (T, ∞)` with `T = max a 0`; the integrand vanishes on `(T, ∞)`
    set T := max a 0 with hT
    have hT0 : 0 ≤ T := le_max_right _ _
    have hsplit : Ioi (0 : ℝ) = Ioc 0 T ∪ Ioi T := (Ioc_union_Ioi_eq_Ioi hT0).symm
    rw [hsplit, lintegral_union measurableSet_Ioi (Ioc_disjoint_Ioi le_rfl)]
    have h2 : ∫⁻ t in Ioi T, ENNReal.ofReal (deriv ψ (a - t)) = 0 := by
      refine setLIntegral_eq_zero_iff' measurableSet_Ioi ?_ |>.2 ?_
      · exact (ENNReal.measurable_ofReal.comp ((measurable_deriv ψ).comp
          (measurable_const.sub measurable_id))).aemeasurable
      · refine Eventually.of_forall fun t ht ↦ ?_
        have : a - t < 0 := by
          have := le_max_left a 0
          rw [Set.mem_Ioi] at ht
          linarith
        rw [hd0 _ this, ENNReal.ofReal_zero]
    rw [h2, add_zero]
    -- on `(0, T]`: substitution `u = a - t` and FTC give `ψ(a) - ψ(a - T) = ψ(a) ≤ 1`
    have hint : IntegrableOn (fun t ↦ deriv ψ (a - t)) (Ioc 0 T) :=
      ((hdcont.comp (continuous_const.sub continuous_id)).integrableOn_Icc).mono_set
        Ioc_subset_Icc_self
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun t ↦ hdnn _),
      ← intervalIntegral.integral_of_le hT0, intervalIntegral.integral_comp_sub_left,
      intervalIntegral.integral_deriv_eq_sub (fun x _ ↦ (hψC.differentiable one_ne_zero) x)
        (hdcont.intervalIntegrable _ _)]
    have : a - T ≤ 0 := by have := le_max_left a 0; linarith
    rw [sub_zero, hψ0 _ this, sub_zero]
    exact ENNReal.ofReal_le_one.2 (Real.smoothTransition.le_one _)
/-- **Kernel bound** (Simon Ch. 4, 4.10(2) for full balls, via 4.11; used in 5.6). If
`μ(B_s(y)) ≤ K sⁿ` for `0 < s ≤ ρ`, then `∫_{B_s(y)} |x - y|^{1-n} dμ ≤ n K s` for `0 < s ≤ ρ`.
By the layer-cake formula, the levels `t ≤ s^{1-n}` contribute at most `μ(B_s(y)) s^{1-n} ≤ K s`;
for `t > s^{1-n}` the superlevel set lies in `B_{t^{1/(1-n)}}(y)`, so these levels contribute at
most `K ∫_{s^{1-n}}^∞ t^{n/(1-n)} dt = (n - 1) K s`. -/
theorem Submission.closedBall_rpow_kernel_lintegral_le_of_growth : ∀ {X : Type} [NormedAddCommGroup X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) (n : ℕ) (y : X) (ρ K : ℝ), 0 < n → (∀ s : ℝ, 0 < s → s ≤ ρ → μ (closedBall y s) ≤ ENNReal.ofReal (K * s ^ n)) → ∀ s : ℝ, 0 < s → s ≤ ρ → ∫⁻ x in closedBall y s, ENNReal.ofReal (‖x - y‖ ^ (1 - (n : ℝ))) ∂μ ≤ ENNReal.ofReal (n * K * s) := by
  intro X _ _ _ μ n y ρ K hn hgrowth s hs hsρ
  -- `K < 0`: then `μ(B_s(y)) = 0`
  rcases lt_or_ge K 0 with hK | hK
  · have h0 : μ (closedBall y s) = 0 := by
      have := hgrowth s hs hsρ
      rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hK.le (pow_pos hs n).le)] at this
      exact le_antisymm this bot_le
    rw [Measure.restrict_eq_zero.2 h0, lintegral_zero_measure]
    exact bot_le
  -- `n = 1`: the integrand is `1` and the bound is the growth hypothesis
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · have hn1 : n = 1 := by omega
    subst hn1
    simp only [Nat.cast_one, sub_self, Real.rpow_zero, ENNReal.ofReal_one, lintegral_const,
      Measure.restrict_apply MeasurableSet.univ, univ_inter, one_mul]
    simpa using hgrowth s hs hsρ
  -- `n ≥ 2`: layer cake for `F = ‖· - y‖^z`, `z = 1 - n < 0`, on `μ ⌞ B_s(y)`
  set z : ℝ := 1 - (n : ℝ) with hz
  have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hz0 : z < 0 := by linarith
  set F : X → ℝ := fun x => ‖x - y‖ ^ z with hF
  have hFmeas : Measurable F := (measurable_id.sub_const y).norm.pow_const z
  have hF0 : ∀ x, 0 ≤ F x := fun x => Real.rpow_nonneg (norm_nonneg _) _
  have hLC := lintegral_eq_lintegral_meas_lt (μ.restrict (closedBall y s))
    (Eventually.of_forall hF0) hFmeas.aemeasurable
  rw [hLC]
  set T : ℝ := s ^ z with hT
  have hTpos : 0 < T := Real.rpow_pos_of_pos hs z
  -- every level set has measure at most `μ(B_s(y)) ≤ K sⁿ`
  have hlev1 : ∀ t : ℝ, (μ.restrict (closedBall y s)) {x | t < F x} ≤
      ENNReal.ofReal (K * s ^ n) := by
    intro t
    calc (μ.restrict (closedBall y s)) {x | t < F x} ≤ (μ.restrict (closedBall y s)) univ :=
          measure_mono (subset_univ _)
      _ = μ (closedBall y s) := by rw [Measure.restrict_apply_univ]
      _ ≤ _ := hgrowth s hs hsρ
  -- for `t > T = s^z`, `{F > t} ⊆ B_{t^{1/z}}(y)` with `0 < t^{1/z} < s`
  have hlev2 : ∀ t : ℝ, T < t →
      (μ.restrict (closedBall y s)) {x | t < F x} ≤ ENNReal.ofReal (K * t ^ ((n : ℝ) / z)) := by
    intro t ht
    have htpos : 0 < t := hTpos.trans ht
    have hr : t ^ z⁻¹ < s := (Real.rpow_inv_lt_iff_of_neg htpos hs hz0).2 ht
    have hrpos : 0 < t ^ z⁻¹ := Real.rpow_pos_of_pos htpos _
    have hpow : (t ^ z⁻¹) ^ n = t ^ ((n : ℝ) / z) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul htpos.le, inv_mul_eq_div]
    calc (μ.restrict (closedBall y s)) {x | t < F x} ≤ μ {x | t < F x} :=
          Measure.restrict_le_self _
      _ ≤ μ (closedBall y (t ^ z⁻¹)) := by
          apply measure_mono
          intro x hx
          simp only [Set.mem_ofPred_eq, hF] at hx
          rw [mem_closedBall, dist_eq_norm]
          by_cases hxy : ‖x - y‖ = 0
          · rw [hxy, Real.zero_rpow hz0.ne] at hx; linarith
          · have hpos : 0 < ‖x - y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hxy)
            exact ((Real.lt_rpow_inv_iff_of_neg hpos htpos hz0).2 hx).le
      _ ≤ ENNReal.ofReal (K * (t ^ z⁻¹) ^ n) := hgrowth _ hrpos (hr.le.trans hsρ)
      _ = ENNReal.ofReal (K * t ^ ((n : ℝ) / z)) := by rw [hpow]
  -- split `(0, ∞) = (0, T] ∪ (T, ∞)`
  have hsplit : Ioi (0 : ℝ) = Ioc 0 T ∪ Ioi T := (Ioc_union_Ioi_eq_Ioi hTpos.le).symm
  rw [hsplit, lintegral_union measurableSet_Ioi (Ioc_disjoint_Ioi le_rfl)]
  -- `(0, T]`: at most `K sⁿ · s^{1-n} = K s`
  have hI1 : ∫⁻ t in Ioc 0 T, (μ.restrict (closedBall y s)) {x | t < F x} ≤
      ENNReal.ofReal (K * s) := by
    calc ∫⁻ t in Ioc 0 T, (μ.restrict (closedBall y s)) {x | t < F x}
        ≤ ∫⁻ t in Ioc 0 T, ENNReal.ofReal (K * s ^ n) :=
          setLIntegral_mono' measurableSet_Ioc fun t _ => hlev1 t
      _ = ENNReal.ofReal (K * s ^ n) * ENNReal.ofReal T := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero]
      _ = ENNReal.ofReal (K * s) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [hT, hz, mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hs]
          norm_num
  -- `n/z + 1 = 1/z < 0`
  have h1 : (n : ℝ) / z + 1 = z⁻¹ := by
    have hzne : (1 : ℝ) - n ≠ 0 := by linarith
    rw [hz]; field_simp; ring
  have hexp : (n : ℝ) / z < -1 := by
    have h2 : z⁻¹ < 0 := inv_lt_zero.2 hz0
    linarith
  -- `(T, ∞)`: at most `K ∫_T^∞ t^{n/z} dt = K (n - 1) s`
  have hI2 : ∫⁻ t in Ioi T, (μ.restrict (closedBall y s)) {x | t < F x} ≤
      ENNReal.ofReal (K * ((n : ℝ) - 1) * s) := by
    calc ∫⁻ t in Ioi T, (μ.restrict (closedBall y s)) {x | t < F x}
        ≤ ∫⁻ t in Ioi T, ENNReal.ofReal (K * t ^ ((n : ℝ) / z)) :=
          setLIntegral_mono' measurableSet_Ioi fun t ht => hlev2 t ht
      _ = ENNReal.ofReal (∫ t in Ioi T, K * t ^ ((n : ℝ) / z)) := by
          rw [ofReal_integral_eq_lintegral_ofReal]
          · exact (integrableOn_Ioi_rpow_of_lt hexp hTpos).const_mul K
          · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
            exact mul_nonneg hK (Real.rpow_nonneg (hTpos.trans ht).le _)
      _ = ENNReal.ofReal (K * ((n : ℝ) - 1) * s) := by
          congr 1
          rw [integral_const_mul, integral_Ioi_rpow_of_lt hexp hTpos, h1, hT,
            Real.rpow_rpow_inv hs.le hz0.ne, hz]
          field_simp
          ring
  -- total: `K s + K (n - 1) s = n K s`
  calc _ ≤ ENNReal.ofReal (K * s) + ENNReal.ofReal (K * ((n : ℝ) - 1) * s) := add_le_add hI1 hI2
    _ = ENNReal.ofReal (n * K * s) := by
        have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by linarith
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
/-- **Layer-cake/Tonelli bound** (Simon Ch. 4, proof of 5.6, p. 98: integration over
`ζ ∈ A_{t+ε} ∩ B_{βρ}(ξ)`, then over `t ∈ (0, ∞)` using 4.11). With `f = max (h - ε) 0`, the layer-cake
formula for `μ ⌞ A` gives `∫_A (h - ε)⁺ dμ = ∫_0^∞ μ(A ∩ {t + ε < h}) dt`. For each `t > 0` the
level-`t` hypothesis, Tonelli in `(ζ, x)` and `∫_A k(x, ·) dμ ≤ L` on `B` give
`κ μ(A ∩ {t + ε < h}) ≤ L ∫_B φ(t, ·) G dμ`; integrating in `t`, Tonelli in `(t, x)` and
`∫_0^∞ φ(t, x) dt ≤ 1` on `B` give the claim. Everything is in `[0, ∞]`, so no finiteness is
needed. -/
theorem Submission.layer_cake_tonelli_truncation_bound : ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) [SFinite μ] (A B : Set X) (h : X → ℝ) (φ : ℝ → X → ℝ≥0∞) (G : X → ℝ≥0∞) (k : X → X → ℝ≥0∞) (κ L : ℝ≥0∞) (ε : ℝ), MeasurableSet A → MeasurableSet B → Measurable h → Measurable (Function.uncurry φ) → Measurable G → Measurable (Function.uncurry k) → (∀ x ∈ B, ∫⁻ t in Ioi 0, φ t x ≤ 1) → (∀ x ∈ B, ∫⁻ ζ in A, k x ζ ∂μ ≤ L) → (∀ t : ℝ, 0 < t → ∀ᵐ ζ ∂μ, ζ ∈ A → t + ε < h ζ → κ ≤ ∫⁻ x in B, φ t x * G x * k x ζ ∂μ) → κ * ∫⁻ ζ in A, ENNReal.ofReal (h ζ - ε) ∂μ ≤ L * ∫⁻ x in B, G x ∂μ := by
  intro X _ μ _ A B h φ G k κ L ε hA hB hh hφ hG hk hi hii hiii
  -- step 1: `ofReal (h - ε) = ofReal f` with `f = max (h - ε) 0 ≥ 0`, then layer cake on `μ ⌞ A`
  set f : X → ℝ := fun ζ ↦ max (h ζ - ε) 0 with hf
  have hfmeas : Measurable f := (hh.sub measurable_const).max measurable_const
  have hofReal : ∀ ζ, ENNReal.ofReal (h ζ - ε) = ENNReal.ofReal (f ζ) := fun ζ ↦ by
    show ENNReal.ofReal (h ζ - ε) = ENNReal.ofReal (max (h ζ - ε) 0)
    rcases le_total 0 (h ζ - ε) with hp | hn
    · rw [max_eq_left hp]
    · rw [max_eq_right hn, ENNReal.ofReal_of_nonpos hn, ENNReal.ofReal_zero]
  have hLC := lintegral_eq_lintegral_meas_lt (μ.restrict A)
    (Eventually.of_forall fun ζ ↦ (le_max_right _ _ : (0 : ℝ) ≤ f ζ)) hfmeas.aemeasurable
  simp_rw [hofReal]
  rw [hLC]
  -- step 2: for `t > 0` the level set is `S_t = {t + ε < h} ∩ A`
  have hSmeas : ∀ t : ℝ, MeasurableSet {ζ | t < f ζ} := fun t ↦
    measurableSet_lt measurable_const hfmeas
  have hset : ∀ t : ℝ, 0 < t → (μ.restrict A) {ζ | t < f ζ} = μ ({ζ | t + ε < h ζ} ∩ A) := by
    intro t ht
    rw [Measure.restrict_apply (hSmeas t)]
    congr 1
    ext ζ
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, hf, lt_max_iff]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact ⟨by linarith, h2⟩
      · exact absurd h1 (not_lt.2 ht.le)
    · rintro ⟨h1, h2⟩
      exact ⟨Or.inl (by linarith), h2⟩
  -- step 3: `κ μ(S_t) ≤ ∫_{S_t} I_t ≤ ∫_A I_t = ∫_B φ(t, ·) G ∫_A k ≤ L ∫_B φ(t, ·) G` (Tonelli)
  have hFmeas : ∀ t : ℝ, Measurable fun ζ ↦ ∫⁻ x in B, φ t x * G x * k x ζ ∂μ := by
    intro t
    have : Measurable fun p : X × X ↦ φ t p.2 * G p.2 * k p.2 p.1 :=
      ((hφ.comp (measurable_const.prodMk measurable_snd)).mul (hG.comp measurable_snd)).mul
        (hk.comp (measurable_snd.prodMk measurable_fst))
    exact this.lintegral_prod_right'
  have hinner : ∀ t : ℝ, 0 < t →
      κ * (μ.restrict A) {ζ | t < f ζ} ≤ L * ∫⁻ x in B, φ t x * G x ∂μ := by
    intro t ht
    rw [hset t ht]
    calc κ * μ ({ζ | t + ε < h ζ} ∩ A) = ∫⁻ ζ in {ζ | t + ε < h ζ} ∩ A, κ ∂μ := by
          rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ ζ in {ζ | t + ε < h ζ} ∩ A, ∫⁻ x in B, φ t x * G x * k x ζ ∂μ ∂μ := by
          refine setLIntegral_mono_ae (hFmeas t).aemeasurable ?_
          filter_upwards [hiii t ht] with ζ hζ hmem
          exact hζ hmem.2 hmem.1
      _ ≤ ∫⁻ ζ in A, ∫⁻ x in B, φ t x * G x * k x ζ ∂μ ∂μ :=
          lintegral_mono_set Set.inter_subset_right
      _ = ∫⁻ x in B, ∫⁻ ζ in A, φ t x * G x * k x ζ ∂μ ∂μ := by
          rw [lintegral_lintegral_swap]
          exact (((hφ.comp (measurable_const.prodMk measurable_snd)).mul
            (hG.comp measurable_snd)).mul (hk.comp (measurable_snd.prodMk measurable_fst))).aemeasurable
      _ = ∫⁻ x in B, φ t x * G x * ∫⁻ ζ in A, k x ζ ∂μ ∂μ := by
          refine lintegral_congr fun x ↦ ?_
          rw [lintegral_const_mul]
          exact hk.comp (measurable_const.prodMk measurable_id)
      _ ≤ ∫⁻ x in B, φ t x * G x * L ∂μ := by
          refine setLIntegral_mono' hB fun x hx ↦ ?_
          gcongr
          exact hii x hx
      _ = L * ∫⁻ x in B, φ t x * G x ∂μ := by
          rw [lintegral_mul_const, mul_comm]
          exact (hφ.comp (measurable_const.prodMk measurable_id)).mul hG
  -- step 4: integrate in `t`; `t ↦ μ(A ∩ {f > t})` is antitone, hence measurable
  have hanti : Antitone fun t : ℝ ↦ (μ.restrict A) {ζ | t < f ζ} := by
    intro s t hst
    exact measure_mono fun ζ hζ ↦ lt_of_le_of_lt hst hζ
  have hPmeas : Measurable fun t : ℝ ↦ ∫⁻ x in B, φ t x * G x ∂μ := by
    have : Measurable fun p : ℝ × X ↦ φ p.1 p.2 * G p.2 := hφ.mul (hG.comp measurable_snd)
    exact this.lintegral_prod_right'
  -- step 5: Tonelli in `(t, x)` and `∫_0^∞ φ(t, x) dt ≤ 1` on `B`
  calc κ * ∫⁻ t in Ioi 0, (μ.restrict A) {ζ | t < f ζ}
      = ∫⁻ t in Ioi 0, κ * (μ.restrict A) {ζ | t < f ζ} := by
        rw [lintegral_const_mul _ hanti.measurable]
    _ ≤ ∫⁻ t in Ioi 0, L * ∫⁻ x in B, φ t x * G x ∂μ :=
        setLIntegral_mono' measurableSet_Ioi fun t ht ↦ hinner t ht
    _ = L * ∫⁻ t in Ioi 0, ∫⁻ x in B, φ t x * G x ∂μ := by
        rw [lintegral_const_mul _ hPmeas]
    _ = L * ∫⁻ x in B, (∫⁻ t in Ioi 0, φ t x * G x) ∂μ := by
        rw [lintegral_lintegral_swap]
        exact (hφ.mul (hG.comp measurable_snd)).aemeasurable
    _ = L * ∫⁻ x in B, (∫⁻ t in Ioi 0, φ t x) * G x ∂μ := by
        congr 1
        refine lintegral_congr fun x ↦ ?_
        rw [lintegral_mul_const]
        exact hφ.comp (measurable_id.prodMk measurable_const)
    _ ≤ L * ∫⁻ x in B, G x ∂μ := by
        gcongr L * ?_
        refine setLIntegral_mono' hB fun x hx ↦ ?_
        calc (∫⁻ t in Ioi 0, φ t x) * G x ≤ 1 * G x := by gcongr; exact hi x hx
          _ = G x := one_mul _

/-- **Simon Ch. 4, 5.4 in Gronwall form (bounded mean curvature).** Assume the weighted
monotonicity identity (WMI) as a hypothesis. If `μ_V` is finite on compacts, `T_x V` is
`n`-dimensional `μ_V`-a.e. with `x ↦ p_{T_x V}` `μ_V`-a.e. strongly measurable, `V` has generalized
mean curvature `H` in the open set `U` with `|H| ≤ Λ`, `g ∈ C¹(U)`, `g ≥ 0`, `B_r(y) ⊆ U`,
`0 < s ≤ r` and `|∇^M g| |x - y|^{1-n}` is `μ_V`-integrable on `B_r(y)`, then
`s⁻ⁿ ∫_{B_s(y)} g dμ_V ≤ e^{Λ(r-s)} (r⁻ⁿ ∫_{B_r(y)} g dμ_V +
n⁻¹ ∫_{B_r(y)} |∇^M g| |x - y|^{1-n} dμ_V)` (the printed factor is the weaker `e^{Λρ}`).
Put `f(τ) = τ⁻ⁿ ∫_{B_τ(y)} g dμ_V`. By (WMI), `|H| ≤ Λ` and Cauchy–Schwarz,
`f(σ) ≤ f(r) + P + Λ ∫_{(σ,r]} f` for `σ ∈ [s, r]`, where
`P = ∫_{(s,r]} τ^{-n-1} ∫_{B_τ(y)} |x - y| |∇^M g| dμ_V dτ`. The backward integral Gronwall
inequality then gives `f(s) ≤ (f(r) + P) e^{Λ(r-s)}`. By Tonelli and
`∫_d^∞ τ^{-n-1} dτ = d^{-n}/n`, `P ≤ n⁻¹ ∫_{B_r(y)} |∇^M g| |x - y|^{1-n} dμ_V`. -/
theorem Submission.bounded_curvature_ball_average_estimate : (∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)) (H : Ambient n ℓ → Ambient n ℓ) (h : Ambient n ℓ → ℝ) (ξ : Ambient n ℓ) (σ ρ : ℝ), 0 < n → IsFiniteMeasureOnCompacts V.weight → (∀ᵐ x ∂V.weight, Module.finrank ℝ (V.tangentSpace x) = n) → AEStronglyMeasurable (fun x ↦ (V.tangentSpace x).starProjection) V.weight → IsOpen U → V.HasMeanCurvatureIn U H → ContDiffOn ℝ 1 h U → tsupport h ∩ closedBall ξ ρ ⊆ U → 0 < σ → σ ≤ ρ → IntegrableOn (fun τ ↦ (∫ x in closedBall ξ τ, inner ℝ (x - ξ) (V.tangentialGradient h x + h x • H x) ∂V.weight) / τ ^ (n + 1)) (Ioc σ ρ) ∧ IntegrableOn (fun x ↦ h x * (V.normalRadialSq ξ x / ‖x - ξ‖ ^ n)) (closedBall ξ ρ \ closedBall ξ σ) V.weight ∧ (∫ x in closedBall ξ ρ, h x ∂V.weight) / ρ ^ n - (∫ x in closedBall ξ σ, h x ∂V.weight) / σ ^ n = ∫ x in closedBall ξ ρ \ closedBall ξ σ, h x * (V.normalRadialSq ξ x / ‖x - ξ‖ ^ n) ∂V.weight + ∫ τ in Ioc σ ρ, (∫ x in closedBall ξ τ, inner ℝ (x - ξ) (V.tangentialGradient h x + h x • H x) ∂V.weight) / τ ^ (n + 1)) → ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)) (H : Ambient n ℓ → Ambient n ℓ) (Λ : ℝ) (g : Ambient n ℓ → ℝ) (y : Ambient n ℓ) (r s : ℝ), 0 < n → IsFiniteMeasureOnCompacts V.weight → (∀ᵐ x ∂V.weight, Module.finrank ℝ (V.tangentSpace x) = n) → AEStronglyMeasurable (fun x ↦ (V.tangentSpace x).starProjection) V.weight → IsOpen U → V.HasMeanCurvatureIn U H → 0 ≤ Λ → (∀ᵐ x ∂V.weight, x ∈ U → ‖H x‖ ≤ Λ) → ContDiffOn ℝ 1 g U → (∀ x ∈ U, 0 ≤ g x) → closedBall y r ⊆ U → 0 < s → s ≤ r → IntegrableOn (fun x ↦ ‖V.tangentialGradient g x‖ * ‖x - y‖ ^ (1 - (n : ℝ))) (closedBall y r) V.weight → (∫ x in closedBall y s, g x ∂V.weight) / s ^ n ≤ Real.exp (Λ * (r - s)) * ((∫ x in closedBall y r, g x ∂V.weight) / r ^ n + (n : ℝ)⁻¹ * ∫ x in closedBall y r, ‖V.tangentialGradient g x‖ * ‖x - y‖ ^ (1 - (n : ℝ)) ∂V.weight) := by
  intro hWMI n ℓ V U H Λ g y r s hn hFV1 hFV2 hFV3 hU hH hΛ hHΛ hg hg0 hball hs hsr hint
  have := hFV1
  set μ := V.weight with hμ
  have hr : 0 < r := hs.trans_le hsr
  have hgcont : ContinuousOn g U := hg.continuousOn
  -- Step 1: bounds and integrability on the closed balls `B_τ(y)`, `τ ≤ r`
  obtain ⟨Cg0, hCg0⟩ : ∃ C, ∀ x ∈ closedBall y r, ‖g x‖ ≤ C :=
    (isCompact_closedBall y r).exists_bound_of_continuousOn (hgcont.mono hball)
  have hgradcont : ContinuousOn (gradient g) U :=
    (InnerProductSpace.toDual ℝ (Ambient n ℓ)).symm.continuous.comp_continuousOn
      (hg.continuousOn_fderiv_of_isOpen hU le_rfl)
  obtain ⟨Cg1, hCg1⟩ : ∃ C, ∀ x ∈ closedBall y r, ‖gradient g x‖ ≤ C :=
    (isCompact_closedBall y r).exists_bound_of_continuousOn (hgradcont.mono hball)
  have hTGbound : ∀ x ∈ closedBall y r, ‖V.tangentialGradient g x‖ ≤ Cg1 := fun x hx =>
    (Submodule.norm_starProjection_apply_le _ _).trans (hCg1 x hx)
  have hTGmeas : AEStronglyMeasurable (V.tangentialGradient g) μ := by
    have hgm : Measurable (gradient g) :=
      (InnerProductSpace.toDual ℝ (Ambient n ℓ)).symm.continuous.measurable.comp
        (measurable_fderiv ℝ g)
    exact (ContinuousLinearMap.id ℝ (Ambient n ℓ →L[ℝ] Ambient n ℓ)).aestronglyMeasurable_comp₂
      hFV3 hgm.aestronglyMeasurable
  have hfinB : ∀ τ : ℝ, IsFiniteMeasure (μ.restrict (closedBall y τ)) := fun τ => ⟨by
    rw [Measure.restrict_apply_univ]; exact (isCompact_closedBall y τ).measure_lt_top⟩
  have hsubB : ∀ τ ≤ r, closedBall y τ ⊆ closedBall y r := fun τ hτ =>
    closedBall_subset_closedBall hτ
  have hgint : ∀ τ ≤ r, IntegrableOn g (closedBall y τ) μ := fun τ hτ =>
    (hgcont.mono ((hsubB τ hτ).trans hball)).integrableOn_compact (isCompact_closedBall y τ)
  have hFint : ∀ τ ≤ r,
      IntegrableOn (fun x => ‖x - y‖ * ‖V.tangentialGradient g x‖) (closedBall y τ) μ := by
    intro τ hτ
    have := hfinB τ
    refine Integrable.of_bound (C := r * Cg1)
      (((continuous_id.sub continuous_const).norm.aestronglyMeasurable).mul
        hTGmeas.norm).restrict ?_
    refine (ae_restrict_iff' measurableSet_closedBall).2 (Eventually.of_forall fun x hx => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    have h1 : ‖x - y‖ ≤ r := by rw [← dist_eq_norm]; exact (mem_closedBall.1 hx).trans hτ
    exact mul_le_mul h1 (hTGbound x (hsubB τ hτ hx)) (norm_nonneg _) hr.le
  have hHint : IntegrableOn H (closedBall y r) μ :=
    hH.1.integrableOn_compact_subset hball (isCompact_closedBall y r)
  have hsubm : AEStronglyMeasurable (fun x : Ambient n ℓ => x - y) μ :=
    (continuous_sub_right y).aestronglyMeasurable
  have hQint : ∀ τ ≤ r, IntegrableOn
      (fun x => inner ℝ (x - y) (V.tangentialGradient g x + g x • H x)) (closedBall y τ) μ := by
    intro τ hτ
    have := hfinB τ
    have h1 : IntegrableOn (fun x => inner ℝ (x - y) (V.tangentialGradient g x))
        (closedBall y τ) μ := by
      refine Integrable.of_bound (C := r * Cg1) ?_ ?_
      · exact (continuous_inner.comp_aestronglyMeasurable₂ hsubm hTGmeas).restrict
      · refine (ae_restrict_iff' measurableSet_closedBall).2 (Eventually.of_forall fun x hx => ?_)
        refine (norm_inner_le_norm _ _).trans ?_
        have h1 : ‖x - y‖ ≤ r := by rw [← dist_eq_norm]; exact (mem_closedBall.1 hx).trans hτ
        exact mul_le_mul h1 (hTGbound x (hsubB τ hτ hx)) (norm_nonneg _) hr.le
    have hHτ : IntegrableOn (fun x => inner ℝ (x - y) (H x)) (closedBall y τ) μ := by
      have hH' := hHint.mono_set (hsubB τ hτ)
      refine (hH'.norm.const_mul r).mono'
        (continuous_inner.comp_aestronglyMeasurable₂ hsubm.restrict hH'.aestronglyMeasurable) ?_
      refine (ae_restrict_iff' measurableSet_closedBall).2 (Eventually.of_forall fun x hx => ?_)
      refine (norm_inner_le_norm _ _).trans ?_
      have h1 : ‖x - y‖ ≤ r := by rw [← dist_eq_norm]; exact (mem_closedBall.1 hx).trans hτ
      exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    have h2 : IntegrableOn (fun x => g x * inner ℝ (x - y) (H x)) (closedBall y τ) μ := by
      refine Integrable.bdd_mul (c := Cg0) hHτ ?_ ?_
      · exact (hgcont.mono ((hsubB τ hτ).trans hball)).aestronglyMeasurable
          measurableSet_closedBall
      · exact (ae_restrict_iff' measurableSet_closedBall).2 (Eventually.of_forall fun x hx =>
          hCg0 x (hsubB τ hτ hx))
    refine (h1.add h2).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, inner_add_right, inner_smul_right]
  -- Step 2: the radial functions `f(τ) = τ⁻ⁿ ∫_{B_τ} g` and `R(τ) = τ⁻ⁿ⁻¹ ∫_{B_τ} |x - y| |∇^M g|`
  -- are integrable on `[s, r]` (bounded, and monotone numerators)
  set f : ℝ → ℝ := fun τ => (∫ x in closedBall y τ, g x ∂μ) / τ ^ n with hf
  set R : ℝ → ℝ := fun τ =>
    (∫ x in closedBall y τ, ‖x - y‖ * ‖V.tangentialGradient g x‖ ∂μ) / τ ^ (n + 1) with hR
  have hg0B : ∀ x ∈ closedBall y r, 0 ≤ g x := fun x hx => hg0 x (hball hx)
  have hmonog : MonotoneOn (fun τ => ∫ x in closedBall y τ, g x ∂μ) (Icc s r) := by
    intro a ha b hb hab
    exact setIntegral_mono_set (hgint b hb.2)
      ((ae_restrict_iff' measurableSet_closedBall).2 (Eventually.of_forall fun x hx =>
        hg0B x (hsubB b hb.2 hx)))
      (Eventually.of_forall (closedBall_subset_closedBall hab))
  have hmonoF : MonotoneOn
      (fun τ => ∫ x in closedBall y τ, ‖x - y‖ * ‖V.tangentialGradient g x‖ ∂μ) (Icc s r) := by
    intro a ha b hb hab
    exact setIntegral_mono_set (hFint b hb.2)
      (Eventually.of_forall fun x => by positivity)
      (Eventually.of_forall (closedBall_subset_closedBall hab))
  have : IsFiniteMeasure (volume.restrict (Icc s r)) := ⟨by
    rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  have hfint : IntegrableOn f (Icc s r) := by
    refine Integrable.of_bound (C := (∫ x in closedBall y r, g x ∂μ) / s ^ n) ?_ ?_
    · exact ((aemeasurable_restrict_of_monotoneOn measurableSet_Icc hmonog).div
        (continuous_pow n).aemeasurable).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun τ hτ => ?_)
      have hτ0 : 0 < τ := hs.trans_le hτ.1
      have hI0 : 0 ≤ ∫ x in closedBall y τ, g x ∂μ :=
        setIntegral_nonneg measurableSet_closedBall fun x hx => hg0B x (hsubB τ hτ.2 hx)
      rw [Real.norm_of_nonneg (div_nonneg hI0 (pow_pos hτ0 n).le)]
      calc (∫ x in closedBall y τ, g x ∂μ) / τ ^ n ≤ (∫ x in closedBall y r, g x ∂μ) / τ ^ n :=
            div_le_div_of_nonneg_right (hmonog hτ ⟨hsr, le_rfl⟩ hτ.2) (pow_pos hτ0 n).le
        _ ≤ (∫ x in closedBall y r, g x ∂μ) / s ^ n :=
            div_le_div_of_nonneg_left (setIntegral_nonneg measurableSet_closedBall hg0B)
              (pow_pos hs n) (pow_le_pow_left₀ hs.le hτ.1 n)
  have hRint : IntegrableOn R (Icc s r) := by
    refine Integrable.of_bound
      (C := (∫ x in closedBall y r, ‖x - y‖ * ‖V.tangentialGradient g x‖ ∂μ) / s ^ (n + 1)) ?_ ?_
    · exact ((aemeasurable_restrict_of_monotoneOn measurableSet_Icc hmonoF).div
        (continuous_pow (n + 1)).aemeasurable).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun τ hτ => ?_)
      have hτ0 : 0 < τ := hs.trans_le hτ.1
      have hI0 : 0 ≤ ∫ x in closedBall y τ, ‖x - y‖ * ‖V.tangentialGradient g x‖ ∂μ :=
        setIntegral_nonneg measurableSet_closedBall fun x _ => by positivity
      rw [Real.norm_of_nonneg (div_nonneg hI0 (pow_pos hτ0 _).le)]
      calc (∫ x in closedBall y τ, ‖x - y‖ * ‖V.tangentialGradient g x‖ ∂μ) / τ ^ (n + 1)
          ≤ (∫ x in closedBall y r, ‖x - y‖ * ‖V.tangentialGradient g x‖ ∂μ) / τ ^ (n + 1) :=
            div_le_div_of_nonneg_right (hmonoF hτ ⟨hsr, le_rfl⟩ hτ.2) (pow_pos hτ0 _).le
        _ ≤ (∫ x in closedBall y r, ‖x - y‖ * ‖V.tangentialGradient g x‖ ∂μ) / s ^ (n + 1) :=
            div_le_div_of_nonneg_left
              (setIntegral_nonneg measurableSet_closedBall fun x _ => by positivity)
              (pow_pos hs _) (pow_le_pow_left₀ hs.le hτ.1 _)
  have hR0 : ∀ τ, 0 < τ → 0 ≤ R τ := fun τ hτ =>
    div_nonneg (integral_nonneg fun x => by positivity) (pow_pos hτ _).le
  set P := ∫ τ in Ioc s r, R τ with hP
  -- Step 3: by (WMI) at radii `σ ≤ r`, `|H| ≤ Λ` and Cauchy–Schwarz,
  -- `f(σ) ≤ f(r) + P + Λ ∫_{(σ,r]} f` for every `σ ∈ [s, r]`
  have hstepA : ∀ σ ∈ Icc s r, f σ ≤ (f r + P) + Λ * ∫ τ in Ioc σ r, f τ := by
    intro σ hσ
    have hσ0 : 0 < σ := hs.trans_le hσ.1
    obtain ⟨hQi, -, hid⟩ := hWMI n ℓ V U H g y σ r hn hFV1 hFV2 hFV3 hU hH hg
      (fun x hx => hball hx.2) hσ0 hσ.2
    have hW0 : 0 ≤ ∫ x in closedBall y r \ closedBall y σ,
        g x * (V.normalRadialSq y x / ‖x - y‖ ^ n) ∂μ := by
      refine setIntegral_nonneg (measurableSet_closedBall.diff measurableSet_closedBall)
        fun x hx => ?_
      have : 0 ≤ V.normalRadialSq y x := by unfold RectifiableVarifold.normalRadialSq; positivity
      exact mul_nonneg (hg0B x hx.1) (div_nonneg this (by positivity))
    have hQlow : ∀ τ ∈ Ioc σ r, -R τ - Λ * f τ ≤
        (∫ x in closedBall y τ, inner ℝ (x - y) (V.tangentialGradient g x + g x • H x) ∂μ) /
          τ ^ (n + 1) := by
      intro τ hτ
      have hτ0 : 0 < τ := hσ0.trans hτ.1
      have hτr : τ ≤ r := hτ.2
      have hint1 : ∫ x in closedBall y τ,
            (-(‖x - y‖ * ‖V.tangentialGradient g x‖) - τ * Λ * g x) ∂μ ≤
          ∫ x in closedBall y τ, inner ℝ (x - y) (V.tangentialGradient g x + g x • H x) ∂μ := by
        refine integral_mono_ae ((hFint τ hτr).neg.sub ((hgint τ hτr).const_mul (τ * Λ)))
          (hQint τ hτr) ?_
        filter_upwards [ae_restrict_mem measurableSet_closedBall, ae_restrict_of_ae hHΛ]
          with x hx hHx
        have hxU : x ∈ U := hball (hsubB τ hτr hx)
        have hgx : 0 ≤ g x := hg0 x hxU
        have hxy : ‖x - y‖ ≤ τ := by rw [← dist_eq_norm]; exact mem_closedBall.1 hx
        have hH1 : ‖H x‖ ≤ Λ := hHx hxU
        have i1 : -(‖x - y‖ * ‖V.tangentialGradient g x‖) ≤
            inner ℝ (x - y) (V.tangentialGradient g x) :=
          neg_le_of_abs_le (abs_real_inner_le_norm _ _)
        have i2 : -(‖x - y‖ * ‖H x‖) ≤ inner ℝ (x - y) (H x) :=
          neg_le_of_abs_le (abs_real_inner_le_norm _ _)
        have i3 : ‖x - y‖ * ‖H x‖ ≤ τ * Λ := mul_le_mul hxy hH1 (norm_nonneg _) hτ0.le
        simp only [inner_add_right, inner_smul_right]
        nlinarith [mul_le_mul_of_nonneg_left i3 hgx, mul_le_mul_of_nonneg_left i2 hgx]
      have heq : ∫ x in closedBall y τ,
            (-(‖x - y‖ * ‖V.tangentialGradient g x‖) - τ * Λ * g x) ∂μ =
          -(∫ x in closedBall y τ, ‖x - y‖ * ‖V.tangentialGradient g x‖ ∂μ) -
            τ * Λ * ∫ x in closedBall y τ, g x ∂μ := by
        rw [integral_sub (f := fun x => -(‖x - y‖ * ‖V.tangentialGradient g x‖))
          (g := fun x => τ * Λ * g x) (hFint τ hτr).neg ((hgint τ hτr).const_mul (τ * Λ)),
          integral_neg, integral_const_mul]
      rw [heq] at hint1
      have hpos : (0 : ℝ) < τ ^ (n + 1) := pow_pos hτ0 _
      have hfτ : f τ = (∫ x in closedBall y τ, g x ∂μ) / τ ^ n := rfl
      have hRτ : R τ =
          (∫ x in closedBall y τ, ‖x - y‖ * ‖V.tangentialGradient g x‖ ∂μ) / τ ^ (n + 1) := rfl
      rw [hfτ, hRτ, le_div_iff₀ hpos]
      have hexp : τ ^ (n + 1) = τ ^ n * τ := pow_succ τ n
      have hτn : (0 : ℝ) < τ ^ n := pow_pos hτ0 n
      calc (-((∫ x in closedBall y τ, ‖x - y‖ * ‖V.tangentialGradient g x‖ ∂μ) / τ ^ (n + 1)) -
            Λ * ((∫ x in closedBall y τ, g x ∂μ) / τ ^ n)) * τ ^ (n + 1)
          = -(∫ x in closedBall y τ, ‖x - y‖ * ‖V.tangentialGradient g x‖ ∂μ) -
            τ * Λ * ∫ x in closedBall y τ, g x ∂μ := by
            rw [hexp]; field_simp
        _ ≤ _ := hint1
    have hT : -(∫ τ in Ioc σ r, R τ) - Λ * ∫ τ in Ioc σ r, f τ ≤
        ∫ τ in Ioc σ r, (∫ x in closedBall y τ,
          inner ℝ (x - y) (V.tangentialGradient g x + g x • H x) ∂μ) / τ ^ (n + 1) := by
      have hsubI : Ioc σ r ⊆ Icc s r := fun τ hτ => ⟨hσ.1.trans hτ.1.le, hτ.2⟩
      have hRi := hRint.mono_set hsubI
      have hfi := hfint.mono_set hsubI
      rw [← integral_neg, ← integral_const_mul, ← integral_sub (f := fun τ => -R τ)
        (g := fun τ => Λ * f τ) hRi.neg (hfi.const_mul Λ)]
      exact setIntegral_mono_on (hRi.neg.sub (hfi.const_mul Λ)) hQi measurableSet_Ioc hQlow
    have hRle : ∫ τ in Ioc σ r, R τ ≤ P := by
      refine setIntegral_mono_set (hRint.mono_set Ioc_subset_Icc_self) ?_ ?_
      · exact (ae_restrict_iff' measurableSet_Ioc).2
          (Eventually.of_forall fun τ hτ => hR0 τ (hs.trans hτ.1))
      · exact Eventually.of_forall (Ioc_subset_Ioc_left hσ.1)
    have hfr : f r = (∫ x in closedBall y r, g x ∂μ) / r ^ n := rfl
    have hfσ : f σ = (∫ x in closedBall y σ, g x ∂μ) / σ ^ n := rfl
    rw [hfσ, hfr]
    rw [hfr] at *
    linarith
  -- Step 4: the sibling backward integral Gronwall inequality gives `f(s) ≤ (f(r) + P) e^{Λ(r-s)}`
  have hB := Submission.backward_integral_gronwall_Ioc s r Λ (f r + P) f hsr hΛ hfint hstepA s
    ⟨le_rfl, hsr⟩
  -- Step 5: by Tonelli and `∫_d^∞ τ^{-n-1} dτ = d^{-n}/n`, `P ≤ n⁻¹ ∫_{B_r} |∇^M g| |x - y|^{1-n}`
  set Kg := ∫ x in closedBall y r, ‖V.tangentialGradient g x‖ * ‖x - y‖ ^ (1 - (n : ℝ)) ∂μ
    with hKg
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hKg0 : 0 ≤ Kg := setIntegral_nonneg measurableSet_closedBall fun x _ => by positivity
  have hstepC : P ≤ (n : ℝ)⁻¹ * Kg := by
    set Fe : Ambient n ℓ → ℝ≥0∞ := fun x => ENNReal.ofReal (‖x - y‖ * ‖V.tangentialGradient g x‖)
      with hFe
    have hFeae : AEMeasurable Fe μ :=
      ENNReal.measurable_ofReal.comp_aemeasurable ((hsubm.norm.mul hTGmeas.norm).aemeasurable)
    have h1 : ENNReal.ofReal P = ∫⁻ τ in Ioc s r, ENNReal.ofReal (R τ) :=
      ofReal_integral_eq_lintegral_ofReal (hRint.mono_set Ioc_subset_Icc_self)
        ((ae_restrict_iff' measurableSet_Ioc).2
          (Eventually.of_forall fun τ hτ => hR0 τ (hs.trans hτ.1)))
    have h2 : ∀ τ ∈ Ioc s r, ENNReal.ofReal (R τ) = ∫⁻ x in closedBall y r,
        ENNReal.ofReal (τ ^ (-(n : ℝ) - 1)) * (closedBall y τ).indicator Fe x ∂μ := by
      intro τ hτ
      have hτ0 : 0 < τ := hs.trans hτ.1
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_indicator measurableSet_closedBall,
        Measure.restrict_restrict measurableSet_closedBall, Set.inter_eq_left.2 (hsubB τ hτ.2),
        ← ofReal_integral_eq_lintegral_ofReal (hFint τ hτ.2)
          (Eventually.of_forall fun x => by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      have : τ ^ (-(n : ℝ) - 1) = (τ ^ (n + 1))⁻¹ := by
        rw [show -(n : ℝ) - 1 = -((n + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_neg hτ0.le,
          Real.rpow_natCast]
      rw [this, hR]
      simp only
      rw [div_eq_inv_mul]
    have hmeasP : MeasurableSet {p : ℝ × Ambient n ℓ | dist p.2 y ≤ p.1} :=
      measurableSet_le (by fun_prop) measurable_fst
    have h3 : ∫⁻ τ in Ioc s r, ∫⁻ x in closedBall y r,
        ENNReal.ofReal (τ ^ (-(n : ℝ) - 1)) * (closedBall y τ).indicator Fe x ∂μ =
        ∫⁻ x in closedBall y r, (∫⁻ τ in Ioc s r,
          ENNReal.ofReal (τ ^ (-(n : ℝ) - 1)) * (closedBall y τ).indicator Fe x) ∂μ := by
      refine lintegral_lintegral_swap ?_
      have heq : Function.uncurry (fun (τ : ℝ) (x : Ambient n ℓ) =>
          ENNReal.ofReal (τ ^ (-(n : ℝ) - 1)) * (closedBall y τ).indicator Fe x) =
          fun p : ℝ × Ambient n ℓ => ENNReal.ofReal (p.1 ^ (-(n : ℝ) - 1)) *
            {p : ℝ × Ambient n ℓ | dist p.2 y ≤ p.1}.indicator (fun p => Fe p.2) p := by
        ext ⟨τ, x⟩
        simp only [Function.uncurry_apply_pair, Set.indicator, mem_closedBall, Set.mem_ofPred_eq]
      rw [heq]
      refine (ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)).aemeasurable.mul ?_
      exact (hFeae.restrict.comp_snd).indicator hmeasP
    have h4 : ∀ x ∈ closedBall y r, (∫⁻ τ in Ioc s r,
        ENNReal.ofReal (τ ^ (-(n : ℝ) - 1)) * (closedBall y τ).indicator Fe x) ≤
        ENNReal.ofReal ((n : ℝ)⁻¹ * (‖V.tangentialGradient g x‖ * ‖x - y‖ ^ (1 - (n : ℝ)))) := by
      intro x hx
      by_cases hd : ‖x - y‖ = 0
      · have hFe0 : Fe x = 0 := by simp only [hFe, hd, zero_mul, ENNReal.ofReal_zero]
        have : ∀ τ, ENNReal.ofReal (τ ^ (-(n : ℝ) - 1)) * (closedBall y τ).indicator Fe x = 0 := by
          intro τ
          by_cases hm : x ∈ closedBall y τ
          · rw [Set.indicator_of_mem hm, hFe0, mul_zero]
          · rw [Set.indicator_of_notMem hm, mul_zero]
        simp only [this, lintegral_zero]
        exact bot_le
      · have hdpos : 0 < ‖x - y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd)
        have hpt : ∀ τ, ENNReal.ofReal (τ ^ (-(n : ℝ) - 1)) * (closedBall y τ).indicator Fe x =
            (Ici ‖x - y‖).indicator (fun τ => ENNReal.ofReal (τ ^ (-(n : ℝ) - 1)) * Fe x) τ := by
          intro τ
          by_cases hm : x ∈ closedBall y τ
          · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (by
              rw [mem_closedBall, dist_eq_norm] at hm; exact hm)]
          · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (by
              rw [mem_closedBall, dist_eq_norm] at hm; simpa using hm), mul_zero]
        have hexp : -(n : ℝ) - 1 < -1 := by linarith
        calc ∫⁻ τ in Ioc s r, ENNReal.ofReal (τ ^ (-(n : ℝ) - 1)) * (closedBall y τ).indicator Fe x
            ≤ ∫⁻ τ, ENNReal.ofReal (τ ^ (-(n : ℝ) - 1)) * (closedBall y τ).indicator Fe x :=
              setLIntegral_le_lintegral _ _
          _ = ∫⁻ τ in Ici ‖x - y‖, ENNReal.ofReal (τ ^ (-(n : ℝ) - 1)) * Fe x := by
              simp_rw [hpt]
              rw [lintegral_indicator measurableSet_Ici]
          _ = ∫⁻ τ in Ioi ‖x - y‖, ENNReal.ofReal (τ ^ (-(n : ℝ) - 1)) * Fe x :=
              setLIntegral_congr Ioi_ae_eq_Ici.symm
          _ = ENNReal.ofReal (∫ τ in Ioi ‖x - y‖, τ ^ (-(n : ℝ) - 1)) * Fe x := by
              rw [lintegral_mul_const' _ _ (by simp only [hFe]; exact ENNReal.ofReal_ne_top),
                ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt hexp hdpos)]
              filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
              exact Real.rpow_nonneg (hdpos.trans hτ).le _
          _ = ENNReal.ofReal
                ((n : ℝ)⁻¹ * (‖V.tangentialGradient g x‖ * ‖x - y‖ ^ (1 - (n : ℝ)))) := by
              rw [integral_Ioi_rpow_of_lt hexp hdpos, hFe]
              simp only
              rw [← ENNReal.ofReal_mul (by
                have : -(n : ℝ) - 1 + 1 = -(n : ℝ) := by ring
                rw [this, neg_div_neg_eq]
                positivity)]
              congr 1
              have h1 : -(n : ℝ) - 1 + 1 = -(n : ℝ) := by ring
              rw [h1]
              have h2 : ‖x - y‖ ^ (1 - (n : ℝ)) = ‖x - y‖ * ‖x - y‖ ^ (-(n : ℝ)) := by
                rw [show (1 : ℝ) - n = 1 + (-(n : ℝ)) by ring, Real.rpow_add hdpos, Real.rpow_one]
              rw [h2]
              field_simp
    have h5 : ∫⁻ x in closedBall y r,
        ENNReal.ofReal ((n : ℝ)⁻¹ * (‖V.tangentialGradient g x‖ * ‖x - y‖ ^ (1 - (n : ℝ)))) ∂μ =
        ENNReal.ofReal ((n : ℝ)⁻¹ * Kg) := by
      rw [← ofReal_integral_eq_lintegral_ofReal (hint.const_mul _)
        (Eventually.of_forall fun x => by positivity), integral_const_mul]
    have hfinal : ENNReal.ofReal P ≤ ENNReal.ofReal ((n : ℝ)⁻¹ * Kg) := by
      rw [h1, setLIntegral_congr_fun measurableSet_Ioc h2, h3, ← h5]
      exact setLIntegral_mono' measurableSet_closedBall h4
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hfinal
  -- Step 6: combine
  have hfs : f s = (∫ x in closedBall y s, g x ∂μ) / s ^ n := rfl
  have hfr : f r = (∫ x in closedBall y r, g x ∂μ) / r ^ n := rfl
  rw [← hfs, ← hfr]
  calc f s ≤ (f r + P) * Real.exp (Λ * (r - s)) := hB
    _ ≤ (f r + (n : ℝ)⁻¹ * Kg) * Real.exp (Λ * (r - s)) := by gcongr
    _ = Real.exp (Λ * (r - s)) * (f r + (n : ℝ)⁻¹ * Kg) := mul_comm _ _

/-- **Mean value inequality at a point of density `≥ 1`** (Simon Ch. 4, the display after 5.5:
`σ ↓ 0` in 5.4). If `|H| ≤ Λ`, `g ∈ C¹(U)` is non-negative, `B_r(ζ) ⊆ U` and
`Θⁿ(μ_V, ζ) = θ₀ ≥ 1`, then
`ωₙ g(ζ) ≤ e^{Λr} (r⁻ⁿ ∫_{B_r(ζ)} g dμ_V + n⁻¹ ∫_{B_r(ζ)} |∇^M g| |x - ζ|^{1-n} dμ_V)`.
The ball-average estimate 5.4 bounds `s⁻ⁿ ∫_{B_s(ζ)} g dμ_V` by `e^{Λ(r-s)}` times the bracket
for `0 < s ≤ r`, and as `s ↓ 0` the left side tends to `ωₙ θ₀ g(ζ)` because `g` is continuous
at `ζ` and the density quotient `μ_V(B_s(ζ)) / (ωₙ sⁿ)` tends to `θ₀`. -/
theorem Submission.density_point_mean_value_estimate : (∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)) (H : Ambient n ℓ → Ambient n ℓ) (h : Ambient n ℓ → ℝ) (ξ : Ambient n ℓ) (σ ρ : ℝ), 0 < n → IsFiniteMeasureOnCompacts V.weight → (∀ᵐ x ∂V.weight, Module.finrank ℝ (V.tangentSpace x) = n) → AEStronglyMeasurable (fun x ↦ (V.tangentSpace x).starProjection) V.weight → IsOpen U → V.HasMeanCurvatureIn U H → ContDiffOn ℝ 1 h U → tsupport h ∩ closedBall ξ ρ ⊆ U → 0 < σ → σ ≤ ρ → IntegrableOn (fun τ ↦ (∫ x in closedBall ξ τ, inner ℝ (x - ξ) (V.tangentialGradient h x + h x • H x) ∂V.weight) / τ ^ (n + 1)) (Ioc σ ρ) ∧ IntegrableOn (fun x ↦ h x * (V.normalRadialSq ξ x / ‖x - ξ‖ ^ n)) (closedBall ξ ρ \ closedBall ξ σ) V.weight ∧ (∫ x in closedBall ξ ρ, h x ∂V.weight) / ρ ^ n - (∫ x in closedBall ξ σ, h x ∂V.weight) / σ ^ n = ∫ x in closedBall ξ ρ \ closedBall ξ σ, h x * (V.normalRadialSq ξ x / ‖x - ξ‖ ^ n) ∂V.weight + ∫ τ in Ioc σ ρ, (∫ x in closedBall ξ τ, inner ℝ (x - ξ) (V.tangentialGradient h x + h x • H x) ∂V.weight) / τ ^ (n + 1)) → ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)) (H : Ambient n ℓ → Ambient n ℓ) (Λ : ℝ) (g : Ambient n ℓ → ℝ) (ζ : Ambient n ℓ) (r θ₀ : ℝ), 0 < n → IsFiniteMeasureOnCompacts V.weight → (∀ᵐ x ∂V.weight, Module.finrank ℝ (V.tangentSpace x) = n) → AEStronglyMeasurable (fun x ↦ (V.tangentSpace x).starProjection) V.weight → IsOpen U → V.HasMeanCurvatureIn U H → 0 ≤ Λ → (∀ᵐ x ∂V.weight, x ∈ U → ‖H x‖ ≤ Λ) → ContDiffOn ℝ 1 g U → (∀ x ∈ U, 0 ≤ g x) → 0 < r → closedBall ζ r ⊆ U → V.HasDensityAt ζ θ₀ → 1 ≤ θ₀ → IntegrableOn (fun x ↦ ‖V.tangentialGradient g x‖ * ‖x - ζ‖ ^ (1 - (n : ℝ))) (closedBall ζ r) V.weight → omega n * g ζ ≤ Real.exp (Λ * r) * ((∫ x in closedBall ζ r, g x ∂V.weight) / r ^ n + (n : ℝ)⁻¹ * ∫ x in closedBall ζ r, ‖V.tangentialGradient g x‖ * ‖x - ζ‖ ^ (1 - (n : ℝ)) ∂V.weight) := by
  intro hWMI n ℓ V U H Λ g ζ r θ₀ hn hFV1 hFV2 hFV3 hU hH hΛ hHΛ hg hg0 hr hball hdens hθ hint
  set μ := V.weight
  -- the bracket `Q` on the right-hand side
  set Q := (∫ x in closedBall ζ r, g x ∂μ) / r ^ n + (n : ℝ)⁻¹ *
    ∫ x in closedBall ζ r, ‖V.tangentialGradient g x‖ * ‖x - ζ‖ ^ (1 - (n : ℝ)) ∂μ
  -- 1. `ζ ∈ U` and `ωₙ > 0`
  have hζU : ζ ∈ U := hball (mem_closedBall_self hr.le)
  have hω : 0 < omega n := by
    unfold omega
    exact ENNReal.toReal_pos (Metric.measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne
  -- 2. the ball-average estimate 5.4 at `y = ζ`: `F(s) ≤ e^{Λ(r-s)} Q` for `0 < s ≤ r`
  have hF : ∀ s : ℝ, 0 < s → s ≤ r →
      (∫ x in closedBall ζ s, g x ∂μ) / s ^ n ≤ Real.exp (Λ * (r - s)) * Q := fun s hs hsr =>
    Submission.bounded_curvature_ball_average_estimate hWMI n ℓ V U H Λ g ζ r s hn hFV1 hFV2 hFV3
      hU hH hΛ hHΛ hg hg0 hball hs hsr hint
  -- 3. `F(s) = g(ζ) ωₙ D(s) + E(s)`, where the density quotient `D(s)` tends to `θ₀`
  set D : ℝ → ℝ := fun s => μ.real (closedBall ζ s) / (omega n * s ^ n) with hD
  have hDlim : Tendsto D (𝓝[>] 0) (𝓝 θ₀) := hdens
  have hgcont : ContinuousAt g ζ := hg.continuousOn.continuousAt (hU.mem_nhds hζU)
  set E : ℝ → ℝ := fun s => (∫ x in closedBall ζ s, (g x - g ζ) ∂μ) / s ^ n with hE
  -- 4. `E(s) → 0`: on small balls `|g - g(ζ)| < η / (2K)` with `K = ωₙ(θ₀ + 1)`, and
  -- eventually `D(s) < θ₀ + 1`
  have hElim : Tendsto E (𝓝[>] 0) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro η hη
    set K := omega n * (θ₀ + 1) with hK
    have hKpos : 0 < K := by
      have : (0:ℝ) < θ₀ + 1 := by linarith
      positivity
    obtain ⟨δ, hδ, hδg⟩ := Metric.continuousAt_iff.1 hgcont (η / (2 * K)) (by positivity)
    have hD1 : ∀ᶠ s in 𝓝[>] (0:ℝ), D s < θ₀ + 1 := hDlim (Iio_mem_nhds (by linarith))
    have hsmall : ∀ᶠ s in 𝓝[>] (0:ℝ), s ∈ Ioo 0 (min δ r) :=
      Ioo_mem_nhdsGT (lt_min hδ hr)
    filter_upwards [hD1, hsmall] with s hDs hs
    have hs0 : 0 < s := hs.1
    have hsδ : s < δ := hs.2.trans_le (min_le_left _ _)
    have hsn : 0 < s ^ n := pow_pos hs0 n
    have hfin : μ (closedBall ζ s) < ⊤ := (isCompact_closedBall ζ s).measure_lt_top
    have hbound :
        ‖∫ x in closedBall ζ s, (g x - g ζ) ∂μ‖ ≤ η / (2 * K) * μ.real (closedBall ζ s) := by
      have := norm_setIntegral_le_of_norm_le_const hfin (C := η / (2 * K)) (f := fun x => g x - g ζ)
        (fun x hx => by
          have hxζ : dist x ζ < δ := lt_of_le_of_lt (mem_closedBall.1 hx) hsδ
          exact (le_of_lt (by simpa [Real.dist_eq] using hδg hxζ)))
      linarith [this]
    have hμs : μ.real (closedBall ζ s) = D s * (omega n * s ^ n) := by
      rw [hD]; field_simp
    rw [dist_zero_right, hE]
    simp only
    rw [norm_div, Real.norm_of_nonneg hsn.le, div_lt_iff₀ hsn]
    calc ‖∫ x in closedBall ζ s, (g x - g ζ) ∂μ‖
        ≤ η / (2 * K) * μ.real (closedBall ζ s) := hbound
      _ = η / (2 * K) * (D s * (omega n * s ^ n)) := by rw [hμs]
      _ ≤ η / (2 * K) * ((θ₀ + 1) * (omega n * s ^ n)) := by gcongr
      _ = η / 2 * s ^ n := by rw [hK]; field_simp
      _ < η * s ^ n := by nlinarith
  -- 5. hence `F(s) → g(ζ) ωₙ θ₀` and `e^{Λ(r-s)} Q → e^{Λr} Q` as `s ↓ 0`; step 2 passes to the
  -- limit
  have hFlim : Tendsto (fun s => (∫ x in closedBall ζ s, g x ∂μ) / s ^ n) (𝓝[>] 0)
      (𝓝 (g ζ * (omega n * θ₀) + 0)) := by
    have h1 : Tendsto (fun s => g ζ * (omega n * D s) + E s) (𝓝[>] 0)
        (𝓝 (g ζ * (omega n * θ₀) + 0)) :=
      ((hDlim.const_mul (omega n)).const_mul (g ζ)).add hElim
    refine h1.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hr] with s hs
    have hsn : 0 < s ^ n := pow_pos hs.1 n
    have hsub : closedBall ζ s ⊆ U := (closedBall_subset_closedBall hs.2.le).trans hball
    have hgint : IntegrableOn g (closedBall ζ s) μ :=
      (hg.continuousOn.mono hsub).integrableOn_compact (isCompact_closedBall ζ s)
    have hfin : μ (closedBall ζ s) ≠ ⊤ := (isCompact_closedBall ζ s).measure_lt_top.ne
    simp only [hD, hE]
    rw [integral_sub hgint (integrableOn_const hfin), setIntegral_const, smul_eq_mul]
    field_simp
    ring
  have hQlim : Tendsto (fun s => Real.exp (Λ * (r - s)) * Q) (𝓝[>] 0)
      (𝓝 (Real.exp (Λ * r) * Q)) := by
    have : Continuous fun s : ℝ => Real.exp (Λ * (r - s)) * Q := by fun_prop
    have h := this.tendsto 0
    simp only [sub_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hle : g ζ * (omega n * θ₀) + 0 ≤ Real.exp (Λ * r) * Q := by
    refine le_of_tendsto_of_tendsto hFlim hQlim ?_
    filter_upwards [Ioo_mem_nhdsGT hr] with s hs
    exact hF s hs.1 hs.2.le
  -- 6. `g(ζ) ≥ 0` and `θ₀ ≥ 1` give `ωₙ g(ζ) ≤ ωₙ θ₀ g(ζ)`
  have hgζ : 0 ≤ g ζ := hg0 ζ hζU
  calc omega n * g ζ ≤ g ζ * (omega n * θ₀) + 0 := by
        nlinarith [mul_nonneg (mul_nonneg hω.le hgζ) (sub_nonneg.2 hθ)]
    _ ≤ _ := hle
/-- **Chain rule for the tangential gradient** (Simon Ch. 4, 5.6, proof). If `h` is
differentiable at `x` and `ψ : ℝ → ℝ` at `h(x)`, then `∇^M(ψ ∘ h)(x) = ψ'(h(x)) ∇^M h(x)`:
`D(ψ ∘ h)(x) = ψ'(h(x)) Dh(x)` by the chain rule, and both the inverse Riesz map defining
`∇f(x)` from `Df(x)` and the projection `p_{T_x V}` are linear. -/
theorem Submission.tangentialGradient_comp_of_differentiableAt : ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (h : Ambient n ℓ → ℝ) (ψ : ℝ → ℝ) (x : Ambient n ℓ), DifferentiableAt ℝ h x → DifferentiableAt ℝ ψ (h x) → V.tangentialGradient (fun y ↦ ψ (h y)) x = deriv ψ (h x) • V.tangentialGradient h x := by
  intro n ℓ V h ψ x hh hψ
  -- chain rule: `D(ψ ∘ h)(x) = ψ'(h(x)) • Dh(x)`
  have hcomp : fderiv ℝ (fun y ↦ ψ (h y)) x = deriv ψ (h x) • fderiv ℝ h x :=
    (hψ.hasDerivAt.comp_hasFDerivAt x hh.hasFDerivAt).fderiv
  -- `∇f(x) = (toDual ℝ _).symm (Df(x))` and `p_{T_x V}` are both linear
  simp only [tangentialGradient, gradient, hcomp, map_smul]
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
/-- **Continuity in the scale** (Simon Ch. 4, 3.3–3.5, p. 90: `I(τ) = ∫ g ψ(r/τ) dμ` is continuous in
`τ`). If `0 < σ`, `0 < c`, `c ρ < R`, `g` is `μ`-integrable on `B_R(ξ)`, `ψ` is continuous and
`ψ(t) = 0` for `t > c`, then for `τ ∈ [σ, ρ]` the integrand vanishes off `B = B_R(ξ)` (there
`|x - ξ| / τ > R / τ > c`), so it equals `1_B g · ψ(|x - ξ| / τ)`. It is bounded by `1_B M |g|`,
where `|ψ| ≤ M` on `[0, R / σ]`, and it is continuous in `τ`. Hence `τ ↦ ∫ g ψ(|x - ξ| / τ) dμ`
is continuous on `[σ, ρ]` (`continuousOn_of_dominated`). -/
theorem Submission.wm_smoothed_scale_integral_continuousOn : ∀ (n ℓ : ℕ) (μ : Measure (Ambient n ℓ)) (g : Ambient n ℓ → ℝ) (ψ : ℝ → ℝ) (ξ : Ambient n ℓ) (c σ ρ R : ℝ), 0 < σ → 0 < c → c * ρ < R → IntegrableOn g (closedBall ξ R) μ → Continuous ψ → (∀ t, c < t → ψ t = 0) → ContinuousOn (fun τ ↦ ∫ x, g x * ψ (‖x - ξ‖ / τ) ∂μ) (Icc σ ρ) := by
  intro n ℓ μ g ψ ξ c σ ρ R hσ hc hcρ hg hψ hψ0
  -- step 1: every `τ ∈ [σ, ρ]` has `τ > 0` and `c τ < R`
  have hτ : ∀ τ ∈ Icc σ ρ, 0 < τ ∧ c * τ < R := fun τ hτ ↦
    ⟨hσ.trans_le hτ.1, (mul_le_mul_of_nonneg_left hτ.2 hc.le).trans_lt hcρ⟩
  -- step 2: off `B = B_R(ξ)`, `|x - ξ| / τ > c`, so `ψ` vanishes and the integrand is `1_B g ψ`
  have hvan : ∀ τ ∈ Icc σ ρ, ∀ x ∉ closedBall ξ R, ψ (‖x - ξ‖ / τ) = 0 := by
    intro τ hτσ x hx
    rw [mem_closedBall, dist_eq_norm, not_le] at hx
    exact hψ0 _ ((lt_div_iff₀ (hτ τ hτσ).1).2 ((hτ τ hτσ).2.trans hx))
  have hF : ∀ τ ∈ Icc σ ρ, ∀ x,
      (closedBall ξ R).indicator g x * ψ (‖x - ξ‖ / τ) = g x * ψ (‖x - ξ‖ / τ) := by
    intro τ hτσ x
    by_cases hx : x ∈ closedBall ξ R
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, hvan τ hτσ x hx, mul_zero, mul_zero]
  -- step 3: `|ψ| ≤ M` on the compact interval `[0, R / σ]`
  obtain ⟨M, hM⟩ :=
    (isCompact_Icc : IsCompact (Icc 0 (R / σ))).exists_bound_of_continuousOn hψ.continuousOn
  -- step 4: `1_B g` and the majorant `1_B (M |g|)` are integrable
  have hgi : Integrable ((closedBall ξ R).indicator g) μ :=
    hg.integrable_indicator measurableSet_closedBall
  have hbi : Integrable ((closedBall ξ R).indicator fun x ↦ M * ‖g x‖) μ :=
    IntegrableOn.integrable_indicator (hg.norm.const_mul M) measurableSet_closedBall
  -- step 8: `continuousOn_of_dominated`, whose hypotheses are steps 5, 6, 4 and 7
  refine continuousOn_of_dominated (fun τ hτσ ↦ ?_) (fun τ hτσ ↦ ?_) hbi ?_
  · -- step 5: `1_B g · ψ(|x - ξ| / τ)` is a.e. strongly measurable
    exact (hgi.aestronglyMeasurable.mul
      (hψ.comp ((continuous_id.sub continuous_const).norm.div_const τ)).aestronglyMeasurable).congr
      (Eventually.of_forall (hF τ hτσ))
  · -- step 6: domination by `1_B (M |g|)`
    filter_upwards with x
    by_cases hx : x ∈ closedBall ξ R
    · have hxR : ‖x - ξ‖ ≤ R := by rwa [mem_closedBall, dist_eq_norm] at hx
      have hτ0 := (hτ τ hτσ).1
      have hs : ‖x - ξ‖ / τ ∈ Icc 0 (R / σ) :=
        ⟨div_nonneg (norm_nonneg _) hτ0.le,
          calc ‖x - ξ‖ / τ ≤ R / τ := div_le_div_of_nonneg_right hxR hτ0.le
            _ ≤ R / σ := div_le_div_of_nonneg_left ((norm_nonneg _).trans hxR) hσ hτσ.1⟩
      rw [indicator_of_mem hx, norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hM _ hs) (norm_nonneg _)
    · simp [indicator_of_notMem hx, hvan τ hτσ x hx]
  · -- step 7: `τ ↦ g x ψ(|x - ξ| / τ)` is continuous on `[σ, ρ]` for every `x`
    filter_upwards with x
    exact continuousOn_const.mul (hψ.comp_continuousOn
      (continuousOn_const.div continuousOn_id fun τ hτσ ↦ (hτ τ hτσ).1.ne'))
/-- **Fubini for the smoothed monotonicity kernel** (Simon Ch. 4, 3.3–3.5, p. 90). Put
`r = |x - ξ|`, `κ(τ, x) = -(r / τ²) χ(r / τ) / τᵏ` and `B = B_R(ξ)`. If `0 < σ`, `0 < c`,
`c ρ < R`, `μ` is finite on compact sets, `w` is a.e. strongly measurable and bounded by `A` on
`B`, `χ` is continuous and `χ(t) = 0` for `t > c`, then `κ(τ, x) = 0` for `τ ∈ (σ, ρ]` and
`x ∉ B`. So both sides are iterated integrals of `f(τ, x) = 1_B w(x) κ(τ, x)`. With `|χ| ≤ M` on
`[0, R / σ]`, `|f| ≤ A (R / σ²) M / σᵏ 1_B` for a.e. `(τ, x)`, which is integrable for
`λ⌞(σ, ρ] ⊗ μ` since `μ(B) < ∞`; Fubini (`integral_integral_swap`) gives the identity. -/
theorem Submission.wm_smoothed_kernel_fubini : ∀ (n ℓ k : ℕ) (μ : Measure (Ambient n ℓ)) (w : Ambient n ℓ → ℝ) (χ : ℝ → ℝ) (ξ : Ambient n ℓ) (c σ ρ R A : ℝ), IsFiniteMeasureOnCompacts μ → 0 < σ → 0 < c → c * ρ < R → AEStronglyMeasurable w (μ.restrict (closedBall ξ R)) → (∀ x ∈ closedBall ξ R, |w x| ≤ A) → Continuous χ → (∀ t, c < t → χ t = 0) → ∫ τ in Ioc σ ρ, (∫ x, w x * (-(‖x - ξ‖ / τ ^ 2) * χ (‖x - ξ‖ / τ)) ∂μ) / τ ^ k = ∫ x, w x * (∫ τ in Ioc σ ρ, -(‖x - ξ‖ / τ ^ 2) * χ (‖x - ξ‖ / τ) / τ ^ k) ∂μ := by
  intro n ℓ k μ w χ ξ c σ ρ R A hμ hσ hc hcρ hw hwA hχ hχ0
  -- step 1: for `τ ∈ (σ, ρ]` and `x ∉ B`, `|x - ξ| / τ > c`, so `χ(|x - ξ| / τ) = 0`
  have hvan : ∀ τ ∈ Ioc σ ρ, ∀ x ∉ closedBall ξ R, χ (‖x - ξ‖ / τ) = 0 := by
    intro τ hτ x hx
    rw [mem_closedBall, dist_eq_norm, not_le] at hx
    exact hχ0 _ ((lt_div_iff₀ (hσ.trans hτ.1)).2
      ((mul_le_mul_of_nonneg_left hτ.2 hc.le).trans_lt (hcρ.trans hx)))
  -- step 2: `|χ| ≤ M` on the compact interval `[0, R / σ]`
  obtain ⟨M, hM⟩ :=
    (isCompact_Icc : IsCompact (Icc 0 (R / σ))).exists_bound_of_continuousOn hχ.continuousOn
  -- steps 3–4: the left side is `∫_{(σ,ρ]} ∫ f(τ, x) dμ dτ`
  have hL : ∫ τ in Ioc σ ρ, (∫ x, w x * (-(‖x - ξ‖ / τ ^ 2) * χ (‖x - ξ‖ / τ)) ∂μ) / τ ^ k =
      ∫ τ in Ioc σ ρ, ∫ x, (closedBall ξ R).indicator w x *
        (-(‖x - ξ‖ / τ ^ 2) * χ (‖x - ξ‖ / τ) / τ ^ k) ∂μ := by
    refine setIntegral_congr_fun measurableSet_Ioc fun τ hτ ↦ ?_
    rw [← integral_div]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    by_cases hx : x ∈ closedBall ξ R
    · simp only [indicator_of_mem hx]
      ring
    · simp only [indicator_of_notMem hx, hvan τ hτ x hx]
      ring
  -- step 5: the right side is `∫ ∫_{(σ,ρ]} f(τ, x) dτ dμ`
  have hR : ∫ x, (∫ τ in Ioc σ ρ, (closedBall ξ R).indicator w x *
        (-(‖x - ξ‖ / τ ^ 2) * χ (‖x - ξ‖ / τ) / τ ^ k)) ∂μ =
      ∫ x, w x * (∫ τ in Ioc σ ρ, -(‖x - ξ‖ / τ ^ 2) * χ (‖x - ξ‖ / τ) / τ ^ k) ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    dsimp only
    rw [integral_const_mul]
    by_cases hx : x ∈ closedBall ξ R
    · rw [indicator_of_mem hx]
    · have h0 : ∫ τ in Ioc σ ρ, -(‖x - ξ‖ / τ ^ 2) * χ (‖x - ξ‖ / τ) / τ ^ k = 0 :=
        setIntegral_eq_zero_of_forall_eq_zero fun τ hτ ↦ by rw [hvan τ hτ x hx, mul_zero, zero_div]
      rw [indicator_of_notMem hx, h0, zero_mul, mul_zero]
  -- steps 6–8: `f` is integrable for `λ⌞(σ, ρ] ⊗ μ`
  have hμB : μ (closedBall ξ R) < ⊤ := (isCompact_closedBall ξ R).measure_lt_top
  have hg : Integrable ((closedBall ξ R).indicator fun _ ↦ A * (R / σ ^ 2 * M / σ ^ k)) μ :=
    (integrableOn_const hμB.ne).integrable_indicator measurableSet_closedBall
  have hint : Integrable (Function.uncurry fun τ x ↦ (closedBall ξ R).indicator w x *
      (-(‖x - ξ‖ / τ ^ 2) * χ (‖x - ξ‖ / τ) / τ ^ k)) ((volume.restrict (Ioc σ ρ)).prod μ) := by
    refine (hg.comp_snd (volume.restrict (Ioc σ ρ))).mono' ?_ ?_
    · -- step 6: `1_B w` is a.e. strongly measurable and the kernel is Borel
      have hr : Measurable fun p : ℝ × Ambient n ℓ ↦ ‖p.2 - ξ‖ := (measurable_snd.sub_const ξ).norm
      exact ((aestronglyMeasurable_indicator_iff measurableSet_closedBall).2 hw).comp_snd.mul
        (((hr.div (measurable_fst.pow_const 2)).neg.mul
          (hχ.measurable.comp (hr.div measurable_fst))).div
            (measurable_fst.pow_const k)).aestronglyMeasurable
    · -- step 7: `|f(τ, x)| ≤ A (R / σ²) M / σᵏ 1_B(x)` for a.e. `(τ, x)`, as `τ ∈ (σ, ρ]`
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)]
      rintro ⟨τ, x⟩ hτ
      have hστ : σ < τ := hτ.1
      have hτ0 : 0 < τ := hσ.trans hστ
      simp only [Function.uncurry_apply_pair]
      by_cases hx : x ∈ closedBall ξ R
      · have hxR : ‖x - ξ‖ ≤ R := by rwa [mem_closedBall, dist_eq_norm] at hx
        have hR0 : 0 ≤ R := (norm_nonneg _).trans hxR
        have hA0 : 0 ≤ A := (abs_nonneg _).trans (hwA x hx)
        have hs : ‖x - ξ‖ / τ ∈ Icc 0 (R / σ) :=
          ⟨by positivity, (div_le_div_of_nonneg_right hxR hτ0.le).trans
            (div_le_div_of_nonneg_left hR0 hσ hστ.le)⟩
        have hχM : |χ (‖x - ξ‖ / τ)| ≤ M := by rw [← Real.norm_eq_abs]; exact hM _ hs
        have hM0 : 0 ≤ M := (abs_nonneg _).trans hχM
        have h1 : ‖x - ξ‖ / τ ^ 2 ≤ R / σ ^ 2 :=
          (div_le_div_of_nonneg_right hxR (by positivity)).trans
            (div_le_div_of_nonneg_left hR0 (by positivity) (pow_le_pow_left₀ hσ.le hστ.le 2))
        have h2 : ‖x - ξ‖ / τ ^ 2 * |χ (‖x - ξ‖ / τ)| / τ ^ k ≤ R / σ ^ 2 * M / σ ^ k :=
          div_le_div₀ (by positivity) (mul_le_mul h1 hχM (abs_nonneg _) (by positivity))
            (by positivity) (pow_le_pow_left₀ hσ.le hστ.le k)
        simp only [indicator_of_mem hx, norm_mul, norm_div, norm_neg, norm_pow, Real.norm_eq_abs,
          abs_norm, abs_of_pos hτ0]
        exact mul_le_mul (hwA x hx) h2 (by positivity) hA0
      · simp only [indicator_of_notMem hx, zero_mul, norm_zero, le_refl]
  -- step 9: Fubini
  exact hL.trans ((integral_integral_swap hint).trans hR)
/-- **Scaled FTC** (Simon Ch. 4, 3.4–3.5, p. 90: `d/dρ (ρ⁻ⁿ I(ρ)) = ρ⁻ⁿ J'(ρ)`, integrated, with
an extra term `L`). If `I' = I₁` and `n I - τ I₁ + τ J₁ + L = 0` on `[σ, ρ]`, `0 < σ ≤ ρ`, then by the
quotient rule `(I / tⁿ)' = J₁ / τⁿ + L / τⁿ⁺¹` on `[σ, ρ]` (for `n = m + 1`, clearing denominators
leaves `τ^{3m+3}` times the identity). For continuous `J₁`, `L` the FTC on `[σ, ρ]` then gives
`I ρ / ρⁿ - I σ / σⁿ = ∫_{(σ,ρ]} J₁ / τⁿ + ∫_{(σ,ρ]} L / τⁿ⁺¹`. -/
theorem Submission.wm_smoothed_scaled_ftc : ∀ (n : ℕ) (I I₁ J₁ L : ℝ → ℝ) (σ ρ : ℝ), 0 < σ → σ ≤ ρ → (∀ τ ∈ Icc σ ρ, HasDerivAt I (I₁ τ) τ) → (∀ τ ∈ Icc σ ρ, (n : ℝ) * I τ - τ * I₁ τ + τ * J₁ τ + L τ = 0) → ContinuousOn J₁ (Icc σ ρ) → ContinuousOn L (Icc σ ρ) → I ρ / ρ ^ n - I σ / σ ^ n = (∫ τ in Ioc σ ρ, J₁ τ / τ ^ n) + ∫ τ in Ioc σ ρ, L τ / τ ^ (n + 1) := by
  intro n I I₁ J₁ L σ ρ hσ hσρ hI hE hJ hL
  have hpos : ∀ τ ∈ Icc σ ρ, 0 < τ := fun τ hτ ↦ hσ.trans_le hτ.1
  -- quotient rule, and the identity turns `(I / tⁿ)'` into `J₁ / τⁿ + L / τⁿ⁺¹`
  have hderiv : ∀ τ ∈ uIcc σ ρ,
      HasDerivAt (fun t ↦ I t / t ^ n) (J₁ τ / τ ^ n + L τ / τ ^ (n + 1)) τ := by
    intro τ hτ
    rw [uIcc_of_le hσρ] at hτ
    have hτ0 : τ ≠ 0 := (hpos τ hτ).ne'
    have hEτ := hE τ hτ
    convert (hI τ hτ).fun_div (hasDerivAt_pow n τ) (pow_ne_zero n hτ0) using 1
    rcases n with _ | m
    · have h₁ : τ ^ 0 ≠ 0 := pow_ne_zero _ hτ0
      have h₂ : τ ^ (0 + 1) ≠ 0 := pow_ne_zero _ hτ0
      rw [div_add_div _ _ h₁ h₂, div_eq_div_iff (mul_ne_zero h₁ h₂) (pow_ne_zero 2 h₁)]
      push_cast at hEτ ⊢
      linear_combination hEτ
    · rw [Nat.add_sub_cancel]
      have h₁ : τ ^ (m + 1) ≠ 0 := pow_ne_zero _ hτ0
      have h₂ : τ ^ (m + 1 + 1) ≠ 0 := pow_ne_zero _ hτ0
      rw [div_add_div _ _ h₁ h₂, div_eq_div_iff (mul_ne_zero h₁ h₂) (pow_ne_zero 2 h₁)]
      push_cast at hEτ ⊢
      linear_combination τ ^ (3 * m + 3) * hEτ
  -- both quotients are continuous on `[σ, ρ]`
  have hc₁ : ContinuousOn (fun τ ↦ J₁ τ / τ ^ n) (Icc σ ρ) :=
    hJ.div₀ (continuousOn_pow n) fun τ hτ ↦ pow_ne_zero n (hpos τ hτ).ne'
  have hc₂ : ContinuousOn (fun τ ↦ L τ / τ ^ (n + 1)) (Icc σ ρ) :=
    hL.div₀ (continuousOn_pow (n + 1)) fun τ hτ ↦ pow_ne_zero (n + 1) (hpos τ hτ).ne'
  -- FTC on `[σ, ρ]`, then split the integral over `(σ, ρ]`
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((hc₁.fun_add hc₂).intervalIntegrable_of_Icc hσρ)
  rw [intervalIntegral.integral_of_le hσρ,
    integral_add (hc₁.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      (hc₂.integrableOn_Icc.mono_set Ioc_subset_Icc_self)] at hftc
  exact hftc.symm
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

/-- **Smoothed monotonicity identity** (Simon Ch. 4, 3.3–3.5, p. 90, for one cutoff `φ`). Write
`r = |x - ξ|`, `I(t) = ∫ u φ(r/t) dμ`, `I₁(t) = ∫ u · (-(r/t²) φ'(r/t)) dμ`,
`J₁(t) = ∫ u q · (-(r/t²) φ'(r/t)) dμ` and `L(t) = ∫ φ(r/t) G dμ`. For `τ ∈ [σ, ρ]`,
`weighted_mono_cutoff_hasDerivAt` (with `c = 1 + ε`, `f = u` and `f = u q`) gives `I' = I₁` and
the integrability of both kernels, so `(ODE_τ)` becomes `n I - τ I₁ + τ J₁ + L = 0`. `L` and
`J₁(τ) = -(∫ u q ψ₁(r/τ) dμ) / τ`, `ψ₁(s) = s φ'(s)`, are continuous on `[σ, ρ]`
(`wm_smoothed_scale_integral_continuousOn`), so `wm_smoothed_scaled_ftc` gives
`I(ρ)/ρⁿ - I(σ)/σⁿ = ∫_{(σ,ρ]} J₁/τⁿ + ∫_{(σ,ρ]} L/τⁿ⁺¹`, and `wm_smoothed_kernel_fubini`
(`w = u q`, `χ = φ'`) turns `∫_{(σ,ρ]} J₁/τⁿ` into `∫ u q k(r) dμ`. -/
theorem Submission.weighted_mono_smoothed_identity : ∀ (n ℓ : ℕ) (μ : Measure (Ambient n ℓ)) (u q G : Ambient n ℓ → ℝ) (φ : ℝ → ℝ) (ξ : Ambient n ℓ) (ε σ ρ R A : ℝ), IsFiniteMeasureOnCompacts μ → 0 < σ → σ ≤ ρ → 0 < ε → (1 + ε) * ρ < R → AEStronglyMeasurable u (μ.restrict (closedBall ξ R)) → AEStronglyMeasurable q (μ.restrict (closedBall ξ R)) → (∀ x ∈ closedBall ξ R, |u x| ≤ A ∧ |q x| ≤ 1) → IntegrableOn G (closedBall ξ R) μ → ContDiff ℝ 1 φ → (∀ t, 1 + ε ≤ t → φ t = 0) → (∀ τ ∈ Icc σ ρ, (n : ℝ) * ∫ x, u x * φ (‖x - ξ‖ / τ) ∂μ + ∫ x, u x * (1 - q x) * (‖x - ξ‖ / τ * deriv φ (‖x - ξ‖ / τ)) ∂μ + ∫ x, φ (‖x - ξ‖ / τ) * G x ∂μ = 0) → (∫ x, u x * φ (‖x - ξ‖ / ρ) ∂μ) / ρ ^ n - (∫ x, u x * φ (‖x - ξ‖ / σ) ∂μ) / σ ^ n = ∫ x, u x * q x * (∫ τ in Ioc σ ρ, -(‖x - ξ‖ / τ ^ 2) * deriv φ (‖x - ξ‖ / τ) / τ ^ n) ∂μ + ∫ τ in Ioc σ ρ, (∫ x, φ (‖x - ξ‖ / τ) * G x ∂μ) / τ ^ (n + 1) := by
  intro n ℓ μ u q G φ ξ ε σ ρ R A hμ hσ hσρ hε hR hu hq huq hG hφ hφ0 hODE
  -- step 0: every `τ ∈ [σ, ρ]` has `τ > 0` and `(1 + ε) τ < R`; `u q` is bounded by `A` on
  -- `B = B_R(ξ)`, hence integrable there (`μ(B) < ∞`)
  have hc : (0 : ℝ) < 1 + ε := by linarith
  have hτ : ∀ τ ∈ Icc σ ρ, 0 < τ ∧ (1 + ε) * τ < R := fun τ hτσ ↦
    ⟨hσ.trans_le hτσ.1, (mul_le_mul_of_nonneg_left hτσ.2 hc.le).trans_lt hR⟩
  have huA : ∀ x ∈ closedBall ξ R, |u x| ≤ A := fun x hx ↦ (huq x hx).1
  have huqm : AEStronglyMeasurable (fun x ↦ u x * q x) (μ.restrict (closedBall ξ R)) :=
    hu.fun_mul hq
  have huqA : ∀ x ∈ closedBall ξ R, |u x * q x| ≤ A := fun x hx ↦ by
    rw [abs_mul, ← mul_one A]
    exact mul_le_mul (huq x hx).1 (huq x hx).2 (abs_nonneg _) ((abs_nonneg _).trans (huq x hx).1)
  have huqi : IntegrableOn (fun x ↦ u x * q x) (closedBall ξ R) μ :=
    IntegrableOn.of_bound (isCompact_closedBall ξ R).measure_lt_top huqm A
      (ae_restrict_of_forall_mem measurableSet_closedBall fun x hx ↦
        (Real.norm_eq_abs _).trans_le (huqA x hx))
  -- `φ'` is continuous and vanishes on the open set `(1 + ε, ∞)`
  have hφ'c : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  have hφ' : ∀ s, 1 + ε < s → deriv φ s = 0 := by
    intro s hs
    have h : φ =ᶠ[𝓝 s] fun _ ↦ 0 :=
      Filter.eventually_of_mem (Ioi_mem_nhds hs) fun t ht ↦ hφ0 t (le_of_lt ht)
    rw [h.deriv_eq, deriv_const]
  -- step 1: `I' = I₁` on `[σ, ρ]`, and both kernels are integrable (`f = u` and `f = u q`)
  have hD := fun τ (hτσ : τ ∈ Icc σ ρ) ↦ Submission.weighted_mono_cutoff_hasDerivAt n ℓ μ u φ ξ
    (1 + ε) R A τ hμ hφ hφ0 hc (hτ τ hτσ).1 (hτ τ hτσ).2 hu huA
  have hDq := fun τ (hτσ : τ ∈ Icc σ ρ) ↦ Submission.weighted_mono_cutoff_hasDerivAt n ℓ μ
    (fun x ↦ u x * q x) φ ξ (1 + ε) R A τ hμ hφ hφ0 hc (hτ τ hτσ).1 (hτ τ hτσ).2 huqm huqA
  -- step 2: since `τ (r / τ²) = r / τ`, `(ODE_τ)` becomes `n I - τ I₁ + τ J₁ + L = 0`
  have hE : ∀ τ ∈ Icc σ ρ, (n : ℝ) * (∫ x, u x * φ (‖x - ξ‖ / τ) ∂μ) -
      τ * (∫ x, u x * (-(‖x - ξ‖ / τ ^ 2) * deriv φ (‖x - ξ‖ / τ)) ∂μ) +
      τ * (∫ x, u x * q x * (-(‖x - ξ‖ / τ ^ 2) * deriv φ (‖x - ξ‖ / τ)) ∂μ) +
      ∫ x, φ (‖x - ξ‖ / τ) * G x ∂μ = 0 := by
    intro τ hτσ
    have hτ0 : τ ≠ 0 := (hτ τ hτσ).1.ne'
    have hmid : ∫ x, u x * (1 - q x) * (‖x - ξ‖ / τ * deriv φ (‖x - ξ‖ / τ)) ∂μ =
        ∫ x, (-τ * (u x * (-(‖x - ξ‖ / τ ^ 2) * deriv φ (‖x - ξ‖ / τ))) +
          τ * (u x * q x * (-(‖x - ξ‖ / τ ^ 2) * deriv φ (‖x - ξ‖ / τ)))) ∂μ := by
      refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
      field_simp
      ring
    rw [integral_add ((hD τ hτσ).2.1.const_mul (-τ)) ((hDq τ hτσ).2.1.const_mul τ),
      integral_const_mul, integral_const_mul] at hmid
    linear_combination hODE τ hτσ - hmid
  -- step 4: `L` is continuous on `[σ, ρ]`
  have hL : ContinuousOn (fun τ ↦ ∫ x, φ (‖x - ξ‖ / τ) * G x ∂μ) (Icc σ ρ) :=
    (Submission.wm_smoothed_scale_integral_continuousOn n ℓ μ G φ ξ (1 + ε) σ ρ R hσ hc hR hG
      hφ.continuous fun t ht ↦ hφ0 t ht.le).congr fun τ _ ↦
      integral_congr_ae (ae_of_all _ fun x ↦ mul_comm _ _)
  -- step 4: `J₁(τ) = -(∫ u q ψ₁(r / τ) dμ) / τ` with `ψ₁(s) = s φ'(s)` is continuous on `[σ, ρ]`
  have hJ : ContinuousOn
      (fun τ ↦ ∫ x, u x * q x * (-(‖x - ξ‖ / τ ^ 2) * deriv φ (‖x - ξ‖ / τ)) ∂μ) (Icc σ ρ) := by
    have hK := Submission.wm_smoothed_scale_integral_continuousOn n ℓ μ (fun x ↦ u x * q x)
      (fun s ↦ s * deriv φ s) ξ (1 + ε) σ ρ R hσ hc hR huqi (continuous_id.mul hφ'c)
      fun s hs ↦ by simp only [hφ' s hs, mul_zero]
    refine (hK.fun_neg.div₀ continuousOn_id fun τ hτσ ↦ (hτ τ hτσ).1.ne').congr fun τ _ ↦ ?_
    show ∫ x, u x * q x * (-(‖x - ξ‖ / τ ^ 2) * deriv φ (‖x - ξ‖ / τ)) ∂μ =
      -(∫ x, u x * q x * (‖x - ξ‖ / τ * deriv φ (‖x - ξ‖ / τ)) ∂μ) / τ
    rw [← integral_neg, ← integral_div]
    exact integral_congr_ae (ae_of_all _ fun x ↦ by ring)
  -- steps 3 and 5: quotient rule and FTC, `I(ρ)/ρⁿ - I(σ)/σⁿ = ∫ J₁/τⁿ + ∫ L/τⁿ⁺¹` over `(σ, ρ]`
  have hftc := Submission.wm_smoothed_scaled_ftc n (fun t ↦ ∫ x, u x * φ (‖x - ξ‖ / t) ∂μ)
    (fun t ↦ ∫ x, u x * (-(‖x - ξ‖ / t ^ 2) * deriv φ (‖x - ξ‖ / t)) ∂μ)
    (fun t ↦ ∫ x, u x * q x * (-(‖x - ξ‖ / t ^ 2) * deriv φ (‖x - ξ‖ / t)) ∂μ)
    (fun t ↦ ∫ x, φ (‖x - ξ‖ / t) * G x ∂μ) σ ρ hσ hσρ (fun τ hτσ ↦ (hD τ hτσ).2.2) hE hJ hL
  -- steps 6 and 7: Fubini for the `J₁`-term (`w = u q`, `χ = φ'`, `k = n`)
  rw [Submission.wm_smoothed_kernel_fubini n ℓ n μ (fun x ↦ u x * q x) (deriv φ) ξ (1 + ε) σ ρ R A
    hμ hσ hc hR huqm huqA hφ'c hφ'] at hftc
  exact hftc
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
/-- **Derivative of the radial field, including the centre** (Simon Ch. 4, 3.2). For `γ ∈ C¹`
and `r = |x - ξ|`, the field `g(y) = γ(|y - ξ|)(y - ξ)` is differentiable at `x` with
`Dg(x)v = γ(r)v + (γ'(r)/r)⟨x - ξ, v⟩(x - ξ)` (with `γ'(r)/r = 0` when `r = 0`). At `x = ξ`
this is `γ(0)·I`, since `g(ξ + v) - g(ξ) - γ(0)v = (γ(|v|) - γ(0))v = o(|v|)` by continuity of
`γ`; for `x ≠ ξ`, `|y - ξ| = √(|y - ξ|²)` has derivative `r⁻¹⟨x - ξ, ·⟩` and the chain and
product rules give the formula. -/
theorem Submission.radial_vector_field_hasFDerivAt : ∀ (n ℓ : ℕ) (γ : ℝ → ℝ) (ξ x : Ambient n ℓ), ContDiff ℝ 1 γ → HasFDerivAt (fun y : Ambient n ℓ ↦ γ ‖y - ξ‖ • (y - ξ)) (γ ‖x - ξ‖ • ContinuousLinearMap.id ℝ (Ambient n ℓ) + (deriv γ ‖x - ξ‖ / ‖x - ξ‖) • (innerSL ℝ (x - ξ)).smulRight (x - ξ)) x := by
  intro n ℓ γ ξ x hγ
  have hγd : Differentiable ℝ γ := hγ.differentiable one_ne_zero
  rcases eq_or_ne x ξ with rfl | hx
  · -- the centre: the claimed derivative is `γ(0)·I` and the remainder is `(γ(|v|) - γ(0))v`
    simp only [sub_self, norm_zero, div_zero, zero_smul, add_zero]
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    have h1 : Tendsto (fun v : Ambient n ℓ ↦ γ ‖v‖ - γ 0) (𝓝 0) (𝓝 0) := by
      have h := (hγd.continuous.tendsto (‖(0 : Ambient n ℓ)‖)).comp (continuous_norm.tendsto 0)
      simpa [Function.comp_def] using h.sub_const (γ 0)
    have h2 : (fun v : Ambient n ℓ ↦ (γ ‖v‖ - γ 0) • v) =o[𝓝 0] fun v ↦ v := by
      have h := ((Asymptotics.isLittleO_one_iff ℝ).2 h1).smul_isBigO
        (Asymptotics.isBigO_refl (fun v : Ambient n ℓ ↦ v) (𝓝 0))
      simpa only [one_smul] using h
    refine h2.congr_left fun v ↦ ?_
    simp [sub_smul]
  · -- off the centre: `|y - ξ| = √(|y - ξ|²)`, then the chain and product rules
    have hr : 0 < ‖x - ξ‖ := norm_pos_iff.2 (sub_ne_zero.2 hx)
    have hsub : HasFDerivAt (fun y : Ambient n ℓ ↦ y - ξ) (ContinuousLinearMap.id ℝ (Ambient n ℓ)) x :=
      (hasFDerivAt_id x).sub_const ξ
    have hnorm : HasFDerivAt (fun y : Ambient n ℓ ↦ ‖y - ξ‖) (‖x - ξ‖⁻¹ • innerSL ℝ (x - ξ)) x := by
      have h := hsub.norm_sq.sqrt (pow_ne_zero 2 hr.ne')
      simp only [Real.sqrt_sq_eq_abs, abs_norm] at h
      refine h.congr_fderiv ?_
      ext v
      simp
      field_simp
    have hφ : HasFDerivAt (fun y : Ambient n ℓ ↦ γ ‖y - ξ‖)
        (deriv γ ‖x - ξ‖ • ‖x - ξ‖⁻¹ • innerSL ℝ (x - ξ)) x :=
      (hγd ‖x - ξ‖).hasDerivAt.comp_hasFDerivAt x hnorm
    refine (hφ.fun_smul hsub).congr_fderiv ?_
    ext v
    simp [smul_smul, div_eq_mul_inv]
/-- **Trace of `(c I + F(·) v) ∘ p_P`** (used for `div_M` of radial fields, Ch. 4, 3.2 and 5.1).
For a subspace `P` with orthogonal projection `p_P`, `c ∈ ℝ`, a continuous linear functional `F`
and `v ∈ ℝ^{n+ℓ}`: `trace((c I + F(·) v) ∘ p_P) = c dim P + F(p_P v)`. -/
theorem Submission.trace_scalar_add_rankOne_comp_starProjection : ∀ (n ℓ : ℕ) (P : Submodule ℝ (Ambient n ℓ)) (c : ℝ) (F : Ambient n ℓ →L[ℝ] ℝ) (v : Ambient n ℓ), LinearMap.trace ℝ (Ambient n ℓ) ((c • ContinuousLinearMap.id ℝ (Ambient n ℓ) + F.smulRight v).toLinearMap ∘ₗ P.starProjection.toLinearMap) = c * (Module.finrank ℝ P : ℝ) + F (P.starProjection v) := by
  intro n ℓ P c F v
  -- `trace p_P = dim P`: `p_P = ι ∘ π`, and `trace (ι ∘ π) = trace (π ∘ ι) = trace id_P`.
  have hp : LinearMap.trace ℝ (Ambient n ℓ) P.starProjection.toLinearMap =
      (Module.finrank ℝ P : ℝ) := by
    rw [Submodule.starProjection, ContinuousLinearMap.toLinearMap_comp,
      LinearMap.trace_comp_comm']
    have hπι : P.orthogonalProjectionOnto.toLinearMap ∘ₗ P.subtypeL.toLinearMap =
        LinearMap.id := by
      ext x
      simp
    rw [hπι, LinearMap.trace_id]
  -- `(c I + F(·) v) ∘ p_P = c p_P + (F ∘ p_P)(·) v`; the rank-one part has trace `F(p_P v)`.
  have hA : (c • ContinuousLinearMap.id ℝ (Ambient n ℓ) + F.smulRight v).toLinearMap ∘ₗ
      P.starProjection.toLinearMap = c • P.starProjection.toLinearMap +
        (F.toLinearMap ∘ₗ P.starProjection.toLinearMap).smulRight v := by
    ext w
    simp
  rw [hA, map_add, map_smul, LinearMap.trace_smulRight, hp, smul_eq_mul]
  rfl

theorem main_theorem : ApproxTangentAE ∧ FirstVariationFormula ∧ StationaryIffVariational ∧ StationaryMonotonicity ∧ StationaryDensity ∧ CanonicalRepresentative ∧ BoundedCurvatureMonotonicity ∧ LogarithmicMonotonicityError ∧ LpMonotonicity ∧ LpDensity ∧ LpSupportRepresentation ∧ PoincareInequality ∧ SobolevInequality ∧ SupportInBall ∧ ConvexHullProperty ∧ ClassicalTangent := by sorry

/-- **Pointwise tangential divergence of the weighted radial field** (Simon Ch. 4, 3.2 and 5.1).
If `dim T_x V = n`, `h` is differentiable at `x` and `γ` is `C¹`, then for
`X(y) = h(y) γ(|y - ξ|)(y - ξ)` and `r = |x - ξ|`,
`div_M X(x) = h(x)(n γ(r) + r γ'(r)(1 - |D^⊥r|²)) + γ(r) (x - ξ) · ∇^M h(x)`. -/
theorem Submission.tangentialDiv_weighted_radial_field : ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (h : Ambient n ℓ → ℝ) (γ : ℝ → ℝ) (ξ x : Ambient n ℓ), Module.finrank ℝ (V.tangentSpace x) = n → DifferentiableAt ℝ h x → ContDiff ℝ 1 γ → V.tangentialDiv (fun y ↦ (h y * γ ‖y - ξ‖) • (y - ξ)) x = h x * ((n : ℝ) * γ ‖x - ξ‖ + ‖x - ξ‖ * deriv γ ‖x - ξ‖ * (1 - V.normalRadialSq ξ x)) + γ ‖x - ξ‖ * inner ℝ (x - ξ) (V.tangentialGradient h x) := by
  intro n ℓ V h γ ξ x hdim hh hγ
  -- `X = h • g` with `g(y) = γ(|y - ξ|)(y - ξ)`; by the product rule and the derivative of `g`,
  -- `DX(x) = c I + F(·)(x - ξ)` with `c = h(x)γ(r)` and `F = h(x)(γ'(r)/r)⟨x - ξ, ·⟩ + γ(r) Dh(x)`.
  have hX : (fun y ↦ (h y * γ ‖y - ξ‖) • (y - ξ)) = fun y ↦ h y • γ ‖y - ξ‖ • (y - ξ) := by
    funext y
    exact mul_smul _ _ _
  have hDX : fderiv ℝ (fun y ↦ (h y * γ ‖y - ξ‖) • (y - ξ)) x =
      (h x * γ ‖x - ξ‖) • ContinuousLinearMap.id ℝ (Ambient n ℓ) +
        ((h x * (deriv γ ‖x - ξ‖ / ‖x - ξ‖)) • innerSL ℝ (x - ξ) +
          γ ‖x - ξ‖ • fderiv ℝ h x).smulRight (x - ξ) := by
    rw [hX, (hh.hasFDerivAt.fun_smul
      (Submission.radial_vector_field_hasFDerivAt n ℓ γ ξ x hγ)).fderiv]
    refine ContinuousLinearMap.ext fun u ↦ ?_
    simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_eq_mul]
    module
  -- Hence `div_M X(x) = c dim T_x V + F(p(x - ξ))`, with `p` the projection onto `T_x V`.
  rw [RectifiableVarifold.tangentialDiv, hDX,
    Submission.trace_scalar_add_rankOne_comp_starProjection n ℓ (V.tangentSpace x), hdim]
  set P := V.tangentSpace x
  -- Gradient term: `Dh(x)(p(x - ξ)) = ⟨∇h(x), p(x - ξ)⟩ = ⟨x - ξ, p ∇h(x)⟩ = ⟨x - ξ, ∇^M h(x)⟩`.
  have hgrad : fderiv ℝ h x (P.starProjection (x - ξ)) =
      inner ℝ (x - ξ) (V.tangentialGradient h x) := by
    rw [← inner_gradient_left, ← P.inner_starProjection_left_eq_right, real_inner_comm]
    rfl
  -- Projection term: `⟨x - ξ, p(x - ξ)⟩ = |p(x - ξ)|²`.
  have hpw : inner ℝ (x - ξ) (P.starProjection (x - ξ)) = ‖P.starProjection (x - ξ)‖ ^ 2 := by
    calc inner ℝ (x - ξ) (P.starProjection (x - ξ))
        = inner ℝ (x - ξ) (P.starProjection (P.starProjection (x - ξ))) := by
          rw [Submodule.starProjection_eq_self_iff.mpr (P.starProjection_apply_mem _)]
      _ = inner ℝ (P.starProjection (x - ξ)) (P.starProjection (x - ξ)) :=
          (P.inner_starProjection_left_eq_right _ _).symm
      _ = ‖P.starProjection (x - ξ)‖ ^ 2 := real_inner_self_eq_norm_sq _
  -- Pythagoras: `r² = |p(x - ξ)|² + |p^⊥(x - ξ)|²`, so `(γ'(r)/r)|p(x - ξ)|² = rγ'(r)(1 - q_ξ(x))`
  -- (both sides vanish when `r = 0`).
  have key : deriv γ ‖x - ξ‖ / ‖x - ξ‖ * ‖P.starProjection (x - ξ)‖ ^ 2 =
      ‖x - ξ‖ * deriv γ ‖x - ξ‖ * (1 - V.normalRadialSq ξ x) := by
    have hpy := P.norm_sq_eq_add_norm_sq_starProjection (x - ξ)
    rw [RectifiableVarifold.normalRadialSq]
    generalize ‖P.starProjection (x - ξ)‖ = a at hpy ⊢
    generalize ‖Pᗮ.starProjection (x - ξ)‖ = b at hpy ⊢
    generalize ‖x - ξ‖ = r at hpy ⊢
    rcases eq_or_ne r 0 with hr | hr
    · simp [hr]
    · rw [show a ^ 2 = r ^ 2 - b ^ 2 by linarith]
      field_simp
  simp only [add_apply, smul_apply, innerSL_apply_apply, smul_eq_mul, hgrad, hpw]
  linear_combination h x * key

/-- Simon 3.2–3.3 and 5.1 (pp. 89–90, 96) with Definition 3.14 (p. 92): the first variation
formula for the radial field `X(x) = h(x) γ(r) (x - ξ)`, `r = |x - ξ|`. If `dim T_x V = n` for
`μ_V`-a.e. `x`, `V` has generalized mean curvature `H` in the open set `U`, `h ∈ C¹(U)`,
`γ ∈ C¹(ℝ)` and `X ∈ C¹_c(U; ℝ^{n+ℓ})`, then `∫_U (h (n γ(r) + r γ'(r) (1 - |D^⊥ r|²)) +
γ(r) (x - ξ) · ∇^M h) dμ_V = -∫_U h γ(r) (x - ξ) · H dμ_V`. -/
theorem Submission.radial_first_variation : ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)) (H : Ambient n ℓ → Ambient n ℓ) (h : Ambient n ℓ → ℝ) (γ : ℝ → ℝ) (ξ : Ambient n ℓ), (∀ᵐ x ∂V.weight, Module.finrank ℝ (V.tangentSpace x) = n) → IsOpen U → V.HasMeanCurvatureIn U H → ContDiffOn ℝ 1 h U → ContDiff ℝ 1 γ → IsTestField U (fun x ↦ (h x * γ ‖x - ξ‖) • (x - ξ)) → ∫ x in U, (h x * ((n : ℝ) * γ ‖x - ξ‖ + ‖x - ξ‖ * deriv γ ‖x - ξ‖ * (1 - V.normalRadialSq ξ x)) + γ ‖x - ξ‖ * inner ℝ (x - ξ) (V.tangentialGradient h x)) ∂V.weight = -∫ x in U, h x * γ ‖x - ξ‖ * inner ℝ (x - ξ) (H x) ∂V.weight := by
  intro n ℓ V U H h γ ξ hdim hU hH hh hγ hX
  -- `X` vanishes near every point off `U`, since `tsupport X ⊆ U`.
  have hout : ∀ x ∉ U, x ∉ tsupport fun y ↦ (h y * γ ‖y - ξ‖) • (y - ξ) :=
    fun x hxU hx ↦ hxU (hX.2.2 hx)
  have hX0 : ∀ x ∉ U, (h x * γ ‖x - ξ‖) • (x - ξ) = 0 :=
    fun x hxU ↦ (image_eq_zero_of_notMem_tsupport (hout x hxU) :)
  calc _ = ∫ x in U, V.tangentialDiv (fun y ↦ (h y * γ ‖y - ξ‖) • (y - ξ)) x ∂V.weight := by
        -- Simon 3.2 and 5.1: the integrand is `div_M X` wherever `dim T_x V = n`.
        refine setIntegral_congr_ae hU.measurableSet ?_
        filter_upwards [hdim] with x hx hxU
        exact (Submission.tangentialDiv_weighted_radial_field n ℓ V h γ ξ x hx
          (hh.differentiableOn_one.differentiableAt (hU.mem_nhds hxU)) hγ).symm
    _ = ∫ x, V.tangentialDiv (fun y ↦ (h y * γ ‖y - ξ‖) • (y - ξ)) x ∂V.weight :=
        setIntegral_eq_integral_of_forall_compl_eq_zero fun x hxU ↦ by
          rw [tangentialDiv, fderiv_of_notMem_tsupport ℝ (hout x hxU)]
          simp
    _ = -∫ x, inner ℝ ((h x * γ ‖x - ξ‖) • (x - ξ)) (H x) ∂V.weight := hH.2 _ hX
    _ = _ := by
        rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := U) fun x hxU ↦ ?_]
        · simp_rw [real_inner_smul_left]
        · rw [hX0 x hxU, inner_zero_left]

/-- **Ch. 4, 3.3–3.6, 3.16, 4.1 and 5.1 (pp. 89–96), weighted monotonicity identity.** Let `V`
satisfy (FV) (`μ_V` finite on compact sets, `dim T_x V = n` `μ_V`-a.e., `x ↦ p_{T_x V}`
`μ_V`-a.e. strongly measurable), let `H` be a generalized mean curvature of `V` in the open set
`U`, `h ∈ C¹(U)` and `tsupport h ∩ B_ρ(ξ) ⊆ U`. Then for `0 < σ ≤ ρ`, with `r = |x - ξ|`,
`ρ⁻ⁿ ∫_{B_ρ(ξ)} h dμ_V - σ⁻ⁿ ∫_{B_σ(ξ)} h dμ_V = ∫_{B_ρ(ξ) \ B_σ(ξ)} h |D^⊥r|² / rⁿ dμ_V`
`+ ∫_{(σ,ρ]} τ⁻ⁿ⁻¹ ∫_{B_τ(ξ)} (x - ξ)·(∇^M h + hH) dμ_V dτ`,
and both integrands on the right are integrable. This is the printed route: the first variation of
`X = h φ(r/τ)(x - ξ)` gives the differentiated cutoff identity (3.3, 5.1), which is integrated over
`τ ∈ [σ, ρ]` (3.4) before the cutoff `φ` is removed (corrected 3.5, then 3.6). With the sign
convention 3.14(‡) the curvature term enters with a `+` sign (3.16, 4.1). -/
theorem Submission.weighted_monotonicity_identity : ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)) (H : Ambient n ℓ → Ambient n ℓ) (h : Ambient n ℓ → ℝ) (ξ : Ambient n ℓ) (σ ρ : ℝ), 0 < n → IsFiniteMeasureOnCompacts V.weight → (∀ᵐ x ∂V.weight, Module.finrank ℝ (V.tangentSpace x) = n) → AEStronglyMeasurable (fun x ↦ (V.tangentSpace x).starProjection) V.weight → IsOpen U → V.HasMeanCurvatureIn U H → ContDiffOn ℝ 1 h U → tsupport h ∩ closedBall ξ ρ ⊆ U → 0 < σ → σ ≤ ρ → IntegrableOn (fun τ ↦ (∫ x in closedBall ξ τ, inner ℝ (x - ξ) (V.tangentialGradient h x + h x • H x) ∂V.weight) / τ ^ (n + 1)) (Ioc σ ρ) ∧ IntegrableOn (fun x ↦ h x * (V.normalRadialSq ξ x / ‖x - ξ‖ ^ n)) (closedBall ξ ρ \ closedBall ξ σ) V.weight ∧ (∫ x in closedBall ξ ρ, h x ∂V.weight) / ρ ^ n - (∫ x in closedBall ξ σ, h x ∂V.weight) / σ ^ n = ∫ x in closedBall ξ ρ \ closedBall ξ σ, h x * (V.normalRadialSq ξ x / ‖x - ξ‖ ^ n) ∂V.weight + ∫ τ in Ioc σ ρ, (∫ x in closedBall ξ τ, inner ℝ (x - ξ) (V.tangentialGradient h x + h x • H x) ∂V.weight) / τ ^ (n + 1) := by
  intro n ℓ V U H h ξ σ ρ _hn hfin hdim hmeas hU hH hh hsupp hσ hσρ
  have hρ : 0 < ρ := hσ.trans_le hσρ
  -- The room `R > ρ`, the data of `h`, `q_ξ = |D^⊥r|²` and `G = (x - ξ)·(∇^M h + hH)` on
  -- `B_R(ξ)`, and for every cutoff `φ` and `0 < τ ≤ ρ` the differentiated identity
  -- `n ∫ h φ(r/τ) + ∫ h (1 - q_ξ) (r/τ) φ'(r/τ) + ∫ φ(r/τ) G = 0`; the first variation of the
  -- radial test fields is `radial_first_variation`.
  obtain ⟨R, A, hρR, hu, hq, hbd, hG, hode⟩ :=
    Submission.weighted_mono_cutoff_first_variation n ℓ V U H h ξ ρ hfin hmeas hU hH hh hsupp hρ
      fun γ hγ hX ↦ Submission.radial_first_variation n ℓ V U H h γ ξ hdim hU hH hh hγ hX
  -- Integrate `(τ⁻ⁿ I)' = τ⁻ⁿ J' + τ⁻ⁿ⁻¹ L_φ` over `[σ, ρ]` for each admissible cutoff `φ`, then
  -- let `φ` decrease to the indicator of `(-∞, 1]`.
  exact Submission.weighted_mono_cutoff_limit n ℓ V.weight h (V.normalRadialSq ξ)
    (fun x ↦ inner ℝ (x - ξ) (V.tangentialGradient h x + h x • H x)) ξ σ ρ R A hfin hσ hσρ hρR
    hu hq hbd hG fun ε φ hε hεR hφ _ h1 h0 ↦
      Submission.weighted_mono_smoothed_identity n ℓ V.weight h (V.normalRadialSq ξ)
        (fun x ↦ inner ℝ (x - ξ) (V.tangentialGradient h x + h x • H x)) φ ξ ε σ ρ R A hfin hσ
        hσρ hε hεR hu hq hbd hG hφ h0 fun τ hτ ↦
          hode ε φ hε hεR hφ h1 h0 τ (hσ.trans_le hτ.1) hτ.2

end

end GMT.Ch04
