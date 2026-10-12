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
import Poincare.SimonGMT.Chapter02.AreaLipschitz

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

/-- **Local lower bound at a regular point.** If `f : ℝⁿ → F` is differentiable at `w` and
`Df(w)` is injective, then for some `c > 0`, `c |u| ≤ |f(w + u) - f(w)|` whenever `|u| ≤ c`
(the pointwise step of the Lipschitz-piece replacement for Simon Ch. 3, Lemma 1.2). -/
theorem Submission.injective_fderiv_local_lower_bound : ∀ (n : ℕ) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : EuclideanSpace ℝ (Fin n) → F) (w : EuclideanSpace ℝ (Fin n)), DifferentiableAt ℝ f w → Function.Injective (fderiv ℝ f w) → ∃ c : ℝ, 0 < c ∧ ∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ ≤ c → c * ‖u‖ ≤ ‖f (w + u) - f w‖ := by
  intro n F _ _ f w hf hinj
  -- `L = Df(w)` is injective on the finite-dimensional `ℝⁿ`, so `‖u‖ ≤ K ‖L u‖` with `K > 0`.
  obtain ⟨K, hK, hKL⟩ :=
    (fderiv ℝ f w : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] F).exists_antilipschitzWith
      (LinearMap.ker_eq_bot.2 hinj)
  have hK' : (0 : ℝ) < K := hK
  -- With `m = K⁻¹`: `m ‖u‖ ≤ ‖L u‖` for all `u`.
  have hm : ∀ u, (K : ℝ)⁻¹ * ‖u‖ ≤ ‖fderiv ℝ f w u‖ := fun u ↦
    (inv_mul_le_iff₀ hK').2 (ZeroHomClass.bound_of_antilipschitz _ hKL u)
  have hm2 : 0 < (K : ℝ)⁻¹ / 2 := half_pos (inv_pos.2 hK')
  -- Differentiability: `‖f(w + u) - f(w) - L u‖ ≤ (m/2) ‖u‖` for `‖u‖ < r`.
  obtain ⟨r, hr, hfr⟩ := Metric.eventually_nhds_iff.1
    ((hasFDerivAt_iff_isLittleO_nhds_zero.1 hf.hasFDerivAt).bound hm2)
  -- `c = min(m/2, r/2)`.
  refine ⟨min ((K : ℝ)⁻¹ / 2) (r / 2), lt_min hm2 (half_pos hr), fun u hu ↦ ?_⟩
  have hur : dist u 0 < r := by
    rw [dist_zero_right]
    exact hu.trans_lt ((min_le_right _ _).trans_lt (half_lt_self hr))
  have h2 : ‖f (w + u) - f w - fderiv ℝ f w u‖ ≤ (K : ℝ)⁻¹ / 2 * ‖u‖ := hfr hur
  -- Triangle inequality: `‖L u‖ ≤ ‖f(w + u) - f(w)‖ + ‖f(w + u) - f(w) - L u‖`.
  have h3 : ‖fderiv ℝ f w u‖ ≤ ‖f (w + u) - f w‖ + ‖f (w + u) - f w - fderiv ℝ f w u‖ := by
    simpa only [sub_sub_cancel] using
      norm_sub_le (f (w + u) - f w) (f (w + u) - f w - fderiv ℝ f w u)
  calc min ((K : ℝ)⁻¹ / 2) (r / 2) * ‖u‖ ≤ (K : ℝ)⁻¹ / 2 * ‖u‖ :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg u)
    _ ≤ ‖f (w + u) - f w‖ := by linarith [hm u]
/-- **Lower Lipschitz pieces from pointwise local lower bounds.** If `f : ℝⁿ → F` is continuous
and every point `w` of the Borel set `R` has some `c > 0` with `c|u| ≤ |f(w + u) - f(w)|` for
`|u| ≤ c`, then `R` is covered by countably many bounded Borel sets `T_p ⊆ R`, on each of which
`f` satisfies a uniform lower Lipschitz bound `c_p|v - w| ≤ |f(v) - f(w)|`. -/
theorem Submission.lower_lipschitz_cover_of_local_bound : ∀ (n : ℕ) {F : Type} [NormedAddCommGroup F] (f : EuclideanSpace ℝ (Fin n) → F) (R : Set (EuclideanSpace ℝ (Fin n))), Continuous f → MeasurableSet R → (∀ w ∈ R, ∃ c : ℝ, 0 < c ∧ ∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ ≤ c → c * ‖u‖ ≤ ‖f (w + u) - f w‖) → ∃ T : ℕ → Set (EuclideanSpace ℝ (Fin n)), R ⊆ ⋃ p, T p ∧ ∀ p, MeasurableSet (T p) ∧ Bornology.IsBounded (T p) ∧ T p ⊆ R ∧ ∃ c : ℝ, 0 < c ∧ ∀ v ∈ T p, ∀ w ∈ T p, c * ‖v - w‖ ≤ ‖f v - f w‖ := by
  intro n F _ f R hf hR hloc
  -- Scales `r_k = 1/(k+1)` and the closed sets `G_k` of points with the lower bound at scale `r_k`.
  obtain ⟨r, hr, hrc⟩ : ∃ r : ℕ → ℝ, (∀ k, 0 < r k) ∧ ∀ c : ℝ, 0 < c → ∃ k, r k < c :=
    ⟨fun k ↦ 1 / ((k : ℝ) + 1), fun _ ↦ Nat.one_div_pos_of_nat, fun _ hc ↦ exists_nat_one_div_lt hc⟩
  obtain ⟨G, hG, hGmem⟩ : ∃ G : ℕ → Set (EuclideanSpace ℝ (Fin n)), (∀ k, IsClosed (G k)) ∧
      ∀ k w, w ∈ G k ↔ ∀ u, ‖u‖ ≤ r k → r k * ‖u‖ ≤ ‖f (w + u) - f w‖ :=
    ⟨fun k ↦ ⋂ u ∈ closedBall 0 (r k), {w | r k * ‖u‖ ≤ ‖f (w + u) - f w‖},
      fun k ↦ isClosed_biInter fun u _ ↦ isClosed_le continuous_const
        ((hf.comp (continuous_id.add continuous_const)).sub hf).norm,
      fun k w ↦ by simp only [mem_iInter₂, mem_closedBall_zero_iff, mem_ofPred_eq]⟩
  -- Every point of `R` lies in some `G_k`.
  have hRG : ∀ w ∈ R, ∃ k, w ∈ G k := fun w hw ↦ by
    obtain ⟨c, hc, hcw⟩ := hloc w hw
    obtain ⟨k, hk⟩ := hrc c hc
    exact ⟨k, (hGmem k w).2 fun u hu ↦
      (mul_le_mul_of_nonneg_right hk.le (norm_nonneg u)).trans (hcw u (hu.trans hk.le))⟩
  -- A dense sequence `q`: balls of radius `r_k / 2` around the `q_m` cover `ℝⁿ` for each `k`.
  obtain ⟨q, hq⟩ := TopologicalSpace.exists_dense_seq (EuclideanSpace ℝ (Fin n))
  refine ⟨fun p ↦ R ∩ G p.unpair.1 ∩ closedBall (q p.unpair.2) (r p.unpair.1 / 2), ?_,
    fun p ↦ ⟨?_, ?_, ?_, ?_⟩⟩
  · intro w hw
    obtain ⟨k, hk⟩ := hRG w hw
    obtain ⟨m, hm⟩ := hq.exists_dist_lt w (half_pos (hr k))
    refine mem_iUnion.2 ⟨Nat.pair k m, ?_⟩
    rw [Nat.unpair_pair]
    exact ⟨⟨hw, hk⟩, mem_closedBall.2 hm.le⟩
  · exact (hR.inter (hG _).measurableSet).inter measurableSet_closedBall
  · exact isBounded_closedBall.subset inter_subset_right
  · exact inter_subset_left.trans inter_subset_left
  · -- Two points of `T_p` are within `r_k` of each other, so the bound of `G_k` applies to `v - w`.
    refine ⟨r p.unpair.1, hr _, fun v hv w hw ↦ ?_⟩
    have hvw : ‖v - w‖ ≤ r p.unpair.1 := by
      rw [← dist_eq_norm]
      calc dist v w ≤ dist v (q p.unpair.2) + dist w (q p.unpair.2) := dist_triangle_right _ _ _
        _ ≤ r p.unpair.1 / 2 + r p.unpair.1 / 2 :=
          add_le_add (mem_closedBall.1 hv.2) (mem_closedBall.1 hw.2)
        _ = r p.unpair.1 := add_halves _
    simpa only [add_sub_cancel] using (hGmem _ w).1 hw.1.2 (v - w) hvw
/-- **Regular points of a continuous map.** If `f : ℝⁿ → ℝ^{n+ℓ}` is continuous, the set `R` of
points where `f` is differentiable with injective derivative is covered by countably many bounded
Borel sets `T_p ⊆ R`, on each of which `f` has a lower Lipschitz bound. `R` is SimonGMT's
`Chapter02.areaRegularSet f`, hence Borel. Each `w ∈ R` has a local lower bound
`c|u| ≤ |f(w + u) - f(w)|` for `|u| ≤ c` (`injective_fderiv_local_lower_bound`), and
`lower_lipschitz_cover_of_local_bound` makes these bounds uniform on countably many pieces. -/
theorem Submission.regular_set_lower_lipschitz_cover : ∀ (n ℓ : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → Ambient n ℓ), Continuous f →
    ∃ T : ℕ → Set (EuclideanSpace ℝ (Fin n)),
      {w | DifferentiableAt ℝ f w ∧ Function.Injective (fderiv ℝ f w)} ⊆ ⋃ p, T p ∧
      ∀ p, MeasurableSet (T p) ∧ Bornology.IsBounded (T p) ∧
        (∀ w ∈ T p, DifferentiableAt ℝ f w ∧ Function.Injective (fderiv ℝ f w)) ∧
        ∃ c : ℝ, 0 < c ∧ ∀ v ∈ T p, ∀ w ∈ T p, c * ‖v - w‖ ≤ ‖f v - f w‖ := by
  intro n ℓ f hf
  -- Every regular point has a pointwise lower bound; the cover makes the bounds uniform.
  obtain ⟨T, hRT, hT⟩ := Submission.lower_lipschitz_cover_of_local_bound n f
    {w | DifferentiableAt ℝ f w ∧ Function.Injective (fderiv ℝ f w)} hf
    (Poincare.SimonGMT.Chapter02.measurableSet_areaRegularSet f)
    (fun w hw ↦ Submission.injective_fderiv_local_lower_bound n f w hw.1 hw.2)
  refine ⟨T, hRT, fun p ↦ ?_⟩
  obtain ⟨hmeas, hbdd, hsub, hlower⟩ := hT p
  exact ⟨hmeas, hbdd, fun w hw ↦ hsub hw, hlower⟩
/-- **Lusin exhaustion (Simon Ch. 1, 1.17).** If `Y` is a finite-dimensional real normed space,
`g : ℝⁿ → Y` is Borel and `S ⊆ ℝⁿ` is Borel with `Lⁿ(S) < ∞`, then `S` is covered up to an
`Lⁿ`-null set by countably many compact sets `C_j ⊆ S` on each of which `g` is continuous. -/
theorem Submission.lusin_compact_exhaustion_of_measurable : ∀ {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] [MeasurableSpace Y] [BorelSpace Y] (n : ℕ) (g : EuclideanSpace ℝ (Fin n) → Y) (S : Set (EuclideanSpace ℝ (Fin n))), Measurable g → MeasurableSet S → volume S ≠ ⊤ → ∃ C : ℕ → Set (EuclideanSpace ℝ (Fin n)), (∀ j, IsCompact (C j) ∧ C j ⊆ S ∧ ContinuousOn g (C j)) ∧ volume (S \ ⋃ j, C j) = 0 := by
  intro Y _ _ _ _ _ n g S hg hS hSfin
  -- `Lⁿ ⌞ S` is finite, hence outer regular; `Y` has a countable topological basis.
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.2 hSfin
  have hb := TopologicalSpace.isBasis_countableBasis Y
  have : Countable (TopologicalSpace.countableBasis Y) :=
    (TopologicalSpace.countable_countableBasis Y).to_subtype
  -- One compact set: `K ⊆ S` with `g` continuous on `K` and `Lⁿ(S \ K) < ε`.
  have key : ∀ ε : ℝ≥0∞, ε ≠ 0 →
      ∃ K, IsCompact K ∧ K ⊆ S ∧ ContinuousOn g K ∧ volume (S \ K) < ε := by
    intro ε hε
    obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_pos_sum_of_countable (ENNReal.half_pos hε).ne'
      (TopologicalSpace.countableBasis Y)
    -- Open `O_U ⊇ g⁻¹(U)` with `(Lⁿ ⌞ S)(O_U \ g⁻¹(U)) < δ_U` for each basic open `U`.
    choose O hgO hO _ hOδ using fun U : TopologicalSpace.countableBasis Y ↦
      (hg (hb.isOpen U.2).measurableSet).exists_isOpen_sdiff_lt (μ := volume.restrict S)
        (measure_ne_top _ _) (ENNReal.coe_ne_zero.2 (hδ U).ne')
    -- The bad set `B = ⋃_U (O_U \ g⁻¹(U))` has `Lⁿ(S ∩ B) < ε/2`.
    set B := ⋃ U, (O U \ g ⁻¹' U)
    have hBm : MeasurableSet B :=
      MeasurableSet.iUnion fun U ↦ (hO U).measurableSet.diff (hg (hb.isOpen U.2).measurableSet)
    have hSB : volume (S ∩ B) < ε / 2 :=
      calc volume (S ∩ B) = volume.restrict S B := by rw [Measure.restrict_apply hBm, inter_comm]
        _ ≤ ∑' U, volume.restrict S (O U \ g ⁻¹' U) := measure_iUnion_le _
        _ ≤ ∑' U, (δ U : ℝ≥0∞) := ENNReal.tsum_le_tsum fun U ↦ (hOδ U).le
        _ < ε / 2 := hδε
    -- Inner regularity: compact `K ⊆ S \ B` with `Lⁿ((S \ B) \ K) < ε/2`.
    obtain ⟨K, hKSB, hK, hKε⟩ := (hS.diff hBm).exists_isCompact_sdiff_lt
      (ne_top_of_le_ne_top hSfin (measure_mono sdiff_subset)) (ENNReal.half_pos hε).ne'
    refine ⟨K, hK, hKSB.trans sdiff_subset, fun x _ ↦ ?_, ?_⟩
    · -- On `K`, `g⁻¹(U) ∩ K = O_U ∩ K` is relatively open, so `g` is continuous on `K`.
      refine hb.nhds_hasBasis.tendsto_right_iff.2 fun U ⟨hUb, hxU⟩ ↦
        mem_nhdsWithin.2 ⟨O ⟨U, hUb⟩, hO _, hgO _ hxU, fun y ⟨hyO, hyK⟩ ↦ ?_⟩
      by_contra hyU
      exact (hKSB hyK).2 (mem_iUnion.2 ⟨⟨U, hUb⟩, hyO, hyU⟩)
    · calc volume (S \ K) ≤ volume (S ∩ B) + volume ((S \ B) \ K) :=
            (measure_mono (show S \ K ⊆ (S ∩ B) ∪ ((S \ B) \ K) from fun y ⟨hyS, hyK⟩ ↦ by
              by_cases hyB : y ∈ B
              · exact Or.inl ⟨hyS, hyB⟩
              · exact Or.inr ⟨⟨hyS, hyB⟩, hyK⟩)).trans (measure_union_le _ _)
        _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hSB hKε
        _ = ε := ENNReal.add_halves ε
  -- Exhaustion: `C_j` with `Lⁿ(S \ C_j) < 1/j`, so `Lⁿ(S \ ⋃ C_j) = 0`.
  choose C hC hCS hCg hCε using fun j : ℕ ↦
    key (j : ℝ≥0∞)⁻¹ (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top j))
  refine ⟨C, fun j ↦ ⟨hC j, hCS j, hCg j⟩, ?_⟩
  by_contra h
  obtain ⟨j, hj⟩ := ENNReal.exists_inv_nat_lt h
  exact lt_asymm hj
    ((measure_mono (sdiff_subset_sdiff_right (subset_iUnion C j))).trans_lt (hCε j))
/-- **Compact pieces of one Lipschitz image.** If `f : ℝⁿ → ℝ^{n+ℓ}` is Lipschitz, then up to an
`Hⁿ`-null set `Y`, `f(ℝⁿ)` is covered by images `f(C_i)` of compact sets on which `f` is
differentiable with injective derivative, `Df` is continuous, and `f` has a lower Lipschitz
bound. The bounded Borel pieces `T_p` of the regular set (`regular_set_lower_lipschitz_cover`)
are exhausted by Lusin compacta `D_{p,q}` for `Df` (`lusin_compact_exhaustion_of_measurable`);
`Y` is the image of the non-regular set (null by the area formula, Ch. 2 §3) together with the
image of the null remainders `T_p \ ⋃_q D_{p,q}` (null by Ch. 2, 1.8(i)). -/
theorem Submission.lipschitz_range_piece_cover : ∀ (n ℓ : ℕ) (K : NNReal)
    (f : EuclideanSpace ℝ (Fin n) → Ambient n ℓ), LipschitzWith K f →
    ∃ (Y : Set (Ambient n ℓ)) (C : ℕ → Set (EuclideanSpace ℝ (Fin n))),
      (μHE[n] : Measure (Ambient n ℓ)) Y = 0 ∧ Set.range f ⊆ Y ∪ ⋃ i, f '' C i ∧
      ∀ i, IsCompact (C i) ∧
        (∀ w ∈ C i, DifferentiableAt ℝ f w ∧ Function.Injective (fderiv ℝ f w)) ∧
        ContinuousOn (fderiv ℝ f) (C i) ∧
        ∃ c : ℝ, 0 < c ∧ ∀ v ∈ C i, ∀ w ∈ C i, c * ‖v - w‖ ≤ ‖f v - f w‖ := by
  intro n ℓ K f hf
  -- Bounded Borel pieces `T_p` of the regular set `R`, with lower Lipschitz bounds.
  obtain ⟨T, hRT, hT⟩ := Submission.regular_set_lower_lipschitz_cover n ℓ f hf.continuous
  -- `T_p` has finite measure and `Df` is Borel, so Lusin gives compacta `D_{p,q} ⊆ T_p` on
  -- which `Df` is continuous, exhausting `T_p` up to a Lebesgue-null set.
  choose D hD hDnull using fun p ↦
    Submission.lusin_compact_exhaustion_of_measurable n (fderiv ℝ f) (T p)
      (measurable_fderiv ℝ f) (hT p).1 (hT p).2.1.measure_lt_top.ne
  -- `Y = f(ℝⁿ \ R) ∪ f(Z)` with `Z = ⋃_p (T_p \ ⋃_q D_{p,q})`; the pieces are `D_{Nat.unpair i}`.
  refine ⟨f '' (univ \ {w | DifferentiableAt ℝ f w ∧ Function.Injective (fderiv ℝ f w)}) ∪
      f '' ⋃ p, (T p \ ⋃ q, D p q), fun i ↦ D (Nat.unpair i).1 (Nat.unpair i).2, ?_, ?_,
      fun i ↦ ?_⟩
  · refine measure_union_null ?_ ?_
    · -- The area formula: the image of the non-regular set is `Hⁿ`-null.
      have h := Poincare.SimonGMT.Chapter02.area_image_compl_regularSet_eq_zero hf univ
      rwa [finrank_euclideanSpace_fin] at h
    · -- Ch. 2, 1.8(i): `Hⁿ(f(Z)) ≤ Kⁿ Hⁿ(Z) = Kⁿ Lⁿ(Z) = 0`.
      have h := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
        (hf.lipschitzOnWith (s := ⋃ p, (T p \ ⋃ q, D p q)))
      rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume n, measure_iUnion_null hDnull,
        mul_zero] at h
      exact nonpos_iff_eq_zero.1 h
  · rintro _ ⟨w, rfl⟩
    by_cases hw : w ∈ {w | DifferentiableAt ℝ f w ∧ Function.Injective (fderiv ℝ f w)}
    · obtain ⟨p, hp⟩ := mem_iUnion.1 (hRT hw)
      by_cases hq : w ∈ ⋃ q, D p q
      · obtain ⟨q, hq⟩ := mem_iUnion.1 hq
        refine mem_union_right _ (mem_iUnion.2 ⟨Nat.pair p q, ?_⟩)
        simpa only [Nat.unpair_pair] using mem_image_of_mem f hq
      · exact mem_union_left _ (mem_union_right _
          (mem_image_of_mem f (mem_iUnion.2 ⟨p, mem_sdiff_of_mem hp hq⟩)))
    · exact mem_union_left _ (mem_union_left _
        (mem_image_of_mem f (mem_sdiff_of_mem (mem_univ w) hw)))
  · -- Each piece inherits the properties of `D_{p,q} ⊆ T_p`.
    obtain ⟨hcpt, hsub, hcont⟩ := hD (Nat.unpair i).1 (Nat.unpair i).2
    obtain ⟨-, -, hreg, c, hc, hlow⟩ := hT (Nat.unpair i).1
    exact ⟨hcpt, fun w hw ↦ hreg w (hsub hw), hcont, c, hc,
      fun v hv w hw ↦ hlow v (hsub hv) w (hsub hw)⟩

theorem main_theorem : ApproxTangentAE ∧ FirstVariationFormula ∧ StationaryIffVariational ∧ StationaryMonotonicity ∧ StationaryDensity ∧ CanonicalRepresentative ∧ BoundedCurvatureMonotonicity ∧ LogarithmicMonotonicityError ∧ LpMonotonicity ∧ LpDensity ∧ LpSupportRepresentation ∧ PoincareInequality ∧ SobolevInequality ∧ SupportInBall ∧ ConvexHullProperty ∧ ClassicalTangent := by sorry

/-- **Lipschitz pieces of a countably `n`-rectifiable set** (Ch. 3, 1.1, with Rademacher, the
area formula and Lusin in place of the `C¹` cover of Ch. 3, 1.2). Up to a Borel `Hⁿ`-null set
`N₀`, `M` is covered by countably many images `F_i(C_i)` of compact sets under Lipschitz maps
that are differentiable on `C_i` with injective, continuous derivative and satisfy a lower
Lipschitz bound there. Each parametrization of 1.1 is split by `lipschitz_range_piece_cover`;
the pieces are re-indexed by `Nat.pair`. -/
theorem Submission.rectifiable_lipschitz_piece_cover : ∀ (n ℓ : ℕ) (M : Set (Ambient n ℓ)),
    0 < n → Poincare.SimonGMT.Chapter03.CountablyRectifiable n M →
    ∃ (N₀ : Set (Ambient n ℓ)) (C : ℕ → Set (EuclideanSpace ℝ (Fin n)))
      (F : ℕ → EuclideanSpace ℝ (Fin n) → Ambient n ℓ),
      MeasurableSet N₀ ∧ (μHE[n] : Measure (Ambient n ℓ)) N₀ = 0 ∧ M ⊆ N₀ ∪ ⋃ i, F i '' C i ∧
      ∀ i, IsCompact (C i) ∧ (∃ K : NNReal, LipschitzWith K (F i)) ∧
        (∀ w ∈ C i, DifferentiableAt ℝ (F i) w ∧ Function.Injective (fderiv ℝ (F i) w)) ∧
        ContinuousOn (fderiv ℝ (F i)) (C i) ∧
        ∃ c : ℝ, 0 < c ∧ ∀ v ∈ C i, ∀ w ∈ C i, c * ‖v - w‖ ≤ ‖F i v - F i w‖ := by
  intro n ℓ M _hn hM
  -- 1.1: `M ⊆ M₀ ∪ ⋃_j G_j(ℝⁿ)` with `Hⁿ(M₀) = 0` and `G_j` Lipschitz with constant `K_j`.
  obtain ⟨M₀, hM₀, G, hG, hMcover⟩ := hM
  choose K hK using hG
  -- Every `G_j(ℝⁿ)` lies in `Y_j ∪ ⋃_q G_j(D_{j,q})` with `Hⁿ(Y_j) = 0`.
  choose Y D hY hrange hD using fun j ↦
    Submission.lipschitz_range_piece_cover n ℓ (K j) (G j) (hK j)
  -- A Borel `Hⁿ`-null hull `N₀` of `M₀ ∪ ⋃_j Y_j`.
  obtain ⟨N₀, hN₀sub, hN₀meas, hN₀null⟩ :=
    exists_measurable_superset_of_null (measure_union_null hM₀ (measure_iUnion_null hY))
  refine ⟨N₀, fun i ↦ D (Nat.unpair i).1 (Nat.unpair i).2, fun i ↦ G (Nat.unpair i).1,
    hN₀meas, hN₀null, ?_, fun i ↦ ?_⟩
  · intro x hx
    rcases hMcover hx with hx₀ | hx
    · exact mem_union_left _ (hN₀sub (mem_union_left _ hx₀))
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    rcases hrange j hj with hxY | hxD
    · exact mem_union_left _ (hN₀sub (mem_union_right _ (mem_iUnion.2 ⟨j, hxY⟩)))
    obtain ⟨q, hq⟩ := mem_iUnion.mp hxD
    refine mem_union_right _ (mem_iUnion.2 ⟨Nat.pair j q, ?_⟩)
    simpa only [Nat.unpair_pair] using hq
  · obtain ⟨hcpt, hdiff, hcont, hlower⟩ := hD (Nat.unpair i).1 (Nat.unpair i).2
    exact ⟨hcpt, ⟨K _, hK _⟩, hdiff, hcont, hlower⟩

end

end GMT.Ch04
