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
/-- Simon 2.1 (p. 87): first-order regularity of a family as in 2.1. The initial velocity
`X = ∂φ_t/∂t|_{t=0}` is `C¹` with `DX = 0` off `K`, and each `φ_t` (`|t| < ε`) is `C¹` and
Lipschitz. -/
theorem Submission.ts_fv_cv_first_order_regularity : ∀ (n ℓ : ℕ) (φ : ℝ → Ambient n ℓ → Ambient n ℓ) (ε : ℝ) (K : Set (Ambient n ℓ)), IsCompactVariation φ ε K → ContDiff ℝ 1 (fun y ↦ deriv (fun t ↦ φ t y) 0) ∧ (∀ y ∉ K, fderiv ℝ (fun y ↦ deriv (fun t ↦ φ t y) 0) y = 0) ∧ (∀ t ∈ Ioo (-ε) ε, (∃ L : NNReal, LipschitzWith L (φ t)) ∧ ContDiff ℝ 1 (φ t)) := by
  intro n ℓ φ ε K hφ
  -- `Φ(q) = φ q.1 q.2` is `C^∞` on the open set `S = (-ε, ε) × ℝ^{n+ℓ}`; `Kᶜ` is open.
  have hS : IsOpen (Ioo (-ε) ε ×ˢ (univ : Set (Ambient n ℓ))) := isOpen_Ioo.prod isOpen_univ
  have hmem : ∀ t ∈ Ioo (-ε) ε, ∀ y : Ambient n ℓ,
      (t, y) ∈ Ioo (-ε) ε ×ˢ (univ : Set (Ambient n ℓ)) :=
    fun t ht y ↦ ⟨ht, mem_univ y⟩
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_lt_zero.mpr hφ.pos, hφ.pos⟩
  have hKc : IsOpen Kᶜ := hφ.compact.isClosed.isOpen_compl
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
      (hφ.smooth.contDiffAt (hS.mem_nhds (hmem 0 h0 y))).differentiableAt (by simp)
    have hg : HasDerivAt (fun t : ℝ ↦ (t, y)) ((1 : ℝ), (0 : Ambient n ℓ)) 0 :=
      (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) y)
    exact (hdiff.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hg).deriv
  -- (a) `DΦ` is `C¹` on `S`, so `y ↦ DΦ(0, y)(1, 0)` is `C¹`.
  have ha : ContDiff ℝ 1 (fun y ↦ deriv (fun t ↦ φ t y) 0) := by
    have h1 : ContDiffOn ℝ 1 (fderiv ℝ (fun q : ℝ × Ambient n ℓ ↦ φ q.1 q.2))
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
      exact h1.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun y _ ↦ hmem 0 h0 y)
    simp_rw [hvel]
    exact h2.clm_apply contDiff_const
  -- Off `K`, `t ↦ φ t y` is constant near `0`, so `X(y) = 0`.
  have hzero : ∀ y ∉ K, deriv (fun t ↦ φ t y) 0 = 0 := by
      exact h1.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun y _ ↦ hmem y)
    simp_rw [hvel]
    exact h2.clm_apply contDiff_const
  -- Off `K`, `t ↦ φ t y` is constant near `0`, so `X(y) = 0`.
  have hzero : ∀ y, y ∉ K → deriv (fun t ↦ φ t y) 0 = 0 := by
    intro y hy
    have : (fun t ↦ φ t y) =ᶠ[𝓝 0] fun _ ↦ y := by
      filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr hφ.pos) hφ.pos] with t ht
      exact hφ.fixed t ht y hy
    rw [this.deriv_eq, deriv_const]
  refine ⟨ha, fun y hy ↦ ?_, fun t ht ↦ ?_⟩
  -- (b) `X = 0` on the open neighbourhood `Kᶜ` of `y`, so `DX(y) = 0`.
  · have : (fun y ↦ deriv (fun t ↦ φ t y) 0) =ᶠ[𝓝 y] fun _ ↦ (0 : Ambient n ℓ) := by
      filter_upwards [hKc.mem_nhds hy] with z hz
      exact hzero z hz
    rw [this.fderiv_eq, fderiv_const_apply]
  -- (c) `φ t = Φ ∘ (y ↦ (t, y))` is `C^∞`.
  have hsm : ContDiff ℝ ∞ (φ t) := by
    rw [contDiff_iff_contDiffAt]
    intro y
    exact (hφ.smooth.contDiffAt (hS.mem_nhds (hmem t ht y))).comp y
      (contDiffAt_const.prodMk contDiffAt_id)
  have hC1 : ContDiff ℝ 1 (φ t) := hsm.of_le (WithTop.coe_le_coe.mpr le_top)
  -- `Dφ_t = I` off `K`, so `‖Dφ_t‖ ≤ 1` there.
  have hout : ∀ y ∉ K, ‖fderiv ℝ (φ t) y‖ ≤ 1 := by
    intro y hy
    have : φ t =ᶠ[𝓝 y] id := by
      filter_upwards [hKc.mem_nhds hy] with z hz
      exact hφ.fixed t ht z hz
    rw [this.fderiv_eq, fderiv_id]
    exact ContinuousLinearMap.norm_id_le
  -- `Dφ_t` is continuous, hence bounded on the compact set `K`.
  obtain ⟨L₀, hL₀⟩ :=
    hφ.compact.exists_bound_of_continuousOn (hC1.continuous_fderiv one_ne_zero).continuousOn
  -- Mean value inequality with `‖Dφ_t‖ ≤ max L₀ 1`.
  let L : NNReal := ⟨max L₀ 1, zero_le_one.trans (le_max_right _ _)⟩
  refine ⟨⟨L, lipschitzWith_of_nnnorm_fderiv_le (hC1.differentiable one_ne_zero) fun y ↦ ?_⟩, hC1⟩
  rw [← NNReal.coe_le_coe, coe_nnnorm]
  change ‖fderiv ℝ (φ t) y‖ ≤ max L₀ 1
  by_cases hy : y ∈ K
  · exact (hL₀ y hy).trans (le_max_left _ _)
  · exact (hout y hy).trans (le_max_right _ _)
/-- Simon 2.1 (p. 87): for a family as in 2.1 and `0 < δ < ε`, the spatial derivatives
`Dφ_t(x)` (`|t| < δ`, `x ∈ ℝ^{n+ℓ}`) and their inverses are bounded uniformly:
`‖Dφ_t(x)‖ ≤ B` and `|v| ≤ B |Dφ_t(x) v|`. -/
theorem Submission.ts_fv_cv_slice_fderiv_bounds : ∀ (n ℓ : ℕ) (φ : ℝ → Ambient n ℓ → Ambient n ℓ) (ε : ℝ) (K : Set (Ambient n ℓ)), IsCompactVariation φ ε K → ∀ δ : ℝ, 0 < δ → δ < ε → ∃ B : ℝ, ∀ x, ∀ t ∈ Ioo (-δ) δ, ‖fderiv ℝ (φ t) x‖ ≤ B ∧ ∀ v, ‖v‖ ≤ B * ‖fderiv ℝ (φ t) x v‖ := by
  intro n ℓ φ ε K hφ δ hδ hδε
  have hU : IsOpen (Ioo (-ε) ε ×ˢ (univ : Set (Ambient n ℓ))) := isOpen_Ioo.prod isOpen_univ
  -- Chain rule along `y ↦ (t, y)`: `Dφ_t(y) = DΦ(t, y) ∘ ι₂` for `t ∈ (-ε, ε)`.
  have hslice : ∀ t ∈ Ioo (-ε) ε, ∀ y : Ambient n ℓ, HasFDerivAt (φ t)
      ((fderiv ℝ (fun q : ℝ × Ambient n ℓ ↦ φ q.1 q.2) (t, y)).comp
        (ContinuousLinearMap.inr ℝ ℝ (Ambient n ℓ))) y := by
    intro t ht y
    have hdiff : DifferentiableAt ℝ (fun q : ℝ × Ambient n ℓ ↦ φ q.1 q.2) (t, y) :=
      (hφ.smooth.contDiffAt (hU.mem_nhds ⟨ht, mem_univ _⟩)).differentiableAt (by simp)
    exact hdiff.hasFDerivAt.comp y ((hasFDerivAt_const t y).prodMk (hasFDerivAt_id y))
  -- `G(q) = Dφ_{q.1}(q.2)` is continuous on `U = (-ε, ε) × ℝ^{n+ℓ}`.
  have hG : ContinuousOn (fun q : ℝ × Ambient n ℓ ↦ fderiv ℝ (φ q.1) q.2)
      (Ioo (-ε) ε ×ˢ univ) := by
    have h1 := (hφ.smooth.continuousOn_fderiv_of_isOpen hU (by simp)).clm_comp
      (continuousOn_const (c := ContinuousLinearMap.inr ℝ ℝ (Ambient n ℓ)))
    refine h1.congr ?_
    rintro ⟨t, y⟩ ⟨ht, -⟩
    exact (hslice t ht y).fderiv
  -- `Dφ_t(x)` is a unit of `L(ℝ^{n+ℓ}, ℝ^{n+ℓ})`, with inverse `Dψ(φ_t x)`, `ψ = φ_t⁻¹`.
  have hunit : ∀ t ∈ Ioo (-ε) ε, ∀ x : Ambient n ℓ, IsUnit (fderiv ℝ (φ t) x) := by
    intro t ht x
    obtain ⟨hbij, hψ⟩ := hφ.diffeo t ht
    have hleft : ∀ y, Function.invFun (φ t) (φ t y) = y :=
      Function.leftInverse_invFun hbij.injective
    have hright : ∀ y, φ t (Function.invFun (φ t) y) = y :=
      Function.rightInverse_invFun hbij.surjective
    have hdφ : HasFDerivAt (φ t) (fderiv ℝ (φ t) x) x :=
      (hslice t ht x).differentiableAt.hasFDerivAt
    have hdψ : HasFDerivAt (Function.invFun (φ t))
        (fderiv ℝ (Function.invFun (φ t)) (φ t x)) (φ t x) :=
      (hψ.differentiable (by simp) (φ t x)).hasFDerivAt
    have h1 : (fderiv ℝ (Function.invFun (φ t)) (φ t x)).comp (fderiv ℝ (φ t) x) =
        ContinuousLinearMap.id ℝ (Ambient n ℓ) := by
      have hcomp := hdψ.comp x hdφ
      rw [show Function.invFun (φ t) ∘ φ t = id from funext hleft] at hcomp
      exact hcomp.unique (hasFDerivAt_id x)
    have h2 : (fderiv ℝ (φ t) x).comp (fderiv ℝ (Function.invFun (φ t)) (φ t x)) =
        ContinuousLinearMap.id ℝ (Ambient n ℓ) := by
      have hdφ' : HasFDerivAt (φ t) (fderiv ℝ (φ t) x) (Function.invFun (φ t) (φ t x)) := by
        rw [hleft]; exact hdφ
      have hcomp := hdφ'.comp (φ t x) hdψ
      rw [show φ t ∘ Function.invFun (φ t) = id from funext hright] at hcomp
      exact hcomp.unique (hasFDerivAt_id (φ t x))
    exact ⟨⟨fderiv ℝ (φ t) x, fderiv ℝ (Function.invFun (φ t)) (φ t x), h2, h1⟩, rfl⟩
  -- Off `K`, `φ_t = id` near the point, so `Dφ_t = I`.
  have hidK : ∀ t ∈ Ioo (-ε) ε, ∀ y ∉ K,
      fderiv ℝ (φ t) y = ContinuousLinearMap.id ℝ (Ambient n ℓ) := by
    intro t ht y hy
    have h : φ t =ᶠ[𝓝 y] id := by
      filter_upwards [hφ.compact.isClosed.isOpen_compl.mem_nhds hy] with z hz
      exact hφ.fixed t ht z hz
    rw [h.fderiv_eq, fderiv_id]
  -- The compact set `Q = [-δ, δ] × K ⊆ U`.
  have hQ : IsCompact (Icc (-δ) δ ×ˢ K) := isCompact_Icc.prod hφ.compact
  have hQU : Icc (-δ) δ ×ˢ K ⊆ Ioo (-ε) ε ×ˢ (univ : Set (Ambient n ℓ)) := by
    rintro ⟨t, y⟩ ⟨⟨h1, h2⟩, -⟩
    exact ⟨⟨by linarith, by linarith⟩, mem_univ _⟩
  -- `Ring.inverse ∘ G` is continuous on `Q`, since `Ring.inverse` is continuous at units.
  have hInv : ContinuousOn (fun q : ℝ × Ambient n ℓ ↦ Ring.inverse (fderiv ℝ (φ q.1) q.2))
      (Icc (-δ) δ ×ˢ K) := by
    intro q hq
    have hu : IsUnit (fderiv ℝ (φ q.1) q.2) := hunit q.1 (hQU hq).1 q.2
    have hcont : ContinuousAt Ring.inverse (fderiv ℝ (φ q.1) q.2) := by
      simpa only [hu.unit_spec] using NormedRing.inverse_continuousAt hu.unit
    exact hcont.comp_continuousWithinAt (f := fun q : ℝ × Ambient n ℓ ↦ fderiv ℝ (φ q.1) q.2)
      ((hG q (hQU hq)).mono hQU)
  obtain ⟨B₁, hB₁⟩ := hQ.exists_bound_of_continuousOn (hG.mono hQU)
  obtain ⟨B₃, hB₃⟩ := hQ.exists_bound_of_continuousOn hInv
  refine ⟨max 1 (max B₁ B₃), fun x t ht ↦ ?_⟩
  have htε : t ∈ Ioo (-ε) ε := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  by_cases hx : x ∈ K
  · have hq : (t, x) ∈ Icc (-δ) δ ×ˢ K := ⟨⟨ht.1.le, ht.2.le⟩, hx⟩
    have hb1 : ‖fderiv ℝ (φ t) x‖ ≤ B₁ := hB₁ (t, x) hq
    have hb3 : ‖Ring.inverse (fderiv ℝ (φ t) x)‖ ≤ B₃ := hB₃ (t, x) hq
    refine ⟨hb1.trans ((le_max_left _ _).trans (le_max_right _ _)), fun v ↦ ?_⟩
    have hv : Ring.inverse (fderiv ℝ (φ t) x) (fderiv ℝ (φ t) x v) = v := by
      change (Ring.inverse (fderiv ℝ (φ t) x) * fderiv ℝ (φ t) x) v = v
      rw [Ring.inverse_mul_cancel _ (hunit t htε x)]
      rfl
    calc ‖v‖ = ‖Ring.inverse (fderiv ℝ (φ t) x) (fderiv ℝ (φ t) x v)‖ := by rw [hv]
      _ ≤ ‖Ring.inverse (fderiv ℝ (φ t) x)‖ * ‖fderiv ℝ (φ t) x v‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ max 1 (max B₁ B₃) * ‖fderiv ℝ (φ t) x v‖ :=
        mul_le_mul_of_nonneg_right (hb3.trans ((le_max_right _ _).trans (le_max_right _ _)))
          (norm_nonneg _)
  · rw [hidK t htε x hx]
    exact ⟨ContinuousLinearMap.norm_id_le.trans (le_max_left _ _),
      fun v ↦ le_mul_of_one_le_left (norm_nonneg _) (le_max_left _ _)⟩
theorem Submission.ts_fv_cv_slice_fderiv_time_deriv : ∀ (n ℓ : ℕ) (φ : ℝ → Ambient n ℓ → Ambient n ℓ) (ε : ℝ) (K : Set (Ambient n ℓ)), IsCompactVariation φ ε K → ∃ Λ' : ℝ → Ambient n ℓ → (Ambient n ℓ →L[ℝ] Ambient n ℓ), (∀ x, Λ' 0 x = fderiv ℝ (fun y ↦ deriv (fun t ↦ φ t y) 0) x ∧ ∀ t ∈ Ioo (-ε) ε, HasDerivAt (fun s ↦ fderiv ℝ (φ s) x) (Λ' t x) t) ∧ ∀ δ : ℝ, 0 < δ → δ < ε → ∃ B : ℝ, ∀ x, ∀ t ∈ Ioo (-δ) δ, ‖Λ' t x‖ ≤ B := by
  intro n ℓ φ ε K hφ
  obtain ⟨hε, hK, hsm, -, -, hfix⟩ := hφ
  -- Step 1. `Φ(t, y) = φ t y` is `C^∞` on the open set `U = (-ε, ε) × ℝ^{n+ℓ}`.
  set Φ : ℝ × Ambient n ℓ → Ambient n ℓ := fun q ↦ φ q.1 q.2
  set U : Set (ℝ × Ambient n ℓ) := Ioo (-ε) ε ×ˢ univ
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_univ
  have hmem : ∀ t ∈ Ioo (-ε) ε, ∀ y : Ambient n ℓ, ((t, y) : ℝ × Ambient n ℓ) ∈ U :=
    fun t ht y ↦ Set.mk_mem_prod ht (mem_univ y)
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hD1 : ContDiffOn ℝ ∞ (fderiv ℝ Φ) U := hsm.fderiv_of_isOpen hU (by simp)
  have hΦd : ∀ q ∈ U, HasFDerivAt Φ (fderiv ℝ Φ q) q := fun q hq ↦
    ((hsm.contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp)).hasFDerivAt
  have hD1d : ∀ q ∈ U, HasFDerivAt (fderiv ℝ Φ) (fderiv ℝ (fderiv ℝ Φ) q) q := fun q hq ↦
    ((hD1.contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp)).hasFDerivAt
  have hD2c : ContinuousOn (fderiv ℝ (fderiv ℝ Φ)) U :=
    hD1.continuousOn_fderiv_of_isOpen hU (by simp)
  -- Step 6(iii). Symmetry of `D²Φ` on `U`, from the mean value inequality and the continuity
  -- of `D²Φ` (`ContDiffAt.isSymmSndFDerivAt` is not reachable from the frozen imports).
  have hsymm : ∀ p ∈ U, ∀ a b : ℝ × Ambient n ℓ,
      fderiv ℝ (fderiv ℝ Φ) p a b = fderiv ℝ (fderiv ℝ Φ) p b a := by
    intro p hp a b
    rw [← sub_eq_zero, ← norm_le_zero_iff]
    refine le_of_forall_pos_le_add fun η hη ↦ ?_
    rw [zero_add]
    obtain ⟨η', hη'pos, hη'le⟩ : ∃ η' : ℝ, 0 < η' ∧ 2 * η' * (‖a‖ * ‖b‖) ≤ η := by
      have hm : 0 < ‖a‖ * ‖b‖ + 1 := by positivity
      refine ⟨η / 2 / (‖a‖ * ‖b‖ + 1), by positivity, ?_⟩
      calc 2 * (η / 2 / (‖a‖ * ‖b‖ + 1)) * (‖a‖ * ‖b‖)
          = η * (‖a‖ * ‖b‖) / (‖a‖ * ‖b‖ + 1) := by ring
        _ ≤ η := by rw [div_le_iff₀ hm]; nlinarith
    obtain ⟨r₁, hr₁, hr₁U⟩ := Metric.isOpen_iff.1 hU p hp
    have hball : ball (fderiv ℝ (fderiv ℝ Φ) p) η' ∈ 𝓝 (fderiv ℝ (fderiv ℝ Φ) p) :=
      ball_mem_nhds (fderiv ℝ (fderiv ℝ Φ) p) hη'pos
    obtain ⟨r₂, hr₂, hr₂c⟩ := Metric.mem_nhds_iff.1 (hD2c.continuousAt (hU.mem_nhds hp) hball)
    obtain ⟨r, hr0, hrU, hrc⟩ : ∃ r : ℝ, 0 < r ∧ ball p r ⊆ U ∧
        ∀ q ∈ ball p r, ‖fderiv ℝ (fderiv ℝ Φ) q - fderiv ℝ (fderiv ℝ Φ) p‖ ≤ η' := by
      refine ⟨min r₁ r₂, lt_min hr₁ hr₂, (ball_subset_ball (min_le_left _ _)).trans hr₁U,
        fun q hq ↦ ?_⟩
      have hq2 : fderiv ℝ (fderiv ℝ Φ) q ∈ ball (fderiv ℝ (fderiv ℝ Φ) p) η' :=
        hr₂c (ball_subset_ball (min_le_right _ _) hq)
      exact ((mem_ball_iff_norm (E := ℝ × Ambient n ℓ →L[ℝ] ℝ × Ambient n ℓ →L[ℝ] Ambient n ℓ)).1
        hq2).le
    have hmvt : ∀ y ∈ ball p r, ∀ z ∈ ball p r,
        ‖fderiv ℝ Φ z - fderiv ℝ Φ y - fderiv ℝ (fderiv ℝ Φ) p (z - y)‖ ≤ η' * ‖z - y‖ :=
      fun y hy z hz ↦ (convex_ball p r).norm_image_sub_le_of_norm_hasFDerivWithin_le'
        (fun q hq ↦ (hD1d q (hrU hq)).hasFDerivWithinAt) hrc hy hz
    -- second differences: `Φ(p+k+l) - Φ(p+k) - Φ(p+l) + Φ(p) = D²Φ(p) l k + O(η' |k| |l|)`
    have hstep : ∀ k l : ℝ × Ambient n ℓ, ‖k‖ < r / 2 → ‖l‖ < r / 2 →
        ‖Φ (p + k + l) - Φ (p + k) - (Φ (p + l) - Φ p) - fderiv ℝ (fderiv ℝ Φ) p l k‖ ≤
          η' * ‖l‖ * ‖k‖ := by
      intro k l hk hl
      have hsub : ∀ y ∈ ball p (r / 2), y ∈ ball p r ∧ y + l ∈ ball p r := by
        intro y hy
        rw [mem_ball_iff_norm] at hy
        refine ⟨mem_ball_iff_norm.2 (by linarith), mem_ball_iff_norm.2 ?_⟩
        calc ‖y + l - p‖ = ‖(y - p) + l‖ := by congr 1; abel
          _ ≤ ‖y - p‖ + ‖l‖ := norm_add_le _ _
          _ < r := by linarith
      have hψ : ∀ y ∈ ball p (r / 2), HasFDerivWithinAt (fun y ↦ Φ (y + l) - Φ y)
          (fderiv ℝ Φ (y + l) - fderiv ℝ Φ y) (ball p (r / 2)) y := by
        intro y hy
        have h1 : HasFDerivAt (fun y ↦ Φ (y + l)) (fderiv ℝ Φ (y + l)) y :=
          (hasFDerivAt_comp_add_right l).2 (hΦd (y + l) (hrU (hsub y hy).2))
        exact (h1.sub (hΦd y (hrU (hsub y hy).1))).hasFDerivWithinAt
      have hbd : ∀ y ∈ ball p (r / 2), ‖fderiv ℝ Φ (y + l) - fderiv ℝ Φ y -
          fderiv ℝ (fderiv ℝ Φ) p l‖ ≤ η' * ‖l‖ := by
        intro y hy
        have h := hmvt y (hsub y hy).1 (y + l) (hsub y hy).2
        rwa [add_sub_cancel_left] at h
      have hpk : p + k ∈ ball p (r / 2) := by
        rw [mem_ball_iff_norm, add_sub_cancel_left]
        exact hk
      have h := (convex_ball p (r / 2)).norm_image_sub_le_of_norm_hasFDerivWithin_le' hψ hbd
        (mem_ball_self (half_pos hr0)) hpk
      rwa [add_sub_cancel_left] at h
    -- rescale `a`, `b` into the ball and compare the two orders
    obtain ⟨c, hcpos, hca, hcb⟩ : ∃ c : ℝ, 0 < c ∧ ‖c • a‖ < r / 2 ∧ ‖c • b‖ < r / 2 := by
      have hs : 0 < ‖a‖ + ‖b‖ + 1 := by positivity
      have hc0 : 0 < r / 2 / (‖a‖ + ‖b‖ + 1) := by positivity
      refine ⟨r / 2 / (‖a‖ + ‖b‖ + 1), hc0, ?_, ?_⟩ <;>
        rw [norm_smul, Real.norm_of_nonneg hc0.le, div_mul_eq_mul_div, div_lt_iff₀ hs] <;>
        nlinarith [norm_nonneg a, norm_nonneg b, half_pos hr0]
    have h1 := hstep (c • a) (c • b) hca hcb
    have h2 := hstep (c • b) (c • a) hcb hca
    rw [add_right_comm p (c • b) (c • a)] at h2
    have hcc : 0 < c * c := mul_pos hcpos hcpos
    have e1 : fderiv ℝ (fderiv ℝ Φ) p (c • a) (c • b) - fderiv ℝ (fderiv ℝ Φ) p (c • b) (c • a) =
        (c * c) • (fderiv ℝ (fderiv ℝ Φ) p a b - fderiv ℝ (fderiv ℝ Φ) p b a) := by
      simp only [map_smul, smul_apply, smul_sub, smul_smul]
    have e2 : fderiv ℝ (fderiv ℝ Φ) p (c • a) (c • b) - fderiv ℝ (fderiv ℝ Φ) p (c • b) (c • a) =
        (Φ (p + c • a + c • b) - Φ (p + c • a) - (Φ (p + c • b) - Φ p) -
            fderiv ℝ (fderiv ℝ Φ) p (c • b) (c • a)) -
          (Φ (p + c • a + c • b) - Φ (p + c • b) - (Φ (p + c • a) - Φ p) -
            fderiv ℝ (fderiv ℝ Φ) p (c • a) (c • b)) := by
      abel
    have hle : c * c * ‖fderiv ℝ (fderiv ℝ Φ) p a b - fderiv ℝ (fderiv ℝ Φ) p b a‖ ≤
        c * c * (2 * η' * (‖a‖ * ‖b‖)) :=
      calc c * c * ‖fderiv ℝ (fderiv ℝ Φ) p a b - fderiv ℝ (fderiv ℝ Φ) p b a‖
          = ‖fderiv ℝ (fderiv ℝ Φ) p (c • a) (c • b) -
              fderiv ℝ (fderiv ℝ Φ) p (c • b) (c • a)‖ := by
            rw [e1, norm_smul, Real.norm_of_nonneg hcc.le]
        _ ≤ η' * ‖c • b‖ * ‖c • a‖ + η' * ‖c • a‖ * ‖c • b‖ := by
            rw [e2]
            exact (norm_sub_le _ _).trans (add_le_add h1 h2)
        _ = c * c * (2 * η' * (‖a‖ * ‖b‖)) := by
            rw [norm_smul, norm_smul, Real.norm_of_nonneg hcpos.le]
            ring
    exact (le_of_mul_le_mul_left hle hcc).trans hη'le
  -- Step 3. Time slices: `D(φ s)(y) = DΦ(s, y) ∘ ι₂` for `s ∈ (-ε, ε)`.
  have hslice : ∀ s ∈ Ioo (-ε) ε, ∀ y : Ambient n ℓ,
      fderiv ℝ (φ s) y = (fderiv ℝ Φ (s, y)).comp (ContinuousLinearMap.inr ℝ ℝ (Ambient n ℓ)) := by
    intro s hs y
    have h := (hΦd (s, y) (hmem s hs y)).comp y (hasFDerivAt_prodMk_right s y)
    exact h.fderiv
  -- Step 4. `Λ'(t, x) = D²Φ(t, x)(1, 0) ∘ ι₂`, i.e. `DG(t, x)(1, 0)` for `G(q) = DΦ(q) ∘ ι₂`.
  refine ⟨fun t x ↦ (fderiv ℝ (fderiv ℝ Φ) (t, x) ((1 : ℝ), (0 : Ambient n ℓ))).comp
      (ContinuousLinearMap.inr ℝ ℝ (Ambient n ℓ)), fun x ↦ ⟨?_, fun t ht ↦ ?_⟩, fun δ hδ hδε ↦ ?_⟩
  · -- Step 6. `Λ'(0, x) = DX(x)`, by the symmetry of `D²Φ(0, x)`.
    have hX : (fun y ↦ deriv (fun t ↦ φ t y) 0) =
        fun y ↦ fderiv ℝ Φ ((0 : ℝ), y) ((1 : ℝ), (0 : Ambient n ℓ)) := by
      funext y
      have hk : HasDerivAt (fun t : ℝ ↦ (t, y)) ((1 : ℝ), (0 : Ambient n ℓ)) 0 :=
        (hasDerivAt_id' (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) y)
      have h := HasFDerivAt.comp_hasDerivAt (l := Φ) (f := fun t : ℝ ↦ (t, y)) (0 : ℝ)
        (hΦd ((0 : ℝ), y) (hmem 0 h0 y)) hk
      exact h.deriv
    have hc : HasFDerivAt (fun y : Ambient n ℓ ↦ fderiv ℝ Φ ((0 : ℝ), y))
        ((fderiv ℝ (fderiv ℝ Φ) ((0 : ℝ), x)).comp
          (ContinuousLinearMap.inr ℝ ℝ (Ambient n ℓ))) x := by
      have h := (hD1d ((0 : ℝ), x) (hmem 0 h0 x)).comp x (hasFDerivAt_prodMk_right (0 : ℝ) x)
      exact h
    have hXd : HasFDerivAt (fun y ↦ deriv (fun t ↦ φ t y) 0)
        (((fderiv ℝ (fderiv ℝ Φ) ((0 : ℝ), x)).comp
          (ContinuousLinearMap.inr ℝ ℝ (Ambient n ℓ))).flip ((1 : ℝ), (0 : Ambient n ℓ))) x := by
      rw [hX]
      have h := hc.clm_apply (hasFDerivAt_const ((1 : ℝ), (0 : Ambient n ℓ)) x)
      rw [ContinuousLinearMap.comp_zero, zero_add] at h
      exact h
    rw [hXd.fderiv]
    ext1 v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.inr_apply]
    exact hsymm _ (hmem 0 h0 x) _ _
  · -- Step 5. `s ↦ D(φ s)(x)` has derivative `Λ'(t, x)` at `t`.
    have hk : HasDerivAt (fun s : ℝ ↦ (s, x)) ((1 : ℝ), (0 : Ambient n ℓ)) t :=
      (hasDerivAt_id' t).prodMk (hasDerivAt_const t x)
    have h1 : HasDerivAt (fun s ↦ fderiv ℝ Φ (s, x))
        (fderiv ℝ (fderiv ℝ Φ) (t, x) ((1 : ℝ), (0 : Ambient n ℓ))) t := by
      have h := HasFDerivAt.comp_hasDerivAt (l := fderiv ℝ Φ) (f := fun s : ℝ ↦ (s, x)) t
        (hD1d (t, x) (hmem t ht x)) hk
      exact h
    have h2 := h1.clm_comp (hasDerivAt_const t (ContinuousLinearMap.inr ℝ ℝ (Ambient n ℓ)))
    rw [ContinuousLinearMap.comp_zero, add_zero] at h2
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact hslice s hs x
  · -- Step 8. Uniform bound: compactness of `[-δ, δ] × K`, and `Λ' = 0` off `K`.
    have hcont : ContinuousOn (fun q : ℝ × Ambient n ℓ ↦
        (fderiv ℝ (fderiv ℝ Φ) q ((1 : ℝ), (0 : Ambient n ℓ))).comp
          (ContinuousLinearMap.inr ℝ ℝ (Ambient n ℓ))) U :=
      (hD2c.clm_apply continuousOn_const).clm_comp continuousOn_const
    have hQU : Icc (-δ) δ ×ˢ K ⊆ U := fun q hq ↦
      Set.mem_prod.2 ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, mem_univ _⟩
    obtain ⟨B, hB⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn (hcont.mono hQU)
    refine ⟨max B 0, fun x t ht ↦ ?_⟩
    have htε : t ∈ Ioo (-ε) ε := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    by_cases hx : x ∈ K
    · exact (hB (t, x) (Set.mk_mem_prod (Ioo_subset_Icc_self ht) hx)).trans (le_max_left _ _)
    · have hW : IsOpen (Ioo (-ε) ε ×ˢ Kᶜ) := isOpen_Ioo.prod hK.isClosed.isOpen_compl
      have hev : fderiv ℝ Φ =ᶠ[𝓝 (t, x)] fun _ ↦ ContinuousLinearMap.snd ℝ ℝ (Ambient n ℓ) := by
        filter_upwards [hW.mem_nhds (Set.mk_mem_prod htε (Set.mem_compl hx))] with q hq
        have hq' : Φ =ᶠ[𝓝 q] Prod.snd := by
          filter_upwards [hW.mem_nhds hq] with q' hq'
          exact hfix q'.1 hq'.1 q'.2 hq'.2
        rw [hq'.fderiv_eq, fderiv_snd]
      have hD0 : fderiv ℝ (fderiv ℝ Φ) (t, x) = 0 := by
        rw [hev.fderiv_eq, fderiv_const_apply]
      simp only [hD0, zero_apply, ContinuousLinearMap.zero_comp, norm_zero]
      exact le_max_right _ _

/-- Simon 2.1 (p. 87): for a family `{φ_t}` as in 2.1 with initial velocity
`X = ∂φ_t/∂t|_{t=0}`, `X` is `C¹` with `DX = 0` off `K`, each `φ_t` is Lipschitz and `C¹`, and
for `|t| < δ = ε/2` the derivatives `Dφ_t(x)`, their time derivatives
`Λ'(t, x) = ∂_s Dφ_s(x)|_{s=t}` (with `Λ'(0, x) = DX(x)`) and the inverses of `Dφ_t(x)` are
bounded uniformly by `B`. -/
theorem Submission.ts_fv_compact_variation_bounds : ∀ (n ℓ : ℕ) (φ : ℝ → Ambient n ℓ → Ambient n ℓ) (ε : ℝ) (K : Set (Ambient n ℓ)), IsCompactVariation φ ε K → ContDiff ℝ 1 (fun y ↦ deriv (fun t ↦ φ t y) 0) ∧ (∀ y ∉ K, fderiv ℝ (fun y ↦ deriv (fun t ↦ φ t y) 0) y = 0) ∧ (∀ t ∈ Ioo (-ε) ε, (∃ L : NNReal, LipschitzWith L (φ t)) ∧ ContDiff ℝ 1 (φ t)) ∧ ∃ δ B : ℝ, 0 < δ ∧ δ < ε ∧ ∃ Λ' : ℝ → Ambient n ℓ → (Ambient n ℓ →L[ℝ] Ambient n ℓ), ∀ x, Λ' 0 x = fderiv ℝ (fun y ↦ deriv (fun t ↦ φ t y) 0) x ∧ ∀ t ∈ Ioo (-δ) δ, HasDerivAt (fun s ↦ fderiv ℝ (φ s) x) (Λ' t x) t ∧ ‖fderiv ℝ (φ t) x‖ ≤ B ∧ ‖Λ' t x‖ ≤ B ∧ ∀ v, ‖v‖ ≤ B * ‖fderiv ℝ (φ t) x v‖ := by
  intro n ℓ φ ε K hφ
  -- Parts (a)–(c): `X` is `C¹` with `DX = 0` off `K`; each `φ_t` is Lipschitz and `C¹`.
  obtain ⟨hX, hDX, hslice⟩ := Submission.ts_fv_cv_first_order_regularity n ℓ φ ε K hφ
  -- `Λ'(t, x) = ∂_s Dφ_s(x)|_{s=t}` on `(-ε, ε)`, `Λ'(0, x) = DX(x)`, bounded on each `|t| < δ`.
  obtain ⟨Λ', hΛ', hΛ'B⟩ := Submission.ts_fv_cv_slice_fderiv_time_deriv n ℓ φ ε K hφ
  -- Part (d) with `δ = ε/2` and `B = max B₁ B₂`, where `B₁` bounds `Dφ_t` and its inverse and
  -- `B₂` bounds `Λ'` on `|t| < ε/2`.
  have hδ : 0 < ε / 2 := half_pos hφ.pos
  have hδε : ε / 2 < ε := half_lt_self hφ.pos
  obtain ⟨B₁, hB₁⟩ := Submission.ts_fv_cv_slice_fderiv_bounds n ℓ φ ε K hφ (ε / 2) hδ hδε
  obtain ⟨B₂, hB₂⟩ := hΛ'B (ε / 2) hδ hδε
  refine ⟨hX, hDX, hslice, ε / 2, max B₁ B₂, hδ, hδε, Λ', fun x ↦ ⟨(hΛ' x).1, fun t ht ↦ ?_⟩⟩
  have htε : t ∈ Ioo (-ε) ε := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨hb, hv⟩ := hB₁ x t ht
  exact ⟨(hΛ' x).2 t htε, hb.trans (le_max_left _ _), (hB₂ x t ht).trans (le_max_right _ _),
    fun v ↦ (hv v).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))⟩
/-- **Tangential Jacobian as a Gram determinant.** Let `P ⊆ ℝᴺ` be a subspace with orthogonal
projection `p` and orthonormal basis `b₁, …, b_k`, and let `Λ : ℝᴺ → ℝᴺ` be linear. Then
`det (⟪Λ p eᵢ, Λ p eⱼ⟫ + ⟪eᵢ - p eᵢ, eⱼ - p eⱼ⟫)ᵢⱼ = det (⟪Λ b_a, Λ b_c⟫)_{a c}`. With
`B i a = ⟪eᵢ, b_a⟫` the left matrix is `1 + B (G Bᵀ - Bᵀ)`, `G` the right Gram matrix, and
`Bᵀ B = 1`, so `det (1 + X W) = det (1 + W X)` gives `det (1 + G - 1) = det G`. -/
theorem Submission.ts_fv_det_tangential_gram_eq : ∀ (N k : ℕ) (P : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (b : OrthonormalBasis (Fin k) ℝ P) (Λ : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)), Matrix.det (Matrix.of fun i j : Fin N ↦ inner ℝ (Λ (P.starProjection (EuclideanSpace.single i (1 : ℝ)))) (Λ (P.starProjection (EuclideanSpace.single j (1 : ℝ)))) + inner ℝ (EuclideanSpace.single i (1 : ℝ) - P.starProjection (EuclideanSpace.single i (1 : ℝ))) (EuclideanSpace.single j (1 : ℝ) - P.starProjection (EuclideanSpace.single j (1 : ℝ)))) = Matrix.det (Matrix.of fun a c : Fin k ↦ inner ℝ (Λ (b a)) (Λ (b c))) := by
  intro N k P b Λ
  -- `B i a = ⟪eᵢ, b_a⟫` is the `i`-th coordinate of `b_a`; `G` is the Gram matrix of `Λ b`
  set B : Matrix (Fin N) (Fin k) ℝ :=
    Matrix.of fun i a ↦ inner ℝ (EuclideanSpace.single i (1 : ℝ)) (b a : EuclideanSpace ℝ (Fin N))
  set G : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun a c ↦ inner ℝ (Λ (b a)) (Λ (b c))
  have hBl : ∀ i a, inner ℝ (EuclideanSpace.single i (1 : ℝ)) (b a : EuclideanSpace ℝ (Fin N)) =
      B i a := fun _ _ ↦ rfl
  have hBr : ∀ i a, inner ℝ (b a : EuclideanSpace ℝ (Fin N)) (EuclideanSpace.single i (1 : ℝ)) =
      B i a := fun _ _ ↦ real_inner_comm _ _
  have hG : ∀ a c, inner ℝ (Λ (b a)) (Λ (b c)) = G a c := fun _ _ ↦ rfl
  -- `p eᵢ = ∑ₐ B i a • b_a`
  have hp : ∀ i, P.starProjection (EuclideanSpace.single i (1 : ℝ)) =
      ∑ a, B i a • (b a : EuclideanSpace ℝ (Fin N)) := fun i ↦ by
    rw [b.starProjection_eq_sum_rankOne, sum_apply]
    exact Finset.sum_congr rfl fun a _ ↦ by rw [InnerProductSpace.rankOne_apply, hBr]
  -- `⟪b_a, b_c⟫ = δ_ac` and `⟪eᵢ, eⱼ⟫ = δᵢⱼ`
  have hb : ∀ a c, inner ℝ (b a : EuclideanSpace ℝ (Fin N)) (b c : EuclideanSpace ℝ (Fin N)) =
      if a = c then (1 : ℝ) else 0 := fun a c ↦ by
    rw [← Submodule.coe_inner]
    exact orthonormal_iff_ite.mp b.orthonormal a c
  have he : ∀ i j, inner ℝ (EuclideanSpace.single i (1 : ℝ))
      (EuclideanSpace.single j (1 : ℝ) : EuclideanSpace ℝ (Fin N)) = if i = j then (1 : ℝ) else 0 :=
    orthonormal_iff_ite.mp EuclideanSpace.orthonormal_single
  -- `Bᵀ B = 1`: Parseval in the standard basis `eᵢ` of `ℝᴺ`
  have hBB : B.transpose * B = 1 := by
    ext a c
    rw [Matrix.mul_apply, Matrix.one_apply, ← hb,
      ← (EuclideanSpace.basisFun (Fin N) ℝ).sum_inner_mul_inner]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [EuclideanSpace.basisFun_apply, hBr, hBl]; rfl
  -- entrywise, the left matrix is `B G Bᵀ + (1 - B Bᵀ) = 1 + B (G Bᵀ - Bᵀ)`
  have hS : (Matrix.of fun i j : Fin N ↦
      inner ℝ (Λ (P.starProjection (EuclideanSpace.single i (1 : ℝ))))
        (Λ (P.starProjection (EuclideanSpace.single j (1 : ℝ)))) +
      inner ℝ (EuclideanSpace.single i (1 : ℝ) - P.starProjection (EuclideanSpace.single i (1 : ℝ)))
        (EuclideanSpace.single j (1 : ℝ) - P.starProjection (EuclideanSpace.single j (1 : ℝ)))) =
      1 + B * (G * B.transpose - B.transpose) := by
    ext i j
    rw [Matrix.of_apply, hp i, hp j]
    simp only [map_sum, map_smul, inner_sum, sum_inner, real_inner_smul_left,
      real_inner_smul_right, inner_sub_left, inner_sub_right, hb, he, hBl, hBr, hG,
      Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply, Matrix.sub_apply,
      Matrix.transpose_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true, sub_self, Finset.sum_const_zero, sub_zero, mul_sub, Finset.mul_sum,
      Finset.sum_sub_distrib]
    have hswap : ∑ c, ∑ a, B j c * (B i a * G a c) = ∑ a, ∑ c, B i a * (G a c * B j c) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
    rw [hswap]
    ring
  -- Weinstein–Aronszajn `det (1 + X W) = det (1 + W X)`, then `Bᵀ B = 1`
  rw [hS, Matrix.det_one_add_mul_comm, Matrix.sub_mul, Matrix.mul_assoc, hBB, Matrix.mul_one,
    add_sub_cancel]

/-- **Area formula on one piece.** Let `F : ℝⁿ → ℝ^{n+ℓ}` be differentiable and injective on the
Borel set `C`, let `A ⊆ F(C)` be Borel, let `f` be injective and differentiable on `A`, and let
`P(F v) = range DF(v)` whenever `v ∈ C` and `F v ∈ A` (`F` and `f` are also Lipschitz). Then
`∫_{f(A)} w dHⁿ = ∫_A jac(Df(y), P(y)) · w(f(y)) dHⁿ(y)` for every weight `w`, where
`jac(Λ, Q) = √det (⟪Λ p eᵢ, Λ p eⱼ⟫ + ⟪eᵢ - p eᵢ, eⱼ - p eⱼ⟫)` with `p` the projection onto `Q`.
Both sides are computed on `B = C ∩ F⁻¹(A)` by the area formula for `f ∘ F` and for `F`, whose
Jacobians satisfy `J(f ∘ F) = (jac ∘ F) · J F`. -/
theorem Submission.ts_fv_piece_image_area_formula : ∀ (n ℓ : ℕ) (C : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → Ambient n ℓ) (f : Ambient n ℓ → Ambient n ℓ) (A : Set (Ambient n ℓ)) (P : Ambient n ℓ → Submodule ℝ (Ambient n ℓ)) (w : Ambient n ℓ → ℝ≥0∞), MeasurableSet C → (∃ L : NNReal, LipschitzWith L F) → (∀ v ∈ C, DifferentiableAt ℝ F v) → Set.InjOn F C → (∃ L : NNReal, LipschitzWith L f) → Set.InjOn f A → (∀ y ∈ A, DifferentiableAt ℝ f y) → MeasurableSet A → A ⊆ F '' C → (∀ v ∈ C, F v ∈ A → P (F v) = LinearMap.range (fderiv ℝ F v).toLinearMap) → ∫⁻ y in f '' A, w y ∂μHE[n] = ∫⁻ y in A, ENNReal.ofReal (Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (n + ℓ) ↦ inner ℝ (fderiv ℝ f y ((P y).starProjection (EuclideanSpace.single i (1 : ℝ)))) (fderiv ℝ f y ((P y).starProjection (EuclideanSpace.single j (1 : ℝ)))) + inner ℝ (EuclideanSpace.single i (1 : ℝ) - (P y).starProjection (EuclideanSpace.single i (1 : ℝ))) (EuclideanSpace.single j (1 : ℝ) - (P y).starProjection (EuclideanSpace.single j (1 : ℝ)))))) * w (f y) ∂μHE[n] := by
  intro n ℓ C F f A P w hC hFL hFd hFi _ hfi hfd hA hAC hP
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
  /- (Z) Images of sets where `Jl ∘ DΦ = 0` are `Hⁿ`-null: partition into pieces where `Φ` is
  close to a non-injective `DΦ(y)` and apply `B3` on bounded parts. -/
  have hZ : ∀ (Φ : EuclideanSpace ℝ (Fin n) → Ambient n ℓ) (s : Set (EuclideanSpace ℝ (Fin n))),
      MeasurableSet s → (∀ x ∈ s, DifferentiableAt ℝ Φ x) → (∀ x ∈ s, Jl (fderiv ℝ Φ x) = 0) →
      (μHE[n] : Measure (Ambient n ℓ)) (Φ '' s) = 0 := by
    intro Φ s hs hsd hs0
    have key : ∀ m : ℕ, (μHE[n] : Measure (Ambient n ℓ)) (Φ '' (s ∩ ball 0 m)) = 0 := by
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
        exists_partition_approximatesLinearOn_of_hasFDerivWithinAt Φ
          (s ∩ ball (0 : EuclideanSpace ℝ (Fin n)) m) (fderiv ℝ Φ)
          (fun x hx => (hsd x hx.1).hasFDerivAt.hasFDerivWithinAt) r rpos
      rcases (s ∩ ball (0 : EuclideanSpace ℝ (Fin n)) m).eq_empty_or_nonempty with he | hne
      · rw [he, image_empty, measure_empty]
        exact zero_le
      have hAni : ∀ k, ¬ Function.Injective (A k) := by
        intro k hk
        obtain ⟨y, hy, hAk⟩ := hAy hne k
        have h1 := LA3 _ hk
        rw [hAk, hs0 y hy.1] at h1
        exact lt_irrefl _ h1
      have hpiece : ∀ k, (μHE[n] : Measure (Ambient n ℓ)) (Φ '' (s ∩ ball 0 m ∩ t k)) ≤
          η * volume (s ∩ ball (0 : EuclideanSpace ℝ (Fin n)) m ∩ t k) := by
        intro k
        apply (B3 (A k) (hAni k) η hη).choose_spec.2 Φ
        have := happ k
        simp only [r, hAni k, dite_false] at this
        exact this
      calc (μHE[n] : Measure (Ambient n ℓ)) (Φ '' (s ∩ ball 0 m))
          ≤ μHE[n] (⋃ k, Φ '' (s ∩ ball 0 m ∩ t k)) := by
            apply measure_mono
            rw [← image_iUnion, ← inter_iUnion]
            exact image_mono (subset_inter subset_rfl hcov)
        _ ≤ ∑' k, μHE[n] (Φ '' (s ∩ ball 0 m ∩ t k)) := measure_iUnion_le _
        _ ≤ ∑' k, (η : ℝ≥0∞) * volume (s ∩ ball (0 : EuclideanSpace ℝ (Fin n)) m ∩ t k) :=
            ENNReal.tsum_le_tsum hpiece
        _ = η * volume (⋃ k, s ∩ ball (0 : EuclideanSpace ℝ (Fin n)) m ∩ t k) := by
            rw [ENNReal.tsum_mul_left, measure_iUnion]
            · exact htd.mono fun i j h => h.mono inter_subset_right inter_subset_right
            · exact fun k => hs'm.inter (htm k)
        _ ≤ η * volume (ball (0 : EuclideanSpace ℝ (Fin n)) m) :=
            mul_le_mul' le_rfl
              (measure_mono (iUnion_subset fun k => inter_subset_left.trans inter_subset_right))
    have hU : Φ '' s = ⋃ m : ℕ, Φ '' (s ∩ ball 0 m) := by
      rw [← image_iUnion, ← inter_iUnion, iUnion_ball_nat, inter_univ]
    rw [hU]
    exact measure_iUnion_null key
  /- (Pos) Where `Φ` is injective and `J = Jl ∘ DΦ > 0`, `Hⁿ(Φ(s)) = ∫_s J`: for `c > 1` split `s`
  into the level sets `c^k ≤ J < c^{k+1}` (`k ∈ ℤ`), partition each into pieces where `Φ` is
  close to an injective `DΦ(y)`, compare both sides on each piece with `B12` up to `c²`, and sum
  (the images of the pieces are disjoint and Borel by Lusin–Souslin). Then let `c → 1`. -/
  have hPos : ∀ (Φ : EuclideanSpace ℝ (Fin n) → Ambient n ℓ) (s : Set (EuclideanSpace ℝ (Fin n))),
      MeasurableSet s → (∀ x ∈ s, DifferentiableAt ℝ Φ x) → Set.InjOn Φ s →
      (∀ x ∈ s, 0 < Jl (fderiv ℝ Φ x)) →
      (μHE[n] : Measure (Ambient n ℓ)) (Φ '' s) =
        ∫⁻ x in s, ENNReal.ofReal (Jl (fderiv ℝ Φ x)) := by
    intro Φ s hs hsd hinjs hspos
    obtain ⟨J, hJ⟩ : ∃ J : EuclideanSpace ℝ (Fin n) → ℝ, J = fun v => Jl (fderiv ℝ Φ v) :=
      ⟨_, rfl⟩
    have hJv : ∀ v, J v = Jl (fderiv ℝ Φ v) := fun v => by rw [hJ]
    have hJm : Measurable J := by
      rw [hJ]
      exact hJl_cont.measurable.comp (measurable_fderiv ℝ Φ)
    simp only [← hJv] at hspos ⊢
    have hΦc : ContinuousOn Φ s := fun x hx => (hsd x hx).continuousAt.continuousWithinAt
    have himgd : ∀ a b : Set (EuclideanSpace ℝ (Fin n)), a ⊆ s → b ⊆ s → Disjoint a b →
        Disjoint (Φ '' a) (Φ '' b) := by
      intro a b ha hb hab
      rw [Set.disjoint_left]
      rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
      have hyx : y = x := hinjs (hb hy) (ha hx) hxy
      exact Set.disjoint_left.mp hab hx (hyx ▸ hy)
    have key : ∀ c : ℝ, 1 < c →
        (μHE[n] : Measure (Ambient n ℓ)) (Φ '' s) ≤
          ENNReal.ofReal c * (ENNReal.ofReal c * ∫⁻ x in s, ENNReal.ofReal (J x)) ∧
        ∫⁻ x in s, ENNReal.ofReal (J x) ≤
          ENNReal.ofReal c * (ENNReal.ofReal c * (μHE[n] : Measure (Ambient n ℓ)) (Φ '' s)) := by
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
          (∀ j, ApproximatesLinearOn Φ (A j) (L k ∩ t j) (r (A j))) ∧
          ((L k).Nonempty → ∀ j, ∃ y ∈ L k, A j = fderiv ℝ Φ y) := fun k =>
        exists_partition_approximatesLinearOn_of_hasFDerivWithinAt Φ (L k) (fderiv ℝ Φ)
          (fun x hx => (hsd x (hLs k hx)).hasFDerivAt.hasFDerivWithinAt) r rpos
      choose t A htd htm hcov happ hAy using hpart
      have hPm : ∀ k j, MeasurableSet (L k ∩ t k j) := fun k j => (hLm k).inter (htm k j)
      have hPs : ∀ k j, L k ∩ t k j ⊆ s := fun k j => inter_subset_left.trans (hLs k)
      have hPd : ∀ k, Pairwise (Function.onFun Disjoint fun j => L k ∩ t k j) := fun k j j' h =>
        (htd k h).mono inter_subset_right inter_subset_right
      have hLP : ∀ k, L k = ⋃ j, L k ∩ t k j := fun k => by
        rw [← inter_iUnion]
        exact (inter_eq_left.mpr (hcov k)).symm
      have hpiece : ∀ k j,
          (μHE[n] : Measure (Ambient n ℓ)) (Φ '' (L k ∩ t k j)) ≤
            ENNReal.ofReal c * (ENNReal.ofReal c * ∫⁻ x in L k ∩ t k j, ENNReal.ofReal (J x)) ∧
          ∫⁻ x in L k ∩ t k j, ENNReal.ofReal (J x) ≤
            ENNReal.ofReal c * (ENNReal.ofReal c *
              (μHE[n] : Measure (Ambient n ℓ)) (Φ '' (L k ∩ t k j))) := by
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
            ApproximatesLinearOn Φ (A k j) (L k ∩ t k j) (B12 (A k j) hinjA c hc).choose := by
          have := happ k j
          simp only [r, hinjA, dite_true] at this
          exact this
        have hB := (B12 (A k j) hinjA c hc).choose_spec.2 Φ (L k ∩ t k j) happ'
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
        · calc (μHE[n] : Measure (Ambient n ℓ)) (Φ '' (L k ∩ t k j))
              ≤ ENNReal.ofReal c * (ENNReal.ofReal (Jl (A k j)) * volume (L k ∩ t k j)) := hB.1
            _ ≤ ENNReal.ofReal c * (ENNReal.ofReal c * ∫⁻ x in L k ∩ t k j, ENNReal.ofReal (J x)) :=
              mul_le_mul' le_rfl hcmp1
        · calc ∫⁻ x in L k ∩ t k j, ENNReal.ofReal (J x)
              ≤ ENNReal.ofReal c * (ENNReal.ofReal (Jl (A k j)) * volume (L k ∩ t k j)) := hcmp2
            _ ≤ ENNReal.ofReal c * (ENNReal.ofReal c *
                (μHE[n] : Measure (Ambient n ℓ)) (Φ '' (L k ∩ t k j))) :=
              mul_le_mul' le_rfl (hB.2 (hinjs.mono (hPs k j)))
      have hFL : ∀ k, (μHE[n] : Measure (Ambient n ℓ)) (Φ '' L k) =
          ∑' j, μHE[n] (Φ '' (L k ∩ t k j)) := by
        intro k
        conv_lhs => rw [hLP k, image_iUnion]
        apply measure_iUnion
        · intro j j' hjj'
          exact himgd _ _ (hPs k j) (hPs k j') (hPd k hjj')
        · exact fun j => (hPm k j).image_of_continuousOn_injOn (hΦc.mono (hPs k j))
            (hinjs.mono (hPs k j))
      have hFs : (μHE[n] : Measure (Ambient n ℓ)) (Φ '' s) = ∑' k, μHE[n] (Φ '' L k) := by
        conv_lhs => rw [hLcov, image_iUnion]
        apply measure_iUnion
        · intro k k' hkk'
          exact himgd _ _ (hLs k) (hLs k') (hLd hkk')
        · exact fun k => (hLm k).image_of_continuousOn_injOn (hΦc.mono (hLs k))
            (hinjs.mono (hLs k))
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
  /- Area formula on Borel sets of injectivity and differentiability: `Hⁿ(Φ(s)) = ∫_s Jl ∘ DΦ`.
  Split `s` into the part where `Jl ∘ DΦ = 0` (null image by `hZ`) and where it is `> 0`. -/
  have hMI : ∀ (Φ : EuclideanSpace ℝ (Fin n) → Ambient n ℓ) (s : Set (EuclideanSpace ℝ (Fin n))),
      MeasurableSet s → (∀ x ∈ s, DifferentiableAt ℝ Φ x) → Set.InjOn Φ s →
      (μHE[n] : Measure (Ambient n ℓ)) (Φ '' s) =
        ∫⁻ x in s, ENNReal.ofReal (Jl (fderiv ℝ Φ x)) := by
    intro Φ s hs hsd hinjs
    have hJm : Measurable fun x => Jl (fderiv ℝ Φ x) :=
      hJl_cont.measurable.comp (measurable_fderiv ℝ Φ)
    have hs₀m : MeasurableSet (s ∩ (fun x => Jl (fderiv ℝ Φ x)) ⁻¹' {0}) :=
      hs.inter (hJm (measurableSet_singleton 0))
    have hs₁m : MeasurableSet (s ∩ (fun x => Jl (fderiv ℝ Φ x)) ⁻¹' Ioi 0) :=
      hs.inter (hJm measurableSet_Ioi)
    have hZ0 : (μHE[n] : Measure (Ambient n ℓ)) (Φ '' (s ∩ (fun x => Jl (fderiv ℝ Φ x)) ⁻¹' {0}))
        = 0 :=
      hZ Φ _ hs₀m (fun x hx => hsd x hx.1) (fun x hx => hx.2)
    have hP1 := hPos Φ _ hs₁m (fun x hx => hsd x hx.1) (hinjs.mono inter_subset_left)
      (fun x hx => hx.2)
    have hsplit : s = (s ∩ (fun x => Jl (fderiv ℝ Φ x)) ⁻¹' Ioi 0) ∪
        (s ∩ (fun x => Jl (fderiv ℝ Φ x)) ⁻¹' {0}) := by
      ext x
      simp only [mem_union, mem_inter_iff, mem_preimage, mem_Ioi, mem_singleton_iff]
      constructor
      · intro hx
        rcases (hJl_nonneg (fderiv ℝ Φ x)).eq_or_lt with h0 | hpos
        · exact Or.inr ⟨hx, h0.symm⟩
        · exact Or.inl ⟨hx, hpos⟩
      · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    have hdisj : Disjoint (s ∩ (fun x => Jl (fderiv ℝ Φ x)) ⁻¹' Ioi 0)
        (s ∩ (fun x => Jl (fderiv ℝ Φ x)) ⁻¹' {0}) := by
      rw [Set.disjoint_left]
      rintro x ⟨_, hx1⟩ ⟨_, hx2⟩
      simp only [mem_preimage, mem_Ioi, mem_singleton_iff] at hx1 hx2
      rw [hx2] at hx1
      exact lt_irrefl _ hx1
    have hint0 : ∫⁻ x in s ∩ (fun x => Jl (fderiv ℝ Φ x)) ⁻¹' {0},
        ENNReal.ofReal (Jl (fderiv ℝ Φ x)) = 0 := by
      rw [setLIntegral_congr_fun hs₀m (g := fun _ => 0) fun x hx => by
        rw [show Jl (fderiv ℝ Φ x) = 0 from hx.2, ENNReal.ofReal_zero]]
      exact lintegral_zero
    have hint : ∫⁻ x in s, ENNReal.ofReal (Jl (fderiv ℝ Φ x)) =
        ∫⁻ x in s ∩ (fun x => Jl (fderiv ℝ Φ x)) ⁻¹' Ioi 0, ENNReal.ofReal (Jl (fderiv ℝ Φ x)) := by
      conv_lhs => rw [hsplit]
      rw [lintegral_union hs₀m hdisj, hint0, add_zero]
    rw [hint, ← hP1]
    apply le_antisymm _ (measure_mono (image_mono inter_subset_left))
    calc (μHE[n] : Measure (Ambient n ℓ)) (Φ '' s)
        ≤ μHE[n] (Φ '' (s ∩ (fun x => Jl (fderiv ℝ Φ x)) ⁻¹' Ioi 0)) +
            μHE[n] (Φ '' (s ∩ (fun x => Jl (fderiv ℝ Φ x)) ⁻¹' {0})) := by
          conv_lhs => rw [hsplit, image_union]
          exact measure_union_le _ _
      _ = μHE[n] (Φ '' (s ∩ (fun x => Jl (fderiv ℝ Φ x)) ⁻¹' Ioi 0)) := by
          rw [hZ0, add_zero]
  /- Weighted area formula with an arbitrary (not necessarily measurable) weight `g`: the
  restriction of `Φ` to `s` is a measurable embedding carrying `(Jl ∘ DΦ) · Lⁿ ⌞ s` to
  `Hⁿ ⌞ Φ(s)` (by `hMI` on measurable subsets of `s`). -/
  have hW : ∀ (Φ : EuclideanSpace ℝ (Fin n) → Ambient n ℓ) (s : Set (EuclideanSpace ℝ (Fin n))),
      MeasurableSet s → (∀ x ∈ s, DifferentiableAt ℝ Φ x) → Set.InjOn Φ s →
      ∀ g : Ambient n ℓ → ℝ≥0∞, ∫⁻ y in Φ '' s, g y ∂μHE[n] =
        ∫⁻ x in s, ENNReal.ofReal (Jl (fderiv ℝ Φ x)) * g (Φ x) := by
    intro Φ s hs hsd hinjs g
    have hΦc : ContinuousOn Φ s := fun x hx => (hsd x hx).continuousAt.continuousWithinAt
    have hemb := hΦc.measurableEmbedding hs hinjs
    have hsub : MeasurableEmbedding (Subtype.val : s → EuclideanSpace ℝ (Fin n)) :=
      MeasurableEmbedding.subtype_coe hs
    have hJm : Measurable fun x => ENNReal.ofReal (Jl (fderiv ℝ Φ x)) :=
      (hJl_cont.measurable.comp (measurable_fderiv ℝ Φ)).ennreal_ofReal
    have hmap : Measure.map (s.domRestrict Φ)
        (((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
          fun x => ENNReal.ofReal (Jl (fderiv ℝ Φ x))).comap
          (Subtype.val : s → EuclideanSpace ℝ (Fin n))) =
        (μHE[n] : Measure (Ambient n ℓ)).restrict (Φ '' s) := by
      ext t ht
      rw [Measure.map_apply hemb.measurable ht, hsub.comap_apply]
      have hBm : MeasurableSet
          ((Subtype.val : s → EuclideanSpace ℝ (Fin n)) '' ((s.domRestrict Φ) ⁻¹' t)) :=
        hsub.measurableSet_image' (hemb.measurable ht)
      have hBs : (Subtype.val : s → EuclideanSpace ℝ (Fin n)) '' ((s.domRestrict Φ) ⁻¹' t) ⊆ s := by
        rintro x ⟨u, _, rfl⟩
        exact u.property
      rw [withDensity_apply _ hBm, ← hMI Φ _ hBm (fun x hx => hsd x (hBs hx)) (hinjs.mono hBs),
        Measure.restrict_apply ht]
      congr 1
      ext y
      constructor
      · rintro ⟨x, ⟨u, hu, rfl⟩, rfl⟩
        exact ⟨hu, ⟨u, u.property, rfl⟩⟩
      · rintro ⟨hy, x, hx, rfl⟩
        exact ⟨x, ⟨⟨x, hx⟩, hy, rfl⟩, rfl⟩
    rw [← hmap, hemb.lintegral_map]
    change (∫⁻ x : s, (fun x : EuclideanSpace ℝ (Fin n) => g (Φ x)) x ∂
      (((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        fun x => ENNReal.ofReal (Jl (fderiv ℝ Φ x))).comap
        (Subtype.val : s → EuclideanSpace ℝ (Fin n)))) = _
    rw [lintegral_subtype_comap hs (fun x : EuclideanSpace ℝ (Fin n) => g (Φ x)),
      setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀ _ hJm.aemeasurable _ hs]
    · rfl
    · exact Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  /- Chain rule for the Jacobian: `Jl (L ∘ T) = jac(L, range T) · Jl T`, where `jac` is the
  square-rooted determinant of the statement. For injective `T` write `T eᵢ = ∑ₐ Mₐᵢ bₐ` in an
  orthonormal basis `b` of `Q = range T`; then the Gram matrices of `T e` and `L T e` are `Mᵀ M`
  and `Mᵀ G M` with `G = (⟪L bₐ, L b_c⟫)`, and `det G = det S_Q(L)` by the sibling theorem. -/
  have hchain : ∀ (L : Ambient n ℓ →L[ℝ] Ambient n ℓ)
      (T : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ) (Q : Submodule ℝ (Ambient n ℓ)),
      Q = LinearMap.range T.toLinearMap →
      Jl (L.comp T) = Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (n + ℓ) ↦
        inner ℝ (L (Q.starProjection (EuclideanSpace.single i (1 : ℝ))))
          (L (Q.starProjection (EuclideanSpace.single j (1 : ℝ)))) +
        inner ℝ (EuclideanSpace.single i (1 : ℝ) - Q.starProjection (EuclideanSpace.single i (1 : ℝ)))
          (EuclideanSpace.single j (1 : ℝ) - Q.starProjection (EuclideanSpace.single j (1 : ℝ))))) *
        Jl T := by
    intro L T Q hQ
    by_cases hT : Function.Injective T
    · have hk : Module.finrank ℝ Q = n := by
        rw [hQ, LinearMap.finrank_range_of_inj hT, finrank_euclideanSpace_fin]
      let b : OrthonormalBasis (Fin n) ℝ Q := (stdOrthonormalBasis ℝ Q).reindex (finCongr hk)
      rw [Submission.ts_fv_det_tangential_gram_eq (n + ℓ) n Q b L]
      have hTQ : ∀ x, T x ∈ Q := fun x => by
        rw [hQ]
        exact LinearMap.mem_range_self _ x
      set M : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun a i =>
        inner ℝ (b a : Ambient n ℓ) (T (EuclideanSpace.basisFun (Fin n) ℝ i)) with hM
      have hexp : ∀ i, T (EuclideanSpace.basisFun (Fin n) ℝ i) =
          ∑ a, M a i • (b a : Ambient n ℓ) := by
        intro i
        have h := congrArg (fun x : Q => (x : Ambient n ℓ))
          (b.sum_repr' ⟨T (EuclideanSpace.basisFun (Fin n) ℝ i), hTQ _⟩)
        simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at h
        exact h.symm
      have hgram : ∀ L' : Ambient n ℓ →L[ℝ] Ambient n ℓ, (Matrix.of fun i j : Fin n =>
          inner ℝ (L' (T (EuclideanSpace.basisFun (Fin n) ℝ i)))
            (L' (T (EuclideanSpace.basisFun (Fin n) ℝ j)))) =
          M.transpose * (Matrix.of fun a c : Fin n => inner ℝ (L' (b a)) (L' (b c))) * M := by
        intro L'
        ext i j
        rw [Matrix.of_apply, hexp i, hexp j]
        simp only [map_sum, map_smul, inner_sum, sum_inner, real_inner_smul_left,
          real_inner_smul_right, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
          Finset.sum_mul]
        exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => by ring
      have hid : (Matrix.of fun a c : Fin n => inner ℝ (b a : Ambient n ℓ) (b c : Ambient n ℓ)) =
          1 := by
        ext a c
        rw [Matrix.of_apply, Matrix.one_apply, ← Submodule.coe_inner]
        exact orthonormal_iff_ite.mp b.orthonormal a c
      have hJT : Jl T = |M.det| := by
        have h := hgram (ContinuousLinearMap.id ℝ (Ambient n ℓ))
        simp only [ContinuousLinearMap.id_apply] at h
        rw [hJl]
        simp only
        rw [h, hid, Matrix.mul_one, Matrix.det_mul, Matrix.det_transpose, Real.sqrt_mul_self_eq_abs]
      rw [hJT, hJl]
      simp only [ContinuousLinearMap.comp_apply]
      rw [hgram L, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
        show M.det * (Matrix.of fun a c : Fin n => inner ℝ (L (b a)) (L (b c))).det * M.det =
          M.det ^ 2 * (Matrix.of fun a c : Fin n => inner ℝ (L (b a)) (L (b c))).det by ring,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
      ring
    · have hLT : ¬ Function.Injective (L.comp T) := fun h =>
        hT fun x y hxy => h (by rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
          hxy])
      rw [LA2 T hT, LA2 _ hLT, mul_zero]
  /- Assembly. `B = C ∩ F⁻¹(A)` is Borel with `F(B) = A`; `F` and `G = f ∘ F` are injective
  and differentiable on `B` with `G(B) = f(A)`. Apply `hW` to `G` with weight `w` and to `F` with
  weight `jac · (w ∘ f)`, and compare the integrands on `B` with `fderiv_comp` and `hchain`. -/
  obtain ⟨LF, hLF⟩ := hFL
  have hB : MeasurableSet (C ∩ F ⁻¹' A) := hC.inter (hLF.continuous.measurable hA)
  have hBA : F '' (C ∩ F ⁻¹' A) = A := by
    apply Subset.antisymm
    · rintro _ ⟨v, ⟨_, hv⟩, rfl⟩
      exact hv
    · intro y hy
      obtain ⟨v, hv, rfl⟩ := hAC hy
      exact ⟨v, ⟨hv, hy⟩, rfl⟩
  have hBd : ∀ v ∈ C ∩ F ⁻¹' A, DifferentiableAt ℝ F v := fun v hv => hFd v hv.1
  have hBi : Set.InjOn F (C ∩ F ⁻¹' A) := hFi.mono inter_subset_left
  have hGd : ∀ v ∈ C ∩ F ⁻¹' A, DifferentiableAt ℝ (f ∘ F) v := fun v hv =>
    (hfd _ hv.2).comp v (hFd v hv.1)
  have hGi : Set.InjOn (f ∘ F) (C ∩ F ⁻¹' A) := fun v hv v' hv' h =>
    hBi hv hv' (hfi hv.2 hv'.2 h)
  have hGB : (f ∘ F) '' (C ∩ F ⁻¹' A) = f '' A := by rw [image_comp, hBA]
  rw [← hGB, hW _ _ hB hGd hGi w]
  conv_rhs => rw [← hBA]
  rw [hW _ _ hB hBd hBi]
  apply setLIntegral_congr_fun hB
  intro v hv
  simp only [Function.comp_apply]
  rw [fderiv_comp v (hfd _ hv.2) (hFd v hv.1), hchain _ _ (P (F v)) (hP v hv.1 hv.2),
    ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  ring
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

/-- **Blow-up of a Lipschitz piece at a Lebesgue density point** (Simon Ch. 3, proof of 1.6 `⇒`,
for a parametrized piece in place of the embedded `C¹` pieces of 1.2). Let `C ⊆ ℝⁿ` be compact and
`F : ℝⁿ → ℝ^{n+ℓ}` `K`-Lipschitz, differentiable at every `w ∈ C` with injective `DF(w)`, `DF`
continuous on `C`, and `c|v - w| ≤ |F(v) - F(w)|` on `C` with `c > 0`. Then (3b)
`Hⁿ(F(C) ∩ B_ρ(x)) ≤ Γρⁿ` for `x ∈ F(C)`, `ρ > 0`, with `Γ = Kⁿωₙ/cⁿ`; and (3a) at every Lebesgue
density point `w ∈ C` of `C` and for `f ∈ C_c`,
`t⁻ⁿ ∫_{F(C)} f(t⁻¹(y - F(w))) dHⁿ(y) → ∫_{DF(w)(ℝⁿ)} f dHⁿ` as `t ↓ 0`. -/
theorem Submission.ts_piece_density_blowup : ∀ (n ℓ : ℕ) (C : Set (EuclideanSpace ℝ (Fin n)))
    (F : EuclideanSpace ℝ (Fin n) → Ambient n ℓ), 0 < n →
    (IsCompact C ∧ (∃ K : NNReal, LipschitzWith K F) ∧
      (∀ w ∈ C, DifferentiableAt ℝ F w ∧ Function.Injective (fderiv ℝ F w)) ∧
      ContinuousOn (fderiv ℝ F) C ∧
      ∃ c : ℝ, 0 < c ∧ ∀ v ∈ C, ∀ w ∈ C, c * ‖v - w‖ ≤ ‖F v - F w‖) →
    (∃ Γ : ℝ, ∀ x ∈ F '' C, ∀ ρ : ℝ, 0 < ρ →
      (μHE[n] : Measure (Ambient n ℓ)) (F '' C ∩ closedBall x ρ) ≤ ENNReal.ofReal (Γ * ρ ^ n)) ∧
    ∀ w ∈ C, Tendsto (fun r : ℝ ↦ volume (C ∩ closedBall w r) / volume (closedBall w r))
      (𝓝[>] 0) (𝓝 1) →
    ∀ f : C_c(Ambient n ℓ, ℝ),
      Tendsto (fun t : ℝ ↦ (t ^ n)⁻¹ * ∫ y in F '' C, f (t⁻¹ • (y - F w)) ∂μHE[n]) (𝓝[>] 0)
        (𝓝 (∫ y in (LinearMap.range (fderiv ℝ F w).toLinearMap : Set (Ambient n ℓ)),
          f y ∂μHE[n])) := by
  rintro n ℓ C F - ⟨hC, ⟨K, hK⟩, hdiff, hcont, c, hc, hlow⟩
  -- Step 1(a): by the lower Lipschitz bound, `F` is injective on `C`.
  have hinj : Set.InjOn F C := fun v hv w hw hvw ↦ by
    have h := hlow v hv w hw
    rw [hvw, sub_self, norm_zero] at h
    have h' : ‖v - w‖ = 0 := le_antisymm (by nlinarith [norm_nonneg (v - w)]) (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp h')
  refine ⟨⟨(K : ℝ) ^ n * omega n / c ^ n, ?_⟩, ?_⟩
  -- Step 2, claim (3b): `F(C) ∩ B_ρ(F w) ⊆ F(C ∩ B_{ρ/c}(w))` and the Lipschitz image bound.
  · rintro x ⟨w, hw, rfl⟩ ρ hρ
    exact Submission.ts_pdb_image_closedBall_measure_le n ℓ C F K c w hK hc
      (fun v hv ↦ hlow v hv w hw) ρ hρ
  -- Steps 3–7, claim (3a).
  · intro w hw hdens f
    -- Steps 1(c) and 4: the area formula on the piece, with a Jacobian `J` continuous on `C`
    -- that is the area factor of each `DF(v)`, `v ∈ C`.
    obtain ⟨J, hJ, hJC, harea⟩ := Submission.ts_pdb_piece_area_formula n ℓ C F K
      hC.isClosed.measurableSet hK hinj hcont
    obtain ⟨hJw, hJwS⟩ := hJC w hw
    -- (4.1) for `g = f(t⁻¹(· - F(w)))`.
    have hN : ∀ t : ℝ, ∫ y in F '' C, f (t⁻¹ • (y - F w)) ∂μHE[n] =
        ∫ v in C, J v * f (t⁻¹ • (F v - F w)) := fun t ↦
      harea (fun y ↦ f (t⁻¹ • (y - F w))) (by fun_prop)
    -- Step 6: `∫_{range DF(w)} f dHⁿ = J(w) ∫ f(DF(w) u) du`.
    have hT : ∫ y in (LinearMap.range (fderiv ℝ F w).toLinearMap : Set (Ambient n ℓ)),
        f y ∂μHE[n] = J w * ∫ u, f (fderiv ℝ F w u) :=
      Submission.ts_pdb_linear_range_integral n ℓ (fderiv ℝ F w) (J w) hJw hJwS f
    -- Steps 5 and 7: `t⁻ⁿ ∫_C J(v) f(t⁻¹(F(v) - F(w))) dv → J(w) ∫ f(DF(w) u) du`.
    rw [hT]
    refine (Submission.ts_pdb_density_point_rescaled_limit n ℓ C F J (fderiv ℝ F w) w c hC
      hK.continuous hJ hw (hdiff w hw).1.hasFDerivAt (hdiff w hw).2 hc
      (fun v hv ↦ hlow v hv w hw) hdens f).congr fun t ↦ ?_
    rw [hN t]
/-- **Ch. 3, Remark 1.5(1) and Definition 1.7 (pp. 71, 74); Ch. 4, 1.3 (p. 86).** The approximate
tangent space `T_x V` is unique when it exists: if `P` and `Q` both satisfy `V.IsApproxTangentAt x`
(with possibly different multiplicities `c, c' > 0`), then `P = Q`. -/
theorem Submission.ts_approx_tangent_plane_unique : ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (x : Ambient n ℓ) (P Q : Submodule ℝ (Ambient n ℓ)), V.IsApproxTangentAt x P → V.IsApproxTangentAt x Q → P = Q := by
  intro n ℓ V x P Q ⟨hP, c, hc, hPlim⟩ ⟨hQ, c', hc', hQlim⟩
  -- `c Hⁿ ⌞ P` and `c' Hⁿ ⌞ Q` are regular with the same `C_c` integrals (uniqueness of the
  -- blow-up limit as `λ ↓ 0`), hence equal.
  have hmeas : ENNReal.ofReal c • (μHE[n] : Measure (Ambient n ℓ)).restrict P =
      ENNReal.ofReal c' • (μHE[n] : Measure (Ambient n ℓ)).restrict Q := by
    have := Poincare.SimonGMT.Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule hP
    have := Poincare.SimonGMT.Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule hQ
    have : (ENNReal.ofReal c • (μHE[n] : Measure (Ambient n ℓ)).restrict P).Regular :=
      .smul ENNReal.ofReal_ne_top
    have : (ENNReal.ofReal c' • (μHE[n] : Measure (Ambient n ℓ)).restrict Q).Regular :=
      .smul ENNReal.ofReal_ne_top
    refine Measure.ext_of_integral_eq_on_compactlySupported fun f ↦ ?_
    rw [integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal hc.le,
      ENNReal.toReal_ofReal hc'.le, smul_eq_mul, smul_eq_mul]
    exact tendsto_nhds_unique (hPlim f) (hQlim f)
  -- A nonzero multiple of a measure has the same support, and `spt (Hⁿ ⌞ P) = P`.
  have hsupp (a : ℝ≥0∞) (μ : Measure (Ambient n ℓ)) (ha : a ≠ 0) : (a • μ).support = μ.support :=
    Measure.smul_absolutelyContinuous.support_mono.antisymm
      (Measure.absolutelyContinuous_smul ha).support_mono
  apply SetLike.ext'
  calc (P : Set (Ambient n ℓ))
      = ((μHE[n] : Measure (Ambient n ℓ)).restrict P).support :=
        (Poincare.SimonGMT.Chapter03.support_euclideanHausdorffMeasure_restrict_submodule hP).symm
    _ = (ENNReal.ofReal c • (μHE[n] : Measure (Ambient n ℓ)).restrict P).support :=
        (hsupp _ _ (ENNReal.ofReal_pos.2 hc).ne').symm
    _ = (ENNReal.ofReal c' • (μHE[n] : Measure (Ambient n ℓ)).restrict Q).support := by
        rw [hmeas]
    _ = ((μHE[n] : Measure (Ambient n ℓ)).restrict Q).support :=
        hsupp _ _ (ENNReal.ofReal_pos.2 hc').ne'
    _ = Q := Poincare.SimonGMT.Chapter03.support_euclideanHausdorffMeasure_restrict_submodule hQ
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
/-- Simon Ch. 3, 1.7 and Ch. 4, 1.3 (pp. 75, 86): for `V = v(M, θ)` and `λ > 0`, the change of
variables `y ↦ λ⁻¹(y - x)` gives
`λ⁻ⁿ ∫ f(λ⁻¹(y - x)) dμ_V(y) = ∫_{η_{x,λ}(M)} f(y) θ(x + λy) dHⁿ(y)`. So if `dim P = n` and the
left side tends to `θ(x) ∫_P f dHⁿ` for every `f ∈ C_c`, then `P` is the approximate tangent
space of `M` with respect to `θ` at `x`. -/
theorem Submission.ts_blowup_weighted_tangent : ∀ (n ℓ : ℕ) (a : RectifiablePair n ℓ) (x : Ambient n ℓ) (P : Submodule ℝ (Ambient n ℓ)), Module.finrank ℝ P = n → (∀ f : C_c(Ambient n ℓ, ℝ), Tendsto (fun t : ℝ ↦ (t ^ n)⁻¹ * ∫ y, f (t⁻¹ • (y - x)) ∂(mk a).weight) (𝓝[>] 0) (𝓝 (a.θ x * ∫ y in (P : Set (Ambient n ℓ)), f y ∂μHE[n]))) → Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n a.M a.θ x P := by
  intro n ℓ a x P hP hlim
  -- `θ` is a.e.-strongly measurable on `M = ⋃ₖ M ∩ B_k(0)`: it is integrable on each piece.
  have hθ : AEStronglyMeasurable a.θ ((μHE[n] : Measure (Ambient n ℓ)).restrict a.M) := by
    have hM : a.M = ⋃ k : ℕ, a.M ∩ closedBall (0 : Ambient n ℓ) k := by
      ext y
      simp only [mem_iUnion, mem_inter_iff, mem_closedBall, dist_zero_right]
      exact ⟨fun hy ↦ ⟨⌈‖y‖⌉₊, hy, Nat.le_ceil _⟩, fun ⟨_, hy, _⟩ ↦ hy⟩
    rw [hM, aestronglyMeasurable_iUnion_iff]
    exact fun k ↦
      (a.isRectifiablePair.locallyIntegrable _ (isCompact_closedBall 0 k)).aestronglyMeasurable
  -- `∫ h dμ_V = ∫_M h θ dHⁿ` for every `h`.
  have hweight : ∀ h : Ambient n ℓ → ℝ,
      ∫ y, h y ∂(mk a).weight = ∫ y in a.M, h y * a.θ y ∂μHE[n] := by
    intro h
    have hw : (mk a).weight = ((μHE[n] : Measure (Ambient n ℓ)).restrict a.M).withDensity
        fun y ↦ ENNReal.ofReal (a.θ y) := rfl
    rw [hw, integral_withDensity_eq_integral_toReal_smul₀ hθ.aemeasurable.ennreal_ofReal
      (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top) h]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem₀ a.isRectifiablePair.measurable] with y hy
    rw [ENNReal.toReal_ofReal (a.isRectifiablePair.pos y hy).le, smul_eq_mul, mul_comm]
  -- Change of variables under `η_{x,r} = e⁻¹`, where `e : y ↦ x + r y`.
  have hcov : ∀ r : ℝ, 0 < r → ∀ g : Ambient n ℓ → ℝ,
      ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' a.M, g y * a.θ (x + r • y) ∂μHE[n] =
        (r ^ n)⁻¹ * ∫ y, g (r⁻¹ • (y - x)) ∂(mk a).weight := by
    intro r hr g
    let e : Ambient n ℓ ≃ₜ Ambient n ℓ :=
      { toFun := fun y ↦ x + r • y
        invFun := fun y ↦ r⁻¹ • (y - x)
        left_inv := fun y ↦ by simp [smul_smul, hr.ne']
        right_inv := fun y ↦ by simp [smul_smul, hr.ne']
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    change ∫ y in e.symm '' a.M, g y * a.θ (e y) ∂μHE[n] = _
    -- `Hⁿ(η_{x,r}(S)) = r⁻ⁿ Hⁿ(S)`: a translation followed by the dilation by `r⁻¹`.
    have hshift : Isometry (fun y : Ambient n ℓ ↦ y - x) := by
      apply Isometry.of_dist_eq
      intro y z
      simp only [dist_eq_norm]
      congr 1
      abel
    have hscale : ∀ S : Set (Ambient n ℓ), (μHE[n] : Measure (Ambient n ℓ)) (e.symm '' S) =
        ENNReal.ofReal (r⁻¹) ^ n * (μHE[n] : Measure (Ambient n ℓ)) S := by
      intro S
      have himage : e.symm '' S =
          AffineMap.homothety (0 : Ambient n ℓ) r⁻¹ '' ((fun y ↦ y - x) '' S) := by
        rw [image_image]
        congr 1
        funext y
        simp [e, AffineMap.homothety_apply]
      rw [himage,
        euclideanHausdorffMeasure_homothety_image n (0 : Ambient n ℓ) (inv_ne_zero hr.ne'),
        hshift.euclideanHausdorffMeasure_image, ENNReal.smul_def, ENNReal.coe_pow,
        ← ENNReal.ofReal_coe_nnreal, coe_nnnorm, Real.norm_of_nonneg (inv_pos.mpr hr).le]
      rfl
    -- Pushing `Hⁿ ⌞ η_{x,r}(M)` forward by `e` gives `r⁻ⁿ Hⁿ ⌞ M`.
    have hmap : ((μHE[n] : Measure (Ambient n ℓ)).restrict (e.symm '' a.M)).map e =
        ENNReal.ofReal (r⁻¹) ^ n • (μHE[n] : Measure (Ambient n ℓ)).restrict a.M := by
      ext A hA
      rw [Measure.map_apply e.continuous.measurable hA,
        Measure.restrict_apply (e.continuous.measurable hA), Measure.smul_apply,
        Measure.restrict_apply hA, smul_eq_mul]
      have hset : e ⁻¹' A ∩ e.symm '' a.M = e.symm '' (A ∩ a.M) := by
        ext z
        constructor
        · rintro ⟨hz, y, hy, rfl⟩
          exact ⟨y, ⟨by simpa only [mem_preimage, e.apply_symm_apply] using hz, hy⟩, rfl⟩
        · rintro ⟨y, ⟨hyA, hyM⟩, rfl⟩
          exact ⟨by simpa only [mem_preimage, e.apply_symm_apply] using hyA, y, hyM, rfl⟩
      rw [hset, hscale]
    have hi := e.measurableEmbedding.integral_map
      (μ := (μHE[n] : Measure (Ambient n ℓ)).restrict (e.symm '' a.M))
      (fun z ↦ g (e.symm z) * a.θ z)
    rw [hmap, integral_smul_measure, ENNReal.toReal_pow, ENNReal.toReal_ofReal (inv_pos.mpr hr).le,
      smul_eq_mul] at hi
    simp only [e.symm_apply_apply] at hi
    rw [hweight, ← inv_pow]
    exact hi.symm
  -- The two blow-up functions agree on `(0, ∞) ∈ 𝓝[>] 0`.
  refine ⟨hP, fun f ↦ (hlim f).congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (hcov r hr f).symm
/-- **Countable gluing of image integrals.** Let `f : X → X` be injective and map `μ`-null sets to
`μ`-null sets and `μ`-null-measurable sets to `μ`-null-measurable sets. If the pairwise disjoint
measurable sets `D i` cover the `μ`-null-measurable set `Z` up to a `μ`-null set and
`∫_{f(Z ∩ D i)} u dμ = ∫_{Z ∩ D i} g dμ` for every `i`, then `∫_{f(Z)} u dμ = ∫_Z g dμ`. -/
theorem Submission.ts_fv_lintegral_image_eq_of_pieces : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (f : X → X) (Z : Set X) (D : ℕ → Set X) (u g : X → ℝ≥0∞), Function.Injective f → (∀ Y : Set X, μ Y = 0 → μ (f '' Y) = 0) → (∀ Y : Set X, NullMeasurableSet Y μ → NullMeasurableSet (f '' Y) μ) → NullMeasurableSet Z μ → (∀ i, MeasurableSet (D i)) → Pairwise (fun i j ↦ Disjoint (D i) (D j)) → μ (Z \ ⋃ i, D i) = 0 → (∀ i, ∫⁻ y in f '' (Z ∩ D i), u y ∂μ = ∫⁻ x in Z ∩ D i, g x ∂μ) → ∫⁻ y in f '' Z, u y ∂μ = ∫⁻ x in Z, g x ∂μ := by
  intro X _ μ f Z D u g hf hnull hnm hZ hD hdisj hrem hpiece
  -- `Z =ᵐ ⋃ i, Z ∩ D i`: the remainder `Z \ ⋃ i, (Z ∩ D i) = Z \ ⋃ i, D i` is null.
  have hrem' : Z \ ⋃ i, (Z ∩ D i) = Z \ ⋃ i, D i := by
    rw [← Set.inter_iUnion, Set.sdiff_self_inter]
  have hsub : ⋃ i, (Z ∩ D i) ⊆ Z := Set.iUnion_subset fun i ↦ Set.inter_subset_left
  have hZae : Z =ᵐ[μ] ⋃ i, (Z ∩ D i) := by
    refine ae_eq_set.2 ⟨by rw [hrem']; exact hrem, ?_⟩
    rw [Set.sdiff_eq_empty.2 hsub]
    exact measure_empty
  -- `f(Z) =ᵐ ⋃ i, f(Z ∩ D i)`: the remainder is `f(Z \ ⋃ i, D i)`, null since `f` keeps null sets.
  have hfZae : f '' Z =ᵐ[μ] ⋃ i, f '' (Z ∩ D i) := by
    rw [← Set.image_iUnion]
    refine ae_eq_set.2 ⟨?_, ?_⟩
    · rw [← Set.image_sdiff hf, hrem']
      exact hnull _ hrem
    · rw [Set.sdiff_eq_empty.2 (Set.image_mono hsub)]
      exact measure_empty
  -- The pieces are null-measurable and pairwise disjoint; so are their images (`f` injective).
  have hm : ∀ i, NullMeasurableSet (Z ∩ D i) μ := fun i ↦ hZ.inter (hD i).nullMeasurableSet
  have hd : ∀ i j, i ≠ j → Disjoint (Z ∩ D i) (Z ∩ D j) := fun i j hij ↦
    (hdisj hij).mono Set.inter_subset_right Set.inter_subset_right
  -- Sum the piecewise identities over both countable decompositions.
  calc ∫⁻ y in f '' Z, u y ∂μ = ∫⁻ y in ⋃ i, f '' (Z ∩ D i), u y ∂μ := setLIntegral_congr hfZae
    _ = ∑' i, ∫⁻ y in f '' (Z ∩ D i), u y ∂μ :=
        lintegral_iUnion₀ (fun i ↦ hnm _ (hm i))
          (fun i j hij ↦ (Set.disjoint_image_of_injective hf (hd i j hij)).aedisjoint) u
    _ = ∑' i, ∫⁻ x in Z ∩ D i, g x ∂μ := tsum_congr hpiece
    _ = ∫⁻ x in ⋃ i, (Z ∩ D i), g x ∂μ :=
        (lintegral_iUnion₀ hm (fun i j hij ↦ (hd i j hij).aedisjoint) g).symm
    _ = ∫⁻ x in Z, g x ∂μ := setLIntegral_congr hZae.symm

/-- **Image mass by the area formula on Lipschitz pieces (Simon Ch. 4, 1.5–1.7).** Let the carrier
`M` of `a = (M, θ)` be covered, up to the `Hⁿ`-null Borel set `N₀`, by the images `F i (C i)` of
compact sets under Lipschitz maps injective on `C i`, with `T_x V = range DF i (w)` whenever
`F i (w) = x`, for `Hⁿ`-a.e. `x ∈ M`. If `f` is injective, Lipschitz and differentiable, then
`M(f_#(V ⌞ K)) = ∫_{M ∩ K} θ jac(Df, T_x V) dHⁿ`, with
`jac(Λ, P) = √det(⟪Λ p eᵢ, Λ p eⱼ⟫ + ⟪q eᵢ, q eⱼ⟫)` the tangential Jacobian of `Λ` along `P`.
The cover is disjointified into the Borel sets `D i = F i (C i) \ (N₀ ∪ ⋃_{j < i} F j (C j))`;
`ts_fv_piece_image_area_formula` applies to a Borel hull of each piece `M ∩ K ∩ D i` inside `D i`,
and `ts_fv_lintegral_image_eq_of_pieces` glues the pieces. -/
theorem Submission.ts_fv_image_mass_area_formula : ∀ (n ℓ : ℕ) (a : RectifiablePair n ℓ) (N₀ : Set (Ambient n ℓ)) (C : ℕ → Set (EuclideanSpace ℝ (Fin n))) (F : ℕ → EuclideanSpace ℝ (Fin n) → Ambient n ℓ) (f : Ambient n ℓ → Ambient n ℓ) (K : Set (Ambient n ℓ)), 0 < n → MeasurableSet N₀ → (μHE[n] : Measure (Ambient n ℓ)) N₀ = 0 → a.M ⊆ N₀ ∪ ⋃ i, F i '' C i → (∀ i, IsCompact (C i) ∧ (∃ K : NNReal, LipschitzWith K (F i)) ∧ (∀ w ∈ C i, DifferentiableAt ℝ (F i) w ∧ Function.Injective (fderiv ℝ (F i) w)) ∧ ContinuousOn (fderiv ℝ (F i)) (C i) ∧ ∃ c : ℝ, 0 < c ∧ ∀ v ∈ C i, ∀ w ∈ C i, c * ‖v - w‖ ≤ ‖F i v - F i w‖) → (∀ᵐ x ∂(μHE[n] : Measure (Ambient n ℓ)).restrict a.M, ∀ i, ∀ w ∈ C i, F i w = x → (mk a).tangentSpace x = LinearMap.range (fderiv ℝ (F i) w).toLinearMap) → Function.Injective f → (∃ L : NNReal, LipschitzWith L f) → (∀ y, DifferentiableAt ℝ f y) → MeasurableSet K → imageMass a f K = ∫⁻ x in a.M ∩ K, ENNReal.ofReal (a.θ x * Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (n + ℓ) ↦ inner ℝ (fderiv ℝ f x (((mk a).tangentSpace x).starProjection (EuclideanSpace.single i (1 : ℝ)))) (fderiv ℝ f x (((mk a).tangentSpace x).starProjection (EuclideanSpace.single j (1 : ℝ)))) + inner ℝ (EuclideanSpace.single i (1 : ℝ) - ((mk a).tangentSpace x).starProjection (EuclideanSpace.single i (1 : ℝ))) (EuclideanSpace.single j (1 : ℝ) - ((mk a).tangentSpace x).starProjection (EuclideanSpace.single j (1 : ℝ)))))) ∂μHE[n] := by
  intro n ℓ a N₀ C F f K _hn hN₀ hN₀0 hcover hpieces htan hfinj hfLip hfdiff hK
  obtain ⟨L, hL⟩ := hfLip
  -- `jac P y = √det(⟪Df(y) p eᵢ, Df(y) p eⱼ⟫ + ⟪q eᵢ, q eⱼ⟫)`, `p = P.starProjection`, `q = 1 - p`
  let jac : Submodule ℝ (Ambient n ℓ) → Ambient n ℓ → ℝ := fun P y ↦
    Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (n + ℓ) ↦
      inner ℝ (fderiv ℝ f y (P.starProjection (EuclideanSpace.single i (1 : ℝ))))
          (fderiv ℝ f y (P.starProjection (EuclideanSpace.single j (1 : ℝ)))) +
        inner ℝ
          (EuclideanSpace.single i (1 : ℝ) - P.starProjection (EuclideanSpace.single i (1 : ℝ)))
          (EuclideanSpace.single j (1 : ℝ) - P.starProjection (EuclideanSpace.single j (1 : ℝ)))))
  -- the density `u = θ ∘ f⁻¹` of the image and the density `g = θ jac(Df, T)` on `M`
  let u : Ambient n ℓ → ℝ≥0∞ := fun y ↦ ENNReal.ofReal (a.θ (Function.invFun f y))
  let g : Ambient n ℓ → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (a.θ x * jac ((mk a).tangentSpace x) x)
  show ∫⁻ y in f '' (a.M ∩ K), u y ∂μHE[n] = ∫⁻ x in a.M ∩ K, g x ∂μHE[n]
  -- `f` maps `Hⁿ`-null sets to null sets (it is Lipschitz) and Borel sets to Borel sets
  -- (Lusin–Souslin), hence null-measurable sets to null-measurable sets
  have hnull : ∀ Y : Set (Ambient n ℓ), (μHE[n] : Measure (Ambient n ℓ)) Y = 0 →
      (μHE[n] : Measure (Ambient n ℓ)) (f '' Y) = 0 := fun Y hY ↦
    le_antisymm ((Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
      hL.lipschitzOnWith).trans (by rw [hY, mul_zero])) bot_le
  have hnm : ∀ Y : Set (Ambient n ℓ), NullMeasurableSet Y (μHE[n] : Measure (Ambient n ℓ)) →
      NullMeasurableSet (f '' Y) (μHE[n] : Measure (Ambient n ℓ)) := by
    intro Y hY
    obtain ⟨Y₀, hY₀Y, hY₀, hY₀ae⟩ := hY.exists_measurable_subset_ae_eq
    rw [← Set.union_sdiff_cancel hY₀Y, Set.image_union]
    exact (hY₀.image_of_continuousOn_injOn hL.continuous.continuousOn
      hfinj.injOn).nullMeasurableSet.union
        (NullMeasurableSet.of_null (hnull _ (ae_le_set.1 hY₀ae.symm.le)))
  -- disjointify the cover: the Borel sets `D i = F i (C i) \ (N₀ ∪ ⋃_{j < i} F j (C j))`
  have hFC : ∀ i, MeasurableSet (F i '' C i) := fun i ↦ by
    obtain ⟨hCc, ⟨LF, hLF⟩, -⟩ := hpieces i
    exact (hCc.image hLF.continuous).measurableSet
  let D : ℕ → Set (Ambient n ℓ) := fun i ↦ F i '' C i \ (N₀ ∪ ⋃ j : Fin i, F j '' C j)
  have hDm : ∀ i, MeasurableSet (D i) := fun i ↦
    (hFC i).diff (hN₀.union (MeasurableSet.iUnion fun j : Fin i ↦ hFC j))
  have hDsub : ∀ i, D i ⊆ F i '' C i := fun _ ↦ Set.sdiff_subset
  have hDdisj : Pairwise fun i j ↦ Disjoint (D i) (D j) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact Set.disjoint_left.2 fun x hxi hxj ↦ hxj.2 (Or.inr (Set.mem_iUnion.2 ⟨⟨i, h⟩, hxi.1⟩))
    · exact Set.disjoint_left.2 fun x hxi hxj ↦ hxi.2 (Or.inr (Set.mem_iUnion.2 ⟨⟨j, h⟩, hxj.1⟩))
  -- the `D i` cover `(M ∩ K) \ N₀`: a point of `M \ N₀` lies in `D i` for the least `i` with
  -- `x ∈ F i (C i)`
  have hrem : (μHE[n] : Measure (Ambient n ℓ)) ((a.M ∩ K) \ ⋃ i, D i) = 0 := by
    classical
    refine measure_mono_null (fun x hx ↦ ?_) hN₀0
    by_contra hxN
    have hex : ∃ i, x ∈ F i '' C i := Set.mem_iUnion.1 (Or.resolve_left (hcover hx.1.1) hxN)
    refine hx.2 (Set.mem_iUnion.2 ⟨Nat.find hex, Nat.find_spec hex, ?_⟩)
    rintro (h | h)
    · exact hxN h
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 h
      exact Nat.find_min hex j.2 hj
  refine Submission.ts_fv_lintegral_image_eq_of_pieces (Ambient n ℓ) μHE[n] f (a.M ∩ K) D u g
    hfinj hnull hnm (a.isRectifiablePair.measurable.inter hK.nullMeasurableSet) hDm hDdisj hrem
    fun i ↦ ?_
  -- the piece `M ∩ K ∩ D i`
  obtain ⟨hCc, ⟨LF, hLF⟩, hdiff, -, c, hc, hlow⟩ := hpieces i
  -- `F i` is injective on `C i` by the lower bound `c ‖v - w‖ ≤ ‖F i v - F i w‖`
  have hinj : Set.InjOn (F i) (C i) := fun v hv w hw hvw ↦ by
    by_contra hne
    have h := hlow v hv w hw
    rw [hvw, sub_self, norm_zero] at h
    exact not_le.2 (mul_pos hc (norm_pos_iff.2 (sub_ne_zero.2 hne))) h
  -- a Borel hull `A' ∩ D i` of the piece, which differs from it by an `Hⁿ`-null set
  have hZnm : NullMeasurableSet (a.M ∩ K ∩ D i) (μHE[n] : Measure (Ambient n ℓ)) :=
    (a.isRectifiablePair.measurable.inter hK.nullMeasurableSet).inter (hDm i).nullMeasurableSet
  obtain ⟨A', hA'Z, hA', hA'ae⟩ := hZnm.exists_measurable_superset_ae_eq
  have hZA : a.M ∩ K ∩ D i ⊆ A' ∩ D i := fun x hx ↦ ⟨hA'Z hx, hx.2⟩
  have hAZ : (μHE[n] : Measure (Ambient n ℓ)) ((A' ∩ D i) \ (a.M ∩ K ∩ D i)) = 0 :=
    measure_mono_null (Set.sdiff_subset_sdiff_left Set.inter_subset_left) (ae_le_set.1 hA'ae.le)
  have hAae : A' ∩ D i =ᵐ[(μHE[n] : Measure (Ambient n ℓ))] a.M ∩ K ∩ D i :=
    ae_eq_set.2 ⟨hAZ, by rw [Set.sdiff_eq_empty.2 hZA, measure_empty]⟩
  have hfAae : f '' (A' ∩ D i) =ᵐ[(μHE[n] : Measure (Ambient n ℓ))] f '' (a.M ∩ K ∩ D i) :=
    ae_eq_set.2 ⟨by rw [← Set.image_sdiff hfinj]; exact hnull _ hAZ,
      by rw [Set.sdiff_eq_empty.2 (Set.image_mono hZA), measure_empty]⟩
  -- the area formula on the hull, with the tangent planes `P y = range DF i (F i⁻¹ y)`
  let P : Ambient n ℓ → Submodule ℝ (Ambient n ℓ) := fun y ↦
    LinearMap.range (fderiv ℝ (F i) (Function.invFunOn (F i) (C i) y)).toLinearMap
  have harea : ∫⁻ y in f '' (A' ∩ D i), u y ∂μHE[n] =
      ∫⁻ y in A' ∩ D i, ENNReal.ofReal (jac (P y) y) * u (f y) ∂μHE[n] :=
    Submission.ts_fv_piece_image_area_formula n ℓ (C i) (F i) f (A' ∩ D i) P u hCc.measurableSet
      ⟨LF, hLF⟩ (fun v hv ↦ (hdiff v hv).1) hinj ⟨L, hL⟩ hfinj.injOn (fun y _ ↦ hfdiff y)
      (hA'.inter (hDm i)) (Set.inter_subset_right.trans (hDsub i)) fun v hv _ ↦ by
        show LinearMap.range
          (fderiv ℝ (F i) (Function.invFunOn (F i) (C i) (F i v))).toLinearMap = _
        rw [hinj.leftInvOn_invFunOn hv]
  rw [setLIntegral_congr hfAae.symm, harea, setLIntegral_congr hAae]
  -- on the piece, `P x = T_x V` a.e. by the tangent hypothesis, and `u (f x) = θ x`
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_mem₀ hZnm,
    ae_restrict_of_ae_restrict_of_subset (fun x hx ↦ hx.1.1 : a.M ∩ K ∩ D i ⊆ a.M) htan]
    with x hx htx
  have hxC : x ∈ F i '' C i := hDsub i hx.2
  have hT : (mk a).tangentSpace x = P x :=
    htx i _ (Function.invFunOn_mem hxC) (Function.invFunOn_eq hxC)
  have hjac : 0 ≤ jac (P x) x := Real.sqrt_nonneg _
  show ENNReal.ofReal (jac (P x) x) * ENNReal.ofReal (a.θ (Function.invFun f (f x))) =
    ENNReal.ofReal (a.θ x * jac ((mk a).tangentSpace x) x)
  rw [Function.leftInverse_invFun hfinj x, hT, ENNReal.ofReal_mul' hjac, mul_comm]
/-- **Determinant lower bound for a coercive symmetric matrix** (used for Simon Ch. 4, 2.2). If
`S` is a real symmetric `N × N` matrix and `c ∑ᵢ ξᵢ² ≤ ∑ᵢ ∑ⱼ ξᵢ Sᵢⱼ ξⱼ` for every `ξ`, with
`c ≥ 0`, then `cᴺ ≤ det S`. Induction on `N`: testing `ξ = e₀` gives `c ≤ S₀₀`; if `S₀₀ > 0`,
row operations give `det S = S₀₀ · det S'` for the Schur complement
`S'ᵢⱼ = S_{i+1,j+1} - S_{i+1,0} S_{0,j+1} / S₀₀`, which is again symmetric and `c`-coercive; if
`S₀₀ = 0`, then `c = 0` and the first row of `S` vanishes. -/
theorem Submission.ts_fv_det_ge_pow_of_quadForm_ge : (∀ (N : ℕ) (S : Matrix (Fin N) (Fin N) ℝ) (c : ℝ), 0 ≤ c → (∀ i j, S i j = S j i) → (∀ ξ : Fin N → ℝ, c * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, ξ i * S i j * ξ j) → c ^ N ≤ S.det) := by
  intro N
  induction N with
  | zero =>
    intro S c _ _ _
    simp [Matrix.det_isEmpty]
  | succ n ih =>
    intro S c hc hsym hq
    -- Split `ξ = (t, η)` along the first coordinate.
    have hnorm : ∀ (t : ℝ) (η : Fin n → ℝ),
        ∑ i, (Fin.cons t η : Fin (n + 1) → ℝ) i ^ 2 = t ^ 2 + ∑ i, η i ^ 2 := by
      intro t η
      simp [Fin.sum_univ_succ]
    have hexp : ∀ (t : ℝ) (η : Fin n → ℝ),
        ∑ i, ∑ j, (Fin.cons t η : Fin (n + 1) → ℝ) i * S i j * (Fin.cons t η : Fin (n + 1) → ℝ) j =
          S 0 0 * t ^ 2 + 2 * t * ∑ j, S 0 j.succ * η j +
            ∑ i, ∑ j, η i * S i.succ j.succ * η j := by
      intro t η
      simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      have h1 : ∑ i : Fin n, η i * S i.succ 0 * t = t * ∑ j, S 0 j.succ * η j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hsym]
        ring
      have h2 : ∑ j : Fin n, t * S 0 j.succ * η j = t * ∑ j, S 0 j.succ * η j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [Finset.sum_add_distrib, h1, h2]
      ring
    -- `ξ = e₀` gives `c ≤ S 0 0`.
    have hca : c ≤ S 0 0 := by
      have h := hq (Fin.cons 1 0)
      rw [hnorm, hexp] at h
      simpa using h
    rcases (hc.trans hca).lt_or_eq with hapos | ha0
    · -- `S 0 0 > 0`: pass to the Schur complement `S'` of the pivot `S 0 0`.
      have ha : S 0 0 ≠ 0 := hapos.ne'
      obtain ⟨S', hS'⟩ : ∃ S' : Matrix (Fin n) (Fin n) ℝ,
          S' = Matrix.of fun i j => S i.succ j.succ - S i.succ 0 * S 0 j.succ / S 0 0 := ⟨_, rfl⟩
      have hS'ij : ∀ i j, S' i j = S i.succ j.succ - S i.succ 0 * S 0 j.succ / S 0 0 := by
        intro i j
        rw [hS']
        rfl
      -- Row operations clear the first column below the pivot: `det S = S 0 0 * det S'`.
      have hdet : S.det = S 0 0 * S'.det := by
        let T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := Matrix.of fun i j =>
          S i j + (Fin.cons 0 fun i' => -(S i'.succ 0 / S 0 0) : Fin (n + 1) → ℝ) i * S 0 j
        have hT : T.det = S.det :=
          Matrix.det_eq_of_forall_row_eq_smul_add_const _ 0 (Fin.cons_zero _ _) fun _ _ => rfl
        have hcol : ∀ i : Fin n, T i.succ 0 = 0 := by
          intro i
          simp only [T, Matrix.of_apply, Fin.cons_succ]
          field_simp
          ring
        have hsub : T.submatrix (Fin.succAbove 0) Fin.succ = S' := by
          ext i j
          simp only [T, Matrix.submatrix_apply, Fin.succAbove_zero, Matrix.of_apply, Fin.cons_succ,
            hS'ij]
          ring
        rw [← hT, Matrix.det_succ_column_zero, Fin.sum_univ_succ]
        simp only [hcol, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, hsub]
        simp [T]
      -- `S'` is symmetric.
      have hS'sym : ∀ i j, S' i j = S' j i := by
        intro i j
        rw [hS'ij, hS'ij, hsym i.succ j.succ, hsym i.succ 0, hsym 0 j.succ]
        ring
      -- The quadratic form of `S'`.
      have hS'form : ∀ η : Fin n → ℝ, ∑ i, ∑ j, η i * S' i j * η j =
          ∑ i, ∑ j, η i * S i.succ j.succ * η j - (∑ j, S 0 j.succ * η j) ^ 2 / S 0 0 := by
        intro η
        have hb : ∑ i, η i * S i.succ 0 = ∑ j, S 0 j.succ * η j :=
          Finset.sum_congr rfl fun i _ => by rw [hsym]; ring
        calc ∑ i, ∑ j, η i * S' i j * η j
            = ∑ i, ∑ j, (η i * S i.succ j.succ * η j -
                η i * S i.succ 0 * (S 0 j.succ * η j) / S 0 0) := by
              refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
              rw [hS'ij]
              ring
          _ = ∑ i, ∑ j, η i * S i.succ j.succ * η j -
                (∑ i, η i * S i.succ 0) * (∑ j, S 0 j.succ * η j) / S 0 0 := by
              rw [Finset.sum_mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.sum_div, ← Finset.sum_sub_distrib]
          _ = _ := by rw [hb, sq]
      -- `S'` is again `c`-coercive: test the hypothesis on `ξ = (-b / S 0 0, η)`.
      have hS'q : ∀ η : Fin n → ℝ, c * ∑ i, η i ^ 2 ≤ ∑ i, ∑ j, η i * S' i j * η j := by
        intro η
        rw [hS'form]
        have h := hq (Fin.cons (-(∑ j, S 0 j.succ * η j) / S 0 0) η)
        rw [hnorm, hexp] at h
        have ht : S 0 0 * (-(∑ j, S 0 j.succ * η j) / S 0 0) ^ 2 +
            2 * (-(∑ j, S 0 j.succ * η j) / S 0 0) * ∑ j, S 0 j.succ * η j =
            -((∑ j, S 0 j.succ * η j) ^ 2 / S 0 0) := by
          field_simp
          ring
        have hct : 0 ≤ c * (-(∑ j, S 0 j.succ * η j) / S 0 0) ^ 2 :=
          mul_nonneg hc (sq_nonneg _)
        linarith
      have hih := ih S' c hc hS'sym hS'q
      rw [hdet, pow_succ]
      calc c ^ n * c ≤ S'.det * S 0 0 :=
            mul_le_mul hih hca hc ((pow_nonneg hc n).trans hih)
        _ = S 0 0 * S'.det := mul_comm _ _
    · -- `S 0 0 = 0`: then `c = 0` and the first row of `S` vanishes.
      have hc0 : c = 0 := le_antisymm (ha0 ▸ hca) hc
      have hrow : ∀ j, S 0 j = 0 := by
        intro j
        refine Fin.cases ha0.symm (fun j' => ?_) j
        by_contra hb
        have h := hq (Fin.cons
          (-(∑ i, ∑ j, (Pi.single j' 1 : Fin n → ℝ) i * S i.succ j.succ *
              (Pi.single j' 1 : Fin n → ℝ) j + 1) / (2 * S 0 j'.succ))
          (Pi.single j' 1))
        rw [hnorm, hexp, ← ha0, hc0] at h
        have hb' : ∑ j, S 0 j.succ * (Pi.single j' 1 : Fin n → ℝ) j = S 0 j'.succ := by
          simp [Pi.single_apply]
        rw [hb'] at h
        have key : 2 * (-(∑ i, ∑ j, (Pi.single j' 1 : Fin n → ℝ) i * S i.succ j.succ *
              (Pi.single j' 1 : Fin n → ℝ) j + 1) / (2 * S 0 j'.succ)) * S 0 j'.succ =
            -(∑ i, ∑ j, (Pi.single j' 1 : Fin n → ℝ) i * S i.succ j.succ *
              (Pi.single j' 1 : Fin n → ℝ) j + 1) := by
          field_simp
        linarith
      rw [Matrix.det_eq_zero_of_row_eq_zero 0 hrow, hc0, zero_pow (Nat.succ_ne_zero n)]
/-- **Jacobi's formula for an entrywise-differentiable matrix family** (Simon Ch. 2, 5.2–5.3;
used for `∂_t J = div_M X` in Ch. 4, 2.2). If every entry `s ↦ A(s)_{ij}` has derivative `A'_{ij}`
at `t`, `|A(t)_{ij}| ≤ M` and `|A'_{ij}| ≤ M'`, then `s ↦ det A(s)` has a derivative `D` at `t`
with `|D| ≤ N! N M' M^{N-1}`, and `D = trace A'` when `A(t) = I`. -/
theorem Submission.ts_fv_hasDerivAt_det_of_entries : ∀ (N : ℕ) (A : ℝ → Matrix (Fin N) (Fin N) ℝ) (A' : Matrix (Fin N) (Fin N) ℝ) (t M M' : ℝ), (∀ i j, HasDerivAt (fun s ↦ A s i j) (A' i j) t) → (∀ i j, |A t i j| ≤ M) → (∀ i j, |A' i j| ≤ M') → ∃ D : ℝ, HasDerivAt (fun s ↦ (A s).det) D t ∧ |D| ≤ (N.factorial : ℝ) * N * M' * M ^ (N - 1) ∧ (A t = 1 → D = A'.trace) := by
  intro N A A' t M M' hA hM hM'
  -- `D = ∑_σ ε(σ) ∑_k (∏_{i ≠ k} A(t)_{σ(i) i}) A'_{σ(k) k}`, the derivative of the Leibniz
  -- formula.
  refine ⟨∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
      ∑ k : Fin N, (∏ i ∈ Finset.univ.erase k, A t (σ i) i) * A' (σ k) k, ?_, ?_, ?_⟩
  · -- Product rule on each Leibniz term, then constant multiples and the finite sum.
    have hdet : (fun s ↦ (A s).det) = fun s ↦ ∑ σ : Equiv.Perm (Fin N),
        ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, A s (σ i) i := by
      funext s
      exact Matrix.det_apply' (A s)
    rw [hdet]
    refine HasDerivAt.fun_sum fun σ _ ↦ HasDerivAt.const_mul _ ?_
    simpa only [smul_eq_mul] using
      HasDerivAt.fun_finsetProd (u := Finset.univ) (f := fun i s ↦ A s (σ i) i)
        (f' := fun i ↦ A' (σ i) i) fun i _ ↦ hA (σ i) i
  · -- Each `∏_{i ≠ k}` has `N - 1` factors bounded by `M`; there are `N` indices `k` and `N!`
    -- permutations `σ`.
    calc |∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∑ k : Fin N, (∏ i ∈ Finset.univ.erase k, A t (σ i) i) * A' (σ k) k|
        ≤ ∑ σ : Equiv.Perm (Fin N), |((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∑ k : Fin N, (∏ i ∈ Finset.univ.erase k, A t (σ i) i) * A' (σ k) k| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _σ : Equiv.Perm (Fin N), ∑ _k : Fin N, M' * M ^ (N - 1) := by
          refine Finset.sum_le_sum fun σ _ ↦ ?_
          rw [abs_mul, abs_unit_intCast, one_mul]
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
          have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM k k)
          have hprod : ∏ i ∈ Finset.univ.erase k, |A t (σ i) i| ≤ M ^ (N - 1) := by
            calc ∏ i ∈ Finset.univ.erase k, |A t (σ i) i|
                ≤ ∏ _i ∈ Finset.univ.erase k, M :=
                  Finset.prod_le_prod₀ (fun i _ ↦ abs_nonneg _) fun i _ ↦ hM _ _
              _ = M ^ (N - 1) := by
                  rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _),
                    Finset.card_univ, Fintype.card_fin]
          rw [abs_mul, Finset.abs_prod, mul_comm M']
          exact mul_le_mul hprod (hM' _ _) (abs_nonneg _) (pow_nonneg hM0 _)
      _ = (N.factorial : ℝ) * N * M' * M ^ (N - 1) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
            nsmul_eq_mul]
          ring
  · -- At `A(t) = I` only `σ = id` contributes: for `σ ≠ id` pick `σ j ≠ j`; then every
    -- `∏_{i ≠ k}` contains the factor `I_{σ j, j} = 0` or `I_{σ (σ j), σ j} = 0`.
    intro h1
    have hAt1 : ∀ a, A t a a = 1 := fun a ↦
      (congrFun (congrFun h1 a) a).trans (Matrix.one_apply_eq a)
    have hAt0 : ∀ a b, a ≠ b → A t a b = 0 := fun a b hab ↦
      (congrFun (congrFun h1 a) b).trans (Matrix.one_apply_ne hab)
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin N))]
    · rw [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul, Matrix.trace]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      have hk : ∏ i ∈ Finset.univ.erase k, A t ((1 : Equiv.Perm (Fin N)) i) i = 1 :=
        Finset.prod_eq_one fun i _ ↦ hAt1 i
      rw [hk, one_mul]
      rfl
    · intro σ _ hσ
      obtain ⟨j, hj⟩ : ∃ j, σ j ≠ j := by
        by_contra h
        exact hσ (Equiv.ext fun x ↦ not_not.mp fun hx ↦ h ⟨x, hx⟩)
      have hzero : ∀ k, ∏ i ∈ Finset.univ.erase k, A t (σ i) i = 0 := by
        intro k
        by_cases hk : k = j
        · subst hk
          exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩)
            (hAt0 _ _ fun h ↦ hj (σ.injective h))
        · exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨fun h ↦ hk h.symm, Finset.mem_univ _⟩)
            (hAt0 _ _ hj)
      simp only [hzero, zero_mul, Finset.sum_const_zero, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
/-- **Tangential trace in the standard basis** (used for `∂_t J = div_M X`, Ch. 4, 2.2).
For a subspace `P` of `ℝ^N` with orthogonal projection `p_P`, a linear map `L` and the standard
basis `e_k`: `∑ₖ ⟨L(p_P eₖ), p_P eₖ⟩ = trace (L ∘ p_P)`. -/
theorem Submission.ts_fv_sum_inner_starProjection_eq_trace : ∀ (N : ℕ) (P : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (L : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)), ∑ k : Fin N, inner ℝ (L (P.starProjection (EuclideanSpace.single k (1 : ℝ)))) (P.starProjection (EuclideanSpace.single k (1 : ℝ))) = LinearMap.trace ℝ (EuclideanSpace ℝ (Fin N)) (L.toLinearMap ∘ₗ P.starProjection.toLinearMap) := by
  intro N P L
  -- `p_P ∘ p_P = p_P`, so `L ∘ p_P = (L ∘ p_P) ∘ p_P`.
  have hpp : L.toLinearMap ∘ₗ P.starProjection.toLinearMap =
      (L.toLinearMap ∘ₗ P.starProjection.toLinearMap) ∘ₗ P.starProjection.toLinearMap := by
    ext v : 1
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      Submodule.starProjection_eq_self_iff.mpr (P.starProjection_apply_mem v)]
  -- Cyclicity gives `trace (p_P ∘ L ∘ p_P)`; compute it in the orthonormal basis `eₖ`.
  rw [hpp, LinearMap.trace_comp_comm',
    LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis, Matrix.trace]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
  -- `⟨L(p_P eₖ), p_P eₖ⟩ = ⟨p_P eₖ, L(p_P eₖ)⟩ = ⟨eₖ, p_P(L(p_P eₖ))⟩` (`p_P` is self-adjoint).
  rw [real_inner_comm, Submodule.inner_starProjection_left_eq_right]
/-- **Entry bound and uniform ellipticity of the tangential matrix** (auxiliary to the Jacobian
computation behind Simon Ch. 4, 2.2, done as in Ch. 2, 5.2–5.3). Let `p` be the orthogonal
projection onto `P ⊆ ℝᴺ`, `eᵢ` the standard basis and `L` a linear map with `‖L‖ ≤ b`,
`‖v‖ ≤ b‖L v‖` and `b ≥ 1`. Then `S_ij = ⟨L(p eᵢ), L(p eⱼ)⟩ + ⟨eᵢ - p eᵢ, eⱼ - p eⱼ⟩` satisfies
`|S_ij| ≤ b² + 1` and `(b²)⁻¹ ∑ᵢ ξᵢ² ≤ ∑ᵢ ∑ⱼ ξᵢ S_ij ξⱼ`: for `v = ∑ᵢ ξᵢ eᵢ` the form equals
`‖L(p v)‖² + ‖v - p v‖²`, while `∑ᵢ ξᵢ² = ‖v‖² = ‖p v‖² + ‖v - p v‖²`. -/
theorem Submission.ts_fv_tangential_matrix_estimates : (∀ (N : ℕ) (P : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (L : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) (b : ℝ), 1 ≤ b → ‖L‖ ≤ b → (∀ v, ‖v‖ ≤ b * ‖L v‖) → (∀ i j : Fin N, |inner ℝ (L (P.starProjection (EuclideanSpace.single i (1 : ℝ)))) (L (P.starProjection (EuclideanSpace.single j (1 : ℝ)))) + inner ℝ (EuclideanSpace.single i (1 : ℝ) - P.starProjection (EuclideanSpace.single i (1 : ℝ))) (EuclideanSpace.single j (1 : ℝ) - P.starProjection (EuclideanSpace.single j (1 : ℝ)))| ≤ b ^ 2 + 1) ∧ ∀ ξ : Fin N → ℝ, (b ^ 2)⁻¹ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, ξ i * (inner ℝ (L (P.starProjection (EuclideanSpace.single i (1 : ℝ)))) (L (P.starProjection (EuclideanSpace.single j (1 : ℝ)))) + inner ℝ (EuclideanSpace.single i (1 : ℝ) - P.starProjection (EuclideanSpace.single i (1 : ℝ))) (EuclideanSpace.single j (1 : ℝ) - P.starProjection (EuclideanSpace.single j (1 : ℝ)))) * ξ j) := by
  intro N P L b hb hL hLinv
  have hb0 : 0 < b := one_pos.trans_le hb
  -- Pythagoras: `‖v‖² = ‖p v‖² + ‖v - p v‖²`, since `v - p v ⊥ P ∋ p v`.
  have pyth : ∀ v : EuclideanSpace ℝ (Fin N),
      ‖v‖ ^ 2 = ‖P.starProjection v‖ ^ 2 + ‖v - P.starProjection v‖ ^ 2 := by
    intro v
    have h0 : inner ℝ (P.starProjection v) (v - P.starProjection v) = 0 := by
      rw [real_inner_comm]
      exact Submodule.starProjection_inner_eq_zero v _ (P.starProjection_apply_mem v)
    have h := norm_add_sq_real (P.starProjection v) (v - P.starProjection v)
    rwa [add_sub_cancel, h0, mul_zero, add_zero] at h
  refine ⟨fun i j ↦ ?_, fun ξ ↦ ?_⟩
  · -- (a) Cauchy–Schwarz with `‖L(p eₖ)‖ ≤ ‖L‖‖p eₖ‖ ≤ b` and `‖eₖ - p eₖ‖ ≤ ‖eₖ‖ = 1`.
    have he : ∀ k : Fin N, ‖(EuclideanSpace.single k (1 : ℝ) : EuclideanSpace ℝ (Fin N))‖ = 1 :=
      fun k ↦ by simp
    have hA : ∀ k : Fin N, ‖L (P.starProjection (EuclideanSpace.single k (1 : ℝ)))‖ ≤ b := by
      intro k
      calc ‖L (P.starProjection (EuclideanSpace.single k (1 : ℝ)))‖
          ≤ ‖L‖ * ‖P.starProjection (EuclideanSpace.single k (1 : ℝ))‖ := L.le_opNorm _
        _ ≤ b * 1 := by
          gcongr
          exact (P.norm_starProjection_apply_le _).trans (he k).le
        _ = b := mul_one b
    have hB : ∀ k : Fin N, ‖EuclideanSpace.single k (1 : ℝ) -
        P.starProjection (EuclideanSpace.single k (1 : ℝ))‖ ≤ 1 := by
      intro k
      have h := pyth (EuclideanSpace.single k (1 : ℝ))
      rw [he k] at h
      nlinarith [norm_nonneg (EuclideanSpace.single k (1 : ℝ) -
        P.starProjection (EuclideanSpace.single k (1 : ℝ))),
        sq_nonneg ‖P.starProjection (EuclideanSpace.single k (1 : ℝ))‖]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (abs_real_inner_le_norm _ _).trans ?_
      rw [sq]
      exact mul_le_mul (hA i) (hA j) (norm_nonneg _) hb0.le
    · refine (abs_real_inner_le_norm _ _).trans ?_
      calc _ ≤ (1 : ℝ) * 1 := mul_le_mul (hB i) (hB j) (norm_nonneg _) zero_le_one
        _ = 1 := mul_one 1
  · -- (b) With `v = ∑ᵢ ξᵢ eᵢ` the form is `‖L(p v)‖² + ‖v - p v‖²`, and `∑ᵢ ξᵢ² = ‖v‖²`.
    set v : EuclideanSpace ℝ (Fin N) := ∑ i, ξ i • EuclideanSpace.single i (1 : ℝ) with hv
    -- bilinearity: `⟨∑ᵢ ξᵢ uᵢ, ∑ⱼ ξⱼ uⱼ⟩ = ∑ᵢ ∑ⱼ ξᵢ ⟨uᵢ, uⱼ⟩ ξⱼ`
    have bil : ∀ u : Fin N → EuclideanSpace ℝ (Fin N),
        inner ℝ (∑ i, ξ i • u i) (∑ j, ξ j • u j) = ∑ i, ∑ j, ξ i * inner ℝ (u i) (u j) * ξ j := by
      intro u
      rw [sum_inner]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [real_inner_smul_left, inner_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [real_inner_smul_right]
      ring
    have hLv : L (P.starProjection v) =
        ∑ i, ξ i • L (P.starProjection (EuclideanSpace.single i (1 : ℝ))) := by
      simp only [hv, map_sum, map_smul]
    have hQv : v - P.starProjection v = ∑ i, ξ i • (EuclideanSpace.single i (1 : ℝ) -
        P.starProjection (EuclideanSpace.single i (1 : ℝ))) := by
      simp only [hv, map_sum, map_smul, smul_sub, Finset.sum_sub_distrib]
    have hform : ∑ i, ∑ j, ξ i * (inner ℝ (L (P.starProjection (EuclideanSpace.single i (1 : ℝ))))
        (L (P.starProjection (EuclideanSpace.single j (1 : ℝ)))) +
        inner ℝ
          (EuclideanSpace.single i (1 : ℝ) - P.starProjection (EuclideanSpace.single i (1 : ℝ)))
          (EuclideanSpace.single j (1 : ℝ) - P.starProjection (EuclideanSpace.single j (1 : ℝ)))) *
          ξ j = ‖L (P.starProjection v)‖ ^ 2 + ‖v - P.starProjection v‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hLv, hQv,
        bil fun i ↦ L (P.starProjection (EuclideanSpace.single i (1 : ℝ))),
        bil fun i ↦ EuclideanSpace.single i (1 : ℝ) -
          P.starProjection (EuclideanSpace.single i (1 : ℝ))]
      simp only [mul_add, add_mul, Finset.sum_add_distrib]
    have hnv : ‖v‖ ^ 2 = ∑ i, ξ i ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, hv, bil fun i ↦ EuclideanSpace.single i (1 : ℝ)]
      simp [EuclideanSpace.inner_single_left, sq]
    -- `‖p v‖ ≤ b‖L(p v)‖` and `(b²)⁻¹ ≤ 1`
    have hlow : ‖P.starProjection v‖ ^ 2 ≤ b ^ 2 * ‖L (P.starProjection v)‖ ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hLinv _) 2
    rw [hform, ← hnv, pyth v, mul_add]
    exact add_le_add ((inv_mul_le_iff₀ (by positivity)).2 hlow)
      (mul_le_of_le_one_left (sq_nonneg _) (inv_le_one_of_one_le₀ (one_le_pow₀ hb)))

/-- **Derivative of the tangential Jacobian** (Ch. 4, 2.2 with Ch. 2, 5.2–5.3: Jacobi's formula).
Let `p_P` be the orthogonal projection onto a subspace `P ⊆ ℝ^N`, `q_P = I - p_P`, and let `Λ(t)`
be a family of linear maps with `Λ(0) = I`, derivative `Λ'(t)`, and `‖Λ(t)‖, ‖Λ'(t)‖ ≤ B`,
`|v| ≤ B |Λ(t) v|` for `|t| < δ`. Then the tangential Jacobian
`J(t) = (det [⟨Λ(t) p_P eᵢ, Λ(t) p_P eⱼ⟩ + ⟨q_P eᵢ, q_P eⱼ⟩])^{1/2}` satisfies `0 ≤ J ≤ C`,
`|J'| ≤ C` on `(-δ, δ)` with `C = C(N, B)`, and `J'(0) = trace (Λ'(0) ∘ p_P)`. -/
theorem Submission.ts_fv_tangential_jacobian_hasDerivAt : ∀ (N : ℕ) (B : ℝ), ∃ C : ℝ, ∀ (P : Submodule ℝ (EuclideanSpace ℝ (Fin N))) (Λ Λ' : ℝ → (EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))) (J : ℝ → ℝ) (δ : ℝ), 0 < δ → Λ 0 = 1 → (∀ t ∈ Ioo (-δ) δ, HasDerivAt Λ (Λ' t) t ∧ ‖Λ t‖ ≤ B ∧ ‖Λ' t‖ ≤ B ∧ ∀ v, ‖v‖ ≤ B * ‖Λ t v‖) → (∀ t, J t = Real.sqrt (Matrix.det (Matrix.of fun i j : Fin N ↦ inner ℝ (Λ t (P.starProjection (EuclideanSpace.single i (1 : ℝ)))) (Λ t (P.starProjection (EuclideanSpace.single j (1 : ℝ)))) + inner ℝ (EuclideanSpace.single i (1 : ℝ) - P.starProjection (EuclideanSpace.single i (1 : ℝ))) (EuclideanSpace.single j (1 : ℝ) - P.starProjection (EuclideanSpace.single j (1 : ℝ)))))) → (∀ t ∈ Ioo (-δ) δ, 0 ≤ J t ∧ J t ≤ C ∧ ∃ d : ℝ, HasDerivAt J d t ∧ |d| ≤ C) ∧ HasDerivAt J (LinearMap.trace ℝ (EuclideanSpace ℝ (Fin N)) ((Λ' 0).toLinearMap ∘ₗ P.starProjection.toLinearMap)) 0 := by
  intro N B
  -- Step 0: `B₁ = max(B, 1)`, `M₀ = B₁² + 1` and `C = (N! M₀^N)^{1/2} + N! N B₁^{N+2} M₀^{N-1}`.
  obtain ⟨B₁, hBB₁, hB₁⟩ : ∃ B₁ : ℝ, B ≤ B₁ ∧ 1 ≤ B₁ :=
    ⟨max B 1, le_max_left _ _, le_max_right _ _⟩
  have hB₁0 : 0 < B₁ := zero_lt_one.trans_le hB₁
  obtain ⟨M₀, hM₀⟩ : ∃ M₀ : ℝ, M₀ = B₁ ^ 2 + 1 := ⟨_, rfl⟩
  have hM₀0 : 0 < M₀ := by rw [hM₀]; positivity
  refine ⟨Real.sqrt (N.factorial * M₀ ^ N) + N.factorial * N * B₁ ^ (N + 2) * M₀ ^ (N - 1), ?_⟩
  intro P Λ Λ' J δ hδ hΛ0 hΛ hJ
  -- `S t` is the matrix under the square root and `S' t` its entrywise derivative (step 4).
  obtain ⟨S, hS⟩ : ∃ S : ℝ → Matrix (Fin N) (Fin N) ℝ, ∀ t i j, S t i j =
      inner ℝ (Λ t (P.starProjection (EuclideanSpace.single i (1 : ℝ))))
          (Λ t (P.starProjection (EuclideanSpace.single j (1 : ℝ)))) +
        inner ℝ
          (EuclideanSpace.single i (1 : ℝ) - P.starProjection (EuclideanSpace.single i (1 : ℝ)))
          (EuclideanSpace.single j (1 : ℝ) - P.starProjection (EuclideanSpace.single j (1 : ℝ))) :=
    ⟨fun t ↦ Matrix.of fun i j ↦
      inner ℝ (Λ t (P.starProjection (EuclideanSpace.single i (1 : ℝ))))
          (Λ t (P.starProjection (EuclideanSpace.single j (1 : ℝ)))) +
        inner ℝ
          (EuclideanSpace.single i (1 : ℝ) - P.starProjection (EuclideanSpace.single i (1 : ℝ)))
          (EuclideanSpace.single j (1 : ℝ) - P.starProjection (EuclideanSpace.single j (1 : ℝ))),
      fun _ _ _ ↦ rfl⟩
  obtain ⟨S', hS'⟩ : ∃ S' : ℝ → Matrix (Fin N) (Fin N) ℝ, ∀ t i j, S' t i j =
      inner ℝ (Λ t (P.starProjection (EuclideanSpace.single i (1 : ℝ))))
          (Λ' t (P.starProjection (EuclideanSpace.single j (1 : ℝ)))) +
        inner ℝ (Λ' t (P.starProjection (EuclideanSpace.single i (1 : ℝ))))
          (Λ t (P.starProjection (EuclideanSpace.single j (1 : ℝ)))) :=
    ⟨fun t ↦ Matrix.of fun i j ↦
      inner ℝ (Λ t (P.starProjection (EuclideanSpace.single i (1 : ℝ))))
          (Λ' t (P.starProjection (EuclideanSpace.single j (1 : ℝ)))) +
        inner ℝ (Λ' t (P.starProjection (EuclideanSpace.single i (1 : ℝ))))
          (Λ t (P.starProjection (EuclideanSpace.single j (1 : ℝ)))),
      fun _ _ _ ↦ rfl⟩
  have hJS : ∀ t, J t = Real.sqrt (S t).det := by
    intro t
    rw [hJ t]
    congr 2
    ext i j
    rw [Matrix.of_apply, hS]
  -- On `(-δ, δ)` the hypotheses hold with `B₁` in place of `B`.
  have hbd : ∀ t ∈ Ioo (-δ) δ, ‖Λ t‖ ≤ B₁ ∧ ‖Λ' t‖ ≤ B₁ ∧ ∀ v, ‖v‖ ≤ B₁ * ‖Λ t v‖ := by
    intro t ht
    obtain ⟨-, h1, h2, h3⟩ := hΛ t ht
    exact ⟨h1.trans hBB₁, h2.trans hBB₁,
      fun v ↦ (h3 v).trans (mul_le_mul_of_nonneg_right hBB₁ (norm_nonneg _))⟩
  -- Steps 1 and 2(b): `S t` is symmetric, `|S t i j| ≤ M₀` and `ξᵀ (S t) ξ ≥ B₁⁻² |ξ|²`.
  have hsymm : ∀ t i j, S t i j = S t j i := by
    intro t i j
    rw [hS, hS]
    congr 1 <;> exact real_inner_comm _ _
  have hest : ∀ t ∈ Ioo (-δ) δ, (∀ i j, |S t i j| ≤ M₀) ∧
      ∀ ξ : Fin N → ℝ, (B₁ ^ 2)⁻¹ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, ξ i * S t i j * ξ j := by
    intro t ht
    obtain ⟨h1, -, h3⟩ := hbd t ht
    obtain ⟨hA, hQ⟩ := Submission.ts_fv_tangential_matrix_estimates N P (Λ t) B₁ hB₁ h1 h3
    refine ⟨fun i j ↦ ?_, fun ξ ↦ ?_⟩
    · rw [hS, hM₀]
      exact hA i j
    · simp only [hS]
      exact hQ ξ
  -- Step 2: `(det S t)^{1/2} ≥ B₁^{-N}` (spectral bound) and `|det S t| ≤ N! M₀^N` (Leibniz).
  have hdet : ∀ t ∈ Ioo (-δ) δ,
      (B₁ ^ N)⁻¹ ≤ Real.sqrt (S t).det ∧ |(S t).det| ≤ N.factorial * M₀ ^ N := by
    intro t ht
    obtain ⟨hA, hQ⟩ := hest t ht
    refine ⟨?_, ?_⟩
    · have hc := Submission.ts_fv_det_ge_pow_of_quadForm_ge N (S t) ((B₁ ^ 2)⁻¹) (by positivity)
        (hsymm t) hQ
      refine Real.le_sqrt_of_sq_le ?_
      calc ((B₁ ^ N)⁻¹) ^ 2 = ((B₁ ^ 2)⁻¹) ^ N := by ring
        _ ≤ (S t).det := hc
    · rw [Matrix.det_apply']
      calc |∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, S t (σ i) i|
          ≤ ∑ σ : Equiv.Perm (Fin N), |((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, S t (σ i) i| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _σ : Equiv.Perm (Fin N), ∏ _i : Fin N, M₀ := by
            gcongr with σ
            have hsign : |((Equiv.Perm.sign σ : ℤ) : ℝ)| = 1 := by
              rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
            rw [abs_mul, hsign, one_mul, Finset.abs_prod]
            exact Finset.prod_le_prod₀ (fun i _ ↦ abs_nonneg _) (fun i _ ↦ hA _ _)
        _ = N.factorial * M₀ ^ N := by
            simp [Finset.prod_const, Finset.sum_const, Fintype.card_perm]
  -- Steps 4–6: the entries are differentiable, `|S' t i j| ≤ 2 B₁²`, Jacobi's formula and the
  -- chain rule for the square root.
  have hderiv : ∀ t ∈ Ioo (-δ) δ, ∀ i j, HasDerivAt (fun s ↦ S s i j) (S' t i j) t := by
    intro t ht i j
    have hv : ∀ w, HasDerivAt (fun s ↦ Λ s w) (Λ' t w) t := fun w ↦ by
      simpa using (hΛ t ht).1.clm_apply (hasDerivAt_const t w)
    simp only [hS, hS']
    exact ((hv _).inner ℝ (hv _)).add_const _
  have hderiv_bd : ∀ t ∈ Ioo (-δ) δ, ∀ i j, |S' t i j| ≤ 2 * B₁ ^ 2 := by
    intro t ht i j
    obtain ⟨h1, h2, -⟩ := hbd t ht
    have hL : ∀ L : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N), ‖L‖ ≤ B₁ →
        ∀ k, ‖L (P.starProjection (EuclideanSpace.single k (1 : ℝ)))‖ ≤ B₁ := by
      intro L hL k
      have hp : ‖P.starProjection (EuclideanSpace.single k (1 : ℝ))‖ ≤ 1 :=
        (Submodule.norm_starProjection_apply_le (K := P) _).trans (by simp)
      calc ‖L (P.starProjection (EuclideanSpace.single k (1 : ℝ)))‖
          ≤ ‖L‖ * ‖P.starProjection (EuclideanSpace.single k (1 : ℝ))‖ := L.le_opNorm _
        _ ≤ B₁ * 1 := by gcongr
        _ = B₁ := mul_one _
    -- Cauchy–Schwarz on both terms of `S' t i j`.
    have hx := (abs_real_inner_le_norm _ _).trans
      (mul_le_mul (hL _ h1 i) (hL _ h2 j) (norm_nonneg _) hB₁0.le)
    have hy := (abs_real_inner_le_norm _ _).trans
      (mul_le_mul (hL _ h2 i) (hL _ h1 j) (norm_nonneg _) hB₁0.le)
    rw [hS']
    rw [abs_le] at hx hy ⊢
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hJd : ∀ t ∈ Ioo (-δ) δ, ∃ D : ℝ, HasDerivAt J (D / (2 * Real.sqrt (S t).det)) t ∧
      |D| ≤ N.factorial * N * (2 * B₁ ^ 2) * M₀ ^ (N - 1) ∧ (S t = 1 → D = (S' t).trace) := by
    intro t ht
    obtain ⟨D, hD, hDb, hD1⟩ := Submission.ts_fv_hasDerivAt_det_of_entries N S (S' t) t M₀
      (2 * B₁ ^ 2) (hderiv t ht) (hest t ht).1 (hderiv_bd t ht)
    have hpos : 0 < (S t).det :=
      Real.sqrt_pos.1 ((inv_pos.2 (pow_pos hB₁0 N)).trans_le (hdet t ht).1)
    refine ⟨D, ?_, hDb, hD1⟩
    rw [show J = fun s ↦ Real.sqrt (S s).det from funext hJS]
    exact hD.sqrt hpos.ne'
  refine ⟨fun t ht ↦ ?_, ?_⟩
  · -- Steps 3 and 6: `0 ≤ J t ≤ C` and `|J'(t)| ≤ C`.
    obtain ⟨hlow, hup⟩ := hdet t ht
    obtain ⟨D, hD, hDb, -⟩ := hJd t ht
    have hsq : 0 < Real.sqrt (S t).det := (inv_pos.2 (pow_pos hB₁0 N)).trans_le hlow
    have h2s : 0 < 2 * Real.sqrt (S t).det := mul_pos two_pos hsq
    have hK : 0 ≤ (N.factorial : ℝ) * N * B₁ ^ (N + 2) * M₀ ^ (N - 1) := by positivity
    have hpow : B₁ ^ (N + 2) * (B₁ ^ N)⁻¹ = B₁ ^ 2 := by
      rw [pow_add B₁ N 2, mul_assoc, mul_comm (B₁ ^ 2), ← mul_assoc,
        mul_inv_cancel₀ (pow_ne_zero _ hB₁0.ne'), one_mul]
    refine ⟨by rw [hJS t]; exact Real.sqrt_nonneg _, ?_, D / (2 * Real.sqrt (S t).det), hD, ?_⟩
    · rw [hJS t]
      calc Real.sqrt (S t).det ≤ Real.sqrt (N.factorial * M₀ ^ N) :=
            Real.sqrt_le_sqrt ((le_abs_self _).trans hup)
        _ ≤ _ := le_add_of_nonneg_right hK
    · rw [abs_div, abs_of_pos h2s, div_le_iff₀ h2s]
      calc |D| ≤ N.factorial * N * (2 * B₁ ^ 2) * M₀ ^ (N - 1) := hDb
        _ = N.factorial * N * B₁ ^ (N + 2) * M₀ ^ (N - 1) * (2 * (B₁ ^ N)⁻¹) := by
            rw [← hpow]
            ring
        _ ≤ N.factorial * N * B₁ ^ (N + 2) * M₀ ^ (N - 1) * (2 * Real.sqrt (S t).det) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlow zero_le_two) hK
        _ ≤ (Real.sqrt (N.factorial * M₀ ^ N) + N.factorial * N * B₁ ^ (N + 2) * M₀ ^ (N - 1)) *
              (2 * Real.sqrt (S t).det) :=
            mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (Real.sqrt_nonneg _)) h2s.le
  · -- Steps 7 and 8: `S 0 = I`, so `J'(0) = trace (S' 0) / 2 = ∑ₖ ⟨Λ'(0) p eₖ, p eₖ⟩`.
    have h0 : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_lt_zero.2 hδ, hδ⟩
    obtain ⟨D, hD, -, hD1⟩ := hJd 0 h0
    have hS0 : S 0 = 1 := by
      ext i j
      rw [hS, hΛ0, one_apply_eq_self, one_apply_eq_self]
      -- `q eᵢ ⊥ P`, so `⟨p eᵢ, p eⱼ⟩ + ⟨q eᵢ, q eⱼ⟩ = ⟨eᵢ, eⱼ⟩ = δᵢⱼ`.
      have h1 := Submodule.starProjection_inner_eq_zero (K := P) (EuclideanSpace.single i (1 : ℝ))
        (P.starProjection (EuclideanSpace.single j (1 : ℝ))) (P.starProjection_apply_mem _)
      have h2 := Submodule.starProjection_inner_eq_zero (K := P) (EuclideanSpace.single j (1 : ℝ))
        (P.starProjection (EuclideanSpace.single i (1 : ℝ))) (P.starProjection_apply_mem _)
      have he : inner ℝ (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) =
          (1 : Matrix (Fin N) (Fin N) ℝ) i j := by
        simp [EuclideanSpace.inner_single_left, Matrix.one_apply]
      rw [← he]
      simp only [inner_sub_left, inner_sub_right] at h1 h2 ⊢
      linarith [real_inner_comm (P.starProjection (EuclideanSpace.single i (1 : ℝ)))
          (EuclideanSpace.single j (1 : ℝ)),
        real_inner_comm (P.starProjection (EuclideanSpace.single i (1 : ℝ)))
          (P.starProjection (EuclideanSpace.single j (1 : ℝ)))]
    rw [hS0, Matrix.det_one, Real.sqrt_one, hD1 hS0] at hD
    refine hD.congr_deriv ?_
    rw [← Submission.ts_fv_sum_inner_starProjection_eq_trace N P (Λ' 0), Matrix.trace,
      Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Matrix.diag_apply, hS', hΛ0, one_apply_eq_self,
      real_inner_comm (P.starProjection (EuclideanSpace.single k (1 : ℝ)))]
    ring
/-- **Differentiation under the integral sign for `θ`-weighted integrals over `M ∩ K`** (used for
the first variation formula, Ch. 4, 2.2). Let `K` be compact and `δ > 0`. If for `|t| < δ`,
`m(t) = ∫_{M ∩ K} θ J(t, ·) dHⁿ` with `J(t, ·)` `Hⁿ ⌞ M`-measurable, and for `Hⁿ`-a.e. `x ∈ M ∩ K`
and all `|t| < δ`: `0 ≤ J(t, x) ≤ B`, `∂ₜJ(t, x) = J'(t, x)`, `|J'(t, x)| ≤ B`, and
`J'(0, x) = g(x)`, where `g` is `Hⁿ ⌞ M`-measurable and vanishes off `K`, then `t ↦ m(t)` has
derivative `∫ g dμ_V` at `t = 0`. -/
theorem Submission.ts_fv_hasDerivAt_of_weighted_jacobian : ∀ (n ℓ : ℕ) (a : RectifiablePair n ℓ) (K : Set (Ambient n ℓ)) (m : ℝ → ℝ≥0∞) (J J' : ℝ → Ambient n ℓ → ℝ) (g : Ambient n ℓ → ℝ) (δ B : ℝ), 0 < δ → IsCompact K → (∀ t ∈ Ioo (-δ) δ, m t = ∫⁻ x in a.M ∩ K, ENNReal.ofReal (a.θ x * J t x) ∂μHE[n]) → (∀ t ∈ Ioo (-δ) δ, AEStronglyMeasurable (J t) ((μHE[n] : Measure (Ambient n ℓ)).restrict a.M)) → AEStronglyMeasurable g ((μHE[n] : Measure (Ambient n ℓ)).restrict a.M) → (∀ x ∉ K, g x = 0) → (∀ᵐ x ∂(μHE[n] : Measure (Ambient n ℓ)).restrict a.M, x ∈ K → J' 0 x = g x ∧ ∀ t ∈ Ioo (-δ) δ, 0 ≤ J t x ∧ J t x ≤ B ∧ HasDerivAt (fun s ↦ J s x) (J' t x) t ∧ |J' t x| ≤ B) → HasDerivAt (fun t ↦ (m t).toReal) (∫ x, g x ∂(mk a).weight) 0 := by
  intro n ℓ a K m J J' g δ B hδ hK hm hJ hg hg0 hae
  -- Work with `ν = Hⁿ ⌞ (M ∩ K) = (Hⁿ ⌞ M) ⌞ K` on the neighbourhood `I = (-δ, δ)` of `0`.
  set ν : Measure (Ambient n ℓ) := (μHE[n] : Measure (Ambient n ℓ)).restrict (a.M ∩ K)
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hνK : ((μHE[n] : Measure (Ambient n ℓ)).restrict a.M).restrict K = ν := by
    rw [Measure.restrict_restrict hKm, Set.inter_comm]
  have hle : ν ≤ (μHE[n] : Measure (Ambient n ℓ)).restrict a.M :=
    Measure.restrict_mono Set.inter_subset_left le_rfl
  have hs : Ioo (-δ) δ ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by linarith) hδ
  -- `θ` is `ν`-integrable and `ν`-a.e. positive, and the pointwise hypotheses hold `ν`-a.e.
  have hθ : Integrable a.θ ν := a.isRectifiablePair.locallyIntegrable K hK
  have hθpos : ∀ᵐ x ∂ν, 0 < a.θ x :=
    (ae_restrict_mem₀ (a.isRectifiablePair.measurable.inter hKm.nullMeasurableSet)).mono
      fun x hx ↦ a.isRectifiablePair.pos x hx.1
  have hae' : ∀ᵐ x ∂ν, J' 0 x = g x ∧ ∀ t ∈ Ioo (-δ) δ, 0 ≤ J t x ∧ J t x ≤ B ∧
      HasDerivAt (fun s ↦ J s x) (J' t x) t ∧ |J' t x| ≤ B := by
    rw [← hνK]
    exact (ae_restrict_iff' hKm).2 hae
  -- For `t ∈ I`, `0 ≤ θ J(t, ·) ≤ B θ` `ν`-a.e., so `θ J(t, ·)` is `ν`-integrable and
  -- `(m t).toReal = ∫ θ J(t, ·) dν`.
  have hFint : ∀ t ∈ Ioo (-δ) δ, Integrable (fun x ↦ a.θ x * J t x) ν := by
    intro t ht
    refine (hθ.const_mul B).mono' (hθ.aestronglyMeasurable.mul ((hJ t ht).mono_measure hle)) ?_
    filter_upwards [hθpos, hae'] with x hx hx'
    obtain ⟨h0, h1, -, -⟩ := hx'.2 t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx.le h0), mul_comm B]
    exact mul_le_mul_of_nonneg_left h1 hx.le
  have hmt : ∀ t ∈ Ioo (-δ) δ, (m t).toReal = ∫ x, a.θ x * J t x ∂ν := by
    intro t ht
    have hnn : 0 ≤ᵐ[ν] fun x ↦ a.θ x * J t x := by
      filter_upwards [hθpos, hae'] with x hx hx'
      exact mul_nonneg hx.le (hx'.2 t ht).1
    rw [hm t ht, ← ofReal_integral_eq_lintegral_ofReal (hFint t ht) hnn,
      ENNReal.toReal_ofReal (integral_nonneg_of_ae hnn)]
  -- Differentiate under the integral sign, with the integrable bound `B θ`.
  obtain ⟨-, hD⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
    (F := fun t x ↦ a.θ x * J t x) (F' := fun t x ↦ a.θ x * J' t x)
    (bound := fun x ↦ B * a.θ x) hs
    (Filter.eventually_of_mem hs fun t ht ↦ (hFint t ht).aestronglyMeasurable)
    (hFint 0 ⟨by linarith, hδ⟩)
    ((hθ.aestronglyMeasurable.mul (hg.mono_measure hle)).congr (by
      filter_upwards [hae'] with x hx
      show a.θ x * g x = a.θ x * J' 0 x
      rw [hx.1]))
    (by
      filter_upwards [hθpos, hae'] with x hx hx' t ht
      show ‖a.θ x * J' t x‖ ≤ B * a.θ x
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos hx, mul_comm B]
      exact mul_le_mul_of_nonneg_left (hx'.2 t ht).2.2.2 hx.le)
    (hθ.const_mul B)
    (by
      filter_upwards [hae'] with x hx t ht
      exact (hx.2 t ht).2.2.1.const_mul (a.θ x))
  -- The derivative is `∫ θ g dν = ∫_K g dμ_V = ∫ g dμ_V`, as `μ_V ⌞ K = ν.withDensity θ`.
  have hval : ∫ x, a.θ x * J' 0 x ∂ν = ∫ x, g x ∂(mk a).weight := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hg0]
    show _ = ∫ x, g x ∂(((μHE[n] : Measure (Ambient n ℓ)).restrict a.M).withDensity
      fun x ↦ ENNReal.ofReal (a.θ x)).restrict K
    rw [restrict_withDensity hKm, hνK, integral_withDensity_eq_integral_toReal_smul₀
      hθ.aemeasurable.ennreal_ofReal (ae_of_all _ fun x ↦ ENNReal.ofReal_lt_top)]
    refine integral_congr_ae ?_
    filter_upwards [hθpos, hae'] with x hx hx'
    rw [hx'.1, ENNReal.toReal_ofReal hx.le, smul_eq_mul]
  rw [← hval]
  exact hD.congr_of_eventuallyEq (Filter.eventually_of_mem hs hmt)

/-- **Ch. 4, 2.1–2.2 (pp. 87–88), first variation via Lipschitz pieces** (with the area formula of
Ch. 3, 2.4–2.5 and the Jacobian computation of Ch. 2, 5.2–5.3). Let `M ⊆ N₀ ∪ ⋃ᵢ Fᵢ(Cᵢ)` with
`Hⁿ(N₀) = 0`, where the Lipschitz pieces `(Cᵢ, Fᵢ)` compute the tangent spaces
(`T_x V = DFᵢ(w)(ℝⁿ)` whenever `Fᵢ(w) = x`, for `Hⁿ`-a.e. `x ∈ M`), and let `x ↦ p_{T_x V}` be
`Hⁿ ⌞ M`-a.e. strongly measurable. Then for every compact variation `(φ, ε, K)` the mass
`t ↦ M(φ_t#(V ⌞ K))` has derivative `∫ div_M X dμ_V` at `t = 0`, where `X = ∂φ_t/∂t|_{t=0}`. -/
theorem Submission.ts_first_variation_of_pieces : ∀ (n ℓ : ℕ) (a : RectifiablePair n ℓ) (N₀ : Set (Ambient n ℓ)) (C : ℕ → Set (EuclideanSpace ℝ (Fin n))) (F : ℕ → EuclideanSpace ℝ (Fin n) → Ambient n ℓ) (φ : ℝ → Ambient n ℓ → Ambient n ℓ) (ε : ℝ) (K : Set (Ambient n ℓ)), 0 < n → MeasurableSet N₀ → (μHE[n] : Measure (Ambient n ℓ)) N₀ = 0 → a.M ⊆ N₀ ∪ ⋃ i, F i '' C i → (∀ i, IsCompact (C i) ∧ (∃ K : NNReal, LipschitzWith K (F i)) ∧ (∀ w ∈ C i, DifferentiableAt ℝ (F i) w ∧ Function.Injective (fderiv ℝ (F i) w)) ∧ ContinuousOn (fderiv ℝ (F i)) (C i) ∧ ∃ c : ℝ, 0 < c ∧ ∀ v ∈ C i, ∀ w ∈ C i, c * ‖v - w‖ ≤ ‖F i v - F i w‖) → (∀ᵐ x ∂(μHE[n] : Measure (Ambient n ℓ)).restrict a.M, ∀ i, ∀ w ∈ C i, F i w = x → (mk a).tangentSpace x = LinearMap.range (fderiv ℝ (F i) w).toLinearMap) → AEStronglyMeasurable (fun x ↦ ((mk a).tangentSpace x).starProjection) ((μHE[n] : Measure (Ambient n ℓ)).restrict a.M) → IsCompactVariation φ ε K → HasDerivAt (fun t ↦ (imageMass a (φ t) K).toReal) (∫ x, (mk a).tangentialDiv (fun y ↦ deriv (fun t ↦ φ t y) 0) x ∂(mk a).weight) 0 := by
  intro n ℓ a N₀ C F φ ε K hn hN₀ hN₀0 hcover hpieces htan hproj hV
  -- The variation: `X` is `C¹` with `DX = 0` off `K`, each `φ_t` is Lipschitz and `C¹`, and near
  -- `t = 0` the map `t ↦ Dφ_t(x)` is differentiable with `∂_t Dφ_t(x)|_{t=0} = DX(x)` and with
  -- uniform bounds on `Dφ_t(x)`, `∂_t Dφ_t(x)` and `Dφ_t(x)⁻¹`.
  obtain ⟨hX, hDX, hφ, δ, B, hδ, hδε, Λ', hΛ'⟩ :=
    Submission.ts_fv_compact_variation_bounds n ℓ φ ε K hV
  -- Jacobi's formula with a constant uniform in `x` and in the plane `T_x V`.
  obtain ⟨A, hA⟩ := Submission.ts_fv_tangential_jacobian_hasDerivAt (n + ℓ) B
  have hφ0 : ∀ x, fderiv ℝ (φ 0) x = 1 := fun x ↦ by
    rw [show φ 0 = fun y ↦ y from funext hV.init, fderiv_fun_id]
    rfl
  have hε : ∀ t ∈ Ioo (-δ) δ, t ∈ Ioo (-ε) ε := fun t ht ↦
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- `J^P(L) = (det (P L* L P + I - P))^{1/2}`, with the matrix taken in the standard basis; it is
  -- continuous in `(L, P)`.
  let G : (Ambient n ℓ →L[ℝ] Ambient n ℓ) → (Ambient n ℓ →L[ℝ] Ambient n ℓ) → ℝ := fun L P ↦
    Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (n + ℓ) ↦
      inner ℝ (L (P (EuclideanSpace.single i (1 : ℝ)))) (L (P (EuclideanSpace.single j (1 : ℝ)))) +
        inner ℝ (EuclideanSpace.single i (1 : ℝ) - P (EuclideanSpace.single i (1 : ℝ)))
          (EuclideanSpace.single j (1 : ℝ) - P (EuclideanSpace.single j (1 : ℝ)))))
  have hG : Continuous (Function.uncurry G) := by
    refine Real.continuous_sqrt.comp (Continuous.matrix_det (continuous_matrix fun i j ↦ ?_))
    simp only [Matrix.of_apply]
    fun_prop
  -- `trace (L ∘ P)` is continuous in `(L, P)`; at `(DX(x), p_{T_x V})` it is `div_M X(x)`.
  have hT : Continuous (Function.uncurry fun L P : Ambient n ℓ →L[ℝ] Ambient n ℓ ↦
      LinearMap.trace ℝ (Ambient n ℓ) (L.toLinearMap ∘ₗ P.toLinearMap)) :=
    ((LinearMap.trace ℝ (Ambient n ℓ)).comp
      (ContinuousLinearMap.coeLM ℝ)).continuous_of_finiteDimensional.comp
        (continuous_fst.clm_comp continuous_snd)
  -- The tangential Jacobian `J_t(x) = J^{T_x V}(Dφ_t(x))` and its `t`-derivative.
  let J : ℝ → Ambient n ℓ → ℝ := fun t x ↦
    G (fderiv ℝ (φ t) x) ((mk a).tangentSpace x).starProjection
  let J' : ℝ → Ambient n ℓ → ℝ := fun t x ↦ deriv (fun s ↦ J s x) t
  -- Differentiation under the integral sign, dominated by `A θ` on `M ∩ K`.
  refine Submission.ts_fv_hasDerivAt_of_weighted_jacobian n ℓ a K
    (fun t ↦ imageMass a (φ t) K) J J'
    (fun x ↦ (mk a).tangentialDiv (fun y ↦ deriv (fun t ↦ φ t y) 0) x) δ A hδ hV.compact
    (fun t ht ↦ ?_) (fun t ht ↦ ?_) ?_ (fun x hx ↦ ?_) (ae_of_all _ fun x _ ↦ ?_)
  · -- the area formula for the injective Lipschitz map `φ_t` on `M ∩ K`
    exact Submission.ts_fv_image_mass_area_formula n ℓ a N₀ C F (φ t) K hn hN₀ hN₀0 hcover
      hpieces htan (hV.diffeo t (hε t ht)).1.injective (hφ t (hε t ht)).1
      ((hφ t (hε t ht)).2.differentiable one_ne_zero) hV.compact.isClosed.measurableSet
  · exact hG.comp_aestronglyMeasurable₂
      (((hφ t (hε t ht)).2.continuous_fderiv one_ne_zero).aestronglyMeasurable) hproj
  · exact hT.comp_aestronglyMeasurable₂ ((hX.continuous_fderiv one_ne_zero).aestronglyMeasurable)
      hproj
  · show LinearMap.trace ℝ (Ambient n ℓ) ((fderiv ℝ (fun y ↦ deriv (fun t ↦ φ t y) 0) x).toLinearMap
      ∘ₗ ((mk a).tangentSpace x).starProjection.toLinearMap) = 0
    rw [hDX x hx, ContinuousLinearMap.toLinearMap_zero, LinearMap.zero_comp, map_zero]
  · -- Jacobi's formula along `t ↦ Dφ_t(x)` in the plane `T_x V`, for every `x`
    obtain ⟨hbd, hd0⟩ := hA ((mk a).tangentSpace x) (fun s ↦ fderiv ℝ (φ s) x) (fun s ↦ Λ' s x)
      (fun s ↦ J s x) δ hδ (hφ0 x) (fun t ht ↦ (hΛ' x).2 t ht) fun t ↦ rfl
    refine ⟨?_, fun t ht ↦ ?_⟩
    · rw [show J' 0 x = _ from hd0.deriv]
      beta_reduce
      rw [(hΛ' x).1]
      rfl
    · obtain ⟨hJ0, hJA, d, hd, hdA⟩ := hbd t ht
      have hJ' : J' t x = d := hd.deriv
      exact ⟨hJ0, hJA, hJ' ▸ hd, hJ' ▸ hdA⟩

/-- Simon Ch. 3, proof of Theorem 1.6 (⇒) with Remark 1.8(1), and Ch. 4, 1.1 (pp. 71–72, 75, 86):
the weighted blow-up at a good point of a Lusin piece. Let `μ = μ_V` for `V = v(M, θ)`, let
`N` be Borel with `Hⁿ(N) < ∞`, `K ⊆ M ∩ N` compact, `θ|K` continuous at `x`, and `f ∈ C_c`.
If `Hⁿ(N ∩ B_ρ(x)) ≤ Γρⁿ` for `ρ > 0`, `μ(B_r(x) \ K) / rⁿ → 0`, `Hⁿ(N ∩ B_r(x) \ K) / rⁿ → 0`
and `t⁻ⁿ ∫_N f(t⁻¹(y - x)) dHⁿ(y) → L`, then `t⁻ⁿ ∫ f(t⁻¹(y - x)) dμ(y) → θ(x) L` as `t ↓ 0`.
With `g_t = f(t⁻¹(· - x))`, which vanishes off `B_{Rt}(x)` when `f` vanishes off `B_R(0)`,
`t⁻ⁿ ∫ g_t dμ = θ(x) t⁻ⁿ ∫_N g_t - θ(x) t⁻ⁿ ∫_{N \ K} g_t + t⁻ⁿ ∫_K (θ - θ(x)) g_t
  + t⁻ⁿ ∫_{Kᶜ} g_t dμ`, and the last three terms tend to `0`. -/
theorem Submission.ts_pwb_blowup_at_good_point : ∀ (n ℓ : ℕ) (a : RectifiablePair n ℓ) (N K : Set (Ambient n ℓ)) (x : Ambient n ℓ) (f : C_c(Ambient n ℓ, ℝ)) (Γ L : ℝ), MeasurableSet N → (μHE[n] : Measure (Ambient n ℓ)) N ≠ ⊤ → IsCompact K → K ⊆ a.M ∩ N → x ∈ K → ContinuousWithinAt a.θ K x → (∀ ρ : ℝ, 0 < ρ → (μHE[n] : Measure (Ambient n ℓ)) (N ∩ closedBall x ρ) ≤ ENNReal.ofReal (Γ * ρ ^ n)) → Tendsto (fun r : ℝ ↦ (mk a).weight.real (Kᶜ ∩ closedBall x r) / r ^ n) (𝓝[>] 0) (𝓝 0) → Tendsto (fun r : ℝ ↦ ((μHE[n] : Measure (Ambient n ℓ)).restrict N).real (Kᶜ ∩ closedBall x r) / r ^ n) (𝓝[>] 0) (𝓝 0) → Tendsto (fun t : ℝ ↦ (t ^ n)⁻¹ * ∫ y in N, f (t⁻¹ • (y - x)) ∂μHE[n]) (𝓝[>] 0) (𝓝 L) → Tendsto (fun t : ℝ ↦ (t ^ n)⁻¹ * ∫ y, f (t⁻¹ • (y - x)) ∂(mk a).weight) (𝓝[>] 0) (𝓝 (a.θ x * L)) := by
  intro n ℓ a N K x f Γ L hNm hNfin hKc hKMN _ hθc hΓ hA hB hI1
  -- `μ_V` is finite on compact sets and `∫ h dμ_V = ∫_M θ h dHⁿ` for every `h`.
  obtain ⟨hfin, hint⟩ := Submission.ts_pwb_pair_weight_integral n ℓ a
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hKM : K ⊆ a.M := fun y hy ↦ (hKMN hy).1
  have hKN : K ⊆ N := fun y hy ↦ (hKMN hy).2
  have hMm := a.isRectifiablePair.measurable
  -- `|f| ≤ m`, and `f = 0` off `B_R(0)`.
  obtain ⟨m, hm⟩ : ∃ m, ∀ z, ‖f z‖ ≤ m :=
    f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  have hm0 : 0 ≤ m := (norm_nonneg _).trans (hm 0)
  obtain ⟨R, hR, hRs⟩ : ∃ R : ℝ, 0 < R ∧ ∀ z, R < ‖z‖ → f z = 0 := by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 f.hasCompactSupport.isCompact.isBounded
    refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun z hz ↦ ?_⟩
    apply image_eq_zero_of_notMem_tsupport
    intro hzs
    exact absurd (hC z hzs) (not_le.2 (lt_of_le_of_lt (le_max_left _ _) hz))
  -- `g_t = f(t⁻¹(· - x))` is continuous, bounded by `m`, and vanishes off `B_{Rt}(x)`.
  set g : ℝ → Ambient n ℓ → ℝ := fun t y ↦ f (t⁻¹ • (y - x)) with hg
  have hgc : ∀ t, Continuous (g t) := fun t ↦
    f.continuous.comp (by fun_prop)
  have hgb : ∀ t y, ‖g t y‖ ≤ m := fun t y ↦ hm _
  have hgs : ∀ t, 0 < t → ∀ y, y ∉ closedBall x (R * t) → g t y = 0 := by
    intro t ht y hy
    apply hRs
    rw [mem_closedBall, dist_eq_norm, not_le] at hy
    rw [norm_smul, norm_inv, Real.norm_of_nonneg ht.le, lt_inv_mul_iff₀ ht]
    linarith [mul_comm R t]
  -- Integrability: `g_t` on `N` (as `Hⁿ(N) < ∞`), and `θ g_t` on `M` (it vanishes off the
  -- compact ball `B_{Rt}(x)`, on which `θ` is integrable).
  have hgN : ∀ t, IntegrableOn (g t) N μHE[n] := fun t ↦
    IntegrableOn.of_bound (lt_top_iff_ne_top.2 hNfin) (hgc t).aestronglyMeasurable m
      (Eventually.of_forall (hgb t))
  have hθg : ∀ t, 0 < t → IntegrableOn (fun y ↦ a.θ y * g t y) a.M μHE[n] := by
    intro t ht
    have h1 : IntegrableOn a.θ (a.M ∩ closedBall x (R * t)) μHE[n] :=
      a.isRectifiablePair.locallyIntegrable _ (isCompact_closedBall _ _)
    have h2 : IntegrableOn (fun y ↦ a.θ y * g t y) (a.M ∩ closedBall x (R * t)) μHE[n] :=
      Integrable.mul_bdd h1 (hgc t).aestronglyMeasurable (Eventually.of_forall (hgb t))
    refine h2.of_ae_sdiff_eq_zero hMm (Eventually.of_forall fun y hy ↦ ?_)
    rw [hgs t ht y (fun hyB ↦ hy.2 ⟨hy.1, hyB⟩), mul_zero]
  -- The four-term decomposition `t⁻ⁿ ∫ g_t dμ = θ(x) T₁ - θ(x) T₂ + T₃ + T₄`.
  have hdec : ∀ t, 0 < t → (t ^ n)⁻¹ * ∫ y, g t y ∂(mk a).weight =
      a.θ x * ((t ^ n)⁻¹ * ∫ y in N, g t y ∂μHE[n]) -
        a.θ x * ((t ^ n)⁻¹ * ∫ y in N \ K, g t y ∂μHE[n]) +
        (t ^ n)⁻¹ * ∫ y in K, (a.θ y - a.θ x) * g t y ∂μHE[n] +
        (t ^ n)⁻¹ * ∫ y in Kᶜ, g t y ∂(mk a).weight := by
    intro t ht
    have e1 : ∫ y, g t y ∂(mk a).weight = ∫ y in a.M, a.θ y * g t y ∂μHE[n] := hint (g t)
    have e2 : ∫ y in a.M, a.θ y * g t y ∂μHE[n] =
        ∫ y in K, a.θ y * g t y ∂μHE[n] + ∫ y in a.M \ K, a.θ y * g t y ∂μHE[n] := by
      rw [← integral_inter_add_sdiff hKm (hθg t ht), inter_eq_right.2 hKM]
    have e3 : ∫ y in a.M \ K, a.θ y * g t y ∂μHE[n] = ∫ y in Kᶜ, g t y ∂(mk a).weight := by
      rw [← integral_indicator hKm.compl, hint, sdiff_eq, ← setIntegral_indicator hKm.compl]
      congr 1
      ext y
      by_cases hy : y ∈ Kᶜ <;> simp [indicator, hy]
    have hgK : IntegrableOn (g t) K μHE[n] := (hgN t).mono_set hKN
    have hθgK : IntegrableOn (fun y ↦ a.θ y * g t y) K μHE[n] := (hθg t ht).mono_set hKM
    have e4 : ∫ y in K, a.θ y * g t y ∂μHE[n] =
        a.θ x * ∫ y in K, g t y ∂μHE[n] + ∫ y in K, (a.θ y - a.θ x) * g t y ∂μHE[n] := by
      have : (fun y ↦ (a.θ y - a.θ x) * g t y) = fun y ↦ a.θ y * g t y - a.θ x * g t y := by
        ext y; ring
      rw [this, integral_sub hθgK (hgK.const_mul _), integral_const_mul]
      ring
    have e5 : ∫ y in K, g t y ∂μHE[n] = ∫ y in N, g t y ∂μHE[n] - ∫ y in N \ K, g t y ∂μHE[n] := by
      rw [← integral_inter_add_sdiff hKm (hgN t), inter_eq_right.2 hKN]
      ring
    rw [e1, e2, e3, e4, e5]
    ring
  -- Rescaling the excess-density hypotheses by `r = Rt`.
  have hRt : Tendsto (fun t : ℝ ↦ R * t) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun t : ℝ ↦ R * t) (𝓝 0) (𝓝 (R * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_pos hR ht
  have hA' := hA.comp hRt
  have hB' := hB.comp hRt
  -- `|T₂(t)| ≤ m Rⁿ (Hⁿ ⌞ N)(Kᶜ ∩ B_{Rt}(x)) / (Rt)ⁿ → 0`.
  have hT2 : Tendsto (fun t ↦ (t ^ n)⁻¹ * ∫ y in N \ K, g t y ∂μHE[n]) (𝓝[>] 0) (𝓝 0) := by
    have hlim : Tendsto (fun t ↦ m * R ^ n * (((μHE[n] : Measure (Ambient n ℓ)).restrict N).real
        (Kᶜ ∩ closedBall x (R * t)) / (R * t) ^ n)) (𝓝[>] 0) (𝓝 0) := by
      simpa using hB'.const_mul (m * R ^ n)
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : (0 : ℝ) < t := ht
    have hsplit : ∫ y in N \ K, g t y ∂μHE[n] =
        ∫ y in (N \ K) ∩ closedBall x (R * t), g t y ∂μHE[n] :=
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hNm.diff hKm) inter_subset_left
        (fun y hy ↦ hgs t ht' y (fun hyB ↦ hy.2 ⟨hy.1, hyB⟩))
    have hmeas : (μHE[n] : Measure (Ambient n ℓ)) ((N \ K) ∩ closedBall x (R * t)) < ⊤ :=
      (measure_mono (inter_subset_left.trans sdiff_subset)).trans_lt (lt_top_iff_ne_top.2 hNfin)
    have hbound := norm_setIntegral_le_of_norm_le_const hmeas (fun y _ ↦ hgb t y)
    have hreal : (μHE[n] : Measure (Ambient n ℓ)).real ((N \ K) ∩ closedBall x (R * t)) =
        ((μHE[n] : Measure (Ambient n ℓ)).restrict N).real (Kᶜ ∩ closedBall x (R * t)) := by
      rw [Measure.real, Measure.real,
        Measure.restrict_apply (hKm.compl.inter measurableSet_closedBall)]
      congr 2
      ext y
      simp only [mem_inter_iff, Set.mem_sdiff, mem_compl_iff]
      tauto
    rw [norm_mul, hsplit, norm_inv, norm_pow, Real.norm_of_nonneg ht'.le]
    calc (t ^ n)⁻¹ * ‖∫ y in (N \ K) ∩ closedBall x (R * t), g t y ∂μHE[n]‖
        ≤ (t ^ n)⁻¹ * (m * (μHE[n] : Measure (Ambient n ℓ)).real
            ((N \ K) ∩ closedBall x (R * t))) := by gcongr
      _ = m * R ^ n * (((μHE[n] : Measure (Ambient n ℓ)).restrict N).real
            (Kᶜ ∩ closedBall x (R * t)) / (R * t) ^ n) := by
        rw [hreal, mul_pow]
        field_simp
  -- `|T₄(t)| ≤ m Rⁿ μ_V(Kᶜ ∩ B_{Rt}(x)) / (Rt)ⁿ → 0`.
  have hT4 : Tendsto (fun t ↦ (t ^ n)⁻¹ * ∫ y in Kᶜ, g t y ∂(mk a).weight) (𝓝[>] 0) (𝓝 0) := by
    have hlim : Tendsto (fun t ↦ m * R ^ n * ((mk a).weight.real
        (Kᶜ ∩ closedBall x (R * t)) / (R * t) ^ n)) (𝓝[>] 0) (𝓝 0) := by
      simpa using hA'.const_mul (m * R ^ n)
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : (0 : ℝ) < t := ht
    have hsplit : ∫ y in Kᶜ, g t y ∂(mk a).weight =
        ∫ y in Kᶜ ∩ closedBall x (R * t), g t y ∂(mk a).weight :=
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hKm.compl inter_subset_left
        (fun y hy ↦ hgs t ht' y (fun hyB ↦ hy.2 ⟨hy.1, hyB⟩))
    have hmeas : (mk a).weight (Kᶜ ∩ closedBall x (R * t)) < ⊤ :=
      (measure_mono inter_subset_right).trans_lt (isCompact_closedBall _ _).measure_lt_top
    rw [norm_mul, hsplit, norm_inv, norm_pow, Real.norm_of_nonneg ht'.le]
    calc (t ^ n)⁻¹ * ‖∫ y in Kᶜ ∩ closedBall x (R * t), g t y ∂(mk a).weight‖
        ≤ (t ^ n)⁻¹ * (m * (mk a).weight.real (Kᶜ ∩ closedBall x (R * t))) := by
          gcongr
          exact norm_setIntegral_le_of_norm_le_const hmeas (fun y _ ↦ hgb t y)
      _ = m * R ^ n * ((mk a).weight.real (Kᶜ ∩ closedBall x (R * t)) / (R * t) ^ n) := by
        rw [mul_pow]
        field_simp
  -- `|T₃(t)| ≤ (ε / c) m Rⁿ max(Γ, 0) < ε` for `0 < t < δ / R`, by continuity of `θ|K` at `x`
  -- and the bound `Hⁿ(K ∩ B_{Rt}(x)) ≤ Hⁿ(N ∩ B_{Rt}(x)) ≤ Γ (Rt)ⁿ`.
  have hT3 : Tendsto (fun t ↦ (t ^ n)⁻¹ * ∫ y in K, (a.θ y - a.θ x) * g t y ∂μHE[n])
      (𝓝[>] 0) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    set c := m * max Γ 0 * R ^ n + 1 with hc
    have hc0 : 0 < c := by positivity
    obtain ⟨δ, hδ, hδθ⟩ := Metric.continuousWithinAt_iff.1 hθc (ε / c) (div_pos hε hc0)
    filter_upwards [Ioo_mem_nhdsGT (div_pos hδ hR)] with t ht
    obtain ⟨ht0, htδ⟩ := ht
    have hRtδ : R * t < δ := by
      rw [lt_div_iff₀ hR] at htδ
      linarith [mul_comm R t]
    have hsplit : ∫ y in K, (a.θ y - a.θ x) * g t y ∂μHE[n] =
        ∫ y in K ∩ closedBall x (R * t), (a.θ y - a.θ x) * g t y ∂μHE[n] :=
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hKm inter_subset_left
        (fun y hy ↦ by rw [hgs t ht0 y (fun hyB ↦ hy.2 ⟨hy.1, hyB⟩), mul_zero])
    have hmeasN : (μHE[n] : Measure (Ambient n ℓ)) (N ∩ closedBall x (R * t)) < ⊤ :=
      (measure_mono inter_subset_left).trans_lt (lt_top_iff_ne_top.2 hNfin)
    have hmeasK : (μHE[n] : Measure (Ambient n ℓ)) (K ∩ closedBall x (R * t)) < ⊤ :=
      (measure_mono (inter_subset_inter_left _ hKN)).trans_lt hmeasN
    have hpt : ∀ y ∈ K ∩ closedBall x (R * t), ‖(a.θ y - a.θ x) * g t y‖ ≤ ε / c * m := by
      intro y hy
      rw [norm_mul]
      have h1 : dist y x < δ := lt_of_le_of_lt (mem_closedBall.1 hy.2) hRtδ
      have h2 := hδθ hy.1 h1
      rw [Real.dist_eq] at h2
      exact mul_le_mul (le_of_lt (by simpa [Real.norm_eq_abs] using h2)) (hgb t y)
        (norm_nonneg _) (div_pos hε hc0).le
    have hbound := norm_setIntegral_le_of_norm_le_const hmeasK hpt
    have hKreal : (μHE[n] : Measure (Ambient n ℓ)).real (K ∩ closedBall x (R * t)) ≤
        max Γ 0 * (R * t) ^ n := by
      calc (μHE[n] : Measure (Ambient n ℓ)).real (K ∩ closedBall x (R * t))
          ≤ (μHE[n] : Measure (Ambient n ℓ)).real (N ∩ closedBall x (R * t)) :=
            measureReal_mono (inter_subset_inter_left _ hKN) hmeasN.ne
        _ ≤ (ENNReal.ofReal (Γ * (R * t) ^ n)).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top (hΓ _ (mul_pos hR ht0))
        _ = max (Γ * (R * t) ^ n) 0 := ENNReal.toReal_ofReal'
        _ ≤ max Γ 0 * (R * t) ^ n := by
          have hp : 0 ≤ (R * t) ^ n := by positivity
          rcases le_total Γ 0 with h | h
          · rw [max_eq_right h, max_eq_right (mul_nonpos_of_nonpos_of_nonneg h hp), zero_mul]
          · rw [max_eq_left h, max_eq_left (mul_nonneg h hp)]
    rw [dist_zero_right, norm_mul, hsplit, norm_inv, norm_pow, Real.norm_of_nonneg ht0.le]
    have hεc : 0 ≤ ε / c * m := mul_nonneg (div_pos hε hc0).le hm0
    calc (t ^ n)⁻¹ * ‖∫ y in K ∩ closedBall x (R * t), (a.θ y - a.θ x) * g t y ∂μHE[n]‖
        ≤ (t ^ n)⁻¹ * (ε / c * m * (μHE[n] : Measure (Ambient n ℓ)).real
            (K ∩ closedBall x (R * t))) := by gcongr
      _ ≤ (t ^ n)⁻¹ * (ε / c * m * (max Γ 0 * (R * t) ^ n)) := by gcongr
      _ = ε / c * (m * max Γ 0 * R ^ n) := by
        rw [mul_pow]
        field_simp
      _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ hc0, hc]
        nlinarith
  -- Sum the four limits: `θ(x) L - θ(x) · 0 + 0 + 0 = θ(x) L`.
  have hsum := (((hI1.const_mul (a.θ x)).sub (hT2.const_mul (a.θ x))).add hT3).add hT4
  rw [mul_zero, sub_zero, add_zero, add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (hdec t ht).symm

/-- **Weighted blow-up on one Lipschitz piece (Simon Ch. 3, 1.9 via 1.6 and 1.8(1)).** For a
Lipschitz piece `(C, F)` and `Hⁿ`-a.e. `x ∈ M`, at every `w ∈ C` with `F(w) = x` the blow-ups of
`μ_V` converge: `t⁻ⁿ ∫ f(t⁻¹(y - x)) dμ_V(y) → θ(x) ∫_{DF(w)(ℝⁿ)} f dHⁿ` as `t ↓ 0`. -/
theorem Submission.ts_piece_weighted_blowup_ae : ∀ (n ℓ : ℕ) (a : RectifiablePair n ℓ) (C : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → Ambient n ℓ), 0 < n → (IsCompact C ∧ (∃ K : NNReal, LipschitzWith K F) ∧ (∀ w ∈ C, DifferentiableAt ℝ F w ∧ Function.Injective (fderiv ℝ F w)) ∧ ContinuousOn (fderiv ℝ F) C ∧ ∃ c : ℝ, 0 < c ∧ ∀ v ∈ C, ∀ w ∈ C, c * ‖v - w‖ ≤ ‖F v - F w‖) → ∀ᵐ x ∂(μHE[n] : Measure (Ambient n ℓ)).restrict a.M, ∀ w ∈ C, F w = x → ∀ f : C_c(Ambient n ℓ, ℝ), Tendsto (fun t : ℝ ↦ (t ^ n)⁻¹ * ∫ y, f (t⁻¹ • (y - x)) ∂(mk a).weight) (𝓝[>] 0) (𝓝 (a.θ x * ∫ y in (LinearMap.range (fderiv ℝ F w).toLinearMap : Set (Ambient n ℓ)), f y ∂μHE[n])) := by
  intro n ℓ a C F hn hpiece
  have hC : IsCompact C := hpiece.1
  obtain ⟨κ, hF⟩ := hpiece.2.1
  have hM := a.isRectifiablePair.measurable
  -- the sibling: `Hⁿ(F(C) ∩ B_ρ(z)) ≤ Γρⁿ` on `F(C)`, and the blow-up of `Hⁿ ⌞ F(C)` at the
  -- image of every density point of `C`
  obtain ⟨⟨Γ, hΓ⟩, hblow⟩ := Submission.ts_piece_density_blowup n ℓ C F hn hpiece
  -- `F(C)` is compact, hence Borel, and `Hⁿ(F(C)) < ∞`
  have hNc : IsCompact (F '' C) := hC.image hF.continuous
  have hNm : MeasurableSet (F '' C) := hNc.isClosed.measurableSet
  have hNfin : (μHE[n] : Measure (Ambient n ℓ)) (F '' C) ≠ ⊤ := by
    rcases (F '' C).eq_empty_or_nonempty with h | ⟨z, hz⟩
    · rw [h, measure_empty]
      exact ENNReal.zero_ne_top
    obtain ⟨r, hr⟩ := hNc.isBounded.subset_closedBall z
    have h := hΓ z hz (max r 1) (one_pos.trans_le (le_max_right r 1))
    rw [inter_eq_left.2 (hr.trans (closedBall_subset_closedBall (le_max_left r 1)))] at h
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  -- Lusin: compact `K k ⊆ M ∩ F(C)`, with `θ` continuous on each, cover `M ∩ F(C)` up to an
  -- `Hⁿ`-null set
  obtain ⟨K, hK, hKnull⟩ := Submission.ts_pwb_lusin_compact_cover n ℓ μHE[n] (a.M ∩ F '' C) a.θ
    (hM.inter hNm.nullMeasurableSet)
    (ne_top_of_le_ne_top hNfin (measure_mono inter_subset_right))
    (Integrable.aestronglyMeasurable (a.isRectifiablePair.locallyIntegrable _ hNc))
  -- upper densities of `μ_V ⌞ (K k)ᶜ` and of `Hⁿ ⌞ (F(C) \ K k)` vanish `Hⁿ`-a.e. on `K k`
  have hfin : IsFiniteMeasureOnCompacts ((μHE[n] : Measure (Ambient n ℓ)).restrict (F '' C)) := by
    have : IsFiniteMeasure ((μHE[n] : Measure (Ambient n ℓ)).restrict (F '' C)) :=
      isFiniteMeasure_restrict.2 hNfin
    infer_instance
  have hA := fun k ↦ Submission.ts_pwb_upper_density_vanish_ae n ℓ (mk a).weight (K k)ᶜ
    (Submission.ts_pwb_pair_weight_integral n ℓ a).1 (hK k).1.isClosed.measurableSet.compl
  have hB := fun k ↦ Submission.ts_pwb_upper_density_vanish_ae n ℓ _ (K k)ᶜ hfin
    (hK k).1.isClosed.measurableSet.compl
  -- `Hⁿ`-a.e. point of `F(C)` is the image of density points of `C` only
  have hD := Submission.ts_pwb_density_points_of_image_ae n ℓ C F hC.isClosed.measurableSet ⟨κ, hF⟩
  filter_upwards [ae_restrict_mem₀ hM, ae_restrict_of_ae (ae_all_iff.2 hA),
    ae_restrict_of_ae (ae_all_iff.2 hB), ae_restrict_of_ae hD,
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hKnull)] with x hxM hxA hxB hxD hxK
  intro w hw hFw f
  have hxN : x ∈ F '' C := ⟨w, hw, hFw⟩
  obtain ⟨k, hk⟩ := mem_iUnion.1 (not_not.1 fun h ↦ hxK ⟨⟨hxM, hxN⟩, h⟩)
  have hL := hblow w hw (hxD w hw hFw) f
  rw [hFw] at hL
  exact Submission.ts_pwb_blowup_at_good_point n ℓ a (F '' C) (K k) x f Γ _ hNm hNfin (hK k).1
    (hK k).2.1 hk ((hK k).2.2 x hk) (hΓ x hxN) (hxA k fun h ↦ h hk) (hxB k fun h ↦ h hk) hL
/-- **Continuity of the projection onto the range** (used for the tangent field of a `C¹` piece,
Ch. 4, 1.3). On injective `A ∈ L(ℝⁿ, ℝ^{n+ℓ})`, `A ↦ p_{A(ℝⁿ)}` is continuous: there
`p_{A(ℝⁿ)} = A (A*A)⁻¹ A*`, with `A*A` invertible, and inversion is continuous at units. -/
theorem Submission.ts_starProjection_range_continuousOn_injective : ∀ (n ℓ : ℕ), ContinuousOn (fun (A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ) ↦ (LinearMap.range A.toLinearMap).starProjection) {A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ | Function.Injective A} := by
  intro n ℓ
  -- Riesz construction of the adjoint `A ↦ A*` (Mathlib's `adjointAux`, rebuilt from
  -- `toDual` and `toSesqForm`, which the frozen imports provide).
  set adj : (EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ) →L⋆[ℝ]
      (Ambient n ℓ →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
    (ContinuousLinearMap.compSL _ _ _ _ _
      ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm :
        StrongDual ℝ (EuclideanSpace ℝ (Fin n)) →L⋆[ℝ] EuclideanSpace ℝ (Fin n))).comp
      (ContinuousLinearMap.toSesqForm :
        (EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ) →L[ℝ]
          Ambient n ℓ →L⋆[ℝ] StrongDual ℝ (EuclideanSpace ℝ (Fin n))) with hadj
  have hadj_inner : ∀ (A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ) (y : Ambient n ℓ)
      (x : EuclideanSpace ℝ (Fin n)), inner ℝ (adj A y) x = inner ℝ y (A x) := by
    intro A y x
    change inner ℝ ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
      (ContinuousLinearMap.toSesqForm A y)) x = _
    rw [InnerProductSpace.toDual_symm_apply, ContinuousLinearMap.toSesqForm_apply_coe]
    rfl
  -- `Φ(A) = A ∘ (A*A)⁻¹ ∘ A*`
  set Φ : (EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ) → (Ambient n ℓ →L[ℝ] Ambient n ℓ) :=
    fun A ↦ A ∘L (Ring.inverse (adj A ∘L A) ∘L adj A) with hΦ
  -- `A*A` is a unit for injective `A`: `⟪A*Av, v⟫ = ‖Av‖²`, and injective means bijective in
  -- finite dimension
  have hunit : ∀ A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ, Function.Injective A →
      IsUnit (adj A ∘L A) := by
    intro A hA
    have hinj : Function.Injective (adj A ∘L A) := by
      intro v w hvw
      have h0 : (adj A ∘L A) (v - w) = 0 := by
        rw [map_sub, hvw, sub_self]
      have h1 : ‖A (v - w)‖ ^ 2 = 0 := by
        rw [← real_inner_self_eq_norm_sq, ← hadj_inner]
        simp only [ContinuousLinearMap.comp_apply] at h0
        rw [h0, inner_zero_left]
      have h2 : A (v - w) = 0 := by
        simpa using h1
      have h3 : v - w = 0 := hA (by rw [h2, map_zero])
      exact sub_eq_zero.mp h3
    refine ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hinj, ?_⟩
    exact (LinearMap.injective_iff_surjective (f := (adj A ∘L A).toLinearMap)).mp hinj
  -- the projection formula `p_{A(ℝⁿ)} = Φ(A)`: `Φ(A)z ∈ A(ℝⁿ)` and `z - Φ(A)z ⊥ A(ℝⁿ)`
  have hformula : ∀ A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ, Function.Injective A →
      (LinearMap.range A.toLinearMap).starProjection = Φ A := by
    intro A hA
    ext1 z
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact ⟨_, rfl⟩
    · rintro _ ⟨v, rfl⟩
      rw [ContinuousLinearMap.coe_coe, ← hadj_inner, map_sub]
      have hcancel : adj A (Φ A z) = adj A z := by
        have := Ring.mul_inverse_cancel _ (hunit A hA)
        calc adj A (Φ A z)
            = ((adj A ∘L A) * Ring.inverse (adj A ∘L A)) (adj A z) := by
              simp only [hΦ, ContinuousLinearMap.comp_apply, mul_apply_eq_comp]
          _ = adj A z := by rw [this, one_apply_eq_self]
      rw [hcancel, sub_self, inner_zero_left]
  -- continuity of `Φ` at injective maps: `A ↦ A*` is continuous, `Ring.inverse` is continuous
  -- at units, and composition is continuous
  have hcont : ∀ A₀ : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ, Function.Injective A₀ →
      ContinuousAt Φ A₀ := by
    intro A₀ hA₀
    have hadjc : Continuous fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ ↦ adj A :=
      adj.continuous
    have hgram : Continuous fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ ↦
        adj A ∘L A := hadjc.clm_comp continuous_id
    have hinv : ContinuousAt (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ ↦
        Ring.inverse (adj A ∘L A)) A₀ := by
      have := NormedRing.inverse_continuousAt (hunit A₀ hA₀).unit
      exact ContinuousAt.comp (f := fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ ↦
        adj A ∘L A) (by simpa using this) hgram.continuousAt
    exact continuousAt_id.clm_comp (hinv.clm_comp hadjc.continuousAt)
  -- `p_{A(ℝⁿ)}` agrees with `Φ` on the injective maps, so it is continuous there
  intro A₀ hA₀
  exact ((hcont A₀ hA₀).continuousWithinAt).congr (fun A hA ↦ hformula A hA) (hformula A₀ hA₀)

/-- **The tangent projection of a `C¹` piece, as a function on its image** (Ch. 4, 1.3). If
`c‖v - w‖ ≤ ‖F v - F w‖` on `C` with `c > 0`, and `DF` is injective and continuous on `C`, then
`y ↦ p_{DF(ψ y)(ℝⁿ)}` is continuous on `F(C)`, where `ψ` inverts `F` on `C` and is
`c⁻¹`-Lipschitz on `F(C)`. -/
theorem Submission.ts_piece_projection_continuousOn_image : ∀ (n ℓ : ℕ) (C : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → Ambient n ℓ) (c : ℝ), 0 < c → (∀ v ∈ C, ∀ w ∈ C, c * ‖v - w‖ ≤ ‖F v - F w‖) → (∀ w ∈ C, Function.Injective (fderiv ℝ F w)) → ContinuousOn (fderiv ℝ F) C → ∃ G : Ambient n ℓ → (Ambient n ℓ →L[ℝ] Ambient n ℓ), ContinuousOn G (F '' C) ∧ ∀ w ∈ C, G (F w) = (LinearMap.range (fderiv ℝ F w).toLinearMap).starProjection := by
  intro n ℓ C F c hc hlow hinj hcont
  classical
  -- `F` is injective on `C`: `F v = F w` forces `c‖v - w‖ ≤ 0`
  have hInjOn : Set.InjOn F C := by
    intro v hv w hw hvw
    have h := hlow v hv w hw
    rw [hvw, sub_self, norm_zero] at h
    have h' : ‖v - w‖ ≤ 0 := by
      by_contra hpos
      exact absurd h (not_le.mpr (mul_pos hc (lt_of_not_ge hpos)))
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h')
  -- the inverse `ψ` of `F` on `C`
  set ψ : Ambient n ℓ → EuclideanSpace ℝ (Fin n) := Function.invFunOn F C with hψ
  have hψmaps : Set.MapsTo ψ (F '' C) C := fun y hy ↦ Function.invFunOn_mem hy
  have hFψ : ∀ y ∈ F '' C, F (ψ y) = y := fun y hy ↦ Function.invFunOn_eq hy
  have hψF : ∀ w ∈ C, ψ (F w) = w := fun w hw ↦ hInjOn.leftInvOn_invFunOn hw
  -- `ψ` is `c⁻¹`-Lipschitz, hence continuous, on `F(C)`
  have hψcont : ContinuousOn ψ (F '' C) := by
    refine (LipschitzOnWith.of_dist_le_mul (K := Real.toNNReal c⁻¹) fun y hy y' hy' ↦ ?_).continuousOn
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (inv_nonneg.mpr hc.le)]
    have h := hlow (ψ y) (hψmaps hy) (ψ y') (hψmaps hy')
    rw [hFψ y hy, hFψ y' hy'] at h
    rw [inv_mul_eq_div, le_div_iff₀ hc, mul_comm]
    exact h
  -- `G = p ∘ DF ∘ ψ`: `ψ` maps `F(C)` into `C`, where `DF` is continuous with injective values,
  -- and `A ↦ p_{A(ℝⁿ)}` is continuous on the injective maps
  refine ⟨fun y ↦ (LinearMap.range (fderiv ℝ F (ψ y)).toLinearMap).starProjection, ?_, ?_⟩
  · exact (Submission.ts_starProjection_range_continuousOn_injective n ℓ).comp
      (hcont.comp hψcont hψmaps) (fun y hy ↦ hinj (ψ y) (hψmaps hy))
  · intro w hw
    simp only [hψF w hw]
/-- **Borel pasting of relatively continuous operator fields** (the field on the disjointified
pieces `N_i \ ⋃_{j<i} N_j`). If every `N_i ⊆ ℝ^{n+ℓ}` is measurable and every
`G_i : ℝ^{n+ℓ} → L(ℝ^{n+ℓ}, ℝ^{n+ℓ})` is continuous on `N_i`, then some strongly measurable `g`
equals `G_i` on `N_i \ ⋃_{j<i} N_j` for every `i`: `g y = G_{i(y)} y` for the least `i(y)` with
`y ∈ N_{i(y)}`, and `g = 0` off `⋃_i N_i`. -/
theorem Submission.ts_stronglyMeasurable_paste_continuousOn : ∀ (n ℓ : ℕ) (N : ℕ → Set (Ambient n ℓ)) (G : ℕ → Ambient n ℓ → (Ambient n ℓ →L[ℝ] Ambient n ℓ)), (∀ i, MeasurableSet (N i)) → (∀ i, ContinuousOn (G i) (N i)) → ∃ g : Ambient n ℓ → (Ambient n ℓ →L[ℝ] Ambient n ℓ), StronglyMeasurable g ∧ ∀ i, ∀ y ∈ N i, (∀ j < i, y ∉ N j) → g y = G i y := by
  intro n ℓ N G hN hG
  classical
  -- `G' i` extends `G i` by `0` off `N i`; it is Borel as `G i` is continuous on the Borel `N i`.
  set G' : ℕ → Ambient n ℓ → (Ambient n ℓ →L[ℝ] Ambient n ℓ) :=
    fun i ↦ (N i).piecewise (G i) 0 with hG'
  have hG'meas : ∀ i, Measurable (G' i) := fun i ↦
    (hG i).measurable_piecewise continuousOn_const (hN i)
  -- The index `i` is admissible at `y` if `y ∈ N i` or `y` lies in no piece.
  set p : ℕ → Ambient n ℓ → Prop := fun i y ↦ y ∈ N i ∨ y ∉ ⋃ j, N j
  have hpex : ∀ y, ∃ i, p i y := by
    intro y
    by_cases hy : y ∈ ⋃ j, N j
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hy
      exact ⟨j, Or.inl hj⟩
    · exact ⟨0, Or.inr hy⟩
  have hpmeas : ∀ i, MeasurableSet {y | p i y} := fun i ↦
    (hN i).union (MeasurableSet.iUnion hN).compl
  -- `g y = G' i y` for the least admissible `i` is Borel (`Measurable.find`), hence strongly
  -- measurable since `L(ℝ^{n+ℓ}, ℝ^{n+ℓ})` is finite-dimensional.
  refine ⟨fun y ↦ G' (Nat.find (hpex y)) y, ?_, ?_⟩
  · exact (Measurable.find hG'meas hpmeas hpex).stronglyMeasurable
  · -- On `N i \ ⋃_{j<i} N j` the least admissible index is `i`.
    intro i y hy hfirst
    have hfind : Nat.find (hpex y) = i := by
      rw [Nat.find_eq_iff]
      refine ⟨Or.inl hy, fun j hj ↦ ?_⟩
      rintro (hjy | hnot)
      · exact hfirst j hj hjy
      · exact hnot (mem_iUnion.mpr ⟨i, hy⟩)
    simp only [hfind, hG', Set.piecewise_eq_of_mem _ _ _ hy]

/-- **Tangent projection field of a sequence of Lipschitz pieces** (measurability of
`x ↦ p_{T_x V}`, Ch. 4, 1.3). Let `C_i ⊆ ℝⁿ` be compact and `F_i : ℝⁿ → ℝ^{n+ℓ}` Lipschitz,
differentiable on `C_i` with injective `DF_i` continuous on `C_i`, and
`c_i|v - w| ≤ |F_i(v) - F_i(w)|` on `C_i` with `c_i > 0`. Then some strongly measurable
`g : ℝ^{n+ℓ} → L(ℝ^{n+ℓ}, ℝ^{n+ℓ})` is the orthogonal projection onto `DF_i(w)(ℝⁿ)` at `F_i(w)`
whenever `F_i(w) ∉ F_j(C_j)` for all `j < i`: the projection field of each piece is continuous
on the compact image `F_i(C_i)` (`ts_piece_projection_continuousOn_image`), and these fields are
pasted along `F_i(C_i) \ ⋃_{j<i} F_j(C_j)` (`ts_stronglyMeasurable_paste_continuousOn`). -/
theorem Submission.ts_piece_tangent_projection_field : ∀ (n ℓ : ℕ) (C : ℕ → Set (EuclideanSpace ℝ (Fin n))) (F : ℕ → EuclideanSpace ℝ (Fin n) → Ambient n ℓ), (∀ i, IsCompact (C i) ∧ (∃ K : NNReal, LipschitzWith K (F i)) ∧ (∀ w ∈ C i, DifferentiableAt ℝ (F i) w ∧ Function.Injective (fderiv ℝ (F i) w)) ∧ ContinuousOn (fderiv ℝ (F i)) (C i) ∧ ∃ c : ℝ, 0 < c ∧ ∀ v ∈ C i, ∀ w ∈ C i, c * ‖v - w‖ ≤ ‖F i v - F i w‖) → ∃ g : Ambient n ℓ → (Ambient n ℓ →L[ℝ] Ambient n ℓ), StronglyMeasurable g ∧ ∀ i, ∀ w ∈ C i, (∀ j < i, F i w ∉ F j '' C j) → g (F i w) = (LinearMap.range (fderiv ℝ (F i) w).toLinearMap).starProjection := by
  intro n ℓ C F hpiece
  -- Step 3: on each piece `N_i = F_i(C_i)` the projection field `G_i` is continuous, with
  -- `G_i(F_i(w)) = p_{DF_i(w)(ℝⁿ)}` for `w ∈ C_i`.
  have hG : ∀ i, ∃ G : Ambient n ℓ → (Ambient n ℓ →L[ℝ] Ambient n ℓ),
      ContinuousOn G (F i '' C i) ∧
        ∀ w ∈ C i, G (F i w) = (LinearMap.range (fderiv ℝ (F i) w).toLinearMap).starProjection := by
    intro i
    obtain ⟨-, -, hdiff, hcont, c, hc, hlow⟩ := hpiece i
    exact Submission.ts_piece_projection_continuousOn_image n ℓ (C i) (F i) c hc hlow
      (fun w hw ↦ (hdiff w hw).2) hcont
  choose G hGcont hGval using hG
  -- Step 4: `N_i` is compact, as the image of the compact `C_i` under the Lipschitz `F_i`, hence
  -- Borel.
  have hN : ∀ i, MeasurableSet (F i '' C i) := fun i ↦ by
    obtain ⟨hC, ⟨K, hK⟩, -⟩ := hpiece i
    exact (hC.image hK.continuous).measurableSet
  -- Step 5: paste the `G_i` along the disjointified pieces `N_i \ ⋃_{j<i} N_j`.
  obtain ⟨g, hgmeas, hg⟩ :=
    Submission.ts_stronglyMeasurable_paste_continuousOn n ℓ (fun i ↦ F i '' C i) G hN hGcont
  -- Step 6: at `F_i(w)` outside the earlier pieces, `g = G_i = p_{DF_i(w)(ℝⁿ)}`.
  refine ⟨g, hgmeas, fun i w hw hfirst ↦ ?_⟩
  rw [hg i (F i w) (mem_image_of_mem (F i) hw) hfirst, hGval i w hw]
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

/-- **Ch. 4, 1.3 and 2.2, with Ch. 3, 1.6–1.9.** `ApproxTangentAE`; for every `V`, `μ_V` is finite
on compact sets, `dim T_x V = n` `μ_V`-a.e. and `x ↦ p_{T_x V}` is `μ_V`-measurable; and the first
variation formula `FirstVariationFormula`. Up to an `Hⁿ`-null set, `M` is covered by the Lipschitz
pieces `F_i(C_i)` of `rectifiable_lipschitz_piece_cover`. At `Hⁿ`-a.e. `x = F_i(w) ∈ M` the
weighted blow-up of `μ_V` is `θ(x) Hⁿ ⌞ DF_i(w)(ℝⁿ)` (`ts_piece_weighted_blowup_ae`), so the
approximate tangent plane at `x` is `DF_i(w)(ℝⁿ)` for every piece through `x`. -/
theorem Submission.tangent_structure_first_variation : ApproxTangentAE ∧
    (∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ), 0 < n →
      IsFiniteMeasureOnCompacts V.weight ∧
        (∀ᵐ x ∂V.weight, Module.finrank ℝ (V.tangentSpace x) = n) ∧
        AEStronglyMeasurable (fun x ↦ (V.tangentSpace x).starProjection) V.weight) ∧
    FirstVariationFormula := by
  classical
  -- Step 6(i): `μ_V(K) = ∫_{M ∩ K} θ dHⁿ < ∞` for compact `K`.
  have hfin : ∀ (n ℓ : ℕ) (a : RectifiablePair n ℓ),
      IsFiniteMeasureOnCompacts (mk a).weight := by
    intro n ℓ a
    refine ⟨fun K hK ↦ ?_⟩
    change pairWeight n a.M a.θ K < ⊤
    rw [pairWeight, withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
    exact (a.isRectifiablePair.locallyIntegrable K hK).setLIntegral_lt_top
  -- Steps 1–6 for one pair `a = (M, θ)`: a piece cover such that, `Hⁿ`-a.e. on `M`, `T_x V` is
  -- the tangent plane of every piece through `x`, the conclusions of `ApproxTangentAE` hold and
  -- `dim T_x V = n`; and `x ↦ p_{T_x V}` is `Hⁿ ⌞ M`-measurable.
  have hpair : ∀ (n ℓ : ℕ) (a : RectifiablePair n ℓ), 0 < n →
      ∃ (N₀ : Set (Ambient n ℓ)) (C : ℕ → Set (EuclideanSpace ℝ (Fin n)))
        (F : ℕ → EuclideanSpace ℝ (Fin n) → Ambient n ℓ),
        MeasurableSet N₀ ∧ (μHE[n] : Measure (Ambient n ℓ)) N₀ = 0 ∧
        a.M ⊆ N₀ ∪ ⋃ i, F i '' C i ∧
        (∀ i, IsCompact (C i) ∧ (∃ K : NNReal, LipschitzWith K (F i)) ∧
          (∀ w ∈ C i, DifferentiableAt ℝ (F i) w ∧ Function.Injective (fderiv ℝ (F i) w)) ∧
          ContinuousOn (fderiv ℝ (F i)) (C i) ∧
          ∃ c : ℝ, 0 < c ∧ ∀ v ∈ C i, ∀ w ∈ C i, c * ‖v - w‖ ≤ ‖F i v - F i w‖) ∧
        (∀ᵐ x ∂(μHE[n] : Measure (Ambient n ℓ)).restrict a.M,
          (∀ i, ∀ w ∈ C i, F i w = x →
            (mk a).tangentSpace x = LinearMap.range (fderiv ℝ (F i) w).toLinearMap) ∧
          ((∃! P, (mk a).IsApproxTangentAt x P) ∧
            Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n a.M a.θ x
              ((mk a).tangentSpace x) ∧
            (mk a).HasDensityAt x (a.θ x)) ∧
          Module.finrank ℝ ((mk a).tangentSpace x) = n) ∧
        AEStronglyMeasurable (fun x ↦ ((mk a).tangentSpace x).starProjection)
          ((μHE[n] : Measure (Ambient n ℓ)).restrict a.M) := by
    intro n ℓ a hn
    -- Step 1: the Lipschitz pieces `N_i = F_i(C_i)`.
    obtain ⟨N₀, C, F, hN₀, hN₀null, hcover, hpiece⟩ :=
      Submission.rectifiable_lipschitz_piece_cover n ℓ a.M hn
        a.isRectifiablePair.countablyRectifiable
    -- `T_i(F_i(w)) = DF_i(w)(ℝⁿ)` is `n`-dimensional.
    have hrank : ∀ i, ∀ w ∈ C i,
        Module.finrank ℝ (LinearMap.range (fderiv ℝ (F i) w).toLinearMap) = n := fun i w hw ↦
      (LinearMap.finrank_range_of_inj (f := (fderiv ℝ (F i) w).toLinearMap)
        ((hpiece i).2.2.1 w hw).2).trans finrank_euclideanSpace_fin
    -- Step 4 on every piece: the weighted blow-up `(★)` at `x = F_i(w)`.
    have hblow : ∀ᵐ x ∂(μHE[n] : Measure (Ambient n ℓ)).restrict a.M, ∀ i, ∀ w ∈ C i,
        F i w = x → ∀ f : C_c(Ambient n ℓ, ℝ),
          Tendsto (fun t : ℝ ↦ (t ^ n)⁻¹ * ∫ y, f (t⁻¹ • (y - x)) ∂(mk a).weight) (𝓝[>] 0)
            (𝓝 (a.θ x * ∫ y in (LinearMap.range (fderiv ℝ (F i) w).toLinearMap :
              Set (Ambient n ℓ)), f y ∂μHE[n])) :=
      ae_all_iff.2 fun i ↦ Submission.ts_piece_weighted_blowup_ae n ℓ a (C i) (F i) hn (hpiece i)
    -- `Hⁿ ⌞ M`-a.e. `x` lies in `M \ N₀`, hence on some piece.
    have hon : ∀ᵐ x ∂(μHE[n] : Measure (Ambient n ℓ)).restrict a.M,
        x ∈ a.M ∧ ∃ i, x ∈ F i '' C i := by
      filter_upwards [ae_restrict_mem₀ a.isRectifiablePair.measurable,
        ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hN₀null)] with x hxM hxN₀
      exact ⟨hxM, mem_iUnion.1 ((hcover hxM).resolve_left hxN₀)⟩
    -- Step 5.
    have hae : ∀ᵐ x ∂(μHE[n] : Measure (Ambient n ℓ)).restrict a.M,
        (∀ i, ∀ w ∈ C i, F i w = x →
          (mk a).tangentSpace x = LinearMap.range (fderiv ℝ (F i) w).toLinearMap) ∧
        ((∃! P, (mk a).IsApproxTangentAt x P) ∧
          Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n a.M a.θ x
            ((mk a).tangentSpace x) ∧
          (mk a).HasDensityAt x (a.θ x)) ∧
        Module.finrank ℝ ((mk a).tangentSpace x) = n := by
      filter_upwards [hblow, hon] with x hx hxon
      obtain ⟨hxM, i, w, hw, hFw⟩ := hxon
      -- 5(i): each piece plane through `x` is an approximate tangent plane, with `c = θ(x) > 0`.
      have happrox : ∀ i, ∀ w ∈ C i, F i w = x →
          (mk a).IsApproxTangentAt x (LinearMap.range (fderiv ℝ (F i) w).toLinearMap) :=
        fun i w hw hFw ↦ ⟨hrank i w hw, a.θ x, a.isRectifiablePair.pos x hxM, hx i w hw hFw⟩
      -- 5(ii): the approximate tangent plane is unique, so `T_x V` is the piece plane.
      have hP := happrox i w hw hFw
      have hT : (mk a).tangentSpace x = LinearMap.range (fderiv ℝ (F i) w).toLinearMap := by
        have hex : ∃ P, (mk a).IsApproxTangentAt x P := ⟨_, hP⟩
        rw [RectifiableVarifold.tangentSpace, dite_eq_left hex]
        exact Submission.ts_approx_tangent_plane_unique n ℓ (mk a) x _ _ hex.choose_spec hP
      refine ⟨fun j v hv hFv ↦ hT.trans
          (Submission.ts_approx_tangent_plane_unique n ℓ (mk a) x _ _ hP (happrox j v hv hFv)),
        ⟨⟨_, hP, fun Q hQ ↦ Submission.ts_approx_tangent_plane_unique n ℓ (mk a) x _ _ hQ hP⟩,
          ?_, ?_⟩, ?_⟩
      · -- 5(iii): `T_x V` is the approximate tangent space of Ch. 3, 1.7.
        rw [hT]
        exact Submission.ts_blowup_weighted_tangent n ℓ a x _ hP.1 (hx i w hw hFw)
      · -- 5(iv): `Θⁿ(μ_V, x) = θ(x)`.
        exact Submission.ts_blowup_closedBall_density n ℓ (mk a).weight x _ (a.θ x) hn
          (hfin n ℓ a) hP.1 (a.isRectifiablePair.pos x hxM) (hx i w hw hFw)
      · rw [hT]
        exact hP.1
    -- Step 6(iii): `p_{T_x V} = g(x)`, evaluated at the first piece through `x`.
    obtain ⟨g, hg, hgF⟩ := Submission.ts_piece_tangent_projection_field n ℓ C F hpiece
    refine ⟨N₀, C, F, hN₀, hN₀null, hcover, hpiece, hae, hg.aestronglyMeasurable.congr ?_⟩
    filter_upwards [hae, hon] with x hx hxon
    obtain ⟨i, ⟨w, hw, hFw⟩, hmin⟩ : ∃ i, x ∈ F i '' C i ∧ ∀ j < i, x ∉ F j '' C j :=
      ⟨Nat.find hxon.2, Nat.find_spec hxon.2, fun j hj ↦ Nat.find_min hxon.2 hj⟩
    rw [hx.1 i w hw hFw]
    subst hFw
    exact hgF i w hw hmin
  refine ⟨fun n ℓ a hn ↦ ?_, fun n ℓ V hn ↦ ?_, fun n ℓ a φ ε K hn hφ ↦ ?_⟩
  · -- `ApproxTangentAE`.
    obtain ⟨_, _, _, _, _, _, _, hae, _⟩ := hpair n ℓ a hn
    exact hae.mono fun x hx ↦ hx.2.1
  · -- Step 6, (GF), for `V = v(M, θ)`, using `μ_V ≪ Hⁿ ⌞ M`.
    obtain ⟨a, rfl⟩ : ∃ a : RectifiablePair n ℓ, mk a = V := Quot.exists_rep V
    obtain ⟨_, _, _, _, _, _, _, hae, hproj⟩ := hpair n ℓ a hn
    have hac : (mk a).weight ≪ (μHE[n] : Measure (Ambient n ℓ)).restrict a.M :=
      withDensity_absolutelyContinuous _ _
    exact ⟨hfin n ℓ a, hac.ae_le (hae.mono fun x hx ↦ hx.2.2), hproj.mono_ac hac⟩
  · -- Steps 7–10, `FirstVariationFormula`, on the piece cover.
    obtain ⟨N₀, C, F, hN₀, hN₀null, hcover, hpiece, hae, hproj⟩ := hpair n ℓ a hn
    exact Submission.ts_first_variation_of_pieces n ℓ a N₀ C F φ ε K hn hN₀ hN₀null hcover
      hpiece (hae.mono fun x hx ↦ hx.1) hproj hφ
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
/-- **Simon Ch. 1, Thm 3.3 (special case).** If `μ` is finite on compact sets, `μ(A) = 0`, and
at every `x ∈ A` the density `lim_{ρ↓0} μ(B_ρ(x)) / (ωₙρⁿ)` exists and is `≥ t > 0`, then
`Hⁿ(A) = 0`. Proof: for `ε > 0` take an open `O ⊇ A` with `μ(O)` small, choose at each `x ∈ A`
small radii with `B_ρ(x) ⊆ O` and `μ(B_ρ(x)) ≥ (tωₙ/2)ρⁿ`, and apply the Vitali `5r`-covering
lemma; the disjoint balls have total mass `≤ μ(O)`, which bounds the `Hⁿ`-size of the cover. -/
theorem Submission.hausdorff_null_of_measure_null_density_ge : ∀ (n ℓ : ℕ) (μ : Measure (Ambient n ℓ)) (A : Set (Ambient n ℓ)) (t : ℝ), 0 < n → IsFiniteMeasureOnCompacts μ → 0 < t → μ A = 0 → (∀ x ∈ A, ∃ s : ℝ, t ≤ s ∧ Tendsto (fun ρ ↦ μ.real (closedBall x ρ) / (omega n * ρ ^ n)) (𝓝[>] 0) (𝓝 s)) → (μHE[n] : Measure (Ambient n ℓ)) A = 0 := by
  intro n ℓ μ A t _ hμ ht hA hdens
  have hω : 0 < omega n :=
    ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne
  obtain ⟨c, hc, hct⟩ : ∃ c : ℝ, 0 < c ∧ c = t / 2 * omega n := ⟨_, by positivity, rfl⟩
  obtain ⟨K, hK, hKc⟩ : ∃ K : ℝ, 0 < K ∧ K * c = 10 ^ n :=
    ⟨10 ^ n / c, by positivity, div_mul_cancel₀ _ hc.ne'⟩
  -- the density hypothesis gives `μ(B_ρ(x)) ≥ c ρⁿ` at arbitrarily small radii `ρ`
  have hlow : ∀ x ∈ A, ∀ η > 0, ∃ ρ, 0 < ρ ∧ ρ < η ∧
      ENNReal.ofReal (c * ρ ^ n) ≤ μ (closedBall x ρ) := by
    intro x hx η hη
    obtain ⟨s, hts, hs⟩ := hdens x hx
    obtain ⟨ρ, hρq, hρ⟩ :=
      ((hs.eventually (lt_mem_nhds (by linarith : t / 2 < s))).and (Ioo_mem_nhdsGT hη)).exists
    refine ⟨ρ, hρ.1, hρ.2, ?_⟩
    rw [lt_div_iff₀ (mul_pos hω (pow_pos hρ.1 n))] at hρq
    rw [← ofReal_measureReal (measure_closedBall_lt_top (μ := μ)).ne, hct, mul_assoc]
    exact ENNReal.ofReal_le_ofReal hρq.le
  suffices h : (μH[n] : Measure (Ambient n ℓ)) A = 0 by
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, h, smul_zero]
  refine le_antisymm (le_of_forall_gt_imp_ge_of_dense fun ε hε ↦ ?_) zero_le
  have hεK : μ A < ε / ENNReal.ofReal K := hA ▸ ENNReal.div_pos hε.ne' ENNReal.ofReal_ne_top
  obtain ⟨O, hAO, hO, hμO⟩ := Set.exists_isOpen_lt_of_lt A _ hεK
  -- at every scale `δ`, a countable cover of `A` by balls `B_{5R(b)}(b)` with `Σ diamⁿ ≤ ε`
  have hcover : ∀ δ : ℝ, 0 < δ → ∃ U : Set (Ambient n ℓ), U.Countable ∧
      ∃ R : Ambient n ℓ → ℝ, (∀ b ∈ U, 0 < R b ∧ R b ≤ δ) ∧
        A ⊆ ⋃ b ∈ U, closedBall b (5 * R b) ∧
        ∑' b : U, ediam (closedBall (b : Ambient n ℓ) (5 * R b)) ^ (n : ℝ) ≤ ε := by
    intro δ hδ
    have hex : ∀ x, ∃ ρ, x ∈ A → 0 < ρ ∧ ρ ≤ δ ∧ closedBall x ρ ⊆ O ∧
        ENNReal.ofReal (c * ρ ^ n) ≤ μ (closedBall x ρ) := by
      intro x
      by_cases hx : x ∈ A
      · obtain ⟨η, hη, hηO⟩ := Metric.isOpen_iff.mp hO x (hAO hx)
        obtain ⟨ρ, hρ0, hρη, hρμ⟩ := hlow x hx (min δ η) (lt_min hδ hη)
        exact ⟨ρ, fun _ ↦ ⟨hρ0, hρη.le.trans (min_le_left _ _),
          (closedBall_subset_ball (hρη.trans_le (min_le_right _ _))).trans hηO, hρμ⟩⟩
      · exact ⟨0, fun h ↦ absurd h hx⟩
    choose R hR using hex
    obtain ⟨u, huA, hudisj, hucov⟩ :=
      Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall A id R δ
        (fun a ha ↦ (hR a ha).2.1) 5 (by norm_num)
    have hucount : u.Countable := hudisj.countable_of_nonempty_interior fun b hb ↦
      ⟨b, mem_interior.2 ⟨ball b (R b), ball_subset_closedBall, isOpen_ball,
        mem_ball_self (hR b (huA hb)).1⟩⟩
    refine ⟨u, hucount, R, fun b hb ↦ ⟨(hR b (huA hb)).1, (hR b (huA hb)).2.1⟩, ?_, ?_⟩
    · intro a ha
      obtain ⟨b, hbu, hab⟩ := hucov a ha
      exact mem_biUnion hbu (hab (mem_closedBall_self (hR a ha).1.le))
    · calc ∑' b : u, ediam (closedBall (b : Ambient n ℓ) (5 * R b)) ^ (n : ℝ)
          ≤ ∑' b : u, ENNReal.ofReal K * μ (closedBall (b : Ambient n ℓ) (R b)) := by
            refine ENNReal.tsum_le_tsum fun b ↦ ?_
            obtain ⟨hb0, -, -, hbμ⟩ := hR b (huA b.2)
            have hdiam : ediam (closedBall (b : Ambient n ℓ) (5 * R b)) ≤
                ENNReal.ofReal (10 * R b) := by
              refine Metric.ediam_le_of_forall_dist_le fun y hy z hz ↦ ?_
              have := dist_triangle_right y z b
              rw [mem_closedBall] at hy hz
              linarith
            calc ediam (closedBall (b : Ambient n ℓ) (5 * R b)) ^ (n : ℝ)
                ≤ ENNReal.ofReal (10 * R b) ^ (n : ℝ) :=
                  ENNReal.rpow_le_rpow hdiam (Nat.cast_nonneg n)
              _ = ENNReal.ofReal (K * (c * R b ^ n)) := by
                rw [ENNReal.rpow_natCast, ← ENNReal.ofReal_pow (by positivity), ← mul_assoc, hKc,
                  mul_pow]
              _ = ENNReal.ofReal K * ENNReal.ofReal (c * R b ^ n) := ENNReal.ofReal_mul hK.le
              _ ≤ ENNReal.ofReal K * μ (closedBall (b : Ambient n ℓ) (R b)) := by gcongr
        _ = ENNReal.ofReal K * ∑' b : u, μ (closedBall (b : Ambient n ℓ) (R b)) :=
            ENNReal.tsum_mul_left
        _ ≤ ENNReal.ofReal K * μ O := by
            gcongr
            calc ∑' b : u, μ (closedBall (b : Ambient n ℓ) (R b))
                ≤ μ (⋃ b : u, closedBall (b : Ambient n ℓ) (R b)) :=
                  tsum_meas_le_meas_iUnion_of_disjoint μ (fun b ↦ measurableSet_closedBall)
                    ((pairwise_subtype_iff_pairwise_set u _).2 hudisj)
              _ ≤ μ O := measure_mono (iUnion_subset fun b ↦ (hR b (huA b.2)).2.2.1)
        _ ≤ ENNReal.ofReal K * (ε / ENNReal.ofReal K) := by gcongr
        _ = ε := ENNReal.mul_div_cancel (by simp [hK]) ENNReal.ofReal_ne_top
  -- covers at scales `1 / (m + 1) → 0` bound `Hⁿ(A)` by `ε`
  choose U hUc R hR hUcov hUsum using fun m : ℕ ↦ hcover (1 / (m + 1)) Nat.one_div_pos_of_nat
  have : ∀ m, Countable (U m) := fun m ↦ (hUc m).to_subtype
  calc (μH[n] : Measure (Ambient n ℓ)) A
      ≤ liminf (fun m ↦ ∑' b : U m,
          ediam (closedBall (b : Ambient n ℓ) (5 * R m b)) ^ (n : ℝ)) atTop := by
        refine Measure.hausdorffMeasure_le_liminf_tsum _ A
          (fun m : ℕ ↦ ENNReal.ofReal (10 * (1 / (m + 1)))) ?_
          (fun m (b : U m) ↦ closedBall (b : Ambient n ℓ) (5 * R m b)) ?_ ?_
        · simpa using ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul 10)
        · refine Eventually.of_forall fun m b ↦ ?_
          refine Metric.ediam_le_of_forall_dist_le fun y hy z hz ↦ ?_
          have := dist_triangle_right y z b
          have hb := (hR m b b.2).2
          rw [mem_closedBall] at hy hz
          linarith
        · refine Eventually.of_forall fun m a ha ↦ ?_
          obtain ⟨b, hb, hab⟩ := mem_iUnion₂.1 (hUcov m ha)
          exact mem_iUnion.2 ⟨⟨b, hb⟩, hab⟩
    _ ≤ ε := liminf_le_of_frequently_le' (Frequently.of_forall fun m ↦ hUsum m)

/-- **Simon 3.12 (p. 91), given `ApproxTangentAE`.** If `μ_V` is finite on compact sets and
`Θⁿ(μ_V, ·)` exists at every point of the open set `U`, then `(M_V, Θⁿ(μ_V, ·))` is an admissible
pair whose weight is `μ_V ⌞ U`. Proof: for a representative `(M, θ)` of `V`, `Θⁿ(μ_V, ·) = θ`
`Hⁿ`-a.e. on `M` by `ApproxTangentAE`, so `Hⁿ((M ∩ U) \ M_V) = 0`; `μ_V(Mᶜ) = 0`, so
`Hⁿ(M_V \ M) = 0` by the density lemma `Submission.hausdorff_null_of_measure_null_density_ge`
applied to `{x ∈ U \ M : Θⁿ(μ_V, x) ≥ 1/(k+1)}`. Hence `M_V = M ∩ U` up to `Hⁿ`-null sets. -/
theorem Submission.canonicalCarrier_rectifiablePair_weight : ApproxTangentAE → ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)), 0 < n → IsOpen U → IsFiniteMeasureOnCompacts V.weight → (∀ ξ ∈ U, V.HasDensityAt ξ (V.density ξ)) → IsRectifiablePair n (V.canonicalCarrier U) V.density ∧ pairWeight n (V.canonicalCarrier U) V.density = V.weight.restrict U := by
  intro hAT n ℓ V U hn hU hfin hdens
  -- a representative `(M, θ)` of `V`, so that `μ_V = Hⁿ ⌞ θ`
  obtain ⟨a, ha⟩ : ∃ a, RectifiableVarifold.mk a = V := Quot.exists_rep V
  obtain ⟨hrect, hmeas, hpos, hint⟩ := a.isRectifiablePair
  have hw : V.weight = pairWeight n a.M a.θ := by subst ha; rfl
  -- `Θ = θ` `Hⁿ`-a.e. on `M`, by `ApproxTangentAE` and uniqueness of limits
  have hN : ∀ S ⊆ a.M, V.density =ᵐ[(μHE[n] : Measure (Ambient n ℓ)).restrict S] a.θ := by
    intro S hS
    refine EventuallyEq.filter_mono ?_ (ae_mono (Measure.restrict_mono hS le_rfl))
    subst ha
    filter_upwards [hAT n ℓ a hn] with x hx
    exact hx.2.2.limUnder_eq
  -- `μ_V(Mᶜ) = 0`
  have hMc : V.weight a.Mᶜ = 0 := by
    rw [hw]
    refine withDensity_absolutelyContinuous _ _ ?_
    rw [Measure.restrict_apply₀' hmeas, compl_inter_self, measure_empty]
  -- `Hⁿ(M_V \ M) = 0`: apply the density lemma to `{x ∈ U \ M : Θ(x) ≥ 1/(k+1)}`
  have hVM : (μHE[n] : Measure (Ambient n ℓ)) (V.canonicalCarrier U \ a.M) = 0 := by
    have hsub : V.canonicalCarrier U \ a.M ⊆
        ⋃ k : ℕ, {x | x ∈ U ∧ x ∉ a.M ∧ 1 / ((k : ℝ) + 1) ≤ V.density x} := by
      rintro x ⟨⟨hxU, hx⟩, hxM⟩
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hx
      exact mem_iUnion.2 ⟨k, hxU, hxM, hk.le⟩
    refine measure_mono_null hsub (measure_iUnion_null fun k ↦ ?_)
    refine Submission.hausdorff_null_of_measure_null_density_ge n ℓ _ _ (1 / ((k : ℝ) + 1)) hn
      hfin (by positivity) (measure_mono_null (fun x hx ↦ hx.2.1) hMc) ?_
    rintro x ⟨hxU, -, hx⟩
    exact ⟨_, hx, hdens x hxU⟩
  -- `Hⁿ((M ∩ U) \ M_V) = 0`, since `Θ = θ > 0` `Hⁿ`-a.e. on `M`
  have hMV : (μHE[n] : Measure (Ambient n ℓ)) ((a.M ∩ U) \ V.canonicalCarrier U) = 0 := by
    have h : ∀ᵐ x ∂(μHE[n] : Measure (Ambient n ℓ)).restrict a.M, 0 < V.density x := by
      filter_upwards [hN a.M subset_rfl, ae_restrict_mem₀ hmeas] with x hx hxM
      rw [hx]
      exact hpos x hxM
    rw [ae_iff, Measure.restrict_apply₀' hmeas] at h
    refine measure_mono_null ?_ h
    rintro x ⟨⟨hxM, hxU⟩, hx⟩
    exact ⟨fun h ↦ hx ⟨hxU, h⟩, hxM⟩
  -- hence `M_V = M ∩ U` up to an `Hⁿ`-null set
  have hae : V.canonicalCarrier U =ᵐ[(μHE[n] : Measure (Ambient n ℓ))] a.M ∩ U := by
    refine ae_eq_set.2 ⟨measure_mono_null ?_ hVM, hMV⟩
    rintro x ⟨hx, hxMU⟩
    exact ⟨hx, fun hxM ↦ hxMU ⟨hxM, hx.1⟩⟩
  refine ⟨⟨?_, (hmeas.inter hU.measurableSet.nullMeasurableSet).congr hae.symm,
    fun x hx ↦ hx.2, fun K hK ↦ ?_⟩, ?_⟩
  · -- add `M_V \ M` to the null set of a Lipschitz cover of `M`
    obtain ⟨M₀, hM₀, F, hF, hcover⟩ := hrect
    refine ⟨M₀ ∪ (V.canonicalCarrier U \ a.M), measure_union_null hM₀ hVM, F, hF,
      fun x hx ↦ ?_⟩
    by_cases hxM : x ∈ a.M
    · rcases hcover hxM with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · exact Or.inl (Or.inr ⟨hx, hxM⟩)
  · have h : IntegrableOn a.θ (a.M ∩ U ∩ K) μHE[n] :=
      (hint K hK).mono_set fun x hx ↦ ⟨hx.1.1, hx.2⟩
    exact (h.congr_fun_ae (hN _ fun x hx ↦ hx.1.1).symm).congr_set_ae (hae.inter .rfl)
  · rw [hw]
    unfold pairWeight
    rw [Measure.restrict_congr_set hae, restrict_withDensity hU.measurableSet,
      Measure.restrict_restrict hU.measurableSet, inter_comm U a.M]
    refine withDensity_congr_ae ?_
    filter_upwards [hN (a.M ∩ U) inter_subset_left] with x hx
    rw [hx]
/-- **Ch. 4, 3.13 (p. 91) and 4.10(1) (p. 95).** Assume `ApproxTangentAE`, and that `Θⁿ(μ_V, ·)`
exists on the open set `U` and is upper semicontinuous there. Then `{x ∈ M_V : Θⁿ(μ_V, x) ≥ α}`
is relatively closed in `U` for every `α > 0`, and if `θ ≥ α > 0` `Hⁿ`-a.e. on `M ∩ U` then
`M_V = spt V ∩ U` and `Θⁿ(μ_V, ·) ≥ α` at every point of `M_V`. -/
theorem Submission.canonicalCarrier_closed_support : ApproxTangentAE → ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)), 0 < n → IsOpen U → (∀ ξ ∈ U, V.HasDensityAt ξ (V.density ξ)) → UpperSemicontinuousOn V.density U → (∀ α : ℝ, 0 < α → ∃ C, IsClosed C ∧ {x | x ∈ V.canonicalCarrier U ∧ α ≤ V.density x} = C ∩ U) ∧ ∀ α : ℝ, 0 < α → V.MultiplicityGE α U → V.canonicalCarrier U = V.support ∩ U ∧ ∀ x ∈ V.canonicalCarrier U, α ≤ V.density x := by
  intro hTangent n ℓ V U hn hU hDensity hUSC
  refine ⟨fun α hα ↦ ?_, fun α hα hθ ↦ ?_⟩
  · -- Upper semicontinuity: `U ∩ {Θ ≥ α} = U ∩ C` with `C` closed; `Θ ≥ α > 0` gives `x ∈ M_V`.
    obtain ⟨C, hC, hUC⟩ := upperSemicontinuousOn_iff_preimage_Ici.1 hUSC α
    refine ⟨C, hC, Set.ext fun x ↦ ?_⟩
    have hx := Set.ext_iff.1 hUC x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ici] at hx
    simp only [canonicalCarrier, Set.mem_ofPred_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨⟨hxU, -⟩, hαx⟩
      exact ⟨(hx.1 ⟨hxU, hαx⟩).2, hxU⟩
    · rintro ⟨hxC, hxU⟩
      have hαx := (hx.2 ⟨hxU, hxC⟩).2
      exact ⟨⟨hxU, hα.trans_le hαx⟩, hαx⟩
  · obtain ⟨a, ha, hθ⟩ := hθ
    -- `Θ ≥ α` `μ_V`-a.e. in `U`: `Θ = θ` `Hⁿ`-a.e. on `M` by `ApproxTangentAE`, and
    -- `μ_V = (Hⁿ ⌞ M).withDensity θ ≪ Hⁿ ⌞ M`.
    have hae : ∀ᵐ x ∂V.weight, x ∈ U → α ≤ V.density x := by
      have hθU : ∀ᵐ x ∂(μHE[n] : Measure (Ambient n ℓ)).restrict a.M, x ∈ U → α ≤ a.θ x := by
        rw [← ae_restrict_iff' hU.measurableSet, Measure.restrict_restrict hU.measurableSet,
          Set.inter_comm]
        exact hθ
      have hac : V.weight ≪ (μHE[n] : Measure (Ambient n ℓ)).restrict a.M := by
        rw [← ha]
        exact withDensity_absolutelyContinuous _ _
      refine hac.ae_le ?_
      filter_upwards [hTangent n ℓ a hn, hθU] with x hx hxθ hxU
      have hlim : V.density x = a.θ x := by
        rw [← ha]
        exact Filter.Tendsto.limUnder_eq hx.2.2
      rw [hlim]
      exact hxθ hxU
    -- At `x ∈ spt V ∩ U` with `Θ(x) < α`, upper semicontinuity gives a neighbourhood of `x`
    -- of positive `μ_V`-measure inside `U ∩ {Θ < α}`, which is `μ_V`-null.
    have hsupp : ∀ x ∈ V.support ∩ U, α ≤ V.density x := by
      rintro x ⟨hx, hxU⟩
      by_contra hlt
      rw [not_le] at hlt
      have hev := upperSemicontinuousWithinAt_iff.1 (upperSemicontinuousOn_iff.1 hUSC x hxU) α hlt
      rw [hU.nhdsWithin_eq hxU] at hev
      have hpos :=
        (Measure.mem_support_iff_forall x).1 hx _ (Filter.inter_mem (hU.mem_nhds hxU) hev)
      refine hpos.ne' (measure_mono_null ?_ (ae_iff.1 hae))
      rintro y ⟨hyU, hy⟩ h
      exact (not_le.2 hy) (h hyU)
    -- `Θ(x) > 0` forces `μ_V(B_ρ(x)) > 0` for small `ρ`, so `M_V ⊆ spt V`.
    have hcarrier : ∀ x ∈ V.canonicalCarrier U, x ∈ V.support := by
      rintro x ⟨hxU, hx⟩
      refine (Metric.nhds_basis_closedBall.mem_measureSupport (μ := V.weight)).2 fun r hr ↦ ?_
      obtain ⟨ρ, hρq, hρr⟩ := ((Filter.Tendsto.eventually (hDensity x hxU) (lt_mem_nhds hx)).and
        (Ioo_mem_nhdsGT hr)).exists
      have hρ : V.weight (closedBall x ρ) ≠ 0 := by
        intro h
        rw [Measure.real, h, ENNReal.toReal_zero, zero_div] at hρq
        exact lt_irrefl _ hρq
      exact (pos_iff_ne_zero.2 hρ).trans_le (measure_mono (closedBall_subset_closedBall hρr.2.le))
    refine ⟨Set.Subset.antisymm (fun x hx ↦ ⟨hcarrier x hx, hx.1⟩)
      fun x hx ↦ ⟨hx.2, hα.trans_le (hsupp x hx)⟩, fun x hx ↦ hsupp x ⟨hcarrier x hx, hx.1⟩⟩
/-- **Ch. 4, 3.8–3.10 (p. 91), from the annulus identity.** Write `w = |D^⊥r|²/rⁿ` and
`a(ρ) = ρ⁻ⁿ μ_V(B_ρ(ξ))`. If for all `0 < σ ≤ ρ < R` the function `w` is `μ_V`-integrable on
`B_ρ(ξ) \ B_σ(ξ)` and `a(ρ) - a(σ) = ∫_{B_ρ(ξ) \ B_σ(ξ)} w dμ_V`, then `a` is increasing on
`(0, R)`; for `0 < ρ < R`, `w` is `μ_V`-integrable on `B_ρ(ξ)` and
`(ωₙρⁿ)⁻¹ μ_V(B_ρ(ξ)) - Θⁿ(μ_V, ξ) = ωₙ⁻¹ ∫_{B_ρ(ξ)} w dμ_V`; if `R > 0` then `Θⁿ(μ_V, ξ)` exists
as a limit; and `Θⁿ(μ_V, ξ) ≤ (ωₙρⁿ)⁻¹ μ_V(B_ρ(ξ))` for `0 < ρ < R`. -/
theorem Submission.stationary_ratio_limit_of_annulus_identity : ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (ξ : Ambient n ℓ) (R : ℝ), (∀ σ ρ : ℝ, 0 < σ → σ ≤ ρ → ρ < R → IntegrableOn (fun x ↦ V.normalRadialSq ξ x / ‖x - ξ‖ ^ n) (closedBall ξ ρ \ closedBall ξ σ) V.weight ∧ V.weight.real (closedBall ξ ρ) / ρ ^ n - V.weight.real (closedBall ξ σ) / σ ^ n = ∫ x in closedBall ξ ρ \ closedBall ξ σ, V.normalRadialSq ξ x / ‖x - ξ‖ ^ n ∂V.weight) → MonotoneOn (fun ρ ↦ V.weight.real (closedBall ξ ρ) / ρ ^ n) (Ioo 0 R) ∧ (∀ ρ : ℝ, 0 < ρ → ρ < R → IntegrableOn (fun x ↦ V.normalRadialSq ξ x / ‖x - ξ‖ ^ n) (closedBall ξ ρ) V.weight ∧ V.weight.real (closedBall ξ ρ) / (omega n * ρ ^ n) - V.density ξ = (omega n)⁻¹ * ∫ x in closedBall ξ ρ, V.normalRadialSq ξ x / ‖x - ξ‖ ^ n ∂V.weight) ∧ (0 < R → V.HasDensityAt ξ (V.density ξ)) ∧ ∀ ρ : ℝ, 0 < ρ → ρ < R → V.density ξ ≤ V.weight.real (closedBall ξ ρ) / (omega n * ρ ^ n) := by
  intro n ℓ V ξ R hid
  set μ := V.weight
  set w : Ambient n ℓ → ℝ := fun x ↦ V.normalRadialSq ξ x / ‖x - ξ‖ ^ n with hw
  set a : ℝ → ℝ := fun ρ ↦ μ.real (closedBall ξ ρ) / ρ ^ n with ha
  -- Elementary facts: `w ≥ 0`, `w ξ = 0`, `a ≥ 0` on `(0, ∞)`, and the density quotient is
  -- `ωₙ⁻¹ a` with `ωₙ⁻¹ ≥ 0`.
  have hw0 : ∀ x, 0 ≤ w x := fun x ↦
    div_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _)) (pow_nonneg (norm_nonneg _) _)
  have hwξ : w ξ = 0 := by simp [hw, normalRadialSq]
  have ha0 : ∀ ρ, 0 < ρ → 0 ≤ a ρ := fun ρ hρ ↦
    div_nonneg measureReal_nonneg (pow_nonneg hρ.le _)
  have hQ : ∀ ρ, μ.real (closedBall ξ ρ) / (omega n * ρ ^ n) = (omega n)⁻¹ * a ρ := by
    intro ρ
    simp only [ha, div_eq_mul_inv, mul_inv]
    ring
  have hωinv : 0 ≤ (omega n)⁻¹ := inv_nonneg.2 ENNReal.toReal_nonneg
  -- 3.8: the annulus identity and `∫ w ≥ 0` make `a` monotone on `(0, R)`.
  have hmono : MonotoneOn a (Ioo 0 R) := by
    intro σ hσ ρ hρ hσρ
    have h := (hid σ ρ hσ.1 hσρ hρ.2).2
    have hnn : 0 ≤ ∫ x in closedBall ξ ρ \ closedBall ξ σ, w x ∂μ :=
      setIntegral_nonneg (measurableSet_closedBall.diff measurableSet_closedBall)
        fun x _ ↦ hw0 x
    change a ρ - a σ = _ at h
    linarith
  -- 3.9: `a` is bounded below by `0`, so `a ρ → L = inf a` as `ρ ↓ 0`, and the density
  -- quotient tends to `ωₙ⁻¹ L`, which is therefore `Θⁿ(μ_V, ξ)`.
  set L := sInf (a '' Ioo 0 R)
  have hbdd : BddBelow (a '' Ioo 0 R) := ⟨0, by
    rintro _ ⟨ρ, hρ, rfl⟩
    exact ha0 ρ hρ.1⟩
  have hLle : ∀ s ∈ Ioo 0 R, L ≤ a s := fun s hs ↦ csInf_le hbdd (mem_image_of_mem _ hs)
  have hlim : 0 < R → Tendsto a (𝓝[>] 0) (𝓝 L) ∧ V.density ξ = (omega n)⁻¹ * L ∧
      Tendsto (fun ρ ↦ μ.real (closedBall ξ ρ) / (omega n * ρ ^ n)) (𝓝[>] 0)
        (𝓝 ((omega n)⁻¹ * L)) := by
    intro hR
    have hT : Tendsto a (𝓝[>] 0) (𝓝 L) :=
      MonotoneOn.tendsto_nhdsWithin_Ioo_right ⟨R / 2, by positivity, by linarith⟩ hmono hbdd
    have hT' : Tendsto (fun ρ ↦ μ.real (closedBall ξ ρ) / (omega n * ρ ^ n)) (𝓝[>] 0)
        (𝓝 ((omega n)⁻¹ * L)) := by
      simp_rw [hQ]
      exact hT.const_mul _
    exact ⟨hT, hT'.limUnder_eq, hT'⟩
  refine ⟨hmono, ?_, ?_, ?_⟩
  · -- 3.10: monotone convergence on `A k = B_ρ(ξ) \ B_{ρ/(k+1)}(ξ)`, which increase to
    -- `B_ρ(ξ) \ {ξ}`; the point `ξ` contributes nothing since `w ξ = 0`.
    intro ρ hρ hρR
    obtain ⟨hT, hdens, -⟩ := hlim (hρ.trans hρR)
    set s : ℕ → ℝ := fun k ↦ ρ / (k + 1) with hs
    have hs0 : ∀ k, 0 < s k := fun k ↦ by positivity
    have hsρ : ∀ k, s k ≤ ρ := fun k ↦ div_le_self hρ.le (by norm_cast; omega)
    have hsanti : Antitone s := fun i j hij ↦ by
      simp only [hs]
      gcongr
    have hts : Tendsto s atTop (𝓝 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ρ
      rw [mul_zero] at this
      refine this.congr fun k ↦ ?_
      simp only [hs]
      ring
    have hsT : Tendsto s atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨hts, Eventually.of_forall hs0⟩
    set A : ℕ → Set (Ambient n ℓ) := fun k ↦ closedBall ξ ρ \ closedBall ξ (s k) with hA
    have hAmono : Monotone A := fun i j hij ↦
      sdiff_subset_sdiff_right (closedBall_subset_closedBall (hsanti hij))
    have hAmeas : ∀ k, MeasurableSet (A k) := fun k ↦
      measurableSet_closedBall.diff measurableSet_closedBall
    have hAint : ∀ k, IntegrableOn w (A k) μ := fun k ↦ (hid (s k) ρ (hs0 k) (hsρ k) hρR).1
    have hAeq : ∀ k, ∫ x in A k, w x ∂μ = a ρ - a (s k) := fun k ↦
      (hid (s k) ρ (hs0 k) (hsρ k) hρR).2.symm
    have hUnion : (⋃ k, A k) = closedBall ξ ρ \ {ξ} := by
      ext x
      simp only [hA, mem_iUnion, Set.mem_sdiff, mem_closedBall, mem_singleton_iff, not_le]
      constructor
      · rintro ⟨k, hxρ, hxk⟩
        refine ⟨hxρ, fun hx ↦ ?_⟩
        rw [hx, dist_self] at hxk
        exact lt_irrefl _ ((hs0 k).trans hxk)
      · rintro ⟨hxρ, hxξ⟩
        obtain ⟨k, hk⟩ := (hts.eventually (gt_mem_nhds (dist_pos.2 hxξ))).exists
        exact ⟨k, hxρ, hk⟩
    -- The lower integrals of `w` over the `A k` are at most `a ρ - L`, so `w` is integrable
    -- on their union.
    have hlin : ∀ k, ∫⁻ x in A k, ENNReal.ofReal (w x) ∂μ = ENNReal.ofReal (a ρ - a (s k)) := by
      intro k
      rw [← hAeq k, ofReal_integral_eq_lintegral_ofReal (hAint k)
        (Eventually.of_forall fun x ↦ hw0 x)]
    have hlinU : ∫⁻ x in ⋃ k, A k, ENNReal.ofReal (w x) ∂μ ≤ ENNReal.ofReal (a ρ - L) := by
      rw [setLIntegral_iUnion_of_directed _ hAmono.directed_le]
      refine iSup_le fun k ↦ ?_
      rw [hlin k]
      exact ENNReal.ofReal_le_ofReal (by linarith [hLle (s k) ⟨hs0 k, (hsρ k).trans_lt hρR⟩])
    have hintU : IntegrableOn w (⋃ k, A k) μ := by
      refine ⟨aestronglyMeasurable_iUnion_iff.2 fun k ↦ (hAint k).1, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x ↦ hw0 x)]
      exact hlinU.trans_lt ENNReal.ofReal_lt_top
    have hintξ : IntegrableOn w {ξ} μ :=
      (integrableOn_singleton_iff (hfx := enorm_ne_top)).2 (Or.inl (by rw [hwξ, enorm_zero]))
    have hball : closedBall ξ ρ = (⋃ k, A k) ∪ {ξ} := by
      rw [hUnion, sdiff_union_self, union_eq_left.2 (singleton_subset_iff.2
        (mem_closedBall_self hρ.le))]
    have hint : IntegrableOn w (closedBall ξ ρ) μ := by
      rw [hball]
      exact hintU.union hintξ
    -- The value: `∫_{A k} w = a ρ - a (s k) → a ρ - L`, and by dominated convergence it also
    -- tends to the integral over the union.
    have hvalU : ∫ x in ⋃ k, A k, w x ∂μ = a ρ - L := by
      refine tendsto_nhds_unique (tendsto_setIntegral_of_monotone hAmeas hAmono hintU) ?_
      simp_rw [hAeq]
      exact tendsto_const_nhds.sub (hT.comp hsT)
    have hvalξ : ∫ x in ({ξ} : Set (Ambient n ℓ)), w x ∂μ = 0 := by
      rw [setIntegral_congr_fun (measurableSet_singleton ξ) (g := fun _ ↦ (0 : ℝ))
        (fun x hx ↦ by rw [mem_singleton_iff.1 hx]; exact hwξ)]
      simp
    have hdisj : Disjoint (⋃ k, A k) {ξ} := by
      rw [hUnion]
      exact disjoint_sdiff_left
    have hval : ∫ x in closedBall ξ ρ, w x ∂μ = a ρ - L := by
      rw [hball, setIntegral_union hdisj (measurableSet_singleton ξ) hintU hintξ, hvalU, hvalξ,
        add_zero]
    refine ⟨hint, ?_⟩
    change μ.real (closedBall ξ ρ) / (omega n * ρ ^ n) - V.density ξ =
      (omega n)⁻¹ * ∫ x in closedBall ξ ρ, w x ∂μ
    rw [hQ, hdens, hval]
    ring
  · intro hR
    obtain ⟨-, hdens, hT'⟩ := hlim hR
    unfold HasDensityAt
    rw [hdens]
    exact hT'
  · -- The ratio bound: `ωₙ Θⁿ(μ_V, ξ) = L ≤ a ρ`.
    intro ρ hρ hρR
    obtain ⟨-, hdens, -⟩ := hlim (hρ.trans hρR)
    rw [hQ, hdens]
    exact mul_le_mul_of_nonneg_left (hLle ρ ⟨hρ, hρR⟩) hωinv
/-- **Upper semicontinuity of the density from the ratio bound (Simon 3.11).** Let `μ_V` be finite
on compact sets and `U` open. If `Θⁿ(μ_V, ξ)` exists at every `ξ ∈ U`, and
`Θⁿ(μ_V, η) ≤ μ_V(B_ρ(η))/(ωₙρⁿ)` whenever `B_R(η) ⊆ U` and `0 < ρ < R`, then `Θⁿ(μ_V, ·)` is
upper semicontinuous on `U`. -/
theorem Submission.stationary_density_usc_of_ratio_bound : ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)), IsOpen U → IsFiniteMeasureOnCompacts V.weight → (∀ ξ ∈ U, V.HasDensityAt ξ (V.density ξ)) → (∀ (η : Ambient n ℓ) (R ρ : ℝ), closedBall η R ⊆ U → 0 < ρ → ρ < R → V.density η ≤ V.weight.real (closedBall η ρ) / (omega n * ρ ^ n)) → UpperSemicontinuousOn V.density U := by
  intro n ℓ V U hU _ hdens hbound
  refine upperSemicontinuousOn_iff.2 fun ξ hξ ↦ upperSemicontinuousWithinAt_iff.2 fun t ht ↦ ?_
  -- Step 1: a radius `R > 0` with `B_{2R}(ξ) ⊆ U`, since `U` is open.
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU ξ hξ
  obtain ⟨R, hR0, hRε⟩ : ∃ R : ℝ, 0 < R ∧ 2 * R < ε := ⟨ε / 4, by positivity, by linarith⟩
  have h2R : closedBall ξ (2 * R) ⊆ U := (closedBall_subset_ball hRε).trans hεU
  -- Step 2: `ρ ∈ (0, R/2)` with `μ_V(B_ρ(ξ))/(ωₙρⁿ) < t`, as this quotient tends to `Θ(ξ) < t`.
  have hξd : Tendsto (fun r ↦ V.weight.real (closedBall ξ r) / (omega n * r ^ n)) (𝓝[>] 0)
      (𝓝 (V.density ξ)) := hdens ξ hξ
  obtain ⟨ρ, hρt, hρ0, hρR⟩ :=
    ((hξd.eventually (gt_mem_nhds ht)).and (Ioo_mem_nhdsGT (half_pos hR0))).exists
  -- Step 3: continuity from above, `μ_V(B_{ρ+δ}(ξ)) → μ_V(B_ρ(ξ))` as `δ ↓ 0` (`μ_V` is finite on
  -- the compact balls), gives `δ ∈ (0, R/2)` with `μ_V(B_{ρ+δ}(ξ))/(ωₙρⁿ) < t`.
  have hinter : ⋂ δ > (0 : ℝ), closedBall ξ (ρ + δ) = closedBall ξ ρ := by
    ext x
    simp only [mem_iInter, mem_closedBall]
    exact ⟨fun h ↦ le_of_forall_pos_le_add h, fun h δ hδ ↦ by linarith⟩
  have hcont : Tendsto (fun δ ↦ V.weight.real (closedBall ξ (ρ + δ)) / (omega n * ρ ^ n))
      (𝓝[>] 0) (𝓝 (V.weight.real (closedBall ξ ρ) / (omega n * ρ ^ n))) := by
    have h := tendsto_measure_biInter_gt (μ := V.weight) (s := fun δ : ℝ ↦ closedBall ξ (ρ + δ))
      (a := 0) (fun _ _ ↦ measurableSet_closedBall.nullMeasurableSet)
      (fun _ _ _ hij ↦ closedBall_subset_closedBall (by linarith))
      ⟨1, one_pos, measure_closedBall_lt_top.ne⟩
    rw [hinter] at h
    exact ((ENNReal.tendsto_toReal measure_closedBall_lt_top.ne).comp h).div_const _
  obtain ⟨δ, hδt, hδ0, hδR⟩ :=
    ((hcont.eventually (gt_mem_nhds hρt)).and (Ioo_mem_nhdsGT (half_pos hR0))).exists
  -- Step 4: for `|η - ξ| < δ`, `B_R(η) ⊆ B_{2R}(ξ) ⊆ U` and `B_ρ(η) ⊆ B_{ρ+δ}(ξ)`, hence
  -- `Θ(η) ≤ μ_V(B_ρ(η))/(ωₙρⁿ) ≤ μ_V(B_{ρ+δ}(ξ))/(ωₙρⁿ) < t`.
  have hω : 0 ≤ omega n * ρ ^ n := mul_nonneg ENNReal.toReal_nonneg (pow_nonneg hρ0.le n)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds ξ hδ0)] with η hη
  rw [mem_ball] at hη
  have hball : closedBall η R ⊆ U := (closedBall_subset_closedBall' (by linarith)).trans h2R
  have hsub : closedBall η ρ ⊆ closedBall ξ (ρ + δ) := closedBall_subset_closedBall' (by linarith)
  calc V.density η ≤ V.weight.real (closedBall η ρ) / (omega n * ρ ^ n) :=
        hbound η R ρ hball hρ0 (by linarith)
    _ ≤ V.weight.real (closedBall ξ (ρ + δ)) / (omega n * ρ ^ n) :=
        div_le_div_of_nonneg_right (measureReal_mono hsub measure_closedBall_lt_top.ne) hω
    _ < t := hδt
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
/-- **Ch. 4, p. 94 (the Hölder estimate between 4.2 and 4.3).** If `H ∈ Lᵖ(μ ⌞ B_R(ξ))` with
`p > n ≥ 1`, `μ` finite on compact sets and `0 < τ ≤ R`, then
`|τ^{-n-1} ∫_{B_τ(ξ)} (x - ξ) · H dμ| ≤
  (R^{p-n} ∫_{B_R(ξ)} |H|^p dμ)^{1/p} R⁻¹ (τ/R)^{-n/p} (1 + τ⁻ⁿ μ(B_τ(ξ)))`. -/
theorem Submission.mcm_lp_holder_bound : ∀ (n ℓ : ℕ) (μ : Measure (Ambient n ℓ)) (H : Ambient n ℓ → Ambient n ℓ) (p : ℝ) (ξ : Ambient n ℓ) (R τ : ℝ), 0 < n → IsFiniteMeasureOnCompacts μ → (n : ℝ) < p → MemLp H (ENNReal.ofReal p) (μ.restrict (closedBall ξ R)) → 0 < τ → τ ≤ R → |(∫ x in closedBall ξ τ, inner ℝ (x - ξ) (H x) ∂μ) / τ ^ (n + 1)| ≤ (R ^ (p - n) * ∫ x in closedBall ξ R, ‖H x‖ ^ p ∂μ) ^ (1 / p) / R * (τ / R) ^ (-(n : ℝ) / p) * (1 + μ.real (closedBall ξ τ) / τ ^ n) := by
  intro n ℓ μ H p ξ R τ hn hμ hp hH hτ hτR
  have hp1 : 1 < p := (show (1 : ℝ) ≤ n by exact_mod_cast hn).trans_lt hp
  have hp0 : 0 < p := zero_lt_one.trans hp1
  have hR : 0 < R := hτ.trans_le hτR
  have htn : 0 < τ ^ n := pow_pos hτ n
  -- Conjugate exponent `q`, `1 / q = 1 - 1 / p ∈ (0, 1)`.
  have hpq := Real.HolderConjugate.conjExponent hp1
  set q := p.conjExponent
  have hq : 1 / q = 1 - 1 / p := by
    have := hpq.inv_add_inv_eq_one
    rw [one_div, one_div]
    linarith
  have hsub : closedBall ξ τ ⊆ closedBall ξ R := closedBall_subset_closedBall hτR
  have : IsFiniteMeasure (μ.restrict (closedBall ξ τ)) :=
    isFiniteMeasure_restrict.2 (isCompact_closedBall ξ τ).measure_lt_top.ne
  have hHτ : MemLp H (ENNReal.ofReal p) (μ.restrict (closedBall ξ τ)) :=
    hH.mono_measure (Measure.restrict_mono hsub le_rfl)
  set I := ∫ x in closedBall ξ R, ‖H x‖ ^ p ∂μ
  set m := μ.real (closedBall ξ τ)
  have hI : 0 ≤ I := setIntegral_nonneg measurableSet_closedBall fun x _ ↦ by positivity
  have hm : 0 ≤ m := measureReal_nonneg
  -- `|∫_{B_τ} ⟨x - ξ, H⟩| ≤ τ ∫_{B_τ} |H|`, as `|x - ξ| ≤ τ` on `B_τ(ξ)`.
  have h3 : |∫ x in closedBall ξ τ, inner ℝ (x - ξ) (H x) ∂μ| ≤
      τ * ∫ x in closedBall ξ τ, ‖H x‖ ∂μ := by
    rw [← Real.norm_eq_abs, ← integral_const_mul]
    refine norm_integral_le_of_norm_le
      ((hHτ.integrable (ENNReal.one_le_ofReal.2 hp1.le)).norm.const_mul τ) ?_
    refine ae_restrict_of_forall_mem measurableSet_closedBall fun x hx ↦ ?_
    rw [mem_closedBall, dist_eq_norm] at hx
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
  -- Hölder with the constant `1` on `B_τ`, then `∫_{B_τ} |H|^p ≤ ∫_{B_R} |H|^p`.
  have h4 : ∫ x in closedBall ξ τ, ‖H x‖ ∂μ ≤ I ^ (1 / p) * m ^ (1 / q) := by
    have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ.restrict (closedBall ξ τ)) hpq
      (ae_of_all _ fun x ↦ norm_nonneg (H x)) (ae_of_all _ fun _ ↦ zero_le_one)
      hHτ.norm (memLp_const (1 : ℝ))
    simp only [mul_one, Real.one_rpow, integral_const, measureReal_restrict_apply_univ,
      smul_eq_mul] at hHolder
    refine hHolder.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hm _))
    refine Real.rpow_le_rpow
      (setIntegral_nonneg measurableSet_closedBall fun x _ ↦ by positivity) ?_ (by positivity)
    have hint := hH.integrable_norm_rpow (ENNReal.ofReal_pos.2 hp0).ne' ENNReal.ofReal_ne_top
    rw [ENNReal.toReal_ofReal hp0.le] at hint
    exact setIntegral_mono_set hint (ae_of_all _ fun x ↦ by positivity) (ae_of_all _ hsub)
  -- `m^{1-1/p} / τⁿ = a^{1-1/p} τ^{-n/p} ≤ (1 + a) τ^{-n/p}` with `a = m / τⁿ`.
  have h5 : m ^ (1 / q) / τ ^ n ≤ τ ^ (-(n : ℝ) / p) * (1 + m / τ ^ n) := by
    have ha : 0 ≤ m / τ ^ n := div_nonneg hm htn.le
    have hs : 0 ≤ 1 / q := by rw [hq, sub_nonneg]; exact (div_le_one hp0).2 hp1.le
    have has : (m / τ ^ n) ^ (1 / q) ≤ 1 + m / τ ^ n := by
      rcases le_total (m / τ ^ n) 1 with h | h
      · linarith [Real.rpow_le_one ha h hs]
      · have := Real.rpow_le_rpow_of_exponent_le h
          (show 1 / q ≤ 1 by rw [hq]; linarith [one_div_pos.2 hp0])
        rw [Real.rpow_one] at this
        linarith
    have heq : m ^ (1 / q) / τ ^ n = (m / τ ^ n) ^ (1 / q) * τ ^ (-(n : ℝ) / p) := by
      have hτq : (τ ^ n) ^ (1 / q) = τ ^ n * τ ^ (-(n : ℝ) / p) := by
        rw [← Real.rpow_natCast_mul hτ.le, hq, ← Real.rpow_natCast τ n, ← Real.rpow_add hτ]
        congr 1
        ring
      have hτp : τ ^ (-(n : ℝ) / p) ≠ 0 := (Real.rpow_pos_of_pos hτ _).ne'
      rw [Real.div_rpow hm htn.le, hτq]
      field_simp
    rw [heq, mul_comm]
    exact mul_le_mul_of_nonneg_left has (Real.rpow_nonneg hτ.le _)
  -- Simplify the right-hand side: `(R^{p-n} I)^{1/p} / R (τ/R)^{-n/p} = I^{1/p} τ^{-n/p}`.
  have h6 : (R ^ (p - n) * I) ^ (1 / p) / R * (τ / R) ^ (-(n : ℝ) / p) =
      I ^ (1 / p) * τ ^ (-(n : ℝ) / p) := by
    have hRn : R ^ (-(n : ℝ) / p) ≠ 0 := (Real.rpow_pos_of_pos hR _).ne'
    rw [Real.mul_rpow (Real.rpow_nonneg hR.le _) hI, ← Real.rpow_mul hR.le,
      show (p - n) * (1 / p) = 1 + -(n : ℝ) / p by field_simp; ring, Real.rpow_add hR,
      Real.rpow_one, Real.div_rpow hτ.le hR.le]
    field_simp
  rw [h6, abs_div, abs_of_pos (pow_pos hτ _), div_le_iff₀ (pow_pos hτ _)]
  calc |∫ x in closedBall ξ τ, inner ℝ (x - ξ) (H x) ∂μ|
      ≤ τ * (I ^ (1 / p) * m ^ (1 / q)) := h3.trans (mul_le_mul_of_nonneg_left h4 hτ.le)
    _ = I ^ (1 / p) * (m ^ (1 / q) / τ ^ n) * τ ^ (n + 1) := by
      rw [pow_succ]
      field_simp
    _ ≤ I ^ (1 / p) * (τ ^ (-(n : ℝ) / p) * (1 + m / τ ^ n)) * τ ^ (n + 1) := by
      gcongr
    _ = I ^ (1 / p) * τ ^ (-(n : ℝ) / p) * (1 + m / τ ^ n) * τ ^ (n + 1) := by ring

/-- **Simon 4.9 (p. 95) from 4.5 and 4.8.** Under (GF) (of which only the finiteness of `μ_V` on
compact sets is used), `LpMonotonicity` implies `LpDensity`. For `ξ ∈ U` pick `R > 0` with
`B_{2R}(ξ) ⊆ U`; the `Lᵖ` bound on the compact ball `B_{2R}(ξ)` gives one `Λ ≥ 0` for which 4.8
applies on `B_R(η)` for every `|η - ξ| < R`, and `F_η`, `E_η = F_η - 1` satisfy the hypothesis of
`mcm_density_usc_of_monotone` with `c(ρ) = e^{Λ/2} Λ (ρ/R)^{1-n/p} → 0`. -/
theorem Submission.mcm_lp_density_of_monotonicity : (∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ), 0 < n → IsFiniteMeasureOnCompacts V.weight ∧ (∀ᵐ x ∂V.weight, Module.finrank ℝ (V.tangentSpace x) = n) ∧ AEStronglyMeasurable (fun x ↦ (V.tangentSpace x).starProjection) V.weight) → LpMonotonicity → LpDensity := by
  intro hGF hMono n ℓ V U H p hn hU hH hp hLp
  -- `p > n ≥ 1`, so `p > 0`, `κ = (p - n)/(4p) > 0` and `θ = 1 - n/p > 0`.
  have hp0 : 0 < p := (Nat.cast_pos.2 hn).trans hp
  have hκ : 0 < lpKappa n p := div_pos (sub_pos.2 hp) (by positivity)
  have hθ : 0 < 1 - (n : ℝ) / p := sub_pos.2 ((div_lt_one hp0).2 hp)
  refine Submission.mcm_density_usc_of_monotone n ℓ V U (hGF n ℓ V hn).1 fun ξ hξ ↦ ?_
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU ξ hξ
  obtain ⟨R, hR, h2R⟩ : ∃ R : ℝ, 0 < R ∧ closedBall ξ (2 * R) ⊆ U :=
    ⟨ε / 3, by positivity, (closedBall_subset_ball (by linarith)).trans hεU⟩
  -- `|H|ᵖ` is integrable on the compact ball `B_{2R}(ξ) ⊆ U`.
  have hint : IntegrableOn (fun x ↦ ‖H x‖ ^ p) (closedBall ξ (2 * R)) V.weight := by
    have h := (hLp _ (isCompact_closedBall ξ (2 * R)) h2R).integrable_norm_rpow
      (ENNReal.ofReal_pos.2 hp0).ne' ENNReal.ofReal_ne_top
    rwa [ENNReal.toReal_ofReal hp0.le] at h
  have hI : ∀ s, 0 ≤ R ^ (p - n) * ∫ x in s, ‖H x‖ ^ p ∂V.weight := fun s ↦
    mul_nonneg (Real.rpow_nonneg hR.le _)
      (integral_nonneg fun x ↦ Real.rpow_nonneg (norm_nonneg _) _)
  -- `Λ = A₀/κ`, where `A₀ = (R^{p-n} ∫_{B_{2R}(ξ)} |H|ᵖ)^{1/p}`.
  obtain ⟨Λ, hΛ, hA⟩ : ∃ Λ : ℝ, 0 ≤ Λ ∧
      (R ^ (p - n) * ∫ x in closedBall ξ (2 * R), ‖H x‖ ^ p ∂V.weight) ^ (1 / p) ≤
        lpKappa n p * Λ :=
    ⟨_, div_nonneg (Real.rpow_nonneg (hI _) _) hκ.le, (mul_div_cancel₀ _ hκ.ne').ge⟩
  refine ⟨R, hR, fun ρ ↦ Real.exp (Λ / 2) * Λ * (ρ / R) ^ (1 - (n : ℝ) / p), ?_, fun η hη ↦ ?_⟩
  · -- `c(ρ) → c(0) = 0` as `ρ ↓ 0`, since `θ > 0`.
    have hc : ContinuousAt (fun ρ : ℝ ↦ Real.exp (Λ / 2) * Λ * (ρ / R) ^ (1 - (n : ℝ) / p)) 0 :=
      continuousAt_const.mul ((continuousAt_id.div_const R).rpow_const (Or.inr hθ.le))
    have h := hc.tendsto
    rw [zero_div, Real.zero_rpow hθ.ne', mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  -- `B_R(η) ⊆ B_{2R}(ξ)`, so `(R^{p-n} ∫_{B_R(η)} |H|ᵖ)^{1/p} ≤ A₀ ≤ κΛ` and 4.8 applies.
  have hsub : closedBall η R ⊆ closedBall ξ (2 * R) :=
    closedBall_subset_closedBall' (by linarith [mem_ball.1 hη])
  have hbound : (R ^ (p - n) * ∫ x in closedBall η R, ‖H x‖ ^ p ∂V.weight) ^ (1 / p) ≤
      lpKappa n p * Λ := by
    refine (Real.rpow_le_rpow (hI _) (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hR.le _))
      (one_div_pos.2 hp0).le).trans hA
    exact setIntegral_mono_set hint (ae_of_all _ fun x ↦ Real.rpow_nonneg (norm_nonneg _) _)
      (ae_of_all _ hsub)
  obtain ⟨F, _, hF, -, hFmono⟩ :=
    hMono n ℓ V U H p η R Λ hn hU hH hp hLp hR (hsub.trans h2R) hbound
  -- `E = F - 1`: the bounds of 4.5 on `(0, R)` are dominated by `c(ρ)`, as `e^{Λ/2} ≥ 1`.
  refine ⟨F, fun ρ ↦ F ρ - 1, fun ρ hρ ↦ ?_, hFmono.mono Ioo_subset_Ioc_self⟩
  obtain ⟨hF₁, hF₂, hF₃⟩ := hF ρ (Ioo_subset_Ioc_self hρ)
  have ht : 0 ≤ Λ * (ρ / R) ^ (1 - (n : ℝ) / p) :=
    mul_nonneg hΛ (Real.rpow_nonneg (div_nonneg hρ.1.le hR.le) _)
  have he : 1 ≤ Real.exp (Λ / 2) := Real.one_le_exp (by positivity)
  have h₁ : Λ / 2 * (ρ / R) ^ (1 - (n : ℝ) / p) ≤
      Real.exp (Λ / 2) * Λ * (ρ / R) ^ (1 - (n : ℝ) / p) := by nlinarith
  have h₂ : Real.exp (Λ / 2) / 2 * Λ * (ρ / R) ^ (1 - (n : ℝ) / p) ≤
      Real.exp (Λ / 2) * Λ * (ρ / R) ^ (1 - (n : ℝ) / p) := by nlinarith
  exact ⟨⟨(Real.exp_le_exp.2 (neg_le_neg h₁)).trans hF₁, hF₂.trans (Real.exp_le_exp.2 h₁)⟩,
    hF₃.trans h₂⟩

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
/-- **Ch. 4, 4.2–4.8 (pp. 93–94), `Lᵖ` monotonicity from the unit-weight identity.** Assume
(GF) (`μ_V` is finite on compact sets, with the a.e. tangent-plane facts) and (UI) (for
`0 < σ ≤ ρ`, `B_ρ(ξ) ⊆ U`, `e(τ) = τ^{-n-1} ∫_{B_τ(ξ)} (x - ξ) · H dμ_V` is integrable on `(σ, ρ]`,
`w = |D^⊥r|²/rⁿ` is integrable on `B_ρ(ξ) \ B_σ(ξ)`, and `a(ρ) - a(σ) = ∫_{B_ρ \ B_σ} w + ∫_σ^ρ e`
with `a(τ) = τ⁻ⁿ μ_V(B_τ(ξ))`). Then `LpMonotonicity` holds, with
`F(ρ) = exp(-∫_{(0,ρ]} e/(1 + a))` and `G(σ,ρ) = ∫_{B_ρ \ B_σ} F(r) w / ∫_{B_ρ \ B_σ} w`
(`G = 1` if the denominator vanishes). -/
theorem Submission.mcm_lp_monotonicity_of_identity : (∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ), 0 < n → IsFiniteMeasureOnCompacts V.weight ∧ (∀ᵐ x ∂V.weight, Module.finrank ℝ (V.tangentSpace x) = n) ∧ AEStronglyMeasurable (fun x ↦ (V.tangentSpace x).starProjection) V.weight) → (∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)) (H : Ambient n ℓ → Ambient n ℓ) (ξ : Ambient n ℓ) (σ ρ : ℝ), 0 < n → IsOpen U → V.HasMeanCurvatureIn U H → closedBall ξ ρ ⊆ U → 0 < σ → σ ≤ ρ → IntegrableOn (fun τ ↦ (∫ x in closedBall ξ τ, inner ℝ (x - ξ) (H x) ∂V.weight) / τ ^ (n + 1)) (Ioc σ ρ) ∧ IntegrableOn (fun x ↦ V.normalRadialSq ξ x / ‖x - ξ‖ ^ n) (closedBall ξ ρ \ closedBall ξ σ) V.weight ∧ V.weight.real (closedBall ξ ρ) / ρ ^ n - V.weight.real (closedBall ξ σ) / σ ^ n = ∫ x in closedBall ξ ρ \ closedBall ξ σ, V.normalRadialSq ξ x / ‖x - ξ‖ ^ n ∂V.weight + ∫ τ in Ioc σ ρ, (∫ x in closedBall ξ τ, inner ℝ (x - ξ) (H x) ∂V.weight) / τ ^ (n + 1)) → LpMonotonicity := by
  intro hGF hUI n ℓ V U H p ξ R Λ hn hU hH hnp hLp hR hball hA
  have hfin : IsFiniteMeasureOnCompacts V.weight := (hGF n ℓ V hn).1
  -- `a = a_ξ`, `e = e_ξ`, `w = w_ξ` as in (UI); `θ = 1 - n/p`.
  set a : ℝ → ℝ := fun τ ↦ V.weight.real (closedBall ξ τ) / τ ^ n
  set e : ℝ → ℝ := fun τ ↦
    (∫ x in closedBall ξ τ, inner ℝ (x - ξ) (H x) ∂V.weight) / τ ^ (n + 1)
  set w : Ambient n ℓ → ℝ := fun x ↦ V.normalRadialSq ξ x / ‖x - ξ‖ ^ n
  -- Step 1: `p > n ≥ 1`, `κ > 0`, `A ≥ 0`, hence `Λ ≥ 0`; `θ = 1 - n/p > 0`.
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 < p := by linarith
  have hκ : 0 < lpKappa n p := by
    unfold lpKappa
    exact div_pos (by linarith) (by linarith)
  have hA0 : 0 ≤ (R ^ (p - n) * ∫ x in closedBall ξ R, ‖H x‖ ^ p ∂V.weight) ^ (1 / p) :=
    Real.rpow_nonneg (mul_nonneg (Real.rpow_nonneg hR.le _)
      (integral_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _)) _
  have hΛ : 0 ≤ Λ := nonneg_of_mul_nonneg_right (hA0.trans hA) hκ
  have hθ : 0 < 1 - (n : ℝ) / p := by
    rw [sub_pos, div_lt_one hp]
    exact hnp
  -- Step 2 (4.2–4.3): HB and `A ≤ κΛ` give `|e τ| ≤ k τ (1 + a τ)` on `(0, R]`,
  -- with `k τ = (κΛ/R)(τ/R)^{-n/p}`.
  set k : ℝ → ℝ := fun τ ↦ lpKappa n p * Λ / R * (τ / R) ^ (-(n : ℝ) / p)
  have hmem : MemLp H (ENNReal.ofReal p) (V.weight.restrict (closedBall ξ R)) :=
    hLp _ (isCompact_closedBall ξ R) hball
  have ha0 : ∀ τ ∈ Ioc (0 : ℝ) R, 0 ≤ a τ := fun τ hτ ↦
    div_nonneg measureReal_nonneg (pow_nonneg hτ.1.le n)
  have he_le : ∀ τ ∈ Ioc (0 : ℝ) R, |e τ| ≤ k τ * (1 + a τ) := by
    intro τ hτ
    refine (Submission.mcm_lp_holder_bound n ℓ V.weight H p ξ R τ hn hfin hnp hmem hτ.1
      hτ.2).trans ?_
    have hc : 0 ≤ (τ / R) ^ (-(n : ℝ) / p) := Real.rpow_nonneg (div_nonneg hτ.1.le hR.le) _
    have h1a : 0 ≤ 1 + a τ := by linarith [ha0 τ hτ]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hA hR.le) hc) h1a
  -- Step 4a (4.5): `k` is integrable on `(0, R]` and `∫_{(0,ρ]} k = (Λ/4)(ρ/R)^θ`; this is where
  -- the corrected `κ = (p - n)/(4p)` enters, through `κ p/(p - n) = 1/4`.
  have hr : -1 < -(n : ℝ) / p := by
    rw [neg_div, neg_lt_neg_iff, div_lt_one hp]
    exact hnp
  have hk_pt : ∀ τ : ℝ, 0 ≤ τ →
      k τ = lpKappa n p * Λ / R * R ^ ((n : ℝ) / p) * τ ^ (-(n : ℝ) / p) := by
    intro τ hτ
    show lpKappa n p * Λ / R * (τ / R) ^ (-(n : ℝ) / p) = _
    rw [Real.div_rpow hτ hR.le, neg_div, Real.rpow_neg hR.le, div_inv_eq_mul]
    ring
  have hk_eqOn : ∀ ρ : ℝ, EqOn
      (fun τ ↦ lpKappa n p * Λ / R * R ^ ((n : ℝ) / p) * τ ^ (-(n : ℝ) / p)) k (Ioc 0 ρ) :=
    fun ρ τ hτ ↦ (hk_pt τ hτ.1.le).symm
  have hk_int : IntegrableOn k (Ioc 0 R) :=
    IntegrableOn.congr_fun (((intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le).1
      (intervalIntegral.intervalIntegrable_rpow' hr)).const_mul _) (hk_eqOn R) measurableSet_Ioc
  have hk_integral : ∀ ρ ∈ Ioc (0 : ℝ) R,
      ∫ τ in Ioc 0 ρ, k τ = Λ / 4 * (ρ / R) ^ (1 - (n : ℝ) / p) := by
    intro ρ hρ
    rw [← setIntegral_congr_fun measurableSet_Ioc (hk_eqOn ρ), integral_const_mul,
      ← intervalIntegral.integral_of_le hρ.1.le, integral_rpow (Or.inl hr),
      show -(n : ℝ) / p + 1 = 1 - (n : ℝ) / p by ring, Real.zero_rpow hθ.ne', sub_zero,
      Real.div_rpow hρ.1.le hR.le, Real.rpow_sub hR, Real.rpow_one]
    have hRn : 0 < R ^ ((n : ℝ) / p) := Real.rpow_pos_of_pos hR _
    have hpn : p - n ≠ 0 := sub_ne_zero.2 hnp.ne'
    have hθ' : 1 - (n : ℝ) / p = (p - n) / p := by field_simp
    generalize ρ ^ (1 - (n : ℝ) / p) = X
    rw [hθ']
    unfold lpKappa
    field_simp
  -- Steps 3, 4b: `F₀ = e/(1 + a)` satisfies `|F₀| ≤ k` on `(0, R]`, is integrable there (`e` is
  -- integrable on each `(R/(j+1), R]` by (UI), `a` is monotone hence measurable), and
  -- `∫_{(0,ρ]} |F₀| ≤ (Λ/4)(ρ/R)^θ`.
  set F₀ : ℝ → ℝ := fun τ ↦ e τ / (1 + a τ)
  have hF₀_le : ∀ τ ∈ Ioc (0 : ℝ) R, |F₀ τ| ≤ k τ := by
    intro τ hτ
    have h1 : 0 < 1 + a τ := by linarith [ha0 τ hτ]
    show |e τ / (1 + a τ)| ≤ k τ
    rw [abs_div, abs_of_pos h1, div_le_iff₀ h1]
    exact he_le τ hτ
  have hF₀_int : IntegrableOn F₀ (Ioc 0 R) := by
    have hcover : Ioc (0 : ℝ) R = ⋃ j : ℕ, Ioc (R / ((j : ℝ) + 1)) R := by
      ext τ
      simp only [mem_Ioc, mem_iUnion]
      constructor
      · rintro ⟨hτ0, hτR⟩
        obtain ⟨j, hj⟩ := exists_nat_gt (R / τ)
        refine ⟨j, ?_, hτR⟩
        rw [div_lt_iff₀ (by positivity)]
        rw [div_lt_iff₀ hτ0] at hj
        nlinarith
      · rintro ⟨j, hj, hτR⟩
        exact ⟨lt_trans (by positivity) hj, hτR⟩
    have he_meas : AEStronglyMeasurable e (volume.restrict (Ioc 0 R)) := by
      rw [hcover, aestronglyMeasurable_iUnion_iff]
      intro j
      have hj : (1 : ℝ) ≤ (j : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg j)
      exact (hUI n ℓ V U H ξ (R / ((j : ℝ) + 1)) R hn hU hH hball (by positivity)
        (div_le_self hR.le hj)).1.aestronglyMeasurable
    have hmono : Monotone fun τ : ℝ ↦ V.weight.real (closedBall ξ τ) := fun s t hst ↦
      measureReal_mono (closedBall_subset_closedBall hst) measure_closedBall_lt_top.ne
    have ha_meas : Measurable a := hmono.measurable.div (measurable_id.pow_const n)
    refine Integrable.mono' hk_int
      (he_meas.aemeasurable.div (measurable_const.add ha_meas).aemeasurable).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun τ hτ ↦ ?_))
    rw [Real.norm_eq_abs]
    exact hF₀_le τ hτ
  have hF₀_abs : ∀ ρ ∈ Ioc (0 : ℝ) R,
      ∫ τ in Ioc 0 ρ, |F₀ τ| ≤ Λ / 4 * (ρ / R) ^ (1 - (n : ℝ) / p) := by
    intro ρ hρ
    have hsub : Ioc (0 : ℝ) ρ ⊆ Ioc 0 R := Ioc_subset_Ioc_right hρ.2
    rw [← hk_integral ρ hρ]
    exact setIntegral_mono_on (hF₀_int.mono_set hsub).abs (hk_int.mono_set hsub)
      measurableSet_Ioc fun τ hτ ↦ hF₀_le τ (hsub hτ)
  -- Step 5 (4.5): `F(ρ) = exp(-∫_{(0,ρ]} F₀)`. With `s = -∫_{(0,ρ]} F₀`, `|s| ≤ (Λ/4)(ρ/R)^θ`,
  -- which gives the two exponential bounds, `|F - 1| ≤ e^{|s|}|s| ≤ (e^{Λ/2}/2)Λ(ρ/R)^θ`, and
  -- `e^{-Λ} ≤ F ≤ e^{Λ}` (as `(ρ/R)^θ ≤ 1`).
  set F : ℝ → ℝ := fun ρ ↦ Real.exp (-∫ τ in Ioc 0 ρ, F₀ τ)
  have hFb : ∀ ρ ∈ Ioc (0 : ℝ) R,
      Real.exp (-(Λ / 2 * (ρ / R) ^ (1 - (n : ℝ) / p))) ≤ F ρ ∧
      F ρ ≤ Real.exp (Λ / 2 * (ρ / R) ^ (1 - (n : ℝ) / p)) ∧
      |F ρ - 1| ≤ Real.exp (Λ / 2) / 2 * Λ * (ρ / R) ^ (1 - (n : ℝ) / p) ∧
      Real.exp (-Λ) ≤ F ρ ∧ F ρ ≤ Real.exp Λ := by
    intro ρ hρ
    have hq0 : 0 ≤ ρ / R := div_nonneg hρ.1.le hR.le
    have hc0 : 0 ≤ (ρ / R) ^ (1 - (n : ℝ) / p) := Real.rpow_nonneg hq0 _
    have hc1 : (ρ / R) ^ (1 - (n : ℝ) / p) ≤ 1 :=
      Real.rpow_le_one hq0 ((div_le_one hR).2 hρ.2) hθ.le
    have hs : |-∫ τ in Ioc 0 ρ, F₀ τ| ≤ Λ / 4 * (ρ / R) ^ (1 - (n : ℝ) / p) := by
      rw [abs_neg]
      exact abs_integral_le_integral_abs.trans (hF₀_abs ρ hρ)
    have hFρ : F ρ = Real.exp (-∫ τ in Ioc 0 ρ, F₀ τ) := rfl
    rw [hFρ]
    set s := -∫ τ in Ioc 0 ρ, F₀ τ
    set c := (ρ / R) ^ (1 - (n : ℝ) / p)
    have hΛc0 : 0 ≤ Λ * c := mul_nonneg hΛ hc0
    have hΛc : Λ * c ≤ Λ := mul_le_of_le_one_right hΛ hc1
    have habs : |s| ≤ Λ / 2 := by linarith
    -- `|e^s - 1| ≤ |s| e^{|s|}` (mean value theorem for `exp`).
    have hexp : |Real.exp s - 1| ≤ |s| * Real.exp |s| := by
      rcases le_or_gt 0 s with h | h
      · rw [abs_of_nonneg h, abs_of_nonneg (by linarith [Real.add_one_le_exp s])]
        have h1 := Real.add_one_le_exp (-s)
        have h2 : Real.exp (-s) * Real.exp s = 1 := by
          rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
        nlinarith [Real.exp_pos s]
      · rw [abs_of_neg h, abs_of_nonpos (by linarith [Real.exp_le_one_iff.mpr h.le])]
        have h1 := Real.add_one_le_exp s
        have h2 : 1 ≤ Real.exp (-s) := Real.one_le_exp (by linarith)
        nlinarith
    refine ⟨Real.exp_le_exp.mpr (by linarith [neg_abs_le s]),
      Real.exp_le_exp.mpr (by linarith [le_abs_self s]), ?_,
      Real.exp_le_exp.mpr (by linarith [neg_abs_le s]),
      Real.exp_le_exp.mpr (by linarith [le_abs_self s])⟩
    calc |Real.exp s - 1| ≤ |s| * Real.exp |s| := hexp
      _ ≤ Λ / 4 * c * Real.exp (Λ / 2) :=
        mul_le_mul hs (Real.exp_le_exp.mpr habs) (Real.exp_pos _).le (by positivity)
      _ ≤ Real.exp (Λ / 2) / 2 * Λ * c := by
        have := mul_nonneg hΛc0 (Real.exp_pos (Λ / 2)).le
        linarith
  -- Step 6: FTC for `F`, with `F' = -F₀ F` integrable on `(0, R]`.
  obtain ⟨hF'_int, hFTC⟩ := Submission.mcm_exp_neg_integral_ftc F₀ R hF₀_int
  set F' : ℝ → ℝ := fun τ ↦ -(F₀ τ * Real.exp (-∫ s in Ioc 0 τ, F₀ s))
  have hw0 : ∀ x, 0 ≤ w x := fun x ↦
    div_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _)) (pow_nonneg (norm_nonneg _) n)
  -- Step 7 (4.4, 4.7): IBP on the annulus; the remainder cancels, `F e + F' a = F₀ F = -F'`, so
  -- `(F a + F - 1)(ρ) - (F a + F - 1)(σ) = ∫_{B_ρ \ B_σ} F(|x - ξ|) w dμ_V`.
  have key : ∀ σ ρ : ℝ, 0 < σ → σ ≤ ρ → ρ ≤ R →
      IntegrableOn (fun x ↦ F ‖x - ξ‖ * w x) (closedBall ξ ρ \ closedBall ξ σ) V.weight ∧
      (F ρ * a ρ + (F ρ - 1)) - (F σ * a σ + (F σ - 1)) =
        ∫ x in closedBall ξ ρ \ closedBall ξ σ, F ‖x - ξ‖ * w x ∂V.weight := by
    intro σ ρ hσ hσρ hρR
    have hballρ : closedBall ξ ρ ⊆ U := (closedBall_subset_closedBall hρR).trans hball
    obtain ⟨heI, hwI, -⟩ := hUI n ℓ V U H ξ σ ρ hn hU hH hballρ hσ hσρ
    have hfam : ∀ s t : ℝ, σ ≤ s → s ≤ t → t ≤ ρ →
        a t - a s = ∫ x in closedBall ξ t \ closedBall ξ s, w x ∂V.weight +
          ∫ τ in Ioc s t, e τ := fun s t hs hst ht ↦
      (hUI n ℓ V U H ξ s t hn hU hH ((closedBall_subset_closedBall ht).trans hballρ)
        (hσ.trans_le hs) hst).2.2
    have hF'I : IntegrableOn F' (Ioc σ ρ) := hF'_int.mono_set (Ioc_subset_Ioc hσ.le hρR)
    have hFt : ∀ t ∈ Icc σ ρ, F t = F σ + ∫ τ in Ioc σ t, F' τ := fun t ht ↦
      hFTC σ t hσ.le ht.1 (ht.2.trans hρR)
    obtain ⟨hIint, hIBP⟩ := Submission.mcm_annulus_integration_by_parts n ℓ V.weight ξ w a e F
      F' σ ρ hfin hσ hσρ hw0 hwI heI hfam hF'I hFt
    refine ⟨hIint, ?_⟩
    have hcancel : ∫ τ in Ioc σ ρ, (F τ * e τ + F' τ * a τ) = ∫ τ in Ioc σ ρ, -F' τ := by
      refine setIntegral_congr_fun measurableSet_Ioc fun τ hτ ↦ ?_
      have h1 : 1 + a τ ≠ 0 := by linarith [ha0 τ ⟨hσ.trans hτ.1, hτ.2.trans hρR⟩]
      have he : e τ = F₀ τ * (1 + a τ) := (div_mul_cancel₀ (e τ) h1).symm
      show F τ * e τ + -(F₀ τ * F τ) * a τ = -(-(F₀ τ * F τ))
      rw [he]
      ring
    rw [hcancel, integral_neg] at hIBP
    have hρt := hFt ρ ⟨hσρ, le_rfl⟩
    linarith
  -- Step 8: `e^{-Λ} ≤ F(|x - ξ|) ≤ e^{Λ}` on the annulus, so `e^{-Λ} D ≤ I ≤ e^{Λ} D`, and
  -- `G = I/D` (`G = 1` if `D = 0`) lies in `[e^{-Λ}, e^{Λ}]` with `I = G D`.
  set D : ℝ → ℝ → ℝ := fun σ ρ ↦ ∫ x in closedBall ξ ρ \ closedBall ξ σ, w x ∂V.weight
  set I : ℝ → ℝ → ℝ := fun σ ρ ↦
    ∫ x in closedBall ξ ρ \ closedBall ξ σ, F ‖x - ξ‖ * w x ∂V.weight
  set G : ℝ → ℝ → ℝ := fun σ ρ ↦ if D σ ρ = 0 then 1 else I σ ρ / D σ ρ
  have hD0 : ∀ σ ρ : ℝ, 0 ≤ D σ ρ := fun σ ρ ↦
    setIntegral_nonneg (measurableSet_closedBall.diff measurableSet_closedBall) fun x _ ↦ hw0 x
  have hGI : ∀ σ ρ : ℝ, 0 < σ → σ ≤ ρ → ρ ≤ R →
      G σ ρ ∈ Icc (Real.exp (-Λ)) (Real.exp Λ) ∧ I σ ρ = G σ ρ * D σ ρ := by
    intro σ ρ hσ hσρ hρR
    have hS : MeasurableSet (closedBall ξ ρ \ closedBall ξ σ) :=
      measurableSet_closedBall.diff measurableSet_closedBall
    have hwI := (hUI n ℓ V U H ξ σ ρ hn hU hH ((closedBall_subset_closedBall hρR).trans hball)
      hσ hσρ).2.1
    have hIint := (key σ ρ hσ hσρ hρR).1
    have hFx : ∀ x ∈ closedBall ξ ρ \ closedBall ξ σ,
        Real.exp (-Λ) ≤ F ‖x - ξ‖ ∧ F ‖x - ξ‖ ≤ Real.exp Λ := by
      intro x hx
      have hx1 : ‖x - ξ‖ ≤ ρ := by
        have := hx.1
        rwa [mem_closedBall, dist_eq_norm] at this
      have hx2 : σ < ‖x - ξ‖ := by
        have := hx.2
        rwa [mem_closedBall, dist_eq_norm, not_le] at this
      obtain ⟨-, -, -, h4, h5⟩ := hFb ‖x - ξ‖ ⟨hσ.trans hx2, hx1.trans hρR⟩
      exact ⟨h4, h5⟩
    have hlow : Real.exp (-Λ) * D σ ρ ≤ I σ ρ := by
      show Real.exp (-Λ) * ∫ x in closedBall ξ ρ \ closedBall ξ σ, w x ∂V.weight ≤
        ∫ x in closedBall ξ ρ \ closedBall ξ σ, F ‖x - ξ‖ * w x ∂V.weight
      rw [← integral_const_mul]
      exact setIntegral_mono_on (hwI.const_mul _) hIint hS fun x hx ↦
        mul_le_mul_of_nonneg_right (hFx x hx).1 (hw0 x)
    have hup : I σ ρ ≤ Real.exp Λ * D σ ρ := by
      show ∫ x in closedBall ξ ρ \ closedBall ξ σ, F ‖x - ξ‖ * w x ∂V.weight ≤
        Real.exp Λ * ∫ x in closedBall ξ ρ \ closedBall ξ σ, w x ∂V.weight
      rw [← integral_const_mul]
      exact setIntegral_mono_on hIint (hwI.const_mul _) hS fun x hx ↦
        mul_le_mul_of_nonneg_right (hFx x hx).2 (hw0 x)
    by_cases hD : D σ ρ = 0
    · have hG1 : G σ ρ = 1 := ite_eq_left hD
      rw [hD, mul_zero] at hlow hup
      rw [hG1, hD, mul_zero]
      exact ⟨⟨Real.exp_le_one_iff.mpr (neg_nonpos.mpr hΛ), Real.one_le_exp hΛ⟩,
        le_antisymm hup hlow⟩
    · have hDpos : 0 < D σ ρ := lt_of_le_of_ne (hD0 σ ρ) (Ne.symm hD)
      have hGq : G σ ρ = I σ ρ / D σ ρ := ite_eq_right hD
      rw [hGq]
      exact ⟨⟨(le_div_iff₀ hDpos).2 hlow, (div_le_iff₀ hDpos).2 hup⟩,
        (div_mul_cancel₀ _ hD).symm⟩
  -- Step 9 (4.8): the increment is `G D ≥ 0`, so `F a + F - 1` is nondecreasing on `(0, R]`.
  refine ⟨F, G, fun ρ hρ ↦ ?_, fun σ ρ hσ hσρ hρR ↦ ?_, ?_⟩
  · obtain ⟨h1, h2, h3, -, -⟩ := hFb ρ hρ
    exact ⟨h1, h2, h3⟩
  · obtain ⟨hG, hIGD⟩ := hGI σ ρ hσ hσρ hρR
    exact ⟨hG, (key σ ρ hσ hσρ hρR).2.trans hIGD⟩
  · intro σ hσ ρ hρ hσρ
    obtain ⟨hG, hIGD⟩ := hGI σ ρ hσ.1 hσρ hρ.2
    have hdiff := (key σ ρ hσ.1 hσρ hρ.2).2.trans hIGD
    have hGD := mul_nonneg ((Real.exp_pos _).le.trans hG.1) (hD0 σ ρ)
    show F σ * a σ + (F σ - 1) ≤ F ρ * a ρ + (F ρ - 1)
    linarith
/-- **Smooth level truncation** (Simon Ch. 4, 5.7, proof, with a general cut-off `γ`). If
`∫_{g ≥ 1} g dμ_V ≤ C (∫ g dμ_V)^{1/n} ∫ (|∇^M g| + g|H|) dμ_V` for every nonnegative
`g ∈ C¹_c(U)`, then for `h ∈ C¹_c(U)`, `h ≥ 0`, and `t ≥ 0` the truncation `g = γ(h - t)` gives
`μ_V(h > t + ε) ≤ C μ_V(h > t)^{1/n} (∫ γ'(h - t)|∇^M h| dμ_V + ∫_{h > t} |H| dμ_V)`:
`g = 1` on `{h > t + ε}`, `0 ≤ g ≤ 1_{h > t}`, and `∇^M g = γ'(h - t) ∇^M h` with `γ' ≥ 0`. -/
theorem Submission.sobolev_truncation_superlevel_bound : ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)) (H : Ambient n ℓ → Ambient n ℓ) (h : Ambient n ℓ → ℝ) (γ : ℝ → ℝ) (C ε t : ℝ), IsFiniteMeasureOnCompacts V.weight → LocallyIntegrableOn H U V.weight → 0 ≤ C → (∀ g : Ambient n ℓ → ℝ, ContDiffOn ℝ 1 g U → HasCompactSupport g → tsupport g ⊆ U → (∀ x, 0 ≤ g x) → ∫ x in {x | 1 ≤ g x}, g x ∂V.weight ≤ C * (∫ x, g x ∂V.weight) ^ (n : ℝ)⁻¹ * ∫ x, (‖V.tangentialGradient g x‖ + g x * ‖H x‖) ∂V.weight) → ContDiff ℝ 1 h → HasCompactSupport h → tsupport h ⊆ U → (∀ x, 0 ≤ h x) → Integrable (fun x ↦ ‖V.tangentialGradient h x‖) V.weight → ContDiff ℝ 1 γ → Monotone γ → (∀ s, 0 ≤ γ s ∧ γ s ≤ 1) → (∀ s, s ≤ 0 → γ s = 0) → 0 < ε → (∀ s, ε ≤ s → γ s = 1) → 0 ≤ t → V.weight.real {x | t + ε < h x} ≤ C * (V.weight.real {x | t < h x}) ^ (n : ℝ)⁻¹ * ((∫ x, deriv γ (h x - t) * ‖V.tangentialGradient h x‖ ∂V.weight) + ∫ x in {x | t < h x}, ‖H x‖ ∂V.weight) := by
  intro n ℓ V U H h γ C ε t hfin hHloc hC hS hh hhc hhU hh0 hgrad hγ hγm hγ01 hγ0 hε hγ1 ht
  have hhd : Differentiable ℝ h := hh.differentiable one_ne_zero
  have hγd : Differentiable ℝ γ := hγ.differentiable one_ne_zero
  have hγ' : Continuous (deriv γ) := hγ.continuous_deriv le_rfl
  have hγ'0 : ∀ s, 0 ≤ deriv γ s := fun s ↦ hγm.deriv_nonneg
  have hgc : Continuous fun x ↦ γ (h x - t) :=
    hγ.continuous.comp (hh.continuous.sub continuous_const)
  -- the superlevel sets `M_s = {h > s}` are open, and for `s ≥ 0` lie in the compact `tsupport h`
  have hMmeas : ∀ s, MeasurableSet {x | s < h x} := fun s ↦
    (isOpen_lt continuous_const hh.continuous).measurableSet
  have hMsub : ∀ s, 0 ≤ s → {x | s < h x} ⊆ tsupport h := fun s hs x hx ↦
    subset_tsupport _ (hs.trans_lt hx).ne'
  have hMfin : ∀ s, 0 ≤ s → V.weight {x | s < h x} ≠ ⊤ := fun s hs ↦
    ((measure_mono (hMsub s hs)).trans_lt hhc.isCompact.measure_lt_top).ne
  -- the truncation `g = γ(h - t)` vanishes off `M_t`, so it is admissible in the hypothesis
  have hg0 : ∀ x, ¬ t < h x → γ (h x - t) = 0 := fun x hx ↦ hγ0 _ (by linarith [not_lt.mp hx])
  have hgsupp : Function.support (fun x ↦ γ (h x - t)) ⊆ Function.support h := fun x hx hx0 ↦
    hx (hγ0 _ (by rw [hx0]; linarith))
  have hgcs : HasCompactSupport fun x ↦ γ (h x - t) := hhc.mono hgsupp
  have hgU : tsupport (fun x ↦ γ (h x - t)) ⊆ U := (closure_mono hgsupp).trans hhU
  have hgint : Integrable (fun x ↦ γ (h x - t)) V.weight :=
    hgc.integrable_of_hasCompactSupport hgcs
  have A1 := hS (fun x ↦ γ (h x - t)) (hγ.comp (hh.sub contDiff_const)).contDiffOn hgcs hgU
    (fun x ↦ (hγ01 _).1)
  -- chain rule: `∇^M g = γ'(h - t) ∇^M h`
  have hchain : ∀ x, V.tangentialGradient (fun y ↦ γ (h y - t)) x =
      deriv γ (h x - t) • V.tangentialGradient h x := by
    intro x
    have hcomp : fderiv ℝ (fun y ↦ γ (h y - t)) x = deriv γ (h x - t) • fderiv ℝ h x :=
      ((hγd _).hasDerivAt.comp_hasFDerivAt x ((hhd x).hasFDerivAt.sub_const t)).fderiv
    simp only [RectifiableVarifold.tangentialGradient, gradient, hcomp, map_smul]
  -- left side: `μ(M_{t+ε}) = ∫_{M_{t+ε}} g ≤ ∫_{g ≥ 1} g`
  have hLHS : V.weight.real {x | t + ε < h x} ≤
      ∫ x in {x | 1 ≤ γ (h x - t)}, γ (h x - t) ∂V.weight := by
    calc V.weight.real {x | t + ε < h x} = ∫ x in {x | t + ε < h x}, γ (h x - t) ∂V.weight := by
          rw [setIntegral_congr_fun (hMmeas (t + ε))
            (fun x (hx : t + ε < h x) ↦ hγ1 _ (by linarith) :
              EqOn (fun x ↦ γ (h x - t)) (fun _ ↦ (1 : ℝ)) _), setIntegral_const, smul_eq_mul,
            mul_one]
      _ ≤ ∫ x in {x | 1 ≤ γ (h x - t)}, γ (h x - t) ∂V.weight :=
          setIntegral_mono_set hgint.integrableOn (Eventually.of_forall fun x ↦ (hγ01 _).1)
            (EventuallySubset.of_subset fun x (hx : t + ε < h x) ↦ (hγ1 _ (by linarith)).ge)
  -- mass factor: `0 ≤ g ≤ 1_{M_t}`
  have hmass : ∫ x, γ (h x - t) ∂V.weight ≤ V.weight.real {x | t < h x} := by
    rw [← integral_indicator_one (hMmeas t)]
    refine integral_mono hgint ((integrableOn_const (hMfin t ht)).integrable_indicator (hMmeas t))
      fun x ↦ ?_
    by_cases hx : t < h x
    · rw [Set.indicator_of_mem (show x ∈ {x | t < h x} from hx)]
      exact (hγ01 _).2
    · rw [Set.indicator_of_notMem (show x ∉ {x | t < h x} from hx), hg0 x hx]
  have hmass' : (∫ x, γ (h x - t) ∂V.weight) ^ (n : ℝ)⁻¹ ≤
      (V.weight.real {x | t < h x}) ^ (n : ℝ)⁻¹ :=
    Real.rpow_le_rpow (integral_nonneg fun x ↦ (hγ01 _).1) hmass (inv_nonneg.mpr n.cast_nonneg)
  -- energy factor: integrable majorant `γ'(h - t)|∇^M h| + 1_{M_t}|H|` (`γ'` is bounded on the
  -- range of `h - t`, and `H` is integrable on the compact `tsupport h ⊆ U`)
  have hPint : Integrable (fun x ↦ deriv γ (h x - t) * ‖V.tangentialGradient h x‖) V.weight := by
    obtain ⟨m, hm⟩ := hh.continuous.bounded_above_of_compact_support hhc
    obtain ⟨L, hL⟩ := (isCompact_Icc (a := -t) (b := m - t)).exists_bound_of_continuousOn
      hγ'.continuousOn
    refine hgrad.bdd_mul (c := L)
      (hγ'.comp (hh.continuous.sub continuous_const)).aestronglyMeasurable
      (Eventually.of_forall fun x ↦ hL _ ⟨?_, ?_⟩)
    · linarith [hh0 x]
    · have := hm x
      rw [Real.norm_eq_abs] at this
      linarith [le_abs_self (h x)]
  have hRint : Integrable (Set.indicator {x | t < h x} fun x ↦ ‖H x‖) V.weight :=
    (IntegrableOn.mono_set (Integrable.norm (hHloc.integrableOn_compact_subset hhU hhc.isCompact))
      (hMsub t ht)).integrable_indicator (hMmeas t)
  have hI : ∫ x, (‖V.tangentialGradient (fun y ↦ γ (h y - t)) x‖ + γ (h x - t) * ‖H x‖)
      ∂V.weight ≤ (∫ x, deriv γ (h x - t) * ‖V.tangentialGradient h x‖ ∂V.weight) +
        ∫ x in {x | t < h x}, ‖H x‖ ∂V.weight := by
    rw [← integral_indicator (hMmeas t), ← integral_add hPint hRint]
    refine integral_mono_of_nonneg (Eventually.of_forall fun x ↦ ?_) (hPint.add hRint)
      (Eventually.of_forall fun x ↦ ?_)
    · exact add_nonneg (norm_nonneg _) (mul_nonneg (hγ01 _).1 (norm_nonneg _))
    · dsimp only
      rw [hchain x, norm_smul, Real.norm_of_nonneg (hγ'0 _)]
      refine add_le_add le_rfl ?_
      by_cases hx : t < h x
      · rw [Set.indicator_of_mem (show x ∈ {x | t < h x} from hx)]
        exact mul_le_of_le_one_left (norm_nonneg _) (hγ01 _).2
      · rw [Set.indicator_of_notMem (show x ∉ {x | t < h x} from hx), hg0 x hx, zero_mul]
  have hI0 : 0 ≤ ∫ x, (‖V.tangentialGradient (fun y ↦ γ (h y - t)) x‖ + γ (h x - t) * ‖H x‖)
      ∂V.weight :=
    integral_nonneg fun x ↦ add_nonneg (norm_nonneg _) (mul_nonneg (hγ01 _).1 (norm_nonneg _))
  calc V.weight.real {x | t + ε < h x}
      ≤ ∫ x in {x | 1 ≤ γ (h x - t)}, γ (h x - t) ∂V.weight := hLHS
    _ ≤ C * (∫ x, γ (h x - t) ∂V.weight) ^ (n : ℝ)⁻¹ *
          ∫ x, (‖V.tangentialGradient (fun y ↦ γ (h y - t)) x‖ + γ (h x - t) * ‖H x‖) ∂V.weight :=
        A1
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hmass' hC) hI hI0
          (mul_nonneg hC (Real.rpow_nonneg measureReal_nonneg _))
/-- **Level-set moment factor (Simon Ch. 4, proof of 5.7, p. 100).** The "trivial inequality"
of Simon's proof, with `M_α = {x : h(x) > α}` and `p = n/(n-1)`: if `n ≥ 2`, `μ` is finite on
compact sets, `h ≥ 0` is continuous with compact support, `ε > 0` and `t ≥ 0`, then
`(t + ε)^{1/(n-1)} μ(M_t)^{1/n} ≤ (∫_{M_0} (h + ε)^p dμ)^{1/n}`. -/
theorem Submission.sobolev_level_moment_factor : ∀ (n ℓ : ℕ) (μ : Measure (Ambient n ℓ)) (h : Ambient n ℓ → ℝ) (ε t : ℝ), 2 ≤ n → IsFiniteMeasureOnCompacts μ → Continuous h → HasCompactSupport h → (∀ x, 0 ≤ h x) → 0 < ε → 0 ≤ t → (t + ε) ^ ((n : ℝ) - 1)⁻¹ * (μ.real {x | t < h x}) ^ (n : ℝ)⁻¹ ≤ (∫ x in {x | 0 < h x}, (h x + ε) ^ ((n : ℝ) / ((n : ℝ) - 1)) ∂μ) ^ (n : ℝ)⁻¹ := by
  intro n ℓ μ h ε t hn hμ hh hhc hh0 hε ht
  -- (1) Exponents: `p = n/(n-1) ≥ 0`, `p · (1/n) = 1/(n-1)`, and `t + ε ≥ 0`.
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : (0 : ℝ) < n - 1 := by linarith
  set p : ℝ := (n : ℝ) / ((n : ℝ) - 1) with hp_def
  have hp : 0 ≤ p := div_nonneg hn0.le hn1.le
  have hpn : p * (n : ℝ)⁻¹ = ((n : ℝ) - 1)⁻¹ := by
    rw [hp_def, div_mul_eq_mul_div, mul_inv_cancel₀ hn0.ne', one_div]
  have hte : 0 ≤ t + ε := by linarith
  -- (2) Sets: `M_t ⊆ M_0 ⊆ tsupport h` (compact), so `μ(M_t) < ∞`; `M_t` is open.
  have hMt : MeasurableSet {x | t < h x} := (isOpen_lt continuous_const hh).measurableSet
  have hsub : {x | t < h x} ⊆ {x | 0 < h x} := fun x (hx : t < h x) ↦ ht.trans_lt hx
  have hsubK : {x | 0 < h x} ⊆ tsupport h := fun x (hx : 0 < h x) ↦ subset_tsupport h hx.ne'
  have hK : IsCompact (tsupport h) := hhc.isCompact
  have hMt_fin : μ {x | t < h x} ≠ ⊤ :=
    ((measure_mono (hsub.trans hsubK)).trans_lt hK.measure_lt_top).ne
  -- (3) The continuous `(h + ε)^p` is integrable on `tsupport h`, hence on `M_0`.
  have hcont : Continuous fun x ↦ (h x + ε) ^ p :=
    (hh.add continuous_const).rpow_const fun _ ↦ Or.inr hp
  have hint0 : IntegrableOn (fun x ↦ (h x + ε) ^ p) {x | 0 < h x} μ :=
    (hcont.continuousOn.integrableOn_compact hK).mono_set hsubK
  -- (4) `(t + ε)^p μ(M_t) = ∫_{M_t} (t + ε)^p ≤ ∫_{M_t} (h + ε)^p ≤ ∫_{M_0} (h + ε)^p`.
  have hmom : (t + ε) ^ p * μ.real {x | t < h x} ≤ ∫ x in {x | 0 < h x}, (h x + ε) ^ p ∂μ := by
    calc (t + ε) ^ p * μ.real {x | t < h x} = ∫ _ in {x | t < h x}, (t + ε) ^ p ∂μ := by
          rw [setIntegral_const, smul_eq_mul, mul_comm]
      _ ≤ ∫ x in {x | t < h x}, (h x + ε) ^ p ∂μ :=
          setIntegral_mono_on (integrableOn_const hMt_fin) (hint0.mono_set hsub) hMt
            fun x (hx : t < h x) ↦ Real.rpow_le_rpow hte (by linarith) hp
      _ ≤ ∫ x in {x | 0 < h x}, (h x + ε) ^ p ∂μ :=
          setIntegral_mono_set hint0
            (ae_of_all _ fun x ↦ Real.rpow_nonneg (by linarith [hh0 x]) p)
            (Eventually.of_forall hsub)
  -- (5) `n`-th roots: `((t + ε)^p μ(M_t))^{1/n} = (t + ε)^{1/(n-1)} μ(M_t)^{1/n}`.
  calc (t + ε) ^ ((n : ℝ) - 1)⁻¹ * (μ.real {x | t < h x}) ^ (n : ℝ)⁻¹
      = ((t + ε) ^ p * μ.real {x | t < h x}) ^ (n : ℝ)⁻¹ := by
        rw [Real.mul_rpow (Real.rpow_nonneg hte p) measureReal_nonneg, ← Real.rpow_mul hte, hpn]
    _ ≤ (∫ x in {x | 0 < h x}, (h x + ε) ^ p ∂μ) ^ (n : ℝ)⁻¹ :=
        Real.rpow_le_rpow (mul_nonneg (Real.rpow_nonneg hte p) measureReal_nonneg) hmom
          (inv_nonneg.2 hn0.le)
/-- **Integrated truncation energy over the levels `t ∈ (0, ∞)`** (Simon Ch. 4, proof of 5.7,
p. 100: "Now integrate over `t ∈ (0, ∞)`"). Let `μ` be finite on compacts, `h ≥ 0` continuous with
compact support, `D ≥ 0` integrable, `K ≥ 0` integrable on `tsupport h`, and `γ` a nondecreasing
`C¹` function with `0 ≤ γ ≤ 1` and `γ = 0` on `(-∞, 0]`. With `K' = 1_{tsupport h} K`, Tonelli
turns the left side into `∫ (∫_0^∞ γ'(h - t) dt) D dμ + ∫ (∫_0^∞ 1_{t < h} dt) K' dμ`
`= ∫ γ(h) D dμ + ∫ h K' dμ ≤ ∫ (D + h K) dμ`. -/
theorem Submission.sobolev_level_energy_tonelli : ∀ (n ℓ : ℕ) (μ : Measure (Ambient n ℓ)) (h D K : Ambient n ℓ → ℝ) (γ : ℝ → ℝ), IsFiniteMeasureOnCompacts μ → Continuous h → HasCompactSupport h → (∀ x, 0 ≤ h x) → (∀ x, 0 ≤ D x) → Integrable D μ → (∀ x, 0 ≤ K x) → IntegrableOn K (tsupport h) μ → ContDiff ℝ 1 γ → Monotone γ → (∀ s, 0 ≤ γ s ∧ γ s ≤ 1) → (∀ s, s ≤ 0 → γ s = 0) → ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal ((∫ x, deriv γ (h x - t) * D x ∂μ) + ∫ x in {x | t < h x}, K x ∂μ) ≤ ENNReal.ofReal (∫ x, (D x + h x * K x) ∂μ) := by
  intro n ℓ μ h D K γ hμ hhc hhcs hh0 hD0 hDi hK0 hKi hγ hγm hγb hγ0
  -- `K₀ = tsupport h` is closed, hence measurable; `h = 0` off `K₀`; `M_t ⊆ K₀` for `t ≥ 0`
  have hK₀m : MeasurableSet (tsupport h) := (isClosed_tsupport h).measurableSet
  have hoff : ∀ x, x ∉ tsupport h → h x = 0 := fun x hx ↦ image_eq_zero_of_notMem_tsupport hx
  have hMsub : ∀ t : ℝ, 0 ≤ t → {x | t < h x} ⊆ tsupport h := fun t ht x hx ↦
    subset_tsupport h (ne_of_gt (lt_of_le_of_lt ht hx))
  have hMm : ∀ t : ℝ, MeasurableSet {x | t < h x} := fun t ↦
    measurableSet_lt measurable_const hhc.measurable
  -- the truncation `K' = 1_{K₀} K` is integrable, nonnegative, and `h K' = h K`
  set K' : Ambient n ℓ → ℝ := (tsupport h).indicator K with hK'eq
  have hK'i : Integrable K' μ := (integrable_indicator_iff hK₀m).2 hKi
  have hK'0 : ∀ x, 0 ≤ K' x := fun x ↦ Set.indicator_nonneg (fun y _ ↦ hK0 y) x
  have hhK' : ∀ x, h x * K' x = h x * K x := by
    intro x
    by_cases hx : x ∈ tsupport h
    · rw [hK'eq, Set.indicator_of_mem hx]
    · rw [hoff x hx, zero_mul, zero_mul]
  -- `γ'` is continuous, nonnegative, and vanishes on `(-∞, 0)`
  have hγ'c : Continuous (deriv γ) := hγ.continuous_deriv le_rfl
  have hγ'0 : ∀ s, 0 ≤ deriv γ s := fun s ↦ hγm.deriv_nonneg
  have hγ'neg : ∀ s, s < 0 → deriv γ s = 0 := by
    intro s hs
    have : γ =ᶠ[𝓝 s] fun _ ↦ (0 : ℝ) :=
      (eventually_lt_nhds hs).mono fun y hy ↦ hγ0 y hy.le
    rw [this.deriv_eq, deriv_const]
  -- (B1) `∫⁻_{(0,∞)} γ'(a - t) dt = γ(a) ≤ 1` for `a ≥ 0`
  have hB1 : ∀ a : ℝ, 0 ≤ a → ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (deriv γ (a - t)) ≤ 1 := by
    intro a ha
    rw [← Ioc_union_Ioi_eq_Ioi ha, lintegral_union measurableSet_Ioi (Ioc_disjoint_Ioi le_rfl)]
    have h2 : ∫⁻ t in Ioi a, ENNReal.ofReal (deriv γ (a - t)) = 0 := by
      refine (setLIntegral_eq_zero_iff' measurableSet_Ioi ?_).2 ?_
      · exact (ENNReal.measurable_ofReal.comp ((measurable_deriv γ).comp
          (measurable_const.sub measurable_id))).aemeasurable
      · refine Eventually.of_forall fun t ht ↦ ?_
        rw [hγ'neg _ (sub_neg.2 ht), ENNReal.ofReal_zero]
    rw [h2, add_zero]
    have hint : IntegrableOn (fun t ↦ deriv γ (a - t)) (Ioc 0 a) :=
      ((hγ'c.comp (continuous_const.sub continuous_id)).integrableOn_Icc).mono_set
        Ioc_subset_Icc_self
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun t ↦ hγ'0 _),
      ← intervalIntegral.integral_of_le ha, intervalIntegral.integral_comp_sub_left,
      intervalIntegral.integral_deriv_eq_sub (fun x _ ↦ (hγ.differentiable one_ne_zero) x)
        (hγ'c.intervalIntegrable _ _), sub_self, sub_zero, hγ0 0 le_rfl, sub_zero]
    exact ENNReal.ofReal_le_one.2 (hγb a).2
  -- (B2) `∫⁻_{(0,∞)} 1_{t < a} dt = a`
  have hB2 : ∀ a : ℝ, ∫⁻ t in Ioi (0 : ℝ), (Iio a).indicator 1 t = ENNReal.ofReal a := by
    intro a
    rw [lintegral_indicator_one measurableSet_Iio, Measure.restrict_apply measurableSet_Iio,
      Iio_inter_Ioi, Real.volume_Ioo, sub_zero]
  -- the integrand `F` on `(0, ∞) × E`
  set S : Set (ℝ × Ambient n ℓ) := {p | p.1 < h p.2} with hSdef
  have hSm : MeasurableSet S := measurableSet_lt measurable_fst (hhc.measurable.comp measurable_snd)
  have hSx : ∀ t x, S.indicator (1 : ℝ × Ambient n ℓ → ℝ≥0∞) (t, x) =
      (Iio (h x)).indicator 1 t := by
    intro t x
    by_cases htx : t < h x
    · rw [Set.indicator_of_mem (show (t, x) ∈ S from htx),
        Set.indicator_of_mem (show t ∈ Iio (h x) from htx)]
      rfl
    · rw [Set.indicator_of_notMem (show (t, x) ∉ S from htx),
        Set.indicator_of_notMem (show t ∉ Iio (h x) from htx)]
  let F : ℝ → Ambient n ℓ → ℝ≥0∞ := fun t x ↦
    ENNReal.ofReal (deriv γ (h x - t)) * ENNReal.ofReal (D x) +
      ENNReal.ofReal (K' x) * S.indicator 1 (t, x)
  have hFm : AEMeasurable (Function.uncurry F) ((volume.restrict (Ioi (0 : ℝ))).prod μ) := by
    have h1 : Measurable fun p : ℝ × Ambient n ℓ ↦ ENNReal.ofReal (deriv γ (h p.2 - p.1)) :=
      (hγ'c.measurable.comp
        ((hhc.measurable.comp measurable_snd).sub measurable_fst)).ennreal_ofReal
    have h2 : AEMeasurable (fun p : ℝ × Ambient n ℓ ↦ ENNReal.ofReal (D p.2))
        ((volume.restrict (Ioi (0 : ℝ))).prod μ) :=
      hDi.aemeasurable.ennreal_ofReal.comp_snd
    have h3 : AEMeasurable (fun p : ℝ × Ambient n ℓ ↦ ENNReal.ofReal (K' p.2))
        ((volume.restrict (Ioi (0 : ℝ))).prod μ) :=
      hK'i.aemeasurable.ennreal_ofReal.comp_snd
    have h4 : Measurable (S.indicator (1 : ℝ × Ambient n ℓ → ℝ≥0∞)) :=
      measurable_one.indicator hSm
    exact (h1.aemeasurable.mul h2).add (h3.mul h4.aemeasurable)
  -- one level `t > 0`: `ofReal (P(t) + R(t)) = ∫⁻ F(t, x) dμ`
  have hlevel : ∀ t ∈ Ioi (0 : ℝ), ENNReal.ofReal ((∫ x, deriv γ (h x - t) * D x ∂μ) +
      ∫ x in {x | t < h x}, K x ∂μ) = ∫⁻ x, F t x ∂μ := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have hgc : Continuous fun x ↦ deriv γ (h x - t) := hγ'c.comp (hhc.sub continuous_const)
    have hgs : HasCompactSupport fun x ↦ deriv γ (h x - t) := by
      refine hhcs.comp_left (g := fun s ↦ deriv γ (s - t)) ?_
      show deriv γ (0 - t) = 0
      rw [zero_sub]
      exact hγ'neg _ (neg_lt_zero.2 ht0)
    obtain ⟨c, hc⟩ := hgc.bounded_above_of_compact_support hgs
    have hPi : Integrable (fun x ↦ deriv γ (h x - t) * D x) μ :=
      hDi.bdd_mul hgc.aestronglyMeasurable (Eventually.of_forall hc)
    have hP0 : 0 ≤ ∫ x, deriv γ (h x - t) * D x ∂μ :=
      integral_nonneg fun x ↦ mul_nonneg (hγ'0 _) (hD0 x)
    have hRi : IntegrableOn K {x | t < h x} μ := hKi.mono_set (hMsub t ht0.le)
    have hR0 : 0 ≤ ∫ x in {x | t < h x}, K x ∂μ := integral_nonneg fun x ↦ hK0 x
    rw [ENNReal.ofReal_add hP0 hR0, ofReal_integral_eq_lintegral_ofReal hPi
        (Eventually.of_forall fun x ↦ mul_nonneg (hγ'0 _) (hD0 x)),
      ofReal_integral_eq_lintegral_ofReal hRi (Eventually.of_forall fun x ↦ hK0 x),
      ← lintegral_indicator (hMm t)]
    have hsplit : ∫⁻ x, F t x ∂μ =
        ∫⁻ x, ENNReal.ofReal (deriv γ (h x - t)) * ENNReal.ofReal (D x) ∂μ +
          ∫⁻ x, ENNReal.ofReal (K' x) * S.indicator 1 (t, x) ∂μ :=
      lintegral_add_left' ((hgc.measurable.ennreal_ofReal).aemeasurable.mul
        hDi.aemeasurable.ennreal_ofReal) _
    rw [hsplit]
    congr 1
    · exact lintegral_congr fun x ↦ ENNReal.ofReal_mul (hγ'0 _)
    · refine lintegral_congr fun x ↦ ?_
      by_cases htx : t < h x
      · rw [Set.indicator_of_mem (show x ∈ {x | t < h x} from htx),
          Set.indicator_of_mem (show (t, x) ∈ S from htx), hK'eq,
          Set.indicator_of_mem (hMsub t ht0.le htx)]
        simp
      · rw [Set.indicator_of_notMem (show x ∉ {x | t < h x} from htx),
          Set.indicator_of_notMem (show (t, x) ∉ S from htx), mul_zero]
  -- one point `x`: `∫⁻_{(0,∞)} F(t, x) dt ≤ ofReal (D x) + ofReal (h x K'(x))`
  have hpoint : ∀ x, ∫⁻ t in Ioi (0 : ℝ), F t x ≤
      ENNReal.ofReal (D x) + ENNReal.ofReal (h x * K' x) := by
    intro x
    have hm : Measurable fun t : ℝ ↦ ENNReal.ofReal (deriv γ (h x - t)) * ENNReal.ofReal (D x) :=
      ((hγ'c.measurable.comp (measurable_const.sub measurable_id)).ennreal_ofReal).mul_const _
    have hsplit : ∫⁻ t in Ioi (0 : ℝ), F t x =
        (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (deriv γ (h x - t))) * ENNReal.ofReal (D x) +
          ENNReal.ofReal (K' x) * ∫⁻ t in Ioi (0 : ℝ), (Iio (h x)).indicator 1 t := by
      rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      simp only [← hSx]
      exact lintegral_add_left' hm.aemeasurable _
    rw [hsplit, hB2, ENNReal.ofReal_mul (hh0 x), mul_comm (ENNReal.ofReal (K' x))]
    gcongr
    calc (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (deriv γ (h x - t))) * ENNReal.ofReal (D x)
        ≤ 1 * ENNReal.ofReal (D x) := by gcongr; exact hB1 _ (hh0 x)
      _ = ENNReal.ofReal (D x) := one_mul _
  -- `h K'` (equivalently `h K`) is integrable
  obtain ⟨m, hm⟩ := hhc.bounded_above_of_compact_support hhcs
  have hhK'i : Integrable (fun x ↦ h x * K' x) μ :=
    hK'i.bdd_mul hhc.aestronglyMeasurable (Eventually.of_forall hm)
  have hhKi : Integrable (fun x ↦ h x * K x) μ := by
    simpa only [hhK'] using hhK'i
  have hhK'0 : ∀ x, 0 ≤ h x * K' x := fun x ↦ mul_nonneg (hh0 x) (hK'0 x)
  calc ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal ((∫ x, deriv γ (h x - t) * D x ∂μ) +
        ∫ x in {x | t < h x}, K x ∂μ)
      = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x, F t x ∂μ := setLIntegral_congr_fun measurableSet_Ioi hlevel
    _ = ∫⁻ x, (∫⁻ t in Ioi (0 : ℝ), F t x) ∂μ := lintegral_lintegral_swap hFm
    _ ≤ ∫⁻ x, (ENNReal.ofReal (D x) + ENNReal.ofReal (h x * K' x)) ∂μ := lintegral_mono hpoint
    _ = ENNReal.ofReal (∫ x, D x ∂μ) + ENNReal.ofReal (∫ x, h x * K' x ∂μ) := by
      rw [lintegral_add_left' hDi.aemeasurable.ennreal_ofReal,
        ofReal_integral_eq_lintegral_ofReal hDi (Eventually.of_forall hD0),
        ofReal_integral_eq_lintegral_ofReal hhK'i (Eventually.of_forall hhK'0)]
    _ = ENNReal.ofReal (∫ x, (D x + h x * K x) ∂μ) := by
      rw [← ENNReal.ofReal_add (integral_nonneg hD0) (integral_nonneg hhK'0),
        integral_add hDi hhKi]
      simp only [hhK']
/-- **Shifted layer-cake identity (Simon Ch. 4, 4.11 with `α = n/(n-1)`, `t₀ = ε`; used in the
proof of 5.7, p. 100).** If `n ≥ 2`, `μ` is finite on compact sets, `h ≥ 0` is continuous with
compact support and `ε > 0`, then with `M_s = {x : h(x) > s}` and `p = n/(n-1)`,
`∫_0^∞ (t + ε)^{1/(n-1)} μ(M_{t+ε}) dt = ((n-1)/n) ∫_{M_ε} (h^p - ε^p) dμ`. -/
theorem Submission.sobolev_level_layer_cake : ∀ (n ℓ : ℕ) (μ : Measure (Ambient n ℓ)) (h : Ambient n ℓ → ℝ) (ε : ℝ), 2 ≤ n → IsFiniteMeasureOnCompacts μ → Continuous h → HasCompactSupport h → (∀ x, 0 ≤ h x) → 0 < ε → ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal ((t + ε) ^ ((n : ℝ) - 1)⁻¹ * μ.real {x | t + ε < h x}) = ENNReal.ofReal (((n : ℝ) - 1) / n * ∫ x in {x | ε < h x}, (h x ^ ((n : ℝ) / ((n : ℝ) - 1)) - ε ^ ((n : ℝ) / ((n : ℝ) - 1))) ∂μ) := by
  intro n ℓ μ h ε hn hμ hh hhc hh0 hε
  -- (1) Exponents: `b = 1/(n-1) > 0`, `p = n/(n-1) = b + 1 > 0` and `1/p = (n-1)/n`.
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : (0 : ℝ) < n - 1 := by linarith
  set b : ℝ := ((n : ℝ) - 1)⁻¹ with hb_def
  set p : ℝ := (n : ℝ) / ((n : ℝ) - 1) with hp_def
  have hb : 0 < b := inv_pos.2 hn1
  have hp : 0 < p := div_pos hn0 hn1
  have hbp : b + 1 = p := by
    rw [hb_def, hp_def]
    field_simp
    ring
  have hpinv : p⁻¹ = ((n : ℝ) - 1) / n := by rw [hp_def, inv_div]
  -- (2) Sets: for `s > 0`, `M_s = {h > s}` lies in the compact `tsupport h`, so `μ(M_s) < ∞`;
  -- `M_ε` is open, hence measurable.
  have hK : IsCompact (tsupport h) := hhc.isCompact
  have hsubK : ∀ s, 0 < s → {x | s < h x} ⊆ tsupport h := fun s hs x (hx : s < h x) ↦
    subset_tsupport h (hs.trans hx).ne'
  have hfin : ∀ s, 0 < s → μ {x | s < h x} ≠ ⊤ := fun s hs ↦
    ((measure_mono (hsubK s hs)).trans_lt hK.measure_lt_top).ne
  have hM : MeasurableSet {x | ε < h x} := (isOpen_lt continuous_const hh).measurableSet
  -- (3) With `f = max(h - ε, 0)` and `g(t) = (t + ε)^b`, the integrand is `μ{f > t} g(t)`.
  have hg : Continuous fun t : ℝ ↦ (t + ε) ^ b :=
    (continuous_id.add continuous_const).rpow_const fun _ ↦ Or.inr hb.le
  have step3 :
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal ((t + ε) ^ b * μ.real {x | t + ε < h x}) =
      ∫⁻ t in Ioi (0 : ℝ), μ {x | t < max (h x - ε) 0} * ENNReal.ofReal ((t + ε) ^ b) := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) ↦ ?_
    have hset : {x | t < max (h x - ε) 0} = {x | t + ε < h x} := by
      ext x
      show t < max (h x - ε) 0 ↔ t + ε < h x
      rw [lt_max_iff]
      constructor
      · rintro (hx | hx) <;> linarith
      · intro hx
        left
        linarith
    rw [hset, ENNReal.ofReal_mul (Real.rpow_nonneg (show (0 : ℝ) ≤ t + ε by linarith) b),
      ofReal_measureReal (hfin (t + ε) (by linarith)), mul_comm]
  -- (4) Layer cake (Tonelli): `∫⁻ μ{f > t} g(t) dt = ∫⁻ ofReal (∫_0^{f(x)} g) dμ(x)`.
  have step4 : ∫⁻ x, ENNReal.ofReal (∫ t in (0 : ℝ)..max (h x - ε) 0, (t + ε) ^ b) ∂μ =
      ∫⁻ t in Ioi (0 : ℝ), μ {x | t < max (h x - ε) 0} * ENNReal.ofReal ((t + ε) ^ b) :=
    lintegral_comp_eq_lintegral_meas_lt_mul μ (f := fun x ↦ max (h x - ε) 0)
      (g := fun t ↦ (t + ε) ^ b) (ae_of_all _ fun x ↦ le_max_right _ _)
      ((hh.sub continuous_const).max continuous_const).measurable.aemeasurable
      (fun t _ ↦ hg.intervalIntegrable 0 t)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t (ht : 0 < t) ↦
        show 0 ≤ (t + ε) ^ b from Real.rpow_nonneg (by linarith) b)
  -- (5) Inner integral: `∫_0^{f(x)} (t + ε)^b dt = 1_{M_ε}(x) (h(x)^p - ε^p)/p`.
  have step5 : ∀ x, ENNReal.ofReal (∫ t in (0 : ℝ)..max (h x - ε) 0, (t + ε) ^ b) =
      {x | ε < h x}.indicator
        (fun x ↦ ENNReal.ofReal (((n : ℝ) - 1) / n * (h x ^ p - ε ^ p))) x := by
    intro x
    by_cases hx : ε < h x
    · rw [indicator_of_mem (show x ∈ {x | ε < h x} from hx),
        max_eq_left (by linarith : (0 : ℝ) ≤ h x - ε)]
      congr 1
      calc ∫ t in (0 : ℝ)..h x - ε, (t + ε) ^ b
          = ∫ u in (0 + ε)..(h x - ε + ε), u ^ b :=
            intervalIntegral.integral_comp_add_right (fun u ↦ u ^ b) ε
        _ = ∫ u in ε..h x, u ^ b := by rw [zero_add, sub_add_cancel]
        _ = (h x ^ (b + 1) - ε ^ (b + 1)) / (b + 1) := integral_rpow (Or.inl (by linarith))
        _ = ((n : ℝ) - 1) / n * (h x ^ p - ε ^ p) := by
            rw [hbp, div_eq_mul_inv, mul_comm, hpinv]
    · rw [indicator_of_notMem (show x ∉ {x | ε < h x} from hx),
        max_eq_right (by linarith : h x - ε ≤ 0), intervalIntegral.integral_same,
        ENNReal.ofReal_zero]
  -- (6)–(7) Restrict to `M_ε` and return to the Bochner integral.
  have hcont : Continuous fun x ↦ ((n : ℝ) - 1) / n * (h x ^ p - ε ^ p) :=
    continuous_const.mul ((hh.rpow_const fun _ ↦ Or.inr hp.le).sub continuous_const)
  have hint : IntegrableOn (fun x ↦ ((n : ℝ) - 1) / n * (h x ^ p - ε ^ p)) {x | ε < h x} μ :=
    (hcont.continuousOn.integrableOn_compact hK).mono_set (hsubK ε hε)
  have hnn :
      0 ≤ᵐ[μ.restrict {x | ε < h x}] fun x ↦ ((n : ℝ) - 1) / n * (h x ^ p - ε ^ p) :=
    ae_restrict_of_forall_mem hM fun x (hx : ε < h x) ↦
      mul_nonneg (div_nonneg hn1.le hn0.le) (sub_nonneg.2 (Real.rpow_le_rpow hε.le hx.le hp.le))
  rw [step3, ← step4, lintegral_congr step5, lintegral_indicator hM,
    ← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_const_mul]

/-- **Integrated level-set estimate** (Simon Ch. 4, proof of 5.7, p. 100). Let `p = n/(n-1)`,
`M_s = {x : h(x) > s}`, `P(t) = ∫ γ'(h - t) D dμ` and `R(t) = ∫_{M_t} K dμ`, and suppose
`μ(M_{t+ε}) ≤ C μ(M_t)^{1/n} (P(t) + R(t))` for every `t ≥ 0`. Multiplying by `(t + ε)^{1/(n-1)}`
and using the moment factor `(t + ε)^{1/(n-1)} μ(M_t)^{1/n} ≤ Q_ε^{1/n}`, where
`Q_ε = ∫_{M_0} (h + ε)^p dμ`, gives `(t + ε)^{1/(n-1)} μ(M_{t+ε}) ≤ C Q_ε^{1/n} (P(t) + R(t))`.
Integrating over `t ∈ (0, ∞)`, the right side is at most `C Q_ε^{1/n} ∫ (D + h K) dμ` by Tonelli,
and the left side is `((n-1)/n) ∫_{M_ε} (h^p - ε^p) dμ` by the layer-cake identity 4.11. -/
theorem Submission.sobolev_level_integral_bound : ∀ (n ℓ : ℕ) (μ : Measure (Ambient n ℓ)) (h D K : Ambient n ℓ → ℝ) (γ : ℝ → ℝ) (C ε : ℝ), 2 ≤ n → IsFiniteMeasureOnCompacts μ → Continuous h → HasCompactSupport h → (∀ x, 0 ≤ h x) → (∀ x, 0 ≤ D x) → Integrable D μ → (∀ x, 0 ≤ K x) → IntegrableOn K (tsupport h) μ → ContDiff ℝ 1 γ → Monotone γ → (∀ s, 0 ≤ γ s ∧ γ s ≤ 1) → (∀ s, s ≤ 0 → γ s = 0) → 0 ≤ C → 0 < ε → (∀ t : ℝ, 0 ≤ t → μ.real {x | t + ε < h x} ≤ C * (μ.real {x | t < h x}) ^ (n : ℝ)⁻¹ * ((∫ x, deriv γ (h x - t) * D x ∂μ) + ∫ x in {x | t < h x}, K x ∂μ)) → ((n : ℝ) - 1) / n * ∫ x in {x | ε < h x}, (h x ^ ((n : ℝ) / ((n : ℝ) - 1)) - ε ^ ((n : ℝ) / ((n : ℝ) - 1))) ∂μ ≤ C * (∫ x in {x | 0 < h x}, (h x + ε) ^ ((n : ℝ) / ((n : ℝ) - 1)) ∂μ) ^ (n : ℝ)⁻¹ * ∫ x, (D x + h x * K x) ∂μ := by
  intro n ℓ μ h D K γ C ε hn hμ hhc hhcs hh0 hD0 hDi hK0 hKi hγ hγm hγb hγ0 hC hε hlev
  -- the constants `A = C Q_ε^{1/n}` and `J = ∫ (D + h K) dμ` are nonnegative
  set A : ℝ := C * (∫ x in {x | 0 < h x}, (h x + ε) ^ ((n : ℝ) / ((n : ℝ) - 1)) ∂μ) ^ (n : ℝ)⁻¹
  set J : ℝ := ∫ x, (D x + h x * K x) ∂μ
  have hA : 0 ≤ A := mul_nonneg hC (Real.rpow_nonneg
    (integral_nonneg fun x ↦ Real.rpow_nonneg (by linarith [hh0 x]) _) _)
  have hJ : 0 ≤ J := integral_nonneg fun x ↦ add_nonneg (hD0 x) (mul_nonneg (hh0 x) (hK0 x))
  -- (5.a) for `t ≥ 0`: `(t + ε)^{1/(n-1)} μ(M_{t+ε}) ≤ A (P(t) + R(t))`
  have hweight : ∀ t : ℝ, 0 ≤ t → (t + ε) ^ ((n : ℝ) - 1)⁻¹ * μ.real {x | t + ε < h x} ≤
      A * ((∫ x, deriv γ (h x - t) * D x ∂μ) + ∫ x in {x | t < h x}, K x ∂μ) := by
    intro t ht
    have hb : 0 ≤ (t + ε) ^ ((n : ℝ) - 1)⁻¹ := Real.rpow_nonneg (by linarith) _
    have hPR : 0 ≤ (∫ x, deriv γ (h x - t) * D x ∂μ) + ∫ x in {x | t < h x}, K x ∂μ :=
      add_nonneg (integral_nonneg fun x ↦ mul_nonneg hγm.deriv_nonneg (hD0 x))
        (integral_nonneg fun x ↦ hK0 x)
    calc (t + ε) ^ ((n : ℝ) - 1)⁻¹ * μ.real {x | t + ε < h x}
        ≤ (t + ε) ^ ((n : ℝ) - 1)⁻¹ * (C * (μ.real {x | t < h x}) ^ (n : ℝ)⁻¹ *
            ((∫ x, deriv γ (h x - t) * D x ∂μ) + ∫ x in {x | t < h x}, K x ∂μ)) :=
          mul_le_mul_of_nonneg_left (hlev t ht) hb
      _ = C * ((t + ε) ^ ((n : ℝ) - 1)⁻¹ * (μ.real {x | t < h x}) ^ (n : ℝ)⁻¹) *
            ((∫ x, deriv γ (h x - t) * D x ∂μ) + ∫ x in {x | t < h x}, K x ∂μ) := by ring
      _ ≤ A * ((∫ x, deriv γ (h x - t) * D x ∂μ) + ∫ x in {x | t < h x}, K x ∂μ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (Submission.sobolev_level_moment_factor n ℓ μ h ε t hn hμ hhc hhcs hh0 hε ht) hC) hPR
  -- integrate over `t ∈ (0, ∞)`: the left side is 4.11, the right side is bounded by Tonelli
  have hint : ENNReal.ofReal (((n : ℝ) - 1) / n * ∫ x in {x | ε < h x},
      (h x ^ ((n : ℝ) / ((n : ℝ) - 1)) - ε ^ ((n : ℝ) / ((n : ℝ) - 1))) ∂μ) ≤
      ENNReal.ofReal (A * J) := by
    rw [← Submission.sobolev_level_layer_cake n ℓ μ h ε hn hμ hhc hhcs hh0 hε,
      ENNReal.ofReal_mul hA]
    calc ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal ((t + ε) ^ ((n : ℝ) - 1)⁻¹ *
          μ.real {x | t + ε < h x})
        ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal A *
            ENNReal.ofReal ((∫ x, deriv γ (h x - t) * D x ∂μ) + ∫ x in {x | t < h x}, K x ∂μ) :=
          setLIntegral_mono' measurableSet_Ioi fun t ht ↦ by
            rw [← ENNReal.ofReal_mul hA]
            exact ENNReal.ofReal_le_ofReal (hweight t (mem_Ioi.1 ht).le)
      _ = ENNReal.ofReal A * ∫⁻ t in Ioi (0 : ℝ),
            ENNReal.ofReal ((∫ x, deriv γ (h x - t) * D x ∂μ) + ∫ x in {x | t < h x}, K x ∂μ) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal A * ENNReal.ofReal J :=
          mul_le_mul_right (Submission.sobolev_level_energy_tonelli n ℓ μ h D K γ hμ hhc hhcs hh0
            hD0 hDi hK0 hKi hγ hγm hγb hγ0) _
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hA hJ)).1 hint
/-- **Sobolev inequality, letting the level shift `ε ↓ 0` (Simon Ch. 4, end of the proof of
5.7).** Let `n ≥ 2`, let `μ` be finite on compact sets, let `h ≥ 0` be continuous with compact
support, `C, J ≥ 0` and `p = n/(n-1)`. If for every `ε ∈ (0, 1]`
`((n-1)/n) ∫_{h > ε} (h^p - ε^p) dμ ≤ C (∫_{h > 0} (h + ε)^p dμ)^{1/n} J`, then
`(∫ h^p dμ)^{(n-1)/n} ≤ (n/(n-1)) C J`. -/
theorem Submission.sobolev_of_level_integral_bounds : ∀ (n ℓ : ℕ) (μ : Measure (Ambient n ℓ)) (h : Ambient n ℓ → ℝ) (C J : ℝ), 2 ≤ n → IsFiniteMeasureOnCompacts μ → Continuous h → HasCompactSupport h → (∀ x, 0 ≤ h x) → 0 ≤ C → 0 ≤ J → (∀ ε : ℝ, 0 < ε → ε ≤ 1 → ((n : ℝ) - 1) / n * ∫ x in {x | ε < h x}, (h x ^ ((n : ℝ) / ((n : ℝ) - 1)) - ε ^ ((n : ℝ) / ((n : ℝ) - 1))) ∂μ ≤ C * (∫ x in {x | 0 < h x}, (h x + ε) ^ ((n : ℝ) / ((n : ℝ) - 1)) ∂μ) ^ (n : ℝ)⁻¹ * J) → (∫ x, h x ^ ((n : ℝ) / ((n : ℝ) - 1)) ∂μ) ^ (((n : ℝ) - 1) / n) ≤ (n : ℝ) / ((n : ℝ) - 1) * C * J := by
  intro n ℓ μ h C J hn hμ hc hcs hnn hC hJ hbound
  have hn1 : (1 : ℝ) < n := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hn0 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  set p : ℝ := (n : ℝ) / ((n : ℝ) - 1) with hp
  have hp0 : 0 < p := div_pos (by linarith) hn0
  -- Step 1: `h ^ p` is continuous with compact support, hence `μ`-integrable.
  have hpc : Continuous fun x ↦ h x ^ p := hc.rpow_const fun _ ↦ Or.inr hp0.le
  have hpi : Integrable (fun x ↦ h x ^ p) μ :=
    hpc.integrable_of_hasCompactSupport
      (hcs.comp_left (g := fun y : ℝ ↦ y ^ p) (Real.zero_rpow hp0.ne'))
  -- The level sets `{s < h}` are open, hence measurable.
  have hmeas : ∀ s : ℝ, MeasurableSet {x | s < h x} := fun s ↦
    (isOpen_lt continuous_const hc).measurableSet
  -- The shifts `e k = 1/(k+1) ∈ (0, 1]` tend to `0`.
  set e : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1) with he
  have he0 : ∀ k, 0 < e k := fun k ↦ by positivity
  have he1 : ∀ k, e k ≤ 1 := fun k ↦ by
    rw [he, div_le_one (by positivity)]
    linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  have helim : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  -- Step 2: `∫_{e k < h} (h ^ p - e k ^ p) dμ → ∫ h ^ p dμ` (dominated by `h ^ p`).
  have hlimA : Tendsto (fun k ↦ ∫ x in {x | e k < h x}, (h x ^ p - e k ^ p) ∂μ) atTop
      (𝓝 (∫ x, h x ^ p ∂μ)) := by
    have hind : (fun k ↦ ∫ x in {x | e k < h x}, (h x ^ p - e k ^ p) ∂μ) =
        fun k ↦ ∫ x, {x | e k < h x}.indicator (fun x ↦ h x ^ p - e k ^ p) x ∂μ :=
      funext fun k ↦ (integral_indicator (hmeas (e k))).symm
    rw [hind]
    refine tendsto_integral_of_dominated_convergence (fun x ↦ h x ^ p)
      (fun k ↦ ((hpc.sub continuous_const).aestronglyMeasurable).indicator (hmeas (e k))) hpi
      (fun k ↦ Eventually.of_forall fun x ↦ ?_) (Eventually.of_forall fun x ↦ ?_)
    · by_cases hx : e k < h x
      · rw [indicator_of_mem (show x ∈ {x | e k < h x} from hx), Real.norm_eq_abs,
          abs_of_nonneg (sub_nonneg.2 (Real.rpow_le_rpow (he0 k).le hx.le hp0.le))]
        linarith [Real.rpow_nonneg (he0 k).le p]
      · rw [indicator_of_notMem (show x ∉ {x | e k < h x} from hx), norm_zero]
        exact Real.rpow_nonneg (hnn x) p
    · rcases (hnn x).lt_or_eq with hx | hx
      · have hlim : Tendsto (fun k ↦ h x ^ p - e k ^ p) atTop (𝓝 (h x ^ p - 0)) :=
          tendsto_const_nhds.sub (helim.rpow_const_nhds_zero hp0)
        rw [sub_zero] at hlim
        refine hlim.congr' ?_
        filter_upwards [helim.eventually (eventually_lt_nhds hx)] with k hk
        exact (indicator_of_mem (show x ∈ {x | e k < h x} from hk)
          (fun x ↦ h x ^ p - e k ^ p)).symm
      · have hzero : ∀ k, {x | e k < h x}.indicator (fun x ↦ h x ^ p - e k ^ p) x = 0 :=
          fun k ↦ indicator_of_notMem (s := {x | e k < h x}) (a := x)
            (not_lt.2 (by rw [← hx]; exact (he0 k).le : h x ≤ e k)) _
        simp only [hzero, ← hx, Real.zero_rpow hp0.ne']
        exact tendsto_const_nhds
  -- Step 3: `∫_{0 < h} (h + e k) ^ p dμ → ∫ h ^ p dμ` (dominated by `(h + 1) ^ p` on `{0 < h}`).
  have hlimB : Tendsto (fun k ↦ ∫ x in {x | 0 < h x}, (h x + e k) ^ p ∂μ) atTop
      (𝓝 (∫ x, h x ^ p ∂μ)) := by
    have hsub : {x | 0 < h x} ⊆ tsupport h := fun x hx ↦ subset_tsupport h (ne_of_gt hx)
    have hbi : IntegrableOn (fun x ↦ (h x + 1) ^ p) {x | 0 < h x} μ :=
      (((hc.add continuous_const).rpow_const fun _ ↦ Or.inr hp0.le).continuousOn
        |>.integrableOn_compact hcs.isCompact).mono_set hsub
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := {x | 0 < h x}) fun x hx ↦ by
      rw [show h x = 0 from le_antisymm (not_lt.1 hx) (hnn x), Real.zero_rpow hp0.ne']]
    refine tendsto_integral_of_dominated_convergence (fun x ↦ (h x + 1) ^ p)
      (fun k ↦ ((hc.add continuous_const).rpow_const fun _ ↦ Or.inr hp0.le).aestronglyMeasurable)
      hbi (fun k ↦ (ae_restrict_iff' (hmeas 0)).2 (Eventually.of_forall fun x hx ↦ ?_))
      (Eventually.of_forall fun x ↦ ?_)
    · have hx0 : 0 ≤ h x + e k := by linarith [he0 k, hnn x]
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0 p)]
      exact Real.rpow_le_rpow hx0 (by linarith [he1 k]) hp0.le
    · have hlim := (tendsto_const_nhds (x := h x)).add helim |>.rpow_const (p := p) (Or.inr hp0.le)
      simpa only [add_zero] using hlim
  -- Step 4: pass to the limit in the hypothesis along `e k`.
  set Q := ∫ x, h x ^ p ∂μ
  have hkey : ((n : ℝ) - 1) / n * Q ≤ C * Q ^ (n : ℝ)⁻¹ * J :=
    le_of_tendsto_of_tendsto' (tendsto_const_nhds.mul hlimA)
      ((tendsto_const_nhds.mul (hlimB.rpow_const (Or.inr (by positivity)))).mul tendsto_const_nhds)
      fun k ↦ hbound (e k) (he0 k) (he1 k)
  -- Step 5: absorb `Q ^ (1/n)`.
  have hQ0 : 0 ≤ Q := integral_nonneg fun x ↦ Real.rpow_nonneg (hnn x) p
  have hA0 : 0 ≤ p * C * J := mul_nonneg (mul_nonneg hp0.le hC) hJ
  have hnne : (n : ℝ) ≠ 0 := by positivity
  rcases hQ0.eq_or_lt with hQe | hQpos
  · rw [← hQe, Real.zero_rpow (div_pos hn0 (by linarith)).ne']
    exact hA0
  · have hexp : ((n : ℝ) - 1) / n = 1 - (n : ℝ)⁻¹ := by field_simp
    have hpinv : p * (((n : ℝ) - 1) / n) = 1 := by rw [hp]; field_simp
    have hQn : 0 < Q ^ (n : ℝ)⁻¹ := Real.rpow_pos_of_pos hQpos _
    rw [hexp, Real.rpow_sub hQpos, Real.rpow_one, div_le_iff₀ hQn]
    calc Q = p * (((n : ℝ) - 1) / n * Q) := by rw [← mul_assoc, hpinv, one_mul]
      _ ≤ p * (C * Q ^ (n : ℝ)⁻¹ * J) := mul_le_mul_of_nonneg_left hkey hp0.le
      _ = p * C * J * Q ^ (n : ℝ)⁻¹ := by ring
/-- **Sobolev preliminaries (Simon Ch. 4, 5.7–5.9, Step 1).** If `μ_V` is finite on compact
sets, `x ↦ p_{T_x V}` is `μ_V`-a.e. strongly measurable, `U` is open, `H` is locally
`μ_V`-integrable on `U`, and `g ∈ C¹(U)` has compact support in `U`, then `g ∈ C¹(ℝ^{n+ℓ})`,
`∇^M g = 0` off `tsupport g`, and `|∇^M g|` and `g|H|` are `μ_V`-integrable. -/
theorem Submission.sobolev_energy_integrable : ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)) (H : Ambient n ℓ → Ambient n ℓ) (g : Ambient n ℓ → ℝ), IsFiniteMeasureOnCompacts V.weight → AEStronglyMeasurable (fun x ↦ (V.tangentSpace x).starProjection) V.weight → IsOpen U → LocallyIntegrableOn H U V.weight → ContDiffOn ℝ 1 g U → HasCompactSupport g → tsupport g ⊆ U → ContDiff ℝ 1 g ∧ (∀ x, x ∉ tsupport g → V.tangentialGradient g x = 0) ∧ Integrable (fun x ↦ ‖V.tangentialGradient g x‖) V.weight ∧ Integrable (fun x ↦ g x * ‖H x‖) V.weight := by
  intro n ℓ V U H g hfin hproj hU hH hg hgc hgU
  -- (1) `g` is `C¹` at points of the open set `U`, and `g = 0` near points off `tsupport g ⊆ U`.
  have hC1 : ContDiff ℝ 1 g := contDiff_iff_contDiffAt.2 fun x ↦ by
    by_cases hx : x ∈ U
    · exact hg.contDiffAt (hU.mem_nhds hx)
    · exact contDiffAt_const.congr_of_eventuallyEq
        (notMem_tsupport_iff_eventuallyEq.1 fun h ↦ hx (hgU h))
  -- (2) `∇g`, hence `∇^M g = p_{T_x V}(∇g)`, vanishes off `tsupport g`.
  have hgrad0 : ∀ x, x ∉ tsupport g → gradient g x = 0 := fun x hx ↦ by
    simp [gradient, fderiv_of_notMem_tsupport ℝ hx]
  have hzero : ∀ x, x ∉ tsupport g → V.tangentialGradient g x = 0 := fun x hx ↦ by
    simp [tangentialGradient, hgrad0 x hx]
  -- `∇g` is continuous with compact support, hence `μ_V`-integrable.
  have hgradc : Continuous (gradient g) :=
    (InnerProductSpace.toDual ℝ (Ambient n ℓ)).symm.continuous.comp
      (hC1.continuous_fderiv one_ne_zero)
  have hgradi : Integrable (gradient g) V.weight :=
    hgradc.integrable_of_hasCompactSupport (hgc.mono' fun x hx ↦ of_not_not fun h ↦ hx (hgrad0 x h))
  refine ⟨hC1, hzero, ?_, ?_⟩
  · -- (3) `∇^M g` is a.e. strongly measurable and `|∇^M g| ≤ |∇g|`.
    refine hgradi.mono ?_ (ae_of_all _ fun x ↦ ?_)
    · exact (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
        (hproj.prodMk hgradc.aestronglyMeasurable)).norm
    · rw [norm_norm]
      exact Submodule.norm_starProjection_apply_le _ _
  · -- (4) `H` is integrable on the compact set `tsupport g ⊆ U`, and `g|H|` vanishes off it.
    have hHK : IntegrableOn H (tsupport g) V.weight := hH.integrableOn_compact_subset hgU hgc
    exact (integrableOn_iff_integrable_of_support_subset fun x hx ↦
      subset_tsupport g (left_ne_zero_of_mul hx)).1
      (IntegrableOn.continuousOn_mul hC1.continuous.continuousOn hHK.norm hgc)
/-- **Ch. 4, opening of §5 (statement (1.1) of the Sobolev proof).** Assume `ApproxTangentAE`.
If `U` is open and `θ ≥ 1` `μ_V`-a.e. in `U`, then for `μ_V`-a.e. `x ∈ U` the density
`Θⁿ(μ_V, x)` exists and `Θⁿ(μ_V, x) ≥ 1`: for a representative `(M, θ)` of `V`,
`Θⁿ(μ_V, x) = θ(x) ≥ 1` for `Hⁿ`-a.e. `x ∈ M ∩ U`, and `μ_V = Hⁿ ⌞ θ ≪ Hⁿ ⌞ M`. -/
theorem Submission.sobolev_density_ge_one_ae : ApproxTangentAE → ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)), 0 < n → IsOpen U → V.MultiplicityGE 1 U → ∀ᵐ x ∂V.weight, x ∈ U → V.HasDensityAt x (V.density x) ∧ 1 ≤ V.density x := by
  intro hAT n ℓ V U hn hU hθ
  -- A representative `a = (M, θ)` of `V` with `θ ≥ 1` `Hⁿ`-a.e. on `M ∩ U`.
  obtain ⟨a, rfl, ha⟩ := hθ
  -- `Hⁿ ⌞ (M ∩ U) = (Hⁿ ⌞ M) ⌞ U` (`U` is Borel), so `x ∈ U → 1 ≤ θ x` `Hⁿ ⌞ M`-a.e.
  have hge : ∀ᵐ x ∂(μHE[n] : Measure (Ambient n ℓ)).restrict a.M, x ∈ U → 1 ≤ a.θ x := by
    rw [← ae_restrict_iff' hU.measurableSet, Measure.restrict_restrict hU.measurableSet,
      Set.inter_comm U a.M]
    exact ha
  -- `μ_V = (Hⁿ ⌞ M).withDensity θ ≪ Hⁿ ⌞ M`, so `Hⁿ ⌞ M`-a.e. statements hold `μ_V`-a.e.
  have hac : (mk a).weight ≪ (μHE[n] : Measure (Ambient n ℓ)).restrict a.M :=
    withDensity_absolutelyContinuous _ _
  refine hac.ae_le ?_
  -- `ApproxTangentAE`: `HasDensityAt x (θ x)` for `Hⁿ ⌞ M`-a.e. `x`.
  filter_upwards [hge, hAT n ℓ a hn] with x hx hT hxU
  -- The limit along `𝓝[>] 0` is unique, so `Θⁿ(μ_V, x) = θ x`.
  have hd : (mk a).density x = a.θ x := hT.2.2.limUnder_eq
  rw [hd]
  exact ⟨hT.2.2, hx hxU⟩
/-- **Corrected Simon Lemma 5.8 (good radius), `n ≥ 2`.** Let `f, k` be nondecreasing on `(0, ∞)`
with `0 ≤ f ≤ F` and `0 ≤ k`, such that `s⁻ⁿf(s) ≤ r⁻ⁿf(r) + ∫_{(s,r]} τ⁻ⁿk(τ) dτ` for
`0 < s ≤ r` and `limsup_{s↓0} s⁻ⁿf(s) ≥ 1`. Then `F > 0` and some `r ∈ (0, 2F^{1/n})` satisfies
`f(5r) ≤ 5ⁿF^{1/n}k(r)`. Otherwise, with `r₀ = 2F^{1/n}`, `S = sup_{[s,r₀]} τ⁻ⁿf(τ)` for a small
`s` with `s⁻ⁿf(s) > 2/3`, the substitution `u = 5τ` gives `S ≤ (7/5)2⁻ⁿ + (2/5)S`, so
`S ≤ 7/12`. (The printed lemma's lower bound `1 ≤ σ⁻ⁿf(σ)` for all `σ` contradicts `f ≤ F`.) -/
theorem Submission.sobolev_good_radius_calculus : ∀ (n : ℕ) (f k : ℝ → ℝ) (F : ℝ), 2 ≤ n →
    MonotoneOn f (Ioi 0) → MonotoneOn k (Ioi 0) → (∀ τ : ℝ, 0 < τ → 0 ≤ f τ ∧ f τ ≤ F) →
    (∀ τ : ℝ, 0 < τ → 0 ≤ k τ) →
    (∀ s r : ℝ, 0 < s → s ≤ r → f s / s ^ n ≤ f r / r ^ n + ∫ τ in Ioc s r, k τ / τ ^ n) →
    (∀ η : ℝ, η < 1 → ∃ᶠ s in 𝓝[>] (0 : ℝ), η < f s / s ^ n) →
    0 < F ∧ ∃ r : ℝ, 0 < r ∧ r < 2 * F ^ (n : ℝ)⁻¹ ∧ f (5 * r) ≤ 5 ^ n * F ^ (n : ℝ)⁻¹ * k r := by
  intro n f k F hn hf hk hfb hk0 ha hb
  -- Step 1: `F > 0`, from a radius `s₀ > 0` with `f(s₀)/s₀ⁿ > 0`.
  have hF : 0 < F := by
    obtain ⟨s₀, hpos, hs₀⟩ := ((hb 0 (by norm_num)).and_eventually self_mem_nhdsWithin).exists
    have hs₀' : (0 : ℝ) < s₀ := hs₀
    have h1 : 0 < f s₀ := (div_pos_iff_of_pos_right (pow_pos hs₀' n)).mp hpos
    linarith [(hfb s₀ hs₀').2]
  refine ⟨hF, ?_⟩
  -- Step 2: `r₀ = 2F^{1/n}`, so `r₀ⁿ = 2ⁿF` and `P = F/r₀ⁿ = 2⁻ⁿ ≤ 1/4`.
  obtain ⟨r₀, hr₀⟩ : ∃ r₀ : ℝ, r₀ = 2 * F ^ (n : ℝ)⁻¹ := ⟨_, rfl⟩
  have hFr : F ^ (n : ℝ)⁻¹ = r₀ / 2 := by rw [hr₀]; ring
  have hr₀pos : 0 < r₀ := by rw [hr₀]; positivity
  have hr₀n : r₀ ^ n = 2 ^ n * F := by
    rw [hr₀, mul_pow, Real.rpow_inv_natCast_pow hF.le (by omega)]
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = F / r₀ ^ n := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  have hP4 : P ≤ 1 / 4 := by
    have h4 : (4 : ℝ) ≤ 2 ^ n := by
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
    have hPe : P = 1 / 2 ^ n := by rw [hP, hr₀n]; field_simp
    rw [hPe]
    exact one_div_le_one_div_of_le (by norm_num) h4
  rw [hFr]
  -- Step 4: suppose no radius in `(0, r₀)` is good.
  by_contra hcon
  have hbad : ∀ τ : ℝ, 0 < τ → τ < r₀ → 5 ^ n * (r₀ / 2) * k τ < f (5 * τ) := by
    intro τ hτ hτr
    by_contra hle
    exact hcon ⟨τ, hτ, by linarith, not_lt.mp hle⟩
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = fun u ↦ f u / u ^ n := ⟨_, rfl⟩
  have hgv : ∀ u, g u = f u / u ^ n := fun u ↦ by rw [hg]
  have hg0 : ∀ u, 0 < u → 0 ≤ g u := fun u hu ↦ by
    rw [hgv]; exact div_nonneg (hfb u hu).1 (pow_pos hu n).le
  -- So `τ⁻ⁿk(τ) ≤ (2/r₀) g(5τ)` on `(0, r₀)`.
  have hkey : ∀ τ : ℝ, 0 < τ → τ < r₀ → k τ / τ ^ n ≤ 2 / r₀ * g (5 * τ) := by
    intro τ hτ hτr
    have h := hbad τ hτ hτr
    have hτn : 0 < τ ^ n := pow_pos hτ n
    rw [hgv, mul_pow, div_le_iff₀ hτn]
    have e : 2 / r₀ * (f (5 * τ) / (5 ^ n * τ ^ n)) * τ ^ n = 2 * f (5 * τ) / (r₀ * 5 ^ n) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    have e2 : k τ * (r₀ * 5 ^ n) = 2 * (5 ^ n * (r₀ / 2) * k τ) := by ring
    linarith
  -- Step 3: integrability on compact subintervals of `(0, ∞)`.
  have hint : ∀ φ : ℝ → ℝ, MonotoneOn φ (Ioi 0) → ∀ a b : ℝ, 0 < a → 0 < b →
      IntervalIntegrable (fun τ ↦ φ τ / τ ^ n) volume a b := by
    intro φ hφ a b ha hb
    have hsub : uIcc a b ⊆ Ioi 0 := by
      intro x hx
      rcases mem_uIcc.mp hx with h | h
      · exact lt_of_lt_of_le ha h.1
      · exact lt_of_lt_of_le hb h.1
    have h1 : IntervalIntegrable φ volume a b := (hφ.mono hsub).intervalIntegrable
    have h2 : ContinuousOn (fun τ : ℝ ↦ (τ ^ n)⁻¹) (uIcc a b) :=
      (continuous_pow n).continuousOn.inv₀ fun x hx ↦ pow_ne_zero n (ne_of_gt (hsub hx))
    simpa only [div_eq_mul_inv] using h1.mul_continuousOn h2
  have hgint : ∀ a b : ℝ, 0 < a → 0 < b → IntervalIntegrable g volume a b := by
    intro a b ha hb; rw [hg]; exact hint f hf a b ha hb
  -- Step 5: a radius `s ∈ (0, r₀)` with `f(s)/sⁿ > 2/3`.
  obtain ⟨s, hs2, hs⟩ :=
    ((hb (2 / 3) (by norm_num)).and_eventually (Ioo_mem_nhdsGT hr₀pos)).exists
  have hs0 : 0 < s := hs.1
  -- Step 6: `S = sup_{[s, r₀]} g`.
  have hbdd : BddAbove (g '' Icc s r₀) := by
    refine ⟨F / s ^ n, ?_⟩
    rintro _ ⟨τ, hτ, rfl⟩
    have hτ0 : 0 < τ := lt_of_lt_of_le hs.1 hτ.1
    rw [hgv]
    calc f τ / τ ^ n ≤ F / τ ^ n := by gcongr; exact (hfb τ hτ0).2
      _ ≤ F / s ^ n := by gcongr; exact hτ.1
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = sSup (g '' Icc s r₀) := ⟨_, rfl⟩
  have hgS : ∀ τ ∈ Icc s r₀, g τ ≤ S := fun τ hτ ↦ hS ▸ le_csSup hbdd (mem_image_of_mem g hτ)
  have hS23 : 2 / 3 < S := lt_of_lt_of_le (by rw [hgv]; exact hs2) (hgS s ⟨le_rfl, hs.2.le⟩)
  -- Step 10: `∫_s^{r₀} g ≤ r₀S` and `∫_{r₀}^{5r₀} g ≤ F r₀^{1-n} = r₀P`.
  have hJ1 : ∫ u in s..r₀, g u ≤ r₀ * S := by
    calc ∫ u in s..r₀, g u ≤ ∫ _ in s..r₀, S :=
          intervalIntegral.integral_mono_on hs.2.le (hgint s r₀ hs.1 hr₀pos)
            intervalIntegrable_const hgS
      _ = (r₀ - s) * S := by rw [intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ r₀ * S := by nlinarith [hs.1]
  have hJ2 : ∫ u in r₀..5 * r₀, g u ≤ r₀ * P := by
    have hFint : IntervalIntegrable (fun u ↦ F / u ^ n) volume r₀ (5 * r₀) :=
      hint (fun _ ↦ F) monotoneOn_const r₀ (5 * r₀) hr₀pos (by positivity)
    have hfun : (fun u : ℝ ↦ F / u ^ n) = fun u ↦ F * u ^ (-(n : ℤ)) := by
      funext u; rw [zpow_neg, zpow_natCast, div_eq_mul_inv]
    have hA : r₀ ^ (-(n : ℤ) + 1) = r₀ / r₀ ^ n := by
      rw [zpow_add₀ hr₀pos.ne', zpow_neg, zpow_natCast, zpow_one]; ring
    have hB : 0 < (5 * r₀) ^ (-(n : ℤ) + 1) := zpow_pos (by positivity) _
    have hD : ((-(n : ℤ) : ℤ) : ℝ) + 1 ≤ -1 := by
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      push_cast; linarith
    have hq : ((5 * r₀) ^ (-(n : ℤ) + 1) - r₀ / r₀ ^ n) / (((-(n : ℤ) : ℤ) : ℝ) + 1) ≤
        r₀ / r₀ ^ n := by
      rw [div_le_iff_of_neg (by linarith)]
      have : 0 < r₀ / r₀ ^ n := by positivity
      nlinarith
    calc ∫ u in r₀..5 * r₀, g u ≤ ∫ u in r₀..5 * r₀, F / u ^ n := by
          refine intervalIntegral.integral_mono_on (by linarith)
            (hgint r₀ (5 * r₀) hr₀pos (by positivity)) hFint fun u hu ↦ ?_
          have hu0 : 0 < u := lt_of_lt_of_le hr₀pos hu.1
          rw [hgv]; gcongr; exact (hfb u hu0).2
      _ = F * ∫ u in r₀..5 * r₀, u ^ (-(n : ℤ)) := by
          rw [hfun, intervalIntegral.integral_const_mul]
      _ = F * (((5 * r₀) ^ (-(n : ℤ) + 1) - r₀ ^ (-(n : ℤ) + 1)) / (((-(n : ℤ) : ℤ) : ℝ) + 1)) := by
          rw [integral_zpow (Or.inr ⟨by omega, notMem_uIcc_of_lt hr₀pos (by positivity)⟩)]
      _ ≤ F * (r₀ / r₀ ^ n) := by rw [hA]; gcongr
      _ = r₀ * P := by rw [hP]; ring
  -- Steps 7–11: for every `s' ∈ [s, r₀]`, `g(s') ≤ (7/5)P + (2/5)S`.
  have hstep : ∀ s' ∈ Icc s r₀, g s' ≤ 7 / 5 * P + 2 / 5 * S := by
    intro s' hs'
    have hs'pos : 0 < s' := lt_of_lt_of_le hs.1 hs'.1
    have h1 := ha s' r₀ hs'pos hs'.2
    rw [← intervalIntegral.integral_of_le hs'.2] at h1
    have h2 : f r₀ / r₀ ^ n ≤ P := by rw [hP]; gcongr; exact (hfb r₀ hr₀pos).2
    have h3 : ∫ τ in s'..r₀, k τ / τ ^ n ≤ ∫ τ in s'..r₀, 2 / r₀ * g (5 * τ) := by
      refine intervalIntegral.integral_mono_on_of_le_Ioo hs'.2 (hint k hk s' r₀ hs'pos hr₀pos)
        ?_ fun τ hτ ↦ hkey τ (hs'pos.trans hτ.1) hτ.2
      have h := (hgint (5 * s') (5 * r₀) (by positivity) (by positivity)).comp_mul_left (c := 5)
      rw [mul_div_cancel_left₀ _ (by norm_num : (5 : ℝ) ≠ 0),
        mul_div_cancel_left₀ _ (by norm_num : (5 : ℝ) ≠ 0)] at h
      exact h.const_mul (2 / r₀)
    have h4 : ∫ τ in s'..r₀, 2 / r₀ * g (5 * τ) =
        2 / r₀ * (5⁻¹ * ∫ u in 5 * s'..5 * r₀, g u) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_mul_left g (by norm_num : (5 : ℝ) ≠ 0), smul_eq_mul]
    have h5 : ∫ u in 5 * s'..5 * r₀, g u ≤ r₀ * S + r₀ * P := by
      have e1 := intervalIntegral.integral_add_adjacent_intervals
        (hgint s (5 * s') hs.1 (by positivity)) (hgint (5 * s') (5 * r₀) (by positivity) (by positivity))
      have e2 := intervalIntegral.integral_add_adjacent_intervals
        (hgint s r₀ hs.1 hr₀pos) (hgint r₀ (5 * r₀) hr₀pos (by positivity))
      have e3 : 0 ≤ ∫ u in s..5 * s', g u :=
        intervalIntegral.integral_nonneg (by linarith [hs'.1])
          fun u hu ↦ hg0 u (lt_of_lt_of_le hs.1 hu.1)
      linarith
    have h6 : 2 / r₀ * (5⁻¹ * ∫ u in 5 * s'..5 * r₀, g u) ≤ 2 / 5 * (S + P) := by
      calc 2 / r₀ * (5⁻¹ * ∫ u in 5 * s'..5 * r₀, g u) ≤ 2 / r₀ * (5⁻¹ * (r₀ * S + r₀ * P)) := by
            gcongr
        _ = 2 / 5 * (S + P) := by field_simp
    rw [hgv]
    linarith
  -- Step 12: `S ≤ (7/5)P + (2/5)S`, so `S ≤ (7/3)P ≤ 7/12 < 2/3`.
  have hSle : S ≤ 7 / 5 * P + 2 / 5 * S := by
    rw [hS]
    refine csSup_le ⟨g s, mem_image_of_mem g ⟨le_rfl, hs.2.le⟩⟩ ?_
    rintro _ ⟨τ, hτ, rfl⟩
    rw [← hS]
    exact hstep τ hτ
  linarith

/-- Simon 5.5 for `g ∈ C¹_c(U)`, `g ≥ 0`, at every pair of radii `0 < s ≤ r` (node
`monotonicity_inequality`): assuming the weighted monotonicity identity (W),
`s⁻ⁿ ∫_{B_s(ζ)} g dμ_V ≤ r⁻ⁿ ∫_{B_r(ζ)} g dμ_V + ∫_{(s,r]} τ⁻ⁿ ∫_{B_τ(ζ)} (|∇^M g| + g|H|) dμ_V dτ`.
The annulus term of (W) is nonnegative, and by Cauchy–Schwarz its radial term is bounded below
by `-∫_{(s,r]} τ⁻ⁿ Φ(τ) dτ`, where `Φ(τ) = ∫_{B_τ(ζ)} (|∇^M g| + g|H|) dμ_V` is monotone and
bounded (the energy is integrable by `sobolev_energy_integrable`). -/
theorem Submission.sobolev_monotonicity_inequality : (∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)) (H : Ambient n ℓ → Ambient n ℓ) (h : Ambient n ℓ → ℝ) (ξ : Ambient n ℓ) (σ ρ : ℝ), 0 < n → IsFiniteMeasureOnCompacts V.weight → (∀ᵐ x ∂V.weight, Module.finrank ℝ (V.tangentSpace x) = n) → AEStronglyMeasurable (fun x ↦ (V.tangentSpace x).starProjection) V.weight → IsOpen U → V.HasMeanCurvatureIn U H → ContDiffOn ℝ 1 h U → tsupport h ∩ closedBall ξ ρ ⊆ U → 0 < σ → σ ≤ ρ → IntegrableOn (fun τ ↦ (∫ x in closedBall ξ τ, inner ℝ (x - ξ) (V.tangentialGradient h x + h x • H x) ∂V.weight) / τ ^ (n + 1)) (Ioc σ ρ) ∧ IntegrableOn (fun x ↦ h x * (V.normalRadialSq ξ x / ‖x - ξ‖ ^ n)) (closedBall ξ ρ \ closedBall ξ σ) V.weight ∧ (∫ x in closedBall ξ ρ, h x ∂V.weight) / ρ ^ n - (∫ x in closedBall ξ σ, h x ∂V.weight) / σ ^ n = ∫ x in closedBall ξ ρ \ closedBall ξ σ, h x * (V.normalRadialSq ξ x / ‖x - ξ‖ ^ n) ∂V.weight + ∫ τ in Ioc σ ρ, (∫ x in closedBall ξ τ, inner ℝ (x - ξ) (V.tangentialGradient h x + h x • H x) ∂V.weight) / τ ^ (n + 1)) → ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)) (H : Ambient n ℓ → Ambient n ℓ) (g : Ambient n ℓ → ℝ) (ζ : Ambient n ℓ) (s r : ℝ), 0 < n → IsFiniteMeasureOnCompacts V.weight → (∀ᵐ x ∂V.weight, Module.finrank ℝ (V.tangentSpace x) = n) → AEStronglyMeasurable (fun x ↦ (V.tangentSpace x).starProjection) V.weight → IsOpen U → V.HasMeanCurvatureIn U H → ContDiffOn ℝ 1 g U → HasCompactSupport g → tsupport g ⊆ U → (∀ x, 0 ≤ g x) → 0 < s → s ≤ r → (∫ x in closedBall ζ s, g x ∂V.weight) / s ^ n ≤ (∫ x in closedBall ζ r, g x ∂V.weight) / r ^ n + ∫ τ in Ioc s r, (∫ x in closedBall ζ τ, (‖V.tangentialGradient g x‖ + g x * ‖H x‖) ∂V.weight) / τ ^ n := by
  intro hW n ℓ V U H g ζ s r hn hfin hdim hmeas hU hH hg hgc hgU hg0 hs hsr
  obtain ⟨hLint, -, hid⟩ :=
    hW n ℓ V U H g ζ s r hn hfin hdim hmeas hU hH hg (fun x hx ↦ hgU hx.1) hs hsr
  obtain ⟨-, -, hgrad, hgH⟩ :=
    Submission.sobolev_energy_integrable n ℓ V U H g hfin hmeas hU hH.1 hg hgc hgU
  have hφ : Integrable (fun x ↦ ‖V.tangentialGradient g x‖ + g x * ‖H x‖) V.weight :=
    hgrad.add hgH
  have hφ0 : ∀ x, 0 ≤ ‖V.tangentialGradient g x‖ + g x * ‖H x‖ := fun x ↦
    add_nonneg (norm_nonneg _) (mul_nonneg (hg0 x) (norm_nonneg _))
  -- `Φ(τ) = ∫_{B_τ(ζ)} (|∇^M g| + g|H|) dμ_V` is monotone, so `Φ(τ)/τⁿ` is integrable on `(s, r]`.
  have hΦmono : Monotone fun τ : ℝ ↦
      ∫ x in closedBall ζ τ, (‖V.tangentialGradient g x‖ + g x * ‖H x‖) ∂V.weight :=
    fun τ τ' hττ' ↦ setIntegral_mono_set hφ.integrableOn (ae_of_all _ hφ0)
      (Eventually.of_forall (closedBall_subset_closedBall hττ'))
  have hΦint : IntegrableOn (fun τ ↦ (∫ x in closedBall ζ τ,
      (‖V.tangentialGradient g x‖ + g x * ‖H x‖) ∂V.weight) / τ ^ n) (Ioc s r) := by
    refine Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
      (hΦmono.measurable.div (continuous_pow n).measurable).aestronglyMeasurable
      (M := (∫ x, (‖V.tangentialGradient g x‖ + g x * ‖H x‖) ∂V.weight) / s ^ n)
      (ae_restrict_of_forall_mem measurableSet_Ioc fun τ hτ ↦ ?_)
    have hτ0 : 0 < τ := hs.trans hτ.1
    have hΦ0 : 0 ≤ ∫ x in closedBall ζ τ, (‖V.tangentialGradient g x‖ + g x * ‖H x‖) ∂V.weight :=
      setIntegral_nonneg measurableSet_closedBall fun x _ ↦ hφ0 x
    rw [Real.norm_of_nonneg (div_nonneg hΦ0 (pow_nonneg hτ0.le n))]
    exact div_le_div₀ (integral_nonneg hφ0) (setIntegral_le_integral hφ (ae_of_all _ hφ0))
      (pow_pos hs n) (pow_le_pow_left₀ hs.le hτ.1.le n)
  -- The annulus term of (W) is nonnegative.
  have hA : 0 ≤ ∫ x in closedBall ζ r \ closedBall ζ s,
      g x * (V.normalRadialSq ζ x / ‖x - ζ‖ ^ n) ∂V.weight :=
    integral_nonneg fun x ↦ mul_nonneg (hg0 x)
      (div_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _)) (pow_nonneg (norm_nonneg _) n))
  -- Cauchy–Schwarz on `B_τ(ζ)`: `-L(τ)/τ^{n+1} ≤ |L(τ)|/τ^{n+1} ≤ Φ(τ)/τⁿ` for `τ ∈ (s, r]`.
  have hbound : ∀ τ ∈ Ioc s r,
      -((∫ x in closedBall ζ τ, inner ℝ (x - ζ) (V.tangentialGradient g x + g x • H x)
          ∂V.weight) / τ ^ (n + 1)) ≤
        (∫ x in closedBall ζ τ, (‖V.tangentialGradient g x‖ + g x * ‖H x‖) ∂V.weight) /
          τ ^ n := by
    intro τ hτ
    have hτ0 : 0 < τ := hs.trans hτ.1
    have hL : ‖∫ x in closedBall ζ τ, inner ℝ (x - ζ) (V.tangentialGradient g x + g x • H x)
        ∂V.weight‖ ≤
        τ * ∫ x in closedBall ζ τ, (‖V.tangentialGradient g x‖ + g x * ‖H x‖) ∂V.weight := by
      rw [← integral_const_mul]
      refine norm_integral_le_of_norm_le (hφ.const_mul τ).integrableOn
        (ae_restrict_of_forall_mem measurableSet_closedBall fun x hx ↦ ?_)
      calc ‖inner ℝ (x - ζ) (V.tangentialGradient g x + g x • H x)‖
          ≤ ‖x - ζ‖ * ‖V.tangentialGradient g x + g x • H x‖ := norm_inner_le_norm _ _
        _ ≤ τ * (‖V.tangentialGradient g x‖ + g x * ‖H x‖) := by
          refine mul_le_mul (mem_closedBall_iff_norm.mp hx)
            ((norm_add_le _ _).trans_eq ?_) (norm_nonneg _) hτ0.le
          rw [norm_smul, Real.norm_of_nonneg (hg0 x)]
    have hτn : 0 < τ ^ (n + 1) := pow_pos hτ0 _
    calc -((∫ x in closedBall ζ τ, inner ℝ (x - ζ) (V.tangentialGradient g x + g x • H x)
          ∂V.weight) / τ ^ (n + 1))
        ≤ ‖∫ x in closedBall ζ τ, inner ℝ (x - ζ) (V.tangentialGradient g x + g x • H x)
          ∂V.weight‖ / τ ^ (n + 1) := by
          rw [← neg_div, Real.norm_eq_abs]
          exact div_le_div_of_nonneg_right (neg_le_abs _) hτn.le
      _ ≤ (τ * ∫ x in closedBall ζ τ, (‖V.tangentialGradient g x‖ + g x * ‖H x‖) ∂V.weight) /
          τ ^ (n + 1) := div_le_div_of_nonneg_right hL hτn.le
      _ = (∫ x in closedBall ζ τ, (‖V.tangentialGradient g x‖ + g x * ‖H x‖) ∂V.weight) /
          τ ^ n := by rw [pow_succ', mul_div_mul_left _ _ hτ0.ne']
  -- Integrate the bound over `(s, r]` and rearrange (W).
  have hJ : ∫ τ in Ioc s r, -((∫ x in closedBall ζ τ, inner ℝ (x - ζ)
        (V.tangentialGradient g x + g x • H x) ∂V.weight) / τ ^ (n + 1)) ≤
      ∫ τ in Ioc s r, (∫ x in closedBall ζ τ, (‖V.tangentialGradient g x‖ + g x * ‖H x‖)
        ∂V.weight) / τ ^ n :=
    setIntegral_mono_on hLint.neg hΦint measurableSet_Ioc hbound
  rw [integral_neg] at hJ
  linarith
/-- **Simon 5.7, proof (p. 99): good balls and the 5-times covering, `n ≥ 2`.** Let `μ` be finite
on compact sets, `g ≥ 0` continuous with compact support and `φ ≥ 0` `μ`-integrable, such that
`s⁻ⁿ∫_{B_s(ζ)} g ≤ r⁻ⁿ∫_{B_r(ζ)} g + ∫_{(s,r]} τ⁻ⁿ∫_{B_τ(ζ)} φ dτ` for `0 < s ≤ r`, and
`μ(B_ρ(ζ))/(ωₙρⁿ) → t ≥ 1` at `μ`-a.e. `ζ` with `g(ζ) ≥ 1`. Then
`∫_{g ≥ 1} g dμ ≤ 5ⁿωₙ^{-1/n}(∫ g dμ)^{1/n} ∫ φ dμ`. At such `ζ` the good-radius lemma for
`f(τ) = ωₙ⁻¹∫_{B_τ(ζ)} g` and `k(τ) = ωₙ⁻¹∫_{B_τ(ζ)} φ` gives `r_ζ < 2(ωₙ⁻¹∫ g)^{1/n}` with
`∫_{B_{5r_ζ}(ζ)} g ≤ 5ⁿωₙ^{-1/n}(∫ g)^{1/n} ∫_{B_{r_ζ}(ζ)} φ` (Simon's (1)); the covering lemma
(Ch. 1, 3.4) selects countably many disjoint `B_{r_b}(b)` whose dilates `B_{5r_b}(b)` cover
`{g ≥ 1}` up to a null set, and summing (1) over them gives the claim. -/
theorem Submission.sobolev_covering_inequality : ∀ (n ℓ : ℕ) (μ : Measure (Ambient n ℓ))
    (g φ : Ambient n ℓ → ℝ), 2 ≤ n → IsFiniteMeasureOnCompacts μ → Continuous g →
    HasCompactSupport g → (∀ x, 0 ≤ g x) → (∀ x, 0 ≤ φ x) → Integrable φ μ →
    (∀ (ζ : Ambient n ℓ) (s r : ℝ), 0 < s → s ≤ r →
      (∫ x in closedBall ζ s, g x ∂μ) / s ^ n ≤ (∫ x in closedBall ζ r, g x ∂μ) / r ^ n +
        ∫ τ in Ioc s r, (∫ x in closedBall ζ τ, φ x ∂μ) / τ ^ n) →
    (∀ᵐ ζ ∂μ, 1 ≤ g ζ → ∃ t : ℝ, 1 ≤ t ∧
      Tendsto (fun ρ ↦ μ.real (closedBall ζ ρ) / (omega n * ρ ^ n)) (𝓝[>] 0) (𝓝 t)) →
    ∫ x in {x | 1 ≤ g x}, g x ∂μ ≤
      5 ^ n * omega n ^ (-(n : ℝ)⁻¹) * (∫ x, g x ∂μ) ^ (n : ℝ)⁻¹ * ∫ x, φ x ∂μ := by
  intro n ℓ μ g φ hn hμ hgc hgs hg0 hφ0 hφi hmono hdens
  -- Step 1: `Γ = ∫ g`, `F = ωₙ⁻¹Γ` and the constant `K = 5ⁿF^{1/n} = 5ⁿωₙ^{-1/n}Γ^{1/n}`.
  have hgi : Integrable g μ := hgc.integrable_of_hasCompactSupport hgs
  have hω : 0 < omega n := by
    unfold omega
    exact ENNReal.toReal_pos (measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne
  have hωi : 0 ≤ (omega n)⁻¹ := inv_nonneg.2 hω.le
  set Γ : ℝ := ∫ x, g x ∂μ
  have hΓ0 : 0 ≤ Γ := integral_nonneg hg0
  set F : ℝ := (omega n)⁻¹ * Γ with hF
  set K : ℝ := 5 ^ n * omega n ^ (-(n : ℝ)⁻¹) * Γ ^ (n : ℝ)⁻¹ with hK
  have hFK : 5 ^ n * F ^ (n : ℝ)⁻¹ = K := by
    rw [hF, hK, Real.mul_rpow hωi hΓ0, Real.inv_rpow hω.le, ← Real.rpow_neg hω.le, mul_assoc]
  have hK0 : 0 ≤ K := by
    rw [hK]
    have h1 : 0 ≤ omega n ^ (-(n : ℝ)⁻¹) := Real.rpow_nonneg hω.le _
    have h2 : 0 ≤ Γ ^ (n : ℝ)⁻¹ := Real.rpow_nonneg hΓ0 _
    positivity
  set A : Set (Ambient n ℓ) := {x | 1 ≤ g x}
  have hA : MeasurableSet A := measurableSet_le measurable_const hgc.measurable
  -- Step 2: at `μ`-a.e. `ζ ∈ A`, the good-radius lemma for `f(τ) = ωₙ⁻¹∫_{B_τ(ζ)} g` and
  -- `k(τ) = ωₙ⁻¹∫_{B_τ(ζ)} φ` gives `r ∈ (0, 2F^{1/n})` with `∫_{B_{5r}(ζ)} g ≤ K∫_{B_r(ζ)} φ`.
  have hgood : ∀ᵐ ζ ∂μ, ζ ∈ A → ∃ r : ℝ, 0 < r ∧ r ≤ 2 * F ^ (n : ℝ)⁻¹ ∧
      ∫ x in closedBall ζ (5 * r), g x ∂μ ≤ K * ∫ x in closedBall ζ r, φ x ∂μ := by
    filter_upwards [hdens] with ζ hζ hgζ
    replace hgζ : 1 ≤ g ζ := hgζ
    obtain ⟨t, ht1, htend⟩ := hζ hgζ
    -- (a), (b): `f` and `k` are nondecreasing, `0 ≤ f ≤ F` and `0 ≤ k`.
    have hfm : MonotoneOn (fun τ ↦ (omega n)⁻¹ * ∫ x in closedBall ζ τ, g x ∂μ) (Ioi 0) :=
      fun a _ b _ hab ↦ mul_le_mul_of_nonneg_left (setIntegral_mono_set hgi.integrableOn
        (ae_of_all _ fun x ↦ hg0 x) (closedBall_subset_closedBall hab).eventuallyLE) hωi
    have hkm : MonotoneOn (fun τ ↦ (omega n)⁻¹ * ∫ x in closedBall ζ τ, φ x ∂μ) (Ioi 0) :=
      fun a _ b _ hab ↦ mul_le_mul_of_nonneg_left (setIntegral_mono_set hφi.integrableOn
        (ae_of_all _ fun x ↦ hφ0 x) (closedBall_subset_closedBall hab).eventuallyLE) hωi
    have hfb : ∀ τ : ℝ, 0 < τ → 0 ≤ (omega n)⁻¹ * (∫ x in closedBall ζ τ, g x ∂μ) ∧
        (omega n)⁻¹ * (∫ x in closedBall ζ τ, g x ∂μ) ≤ F := fun τ _ ↦
      ⟨mul_nonneg hωi (setIntegral_nonneg measurableSet_closedBall fun x _ ↦ hg0 x),
        mul_le_mul_of_nonneg_left (setIntegral_le_integral hgi (ae_of_all _ hg0)) hωi⟩
    have hkb : ∀ τ : ℝ, 0 < τ → 0 ≤ (omega n)⁻¹ * ∫ x in closedBall ζ τ, φ x ∂μ := fun τ _ ↦
      mul_nonneg hωi (setIntegral_nonneg measurableSet_closedBall fun x _ ↦ hφ0 x)
    -- (c): the hypothesis at `ζ`, multiplied by `ωₙ⁻¹`.
    have hint : ∀ s r : ℝ, 0 < s → s ≤ r →
        (omega n)⁻¹ * (∫ x in closedBall ζ s, g x ∂μ) / s ^ n ≤
          (omega n)⁻¹ * (∫ x in closedBall ζ r, g x ∂μ) / r ^ n +
            ∫ τ in Ioc s r, (omega n)⁻¹ * (∫ x in closedBall ζ τ, φ x ∂μ) / τ ^ n := by
      intro s r hs hsr
      have h := mul_le_mul_of_nonneg_left (hmono ζ s r hs hsr) hωi
      simp_rw [mul_div_assoc]
      rw [integral_const_mul, ← mul_add]
      exact h
    -- (d): for `η < 1`, `f(s)/sⁿ > η` for all small `s > 0`.
    have hlow : ∀ η : ℝ, η < 1 →
        ∃ᶠ s in 𝓝[>] (0 : ℝ), η < (omega n)⁻¹ * (∫ x in closedBall ζ s, g x ∂μ) / s ^ n := by
      intro η hη
      refine Eventually.frequently ?_
      rcases lt_or_ge η 0 with hη0 | hη0
      · filter_upwards [self_mem_nhdsWithin] with s hs
        have hs0 : (0 : ℝ) < s := hs
        have hI : 0 ≤ ∫ x in closedBall ζ s, g x ∂μ :=
          setIntegral_nonneg measurableSet_closedBall fun x _ ↦ hg0 x
        have : 0 ≤ (omega n)⁻¹ * (∫ x in closedBall ζ s, g x ∂μ) / s ^ n := by positivity
        linarith
      · -- With `η₁ = (1 + η)/2`: `g ≥ η₁` near `ζ`, and the density quotient tends to `t > η/η₁`.
        set η₁ : ℝ := (1 + η) / 2 with hη₁
        have hη₁pos : 0 < η₁ := by rw [hη₁]; linarith
        have hη₁g : η₁ < g ζ := by rw [hη₁]; linarith
        have hcont : ∀ᶠ x in 𝓝 ζ, η₁ < g x := hgc.continuousAt.eventually (lt_mem_nhds hη₁g)
        obtain ⟨δ, hδ, hδball⟩ := Metric.eventually_nhds_iff_ball.1 hcont
        have hlt : η / η₁ < t := by
          rw [div_lt_iff₀ hη₁pos, hη₁]
          nlinarith
        have hratio : ∀ᶠ s in 𝓝[>] (0 : ℝ),
            η / η₁ < μ.real (closedBall ζ s) / (omega n * s ^ n) :=
          htend.eventually (lt_mem_nhds hlt)
        have hsmall : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < δ := nhdsWithin_le_nhds (Iio_mem_nhds hδ)
        filter_upwards [hratio, hsmall, self_mem_nhdsWithin] with s hs1 hs2 hs3
        have hs0 : (0 : ℝ) < s := hs3
        have hsn : (0 : ℝ) < s ^ n := pow_pos hs0 n
        have hgint : IntegrableOn g (closedBall ζ s) μ :=
          hgc.continuousOn.integrableOn_compact (isCompact_closedBall ζ s)
        have hge : η₁ * μ.real (closedBall ζ s) ≤ ∫ x in closedBall ζ s, g x ∂μ :=
          setIntegral_ge_of_const_le_real measurableSet_closedBall measure_closedBall_lt_top.ne
            (fun x hx ↦ (hδball x (closedBall_subset_ball hs2 hx)).le) hgint
        calc η = η₁ * (η / η₁) := by field_simp
          _ < η₁ * (μ.real (closedBall ζ s) / (omega n * s ^ n)) :=
              mul_lt_mul_of_pos_left hs1 hη₁pos
          _ = (omega n)⁻¹ * (η₁ * μ.real (closedBall ζ s)) / s ^ n := by field_simp
          _ ≤ (omega n)⁻¹ * (∫ x in closedBall ζ s, g x ∂μ) / s ^ n := by gcongr
    obtain ⟨_, r, hr0, hrR, hr⟩ := Submission.sobolev_good_radius_calculus n
      (fun τ ↦ (omega n)⁻¹ * ∫ x in closedBall ζ τ, g x ∂μ)
      (fun τ ↦ (omega n)⁻¹ * ∫ x in closedBall ζ τ, φ x ∂μ) F hn hfm hkm hfb hkb hint hlow
    refine ⟨r, hr0, hrR.le, ?_⟩
    -- Multiply `f(5r) ≤ 5ⁿF^{1/n}k(r)` by `ωₙ`.
    have h2 := mul_le_mul_of_nonneg_left hr hω.le
    have hωω : omega n * (omega n)⁻¹ = 1 := mul_inv_cancel₀ hω.ne'
    calc ∫ x in closedBall ζ (5 * r), g x ∂μ
        = omega n * ((omega n)⁻¹ * ∫ x in closedBall ζ (5 * r), g x ∂μ) := by
          rw [← mul_assoc, hωω, one_mul]
      _ ≤ omega n * (5 ^ n * F ^ (n : ℝ)⁻¹ * ((omega n)⁻¹ * ∫ x in closedBall ζ r, φ x ∂μ)) := h2
      _ = K * ∫ x in closedBall ζ r, φ x ∂μ := by
          rw [hFK, mul_left_comm, ← mul_assoc (omega n), hωω, one_mul]
  -- Step 3: a measurable null set `N` containing the points of `A` without a good radius.
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp hgood)
  have hgood' : ∀ ζ ∈ A \ N, ∃ r : ℝ, 0 < r ∧ r ≤ 2 * F ^ (n : ℝ)⁻¹ ∧
      ∫ x in closedBall ζ (5 * r), g x ∂μ ≤ K * ∫ x in closedBall ζ r, φ x ∂μ := by
    intro ζ hζ
    by_contra hbad
    exact hζ.2 (hNsub fun h ↦ hbad (h hζ.1))
  choose! r hr0 hrR hrb using hgood'
  -- Step 4: Vitali's lemma gives a disjoint subfamily `D` of the balls `B_{r_ζ}(ζ)`, `ζ ∈ A \ N`,
  -- whose dilates `B_{5r_b}(b)` cover `A \ N`; `D` is countable as `Ambient n ℓ` is separable.
  obtain ⟨D, hDA, hdisj, hcov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall
    (A \ N) id r (2 * F ^ (n : ℝ)⁻¹) hrR 5 (by norm_num)
  have hDc : D.Countable := hdisj.countable_of_nonempty_interior fun x hx ↦
    (nonempty_ball.mpr (hr0 x (hDA hx))).mono ball_subset_interior_closedBall
  have : Countable D := hDc.to_subtype
  have hcover : A \ N ⊆ ⋃ b : D, closedBall b.val (5 * r b) := by
    intro a ha
    obtain ⟨b, hb, hab⟩ := hcov a ha
    exact mem_iUnion.mpr ⟨⟨b, hb⟩, hab (mem_closedBall_self (hr0 a ha).le)⟩
  have hdisj' : Pairwise fun b c : D ↦ Disjoint (closedBall b.val (r b)) (closedBall c.val (r c)) :=
    fun b c hbc ↦ hdisj b.property c.property (Subtype.coe_ne_coe.mpr hbc)
  -- Step 5: sum the good-ball inequalities with the finite measures `g μ` and `φ μ`.
  set νg : Measure (Ambient n ℓ) := μ.withDensity fun x ↦ ENNReal.ofReal (g x) with hνg
  set νφ : Measure (Ambient n ℓ) := μ.withDensity fun x ↦ ENNReal.ofReal (φ x) with hνφ
  have hconvg : ∀ S, MeasurableSet S → ENNReal.ofReal (∫ x in S, g x ∂μ) = νg S := fun S hS ↦ by
    rw [hνg, withDensity_apply _ hS]
    exact ofReal_integral_eq_lintegral_ofReal hgi.integrableOn (ae_of_all _ fun x ↦ hg0 x)
  have hconvφ : ∀ S, MeasurableSet S → ENNReal.ofReal (∫ x in S, φ x ∂μ) = νφ S := fun S hS ↦ by
    rw [hνφ, withDensity_apply _ hS]
    exact ofReal_integral_eq_lintegral_ofReal hφi.integrableOn (ae_of_all _ fun x ↦ hφ0 x)
  have hball : ∀ b ∈ D,
      νg (closedBall b (5 * r b)) ≤ ENNReal.ofReal K * νφ (closedBall b (r b)) := by
    intro b hb
    rw [← hconvg _ measurableSet_closedBall, ← hconvφ _ measurableSet_closedBall,
      ← ENNReal.ofReal_mul hK0]
    exact ENNReal.ofReal_le_ofReal (hrb b (hDA hb))
  have hN : νg N = 0 := by
    rw [hνg, withDensity_apply _ hNm, Measure.restrict_eq_zero.mpr hN0, lintegral_zero_measure]
  have hsum : νg A ≤ ENNReal.ofReal K * νφ univ :=
    calc νg A ≤ νg (A \ N ∪ N) := measure_mono fun x hx ↦ by
            by_cases hxN : x ∈ N
            · exact Or.inr hxN
            · exact Or.inl ⟨hx, hxN⟩
      _ ≤ νg (A \ N) + νg N := measure_union_le _ _
      _ = νg (A \ N) := by rw [hN, add_zero]
      _ ≤ νg (⋃ b : D, closedBall b.val (5 * r b)) := measure_mono hcover
      _ ≤ ∑' b : D, νg (closedBall b.val (5 * r b)) := measure_iUnion_le _
      _ ≤ ∑' b : D, ENNReal.ofReal K * νφ (closedBall b.val (r b)) :=
          ENNReal.tsum_le_tsum fun b ↦ hball b.val b.property
      _ = ENNReal.ofReal K * ∑' b : D, νφ (closedBall b.val (r b)) := ENNReal.tsum_mul_left
      _ = ENNReal.ofReal K * νφ (⋃ b : D, closedBall b.val (r b)) := by
          rw [measure_iUnion hdisj' fun _ ↦ measurableSet_closedBall]
      _ ≤ ENNReal.ofReal K * νφ univ := by gcongr; exact subset_univ _
  rw [← hconvg A hA, ← hconvφ univ MeasurableSet.univ, setIntegral_univ,
    ← ENNReal.ofReal_mul hK0] at hsum
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hK0 (integral_nonneg hφ0))).1 hsum

/-- **Sobolev inequality from the superlevel inequality (Simon Ch. 4, 5.7–5.9, Steps 5–6, with
4.11).** Let `n ≥ 2`, let `μ_V` be finite on compact sets with `x ↦ p_{T_x V}` `μ_V`-a.e. strongly
measurable, `U` open, `H` locally `μ_V`-integrable on `U` and `C ≥ 0`. If every nonnegative
`g ∈ C¹(U)` with compact support in `U` satisfies
`∫_{g ≥ 1} g dμ_V ≤ C (∫ g dμ_V)^{1/n} ∫ (|∇^M g| + g|H|) dμ_V`, then every nonnegative
`h ∈ C¹(U)` with compact support in `U` satisfies
`(∫ h^{n/(n-1)} dμ_V)^{(n-1)/n} ≤ (n/(n-1)) C ∫ (|∇^M h| + h|H|) dμ_V`. -/
theorem Submission.sobolev_of_superlevel_inequality : ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)) (H : Ambient n ℓ → Ambient n ℓ) (h : Ambient n ℓ → ℝ) (C : ℝ), 2 ≤ n → IsFiniteMeasureOnCompacts V.weight → AEStronglyMeasurable (fun x ↦ (V.tangentSpace x).starProjection) V.weight → IsOpen U → LocallyIntegrableOn H U V.weight → 0 ≤ C → (∀ g : Ambient n ℓ → ℝ, ContDiffOn ℝ 1 g U → HasCompactSupport g → tsupport g ⊆ U → (∀ x, 0 ≤ g x) → ∫ x in {x | 1 ≤ g x}, g x ∂V.weight ≤ C * (∫ x, g x ∂V.weight) ^ (n : ℝ)⁻¹ * ∫ x, (‖V.tangentialGradient g x‖ + g x * ‖H x‖) ∂V.weight) → ContDiffOn ℝ 1 h U → HasCompactSupport h → tsupport h ⊆ U → (∀ x, 0 ≤ h x) → (∫ x, h x ^ ((n : ℝ) / ((n : ℝ) - 1)) ∂V.weight) ^ (((n : ℝ) - 1) / n) ≤ (n : ℝ) / ((n : ℝ) - 1) * C * ∫ x, (‖V.tangentialGradient h x‖ + h x * ‖H x‖) ∂V.weight := by
  intro n ℓ V U H h C hn hfin hproj hU hH hC hsup hh hhc hhU hh0
  -- (1) `h ∈ C¹(ℝ^{n+ℓ})`, `|∇^M h|` is `μ_V`-integrable, and `|H|` is integrable on the compact
  -- set `tsupport h ⊆ U`.
  obtain ⟨hC1, -, hgrad, -⟩ :=
    Submission.sobolev_energy_integrable n ℓ V U H h hfin hproj hU hH hh hhc hhU
  have hHK : IntegrableOn (fun x ↦ ‖H x‖) (tsupport h) V.weight :=
    (hH.integrableOn_compact_subset hhU hhc).norm
  -- (7)–(8) Letting `ε ↓ 0`, it suffices to prove the level-integral bound for each `ε ∈ (0, 1]`,
  -- with `J = ∫ (|∇^M h| + h|H|) dμ_V ≥ 0`.
  refine Submission.sobolev_of_level_integral_bounds n ℓ V.weight h C _ hn hfin hC1.continuous hhc
    hh0 hC (integral_nonneg fun x ↦ add_nonneg (norm_nonneg _) (mul_nonneg (hh0 x) (norm_nonneg _)))
    fun ε hε _ ↦ ?_
  -- (2) The cut-off `γ(s) = ψ(s/ε)`, `ψ = Real.smoothTransition`: `C¹`, nondecreasing, with
  -- values in `[0, 1]`, `γ = 0` on `(-∞, 0]` and `γ = 1` on `[ε, ∞)`.
  let γ : ℝ → ℝ := fun s ↦ Real.smoothTransition (s / ε)
  have hγC1 : ContDiff ℝ 1 γ := Real.smoothTransition.contDiff.comp (contDiff_id.div_const ε)
  have hγmono : Monotone γ := fun a b hab ↦
    Real.smoothTransition.monotone (div_le_div_of_nonneg_right hab hε.le)
  have hγbd : ∀ s, 0 ≤ γ s ∧ γ s ≤ 1 := fun s ↦
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hγ0 : ∀ s, s ≤ 0 → γ s = 0 := fun s hs ↦
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hs hε.le)
  have hγ1 : ∀ s, ε ≤ s → γ s = 1 := fun s hs ↦
    Real.smoothTransition.one_of_one_le ((one_le_div hε).2 hs)
  -- (3)–(6) The superlevel inequality for the truncations `γ(h - t)`, `t ≥ 0`, integrated over
  -- the levels `t` (with `D = |∇^M h|` and `K = |H|`).
  exact Submission.sobolev_level_integral_bound n ℓ V.weight h (fun x ↦ ‖V.tangentialGradient h x‖)
    (fun x ↦ ‖H x‖) γ C ε hn hfin hC1.continuous hhc hh0 (fun _ ↦ norm_nonneg _) hgrad
    (fun _ ↦ norm_nonneg _) hHK hγC1 hγmono hγbd hγ0 hC hε fun t ht ↦
      Submission.sobolev_truncation_superlevel_bound n ℓ V U H h γ C ε t hfin hH hC hsup hC1 hhc
        hhU hh0 hgrad hγC1 hγmono hγbd hγ0 hε hγ1 ht
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
/-- **Cutoff, radial profile and radial test field outside a ball** (Simon Ch. 4, 6.1, proof
steps 2–4). A bump function `ζ` centred at `ξ` is `1` near the compact set `K`; the profile
`γ(t) = g(t² - (R + ε)²)`, `g = expNegInvGlue`, vanishes on `[0, R + ε]`, is positive beyond and
nondecreasing on `[0, ∞)`; and `X(x) = (ζ(x)γ(|x - ξ|))(x - ξ)` is a `C¹` field with compact
support in `ℝ^{n+ℓ} \ B_R(ξ)` (`γ(|x - ξ|) = g(|x - ξ|² - (R + ε)²)` is smooth even at `ξ`). -/
theorem Submission.exists_radial_cutoff_test_field : ∀ (n ℓ : ℕ) (K : Set (Ambient n ℓ)) (ξ : Ambient n ℓ) (R ε : ℝ), IsCompact K → 0 ≤ R → 0 < ε → ∃ (ζ : Ambient n ℓ → ℝ) (γ : ℝ → ℝ), ContDiff ℝ 1 ζ ∧ (∀ x ∈ K, ζ x = 1 ∧ gradient ζ x = 0) ∧ ContDiff ℝ 1 γ ∧ (∀ t : ℝ, 0 ≤ t → 0 ≤ γ t ∧ 0 ≤ deriv γ t) ∧ (∀ t : ℝ, 0 ≤ t → t ≤ R + ε → γ t = 0) ∧ (∀ t : ℝ, R + ε < t → 0 < γ t) ∧ IsTestField (closedBall ξ R)ᶜ (fun x ↦ (ζ x * γ ‖x - ξ‖) • (x - ξ)) := by
  intro n ℓ K ξ R ε hK hR hε
  -- step 1: `K ⊆ W = B(ξ, ρ₀)` with `ρ₀ = |ρ| + 1 > 0`
  obtain ⟨ρ, hρ⟩ := hK.isBounded.subset_ball ξ
  have hρ₀ : 0 < |ρ| + 1 := by positivity
  have hKW : K ⊆ ball ξ (|ρ| + 1) := hρ.trans (ball_subset_ball (by linarith [le_abs_self ρ]))
  -- step 2: `ζ` is the bump function at `ξ` with `rIn = ρ₀`, `rOut = ρ₀ + 1`
  let f : ContDiffBump ξ := ⟨|ρ| + 1, |ρ| + 2, hρ₀, by linarith⟩
  -- steps 4 and 6: `γ(t) = g(t² - (R + ε)²)` vanishes for `0 ≤ t ≤ R + ε`
  have hc : 0 < R + ε := by linarith
  have hzero : ∀ t : ℝ, 0 ≤ t → t ≤ R + ε → expNegInvGlue (t ^ 2 - (R + ε) ^ 2) = 0 :=
    fun t ht htc ↦ expNegInvGlue.zero_of_nonpos (by nlinarith)
  refine ⟨f, fun t ↦ expNegInvGlue (t ^ 2 - (R + ε) ^ 2), f.contDiff, fun x hx ↦ ?_,
    expNegInvGlue.contDiff.comp ((contDiff_id.pow 2).sub contDiff_const), fun t ht ↦ ?_, hzero,
    fun t ht ↦ expNegInvGlue.pos_of_pos (by nlinarith), ?_, ?_, ?_⟩
  · -- step 3: `ζ ≡ 1` on a neighbourhood of `x ∈ K`, so `ζ(x) = 1` and `∇ζ(x) = 0`
    have h1 : (f : Ambient n ℓ → ℝ) =ᶠ[𝓝 x] fun _ ↦ 1 := f.eventuallyEq_one_of_mem_ball (hKW hx)
    exact ⟨h1.eq_of_nhds, h1.gradient_eq.trans (gradient_fun_const x 1)⟩
  · -- step 5: `γ'(t) = g'(t² - (R + ε)²) · 2t` with `g' ≥ 0` since `g` is monotone
    refine ⟨expNegInvGlue.nonneg _, ?_⟩
    have hin : HasDerivAt (fun t : ℝ ↦ t ^ 2 - (R + ε) ^ 2) (2 * t) t := by
      simpa using (hasDerivAt_pow 2 t).sub_const ((R + ε) ^ 2)
    have hg : HasDerivAt expNegInvGlue (deriv expNegInvGlue (t ^ 2 - (R + ε) ^ 2))
        (t ^ 2 - (R + ε) ^ 2) :=
      ((expNegInvGlue.contDiff (n := 1)).differentiable one_ne_zero _).hasDerivAt
    have hd := hg.comp t hin
    rw [Function.comp_def] at hd
    rw [hd.deriv]
    exact mul_nonneg expNegInvGlue.monotone.deriv_nonneg (by linarith)
  · -- step 8: `x ↦ γ(|x - ξ|) = g(|x - ξ|² - (R + ε)²)` is smooth, hence `X` is `C¹`
    have hγ : ContDiff ℝ 1 fun x : Ambient n ℓ ↦ expNegInvGlue (‖x - ξ‖ ^ 2 - (R + ε) ^ 2) :=
      expNegInvGlue.contDiff.comp (((contDiff_id.sub contDiff_const).norm_sq ℝ).sub contDiff_const)
    exact (f.contDiff.mul hγ).smul (contDiff_id.sub contDiff_const)
  · -- step 9: `supp X ⊆ supp ζ`, which is compact
    exact f.hasCompactSupport.mono fun x hx hfx ↦ hx (by simp [hfx])
  · -- step 10: `supp X ⊆ {|x - ξ| ≥ R + ε}`, a closed set inside `(B_R(ξ))ᶜ`
    have hcl : IsClosed {x : Ambient n ℓ | R + ε ≤ ‖x - ξ‖} :=
      isClosed_le continuous_const (continuous_id.sub continuous_const).norm
    refine (closure_minimal (fun x hx ↦ ?_) hcl).trans fun x hx ↦ ?_
    · by_contra hlt
      exact hx (by simp [hzero ‖x - ξ‖ (norm_nonneg _) (not_le.1 hlt).le])
    · simp only [mem_compl_iff, mem_closedBall, dist_eq_norm, not_le]
      exact lt_of_lt_of_le (by linarith) hx
/-- **Measurability and unit bounds of `|D^⊥r|²` (Simon Ch. 4, 6.1, step 7(b); cf. 3.2–3.3).**
If `x ↦ p_{T_x V}` is `μ_V`-a.e. strongly measurable, then so is
`q(x) = |p_{(T_x V)^⊥}(x - ξ)|² / |x - ξ|²` (`q(ξ) = 0 / 0 = 0`), and `0 ≤ q ≤ 1` everywhere. -/
theorem Submission.aestronglyMeasurable_normalRadialSq_and_bounds : (∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (ξ : Ambient n ℓ), AEStronglyMeasurable (fun x ↦ (V.tangentSpace x).starProjection) V.weight → AEStronglyMeasurable (fun x ↦ V.normalRadialSq ξ x) V.weight ∧ ∀ x, 0 ≤ V.normalRadialSq ξ x ∧ V.normalRadialSq ξ x ≤ 1) := by
  intro n ℓ V ξ hP
  -- `p_{(T_x V)^⊥} = 1 - p_{T_x V}`, so `x ↦ p_{(T_x V)^⊥}` is a.e. strongly measurable.
  have hQ : AEStronglyMeasurable (fun x ↦ (V.tangentSpace x)ᗮ.starProjection) V.weight := by
    simp_rw [Submodule.starProjection_orthogonal']
    exact aestronglyMeasurable_const.sub hP
  -- Evaluation `(L, v) ↦ L v` is continuous bilinear, and `x ↦ x - ξ` is continuous.
  have hQv : AEStronglyMeasurable (fun x ↦ (V.tangentSpace x)ᗮ.starProjection (x - ξ)) V.weight :=
    (ContinuousLinearMap.id ℝ (Ambient n ℓ →L[ℝ] Ambient n ℓ)).aestronglyMeasurable_comp₂
      (f := fun x ↦ (V.tangentSpace x)ᗮ.starProjection) (g := fun x ↦ x - ξ) hQ
      (continuous_id.sub continuous_const).aestronglyMeasurable
  -- `x ↦ (|x - ξ|²)⁻¹` is Borel measurable, and `ℝ` is second countable.
  have hden : AEStronglyMeasurable (fun x : Ambient n ℓ ↦ (‖x - ξ‖ ^ 2)⁻¹) V.weight :=
    ((continuous_id.sub continuous_const).norm.pow 2).measurable.inv.aestronglyMeasurable
  refine ⟨?_, fun x ↦ ⟨?_, ?_⟩⟩
  · -- `a / b = a * b⁻¹` for all real `a, b` (also for `b = 0`).
    simp only [RectifiableVarifold.normalRadialSq, div_eq_mul_inv]
    exact (hQv.norm.pow 2).mul hden
  · exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  · -- `|p_{(T_x V)^⊥} v| ≤ |v|`; `a / b ≤ 1` needs only `a ≤ b` and `0 ≤ b`.
    exact div_le_one_of_le₀
      (pow_le_pow_left₀ (norm_nonneg _) (Submodule.norm_starProjection_apply_le _ _) 2)
      (sq_nonneg _)
/-- Positivity argument of Simon 6.1 (p. 100), for an abstract measure `μ` and weight `q` (applied
with `μ = μ_V` and `q = |D^⊥r|²`). Let `μ` be finite on compact sets with compact support,
`U = ℝ^{n+ℓ} \ B_R(ξ)`, `r = |x - ξ|`, `H` locally `μ`-integrable on `U` with `|H · (x - ξ)| < n`
`μ`-a.e. in `U`, `q` a.e. strongly measurable with `0 ≤ q ≤ 1`, and `γ ∈ C¹` with `γ, γ' ≥ 0` on
`[0, ∞)`, `γ = 0` on `[0, R + ε]` and `γ > 0` on `(R + ε, ∞)`. If
`∫_U (nγ(r) + rγ'(r)(1 - q)) dμ = -∫_U γ(r)(x - ξ) · H dμ`, then `spt μ ⊆ B_{R+ε}(ξ)`.
Both integrands are integrable (`μ` is finite and the left one is bounded on `spt μ`; the right one
vanishes off the compact `spt μ ∩ {r ≥ R + ε} ⊆ U`, on which `H` is integrable), so
`∫_U (F + G) dμ = 0` with `F + G ≥ γ(r)(n - |(x - ξ) · H|) ≥ 0` `μ`-a.e. in `U`; hence `γ(r) = 0`
`μ`-a.e. in `U`, and the open set `{r > R + ε} ⊆ U` is `μ`-null, so it misses `spt μ`. -/
theorem Submission.support_subset_closedBall_of_radial_identity : ∀ (n ℓ : ℕ) (μ : Measure (Ambient n ℓ)) (H : Ambient n ℓ → Ambient n ℓ) (q : Ambient n ℓ → ℝ) (γ : ℝ → ℝ) (ξ : Ambient n ℓ) (R ε : ℝ), 0 < n → 0 ≤ R → 0 < ε → IsFiniteMeasureOnCompacts μ → IsCompact μ.support → LocallyIntegrableOn H (closedBall ξ R)ᶜ μ → AEStronglyMeasurable q μ → (∀ x, 0 ≤ q x ∧ q x ≤ 1) → ContDiff ℝ 1 γ → (∀ t : ℝ, 0 ≤ t → 0 ≤ γ t ∧ 0 ≤ deriv γ t) → (∀ t : ℝ, 0 ≤ t → t ≤ R + ε → γ t = 0) → (∀ t : ℝ, R + ε < t → 0 < γ t) → (∀ᵐ x ∂μ, x ∈ (closedBall ξ R)ᶜ → |inner ℝ (H x) (x - ξ)| < (n : ℝ)) → ∫ x in (closedBall ξ R)ᶜ, ((n : ℝ) * γ ‖x - ξ‖ + ‖x - ξ‖ * deriv γ ‖x - ξ‖ * (1 - q x)) ∂μ = -∫ x in (closedBall ξ R)ᶜ, γ ‖x - ξ‖ * inner ℝ (x - ξ) (H x) ∂μ → μ.support ⊆ closedBall ξ (R + ε) := by
  intro n ℓ μ H q γ ξ R ε hn hR hε hfin hcpt hHloc hq hq01 hγ hγnn hγ0 hγpos hC hId
  have hUm : MeasurableSet (closedBall ξ R)ᶜ := measurableSet_closedBall.compl
  have hγc : Continuous γ := hγ.continuous
  have hγ'c : Continuous (deriv γ) := hγ.continuous_deriv le_rfl
  have hrc : Continuous fun x : Ambient n ℓ ↦ ‖x - ξ‖ := (continuous_id.sub continuous_const).norm
  have hr0 : ∀ x : Ambient n ℓ, 0 ≤ ‖x - ξ‖ := fun x ↦ norm_nonneg _
  have hmemU : ∀ x : Ambient n ℓ, R < ‖x - ξ‖ → x ∈ (closedBall ξ R)ᶜ := fun x hx ↦ by
    rwa [mem_compl_iff, mem_closedBall, dist_eq_norm, not_le]
  -- step 1: `μ(E \ spt μ) = 0`, so `μ` is a finite measure
  have hae : ∀ᵐ x ∂μ, x ∈ μ.support := Measure.support_mem_ae
  have : IsFiniteMeasure μ := ⟨(measure_univ_le_add_compl μ.support).trans_lt
    (by rw [Measure.measure_compl_support, add_zero]; exact hcpt.measure_lt_top)⟩
  -- steps 2–4: `F = nγ(r) + rγ'(r)(1 - q)` is a.e. strongly measurable and bounded on `spt μ`
  set F : Ambient n ℓ → ℝ := fun x ↦
    (n : ℝ) * γ ‖x - ξ‖ + ‖x - ξ‖ * deriv γ ‖x - ξ‖ * (1 - q x) with hFdef
  set G : Ambient n ℓ → ℝ := fun x ↦ γ ‖x - ξ‖ * inner ℝ (x - ξ) (H x) with hGdef
  have hFlow : ∀ x, (n : ℝ) * γ ‖x - ξ‖ ≤ F x := fun x ↦ by
    have := mul_nonneg (mul_nonneg (hr0 x) (hγnn _ (hr0 x)).2) (sub_nonneg.2 (hq01 x).2)
    simp only [hFdef]
    linarith
  have hFle : ∀ x, F x ≤ (n : ℝ) * γ ‖x - ξ‖ + ‖x - ξ‖ * deriv γ ‖x - ξ‖ := fun x ↦ by
    have := mul_le_of_le_one_right (mul_nonneg (hr0 x) (hγnn _ (hr0 x)).2)
      (sub_le_self 1 (hq01 x).1)
    simp only [hFdef]
    linarith
  have hFnn : ∀ x, 0 ≤ F x := fun x ↦
    (mul_nonneg (Nat.cast_nonneg n) (hγnn _ (hr0 x)).1).trans (hFlow x)
  obtain ⟨C₁, hC₁⟩ := hcpt.exists_bound_of_continuousOn
    (f := fun x : Ambient n ℓ ↦ (n : ℝ) * γ ‖x - ξ‖ + ‖x - ξ‖ * deriv γ ‖x - ξ‖)
    ((continuous_const.mul (hγc.comp hrc)).add (hrc.mul (hγ'c.comp hrc))).continuousOn
  have hFmeas : AEStronglyMeasurable F μ :=
    (continuous_const.mul (hγc.comp hrc)).aestronglyMeasurable.add
      ((hrc.mul (hγ'c.comp hrc)).aestronglyMeasurable.mul (aestronglyMeasurable_const.sub hq))
  have hFint : Integrable F μ := by
    refine Integrable.of_bound hFmeas C₁ ?_
    filter_upwards [hae] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hFnn x)]
    exact (hFle x).trans ((le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC₁ x hx))
  -- step 5: `G = γ(r)(x - ξ) · H` is integrable on `S = spt μ ∩ {r ≥ R + ε} ⊆ U`, and `G = 0`
  -- `μ`-a.e. on `U \ S`
  set S : Set (Ambient n ℓ) := μ.support ∩ {x | R + ε ≤ ‖x - ξ‖}
  have hSc : IsCompact S := hcpt.inter_right (isClosed_le continuous_const hrc)
  have hSU : S ⊆ (closedBall ξ R)ᶜ := fun x hx ↦
    hmemU x (by have : R + ε ≤ ‖x - ξ‖ := hx.2; linarith)
  have hHS : IntegrableOn H S μ := hHloc.integrableOn_compact_subset hSU hSc
  obtain ⟨C₂, hC₂⟩ := hcpt.exists_bound_of_continuousOn
    (f := fun x : Ambient n ℓ ↦ γ ‖x - ξ‖ * ‖x - ξ‖) ((hγc.comp hrc).mul hrc).continuousOn
  have hGmeas : AEStronglyMeasurable G (μ.restrict S) :=
    (hγc.comp hrc).aestronglyMeasurable.mul (continuous_inner.comp_aestronglyMeasurable
      ((continuous_id.sub continuous_const).aestronglyMeasurable.prodMk hHS.aestronglyMeasurable))
  have hGS : IntegrableOn G S μ := by
    refine Integrable.mono' (hHS.norm.const_mul C₂) hGmeas ?_
    filter_upwards [ae_restrict_mem hSc.isClosed.measurableSet] with x hx
    have hg := (hγnn ‖x - ξ‖ (hr0 x)).1
    have hb := hC₂ x hx.1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hg (hr0 x))] at hb
    calc ‖G x‖ = γ ‖x - ξ‖ * |inner ℝ (x - ξ) (H x)| := by
          simp only [hGdef, norm_mul, Real.norm_eq_abs, abs_of_nonneg hg]
      _ ≤ γ ‖x - ξ‖ * (‖x - ξ‖ * ‖H x‖) :=
          mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) hg
      _ = γ ‖x - ξ‖ * ‖x - ξ‖ * ‖H x‖ := by ring
      _ ≤ C₂ * ‖H x‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg _)
  have hGU : IntegrableOn G (closedBall ξ R)ᶜ μ := by
    refine hGS.of_ae_sdiff_eq_zero hUm.nullMeasurableSet ?_
    filter_upwards [hae] with x hx hxUS
    have hlt : ‖x - ξ‖ < R + ε := lt_of_not_ge fun h ↦ hxUS.2 ⟨hx, h⟩
    simp only [hGdef, hγ0 _ (hr0 x) hlt.le, zero_mul]
  -- step 6: `∫_U (F + G) dμ = 0` and `F + G ≥ γ(r)(n - |(x - ξ) · H|) ≥ 0` `μ`-a.e. on `U`
  have hsum : ∫ x in (closedBall ξ R)ᶜ, (F x + G x) ∂μ = 0 := by
    rw [integral_add hFint.integrableOn hGU]
    have h : ∫ x in (closedBall ξ R)ᶜ, F x ∂μ = -∫ x in (closedBall ξ R)ᶜ, G x ∂μ := hId
    linarith
  have hkey : ∀ x, γ ‖x - ξ‖ * ((n : ℝ) - |inner ℝ (x - ξ) (H x)|) ≤ F x + G x := fun x ↦ by
    have h1 : γ ‖x - ξ‖ * -|inner ℝ (x - ξ) (H x)| ≤ G x :=
      mul_le_mul_of_nonneg_left (neg_abs_le _) (hγnn ‖x - ξ‖ (hr0 x)).1
    have h2 := hFlow x
    linarith
  have hCU : ∀ᵐ x ∂μ, x ∈ (closedBall ξ R)ᶜ → |inner ℝ (x - ξ) (H x)| < (n : ℝ) := by
    filter_upwards [hC] with x hx hxU
    rw [real_inner_comm]
    exact hx hxU
  have hnn : 0 ≤ᵐ[μ.restrict (closedBall ξ R)ᶜ] fun x ↦ F x + G x := by
    rw [EventuallyLE, ae_restrict_iff' hUm]
    filter_upwards [hCU] with x hx hxU
    exact (mul_nonneg (hγnn _ (hr0 x)).1 (sub_nonneg.2 (hx hxU).le)).trans (hkey x)
  have hzero : (fun x ↦ F x + G x) =ᵐ[μ.restrict (closedBall ξ R)ᶜ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnn (hFint.integrableOn.add hGU)).1 hsum
  have hγU : ∀ᵐ x ∂μ, x ∈ (closedBall ξ R)ᶜ → γ ‖x - ξ‖ = 0 := by
    rw [EventuallyEq, ae_restrict_iff' hUm] at hzero
    filter_upwards [hzero, hCU] with x hx hCx hxU
    have hk := hkey x
    have h0 : F x + G x = 0 := hx hxU
    by_contra hne
    have hpos := mul_pos (lt_of_le_of_ne (hγnn _ (hr0 x)).1 (Ne.symm hne)) (sub_pos.2 (hCx hxU))
    linarith
  -- step 7: the open set `{r > R + ε} ⊆ U` is `μ`-null, hence disjoint from `spt μ`
  have hO : IsOpen {x : Ambient n ℓ | R + ε < ‖x - ξ‖} := isOpen_lt continuous_const hrc
  have hμO : μ {x : Ambient n ℓ | R + ε < ‖x - ξ‖} = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hγU] with x hx hxO
    have hxO' : R + ε < ‖x - ξ‖ := hxO
    exact (hγpos _ hxO').ne' (hx (hmemU x (by linarith)))
  intro x hx
  have hxO : x ∉ {x : Ambient n ℓ | R + ε < ‖x - ξ‖} := fun h ↦
    Measure.subset_compl_support_of_isOpen hO hμO h hx
  rw [mem_closedBall, dist_eq_norm]
  exact not_lt.1 hxO

/-- **Ch. 4, 6.1 (p. 100) from the radial first variation.** Assume the radial first variation
identity (3.2–3.3, 3.14) for `X(x) = h(x)γ(|x - ξ|)(x - ξ)`, and that for `n ≥ 1` the weight `μ_V`
is finite on compact sets, `dim T_x V = n` `μ_V`-a.e. and `x ↦ p_{T_x V}` is `μ_V`-a.e. strongly
measurable. Then `SupportInBall`: for `ε > 0`, the identity with `h = ζ`, `ζ = 1` and `∇ζ = 0` on
`spt V`, and `γ = 0` on `[0, R + ε]`, `γ > 0` beyond, reads
`n ∫_U γ(r) dμ_V + ∫_U rγ'(r)(1 - |D^⊥r|²) dμ_V = -∫_U γ(r)(x - ξ)·H dμ_V`, and with
`|H·(x - ξ)| < n` it forces `spt V ⊆ B_{R+ε}(ξ)`. -/
theorem Submission.support_in_ball_of_radial_first_variation : (∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)) (H : Ambient n ℓ → Ambient n ℓ) (h : Ambient n ℓ → ℝ) (γ : ℝ → ℝ) (ξ : Ambient n ℓ), (∀ᵐ x ∂V.weight, Module.finrank ℝ (V.tangentSpace x) = n) → IsOpen U → V.HasMeanCurvatureIn U H → ContDiffOn ℝ 1 h U → ContDiff ℝ 1 γ → IsTestField U (fun x ↦ (h x * γ ‖x - ξ‖) • (x - ξ)) → ∫ x in U, (h x * ((n : ℝ) * γ ‖x - ξ‖ + ‖x - ξ‖ * deriv γ ‖x - ξ‖ * (1 - V.normalRadialSq ξ x)) + γ ‖x - ξ‖ * inner ℝ (x - ξ) (V.tangentialGradient h x)) ∂V.weight = -∫ x in U, h x * γ ‖x - ξ‖ * inner ℝ (x - ξ) (H x) ∂V.weight) → (∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ), 0 < n → IsFiniteMeasureOnCompacts V.weight ∧ (∀ᵐ x ∂V.weight, Module.finrank ℝ (V.tangentSpace x) = n) ∧ AEStronglyMeasurable (fun x ↦ (V.tangentSpace x).starProjection) V.weight) → SupportInBall := by
  intro hRFV hGF n ℓ V H ξ R hn hR hH hcurv hcpt
  obtain ⟨hfin, hdim, hproj⟩ := hGF n ℓ V hn
  -- `|H(x)·(x - ξ)| < n` for `μ_V`-a.e. `x ∈ U = ℝ^{n+ℓ} \ B_R(ξ)`.
  have hC : ∀ᵐ x ∂V.weight, x ∈ (closedBall ξ R)ᶜ → |inner ℝ (H x) (x - ξ)| < (n : ℝ) := by
    filter_upwards [hcurv] with x hx hxU
    have h := (inv_mul_lt_iff₀ (Nat.cast_pos.mpr hn : (0 : ℝ) < n)).1 (hx hxU)
    rwa [mul_one] at h
  -- `|D^⊥r|²` is `μ_V`-a.e. strongly measurable with values in `[0, 1]`.
  obtain ⟨hqm, hq⟩ := Submission.aestronglyMeasurable_normalRadialSq_and_bounds n ℓ V ξ hproj
  have hball : ∀ ε : ℝ, 0 < ε → V.support ⊆ closedBall ξ (R + ε) := by
    intro ε hε
    -- `X(x) = ζ(x)γ(|x - ξ|)(x - ξ)` is a test field in `U`, with `ζ = 1`, `∇ζ = 0` on `spt V`,
    -- so (RFV) applies with `h = ζ`.
    obtain ⟨ζ, γ, hζ, hζK, hγ, hγnn, hγ0, hγpos, hX⟩ :=
      Submission.exists_radial_cutoff_test_field n ℓ V.support ξ R ε hcpt hR hε
    have hstar := hRFV n ℓ V (closedBall ξ R)ᶜ H ζ γ ξ hdim isClosed_closedBall.isOpen_compl hH
      hζ.contDiffOn hγ hX
    -- `μ_V`-a.e. `x` lies in `spt V`, where `ζ = 1` and `∇^M ζ = p_{T_x V}(∇ζ) = 0`, so `ζ` drops
    -- out of both sides of (RFV).
    have hae : ∀ᵐ x ∂V.weight.restrict (closedBall ξ R)ᶜ, ζ x = 1 ∧ gradient ζ x = 0 := by
      refine ae_restrict_of_ae ?_
      filter_upwards [V.weight.support_mem_ae] with x hx using hζK x hx
    have hL : ∫ x in (closedBall ξ R)ᶜ, (ζ x * ((n : ℝ) * γ ‖x - ξ‖ + ‖x - ξ‖ * deriv γ ‖x - ξ‖ *
          (1 - V.normalRadialSq ξ x)) + γ ‖x - ξ‖ * inner ℝ (x - ξ) (V.tangentialGradient ζ x))
          ∂V.weight =
        ∫ x in (closedBall ξ R)ᶜ, ((n : ℝ) * γ ‖x - ξ‖ + ‖x - ξ‖ * deriv γ ‖x - ξ‖ *
          (1 - V.normalRadialSq ξ x)) ∂V.weight := by
      refine integral_congr_ae ?_
      filter_upwards [hae] with x hx
      simp only [RectifiableVarifold.tangentialGradient, hx.1, hx.2, map_zero, inner_zero_right,
        mul_zero, add_zero, one_mul]
    have hR' : ∫ x in (closedBall ξ R)ᶜ, ζ x * γ ‖x - ξ‖ * inner ℝ (x - ξ) (H x) ∂V.weight =
        ∫ x in (closedBall ξ R)ᶜ, γ ‖x - ξ‖ * inner ℝ (x - ξ) (H x) ∂V.weight := by
      refine integral_congr_ae ?_
      filter_upwards [hae] with x hx
      simp only [hx.1, one_mul]
    rw [hL, hR'] at hstar
    -- The identity and `|H·(x - ξ)| < n` force `γ(|x - ξ|) = 0` `μ_V`-a.e. on `U`.
    exact Submission.support_subset_closedBall_of_radial_identity n ℓ V.weight H
      (V.normalRadialSq ξ) γ ξ R ε hn hR hε hfin hcpt hH.1 hqm hq hγ hγnn hγ0 hγpos hC hstar
  -- `spt V ⊆ ⋂_{ε > 0} B_{R+ε}(ξ) = B_R(ξ)`.
  intro x hx
  rw [mem_closedBall]
  exact le_of_forall_pos_le_add fun ε hε ↦ mem_closedBall.1 (hball ε hε hx)
/-- **Ch. 4, 6.2 from 6.1 (p. 101).** Assume `SupportInBall` (6.1). If `spt V` is compact and `V`
is stationary in `ℝ^{n+ℓ} \ K` with `K` compact, then `spt V ⊆ conv K`: for `y ∉ conv K` there is
a closed ball `B_R(c) ⊇ K` with `R ≥ 0` and `y ∉ B_R(c)` (`conv K` is compact by Carathéodory), `V`
has generalized mean curvature `0` in `ℝ^{n+ℓ} \ B_R(c) ⊆ ℝ^{n+ℓ} \ K`, and 6.1 gives
`spt V ⊆ B_R(c)`. -/
theorem Submission.convex_hull_property_of_support_in_ball : SupportInBall → ConvexHullProperty := by
  intro hBall n ℓ V K hn hK hV hstat
  classical
  -- Ball Lemma: every `y ∉ conv K` lies outside some closed ball `B_R(c) ⊇ K` with `R ≥ 0`.
  have hsep : ∀ y ∉ convexHull ℝ K, ∃ (c : Ambient n ℓ) (R : ℝ),
      0 ≤ R ∧ K ⊆ closedBall c R ∧ y ∉ closedBall c R := by
    intro y hy
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · -- `K = ∅`: `dim ℝ^{n+ℓ} = n + ℓ ≥ 1`, so there is `c ≠ y`; take `R = 0`.
      have : Nontrivial (Ambient n ℓ) :=
        Module.nontrivial_of_finrank_pos (by rw [finrank_euclideanSpace_fin]; omega)
      obtain ⟨c, hc⟩ := exists_ne y
      refine ⟨c, 0, le_rfl, by simp [hKe], ?_⟩
      rw [closedBall_zero, mem_singleton_iff]
      exact hc.symm
    -- `K ≠ ∅`: `conv K` is compact. By Carathéodory every point of `conv K` is a convex
    -- combination of at most `dim ℝ^{n+ℓ} + 1` points of `K`, so `conv K` is a finite union of
    -- continuous images `W j` of the compact sets `{w ∈ [0,1]^j : ∑ w = 1} × K^j`.
    have hcomp : IsCompact (convexHull ℝ K) := by
      let W : ℕ → Set (Ambient n ℓ) := fun j ↦
        (fun p : (Fin j → ℝ) × (Fin j → Ambient n ℓ) ↦ ∑ i, p.1 i • p.2 i) ''
          ((Icc (0 : Fin j → ℝ) 1 ∩ {w | ∑ i, w i = 1}) ×ˢ univ.pi fun _ ↦ K)
      have hW : ∀ j, IsCompact (W j) := fun j ↦
        ((isCompact_Icc.inter_right (isClosed_eq (by fun_prop) continuous_const)).prod
          (isCompact_univ_pi fun _ ↦ hK)).image (by fun_prop)
      suffices h : convexHull ℝ K =
          ⋃ j ∈ Finset.range (Module.finrank ℝ (Ambient n ℓ) + 2), W j by
        rw [h]
        exact (Finset.finite_toSet _).isCompact_biUnion fun j _ ↦ hW j
      refine subset_antisymm (fun x hx ↦ ?_) ?_
      · -- A finset `t ⊆ K` of minimal cardinality with `x ∈ conv t`.
        have hex : ∃ m, ∃ t : Finset (Ambient n ℓ), ↑t ⊆ K ∧
            x ∈ convexHull ℝ (t : Set (Ambient n ℓ)) ∧ t.card = m := by
          rw [convexHull_eq_union_convexHull_finite_subsets] at hx
          simp only [mem_iUnion, exists_prop] at hx
          obtain ⟨t, htK, hxt⟩ := hx
          exact ⟨_, t, htK, hxt, rfl⟩
        obtain ⟨t, htK, hxt, htm⟩ := Nat.find_spec hex
        obtain ⟨w, hw0, hw1, hwx⟩ := Finset.mem_convexHull'.1 hxt
        -- Carathéodory: `#t ≤ dim ℝ^{n+ℓ} + 1`. Otherwise an affine relation `∑ g z • z = 0`,
        -- `∑ g z = 0`, `g ≠ 0` on `t` lets us remove a point of `t`, contradicting minimality.
        have hcard : t.card ≤ Module.finrank ℝ (Ambient n ℓ) + 1 := by
          by_contra hlt
          obtain ⟨g, hgx, hg1, hg0⟩ :=
            Module.exists_nontrivial_relation_sum_zero_of_finrank_succ_lt_card (not_le.mp hlt)
          obtain ⟨i₁, hi₁, hgi₁⟩ := Finset.exists_pos_of_sum_zero_of_exists_nonzero g hg1 hg0
          obtain ⟨i₀, hi₀, hmin⟩ := (t.filter fun z ↦ 0 < g z).exists_min_image
            (fun z ↦ w z / g z) ⟨i₁, Finset.mem_filter.2 ⟨hi₁, hgi₁⟩⟩
          rw [Finset.mem_filter] at hi₀
          let k : Ambient n ℓ → ℝ := fun z ↦ w z - w i₀ / g i₀ * g z
          have hk : k i₀ = 0 := by simp [k, hi₀.2.ne']
          have hxe : x ∈ convexHull ℝ (↑(t.erase i₀) : Set (Ambient n ℓ)) := by
            refine Finset.mem_convexHull'.2 ⟨k, fun z hz ↦ ?_, ?_, ?_⟩
            · have hzt := Finset.mem_of_mem_erase hz
              simp only [k, sub_nonneg]
              by_cases hgz : 0 < g z
              · exact (le_div_iff₀ hgz).1 (hmin z (Finset.mem_filter.2 ⟨hzt, hgz⟩))
              · exact (mul_nonpos_of_nonneg_of_nonpos (div_nonneg (hw0 _ hi₀.1) hi₀.2.le)
                  (not_lt.mp hgz)).trans (hw0 z hzt)
            · rw [Finset.sum_erase t hk]
              simp only [k, Finset.sum_sub_distrib, ← Finset.mul_sum, hw1, hg1, mul_zero, sub_zero]
            · rw [Finset.sum_erase t (f := fun z ↦ k z • z) (by simp [hk])]
              simp only [k, sub_smul, mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum, hgx,
                smul_zero, sub_zero, hwx]
          exact Nat.find_min hex
            (show (t.erase i₀).card < Nat.find hex by
              rw [Finset.card_erase_of_mem hi₀.1]; omega)
            ⟨t.erase i₀, (Finset.coe_subset.2 (Finset.erase_subset _ _)).trans htK, hxe, rfl⟩
        -- Reindex the convex combination by `Fin #t`.
        let e := t.equivFin
        let a : Fin t.card → ℝ := fun i ↦ w (e.symm i)
        let z : Fin t.card → Ambient n ℓ := fun i ↦ (e.symm i : Ambient n ℓ)
        have hsum : ∑ i, a i = 1 :=
          (Equiv.sum_comp e.symm fun j : t ↦ w j).trans ((Finset.sum_coe_sort t w).trans hw1)
        have hsumx : ∑ i, a i • z i = x :=
          (Equiv.sum_comp e.symm fun j : t ↦ w j • (j : Ambient n ℓ)).trans
            ((Finset.sum_coe_sort t fun y ↦ w y • y).trans hwx)
        have ha0 : ∀ i, 0 ≤ a i := fun i ↦ hw0 _ (e.symm i).2
        have ha1 : ∀ i, a i ≤ 1 := fun i ↦
          hsum ▸ Finset.single_le_sum (fun j _ ↦ ha0 j) (Finset.mem_univ i)
        exact mem_iUnion₂.2 ⟨t.card, Finset.mem_range.2 (by omega),
          (a, z), ⟨⟨⟨ha0, ha1⟩, hsum⟩, fun i _ ↦ htK (e.symm i).2⟩, hsumx⟩
      · -- Conversely, convex combinations of points of `K` lie in `conv K`.
        simp only [iUnion_subset_iff]
        rintro j - _ ⟨⟨a, z⟩, ⟨⟨⟨ha0, -⟩, hsum⟩, hz⟩, rfl⟩
        exact (convex_convexHull ℝ K).sum_mem (fun i _ ↦ ha0 i) hsum
          fun i _ ↦ subset_convexHull ℝ K (hz i (mem_univ i))
    -- Nearest point `z₀ ∈ conv K` to `y`: `⟪y - z₀, x - z₀⟫ ≤ 0` for `x ∈ conv K`, and
    -- `η = |y - z₀| > 0`.
    obtain ⟨z₀, hz₀, hmin⟩ := exists_norm_eq_iInf_of_complete_convex hKne.convexHull
      hcomp.isComplete (convex_convexHull ℝ K) y
    have hvar := (norm_eq_iInf_iff_real_inner_le_zero (convex_convexHull ℝ K) hz₀).1 hmin
    have hη : 0 < ‖y - z₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr fun h ↦ hy (h ▸ hz₀))
    -- `K ⊆ B_D(z₀)`; with `t η² = D² + 1`, the ball `B_R(c)`, `c = z₀ - t (y - z₀)`,
    -- `R² = D² + t² η²`, contains `K` and `|y - c| = (1 + t) η > R`.
    obtain ⟨D, hD, hKD⟩ := hK.isBounded.subset_ball_lt 0 z₀
    set t : ℝ := (D ^ 2 + 1) / ‖y - z₀‖ ^ 2
    have ht : 0 < t := by positivity
    have htη : t * ‖y - z₀‖ ^ 2 = D ^ 2 + 1 := div_mul_cancel₀ _ (by positivity)
    set R : ℝ := Real.sqrt (D ^ 2 + t ^ 2 * ‖y - z₀‖ ^ 2)
    have hR : 0 ≤ R := Real.sqrt_nonneg _
    have hR2 : R ^ 2 = D ^ 2 + t ^ 2 * ‖y - z₀‖ ^ 2 := Real.sq_sqrt (by positivity)
    refine ⟨z₀ - t • (y - z₀), R, hR, fun x hx ↦ ?_, ?_⟩
    · have hxD : ‖x - z₀‖ < D := by simpa only [mem_ball, dist_eq_norm] using hKD hx
      have hi : inner ℝ (x - z₀) (y - z₀) ≤ 0 := by
        rw [real_inner_comm]
        exact hvar x (subset_convexHull ℝ K hx)
      have heq : x - (z₀ - t • (y - z₀)) = (x - z₀) + t • (y - z₀) := by abel
      have hsq : ‖x - (z₀ - t • (y - z₀))‖ ^ 2 ≤ R ^ 2 := by
        rw [heq, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos ht, hR2]
        nlinarith [mul_nonpos_of_nonneg_of_nonpos ht.le hi, norm_nonneg (x - z₀)]
      rw [mem_closedBall, dist_eq_norm]
      nlinarith [norm_nonneg (x - (z₀ - t • (y - z₀)))]
    · have heq : y - (z₀ - t • (y - z₀)) = (1 + t) • (y - z₀) := by module
      rw [mem_closedBall, dist_eq_norm, heq, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by linarith), not_le]
      nlinarith [sq_nonneg ((1 + t) * ‖y - z₀‖ + R)]
  intro y hy
  by_contra hyK
  obtain ⟨c, R, hR, hKc, hyc⟩ := hsep y hyK
  -- `V` has generalized mean curvature `0` in `ℝ^{n+ℓ} \ B_R(c) ⊆ ℝ^{n+ℓ} \ K`.
  have hmc : V.HasMeanCurvatureIn (closedBall c R)ᶜ fun _ ↦ 0 := by
    refine ⟨locallyIntegrableOn_zero, fun X hX ↦ ?_⟩
    rw [hstat X ⟨hX.1, hX.2.1, hX.2.2.trans (compl_subset_compl.mpr hKc)⟩]
    simp
  -- 6.1 with `H = 0`, `ξ = c`: `spt V ⊆ B_R(c)`, contradicting `y ∈ spt V \ B_R(c)`.
  exact hyc (hBall n ℓ V (fun _ ↦ 0) c R hn hR hmc
    (Filter.Eventually.of_forall fun x _ ↦ by simp) hV hy)
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

/-- **Stationary monotonicity and density** (Ch. 4, 3.6–3.11, pp. 90–91), given the structure
facts of §1 for every varifold (`μ_V` finite on compact sets, `dim T_x V = n` for `μ_V`-a.e. `x`,
and `x ↦ p_{T_x V}` `μ_V`-measurable). A stationary `V` has generalized mean curvature `0` in `U`,
so the weighted monotonicity identity with `h ≡ 1` and `H ≡ 0` is the identity 3.6, with
`r⁻ⁿ|D^⊥r|²` integrable on every annulus. From 3.6 follow 3.8–3.10 and the bound
`Θⁿ(μ_V, ξ) ≤ (ωₙρⁿ)⁻¹ μ_V(B_ρ(ξ))` for `B_R(ξ) ⊆ U` and `0 < ρ < R`; each point of the open set
`U` is the centre of such a ball (3.9), and the bound gives 3.11. -/
theorem Submission.stationary_monotonicity_density : (∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ),
    0 < n → IsFiniteMeasureOnCompacts V.weight ∧
      (∀ᵐ x ∂V.weight, Module.finrank ℝ (V.tangentSpace x) = n) ∧
      AEStronglyMeasurable (fun x ↦ (V.tangentSpace x).starProjection) V.weight) →
    StationaryMonotonicity ∧ StationaryDensity := by
  intro hGF
  -- 3.6, with the integrand integrable on the annulus: the weighted identity with `h ≡ 1` and
  -- `H ≡ 0`, where the error term vanishes since `∇^M 1 = 0`.
  have hannulus : ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ))
      (ξ : Ambient n ℓ) (R : ℝ), 0 < n → IsOpen U → V.IsStationaryIn U → closedBall ξ R ⊆ U →
      ∀ σ ρ : ℝ, 0 < σ → σ ≤ ρ → ρ < R →
        IntegrableOn (fun x ↦ V.normalRadialSq ξ x / ‖x - ξ‖ ^ n)
            (closedBall ξ ρ \ closedBall ξ σ) V.weight ∧
          V.weight.real (closedBall ξ ρ) / ρ ^ n - V.weight.real (closedBall ξ σ) / σ ^ n =
            ∫ x in closedBall ξ ρ \ closedBall ξ σ, V.normalRadialSq ξ x / ‖x - ξ‖ ^ n
              ∂V.weight := by
    intro n ℓ V U ξ R hn hU hV hball σ ρ hσ hσρ hρR
    obtain ⟨hfin, hdim, hmeas⟩ := hGF n ℓ V hn
    -- A stationary varifold has generalized mean curvature `0`.
    have hH : V.HasMeanCurvatureIn U 0 := by
      refine ⟨locallyIntegrableOn_zero, fun X hX ↦ ?_⟩
      rw [hV X hX]
      simp only [Pi.zero_apply, inner_zero_right, integral_zero, neg_zero]
    have hsupp : tsupport (fun _ : Ambient n ℓ ↦ (1 : ℝ)) ∩ closedBall ξ ρ ⊆ U :=
      fun x hx ↦ hball (closedBall_subset_closedBall hρR.le hx.2)
    obtain ⟨-, hint, heq⟩ := Submission.weighted_monotonicity_identity n ℓ V U 0 (fun _ ↦ 1) ξ
      σ ρ hn hfin hdim hmeas hU hH contDiffOn_const hsupp hσ hσρ
    have hgrad : ∀ x, V.tangentialGradient (fun _ ↦ (1 : ℝ)) x = 0 := fun x ↦ by
      simp only [tangentialGradient, gradient_fun_const, map_zero]
    simp only [one_mul, hgrad, Pi.zero_apply, smul_zero, add_zero, inner_zero_right,
      integral_zero, zero_div, setIntegral_const, smul_eq_mul, mul_one] at hint heq
    exact ⟨hint, heq⟩
  refine ⟨?_, ?_⟩
  · -- 3.6, and 3.8 and 3.10 from it.
    intro n ℓ V U ξ R hn hU hV hball
    obtain ⟨hmono, hfull, -, -⟩ := Submission.stationary_ratio_limit_of_annulus_identity n ℓ V ξ R
      (hannulus n ℓ V U ξ R hn hU hV hball)
    exact ⟨fun σ ρ hσ hσρ hρR ↦ (hannulus n ℓ V U ξ R hn hU hV hball σ ρ hσ hσρ hρR).2, hmono,
      hfull⟩
  · intro n ℓ V U hn hU hV
    -- 3.9: every `ξ ∈ U` is the centre of a closed ball `B_{ε/2}(ξ) ⊆ U`.
    have hdens : ∀ ξ ∈ U, V.HasDensityAt ξ (V.density ξ) := by
      intro ξ hξ
      obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU ξ hξ
      exact (Submission.stationary_ratio_limit_of_annulus_identity n ℓ V ξ (ε / 2)
        (hannulus n ℓ V U ξ (ε / 2) hn hU hV
          ((closedBall_subset_ball (half_lt_self hε)).trans hεU))).2.2.1 (half_pos hε)
    -- 3.11, from `Θⁿ(μ_V, η) ≤ (ωₙρⁿ)⁻¹ μ_V(B_ρ(η))` whenever `B_R(η) ⊆ U` and `0 < ρ < R`.
    refine ⟨hdens, Submission.stationary_density_usc_of_ratio_bound n ℓ V U hU (hGF n ℓ V hn).1
      hdens fun η R ρ hball hρ hρR ↦ ?_⟩
    exact (Submission.stationary_ratio_limit_of_annulus_identity n ℓ V η R
      (hannulus n ℓ V U η R hn hU hV hball)).2.2.2 ρ hρ hρR
/-- **Monotonicity with mean curvature** (Ch. 4, 3.16–3.18 and 4.1–4.9, pp. 92–95), given the
structure facts of §1 for every varifold (`μ_V` finite on compact sets, `dim T_x V = n` for
`μ_V`-a.e. `x`, and `x ↦ p_{T_x V}` `μ_V`-measurable). The weighted monotonicity identity with
`h ≡ 1` is 3.16/4.1 integrated from `σ` to `ρ` with the cutoff removed: for `B_ρ(ξ) ⊆ U` and
`0 < σ ≤ ρ`, `a(ρ) - a(σ) = ∫_{B_ρ(ξ) \ B_σ(ξ)} r⁻ⁿ|D^⊥r|² dμ_V + ∫_σ^ρ e`, where
`a(τ) = τ⁻ⁿμ_V(B_τ(ξ))` and `e(τ) = τ^{-n-1} ∫_{B_τ(ξ)} (x - ξ)·H dμ_V`. Then `|e| ≤ δ/τ` gives
3.18; `|e| ≤ Λa` (3.15) and the Hölder bound `|e(τ)| ≤ (κΛ/R)(τ/R)^{-n/p}(1 + a(τ))` (4.2–4.3),
integrated by parts against `F = exp(-∫₀^ρ e/a)`, resp. `F = exp(-∫₀^ρ e/(1 + a))`, give 3.17
and 4.5–4.8; and the resulting monotone quantities give the existence and upper semicontinuity
of `Θⁿ(μ_V, ·)` (the remark after 3.17, and 4.9). -/
theorem Submission.mean_curvature_monotonicity : (∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ),
    0 < n → IsFiniteMeasureOnCompacts V.weight ∧
      (∀ᵐ x ∂V.weight, Module.finrank ℝ (V.tangentSpace x) = n) ∧
      AEStronglyMeasurable (fun x ↦ (V.tangentSpace x).starProjection) V.weight) →
    BoundedCurvatureMonotonicity ∧ LogarithmicMonotonicityError ∧ LpMonotonicity ∧ LpDensity := by
  intro hStruct
  -- 3.16 and 4.1 integrated from `σ` to `ρ`: the weighted identity with `h ≡ 1`.
  have hUnit :=
    Submission.mcm_unit_weight_identity Submission.weighted_monotonicity_identity hStruct
  -- 4.2–4.8, from which 4.9 follows.
  have hLpMono := Submission.mcm_lp_monotonicity_of_identity hStruct hUnit
  -- 3.17 with the remark after it, 3.18, 4.5–4.8 and 4.9.
  exact ⟨Submission.mcm_bounded_curvature_of_identity hStruct hUnit,
    Submission.mcm_log_error_of_identity hUnit, hLpMono,
    Submission.mcm_lp_density_of_monotonicity hStruct hLpMono⟩

/-- **Ch. 4, 3.12, 3.13 (p. 91) and 4.10(1) (p. 95), canonical representatives.** Assume
`ApproxTangentAE` and that every `μ_V` is finite on compacts, with `dim T_x V = n` `μ_V`-a.e.
and `x ↦ p_{T_x V}` `μ_V`-measurable. Both conclusions only use that `Θⁿ(μ_V, ·)` exists on the
open set `U` and is upper semicontinuous there, which is 3.9, 3.11 for stationary `V` and 4.9 for
`H ∈ L^p_loc`, `p > n`. Then `(M_V, Θⁿ(μ_V, ·))` is an admissible pair with weight `μ_V ⌞ U`
(`canonicalCarrier_rectifiablePair_weight`); `{x ∈ M_V : Θⁿ(μ_V, x) ≥ α}` is relatively closed
in `U` for `α > 0`, and if `θ ≥ α > 0` then `M_V = spt V ∩ U` and `Θⁿ(μ_V, ·) ≥ α` on `M_V`
(`canonicalCarrier_closed_support`). With `α = 1` this is 4.10(1). -/
theorem Submission.canonical_representatives : ApproxTangentAE →
    (∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ), 0 < n →
      IsFiniteMeasureOnCompacts V.weight ∧
        (∀ᵐ x ∂V.weight, Module.finrank ℝ (V.tangentSpace x) = n) ∧
        AEStronglyMeasurable (fun x ↦ (V.tangentSpace x).starProjection) V.weight) →
    CanonicalRepresentative ∧ LpSupportRepresentation := by
  intro hTangent hStruct
  refine ⟨fun n ℓ V U hn hU hV ↦ ?_, fun n ℓ V U H p hn hU hH hp hHp hθ ↦ ?_⟩
  · -- 3.9, 3.11: `Θⁿ(μ_V, ·)` exists on `U` and is upper semicontinuous there.
    obtain ⟨hDensity, hUSC⟩ :=
      (Submission.stationary_monotonicity_density hStruct).2 n ℓ V U hn hU hV
    -- 3.12: `(M_V, Θ)` is admissible with weight `μ_V ⌞ U`; 3.13: closedness and `spt V`.
    obtain ⟨hPair, hWeight⟩ := Submission.canonicalCarrier_rectifiablePair_weight hTangent n ℓ V U
      hn hU (hStruct n ℓ V hn).1 hDensity
    obtain ⟨hClosed, hSupport⟩ :=
      Submission.canonicalCarrier_closed_support hTangent n ℓ V U hn hU hDensity hUSC
    exact ⟨hPair, hWeight, hClosed, hSupport⟩
  · -- 4.9: `Θⁿ(μ_V, ·)` exists on `U` and is upper semicontinuous there.
    obtain ⟨hDensity, hUSC⟩ :=
      (Submission.mean_curvature_monotonicity hStruct).2.2.2 n ℓ V U H p hn hU hH hp hHp
    obtain ⟨hPair, hWeight⟩ := Submission.canonicalCarrier_rectifiablePair_weight hTangent n ℓ V U
      hn hU (hStruct n ℓ V hn).1 hDensity
    -- 3.13 with `α = 1`: `M_V = spt V ∩ U` and `Θ ≥ 1` on `M_V`.
    obtain ⟨hCarrier, hOne⟩ :=
      (Submission.canonicalCarrier_closed_support hTangent n ℓ V U hn hU hDensity hUSC).2 1
        one_pos hθ
    rw [hCarrier] at hPair hWeight hOne
    exact ⟨hOne, hPair, hWeight⟩

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
/-- **Michael–Simon Sobolev inequality (Simon 5.7–5.9, corrected Lemma 5.8, `n ≥ 2`).** Under
`ApproxTangentAE` and the structural facts (FV1)–(FV3) for every varifold, `SobolevInequality`
holds with the dimension-only constant `c = 5^{n+1} ωₙ^{-1/n}`. Simon 5.5 at all radii
(`sobolev_monotonicity_inequality`), `Θ ≥ 1` `μ_V`-a.e. in `U` (`sobolev_density_ge_one_ae`)
and the good-ball covering (`sobolev_covering_inequality`) give the superlevel estimate (4.1)
`∫_{g ≥ 1} g ≤ 5ⁿ ωₙ^{-1/n} (∫ g)^{1/n} ∫ (|∇^M g| + g|H|)` for every admissible `g`; truncation
and the layer-cake formula (`sobolev_of_superlevel_inequality`) turn (4.1) into the Sobolev
inequality with constant `n/(n-1) · 5ⁿ ωₙ^{-1/n} ≤ 5^{n+1} ωₙ^{-1/n}`. -/
theorem Submission.sobolev_inequality : ApproxTangentAE → (∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ), 0 < n → IsFiniteMeasureOnCompacts V.weight ∧ (∀ᵐ x ∂V.weight, Module.finrank ℝ (V.tangentSpace x) = n) ∧ AEStronglyMeasurable (fun x ↦ (V.tangentSpace x).starProjection) V.weight) → SobolevInequality := by
  intro hAT hGF n hn
  have hn0 : 0 < n := by omega
  -- `ωₙ > 0`: the open unit ball of `ℝⁿ` has positive, finite Lebesgue measure.
  have hω : 0 < omega n :=
    ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne
  have hK : 0 ≤ (5 : ℝ) ^ n * omega n ^ (-(n : ℝ)⁻¹) :=
    mul_nonneg (pow_nonneg (by norm_num) n) (Real.rpow_nonneg hω.le _)
  refine ⟨5 ^ (n + 1) * omega n ^ (-(n : ℝ)⁻¹),
    mul_pos (pow_pos (by norm_num) _) (Real.rpow_pos_of_pos hω _), ?_⟩
  intro ℓ V U H h hU hH hθ hh hhc hhU hh0
  obtain ⟨hfin, hdim, hmeas⟩ := hGF n ℓ V hn0
  -- (1.1): `Θ` exists and `Θ ≥ 1` at `μ_V`-a.e. point of `U`.
  have hdens := Submission.sobolev_density_ge_one_ae hAT n ℓ V U hn0 hU hθ
  -- (4.1) for every admissible `g`, with the constant `K = 5ⁿ ωₙ^{-1/n}`.
  have hsuper : ∀ g : Ambient n ℓ → ℝ, ContDiffOn ℝ 1 g U → HasCompactSupport g →
      tsupport g ⊆ U → (∀ x, 0 ≤ g x) →
      ∫ x in {x | 1 ≤ g x}, g x ∂V.weight ≤ 5 ^ n * omega n ^ (-(n : ℝ)⁻¹) *
        (∫ x, g x ∂V.weight) ^ (n : ℝ)⁻¹ *
          ∫ x, (‖V.tangentialGradient g x‖ + g x * ‖H x‖) ∂V.weight := by
    intro g hg hgc hgU hg0
    obtain ⟨hgC1, -, hgrad, hgH⟩ :=
      Submission.sobolev_energy_integrable n ℓ V U H g hfin hmeas hU hH.1 hg hgc hgU
    refine Submission.sobolev_covering_inequality n ℓ V.weight g
      (fun x ↦ ‖V.tangentialGradient g x‖ + g x * ‖H x‖) hn hfin hgC1.continuous hgc hg0
      (fun x ↦ add_nonneg (norm_nonneg _) (mul_nonneg (hg0 x) (norm_nonneg _)))
      (hgrad.add hgH) (fun ζ s r hs hsr ↦ ?_) ?_
    · -- Simon 5.5 at every radius, from the weighted monotonicity identity.
      exact Submission.sobolev_monotonicity_inequality Submission.weighted_monotonicity_identity
        n ℓ V U H g ζ s r hn0 hfin hdim hmeas hU hH hg hgc hgU hg0 hs hsr
    · -- `{g ≥ 1} ⊆ tsupport g ⊆ U`, where the density exists and is `≥ 1` a.e.
      filter_upwards [hdens] with ζ hζ hgζ
      obtain ⟨hD, h1⟩ :=
        hζ (hgU (subset_tsupport g (Function.mem_support.2 (zero_lt_one.trans_le hgζ).ne')))
      exact ⟨V.density ζ, h1, hD⟩
  -- Truncation and layer cake give the constant `n/(n-1) · K`, and `n/(n-1) ≤ 5`.
  refine (Submission.sobolev_of_superlevel_inequality n ℓ V U H h _ hn hfin hmeas hU hH.1 hK
    hsuper hh hhc hhU hh0).trans ?_
  have hJ : 0 ≤ ∫ x, (‖V.tangentialGradient h x‖ + h x * ‖H x‖) ∂V.weight :=
    integral_nonneg fun x ↦ add_nonneg (norm_nonneg _) (mul_nonneg (hh0 x) (norm_nonneg _))
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hq : (n : ℝ) / ((n : ℝ) - 1) ≤ 5 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  calc _ ≤ 5 * (5 ^ n * omega n ^ (-(n : ℝ)⁻¹)) *
        ∫ x, (‖V.tangentialGradient h x‖ + h x * ‖H x‖) ∂V.weight :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hq hK) hJ
    _ = _ := by ring
/-- Simon 6.1–6.2 (pp. 100–101): if for every `n ≥ 1` and every `V` the weight `μ_V` is finite
on compact sets, `dim T_x V = n` for `μ_V`-a.e. `x` and `x ↦ p_{T_x V}` is `μ_V`-a.e. strongly
measurable, then `spt V ⊆ B_R(ξ)` whenever `n⁻¹|H(x)·(x - ξ)| < 1` in `ℝ^{n+ℓ} \ B_R(ξ)` and
`spt V` is compact (6.1), and `spt V ⊆ conv K` whenever `spt V` is compact and `V` is stationary
in `ℝ^{n+ℓ} \ K` with `K` compact (6.2). -/
theorem Submission.support_in_ball_convex_hull : (∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ), 0 < n → IsFiniteMeasureOnCompacts V.weight ∧ (∀ᵐ x ∂V.weight, Module.finrank ℝ (V.tangentSpace x) = n) ∧ AEStronglyMeasurable (fun x ↦ (V.tangentSpace x).starProjection) V.weight) → SupportInBall ∧ ConvexHullProperty := by
  intro hGF
  -- 6.1: the radial first variation identity (3.2–3.3, 3.14) for `X(x) = ζ(x) γ(r) (x - ξ)`,
  -- with `ζ ≡ 1` near `spt V` and `γ = 0` on `(-∞, R + ε]`, forces `γ(r) = 0` `μ_V`-a.e.
  have hBall : SupportInBall :=
    Submission.support_in_ball_of_radial_first_variation Submission.radial_first_variation hGF
  -- 6.2: `conv K` is the intersection of the closed balls containing `K`, and `V` has
  -- generalized mean curvature `0` outside each of them.
  exact ⟨hBall, Submission.convex_hull_property_of_support_in_ball hBall⟩

end

end GMT.Ch04
