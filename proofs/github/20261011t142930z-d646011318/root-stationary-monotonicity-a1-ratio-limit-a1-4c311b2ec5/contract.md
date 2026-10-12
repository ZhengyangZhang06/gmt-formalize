<!-- theorem-id: gmt-ch04/root.stationary_monotonicity-a1.ratio_limit-a1 -->

## Theorem `Submission.stationary_ratio_limit_of_annulus_identity`

Let n, ℓ ∈ ℕ, V a rectifiable n-varifold in ℝ^{n+ℓ} with weight μ = μ_V, ξ ∈ ℝ^{n+ℓ} and R ∈ ℝ. Write B_r = B_r(ξ) for the closed ball, μ(S) for the real value μ.real S, q_ξ = V.normalRadialSq ξ, w(x) = q_ξ(x)/|x − ξ|ⁿ and a(r) = μ(B_r)/rⁿ. Assume that for all 0 < σ ≤ ρ < R, w is μ-integrable on B_ρ ∖ B_σ and a(ρ) − a(σ) = ∫_{B_ρ∖B_σ} w dμ. Then: (1) a is nondecreasing on (0, R); (2) for every 0 < ρ < R, w is μ-integrable on B_ρ and μ(B_ρ)/(ω_nρⁿ) − Θⁿ(μ, ξ) = ω_n^{-1}∫_{B_ρ} w dμ, where Θⁿ(μ, ξ) = V.density ξ; (3) if R > 0, then μ(B_s)/(ω_n sⁿ) → V.density ξ as s ↓ 0 (V.HasDensityAt ξ (V.density ξ)); (4) for every 0 < ρ < R, V.density ξ ≤ μ(B_ρ)/(ω_nρⁿ).

Node: `root.stationary_monotonicity-a1.ratio_limit-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/59

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.stationary_ratio_limit_of_annulus_identity`

```lean
∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (ξ : Ambient n ℓ) (R : ℝ), (∀ σ ρ : ℝ, 0 < σ → σ ≤ ρ → ρ < R → IntegrableOn (fun x ↦ V.normalRadialSq ξ x / ‖x - ξ‖ ^ n) (closedBall ξ ρ \ closedBall ξ σ) V.weight ∧ V.weight.real (closedBall ξ ρ) / ρ ^ n - V.weight.real (closedBall ξ σ) / σ ^ n = ∫ x in closedBall ξ ρ \ closedBall ξ σ, V.normalRadialSq ξ x / ‖x - ξ‖ ^ n ∂V.weight) → MonotoneOn (fun ρ ↦ V.weight.real (closedBall ξ ρ) / ρ ^ n) (Ioo 0 R) ∧ (∀ ρ : ℝ, 0 < ρ → ρ < R → IntegrableOn (fun x ↦ V.normalRadialSq ξ x / ‖x - ξ‖ ^ n) (closedBall ξ ρ) V.weight ∧ V.weight.real (closedBall ξ ρ) / (omega n * ρ ^ n) - V.density ξ = (omega n)⁻¹ * ∫ x in closedBall ξ ρ, V.normalRadialSq ξ x / ‖x - ξ‖ ^ n ∂V.weight) ∧ (0 < R → V.HasDensityAt ξ (V.density ξ)) ∧ ∀ ρ : ℝ, 0 < ρ → ρ < R → V.density ξ ≤ V.weight.real (closedBall ξ ρ) / (omega n * ρ ^ n)
```

### Frozen project context

`GMT/Ch04/Contract.lean` at `ff75f52a4c9deb3b3abbd91eb31d7b02e29a4cef` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
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

theorem main_theorem : ApproxTangentAE ∧ FirstVariationFormula ∧ StationaryIffVariational ∧ StationaryMonotonicity ∧ StationaryDensity ∧ CanonicalRepresentative ∧ BoundedCurvatureMonotonicity ∧ LogarithmicMonotonicityError ∧ LpMonotonicity ∧ LpDensity ∧ LpSupportRepresentation ∧ PoincareInequality ∧ SobolevInequality ∧ SupportInBall ∧ ConvexHullProperty ∧ ClassicalTangent := by sorry

end

end GMT.Ch04
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `accepted`.

# Parent-supplied natural-language proof

- Parent DAG node: `root.stationary_monotonicity-a1`
- Child DAG node: `root.stationary_monotonicity-a1.ratio_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. E = Ambient n ℓ = ℝ^{n+ℓ} with its Borel σ-algebra; B_r(ξ) = closedBall ξ r (a closed Borel set; B_r(ξ) = ∅ for r < 0); μ = V.weight; for a Borel set S, μ_ℝ(S) := V.weight.real S = (μ S).toReal ∈ [0, ∞) (it is 0 when μ S = ∞); ω_n = omega n = (Lebesgue measure of the unit ball of ℝⁿ).toReal; real division follows Lean's convention x/0 = 0, 0⁻¹ = 0. Put q(x) := V.normalRadialSq ξ x = ‖p_{(T_xV)^⊥}(x − ξ)‖²/‖x − ξ‖², w(x) := q(x)/‖x − ξ‖ⁿ, a(r) := μ_ℝ(B_r(ξ))/rⁿ, Q(r) := μ_ℝ(B_r(ξ))/(ω_n rⁿ), and Θ := V.density ξ = limUnder (𝓝[>] 0) Q. Hypothesis (H): for all reals 0 < σ ≤ ρ < R, w is μ-integrable on B_ρ(ξ) ∖ B_σ(ξ) and a(ρ) − a(σ) = ∫_{B_ρ(ξ)∖B_σ(ξ)} w dμ. Nothing else is used: no finiteness of μ, and no positivity of n or of ω_n.

Source: Steps 3–4 of the parent proof (Simon Ch. 4, 3.8–3.10) and the inequality of its Step 5 (ω_nΘ(ξ) = inf a ≤ a(ρ)). The parent's monotone-limit and monotone-convergence arguments are written out in full below.

1. Elementary facts. (a) w(x) ≥ 0 for every x, because q(x) is a quotient of two squares and ‖x − ξ‖ⁿ ≥ 0. (b) w(ξ) = 0: since ‖ξ − ξ‖² = 0, q(ξ) = ‖·‖²/0 = 0, hence w(ξ) = 0. (c) a(r) ≥ 0 for r > 0, since μ_ℝ ≥ 0 and rⁿ > 0. (d) Q(r) = ω_n⁻¹ · a(r) for every real r: x/(ω rⁿ) = x·(ω rⁿ)⁻¹ = x·ω⁻¹·(rⁿ)⁻¹ = ω⁻¹·(x/rⁿ), using (uv)⁻¹ = u⁻¹v⁻¹, which holds for all reals under the convention 0⁻¹ = 0. (e) ω_n⁻¹ ≥ 0, because ω_n is the real value of a measure and so ω_n ≥ 0. (ω_n > 0 is true but not needed.)

2. (3.8, monotonicity; conclusion 1.) Let σ, ρ ∈ (0, R) with σ ≤ ρ. Then 0 < σ ≤ ρ < R, so by (H), a(ρ) − a(σ) = ∫_{B_ρ(ξ)∖B_σ(ξ)} w dμ. The set B_ρ(ξ)∖B_σ(ξ) is measurable and w ≥ 0 on it (1a), so the integral is ≥ 0 (setIntegral_nonneg). Hence a(σ) ≤ a(ρ): the function r ↦ μ_ℝ(B_r(ξ))/rⁿ is monotone (nondecreasing) on (0, R).

3. (3.9, existence of the limit and of the density; conclusion 3.) Assume R > 0. The set a((0, R)) is nonempty (R/2 ∈ (0, R)) and bounded below by 0 (1c); let L := inf a((0, R)) ∈ [0, ∞). Then L ≤ a(s) for every s ∈ (0, R), and a(s) → L as s ↓ 0. Indeed, given ε > 0, choose s₀ ∈ (0, R) with a(s₀) < L + ε; for 0 < s < s₀ we have s ∈ (0, R), and by Step 2, L ≤ a(s) ≤ a(s₀) < L + ε. (Mathlib: MonotoneOn.tendsto_nhdsWithin_Ioo_right.) By (1d), Q(s) = ω_n⁻¹a(s) → ω_n⁻¹L as s ↓ 0. The filter 𝓝[>] 0 on ℝ is nontrivial and ℝ is Hausdorff, so the limUnder that defines V.density ξ equals this limit (Tendsto.limUnder_eq): Θ = ω_n⁻¹L. Hence Q(s) → Θ as s ↓ 0, which is V.HasDensityAt ξ (V.density ξ).

4. (Ratio bound; conclusion 4.) Let 0 < ρ < R. Then R > 0, so Step 3 applies and L ≤ a(ρ). Multiplying by ω_n⁻¹ ≥ 0 (1e) and using (1d): V.density ξ = ω_n⁻¹L ≤ ω_n⁻¹a(ρ) = Q(ρ) = μ_ℝ(B_ρ(ξ))/(ω_nρⁿ).

5. (3.10, by monotone convergence; conclusion 2.) Fix 0 < ρ < R. Then R > 0, so Steps 3–4 apply. For k ∈ ℕ put s_k := ρ/(k + 1) and A_k := B_ρ(ξ) ∖ B_{s_k}(ξ).
(a) Properties. 0 < s_k ≤ ρ < R. The sequence (s_k) is nonincreasing and s_k → 0, so s_k → 0 within (0, ∞), i.e. along 𝓝[>] 0. Consequently (A_k) is nondecreasing and every A_k is Borel. Moreover ⋃_k A_k = B_ρ(ξ) ∖ {ξ}: if x ∈ A_k then ‖x − ξ‖ > s_k > 0, so x ≠ ξ; conversely, if x ∈ B_ρ(ξ) and x ≠ ξ, then ‖x − ξ‖ > 0, so s_k < ‖x − ξ‖ for some k (as s_k → 0), and x ∈ A_k.
(b) By (H) with σ = s_k: w is μ-integrable on A_k and ∫_{A_k} w dμ = a(ρ) − a(s_k).
(c) Finite lower integral. Since w ≥ 0 is integrable on A_k, ∫⁻_{A_k} ofReal(w) dμ = ofReal(∫_{A_k} w dμ) = ofReal(a(ρ) − a(s_k)) (ofReal_integral_eq_lintegral_ofReal). This is ≤ ofReal(a(ρ) − L), because L ≤ a(s_k) (s_k ∈ (0, R)). The family (A_k) is increasing, hence directed, so by monotone convergence the lower integral over the union is the supremum (setLIntegral_iUnion_of_directed): ∫⁻_{B_ρ(ξ)∖{ξ}} ofReal(w) dμ = sup_k ∫⁻_{A_k} ofReal(w) dμ ≤ ofReal(a(ρ) − L) < ∞.
(d) Integrability on B_ρ(ξ) ∖ {ξ}. By (b), w is μ-a.e. strongly measurable on each A_k, hence on the countable union ⋃_k A_k = B_ρ(ξ)∖{ξ} (aestronglyMeasurable_iUnion_iff). Together with (c) and w ≥ 0 (hasFiniteIntegral_iff_ofReal), w is μ-integrable on B_ρ(ξ) ∖ {ξ}.
(e) The point ξ. Since w(ξ) = 0 (1b), w is μ-integrable on {ξ} whatever μ{ξ} is (integrableOn_singleton_iff), and ∫_{{ξ}} w dμ = 0 because w vanishes on {ξ}.
(f) Integrability on B_ρ(ξ). Since ‖ξ − ξ‖ = 0 ≤ ρ, we have ξ ∈ B_ρ(ξ), so B_ρ(ξ) = (B_ρ(ξ)∖{ξ}) ∪ {ξ}, a disjoint union of Borel sets. By (d) and (e), w is μ-integrable on B_ρ(ξ). This is the IntegrableOn part of conclusion 2.
(g) Value of the integral. By (d), w is integrable on ⋃_k A_k, and (A_k) is increasing and measurable, so ∫_{A_k} w dμ → ∫_{B_ρ(ξ)∖{ξ}} w dμ (dominated convergence; tendsto_setIntegral_of_monotone). On the other hand, ∫_{A_k} w dμ = a(ρ) − a(s_k) → a(ρ) − L, because s_k → 0 along 𝓝[>] 0 and a(s) → L as s ↓ 0 (Step 3). By uniqueness of limits, ∫_{B_ρ(ξ)∖{ξ}} w dμ = a(ρ) − L. With (e), (f) and additivity of the integral over the disjoint union (setIntegral_union): ∫_{B_ρ(ξ)} w dμ = (a(ρ) − L) + 0 = a(ρ) − L.
(h) Conclusion. By (1d) and Step 3, Q(ρ) − Θ = ω_n⁻¹a(ρ) − ω_n⁻¹L = ω_n⁻¹(a(ρ) − L) = ω_n⁻¹ ∫_{B_ρ(ξ)} w dμ. That is, V.weight.real (closedBall ξ ρ)/(omega n · ρⁿ) − V.density ξ = (omega n)⁻¹ · ∫_{closedBall ξ ρ} V.normalRadialSq ξ x/‖x − ξ‖ⁿ dμ.

6. Steps 2, 5, 3 and 4 give, in that order, the four conjuncts of the statement:
- MonotoneOn on Ioo 0 R;
- for 0 < ρ < R, IntegrableOn on closedBall ξ ρ together with identity 3.10;
- 0 < R → V.HasDensityAt ξ (V.density ξ);
- for 0 < ρ < R, V.density ξ ≤ V.weight.real (closedBall ξ ρ)/(omega n · ρⁿ). ∎

Appendix (reference only; the numbered proof above is complete). The decomposition author compiled the following Lean proof of exactly this statement. It used `import GMT.Ch04.Submission` with the pinned toolchain (Lean v4.35.0-rc3, Mathlib 25730c7c) and has no errors or warnings. `#print axioms` reports only [propext, Classical.choice, Quot.sound].

import GMT.Ch04.Submission

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal ContDiff CompactlySupported

namespace GMT.Ch04

noncomputable section

open RectifiableVarifold

namespace Submission

theorem stationary_ratio_limit_of_annulus_identity : ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (ξ : Ambient n ℓ) (R : ℝ), (∀ σ ρ : ℝ, 0 < σ → σ ≤ ρ → ρ < R → IntegrableOn (fun x ↦ V.normalRadialSq ξ x / ‖x - ξ‖ ^ n) (closedBall ξ ρ \ closedBall ξ σ) V.weight ∧ V.weight.real (closedBall ξ ρ) / ρ ^ n - V.weight.real (closedBall ξ σ) / σ ^ n = ∫ x in closedBall ξ ρ \ closedBall ξ σ, V.normalRadialSq ξ x / ‖x - ξ‖ ^ n ∂V.weight) → MonotoneOn (fun ρ ↦ V.weight.real (closedBall ξ ρ) / ρ ^ n) (Ioo 0 R) ∧ (∀ ρ : ℝ, 0 < ρ → ρ < R → IntegrableOn (fun x ↦ V.normalRadialSq ξ x / ‖x - ξ‖ ^ n) (closedBall ξ ρ) V.weight ∧ V.weight.real (closedBall ξ ρ) / (omega n * ρ ^ n) - V.density ξ = (omega n)⁻¹ * ∫ x in closedBall ξ ρ, V.normalRadialSq ξ x / ‖x - ξ‖ ^ n ∂V.weight) ∧ (0 < R → V.HasDensityAt ξ (V.density ξ)) ∧ ∀ ρ : ℝ, 0 < ρ → ρ < R → V.density ξ ≤ V.weight.real (closedBall ξ ρ) / (omega n * ρ ^ n) := by
  intro n ℓ V ξ R hid
  set μ := V.weight with hμ
  set w : Ambient n ℓ → ℝ := fun x ↦ V.normalRadialSq ξ x / ‖x - ξ‖ ^ n with hw
  set a : ℝ → ℝ := fun ρ ↦ μ.real (closedBall ξ ρ) / ρ ^ n with ha
  have hw0 : ∀ x, 0 ≤ w x := fun x ↦
    div_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _)) (pow_nonneg (norm_nonneg _) _)
  have hwξ : w ξ = 0 := by simp [hw, normalRadialSq]
  have ha0 : ∀ ρ, 0 < ρ → 0 ≤ a ρ := fun ρ hρ ↦
    div_nonneg measureReal_nonneg (pow_nonneg hρ.le _)
  -- Step 1 (3.8): monotonicity.
  have hmono : MonotoneOn a (Ioo 0 R) := by
    intro σ hσ ρ hρ hσρ
    have h := (hid σ ρ hσ.1 hσρ hρ.2).2
    have hnn : 0 ≤ ∫ x in closedBall ξ ρ \ closedBall ξ σ, w x ∂μ :=
      setIntegral_nonneg (measurableSet_closedBall.diff measurableSet_closedBall)
        fun x _ ↦ hw0 x
    change a ρ - a σ = _ at h
    linarith
  -- The density quotient is `ωₙ⁻¹ a`.
  have hQ : ∀ ρ, μ.real (closedBall ξ ρ) / (omega n * ρ ^ n) = (omega n)⁻¹ * a ρ := by
    intro ρ
    simp only [ha, div_eq_mul_inv, mul_inv]
    ring
  have hωinv : 0 ≤ (omega n)⁻¹ := inv_nonneg.2 ENNReal.toReal_nonneg
  -- Step 2 (3.9): the limit `L` and the density.
  have hlim : 0 < R → Tendsto a (𝓝[>] 0) (𝓝 (sInf (a '' Ioo 0 R))) ∧
      V.density ξ = (omega n)⁻¹ * sInf (a '' Ioo 0 R) ∧
      Tendsto (fun ρ ↦ μ.real (closedBall ξ ρ) / (omega n * ρ ^ n)) (𝓝[>] 0)
        (𝓝 ((omega n)⁻¹ * sInf (a '' Ioo 0 R))) := by
    intro hR
    have hbdd : BddBelow (a '' Ioo 0 R) := ⟨0, by
      rintro _ ⟨ρ, hρ, rfl⟩
      exact ha0 ρ hρ.1⟩
    have hT : Tendsto a (𝓝[>] 0) (𝓝 (sInf (a '' Ioo 0 R))) :=
      MonotoneOn.tendsto_nhdsWithin_Ioo_right ⟨R / 2, by positivity, by linarith⟩ hmono hbdd
    have hT' : Tendsto (fun ρ ↦ μ.real (closedBall ξ ρ) / (omega n * ρ ^ n)) (𝓝[>] 0)
        (𝓝 ((omega n)⁻¹ * sInf (a '' Ioo 0 R))) := by
      simp_rw [hQ]
      exact hT.const_mul _
    exact ⟨hT, hT'.limUnder_eq, hT'⟩
  refine ⟨hmono, ?_, ?_, ?_⟩
  · -- Step 3 (3.10): monotone convergence.
    intro ρ hρ hρR
    have hR : 0 < R := hρ.trans hρR
    obtain ⟨hT, hdens, -⟩ := hlim hR
    set L := sInf (a '' Ioo 0 R) with hL
    have hbdd : BddBelow (a '' Ioo 0 R) := ⟨0, by
      rintro _ ⟨ρ, hρ, rfl⟩
      exact ha0 ρ hρ.1⟩
    have hLle : ∀ s ∈ Ioo 0 R, L ≤ a s := fun s hs ↦ csInf_le hbdd (mem_image_of_mem _ hs)
    set s : ℕ → ℝ := fun k ↦ ρ / (k + 1) with hs
    have hs0 : ∀ k, 0 < s k := fun k ↦ by positivity
    have hsρ : ∀ k, s k ≤ ρ := fun k ↦ div_le_self hρ.le (by norm_cast; omega)
    have hsanti : Antitone s := fun i j hij ↦ by
      simp only [hs]
      gcongr
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
        have hd : 0 < dist x ξ := dist_pos.2 hxξ
        have hts : Tendsto s atTop (𝓝 0) := by
          have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ρ
          rw [mul_zero] at this
          refine this.congr fun k ↦ ?_
          simp only [hs]
          ring
        obtain ⟨k, hk⟩ := (hts.eventually (gt_mem_nhds hd)).exists
        exact ⟨k, hxρ, hk⟩
    -- the lintegrals over `A k` are bounded by `a ρ - L`
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
    have hintξ : IntegrableOn w {ξ} μ := (integrableOn_singleton_iff (hfx := enorm_ne_top)).2 (Or.inl (by rw [hwξ, enorm_zero]))
    have hball : closedBall ξ ρ = (⋃ k, A k) ∪ {ξ} := by
      rw [hUnion, sdiff_union_self, union_eq_left.2 (singleton_subset_iff.2
        (mem_closedBall_self hρ.le))]
    have hint : IntegrableOn w (closedBall ξ ρ) μ := by
      rw [hball]
      exact hintU.union hintξ
    -- the value of the integral
    have hlimU : Tendsto (fun k ↦ ∫ x in A k, w x ∂μ) atTop (𝓝 (∫ x in ⋃ k, A k, w x ∂μ)) :=
      tendsto_setIntegral_of_monotone hAmeas hAmono hintU
    have hsT : Tendsto s atTop (𝓝[>] 0) := by
      have hts : Tendsto s atTop (𝓝 0) := by
        have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ρ
        rw [mul_zero] at this
        refine this.congr fun k ↦ ?_
        simp only [hs]
        ring
      exact tendsto_nhdsWithin_iff.2 ⟨hts, Eventually.of_forall hs0⟩
    have hlim2 : Tendsto (fun k ↦ ∫ x in A k, w x ∂μ) atTop (𝓝 (a ρ - L)) := by
      simp_rw [hAeq]
      exact tendsto_const_nhds.sub (hT.comp hsT)
    have hvalU : ∫ x in ⋃ k, A k, w x ∂μ = a ρ - L := tendsto_nhds_unique hlimU hlim2
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
  · intro ρ hρ hρR
    have hR : 0 < R := hρ.trans hρR
    obtain ⟨-, hdens, -⟩ := hlim hR
    have hbdd : BddBelow (a '' Ioo 0 R) := ⟨0, by
      rintro _ ⟨ρ, hρ, rfl⟩
      exact ha0 ρ hρ.1⟩
    rw [hQ, hdens]
    exact mul_le_mul_of_nonneg_left (csInf_le hbdd (mem_image_of_mem _ ⟨hρ, hρR⟩)) hωinv

end Submission

end

end GMT.Ch04

## Key steps

1. Elementary facts: w ≥ 0, w(ξ) = 0 (division by 0 is 0), a ≥ 0 on (0, ∞), μ(B_r)/(ω_n rⁿ) = ω_n⁻¹a(r), ω_n⁻¹ ≥ 0
2. Annulus identity and ∫ w ≥ 0 give that a is monotone on (0, R) (3.8)
3. Monotone and bounded below by 0: a(s) → L = inf_{(0,R)} a as s ↓ 0; the quotient tends to ω_n⁻¹L, so V.density ξ = ω_n⁻¹L (limUnder on the nontrivial filter 𝓝[>]0) and HasDensityAt (3.9)
4. L ≤ a(ρ) gives V.density ξ ≤ μ(B_ρ)/(ω_nρⁿ)
5. Monotone convergence on A_k = B_ρ ∖ B_{ρ/(k+1)} ↑ B_ρ ∖ {ξ}: lintegral ≤ a(ρ) − L < ∞, integrability on B_ρ using w(ξ) = 0, ∫_{B_ρ} w = a(ρ) − L, hence 3.10

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json`
- `sha256sum GMT/Ch04/Contract.lean GMT/Ch04/Submission.lean <snapshot>/project/GMT/Ch04/Contract.lean`
- `rg -n 'theorem (MonotoneOn|Monotone)\.tendsto_nhdsWithin_I(oi|io|oo)' <snapshot>/mathlib/Mathlib`
- `rg -n 'tendsto_nhdsWithin_Ioo_left|tendsto_nhdsWithin_Ioo_right|MonotoneOn.tendsto_nhdsGT|tendsto_nhdsGT' <snapshot>/mathlib/Mathlib/Topology/Order/*.lean`
- `rg -n 'theorem tendsto_measure_cthickening|theorem tendsto_measure_closedBall|tendsto_measure_biInter_gt|theorem tendsto_measure_iInter|tendsto_measure_cthickening_of_isCompact' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem (tendsto_setIntegral_of_monotone|tendsto_setLIntegral_of_monotone|lintegral_iUnion_mono|setLIntegral_iUnion_of_directed|lintegral_iUnion_of_directed|integrableOn_iUnion_of_summable|tendsto_lintegral_of_monotone)' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem gradient_const|theorem gradient_fun_const' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem locallyIntegrableOn_zero|locallyIntegrableOn_const' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem setIntegral_const|theorem integrableOn_singleton_iff|theorem aestronglyMeasurable_iUnion_iff|theorem ofReal_integral_eq_lintegral_ofReal|theorem Tendsto.limUnder_eq|theorem lintegral_singleton' <snapshot>/mathlib/Mathlib`
- `rg -n 'limUnder_eq' <snapshot>/mathlib/Mathlib/Topology/Separation/*.lean`
- `rg -n 'UpperSemicontinuous|monotonicity|HasDensity' lake-packages-25730c7c/simongmt/Poincare/SimonGMT`
- `grep -rl 'stationary_ratio_limit_of_annulus_identity|stationary_density_usc_of_ratio_bound' .humanize GMT lake-packages-25730c7c/simongmt/Poincare lake-packages-25730c7c/mathlib/Mathlib`
- `sed -n 290,365p book/sources/chapter-04-source.txt`
- `lake env lean GMT/Ch04/Submission.lean -o /tmp/sm-a1-audit/olean/GMT/Ch04/Submission.olean`
- `LEAN_PATH=$(lake env printenv LEAN_PATH):/tmp/sm-a1-audit/olean lean /tmp/sm-a1-audit/{Assembly,ChildA,ChildB,Combined,Bare}.lean (with #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/project/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Topology/Order/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Metric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Countable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Topology/Separation/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/Density.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-stationary-monotonicity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-weighted-monotonicity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root/speculative-prompt-v2.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-04-source.txt`
- `/tmp/sm-a1-audit/Assembly.lean`
- `/tmp/sm-a1-audit/ChildA.lean`
- `/tmp/sm-a1-audit/ChildB.lean`
- `/tmp/sm-a1-audit/Combined.lean`
- `/tmp/sm-a1-audit/Bare.lean`

The snapshot contract is byte-identical to the workspace Contract.lean and Submission.lean (sha256 6e58e5dd…0f4770b); the Mathlib revision is 25730c7c.

Every ingredient of the two children exists in the pinned Mathlib:
- MonotoneOn.tendsto_nhdsWithin_Ioo_right (Topology/Order/Monotone.lean:457): the monotone limit at 0+.
- tendsto_measure_biInter_gt (MeasureTheory/Measure/Continuity.lean:266): continuity from above on the closed balls B_{ρ+δ}(ξ).
- setLIntegral_iUnion_of_directed (Integral/Lebesgue/Basic.lean:668) and tendsto_setIntegral_of_monotone (Integral/Bochner/Set.lean:290): monotone convergence on B_ρ∖B_{ρ/(k+1)}.
- integrableOn_singleton_iff (Integral/IntegrableOn.lean:211; it has an autoParam hfx) and ofReal_integral_eq_lintegral_ofReal (Bochner/Basic.lean:739).
- Filter.Tendsto.limUnder_eq (Topology/Separation/Hausdorff.lean:296).

The parent's Steps 1–2 use gradient_fun_const (Gradient/Basic.lean:368), locallyIntegrableOn_zero (LocallyIntegrable.lean:379) and setIntegral_const (Bochner/Set.lean:524).

SimonGMT's Chapter04 upper-semicontinuity and density lemmas (Density.lean:470 IsStationaryIn.upperSemicontinuousOn_stationaryDensityReal) are stated for its own structure RectifiableVarifold (Chapter04/Basic.lean:53, with a lower-density ℝ≥0∞ density), not for the contract's quotient type and limUnder density. They are not usable here, and the children need nothing from SimonGMT.

The two new names (stationary_ratio_limit_of_annulus_identity, stationary_density_usc_of_ratio_bound) occur nowhere in .humanize, GMT, SimonGMT or Mathlib.

With GMT.Ch04.Submission compiled to an olean:
- Both child types elaborate in the bare contract scope.
- Complete Lean proofs of both children compile with no errors or warnings, depending only on propext, Classical.choice and Quot.sound.
- The parent assembly typechecks against the sibling's exact frozen type plus the two children. Its only sorryAx comes from the stubbed sibling.

Simon Ch. 4, 3.6–3.11 (local source lines 290–349) matches the parent's Steps 3–6.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: https://github.com/ZhengyangZhang06/gmt-formalize/pull/501

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
