<!-- theorem-id: gmt-ch04/root.tangent_structure-a1.piece_weighted_blowup-a1.good_point_blowup-a1 -->

## Theorem `Submission.ts_pwb_blowup_at_good_point`

Let n, ℓ ∈ ℕ, E := Ambient n ℓ = ℝ^{n+ℓ}, Hⁿ := μHE[n], let a = (M, θ) be an admissible pair (RectifiablePair n ℓ) with weight μ := (mk a).weight, let N ⊆ E be Borel with Hⁿ(N) < ∞, K ⊆ E compact with K ⊆ M ∩ N, x ∈ K a point at which θ restricted to K is continuous (ContinuousWithinAt θ K x), f ∈ C_c(E, ℝ), and Γ, L ∈ ℝ. Assume (H1) Hⁿ(N ∩ B_ρ(x)) ≤ ofReal(Γρⁿ) for every ρ > 0; (H2) μ(Kᶜ ∩ B_r(x))/rⁿ → 0 as r ↓ 0; (H3) (Hⁿ⌞N)(Kᶜ ∩ B_r(x))/rⁿ → 0 as r ↓ 0; (H4) (tⁿ)⁻¹∫_N f(t⁻¹(y − x)) dHⁿ(y) → L as t ↓ 0. (B_r(x) is the closed ball, Kᶜ = E ∖ K, and the measures in (H2), (H3) are taken as real numbers via toReal.) Then (tⁿ)⁻¹∫ f(t⁻¹(y − x)) dμ(y) → θ(x)·L as t ↓ 0.

Node: `root.tangent_structure-a1.piece_weighted_blowup-a1.good_point_blowup-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/292

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/820

Decomposition children: None

## Lean problem

Declaration: `Submission.ts_pwb_blowup_at_good_point`

```lean
∀ (n ℓ : ℕ) (a : RectifiablePair n ℓ) (N K : Set (Ambient n ℓ)) (x : Ambient n ℓ) (f : C_c(Ambient n ℓ, ℝ)) (Γ L : ℝ), MeasurableSet N → (μHE[n] : Measure (Ambient n ℓ)) N ≠ ⊤ → IsCompact K → K ⊆ a.M ∩ N → x ∈ K → ContinuousWithinAt a.θ K x → (∀ ρ : ℝ, 0 < ρ → (μHE[n] : Measure (Ambient n ℓ)) (N ∩ closedBall x ρ) ≤ ENNReal.ofReal (Γ * ρ ^ n)) → Tendsto (fun r : ℝ ↦ (mk a).weight.real (Kᶜ ∩ closedBall x r) / r ^ n) (𝓝[>] 0) (𝓝 0) → Tendsto (fun r : ℝ ↦ ((μHE[n] : Measure (Ambient n ℓ)).restrict N).real (Kᶜ ∩ closedBall x r) / r ^ n) (𝓝[>] 0) (𝓝 0) → Tendsto (fun t : ℝ ↦ (t ^ n)⁻¹ * ∫ y in N, f (t⁻¹ • (y - x)) ∂μHE[n]) (𝓝[>] 0) (𝓝 L) → Tendsto (fun t : ℝ ↦ (t ^ n)⁻¹ * ∫ y, f (t⁻¹ • (y - x)) ∂(mk a).weight) (𝓝[>] 0) (𝓝 (a.θ x * L))
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

- Parent DAG node: `root.tangent_structure-a1.piece_weighted_blowup-a1`
- Child DAG node: `root.tangent_structure-a1.piece_weighted_blowup-a1.good_point_blowup-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 7 of the parent proof (the four-term comparison at a good point; Simon Ch. 3, proof of Theorem 1.6 '⇒' together with Remark 1.8(1)). The good-point properties used there, namely (a'), (b'), the bound (3b), the limit (3a) of the sibling ts_piece_density_blowup and the continuity of θ on the Lusin piece, are here the hypotheses (H2), (H3), (H1), (H4) and ContinuousWithinAt θ K x. No errata apply.

Notation. E := Ambient n ℓ, Hⁿ := μHE[n], M := a.M, θ := a.θ, μ := (mk a).weight, B_r(x) := closed ball, Kᶜ := E ∖ K, μ.real(S) := μ(S).toReal. All integrals are Hⁿ-integrals unless μ is indicated. Uses the sibling ts_pwb_pair_weight_integral (applied to a): (W1) μ(K') < ∞ for every compact K' ⊆ E; (W2) ∫ h dμ = ∫_M θh dHⁿ for every function h: E → ℝ.

1. Constants of f. f is continuous with compact support, so there is m ≥ 0 with |f(z)| ≤ m for every z. The topological support of f is compact, hence bounded: there is C₀ with |z| ≤ C₀ for z ∈ tsupport f. Put R := max(C₀, 1) > 0; then f(z) = 0 whenever |z| > R (such z lies outside tsupport f).

2. Rescaled functions. For t > 0 put g_t(y) := f(t⁻¹(y − x)) and B_t := B_{Rt}(x). Then g_t is continuous, |g_t| ≤ m, and g_t(y) = 0 for every y ∉ B_t: if |y − x| > Rt then |t⁻¹(y − x)| = t⁻¹|y − x| > R.

3. Integrability (t > 0). (a) g_t is Hⁿ-integrable on N, since it is Borel, bounded by m, and Hⁿ(N) < ∞; hence it is also integrable on the subsets K and N ∖ K. (b) θ·g_t is Hⁿ-integrable on M: θ is Hⁿ-integrable on M ∩ B_t because B_t is compact (admissibility of a), and g_t is a bounded measurable function, so θ·g_t is integrable on M ∩ B_t; it vanishes on M ∖ B_t by step 2, and M is Hⁿ-null-measurable, so θ·g_t is integrable on M (IntegrableOn.of_ae_sdiff_eq_zero). Consequently θ·g_t is integrable on K ⊆ M, and so is (θ − θ(x))·g_t = θg_t − θ(x)g_t.

4. Decomposition (t > 0).
(a) ∫ g_t dμ = ∫_M θg_t, by (W2) with h = g_t.
(b) ∫_M θg_t = ∫_{M∩K} θg_t + ∫_{M∖K} θg_t, because K is Borel and θg_t is integrable on M (step 3(b)); and M ∩ K = K since K ⊆ M.
(c) ∫_{M∖K} θg_t = ∫_{Kᶜ} g_t dμ. Indeed, by (W2) with h = 1_{Kᶜ}·g_t: ∫_{Kᶜ} g_t dμ = ∫ 1_{Kᶜ}g_t dμ = ∫_M θ·1_{Kᶜ}g_t = ∫_M 1_{Kᶜ}·(θg_t) = ∫_{M∩Kᶜ} θg_t (Kᶜ is Borel), and M ∩ Kᶜ = M ∖ K.
(d) ∫_K θg_t = θ(x)∫_K g_t + ∫_K (θ − θ(x))g_t, by linearity (both integrands integrable on K by step 3).
(e) ∫_K g_t = ∫_N g_t − ∫_{N∖K} g_t, because K ⊆ N, K is Borel and g_t is integrable on N.
Combining (a)–(e) and multiplying by (tⁿ)⁻¹:
(tⁿ)⁻¹∫ g_t dμ = θ(x)·T₁(t) − θ(x)·T₂(t) + T₃(t) + T₄(t), where
T₁(t) := (tⁿ)⁻¹∫_N g_t, T₂(t) := (tⁿ)⁻¹∫_{N∖K} g_t, T₃(t) := (tⁿ)⁻¹∫_K (θ − θ(x))g_t, T₄(t) := (tⁿ)⁻¹∫_{Kᶜ} g_t dμ.

5. Rescaling the hypotheses. Since R > 0, the map t ↦ Rt sends (0, ∞) into (0, ∞) and tends to 0 as t → 0, so it maps the filter of right-neighbourhoods of 0 into itself. Hence (H2) and (H3) give Q_μ(Rt) → 0 and Q_N(Rt) → 0 as t ↓ 0, where Q_μ(r) := μ.real(Kᶜ ∩ B_r(x))/rⁿ and Q_N(r) := (Hⁿ⌞N).real(Kᶜ ∩ B_r(x))/rⁿ. Note that (tⁿ)⁻¹ = Rⁿ/(Rt)ⁿ for t > 0.

6. T₁(t) → L as t ↓ 0: T₁(t) is exactly the expression in (H4).

7. T₂(t) → 0. Fix t > 0. Since g_t = 0 on (N ∖ K) ∖ B_t, ∫_{N∖K} g_t = ∫_{(N∖K)∩B_t} g_t, and |∫_{(N∖K)∩B_t} g_t| ≤ m·Hⁿ.real((N ∖ K) ∩ B_t) (the set has finite measure, being contained in N). Since (N ∖ K) ∩ B_t = (Kᶜ ∩ B_t) ∩ N and Kᶜ ∩ B_t is Borel, Hⁿ((N ∖ K) ∩ B_t) = (Hⁿ⌞N)(Kᶜ ∩ B_t). Hence |T₂(t)| ≤ (tⁿ)⁻¹·m·(Hⁿ⌞N).real(Kᶜ ∩ B_{Rt}(x)) = mRⁿ·Q_N(Rt), which tends to 0 by step 5. So T₂(t) → 0.

8. T₄(t) → 0. Fix t > 0. Since g_t = 0 on Kᶜ ∖ B_t, ∫_{Kᶜ} g_t dμ = ∫_{Kᶜ∩B_t} g_t dμ, and μ(Kᶜ ∩ B_t) ≤ μ(B_t) < ∞ by (W1) (B_t is compact). Hence |T₄(t)| ≤ (tⁿ)⁻¹·m·μ.real(Kᶜ ∩ B_{Rt}(x)) = mRⁿ·Q_μ(Rt), which tends to 0 by step 5.

9. T₃(t) → 0. Let ε > 0 and put c := mRⁿ·max(Γ, 0) + 1 > 0. By continuity of θ restricted to K at x there is δ > 0 such that |θ(y) − θ(x)| < ε/c for every y ∈ K with |y − x| < δ. Let 0 < t < δ/R, so that Rt < δ. Since g_t = 0 off B_t, ∫_K (θ − θ(x))g_t = ∫_{K∩B_t} (θ − θ(x))g_t, and for y ∈ K ∩ B_t we have |y − x| ≤ Rt < δ, hence |(θ(y) − θ(x))g_t(y)| ≤ (ε/c)·m. Moreover, as K ⊆ N, (H1) with ρ := Rt > 0 gives Hⁿ(K ∩ B_t) ≤ Hⁿ(N ∩ B_t) ≤ ofReal(Γ(Rt)ⁿ) < ∞, so Hⁿ.real(K ∩ B_t) ≤ max(Γ(Rt)ⁿ, 0) ≤ max(Γ, 0)·(Rt)ⁿ. Therefore |T₃(t)| ≤ (tⁿ)⁻¹·(ε/c)·m·max(Γ, 0)·(Rt)ⁿ = (ε/c)·mRⁿmax(Γ, 0) = ε(c − 1)/c < ε for all t ∈ (0, δ/R). As ε > 0 was arbitrary, T₃(t) → 0.

10. Conclusion. By steps 6–9, θ(x)T₁(t) − θ(x)T₂(t) + T₃(t) + T₄(t) → θ(x)L − θ(x)·0 + 0 + 0 = θ(x)L as t ↓ 0. By step 4 this expression equals (tⁿ)⁻¹∫ f(t⁻¹(y − x)) dμ(y) for every t > 0, i.e. on a set belonging to the filter of right-neighbourhoods of 0. Hence (tⁿ)⁻¹∫ f(t⁻¹(y − x)) dμ(y) → θ(x)·L as t ↓ 0. (The hypothesis x ∈ K is not needed for this argument; it is kept because it holds in the application, where ContinuousWithinAt θ K x is obtained from continuity of θ on K.) ∎

Implementation note (not part of the mathematical argument): during the decomposition the following Lean proof of exactly the frozen statement was compiled without errors, placed in the frozen contract scope (after `open MeasureTheory Metric Set Filter Topology`, `open scoped ENNReal ContDiff CompactlySupported`, inside `namespace GMT.Ch04`, `noncomputable section`, `open RectifiableVarifold`, and `namespace Submission`) of a file importing `GMT.Ch04.Submission`, `Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace`, `Poincare.SimonGMT.Chapter01.DensityComparison`, `Poincare.SimonGMT.Chapter01.Lusin` and `Poincare.SimonGMT.Chapter02.AreaLiteral` (pinned Lean v4.35.0-rc3, Mathlib 25730c7c, SimonGMT 2b36630); `#print axioms` reports only propext, Classical.choice and Quot.sound. The proof calls the sibling `ts_pwb_pair_weight_integral`. It follows the numbered argument above and may be reused verbatim.

```lean
theorem ts_pwb_blowup_at_good_point : ∀ (n ℓ : ℕ) (a : RectifiablePair n ℓ) (N K : Set (Ambient n ℓ)) (x : Ambient n ℓ) (f : C_c(Ambient n ℓ, ℝ)) (Γ L : ℝ), MeasurableSet N → (μHE[n] : Measure (Ambient n ℓ)) N ≠ ⊤ → IsCompact K → K ⊆ a.M ∩ N → x ∈ K → ContinuousWithinAt a.θ K x → (∀ ρ : ℝ, 0 < ρ → (μHE[n] : Measure (Ambient n ℓ)) (N ∩ closedBall x ρ) ≤ ENNReal.ofReal (Γ * ρ ^ n)) → Tendsto (fun r : ℝ ↦ (mk a).weight.real (Kᶜ ∩ closedBall x r) / r ^ n) (𝓝[>] 0) (𝓝 0) → Tendsto (fun r : ℝ ↦ ((μHE[n] : Measure (Ambient n ℓ)).restrict N).real (Kᶜ ∩ closedBall x r) / r ^ n) (𝓝[>] 0) (𝓝 0) → Tendsto (fun t : ℝ ↦ (t ^ n)⁻¹ * ∫ y in N, f (t⁻¹ • (y - x)) ∂μHE[n]) (𝓝[>] 0) (𝓝 L) → Tendsto (fun t : ℝ ↦ (t ^ n)⁻¹ * ∫ y, f (t⁻¹ • (y - x)) ∂(mk a).weight) (𝓝[>] 0) (𝓝 (a.θ x * L)) := by
  intro n ℓ a N K x f Γ L hNm hNfin hKc hKMN hxK hθc hΓ hA hB hI1
  obtain ⟨hfin, hint⟩ := ts_pwb_pair_weight_integral n ℓ a
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hKM : K ⊆ a.M := fun y hy ↦ (hKMN hy).1
  have hKN : K ⊆ N := fun y hy ↦ (hKMN hy).2
  have hMm := a.isRectifiablePair.measurable
  obtain ⟨m, hm⟩ : ∃ m, ∀ z, ‖f z‖ ≤ m :=
    f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  have hm0 : 0 ≤ m := (norm_nonneg _).trans (hm 0)
  obtain ⟨R, hR, hRs⟩ : ∃ R : ℝ, 0 < R ∧ ∀ z, R < ‖z‖ → f z = 0 := by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 f.hasCompactSupport.isCompact.isBounded
    refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun z hz ↦ ?_⟩
    apply image_eq_zero_of_notMem_tsupport
    intro hzs
    exact absurd (hC z hzs) (not_le.2 (lt_of_le_of_lt (le_max_left _ _) hz))
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
  -- integrability
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
  -- decomposition
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
  have := hfin
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
  -- term T2
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
  -- term T4
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
  -- term T3
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
  have hsum := (((hI1.const_mul (a.θ x)).sub (hT2.const_mul (a.θ x))).add hT3).add hT4
  rw [mul_zero, sub_zero, add_zero, add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (hdec t ht).symm
```

## Key steps

1. Choose m ≥ sup|f| and R > 0 with f = 0 outside B_R(0); g_t(y) := f(t⁻¹(y − x)) is bounded by m and vanishes outside B_{Rt}(x)
2. Integrability: g_t on N (Hⁿ(N) < ∞) and θg_t on M (θ integrable on M ∩ B_{Rt}(x), g_t = 0 elsewhere)
3. Using the sibling formula ∫ h dμ = ∫_M θh dHⁿ twice: (tⁿ)⁻¹∫ g_t dμ = θ(x)T₁ − θ(x)T₂ + T₃ + T₄
4. T₁ → L by (H4); |T₂| ≤ mRⁿ·Q_N(Rt) → 0 by (H3); |T₄| ≤ mRⁿ·Q_μ(Rt) → 0 by (H2) and finiteness of μ on balls
5. |T₃| ≤ (ε/c)·mRⁿmax(Γ,0) < ε for t < δ/R, by continuity of θ|K at x and the bound (H1)
6. Sum the limits: the blow-up tends to θ(x)L

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json`
- `sha256sum GMT/Ch04/Contract.lean GMT/Ch04/Submission.lean <snapshot>/project/GMT/Ch04/Contract.lean`
- `git -C .lake/packages/simongmt rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD`
- `python3: list dag.json nodes (id, status, lean_name, lean_statement) for name-collision and reuse checks`
- `grep -rn 'theorem ae_dimensionalUpperDensity_eq_zero_outside|theorem measure_toOuterMeasure_isBorelRegular|theorem simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure|theorem exists_isClosed_continuousOn_of_measurable|theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn|def dimensionalUpperDensity|def realUnitBallVolume' .lake/packages/simongmt/Poincare/`
- `grep -rn 'def IsOpenSigmaFinite|def IsCaratheodoryMeasurable|realUnitBallVolume_pos|realUnitBallVolume_ne_top' .lake/packages/simongmt/Poincare/SimonGMT`
- `rg -n 'theorem ae_tendsto_measure_inter_div|theorem integral_withDensity_eq_integral_toReal_smul₀|theorem ae_restrict_mem₀|exists_isClosed_sdiff_lt|euclideanHausdorffMeasure_eq_volume' <snapshot>/mathlib/Mathlib`
- `rg -n 'measure_eq_zero_iff_ae_notMem|ae_all_iff|ae_restrict_of_ae|isFiniteMeasure_restrict|aestronglyMeasurable_iUnion_iff|of_pseudoMetrizableSpace_of_isFiniteMeasure|exists_measurable_subset_ae_eq|tendsto_of_liminf_eq_limsup|ofReal_le_enorm' <snapshot>/mathlib/Mathlib`
- `rg -n 'integral_inter_add_sdiff|setIntegral_eq_of_subset_of_forall_sdiff_eq_zero|IntegrableOn.of_ae_sdiff_eq_zero|Integrable.mul_bdd|IntegrableOn.of_bound|norm_setIntegral_le_of_norm_le_const|setIntegral_indicator|lt_inv_mul_iff₀|bounded_above_of_compact_support' <snapshot>/mathlib/Mathlib`
- `lake env lean GMT/Ch04/Submission.lean -o /tmp/pwb-decomp/olean/GMT/Ch04/Submission.olean`
- `python3 /tmp/pwb-decomp/scripts/gen.py (verifier gmt-compare.child_modules + lean_contract.validate_lean_statement); lean /tmp/pwb-decomp/gen/Challenge_*.lean`
- `lean /tmp/pwb-decomp/inst/Plain.lean and /tmp/pwb-decomp/inst/WithImports.lean (pp.all) then diff`
- `lean /tmp/pwb-decomp/asm/Assembly.lean (parent from sorry'd children and sibling)`
- `lean /tmp/pwb-decomp/probe/Full.lean and /tmp/pwb-decomp/out/Verify.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/project/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-piece-weighted-blowup-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-piece-weighted-blowup-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-piece-weighted-blowup-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-piece-density-blowup-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLiteral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Topology/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Normed/Group/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Algebra/Order/GroupWithZero/Basic.lean`
- `/tmp/pwb-decomp/gen/Challenge_ts_pwb_pair_weight_integral.lean`
- `/tmp/pwb-decomp/gen/Challenge_ts_pwb_upper_density_vanish_ae.lean`
- `/tmp/pwb-decomp/gen/Challenge_ts_pwb_lusin_compact_cover.lean`
- `/tmp/pwb-decomp/gen/Challenge_ts_pwb_density_points_of_image_ae.lean`
- `/tmp/pwb-decomp/gen/Challenge_ts_pwb_blowup_at_good_point.lean`
- `/tmp/pwb-decomp/inst/Plain.lean`
- `/tmp/pwb-decomp/inst/WithImports.lean`
- `/tmp/pwb-decomp/asm/Assembly.lean`
- `/tmp/pwb-decomp/probe/Full.lean`
- `/tmp/pwb-decomp/out/Verify.lean`

Snapshot and pins:
- The snapshot contract, the workspace Contract.lean and the workspace Submission.lean are byte-identical (sha256 6e58e5dd…0f4770b).
- simongmt is at the pinned 2b3663083f3fe399b6296fb8eaee52169170e197 and mathlib at 25730c7c759d108ef87ab70af2342a196760f79d, as in the manifest.

Library results used by the children (each exists with the stated meaning; every child built on them prints only propext, Classical.choice, Quot.sound):
- SimonGMT (Chapter01/02): ae_dimensionalUpperDensity_eq_zero_outside (Simon 1.3.6), measure_toOuterMeasure_isBorelRegular, realUnitBallVolume_pos and realUnitBallVolume_ne_top, dimensionalDensityQuotient (closed balls), exists_isClosed_continuousOn_of_measurable (Lusin 1.17), euclideanHausdorffMeasure_image_le_of_lipschitzOn, simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure.
- Mathlib snapshot: Besicovitch.ae_tendsto_measure_inter_div, integral_withDensity_eq_integral_toReal_smul₀, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure, MeasurableSet.exists_isClosed_sdiff_lt, NullMeasurableSet.exists_measurable_subset_ae_eq, aestronglyMeasurable_iUnion_iff, ae_restrict_mem₀, tendsto_of_liminf_eq_limsup, integral_inter_add_sdiff, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero, IntegrableOn.of_ae_sdiff_eq_zero, norm_setIntegral_le_of_norm_le_const.
- The Mathlib snapshot has no Lusin theorem, so the SimonGMT one is used.
- No existing DAG declaration matches any child type. The accepted lusin_compact_exhaustion_of_measurable concerns volume on ℝⁿ.

Elaboration checks:
- All five child types elaborate in comparator-generated challenge files.
- They are unchanged (pp.all byte-identical) when the implementation imports are added.
- The parent's frozen type is proved from them plus the sibling (Assembly.lean).
- All five children are fully proved (Full.lean, Verify.lean).


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: https://github.com/ZhengyangZhang06/gmt-formalize/pull/1571

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
