<!-- theorem-id: gmt-ch04/root.tangent_structure-a1.first_variation_pieces-a1 -->

## Theorem `Submission.ts_first_variation_of_pieces`

Let n ≥ 1, ℓ ≥ 0, a = (M, θ) an admissible pair in E = ℝ^{n+ℓ}, V = v(M, θ) with weight μ_V and tangent spaces T_x = V.tangentSpace x. Assume: N₀ ⊆ E is Borel with Hⁿ(N₀) = 0; (C_i, F_i)_{i∈ℕ} are Lipschitz pieces (C_i ⊆ ℝⁿ compact, F_i Lipschitz, differentiable on C_i with injective DF_i, DF_i continuous on C_i, c_i|v − w| ≤ |F_i(v) − F_i(w)| on C_i with c_i > 0) with M ⊆ N₀ ∪ ⋃_i F_i(C_i); for Hⁿ-a.e. x ∈ M, T_x = DF_i(w)(ℝⁿ) for every i and every w ∈ C_i with F_i(w) = x; and x ↦ p_{T_x} is a.e. strongly measurable for Hⁿ⌞M. Then for every compact variation (φ, ε, K) as in Ch. 4, 2.1 (IsCompactVariation φ ε K), the function t ↦ (imageMass a (φ t) K).toReal = M(φ_t#(V⌞K)) has derivative ∫ div_M X dμ_V at t = 0, where X(y) = ∂_tφ(t, y)|_{t=0} and div_M X = V.tangentialDiv X.

Node: `root.tangent_structure-a1.first_variation_pieces-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/55

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/884, https://github.com/ZhengyangZhang06/gmt-formalize/issues/886, https://github.com/ZhengyangZhang06/gmt-formalize/issues/889, https://github.com/ZhengyangZhang06/gmt-formalize/issues/892

## Lean problem

Declaration: `Submission.ts_first_variation_of_pieces`

```lean
∀ (n ℓ : ℕ) (a : RectifiablePair n ℓ) (N₀ : Set (Ambient n ℓ)) (C : ℕ → Set (EuclideanSpace ℝ (Fin n))) (F : ℕ → EuclideanSpace ℝ (Fin n) → Ambient n ℓ) (φ : ℝ → Ambient n ℓ → Ambient n ℓ) (ε : ℝ) (K : Set (Ambient n ℓ)), 0 < n → MeasurableSet N₀ → (μHE[n] : Measure (Ambient n ℓ)) N₀ = 0 → a.M ⊆ N₀ ∪ ⋃ i, F i '' C i → (∀ i, IsCompact (C i) ∧ (∃ K : NNReal, LipschitzWith K (F i)) ∧ (∀ w ∈ C i, DifferentiableAt ℝ (F i) w ∧ Function.Injective (fderiv ℝ (F i) w)) ∧ ContinuousOn (fderiv ℝ (F i)) (C i) ∧ ∃ c : ℝ, 0 < c ∧ ∀ v ∈ C i, ∀ w ∈ C i, c * ‖v - w‖ ≤ ‖F i v - F i w‖) → (∀ᵐ x ∂(μHE[n] : Measure (Ambient n ℓ)).restrict a.M, ∀ i, ∀ w ∈ C i, F i w = x → (mk a).tangentSpace x = LinearMap.range (fderiv ℝ (F i) w).toLinearMap) → AEStronglyMeasurable (fun x ↦ ((mk a).tangentSpace x).starProjection) ((μHE[n] : Measure (Ambient n ℓ)).restrict a.M) → IsCompactVariation φ ε K → HasDerivAt (fun t ↦ (imageMass a (φ t) K).toReal) (∫ x, (mk a).tangentialDiv (fun y ↦ deriv (fun t ↦ φ t y) 0) x ∂(mk a).weight) 0
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

- Parent DAG node: `root.tangent_structure-a1`
- Child DAG node: `root.tangent_structure-a1.first_variation_pieces-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the parent proof, steps 7–10 (Simon Ch. 4, 2.1–2.2 with the area formula of Ch. 3 §2, 2.4–2.5, and the computation of Ch. 2 §5, 5.2–5.3). The parent's references to its steps 4–6 ("T_i(x) = T_x for Hⁿ-a.e. x ∈ M_i", "x ↦ p_x is μ-a.e. strongly measurable", "dim T_x = n a.e.") are replaced by the hypotheses of this theorem (step 0 below). No errata apply.

Conventions. n ≥ 1, ℓ ≥ 0; E := Ambient n ℓ; ℝⁿ := EuclideanSpace ℝ (Fin n) with Lebesgue measure Lⁿ; Hⁿ := μHE[n]; B_ρ(z) := closedBall z ρ. a = (M, θ) is an admissible pair (IsRectifiablePair: M countably n-rectifiable and Hⁿ-null-measurable, θ > 0 on M, θ integrable on M ∩ K for every compact K), V := mk a, μ := V.weight, T_x := V.tangentSpace x, p_x := T_x.starProjection, div_M X(x) := V.tangentialDiv X x = trace(DX(x) ∘ p_x). For a subspace P ⊆ E with inclusion ι_P and Λ ∈ L(E, E) put J^P(Λ) := normDet(Λ ∘ ι_P) ≥ 0 (Mathlib LinearMap.normDet of Λ.domRestrict P); for an orthonormal basis e_1, …, e_k of P, J^P(Λ)² = det[⟨Λe_a, Λe_b⟩]_{a,b≤k} (Mathlib LinearMap.normDet_sq_eq_det_gram), J^{0}(Λ) = 1, and J^P(Λ)² = det S_P(Λ) with S_P(Λ) := p_P Λ*Λ p_P + I − p_P ∈ L(E, E) (Λ* = ContinuousLinearMap.adjoint Λ). Proof of the last identity: take an orthonormal basis e_1, …, e_{n+ℓ} of E with e_1, …, e_k a basis of P and e_{k+1}, …, e_{n+ℓ} a basis of P^⊥ (k = dim P). Since p_P is self-adjoint, p_Pe_a = e_a for a ≤ k and p_Pe_b = 0 for b > k, the matrix ⟨S_P(Λ)e_a, e_b⟩ has entries ⟨Λe_a, Λe_b⟩ for a, b ≤ k, entries δ_{ab} for a, b > k, and 0 in the mixed blocks (for a ≤ k < b: ⟨p_PΛ*Λe_a, e_b⟩ = ⟨Λ*Λe_a, p_Pe_b⟩ = 0 and ⟨S_P(Λ)e_b, e_a⟩ = ⟨Λ*Λp_Pe_b, p_Pe_a⟩ + ⟨e_b − p_Pe_b, e_a⟩ = 0 + ⟨e_b, e_a⟩ = 0); hence det S_P(Λ) = det[⟨Λe_a, Λe_b⟩]_{a,b≤k} = J^P(Λ)² by LinearMap.normDet_sq_eq_det_gram (for k = 0 both sides are 1). Consequently J^P(Λ) = (det S_P(Λ))^{1/2} is a continuous function of the pair (Λ, p_P) (polynomial in the entries, followed by the square root of a nonnegative number). For G: ℝⁿ → E, JG(v) := (fderiv ℝ G v).normDet (SimonGMT Chapter02.areaJacobianAt).
Hypotheses: (h1) N₀ ⊆ E Borel with Hⁿ(N₀) = 0; (h2) for each i ∈ ℕ, (C_i, F_i) is a Lipschitz piece: C_i ⊆ ℝⁿ compact, F_i: ℝⁿ → E Lipschitz, F_i differentiable at each w ∈ C_i with injective DF_i(w), DF_i continuous on C_i, c_i|v − w| ≤ |F_i(v) − F_i(w)| on C_i with c_i > 0; (h3) M ⊆ N₀ ∪ ⋃_i F_i(C_i); (h4) for Hⁿ-a.e. x ∈ M: for all i and all w ∈ C_i with F_i(w) = x, T_x = range DF_i(w); (h5) x ↦ p_x is a.e.-strongly measurable for Hⁿ⌞M; (h6) IsCompactVariation φ ε K: ε > 0, K compact, Φ(t, y) := φ t y is C^∞ on U := (−ε, ε) × E, for t ∈ (−ε, ε) φ_t := φ t is bijective with C^∞ inverse Function.invFun φ_t, φ_0 = id, and φ_t(y) = y for t ∈ (−ε, ε), y ∉ K. X(y) := deriv (t ↦ φ t y) 0.
Results used (pinned; standard axioms only): (R2a) SimonGMT Chapter02.weighted_area_formula_lipschitz_injOn (∫⁻_{G(B)} u dHⁿ = ∫⁻_B ofReal(JG(v))·u(G(v)) dLⁿ(v) for Lipschitz G, Borel B, G injective on B, any u: E → [0, ∞]); (R2b) SimonGMT Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn; Mathlib LinearMap.normDet_comp (normDet(Λ ∘ A') = normDet(Λ restricted to range A')·normDet(A'); also SimonGMT Chapter02.areaJacobian_comp_eq_parametrization_mul_tangential), LinearMap.normDet_sq_eq_det_gram, ContDiffAt.isSymmSndFDerivAt (symmetry of second derivatives), hasDerivAt_integral_of_dominated_loc_of_deriv_le (differentiation under the integral sign), lintegral_iUnion₀, integral_withDensity_eq_integral_toReal_smul₀, ofReal_integral_eq_lintegral_ofReal, withDensity_absolutelyContinuous, AEStronglyMeasurable.mono_ac, LinearMap.finrank_range_of_inj.

Proof.

0. Consequences of the hypotheses.
(0a) For Hⁿ-a.e. x ∈ M, dim T_x = n: Hⁿ-a.e. x ∈ M lies outside N₀ (h1), hence (h3) x = F_i(w) for some i and w ∈ C_i; by (h4) T_x = range DF_i(w), whose dimension is dim ℝⁿ = n because DF_i(w) is injective (LinearMap.finrank_range_of_inj, finrank_euclideanSpace_fin).
(0b) μ = (Hⁿ⌞M).withDensity(ofReal ∘ θ) (definition of the weight on the class mk a). θ is a.e.-strongly measurable for Hⁿ⌞M (it is integrable on each M ∩ B_k(0)); μ(S) = ∫⁻_{M∩S} ofReal θ dHⁿ for Borel S, so μ is finite on compact sets; μ ≪ Hⁿ⌞M (withDensity_absolutelyContinuous); and for every Borel S and every g: E → ℝ, ∫_S g dμ = ∫_{M∩S} gθ dHⁿ (integral_withDensity_eq_integral_toReal_smul₀ — no integrability assumption is needed — together with (ofReal θ(z)).toReal = θ(z) for z ∈ M, which holds Hⁿ⌞M-a.e. by ae_restrict_mem₀).
(0c) By (h5) and μ ≪ Hⁿ⌞M, x ↦ p_x is also μ-a.e. strongly measurable (AEStronglyMeasurable.mono_ac).

1. The variation (parent step 7).
(a) Φ is C^∞ on the open set U. X(y) = DΦ(0, y)(1, 0) (chain rule for t ↦ (t, y)), so X is C^∞ on E. For y ∉ K, Φ(t, y) = y for all t ∈ (−ε, ε), hence X(y) = 0; since E ∖ K is open (K is compact, hence closed), DX = 0 on E ∖ K, and therefore div_M X(x) = trace(0 ∘ p_x) = 0 for every x ∉ K.
(b) Let t ∈ (−ε, ε). φ_t = Φ(t, ·) is C^∞, bijective, with C^∞ inverse ψ_t := Function.invFun φ_t, which is a two-sided inverse (Function.leftInverse_invFun / rightInverse_invFun for the bijection φ_t). Differentiating ψ_t ∘ φ_t = id gives Dψ_t(φ_t(y)) ∘ Dφ_t(y) = I, so Dφ_t(y) is invertible for every y; φ_t is a homeomorphism. On the open set E ∖ K, φ_t = id, so Dφ_t(y) = I there; y ↦ Dφ_t(y) is continuous, hence bounded on K, so sup_y ‖Dφ_t(y)‖ < ∞ and φ_t is Lipschitz (mean value inequality on the convex set E). By (R2b), Hⁿ(φ_t(Z)) = 0 whenever Hⁿ(Z) = 0; images of Borel sets under the homeomorphism φ_t are Borel. Consequently φ_t maps Hⁿ-null-measurable sets to Hⁿ-null-measurable sets (a null-measurable set is a Borel set plus a subset of a null set).
(c) The partial derivative (t, y) ↦ Dφ_t(y) is C^∞ on U, and by the symmetry of the second derivative of Φ at (0, y) (ContDiffAt.isSymmSndFDerivAt), ∂_t Dφ_t(y)|_{t=0} = D_y(∂_tΦ(0, ·))(y) = DX(y). Also Dφ_0(y) = I since φ_0 = id.

2. Area formula on M (parent step 8; Simon Ch. 3, 2.4–2.5). For t ∈ (−ε, ε) and x ∈ E let J_t(x) := J^{T_x}(Dφ_t(x)). Claim: imageMass a φ_t K = ∫⁻_{M∩K} ofReal(θ(x)·J_t(x)) dHⁿ(x).
(2.1) By definition imageMass a φ_t K = ∫⁻_{φ_t(M∩K)} u_t dHⁿ with u_t(y) := ofReal(θ(ψ_t(y))), and u_t(φ_t(x)) = ofReal(θ(x)).
(2.2) Decomposition. Let D_i := F_i(C_i) ∖ (N₀ ∪ ⋃_{j<i} F_j(C_j)) (Borel: the F_j(C_j) are compact) and M_i := M ∩ K ∩ D_i (Hⁿ-null-measurable). The M_i are pairwise disjoint and, by (h3), M ∩ K = (M ∩ K ∩ N₀) ∪ ⋃_i M_i. As φ_t is injective, φ_t(M ∩ K) = φ_t(M ∩ K ∩ N₀) ∪ ⋃_i φ_t(M_i) with pairwise disjoint pieces; by 1(b) they are Hⁿ-null-measurable and Hⁿ(φ_t(M ∩ K ∩ N₀)) = 0. By countable additivity of the lintegral over disjoint null-measurable sets (lintegral_iUnion₀) and since null sets do not contribute:
imageMass a φ_t K = Σ_i ∫⁻_{φ_t(M_i)} u_t dHⁿ and ∫⁻_{M∩K} ofReal(θJ_t) dHⁿ = Σ_i ∫⁻_{M_i} ofReal(θJ_t) dHⁿ.
It therefore suffices to prove ∫⁻_{φ_t(M_i)} u_t dHⁿ = ∫⁻_{M_i} ofReal(θJ_t) dHⁿ for each i.
(2.3) Fix i. Choose a Borel set A with M_i ⊆ A ⊆ D_i and Hⁿ(A ∖ M_i) = 0 (a Borel hull of the null-measurable M_i, intersected with the Borel D_i). Let B := C_i ∩ F_i⁻¹(A): B is Borel, F_i(B) = A (A ⊆ F_i(C_i)), and F_i is injective on B (by the lower bound on C_i). Let ψ_i: F_i(C_i) → C_i be the inverse of F_i on C_i and, for y ∈ F_i(C_i), T_i(y) := range DF_i(ψ_i(y)).
(2.4) G := φ_t ∘ F_i is Lipschitz (composition of Lipschitz maps) and injective on B. For v ∈ B, F_i is differentiable at v and φ_t is differentiable at F_i(v), so DG(v) = Dφ_t(F_i(v)) ∘ DF_i(v) (chain rule), and by LinearMap.normDet_comp (normDet(Λ ∘ A') = J^{range A'}(Λ)·normDet(A')),
JG(v) = J^{range DF_i(v)}(Dφ_t(F_i(v)))·JF_i(v) = J^{T_i(F_i(v))}(Dφ_t(F_i(v)))·JF_i(v).
(2.5) Define h: E → [0, ∞] by h(y) := ofReal(J^{T_i(y)}(Dφ_t(y)))·u_t(φ_t(y)) for y ∈ F_i(C_i) and h(y) := 0 otherwise. Applying (R2a) to G on B and then to F_i on B (no measurability of the integrands is needed):
∫⁻_{φ_t(A)} u_t dHⁿ = ∫⁻_{G(B)} u_t dHⁿ = ∫⁻_B ofReal(JG(v))·u_t(G(v)) dv = ∫⁻_B ofReal(JF_i(v))·h(F_i(v)) dv = ∫⁻_{F_i(B)} h dHⁿ = ∫⁻_A h dHⁿ,
using ofReal(αβ) = ofReal(α)ofReal(β) for α, β ≥ 0 and (2.4).
(2.6) Since Hⁿ(A ∖ M_i) = 0 and, by 1(b), Hⁿ(φ_t(A ∖ M_i)) = 0, we get ∫⁻_{φ_t(M_i)} u_t dHⁿ = ∫⁻_{φ_t(A)} u_t dHⁿ and ∫⁻_A h dHⁿ = ∫⁻_{M_i} h dHⁿ. For Hⁿ-a.e. x ∈ M_i we have x = F_i(ψ_i(x)) with ψ_i(x) ∈ C_i, so (h4) gives T_x = range DF_i(ψ_i(x)) = T_i(x), and then h(x) = ofReal(J_t(x))·ofReal(θ(x)) = ofReal(θ(x)J_t(x)) (θ(x) > 0, J_t(x) ≥ 0). Hence ∫⁻_{φ_t(M_i)} u_t dHⁿ = ∫⁻_{M_i} ofReal(θJ_t) dHⁿ, and summing over i (2.2) proves the claim.

3. The Jacobian (parent step 9; Simon Ch. 2, 5.2–5.3).
(3.1) On the compact set [−ε/2, ε/2] × K the maps (t, y) ↦ Dφ_t(y), ∂_tDφ_t(y) and Dφ_t(y)⁻¹ are continuous (1(b), 1(c); inversion is continuous on invertible operators), hence bounded in operator norm by some Λ_1 ≥ 1.
(3.2) Fix x ∈ K and an n-dimensional subspace P with orthonormal basis e_1, …, e_n. For t ∈ (−ε, ε) let Gram_t := [⟨Dφ_t(x)e_a, Dφ_t(x)e_b⟩]_{a,b=1}^n, so J^P(Dφ_t(x)) = (det Gram_t)^{1/2} (LinearMap.normDet_sq_eq_det_gram). By 1(c), t ↦ Gram_t is C¹, Gram_0 = I, and ∂_tGram_t|_{t=0} = [⟨DX(x)e_a, e_b⟩ + ⟨e_a, DX(x)e_b⟩]_{a,b}, whose trace is 2Σ_a⟨DX(x)e_a, e_a⟩ = 2·trace(DX(x) ∘ p_P) (compute the trace of DX(x) ∘ p_P in an orthonormal basis of E extending (e_a): p_P fixes the e_a and kills the other basis vectors).
(3.3) For |t| ≤ ε/2: ⟨Gram_t ξ, ξ⟩ = |Dφ_t(x)(Σ_a ξ_a e_a)|² ≥ Λ_1⁻²|ξ|², so the symmetric matrix Gram_t is positive definite, det Gram_t > 0, ‖Gram_t⁻¹‖ ≤ Λ_1², ‖Gram_t‖ ≤ Λ_1², ‖∂_tGram_t‖ ≤ 2Λ_1², and det Gram_t ≤ ‖Gram_t‖ⁿ ≤ Λ_1^{2n}. Jacobi's formula: writing det(G + H) = det G·det(I + G⁻¹H) and expanding det(I + Y) = 1 + trace Y + O(|Y|²) by the Leibniz formula, d/dt det Gram_t = det Gram_t·trace(Gram_t⁻¹∂_tGram_t). Since det Gram_t > 0, t ↦ J^P(Dφ_t(x)) = (det Gram_t)^{1/2} is differentiable on (−ε/2, ε/2) with
∂_tJ^P(Dφ_t(x)) = ½·J^P(Dφ_t(x))·trace(Gram_t⁻¹∂_tGram_t);
at t = 0 this equals ½·trace(∂_tGram_t|_{t=0}) = trace(DX(x) ∘ p_P). Using |trace Y| ≤ n‖Y‖ for n×n matrices: |∂_tJ^P(Dφ_t(x))| ≤ ½·Λ_1ⁿ·n·Λ_1²·2Λ_1² = nΛ_1^{n+4} =: C_1, uniformly for |t| < ε/2, x ∈ K and n-dimensional P. Also 0 ≤ J^P(Dφ_t(x)) ≤ Λ_1ⁿ.
(3.4) Measurability. For each t ∈ (−ε, ε), x ↦ J_t(x) = (det(p_x Dφ_t(x)*Dφ_t(x) p_x + I − p_x))^{1/2} is a continuous function of (Dφ_t(x), p_x); x ↦ Dφ_t(x) is continuous and x ↦ p_x is a.e.-strongly measurable for Hⁿ⌞M (h5), so x ↦ J_t(x) is a.e.-strongly measurable for Hⁿ⌞M. Likewise x ↦ div_M X(x) = trace(DX(x) ∘ p_x) is a.e.-strongly measurable for Hⁿ⌞M and (0c) for μ; it vanishes off K (1(a)) and |div_M X(x)| ≤ (n + ℓ)·sup_K‖DX‖ (|trace Y| ≤ dim E·‖Y‖, ‖p_x‖ ≤ 1), so it is μ-integrable (μ(K) < ∞).

4. Conclusion (parent step 10).
(4.1) For |t| < ε/2 put m(t) := ∫_{M∩K} θ(x)J_t(x) dHⁿ(x). By (0a) and (3.3), for Hⁿ-a.e. x ∈ M ∩ K, 0 ≤ J_t(x) ≤ Λ_1ⁿ; θ is integrable on M ∩ K; so θJ_t is integrable on M ∩ K with nonnegative values, and by step 2 and ofReal_integral_eq_lintegral_ofReal, imageMass a φ_t K = ofReal(m(t)) < ∞. Hence (imageMass a (φ t) K).toReal = m(t) for |t| < ε/2.
(4.2) Differentiation under the integral sign (hasDerivAt_integral_of_dominated_loc_of_deriv_le, on the ball |t| < ε/2 and the measure Hⁿ⌞(M ∩ K)): for each such t the integrand x ↦ θ(x)J_t(x) is a.e.-strongly measurable (3.4) and θJ_0 = θ is integrable (J_0 = J^{T_x}(I) = 1); for Hⁿ-a.e. x ∈ M ∩ K (those with dim T_x = n, (0a)) the map t ↦ θ(x)J_t(x) is differentiable at every t with |t| < ε/2, with derivative θ(x)∂_tJ_t(x) bounded by C_1θ(x) (an integrable bound) by (3.3) with P = T_x, and its derivative at t = 0 is θ(x)·trace(DX(x) ∘ p_x) = θ(x)·div_M X(x), which is a.e.-strongly measurable. Therefore m has derivative ∫_{M∩K} θ·div_M X dHⁿ at t = 0.
(4.3) By (0b) with S = K and since div_M X = 0 off K (1(a)) and is μ-integrable (3.4): ∫_{M∩K} θ·div_M X dHⁿ = ∫_K div_M X dμ = ∫ div_M X dμ = ∫ V.tangentialDiv X x dμ_V(x).
(4.4) The function t ↦ (imageMass a (φ t) K).toReal coincides with m on the neighbourhood (−ε/2, ε/2) of 0 (4.1), so it has the same derivative at 0 (HasDerivAt.congr_of_eventuallyEq): HasDerivAt (fun t ↦ (imageMass a (φ t) K).toReal) (∫ x, (mk a).tangentialDiv (fun y ↦ deriv (fun t ↦ φ t y) 0) x ∂(mk a).weight) 0. ∎

Implementation note (not part of the argument): the statement elaborates with the frozen imports; the proof needs, e.g., Mathlib.Analysis.InnerProductSpace.NormDet, Mathlib.Analysis.InnerProductSpace.Adjoint, Mathlib.Analysis.Calculus.ParametricIntegral, Mathlib.Analysis.Calculus.FDeriv.Symmetric and Poincare.SimonGMT.Chapter02.AreaLipschitz (built in the pinned packages); the frozen child types elaborate unchanged with them. Natural sub-lemmas for a further split are step 2 (area formula for φ_t on M) and steps 3–4 (Jacobian derivative and differentiation under the integral sign).

## Key steps

1. From the hypotheses: dim T_x = n Hⁿ-a.e. on M, μ_V = θHⁿ⌞M ≪ Hⁿ⌞M, and x ↦ p_{T_x} is μ_V-a.e. strongly measurable
2. Variation facts: X is smooth, X = DX = div_M X = 0 off K; φ_t is a Lipschitz homeomorphism with invertible Dφ_t; ∂_tDφ_t|_{t=0} = DX
3. Area formula through the disjointified pieces and normDet_comp: imageMass a φ_t K = ∫⁻_{M∩K} ofReal(θ J^{T_x}(Dφ_t(x))) dHⁿ
4. Jacobi's formula: ∂_tJ^{T_x}(Dφ_t(x))|_{t=0} = trace(DX(x)∘p_x), with a uniform bound C_1 on [−ε/2, ε/2] × K
5. Differentiation under the integral sign, dominated by C_1θ, then ∫_{M∩K} θ div_M X dHⁿ = ∫ div_M X dμ_V

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `sha256sum <snapshot>/project/GMT/Ch04/Contract.lean GMT/Ch04/Contract.lean GMT/Ch04/Submission.lean`
- `git -C .lake/packages/simongmt rev-parse HEAD`
- `grep -n 'HasWeightedApproximateTangentSpaceAt\|def CountablyRectifiable\|def blowUpMap' -r .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/`
- `grep -n '^theorem\|^def' Chapter04/{WeightedBlowUp,TangentDensity,FirstVariation,Basic}.lean`
- `grep -rn 'weighted_area_formula_lipschitz_injOn|euclideanHausdorffMeasure_image_le_of_lipschitzOn|ae_dimensionalUpperDensity_eq_zero_outside|measure_toOuterMeasure_isBorelRegular|simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure|exists_isClosed_continuousOn_of_measurable|areaJacobian_comp_eq_parametrization_mul_tangential|def areaJacobianAt|planeMeasure_unit_closedBall|hausdorff_blowUp_image' .lake/packages/simongmt/Poincare/SimonGMT`
- `grep -rn 'continuous.*normDet|measurable_areaJacobianAt' .lake/packages/simongmt/Poincare/SimonGMT`
- `rg -n 'theorem .*[Ll]usin|lusin' <snapshot>/mathlib/Mathlib`
- `rg -n 'measure_eq_zero_iff_ae_notMem|ofReal_le_enorm|Regular.smul|exists_isClosed_sdiff_lt' <snapshot>/mathlib/Mathlib`
- `grep -rn 'InnerProductSpace.volume_closedBall|hasDerivAt_integral_of_dominated_loc_of_deriv_le|isSymmSndFDerivAt|inverse_continuousAt|normDet_comp|def normDet|euclideanHausdorffMeasure_eq_volume' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem integral_withDensity_eq_integral_toReal_smul₀' <snapshot>/mathlib/Mathlib`
- `lake env lean GMT/Ch04/Submission.lean -o /tmp/ch04-ts-decomp/olean/GMT/Ch04/Submission.olean`
- `LEAN_PATH=$(lake env printenv LEAN_PATH):/tmp/ch04-ts-decomp/olean lean /tmp/ch04-ts-decomp/{T0,T1,T5}.lean (statement-scope availability of LinearMap.range/normDet/adjoint; instance #synth)`
- `python3 /tmp/ch04-ts-decomp/scripts/gen.py (verifier gmt-compare.child_modules + lean_contract.validate_lean_statement); lean /tmp/ch04-ts-decomp/gen/Challenge_*.lean`
- `lean /tmp/ch04-ts-decomp/T6.lean (parent assembly from sorry'd children and sibling)`
- `lake env lean /tmp/ch04-ts-decomp/Axioms.lean (#print axioms of the cited lemmas)`
- `lean /tmp/ch04-ts-decomp/gen2/WithImports.lean /tmp/ch04-ts-decomp/gen2/Synth.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/project/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-lipschitz-pieces-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/WeightedBlowUp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLiteral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Normed/Ring/Units.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Topology/MetricSpace/CantorScheme.lean`
- `/tmp/ch04-ts-decomp/T6.lean`
- `/tmp/ch04-ts-decomp/Axioms.lean`
- `/tmp/ch04-ts-decomp/gen2/WithImports.lean`

Contract and pinned packages:
- The snapshot contract (sha256 6e58e5dd…0f4770b) is byte-identical to the workspace Contract.lean and Submission.lean.
- SimonGMT is at the pinned revision 2b3663083f3fe399b6296fb8eaee52169170e197.

What can appear in a child type:
- In the frozen statement scope (`import GMT.Ch04.Submission` plus the contract opens), LinearMap.normDet, ContinuousLinearMap.adjoint and LinearMap.adjoint are unknown constants. So no child type mentions Jacobians or adjoints.
- `LinearMap.range (fderiv ℝ F w)` does not elaborate; `LinearMap.range (fderiv ℝ F w).toLinearMap` does, and the child types use that form.

Lusin's theorem:
- The snapshot Mathlib has no Lusin theorem: `rg 'theorem .*[Ll]usin'` only hits a docstring in Topology/MetricSpace/CantorScheme.lean.
- SimonGMT Chapter01.exists_isClosed_continuousOn_of_measurable is cited instead.

Cited library results — each exists with the stated meaning, and #print axioms shows only propext, Classical.choice, Quot.sound:
- SimonGMT Chapter04: map_inverse_blowUp_carrier, hausdorff_blowUp_image, planeMeasure_unit_closedBall, tangentDensityCutoff_eq_one, RectifiableVarifold.integral_weighted_blowUp.
- SimonGMT Chapter02: continuous_normDet, measurable_areaJacobianAt, weighted_area_formula_lipschitz_injOn, euclideanHausdorffMeasure_image_le_of_lipschitzOn, simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure, areaJacobian_comp_eq_parametrization_mul_tangential.
- SimonGMT Chapter01: exists_isClosed_continuousOn_of_measurable, ae_dimensionalUpperDensity_eq_zero_outside, measure_toOuterMeasure_isBorelRegular.
- SimonGMT Chapter03: regular_euclideanHausdorffMeasure_restrict_submodule, support_euclideanHausdorffMeasure_restrict_submodule.
- Mathlib: Besicovitch.ae_tendsto_measure_inter_div, Measure.ext_of_integral_eq_on_compactlySupported, hasDerivAt_integral_of_dominated_loc_of_deriv_le, ContDiffAt.isSymmSndFDerivAt, NormedRing.inverse_continuousAt, InnerProductSpace.volume_closedBall, LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume, LinearMap.normDet_sq_eq_det_gram, LinearMap.normDet_comp, MeasurableSet.exists_isClosed_sdiff_lt, Measure.Regular.smul.
- integral_withDensity_eq_integral_toReal_smul₀ is a root-namespace lemma in MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean.

Elaboration checks:
- All seven child types pass the verifier's validate_lean_statement.
- Each compiles as a comparator-generated NodeChallenge file, with only the expected sorry warning.
- They still elaborate when the implementation imports are added, with the same instances; for example, volume on EuclideanSpace stays measureSpaceOfInnerProductSpace.

Parent assembly:
- T6.lean declares the seven children and the sibling rectifiable_lipschitz_piece_cover as sorry'd theorems, then gives a full proof of Submission.tangent_structure_first_variation with exactly the frozen type.
- It compiles with only the eight sorry warnings.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: https://github.com/ZhengyangZhang06/gmt-formalize/pull/1935

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
