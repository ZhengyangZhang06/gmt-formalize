<!-- theorem-id: gmt-ch04/root.tangent_structure-a1 -->

## Theorem `Submission.tangent_structure_first_variation`

(1) ApproxTangentAE: for all n ≥ 1, ℓ ≥ 0 and every admissible pair a = (M, θ) in ℝ^{n+ℓ}, for Hⁿ-a.e. x ∈ M: exactly one subspace P satisfies (mk a).IsApproxTangentAt x P; the chosen tangent space (mk a).tangentSpace x is the approximate tangent space of M with respect to θ at x in the sense of Simon Ch. 3, 1.7 (HasWeightedApproximateTangentSpaceAt); and μ_V(B_ρ(x))/(ω_n ρⁿ) → θ(x) as ρ ↓ 0. (2) (GF): for all n ≥ 1, ℓ and every rectifiable n-varifold V in ℝ^{n+ℓ}, μ_V is finite on compact sets, dim T_xV = n for μ_V-a.e. x, and x ↦ p_{T_xV} is μ_V-a.e. strongly measurable. (3) FirstVariationFormula: for every pair a, every n ≥ 1 and every compact variation (φ, ε, K) as in Ch. 4, 2.1, the function t ↦ (imageMass a (φ t) K).toReal = M(φ_t#(V⌞K)) has derivative ∫ div_M X dμ_V at t = 0, where X(y) = ∂_tφ(t, y)|_{t=0}.

Node: `root.tangent_structure-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/54

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/291, https://github.com/ZhengyangZhang06/gmt-formalize/issues/292, https://github.com/ZhengyangZhang06/gmt-formalize/issues/293, https://github.com/ZhengyangZhang06/gmt-formalize/issues/295, https://github.com/ZhengyangZhang06/gmt-formalize/issues/297, https://github.com/ZhengyangZhang06/gmt-formalize/issues/298, https://github.com/ZhengyangZhang06/gmt-formalize/issues/299

## Lean problem

Declaration: `Submission.tangent_structure_first_variation`

```lean
ApproxTangentAE ∧ (∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ), 0 < n → IsFiniteMeasureOnCompacts V.weight ∧ (∀ᵐ x ∂V.weight, Module.finrank ℝ (V.tangentSpace x) = n) ∧ AEStronglyMeasurable (fun x ↦ (V.tangentSpace x).starProjection) V.weight) ∧ FirstVariationFormula
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

- Parent DAG node: `root`
- Child DAG node: `root.tangent_structure-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions (used throughout). n ≥ 1 and ℓ ≥ 0 are integers, E = Ambient n ℓ = ℝ^{n+ℓ}, Hⁿ = μHE[n] (equal to Simon's Hⁿ), B_ρ(ξ) = closedBall ξ ρ (closed ball), ω_n = omega n ∈ (0, ∞), and Hⁿ(P ∩ B_s(0)) = ω_n sⁿ for every n-dimensional subspace P. For a rectifiable n-varifold V: μ = μ_V = V.weight; T_x = V.tangentSpace x; p_x and p_x^⊥ are the orthogonal projections onto T_x and T_x^⊥; div_M X(x) = V.tangentialDiv X x = trace(DX(x)∘p_x); ∇^M h(x) = V.tangentialGradient h x = p_x(∇h(x)); r = |x − ξ|; q_ξ(x) = V.normalRadialSq ξ x = |p_x^⊥(x − ξ)|²/|x − ξ|² ∈ [0, 1] (q_ξ(ξ) = 0 because division by 0 is 0); w_ξ(x) = q_ξ(x)/|x − ξ|ⁿ (w_ξ(ξ) = 0); a_ξ(ρ) = μ(B_ρ(ξ))/ρⁿ (a real number); Θ(ξ) = V.density ξ. A test field in U is a C¹ map X: E → E with compact support and tsupport X ⊆ U (IsTestField). 'V has mean curvature H in U' (HasMeanCurvatureIn) means H ∈ L¹_loc(U, μ) and ∫div_M X dμ = −∫⟨X, H⟩dμ for every test field X in U; 'stationary in U' means ∫div_M X dμ = 0 for every test field X in U. (FV) for V means: (FV1) μ(K) < ∞ for every compact K; (FV2) dim T_x = n for μ-a.e. x; (FV3) x ↦ p_x is μ-a.e. strongly measurable. (GF) is the statement that (FV) holds for every n ≥ 1, every ℓ and every V : RectifiableVarifold n ℓ (exactly the second conjunct of the sibling tangent_structure_first_variation); (AT) is the contract Prop ApproxTangentAE. Under (FV): q_ξ, w_ξ, ∇^M h (for h ∈ C¹(U), on U) and div_M X (for X ∈ C¹) are μ-a.e. strongly measurable, being continuous functions of p_x and of continuous data; |div_M X| ≤ (n+ℓ)‖DX‖ and div_M X = 0 off tsupport X, so div_M X is μ-integrable for every test field X; μ is a locally finite, hence outer regular, Borel measure, and μ(E ∖ spt μ) = 0 (spt V = spt μ).

Source: Simon Ch. 3, Remark 1.3, Theorem 1.6 ('⇒') with Remark 1.5(2), Remark 1.8(1)(2), Theorem 1.9 ('⇒'), the area formula of Ch. 3 §2 (2.4–2.5, from Ch. 2 §3 and 4.11–4.13); Ch. 4, 1.3 and 2.2 (with the computation of Ch. 2 §5, 5.2–5.3). The printed proofs use the covering of Ch. 3, Lemma 1.2 by embedded C¹ submanifolds N_j only through injective parametrizations with continuous injective derivative; here these are the Lipschitz pieces F_i(C_i) supplied by the sibling theorem rectifiable_lipschitz_piece_cover (which replaces Lemma 1.2 and its use of the C¹ Approximation Theorem). The printed arguments are otherwise reproduced in order, with the details required by the contract's formulation (closed balls, the weight μ_V, the chosen tangent space). No errata apply to these items.

Additional notation. For a pair a = (M, θ) write V = mk a and μ = μ_V = pairWeight n M θ, so ∫g dμ = ∫_M gθ dHⁿ for Borel g ≥ 0 and μ(A) = ∫_{M∩A} θ dHⁿ for Borel A. Every V : RectifiableVarifold n ℓ equals mk a for some pair a (it is a quotient). ℝⁿ := EuclideanSpace ℝ (Fin n) with Lebesgue measure Lⁿ (= Hⁿ on ℝⁿ). η_{x,λ}(y) := λ^{-1}(y − x); p_P is the orthogonal projection onto a subspace P. For an injective linear A: ℝⁿ → E, JA := (det(A*A))^{1/2} > 0; for a Lipschitz G: ℝⁿ → E, JG(v) := J(DG(v)) at points where G is differentiable (this is SimonGMT Chapter02.areaJacobianAt G v = (fderiv ℝ G v).normDet). For a linear Λ: E → E and a subspace T with inclusion ι_T, J^TΛ := (Λ restricted to T).normDet = (det(ι_T*Λ*Λι_T))^{1/2} = (det(p_TΛ*Λp_T + I − p_T))^{1/2}, a continuous function of (Λ, p_T) (for T = {0} it equals 1).

Results used as known theorems (all pinned and axiom-checked, standard axioms only).
(R1) The sibling theorem rectifiable_lipschitz_piece_cover.
(R2) Area formula for Lipschitz maps (Simon Ch. 2, §3): if G: ℝⁿ → E is Lipschitz, B ⊆ ℝⁿ is Borel and G is injective on B, then ∫_{G(B)} u dHⁿ = ∫_B JG(v) u(G(v)) dv for every u: E → [0, ∞] [SimonGMT Chapter02.weighted_area_formula_lipschitz_injOn]; and Hⁿ(G(A)) ≤ Lip(G)ⁿ Lⁿ(A) for every A ⊆ ℝⁿ [Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn with Mathlib EuclideanSpace.euclideanHausdorffMeasure_eq_volume]. For an injective linear A: ℝⁿ → E the area formula reads ∫_{A(ℝⁿ)} u dHⁿ = JA∫_{ℝⁿ} u(Av) dv; in particular Hⁿ(P ∩ B_s(0)) = ω_n sⁿ for every n-dimensional subspace P.
(R3) Upper density theorem (Simon Ch. 1, Thm 3.6) [SimonGMT Chapter01.ae_dimensionalUpperDensity_eq_zero_outside, applied to the outer measure of ν, which is Borel regular by Chapter01.measure_toOuterMeasure_isBorelRegular, together with Chapter02.simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure; the density there is normalised by the constant realUnitBallVolume n ∈ (0, ∞), which does not affect vanishing]: if ν is a Borel measure on E and A ⊆ E is Borel with ν(A) < ∞, then for Hⁿ-a.e. x ∉ A, limsup_{ρ↓0} ν(A ∩ B_ρ(x))/ρⁿ = 0.
(R4) Lusin's theorem (Simon Ch. 1, 1.17) [SimonGMT Chapter01.exists_isClosed_continuousOn_of_measurable], for finite Borel measures on E (these are weakly regular, so inner regular by closed sets on Borel sets — Mathlib MeasurableSet.exists_isClosed_sdiff_lt — and, E being proper, by compact sets), and Lebesgue's density theorem [Mathlib Besicovitch.ae_tendsto_measure_inter_div]: for every C ⊆ ℝⁿ, Lⁿ(C ∩ B_r(w))/Lⁿ(B_r(w)) → 1 as r ↓ 0 for Lⁿ-a.e. w ∈ C.
(R5) Two regular, locally finite Borel measures on E with the same integrals of all functions in C_c(E) are equal [Mathlib MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported]; for an n-dimensional subspace P, Hⁿ⌞P is regular [SimonGMT Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule] (hence so is cHⁿ⌞P, c > 0) and supp(Hⁿ⌞P) = P [Chapter03.support_euclideanHausdorffMeasure_restrict_submodule].
(R6) Hⁿ(cA + b) = cⁿHⁿ(A) for c > 0 and b ∈ E (Hⁿ is translation invariant and homogeneous of degree n under dilations); every Hⁿ-null set lies in a Borel Hⁿ-null set; an Hⁿ-null-measurable set contains a Borel set and is contained in a Borel set, both differing from it by Hⁿ-null sets.

Part A. Approximate tangent planes and the tangent field.

1. (Pieces, in place of Lemma 1.2.) Fix a pair a = (M, θ). M is countably n-rectifiable (IsRectifiablePair), so (R1) gives a Borel set N_0 with Hⁿ(N_0) = 0, compact sets C_i ⊆ ℝⁿ and Lipschitz maps F_i: ℝⁿ → E (indexed by i ≥ 1 after shifting the index) with M ⊆ N_0 ∪ ⋃_{i≥1} N_i, N_i := F_i(C_i), such that for every i: F_i is differentiable at each w ∈ C_i with DF_i(w) injective, w ↦ DF_i(w) is continuous on C_i, and c_i|v − w| ≤ |F_i(v) − F_i(w)| for all v, w ∈ C_i, with c_i > 0. Consequences: N_i is compact (a continuous image of a compact set); F_i maps C_i bijectively onto N_i, and the inverse ψ_i: N_i → C_i is (1/c_i)-Lipschitz, hence continuous; for x ∈ N_i, T_i(x) := DF_i(ψ_i(x))(ℝⁿ) is an n-dimensional subspace; x ↦ p_{T_i(x)} is continuous on N_i, being the composition of ψ_i, of DF_i restricted to C_i, and of the map A ↦ p_{A(ℝⁿ)} = A(A*A)^{-1}A*, which is continuous on injective linear maps A: ℝⁿ → E; Hⁿ(N_i) ≤ Lip(F_i)ⁿLⁿ(C_i) < ∞ by (R2); and JF_i is continuous, hence bounded by some constant Γ_i, on the compact set C_i (DF_i is continuous on C_i and A ↦ JA is continuous).

2. (Remark 1.3.) Put M_0' := M ∩ N_0 and M_i := (M ∩ N_i) ∖ (N_0 ∪ ⋃_{1≤j<i} N_j) (i ≥ 1). These sets are Hⁿ-null-measurable (M is, and the N_j are Borel), pairwise disjoint, cover M (a point of M ∖ N_0 lies in M_i for the least i with x ∈ N_i), Hⁿ(M_0') = 0, and M_i ⊆ N_i ∖ ⋃_{1≤j<i} N_j.

3. (Blow-up of a piece at a density point.) Let i ≥ 1, let w ∈ C_i be a Lebesgue density point of C_i (so λ^{-n}Lⁿ(B_{λr}(w) ∖ C_i) → 0 as λ ↓ 0, for every r > 0), x := F_i(w), A := DF_i(w) and T := T_i(x) = A(ℝⁿ). Then
(3a) λ^{-n}∫_{N_i} f(η_{x,λ}(y)) dHⁿ(y) → ∫_T f dHⁿ as λ ↓ 0, for every f ∈ C_c(E);
(3b) λ^{-n}Hⁿ(N_i ∩ B_{Rλ}(x)) ≤ Lip(F_i)ⁿω_n(R/c_i)ⁿ for all λ, R > 0.
Proof of (3b): N_i ∩ B_{Rλ}(x) = F_i(C_i ∩ F_i^{-1}(B_{Rλ}(x))), and C_i ∩ F_i^{-1}(B_{Rλ}(x)) ⊆ B_{Rλ/c_i}(w) by the lower bound of step 1; apply (R2).
Proof of (3a): let spt f ⊆ B_R(0), m_A := min_{|e|=1}|Ae| > 0 and R' := R/min(c_i, m_A). By (R2) for F_i on the Borel set C_i (applied to the positive and negative parts of f∘η_{x,λ}; all integrals are finite because Hⁿ(N_i) < ∞ and JF_i ≤ Γ_i on C_i) and the substitution v = w + λu,
λ^{-n}∫_{N_i} f(η_{x,λ}) dHⁿ = λ^{-n}∫_{C_i} f((F_i(v) − x)/λ) JF_i(v) dv = ∫_{ℝⁿ} 1_{C_i}(w + λu) f(Q_λ(u)) JF_i(w + λu) du, where Q_λ(u) := (F_i(w + λu) − F_i(w))/λ.
If w + λu ∈ C_i and |u| > R', then |Q_λ(u)| ≥ c_i|u| > R, so the integrand vanishes; and |Au| ≥ m_A|u| > R for |u| > R', so f(Au) = 0 there. By (R2) for A, ∫_T f dHⁿ = JA∫_{ℝⁿ} f(Au) du = ∫_{B_{R'}(0)} f(Au) JF_i(w) du (JA = JF_i(w)). Therefore the difference D_λ of the two sides of (3a) satisfies
|D_λ| ≤ ∫_{B_{R'}(0)} 1_{C_i}(w + λu)|f(Q_λ(u))JF_i(w + λu) − f(Au)JF_i(w)| du + sup|f|·JF_i(w)·λ^{-n}Lⁿ(B_{λR'}(w) ∖ C_i).
The second term tends to 0 because w is a density point of C_i. In the first term, for |u| ≤ R' with w + λu ∈ C_i we have |Q_λ(u) − Au| ≤ R'·sup_{0<|h|≤λR'}|F_i(w + h) − F_i(w) − Ah|/|h| → 0 (differentiability of F_i at w) and |JF_i(w + λu) − JF_i(w)| ≤ sup{|JF_i(v) − JF_i(w)| : v ∈ C_i, |v − w| ≤ λR'} → 0 (continuity of DF_i on C_i at w and of A' ↦ JA'); since f is bounded and uniformly continuous and JF_i ≤ Γ_i on C_i, the integrand tends to 0 uniformly on B_{R'}(0) (it is at most ω_f(|Q_λ(u) − Au|)Γ_i + sup|f|·|JF_i(w + λu) − JF_i(w)|, ω_f a modulus of continuity of f). Hence D_λ → 0.

4. (Theorem 1.9 via the proof of 1.6 '⇒' and Remark 1.8(1).) Claim: for Hⁿ-a.e. x ∈ M there is i ≥ 1 with x ∈ M_i such that, with P_x := T_i(x),
(★) λ^{-n}∫ f(η_{x,λ}(y)) dμ(y) = λ^{-n}∫_M f(η_{x,λ}(y))θ(y) dHⁿ(y) → θ(x)∫_{P_x} f dHⁿ as λ ↓ 0, for every f ∈ C_c(E).
Proof. As Hⁿ(M_0') = 0, it suffices to fix i ≥ 1 and prove (★) for Hⁿ-a.e. x ∈ M_i. (i) The set Z_i of points of C_i that are not Lebesgue density points of C_i is Lⁿ-null (R4), so F_i(Z_i) is Hⁿ-null (R2); every x ∈ N_i ∖ F_i(Z_i) equals F_i(w) for the density point w = ψ_i(x). (ii) θ is a.e.-strongly measurable for Hⁿ⌞M (M = ⋃_k M ∩ B_k(0) and θ is integrable on each M ∩ B_k(0)), so there is a Borel function θ̃ with θ = θ̃ Hⁿ-a.e. on M (Mathlib AEMeasurable.mk), and by (R6) a Borel Hⁿ-null set Y with θ = θ̃ on M ∖ Y. For q ≥ 1, by (R6) choose a Borel set A_q ⊆ M_i ∩ {θ̃ ≥ 1/q} ∩ B_q(0) ∖ Y differing from this null-measurable set by an Hⁿ-null set; Hⁿ(A_q) ≤ q∫_{M∩B_q(0)} θ dHⁿ < ∞. By (R4) applied to the finite Borel measure Hⁿ⌞A_q and the Borel function θ̃ (and inner regularity by compact sets), for each m ≥ 1 there is a compact C_{q,m} ⊆ A_q with Hⁿ(A_q ∖ C_{q,m}) < 1/m on which θ = θ̃ is continuous. Since θ > 0 on M, M_i ∖ Y ⊆ ⋃_q (M_i ∩ {θ̃ ≥ 1/q} ∩ B_q(0) ∖ Y); hence the countably many compact sets C_{q,m} cover M_i up to an Hⁿ-null set, and it suffices to prove (★) for Hⁿ-a.e. x in one of them, C. Note C ⊆ M_i ⊆ N_i. (iii) Choose r_C > 0 with C ⊆ ball 0 r_C. Apply (R3) to ν := μ (a Borel measure, finite on balls since μ(B) = ∫_{M∩B} θ dHⁿ) with A := B_{r_C}(0) ∖ C, and to ν := Hⁿ⌞N_i (finite) with A := N_i ∖ C: for Hⁿ-a.e. x ∈ C and every R > 0, (a) λ^{-n}μ(B_{Rλ}(x) ∖ C) → 0 and (b) λ^{-n}Hⁿ((N_i ∖ C) ∩ B_{Rλ}(x)) → 0 as λ ↓ 0 (for small λ, B_{Rλ}(x) ⊆ ball 0 r_C). Fix such an x with x ∉ F_i(Z_i), and f ∈ C_c(E) with spt f ⊆ B_R(0), so that f(η_{x,λ}(y)) = 0 unless |y − x| ≤ Rλ. Since C ⊆ M ∩ N_i, λ^{-n}∫_M f(η_{x,λ})θ dHⁿ = I_1 + I_2 + I_3 + I_4 with I_1 := θ(x)λ^{-n}∫_{N_i} f(η_{x,λ}) dHⁿ, I_2 := −θ(x)λ^{-n}∫_{N_i∖C} f(η_{x,λ}) dHⁿ, I_3 := λ^{-n}∫_C f(η_{x,λ}(y))(θ(y) − θ(x)) dHⁿ(y) and I_4 := λ^{-n}∫_{M∖C} f(η_{x,λ})θ dHⁿ (all integrals finite). By (3a), I_1 → θ(x)∫_{T_i(x)} f dHⁿ; |I_2| ≤ θ(x) sup|f| λ^{-n}Hⁿ((N_i ∖ C) ∩ B_{Rλ}(x)) → 0 by (b); |I_3| ≤ sup|f|·sup_{y∈C∩B_{Rλ}(x)}|θ(y) − θ(x)|·λ^{-n}Hⁿ(N_i ∩ B_{Rλ}(x)) → 0 by continuity of θ on C and (3b); |I_4| ≤ sup|f| λ^{-n}μ(B_{Rλ}(x) ∖ C) → 0 by (a). This proves (★) with P_x = T_i(x).

5. (ApproxTangentAE.) Let x be as in step 4; then x ∈ M and θ(x) > 0. (i) dim P_x = n and (★) is V.IsApproxTangentAt x P_x with c = θ(x) > 0. (ii) If also V.IsApproxTangentAt x Q with a constant c' > 0 (so dim Q = n), then c'∫_Q f dHⁿ = θ(x)∫_{P_x} f dHⁿ for all f ∈ C_c(E) (uniqueness of limits), so the regular locally finite measures c'Hⁿ⌞Q and θ(x)Hⁿ⌞P_x are equal by (R5). Evaluating both on B_1(0) gives c'ω_n = θ(x)ω_n (R2), so c' = θ(x) > 0 and Hⁿ⌞Q = Hⁿ⌞P_x; taking supports (R5), Q = P_x. Hence there is exactly one such P, and the chosen V.tangentSpace x equals P_x. (iii) For r > 0, η_{x,r} is a similarity of ratio r^{-1}, so by (R6) ∫_{η_{x,r}(M)} f(y)θ(x + ry) dHⁿ(y) = r^{-n}∫_M f(η_{x,r}(z))θ(z) dHⁿ(z) → θ(x)∫_{P_x} f dHⁿ by (★); together with dim P_x = n this is HasWeightedApproximateTangentSpaceAt n M θ x (V.tangentSpace x). (iv) (Ch. 3, 1.8(2), with closed balls.) For δ ∈ (0, 1) take f_± ∈ C_c(E) with 0 ≤ f_± ≤ 1, f_+ = 1 on B_1(0), spt f_+ ⊆ B_{1+δ}(0), f_− = 1 on B_{1−δ}(0), spt f_− ⊆ ball 0 1. Then ∫ f_−(η_{x,λ}) dμ ≤ μ(B_λ(x)) ≤ ∫ f_+(η_{x,λ}) dμ, and (★) with Hⁿ(P_x ∩ B_s(0)) = ω_n sⁿ (R2) gives θ(x)ω_n(1 − δ)ⁿ ≤ liminf_{λ↓0} λ^{-n}μ(B_λ(x)) ≤ limsup_{λ↓0} λ^{-n}μ(B_λ(x)) ≤ θ(x)ω_n(1 + δ)ⁿ. Letting δ ↓ 0, μ(B_λ(x))/(ω_nλⁿ) → θ(x), i.e. V.HasDensityAt x (θ x). Since this holds for Hⁿ-a.e. x ∈ M and for every pair, ApproxTangentAE holds.

6. (GF.) Let V = mk a. (i) For compact K, μ(K) = ∫_{M∩K} θ dHⁿ < ∞ (local integrability of θ), so IsFiniteMeasureOnCompacts μ. (ii) μ ≪ Hⁿ⌞M (a measure with density), and by step 5 dim V.tangentSpace x = n for Hⁿ-a.e. x ∈ M, hence for μ-a.e. x. (iii) Define g: E → (E →L E) by g(x) := p_{T_i(x)} for x ∈ N_i ∖ ⋃_{1≤j<i} N_j (i ≥ 1) and g(x) := 0 elsewhere. The sets N_i ∖ ⋃_{j<i} N_j are Borel and pairwise disjoint and g is continuous on each of them (step 1), so g is Borel measurable, hence strongly measurable (finite-dimensional codomain). For Hⁿ-a.e. x ∈ M we have x ∈ M_i ⊆ N_i ∖ ⋃_{j<i} N_j for some i and V.tangentSpace x = T_i(x) (steps 4, 5), i.e. p_x = g(x); since μ ≪ Hⁿ⌞M this holds μ-a.e., so x ↦ p_x is μ-a.e. strongly measurable. This proves (GF).

Part B. The first variation formula (Ch. 4, 2.2).

7. Let a = (M, θ), V = mk a, μ = μ_V, n ≥ 1, and (φ, ε, K) with IsCompactVariation φ ε K; put φ_t := φ t and X(y) := deriv (t ↦ φ t y) 0 = ∂_tφ(t, y)|_{t=0}. As φ is C^∞ on the open set (−ε, ε) × E, X is C^∞ and (t, y) ↦ Dφ_t(y) is C^∞ with ∂_t Dφ_t(y)|_{t=0} = DX(y) (symmetry of second derivatives). For y ∉ K we have φ_t(y) = y for all t, so X = 0 on the open set E ∖ K, DX = 0 there and div_M X = 0 off K. For |t| < ε, φ_t is a bijection with C^∞ inverse, so Function.invFun φ_t = φ_t^{-1}, Dφ_t(y) is invertible for every y (chain rule for φ_t^{-1}∘φ_t = id), and φ_t is a homeomorphism; Dφ_t is continuous and equals the identity on the open set E ∖ K (where φ_t = id), so it is bounded and φ_t is globally Lipschitz; hence φ_t maps Borel sets to Borel sets and Hⁿ-null sets to Hⁿ-null sets.

8. (Area formula on M; Ch. 3, 2.4–2.5.) For |t| < ε and every x ∈ E let J_t(x) := J^{T_x}(Dφ_t(x)) = (det(p_xDφ_t(x)*Dφ_t(x)p_x + I − p_x))^{1/2}, with T_x = V.tangentSpace x and p_x its projection (where no tangent exists T_x = ⊥ and J_t(x) = 1); x ↦ J_t(x) is μ-a.e. equal to the Borel function obtained by replacing p_x with g(x) (step 6). Claim: imageMass a φ_t K = ∫⁻_{φ_t(M∩K)} ofReal(θ(φ_t^{-1}(y))) dHⁿ(y) = ∫⁻_{M∩K} ofReal(θ J_t) dHⁿ. Proof: M ∩ K is the disjoint union of M_0' ∩ K and the sets M_i ∩ K (step 2); φ_t is injective, so their images are pairwise disjoint and Hⁿ-null-measurable, and Hⁿ(φ_t(M_0' ∩ K)) = 0. Fix i ≥ 1. Choose a Borel set A with M_i ∩ K ⊆ A ⊆ N_i and Hⁿ(A ∖ (M_i ∩ K)) = 0 (R6; intersect a Borel hull with the Borel set N_i), and let B := C_i ∩ F_i^{-1}(A), a Borel set with F_i(B) = A on which F_i and the Lipschitz map φ_t∘F_i are injective. For v ∈ B, F_i is differentiable at v and φ_t is C^∞, so D(φ_t∘F_i)(v) = Dφ_t(F_i(v))DF_i(v). For linear A': ℝⁿ → E and Λ: E → E, J(ΛA') = J^{A'(ℝⁿ)}(Λ)·J(A') [Mathlib LinearMap.normDet_comp; SimonGMT Chapter02.areaJacobian_comp_eq_parametrization_mul_tangential] (for injective A' = ιA_0, with ι the inclusion of A'(ℝⁿ) and A_0 invertible: det(A'^*Λ^*ΛA') = det(ι^*Λ^*Λι)·det(A_0^*A_0)). Hence J(φ_t∘F_i)(v) = J^{T_i(F_i(v))}(Dφ_t(F_i(v)))·JF_i(v) for v ∈ B. For every u: E → [0, ∞], (R2) applied to φ_t∘F_i on B and then to F_i on B gives
∫⁻_{φ_t(A)} u dHⁿ = ∫⁻_B J^{T_i(F_i(v))}(Dφ_t(F_i(v)))·u(φ_t(F_i(v)))·JF_i(v) dv = ∫⁻_A J^{T_i(x)}(Dφ_t(x))·u(φ_t(x)) dHⁿ(x).
Take u := ofReal(θ∘φ_t^{-1}), so that u(φ_t(x)) = ofReal(θ(x)). Since A ∖ (M_i ∩ K) and its image under φ_t are Hⁿ-null, and T_i(x) = T_x for Hⁿ-a.e. x ∈ M_i (steps 4, 5), ∫⁻_{φ_t(M_i∩K)} ofReal(θ∘φ_t^{-1}) dHⁿ = ∫⁻_{M_i∩K} ofReal(θ J_t) dHⁿ. Summing over i proves the claim.

9. (Ch. 2 §5.) Fix x with P := T_x of dimension n, let ι: P → E be the inclusion and Gram_t := (Dφ_t(x)ι)*(Dφ_t(x)ι), so J_t(x) = (det Gram_t)^{1/2}, Gram_0 = I_P, and d/dt Gram_t at t = 0 equals (DX(x)ι)*ι + ι*(DX(x)ι), whose trace is 2 trace(ι*DX(x)ι) = 2 trace(DX(x)∘p_P) = 2 div_M X(x). By Jacobi's formula at the identity (det(I + tB + o(t)) = 1 + t·trace B + o(t), from the Leibniz expansion of the determinant), the derivative of det Gram_t at t = 0 is trace(d/dt Gram_t at 0), hence d/dt J_t(x) at t = 0 equals div_M X(x). Uniform bound: on the compact set [−ε/2, ε/2] × K the maps (t, y) ↦ Dφ_t(y), ∂_tDφ_t(y) and Dφ_t(y)^{-1} are continuous, hence bounded in operator norm by some Λ_1 ≥ 1. Fix x ∈ K and an n-plane P. For |t| ≤ ε/2, t ↦ Gram_t is C¹, ‖Gram_t‖ ≤ Λ_1², Gram_t ≥ Λ_1^{-2}I_P (because |Dφ_t(x)v| ≥ Λ_1^{-1}|v|), so Gram_t is invertible with ‖Gram_t^{-1}‖ ≤ Λ_1², and ‖∂_tGram_t‖ ≤ 2Λ_1². Writing det(Gram_t + H) = det Gram_t·det(I + Gram_t^{-1}H) and applying Jacobi's formula at the identity, d/dt det Gram_t = det Gram_t·trace(Gram_t^{-1}∂_tGram_t); as det Gram_t > 0, t ↦ J_t(x) = (det Gram_t)^{1/2} is differentiable on [−ε/2, ε/2] with ∂_tJ_t(x) = ½J_t(x)·trace(Gram_t^{-1}∂_tGram_t). Since J_t(x) ≤ ‖Dφ_t(x)‖ⁿ ≤ Λ_1ⁿ and |trace Y| ≤ n‖Y‖, |∂_tJ_t(x)| ≤ ½Λ_1ⁿ·n·Λ_1²·2Λ_1² = nΛ_1^{n+4} =: C_1 for all |t| ≤ ε/2, all x ∈ K and every n-plane P (at t = 0 the formula reduces to the value div_M X(x) found above). Where T_x = ⊥, J_t(x) = 1 for all t. Moreover x ↦ J_t(x) is μ-measurable, being a continuous function of Dφ_t(x) and of p_x, which equals the Borel g(x) μ-a.e. (step 6).

10. (Conclusion.) Let m(t) := ∫_{M∩K} θ J_t dHⁿ for |t| ≤ ε/2; J_0 = 1, so m(0) = ∫_{M∩K} θ dHⁿ. By step 9 and the mean value theorem, |θ(x)(J_t(x) − J_0(x))/t| ≤ C_1θ(x) with θ ∈ L¹(Hⁿ⌞(M ∩ K)), and the quotient tends to θ(x) div_M X(x) for Hⁿ-a.e. x ∈ M ∩ K (namely wherever dim T_x = n, by step 9). By dominated convergence m is differentiable at 0 with m'(0) = ∫_{M∩K} θ div_M X dHⁿ = ∫_K div_M X dμ = ∫ div_M X dμ (step 7). Since m(t) ≤ (1 + C_1ε)∫_{M∩K} θ dHⁿ < ∞, step 8 gives imageMass a φ_t K = ofReal(m(t)) and (imageMass a (φ t) K).toReal = m(t) for |t| ≤ ε/2. Hence t ↦ (imageMass a (φ t) K).toReal has derivative ∫ V.tangentialDiv X dμ_V at t = 0, which is FirstVariationFormula. With steps 5 and 6 the conjunction is proved.

## Key steps

1. Cover M by the Lipschitz pieces N_i = F_i(C_i) of the sibling rectifiable_lipschitz_piece_cover; T_i(x) = DF_i(ψ_i(x))ℝⁿ has continuous projection on the compact N_i
2. Disjointify: M = M_0' ∪ ⋃ M_i with M_i ⊆ N_i ∖ ⋃_{j<i} N_j (Remark 1.3)
3. At Lebesgue density points w of C_i the blow-up of Hⁿ⌞N_i at F_i(w) converges to Hⁿ⌞T_i (area formula, differentiability at w, continuity of DF_i on C_i), and λ^{-n}Hⁿ(N_i ∩ B_{Rλ}) stays bounded
4. Lusin pieces with θ continuous and the upper density theorem give the weighted blow-up (★) at Hⁿ-a.e. x ∈ M_i (Thms 1.6, 1.9, Remark 1.8(1))
5. (★) gives existence and (by Riesz uniqueness of cHⁿ⌞P) uniqueness of the approximate tangent, the Ch. 3 1.7 weighted tangent, and the closed-ball density θ(x): ApproxTangentAE
6. μ_V finite on compacts, dim T_x = n μ_V-a.e., and p_{T_x} = g(x) a.e. for the Borel piecewise-continuous field g: (GF)
7. Area formula on M ∩ K for φ_t through the pieces and J(φ_t∘F_i) = J^{T_i}(Dφ_t)·JF_i: imageMass = ∫_{M∩K} θ J^{T_x}φ_t dHⁿ
8. Jacobi's formula gives ∂_t J_t at 0 = div_M X; uniform bounds and dominated convergence give the derivative ∫ div_M X dμ_V: FirstVariationFormula

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `sha256sum GMT/Ch04/Contract.lean GMT/Ch04/Submission.lean <snapshot>/project/GMT/Ch04/Contract.lean`
- `rg -n 'def C1Approximation|def WhitneyExtension|def Rademacher' <snapshot>/project/GMT`
- `rg -n 'theorem .*[Ll]usin' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem ae_tendsto_measure_inter_div|theorem exists_measurable_superset_of_null|theorem measurableSet_of_differentiableAt |theorem measurable_fderiv |euclideanHausdorffMeasure_eq_volume' <snapshot>/mathlib/Mathlib`
- `rg -n 'exists_disjoint_subfamily_covering_enlargement_closedBall|geometric_hahn_banach_point_closed|lintegral_eq_lintegral_meas_lt|eq_pos_convex_span_of_mem_convexHull|isCompact_convexHull|measure_compl_support|normDet_comp|exists_isClosed_diff_lt|ext_of_integral_eq_on_compactlySupported' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem exists_partition_approximatesLinearOn_of_hasFDerivWithinAt' <snapshot>/mathlib/Mathlib`
- `grep -n '^theorem|^def' simongmt/Poincare/SimonGMT/Chapter02/{Lipschitz,AreaLipschitz,AreaCritical,WhitneyExtension}.lean Chapter01/{Lusin,DensityComparison}.lean Chapter03/Rectifiable.lean`
- `grep -n 'Whitney' simongmt/Poincare/SimonGMT.lean; test -f simongmt/.lake/build/lib/lean/Poincare/SimonGMT/Chapter02/WhitneyExtension.olean`
- `git -C lake-packages-25730c7c/simongmt rev-parse HEAD`
- `lake env lean GMT/Ch04/Submission.lean -o /tmp/ch04-v2-audit/olean/GMT/Ch04/Submission.olean`
- `LEAN_PATH=$(lake env printenv LEAN_PATH):/tmp/ch04-v2-audit/olean lean /tmp/ch04-v2-audit/ChildTypes.lean`
- `LEAN_PATH=... lean /tmp/ch04-v2-audit/Inspect.lean (rfl check of the elaborated piece-cover type; #print axioms of Mathlib lemmas)`
- `lake env lean /tmp/ch04-v2-audit/Axioms.lean (#print axioms of the cited SimonGMT lemmas)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/project/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/project/GMT/Ch04/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/LocallyConvex/Separation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Convex/Caratheodory.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Layercake.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root/decomposition-audit-v1.json`
- `/tmp/ch04-v2-audit/ChildTypes.lean`
- `/tmp/ch04-v2-audit/Axioms.lean`

The snapshot contract (sha256 6e58e5dd…0f4770b) is byte-identical to the workspace Contract.lean and Submission.lean; the pinned SimonGMT revision is 2b3663083f3fe399b6296fb8eaee52169170e197 as in project/lake-manifest.json. No axiom-checked C¹ approximation or Whitney extension is available: project/GMT/Ch02/Contract.lean has C1Approximation and WhitneyExtension only as Props inside the sorry'd Ch. 2 main theorem, SimonGMT's Chapter02/WhitneyExtension.lean is not imported by Poincare/SimonGMT.lean and has no built olean, and the snapshot Mathlib has no Lusin-type C¹ approximation (no 'theorem …Lusin' match). The v2 split therefore replaces that step by the new child rectifiable_lipschitz_piece_cover, whose cited inputs exist and depend only on propext, Classical.choice and Quot.sound (#print axioms): SimonGMT Chapter02.rademacher_ae_differentiableAt, euclideanHausdorffMeasure_image_le_of_lipschitzOn, measurableSet_areaRegularSet, area_image_compl_regularSet_eq_zero, weighted_area_formula_lipschitz_injOn, Chapter01.exists_isClosed_continuousOn_of_measurable, ae_dimensionalUpperDensity_eq_zero_outside, simon_theorem_3_3, Chapter02.simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure, Chapter03.support_euclideanHausdorffMeasure_restrict_submodule; Mathlib Besicovitch.ae_tendsto_measure_inter_div, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, measurable_fderiv, Measure.ext_of_integral_eq_on_compactlySupported. Also present: Mathlib LinearMap.normDet_comp, MeasurableSet.exists_isClosed_sdiff_lt, Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall, geometric_hahn_banach_point_closed, eq_pos_convex_span_of_mem_convexHull, lintegral_eq_lintegral_meas_lt, Measure.measure_compl_support; SimonGMT Chapter01.measure_toOuterMeasure_isBorelRegular, Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule, Chapter02.areaJacobian_comp_eq_parametrization_mul_tangential. No compact-convex-hull-of-compact-set lemma was found (only Set.Finite.isCompact_convexHull), so support_convex_hull proves compactness of conv K via Carathéodory. With GMT.Ch04.Submission compiled to an olean, all twelve child types elaborate after `import GMT.Ch04.Submission` inside `namespace GMT.Ch04` with the contract's opens and `open RectifiableVarifold`, the elaborated piece-cover type is checked by rfl against a fully explicit form (μHE[n] on Ambient n ℓ, fderiv on EuclideanSpace ℝ (Fin n)), and the parent assembly from the twelve sorry'd children typechecks with exactly the type of GMT.Ch04.main_theorem; the only diagnostics are the expected sorry warnings.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: https://github.com/ZhengyangZhang06/gmt-formalize/pull/2170

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
