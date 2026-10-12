<!-- theorem-id: gmt-ch04/root.support_convex_hull-a1.support_in_ball-a1 -->

## Theorem `Submission.support_in_ball_of_radial_first_variation`

Assume (RFV): for all n, ℓ ∈ ℕ, every rectifiable n-varifold V in E = ℝ^{n+ℓ}, every U ⊆ E, H: E → E, h: E → ℝ, γ: ℝ → ℝ and ξ ∈ E such that dim T_xV = n for μ_V-a.e. x, U is open, V has generalized mean curvature H in U, h ∈ C¹(U), γ ∈ C¹(ℝ) and X(x) = (h(x)γ(|x − ξ|))(x − ξ) is C¹ with compact support and tsupport X ⊆ U, one has ∫_U [h(nγ(r) + rγ'(r)(1 − q_ξ)) + γ(r)⟨x − ξ, ∇^M h⟩] dμ_V = −∫_U hγ(r)⟨x − ξ, H⟩ dμ_V, where r = |x − ξ|, γ' = deriv γ and q_ξ(x) = |p_{T_xV}^⊥(x − ξ)|²/|x − ξ|² (this is verbatim the frozen type of radial_first_variation, a sibling of the parent node; it is a hypothesis here, not a reference to that declaration). Assume (GF): for every n ≥ 1, every ℓ and every rectifiable n-varifold V in ℝ^{n+ℓ}, μ_V is finite on compact sets, dim T_xV = n for μ_V-a.e. x, and x ↦ p_{T_xV} is μ_V-a.e. strongly measurable. Then SupportInBall holds: if n ≥ 1, R ≥ 0, V has (L¹_loc) generalized mean curvature H in U = ℝ^{n+ℓ} ∖ B_R(ξ) (B_R(ξ) the closed ball), n^{-1}|⟨H(x), x − ξ⟩| < 1 for μ_V-a.e. x ∈ U, and spt V is compact, then spt V ⊆ B_R(ξ).

Node: `root.support_convex_hull-a1.support_in_ball-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/64

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/583, https://github.com/ZhengyangZhang06/gmt-formalize/issues/587, https://github.com/ZhengyangZhang06/gmt-formalize/issues/589

## Lean problem

Declaration: `Submission.support_in_ball_of_radial_first_variation`

```lean
(∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)) (H : Ambient n ℓ → Ambient n ℓ) (h : Ambient n ℓ → ℝ) (γ : ℝ → ℝ) (ξ : Ambient n ℓ), (∀ᵐ x ∂V.weight, Module.finrank ℝ (V.tangentSpace x) = n) → IsOpen U → V.HasMeanCurvatureIn U H → ContDiffOn ℝ 1 h U → ContDiff ℝ 1 γ → IsTestField U (fun x ↦ (h x * γ ‖x - ξ‖) • (x - ξ)) → ∫ x in U, (h x * ((n : ℝ) * γ ‖x - ξ‖ + ‖x - ξ‖ * deriv γ ‖x - ξ‖ * (1 - V.normalRadialSq ξ x)) + γ ‖x - ξ‖ * inner ℝ (x - ξ) (V.tangentialGradient h x)) ∂V.weight = -∫ x in U, h x * γ ‖x - ξ‖ * inner ℝ (x - ξ) (H x) ∂V.weight) → (∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ), 0 < n → IsFiniteMeasureOnCompacts V.weight ∧ (∀ᵐ x ∂V.weight, Module.finrank ℝ (V.tangentSpace x) = n) ∧ AEStronglyMeasurable (fun x ↦ (V.tangentSpace x).starProjection) V.weight) → SupportInBall
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

- Parent DAG node: `root.support_convex_hull-a1`
- Child DAG node: `root.support_convex_hull-a1.support_in_ball-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. n ≥ 1 and ℓ ≥ 0 are integers, E = Ambient n ℓ = ℝ^{n+ℓ} with inner product ⟨·,·⟩ and norm |·|; B_ρ(ξ) = closedBall ξ ρ is the closed ball and B(ξ, ρ) = ball ξ ρ the open ball. For a rectifiable n-varifold V: μ = μ_V = V.weight; spt V = V.support = spt μ (Mathlib Measure.support); T_x = V.tangentSpace x; p_x and p_x^⊥ = id − p_x are the orthogonal projections onto T_x and T_x^⊥ (Mathlib starProjection; Submodule.starProjection_orthogonal'); ∇^M h(x) = V.tangentialGradient h x = p_x(∇h(x)); r = |x − ξ|; q(x) = q_ξ(x) = V.normalRadialSq ξ x = |p_x^⊥(x − ξ)|²/|x − ξ|² (q(ξ) = 0 because division by 0 is 0), so 0 ≤ q ≤ 1 because |p_x^⊥ v| ≤ |v|. For γ ∈ C¹(ℝ), γ' = deriv γ. The real inner product is symmetric (real_inner_comm), so ⟨H(x), x − ξ⟩ (the order used in SupportInBall) equals ⟨x − ξ, H(x)⟩ (the order used in (RFV)); the two are used interchangeably below. A test field in U is a C¹ map X: E → E with compact support and tsupport X ⊆ U (IsTestField). 'V has mean curvature H in U' (HasMeanCurvatureIn) means H ∈ L¹_loc(U, μ) (LocallyIntegrableOn H U μ) and ∫ div_M X dμ = −∫⟨X, H⟩ dμ for every test field X in U. The two hypotheses of the theorem are:
(RFV) for all n, ℓ, V, U, H, h, γ, ξ such that dim T_x = n for μ_V-a.e. x, U is open, V has mean curvature H in U, h ∈ C¹(U) (ContDiffOn ℝ 1 h U), γ ∈ C¹(ℝ) and x ↦ (h(x)γ(|x − ξ|))(x − ξ) is a test field in U:
∫_U [h(nγ(r) + rγ'(r)(1 − q_ξ)) + γ(r)⟨x − ξ, ∇^M h⟩] dμ_V = −∫_U hγ(r)⟨x − ξ, H⟩ dμ_V
(this is verbatim the frozen type of radial_first_variation, a sibling of the parent node; the proof below uses only the hypothesis (RFV) and does not refer to the declaration Submission.radial_first_variation);
(GF) for every n ≥ 1, every ℓ and every V: (FV1) μ_V(K) < ∞ for every compact K (IsFiniteMeasureOnCompacts V.weight); (FV2) dim T_x = n for μ_V-a.e. x; (FV3) x ↦ p_x is μ_V-a.e. strongly measurable.

Source: Simon Ch. 4, 6.1 (p. 100). The printed proof substitutes X(x) = ζ(x)γ(r)(x − ξ), with ζ ∈ C¹_c(ℝ^{n+ℓ}), ζ ≡ 1 in a neighbourhood of spt V, and γ a nonnegative nondecreasing C¹ function with γ(t) = 0 for t ≤ R + ε, into the first variation identity of §3, obtaining n∫γ(r) dμ + ∫ rγ'(r)(1 − |D^⊥r|²) dμ = −∫⟨H(x), x − ξ⟩γ(r) dμ(x) (|D^⊥r|² = q; with the sign convention 3.14(‡) the right side carries a minus sign, and only |⟨H, x − ξ⟩| is used), and then uses 1 − |D^⊥r|² ≥ 0 and |⟨H, x − ξ⟩| < n to get γ(r) = 0 μ-a.e. outside B_R(ξ). That identity is (RFV) with h = ζ after step 6 below. Steps 1–10 are the parent proof's SupportInBall steps 1–6 with every detail filled in.

1. Setup. Fix n ≥ 1, ℓ, V, H: E → E, ξ ∈ E and R ≥ 0 such that V has mean curvature H in U := E ∖ B_R(ξ) = {x : |x − ξ| > R}, n^{-1}|⟨H(x), x − ξ⟩| < 1 for μ-a.e. x ∈ U, and spt V is compact; we must show spt V ⊆ B_R(ξ). U is open (complement of a closed ball). Applying (GF) to V (n ≥ 1) gives (FV1), (FV2), (FV3) for μ = μ_V. Multiplying the curvature hypothesis by n > 0 gives
(C) |⟨H(x), x − ξ⟩| < n for μ-a.e. x ∈ U.
Fix ε > 0. Steps 2–9 prove spt V ⊆ B_{R+ε}(ξ).

2. Cutoff. spt V is compact, hence bounded, so there is ρ₀ > 0 with spt V ⊆ B(ξ, ρ₀). Let W be a bounded open set containing spt V (for instance the open 1-neighbourhood {x : dist(x, spt V) < 1} of spt V, as in the parent proof, or simply W := B(ξ, ρ₀)), and choose ζ ∈ C^∞_c(E) with 0 ≤ ζ ≤ 1 and ζ = 1 on W. Such ζ exists by smooth bump functions: if W ⊆ B(ξ, ρ₁) with ρ₁ > 0 (e.g. W := B(ξ, ρ₀) and ρ₁ := ρ₀), take a C^∞ bump about ξ that equals 1 on the closed ball B_{ρ₁}(ξ) and vanishes outside B(ξ, ρ₁ + 1) (Mathlib ContDiffBump with rIn = ρ₁ > 0, rOut = ρ₁ + 1). Then ζ ∈ C¹(E), in particular ζ ∈ C¹(U) (ContDiffOn ℝ 1 ζ U). For x ∈ W, ζ is constant (= 1) on the neighbourhood W of x, so ∇ζ(x) = 0, ∇^M ζ(x) = p_x(0) = 0 and ζ(x) = 1.

3. Radial profile. Let γ(t) := (max(t − R − ε, 0))². Then γ ∈ C¹(ℝ) with γ'(t) = 2 max(t − R − ε, 0): for t > R + ε, γ(s) = (s − R − ε)² for s near t; for t < R + ε, γ ≡ 0 near t; at t₀ = R + ε, 0 ≤ γ(t₀ + s) − γ(t₀) ≤ s² for all s, so γ'(t₀) = 0; and t ↦ 2 max(t − R − ε, 0) is continuous. Moreover γ ≥ 0, γ' ≥ 0, γ(t) = γ'(t) = 0 for t ≤ R + ε, and γ(t) > 0 for t > R + ε.
Remark: steps 4–10 use only the following properties of γ: γ ∈ C¹(ℝ); γ(t) ≥ 0 and γ'(t) ≥ 0 for t ≥ 0; γ(t) = 0 for 0 ≤ t ≤ R + ε (hence γ'(t) = 0 for 0 < t < R + ε, γ vanishing on a neighbourhood of such t); γ(t) > 0 for t > R + ε. Any γ with these properties can be used in place of the specific one (the printed proof allows any such γ), and two choices are cheaper to formalize because they avoid differentiating at the kink t = R + ε: (i) γ(t) := g(t² − (R + ε)²) with g = expNegInvGlue (C^∞ by expNegInvGlue.contDiff, nondecreasing by expNegInvGlue.monotone, 0 on (−∞, 0] by expNegInvGlue.zero_of_nonpos, positive on (0, ∞) by expNegInvGlue.pos_of_pos); then γ'(t) = 2t g'(t² − (R + ε)²) ≥ 0 for t ≥ 0 (g' ≥ 0 by Monotone.deriv_nonneg), and x ↦ γ(|x − ξ|) = g(|x − ξ|² − (R + ε)²) is visibly C^∞ on E, so step 4(a) is immediate; (ii) γ(t) := g(t − R − ε), which is monotone, so γ' ≥ 0 by Monotone.deriv_nonneg, while step 4(a) is needed as written.

4. The field X(x) := (ζ(x)γ(|x − ξ|))(x − ξ) is a test field in U.
(a) X is C¹. Put g₀(x) := γ(|x − ξ|). On the open set E ∖ {ξ}, x ↦ |x − ξ| is C^∞ (the Euclidean norm is smooth away from 0) and γ ∈ C¹, so g₀ is C¹ there. On the open ball B(ξ, R + ε), which contains ξ because R + ε > 0, we have 0 ≤ |x − ξ| < R + ε, so g₀ ≡ 0 there. These two open sets cover E and being C¹ is a local property, so g₀ ∈ C¹(E). Hence X = (ζ g₀)·(x − ξ) is C¹ (products of C¹ scalar functions with the affine map x ↦ x − ξ).
(b) X has compact support: X(x) ≠ 0 implies ζ(x) ≠ 0, so tsupport X ⊆ tsupport ζ, which is compact.
(c) tsupport X ⊆ U: X(x) ≠ 0 implies γ(|x − ξ|) ≠ 0, i.e. |x − ξ| > R + ε. So supp X ⊆ {x : |x − ξ| ≥ R + ε}, a closed set; hence tsupport X ⊆ {x : |x − ξ| ≥ R + ε} ⊆ {x : |x − ξ| > R} = U, because ε > 0.

5. First variation. Apply (RFV) to (n, ℓ, V, U, H, h := ζ, γ, ξ). Its hypotheses hold: dim T_x = n μ-a.e. by (FV2), U is open, V has mean curvature H in U, ζ ∈ C¹(U), γ ∈ C¹(ℝ), and x ↦ (ζ(x)γ(|x − ξ|))(x − ξ) = X is a test field in U by step 4. Therefore
(★) ∫_U [ζ(nγ(r) + rγ'(r)(1 − q)) + γ(r)⟨x − ξ, ∇^M ζ⟩] dμ = −∫_U ζγ(r)⟨x − ξ, H⟩ dμ.

6. Removing ζ. μ(E ∖ spt V) = 0, because the complement of the support of a measure on the second-countable space E is μ-null (Mathlib Measure.support_mem_ae). For x ∈ spt V ⊆ W, step 2 gives ζ(x) = 1 and ∇^M ζ(x) = 0. Hence, for μ-a.e. x (in particular μ⌞U-a.e.), the integrand on the left of (★) equals F(x) := nγ(r) + rγ'(r)(1 − q(x)) and the integrand on the right equals G(x) := γ(r)⟨x − ξ, H(x)⟩. Integrals of μ⌞U-a.e. equal functions coincide, so
(★★) ∫_U F dμ = −∫_U G dμ.

7. Integrability. Let S := spt V ∩ {x : |x − ξ| ≥ R + ε}. S is compact (a closed subset of the compact set spt V), S ⊆ U (because R + ε > R), S ⊆ B(ξ, ρ₀), and μ(S) < ∞ by (FV1).
(a) Vanishing off S: if x ∈ spt V ∖ S then 0 ≤ r < R + ε, so γ(r) = 0 and rγ'(r) = 0 (for r = 0 the factor r vanishes; for 0 < r < R + ε, γ'(r) = 0 by step 3); hence F(x) = G(x) = γ(r) = rγ'(r)(1 − q(x)) = 0. Together with μ(E ∖ spt V) = 0, each of the functions F, G, γ(r), rγ'(r)(1 − q) and γ(r)|⟨x − ξ, H(x)⟩| equals its product with the indicator 1_S μ-a.e.
(b) Measurability: since p_x^⊥ = id − p_x, the map x ↦ p_x^⊥ is μ-a.e. strongly measurable by (FV3); applying it to the continuous map x ↦ x − ξ shows that x ↦ p_x^⊥(x − ξ), and hence q, are μ-a.e. strongly measurable. Therefore F, γ(r) and rγ'(r)(1 − q) are μ-a.e. strongly measurable (continuous functions of x and q(x)).
(c) Bounds: put M₀ := max_{[0, ρ₀]} γ and M₁ := max_{[0, ρ₀]} t γ'(t) (continuous functions on a compact interval). On S we have 0 ≤ r < ρ₀, 0 ≤ γ(r) ≤ M₀, 0 ≤ rγ'(r) ≤ M₁ and 0 ≤ 1 − q ≤ 1. Hence |F| ≤ (nM₀ + M₁)1_S, 0 ≤ γ(r) ≤ M₀1_S and 0 ≤ rγ'(r)(1 − q) ≤ M₁1_S μ-a.e.; since μ(S) < ∞, F, γ(r) and rγ'(r)(1 − q) are μ-integrable, hence μ⌞U-integrable.
(d) H is μ-integrable on the compact set S ⊆ U, because H is locally integrable on U (Mathlib LocallyIntegrableOn.integrableOn_compact_subset); in particular H is a.e. strongly measurable on S. On S, |G| ≤ γ(r) r |H| ≤ M₀ρ₀|H| (Cauchy–Schwarz: |⟨x − ξ, H⟩| ≤ r|H|). Hence 1_S G and 1_S γ(r)|⟨x − ξ, H⟩| are μ-integrable, and by (a) so are G and γ(r)|⟨x − ξ, H⟩| on U (w.r.t. μ⌞U).

8. Positivity. By (★★) and step 7 (linearity of the integral),
n∫_U γ(r) dμ + ∫_U rγ'(r)(1 − q) dμ = ∫_U F dμ = −∫_U γ(r)⟨x − ξ, H⟩ dμ ≤ ∫_U γ(r)|⟨x − ξ, H⟩| dμ.
Since rγ'(r)(1 − q) ≥ 0 everywhere (r ≥ 0, γ'(r) ≥ 0, q ≤ 1), ∫_U rγ'(r)(1 − q) dμ ≥ 0, so
∫_U γ(r)(n − |⟨H(x), x − ξ⟩|) dμ ≤ 0,
the integrand being μ⌞U-integrable as the difference of nγ(r) and γ(r)|⟨x − ξ, H⟩|. By (C) and γ ≥ 0 this integrand is ≥ 0 for μ-a.e. x ∈ U. A μ⌞U-integrable function that is ≥ 0 a.e. and has integral ≤ 0 vanishes a.e. (its integral is then 0; Mathlib integral_eq_zero_iff_of_nonneg_ae). Hence γ(r)(n − |⟨H(x), x − ξ⟩|) = 0 for μ-a.e. x ∈ U, and since n − |⟨H(x), x − ξ⟩| > 0 for μ-a.e. x ∈ U by (C), we get γ(|x − ξ|) = 0 for μ-a.e. x ∈ U.

9. Support. The set O_ε := {x : |x − ξ| > R + ε} is open, O_ε ⊆ U, and γ(|x − ξ|) > 0 for every x ∈ O_ε. By step 8, μ(O_ε) ≤ μ({x ∈ U : γ(|x − ξ|) ≠ 0}) = 0. Every point of spt μ has all its neighbourhoods of positive measure, so the open μ-null set O_ε is disjoint from spt V (Mathlib Measure.subset_compl_support_of_isOpen). Hence spt V ⊆ E ∖ O_ε = B_{R+ε}(ξ).

10. Conclusion. If x ∈ spt V then |x − ξ| ≤ R + ε for every ε > 0 by step 9, so |x − ξ| ≤ R, i.e. x ∈ B_R(ξ) (⋂_{ε>0} B_{R+ε}(ξ) = B_R(ξ)). Thus spt V ⊆ B_R(ξ), which is SupportInBall. ∎

Formalization note (not part of the argument): the pinned SimonGMT file Poincare/SimonGMT/Chapter04/CompactSupportMaximum.lean proves 6.1 for SimonGMT's own (different) varifold structure; its analytic pattern (expNegInvGlue/smoothTransition profiles, integral_eq_zero_iff_of_nonneg_ae, Measure.support_mem_ae, Measure.support_subset_of_isClosed) transfers to steps 3 and 6–9, while the identity (★) must come from (RFV), not from SimonGMT.

## Key steps

1. (GF) gives (FV1)–(FV3) for V, and the hypothesis gives |⟨H(x), x − ξ⟩| < n for μ-a.e. x ∈ U = E ∖ B_R(ξ); fix ε > 0
2. Choose ζ ∈ C^∞_c(E) with ζ ≡ 1 on a bounded open W ⊇ spt V, and γ(t) = ((t − R − ε)^+)² (C¹, γ, γ' ≥ 0, γ = 0 on (−∞, R + ε], γ > 0 beyond)
3. X(x) = (ζ(x)γ(|x − ξ|))(x − ξ) is C¹ with compact support and tsupport X ⊆ {|x − ξ| ≥ R + ε} ⊆ U, so X is a test field in U
4. (RFV) with h = ζ; since μ(E ∖ spt V) = 0 and ζ = 1, ∇^Mζ = 0 on W ⊇ spt V: ∫_U [nγ(r) + rγ'(r)(1 − q)] dμ = −∫_U γ(r)⟨x − ξ, H⟩ dμ
5. All integrands vanish μ-a.e. off the compact S = spt V ∩ {|x − ξ| ≥ R + ε} ⊆ U; q is measurable by (FV3), μ(S) < ∞ by (FV1), H ∈ L¹(S): everything is integrable
6. rγ'(r)(1 − q) ≥ 0 gives ∫_U γ(r)(n − |⟨H, x − ξ⟩|) dμ ≤ 0 with a.e. nonnegative integrand, so γ(|x − ξ|) = 0 for μ-a.e. x ∈ U
7. The open set {|x − ξ| > R + ε} ⊆ U is μ-null, hence disjoint from spt V; so spt V ⊆ B_{R+ε}(ξ) for every ε > 0 and spt V ⊆ B_R(ξ)

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `sha256sum GMT/Ch04/Contract.lean GMT/Ch04/Submission.lean <snapshot>/project/GMT/Ch04/Contract.lean`
- `rg -n 'theorem (IsCompact\.)?(isCompact_)?convexHull|IsCompact.convexHull|isCompact_convexHull|convexHull.*IsCompact|IsCompact \(convexHull' <snapshot>/mathlib/Mathlib`
- `rg -n 'IsCompact \(convexHull|IsCompact \(closedConvexHull|isClosed_convexHull|IsClosed \(convexHull' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem geometric_hahn_banach_(point_closed|closed_point)' -A6 <snapshot>/mathlib/Mathlib/Analysis/LocallyConvex/Separation.lean`
- `sed -n 140,200p <snapshot>/mathlib/Mathlib/Analysis/Convex/Caratheodory.lean; rg -n 'isCompact_stdSimplex' <snapshot>/mathlib/Mathlib`
- `rg -n 'card_le_finrank_succ|theorem LocallyIntegrableOn.integrableOn_compact_subset' <snapshot>/mathlib/Mathlib`
- `rg -n '^(theorem|lemma|def|protected def)' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `rg -n 'structure ContDiffBump' -A8 <snapshot>/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `rg -n 'theorem Convex.sum_mem|starProjection_orthogonal' <snapshot>/mathlib/Mathlib/Analysis/Convex/*.lean <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/*.lean`
- `git -C lake-packages-25730c7c/simongmt rev-parse HEAD; rg -n 'convexHull' -t lean simongmt; rg -n 'SupportInBall|ConvexHull|convex_hull|support_in_ball' -t lean simongmt`
- `cat simongmt/Poincare/SimonGMT/Chapter04/{CompactConvexHull,ConvexHullProperty,CompactSupportMaximum}.lean; ls simongmt/.lake/build/lib/lean/Poincare/SimonGMT/Chapter04/`
- `sed -n 860,905p book/chapter-04.txt (Simon 6.1, 6.2 printed proofs)`
- `rg -l 'support_in_ball_of_radial_first_variation|convex_hull_property_of_support_in_ball' <run-dir> GMT <snapshot>/project simongmt/Poincare`
- `lake env lean GMT/Ch04/Submission.lean -o /tmp/sch-a1-decomp/olean/GMT/Ch04/Submission.olean`
- `LEAN_PATH=$(lake env printenv LEAN_PATH):/tmp/sch-a1-decomp/olean lean /tmp/sch-a1-decomp/check/{ChildTypes,ChildC,ChildC2,Axioms,Final}.lean`
- `python3 -I (verifier/gmt-compare.py contract_scope; verifier/lean_contract.py validate_lean_statement on both child statements)`
- `LEAN_PATH=... lean /tmp/sch-a1-decomp/check/{Probe1,Probe2}.lean (#check of Measure.support_mem_ae, Measure.subset_compl_support_of_isOpen, LocallyIntegrableOn.integrableOn_compact_subset, integral_eq_zero_iff_of_nonneg_ae, Submodule.starProjection_orthogonal', expNegInvGlue.*, Monotone.deriv_nonneg, AffineIndependent.card_le_finrank_succ, Convex.sum_mem, geometric_hahn_banach_closed_point, finrank_euclideanSpace_fin, Submodule.finrank_le; eq_pos_convex_span_of_mem_convexHull is not reachable from the contract imports)`
- `python3 -I (re-read dag.json: 22 nodes, depth-2 lean_names of other branches)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/project/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/project/GMT/Ch04/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Convex/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Convex/Caratheodory.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Convex/Combination.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Convex/StdSimplex.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/LocallyConvex/Separation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/LinearAlgebra/AffineSpace/FiniteDimensional.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/CompactConvexHull.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/ConvexHullProperty.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/CompactSupportMaximum.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-support-convex-hull-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-radial-first-variation-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/sch-a1-decomp/check/Final.lean`
- `/tmp/sch-a1-decomp/check/ChildC2.lean`
- `/tmp/sch-a1-decomp/check/Axioms.lean`

Snapshot (project ff75f52, mathlib 25730c7c): the snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean (sha256 6e58e5dd…0f4770b). Mathlib has Carathéodory (convexHull_eq_union, eq_pos_convex_span_of_mem_convexHull), AffineIndependent.card_le_finrank_succ, isCompact_stdSimplex, Convex.sum_mem, geometric_hahn_banach_closed_point/point_closed, Measure.support_mem_ae, Measure.subset_compl_support_of_isOpen, LocallyIntegrableOn.integrableOn_compact_subset, ContDiffBump and Submodule.starProjection_orthogonal', but no compact-convex-hull lemma for compact (non-finite) sets (only Set.Finite.isCompact_convexHull / isClosed_convexHull). The pinned SimonGMT (rev 2b3663083f3fe399b6296fb8eaee52169170e197, oleans built) has Poincare.SimonGMT.Chapter04.isCompact_convexHull_of_isCompact and exists_closedBall_separating_of_compact_convex in Chapter04/CompactConvexHull.lean (imports only Mathlib; #print axioms: propext, Classical.choice, Quot.sound; they apply to Ambient n ℓ), which make the 6.2 child short; its 6.1/6.2 theorems (CompactSupportMaximum.lean, ConvexHullProperty.lean) are proved only for SimonGMT's strengthened Chapter04.RectifiableVarifold, which the contract does not use (README), so 6.1 must be re-proved from radial_first_variation, with CompactSupportMaximum.lean as a pattern only. Both child types elaborate in the comparator scope, the parent assembly has exactly the frozen parent type, the 6.2 child was fully proved in Lean with standard axioms, and the new names collide with nothing.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: https://github.com/ZhengyangZhang06/gmt-formalize/pull/1721

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
