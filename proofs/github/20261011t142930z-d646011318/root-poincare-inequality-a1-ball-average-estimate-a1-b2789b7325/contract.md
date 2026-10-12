<!-- theorem-id: gmt-ch04/root.poincare_inequality-a1.ball_average_estimate-a1 -->

## Theorem `Submission.bounded_curvature_ball_average_estimate`

Assume (WMI) — the frozen statement of the sibling theorem weighted_monotonicity_identity, taken as a hypothesis exactly as displayed at the start of the Lean statement: for all n, ℓ, V : RectifiableVarifold n ℓ, U, H, h : Ambient n ℓ → ℝ, ξ and σ, ρ ∈ ℝ with n ≥ 1, (FV1) μ_V finite on compacts, (FV2) dim T_xV = n μ_V-a.e., (FV3) x ↦ p_{T_xV} μ_V-a.e. strongly measurable, U open, V has mean curvature H in U, h ∈ C¹(U), tsupport h ∩ B_ρ(ξ) ⊆ U and 0 < σ ≤ ρ: the function τ ↦ τ^{−(n+1)} ∫_{B_τ(ξ)} ⟨x − ξ, ∇^M h(x) + h(x)H(x)⟩ dμ_V(x) is integrable on (σ, ρ], the function h·q_ξ/|x − ξ|ⁿ (q_ξ = V.normalRadialSq ξ) is μ_V-integrable on B_ρ(ξ)∖B_σ(ξ), and ρ^{−n}∫_{B_ρ(ξ)} h dμ_V − σ^{−n}∫_{B_σ(ξ)} h dμ_V = ∫_{B_ρ(ξ)∖B_σ(ξ)} h q_ξ/|x − ξ|ⁿ dμ_V + ∫_{(σ,ρ]} τ^{−(n+1)} ∫_{B_τ(ξ)} ⟨x − ξ, ∇^M h + hH⟩ dμ_V dτ. Let n ≥ 1, ℓ ∈ ℕ, V : RectifiableVarifold n ℓ with μ = μ_V satisfying (FV1)–(FV3), U ⊆ ℝ^{n+ℓ} open, H a generalized mean curvature of V in U, Λ ≥ 0 with |H| ≤ Λ μ-a.e. in U, g ∈ C¹(U) with g ≥ 0 on U, y ∈ ℝ^{n+ℓ}, 0 < s ≤ r with B_r(y) ⊆ U, and assume x ↦ |∇^M g(x)| |x − y|^{1−n} is μ-integrable on B_r(y). Then s^{−n}∫_{B_s(y)} g dμ ≤ e^{Λ(r−s)} ( r^{−n}∫_{B_r(y)} g dμ + n^{−1}∫_{B_r(y)} |∇^M g(x)| |x − y|^{1−n} dμ(x) ). (Real powers; Bochner integrals.)

Node: `root.poincare_inequality-a1.ball_average_estimate-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/62

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/384

Decomposition children: None

## Lean problem

Declaration: `Submission.bounded_curvature_ball_average_estimate`

```lean
(∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)) (H : Ambient n ℓ → Ambient n ℓ) (h : Ambient n ℓ → ℝ) (ξ : Ambient n ℓ) (σ ρ : ℝ), 0 < n → IsFiniteMeasureOnCompacts V.weight → (∀ᵐ x ∂V.weight, Module.finrank ℝ (V.tangentSpace x) = n) → AEStronglyMeasurable (fun x ↦ (V.tangentSpace x).starProjection) V.weight → IsOpen U → V.HasMeanCurvatureIn U H → ContDiffOn ℝ 1 h U → tsupport h ∩ closedBall ξ ρ ⊆ U → 0 < σ → σ ≤ ρ → IntegrableOn (fun τ ↦ (∫ x in closedBall ξ τ, inner ℝ (x - ξ) (V.tangentialGradient h x + h x • H x) ∂V.weight) / τ ^ (n + 1)) (Ioc σ ρ) ∧ IntegrableOn (fun x ↦ h x * (V.normalRadialSq ξ x / ‖x - ξ‖ ^ n)) (closedBall ξ ρ \ closedBall ξ σ) V.weight ∧ (∫ x in closedBall ξ ρ, h x ∂V.weight) / ρ ^ n - (∫ x in closedBall ξ σ, h x ∂V.weight) / σ ^ n = ∫ x in closedBall ξ ρ \ closedBall ξ σ, h x * (V.normalRadialSq ξ x / ‖x - ξ‖ ^ n) ∂V.weight + ∫ τ in Ioc σ ρ, (∫ x in closedBall ξ τ, inner ℝ (x - ξ) (V.tangentialGradient h x + h x • H x) ∂V.weight) / τ ^ (n + 1)) → ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)) (H : Ambient n ℓ → Ambient n ℓ) (Λ : ℝ) (g : Ambient n ℓ → ℝ) (y : Ambient n ℓ) (r s : ℝ), 0 < n → IsFiniteMeasureOnCompacts V.weight → (∀ᵐ x ∂V.weight, Module.finrank ℝ (V.tangentSpace x) = n) → AEStronglyMeasurable (fun x ↦ (V.tangentSpace x).starProjection) V.weight → IsOpen U → V.HasMeanCurvatureIn U H → 0 ≤ Λ → (∀ᵐ x ∂V.weight, x ∈ U → ‖H x‖ ≤ Λ) → ContDiffOn ℝ 1 g U → (∀ x ∈ U, 0 ≤ g x) → closedBall y r ⊆ U → 0 < s → s ≤ r → IntegrableOn (fun x ↦ ‖V.tangentialGradient g x‖ * ‖x - y‖ ^ (1 - (n : ℝ))) (closedBall y r) V.weight → (∫ x in closedBall y s, g x ∂V.weight) / s ^ n ≤ Real.exp (Λ * (r - s)) * ((∫ x in closedBall y r, g x ∂V.weight) / r ^ n + (n : ℝ)⁻¹ * ∫ x in closedBall y r, ‖V.tangentialGradient g x‖ * ‖x - y‖ ^ (1 - (n : ℝ)) ∂V.weight)
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

- Parent DAG node: `root.poincare_inequality-a1`
- Child DAG node: `root.poincare_inequality-a1.ball_average_estimate-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 2 ('Gronwall form of 5.4'), with the Gronwall computation supplied by the sibling integral_gronwall and the sibling theorem weighted_monotonicity_identity supplied as the hypothesis (WMI). Corrections as documented in the parent: the coefficient in 5.2 is Λ (not Λρ), which produces the factor e^{Λ(r−s)}.

0. Notation. μ = V.weight, B_τ = B_τ(y) (closed ball), r > 0 (as 0 < s ≤ r). For τ ∈ ℝ put
f(τ) := τ^{−n} ∫_{B_τ} g dμ,  R(τ) := τ^{−(n+1)} ∫_{B_τ} |x − y| |∇^M g(x)| dμ(x),
Q(τ) := τ^{−(n+1)} ∫_{B_τ} ⟨x − y, ∇^M g(x) + g(x)H(x)⟩ dμ(x),  K_g := ∫_{B_r} |∇^M g(x)| |x − y|^{1−n} dμ(x).
The claim is f(s) ≤ e^{Λ(r−s)} (f(r) + n^{−1}K_g).

1. Preliminary facts. μ(B_τ) < ∞ for every τ by (FV1). Since B_r ⊆ U and g ∈ C¹(U), g is continuous on the compact set B_r, hence bounded there, and g ≥ 0 on B_r. The gradient ∇g is continuous on the open set U, so |∇g| ≤ C₁ on B_r for some C₁; as an orthogonal projection has norm ≤ 1, |∇^M g(x)| = |p_{T_xV}(∇g(x))| ≤ |∇g(x)| ≤ C₁ on B_r. The map x ↦ ∇^M g(x) is μ-a.e. strongly measurable: x ↦ ∇g(x) (the Riesz representative of Dg(x)) is Borel measurable for every function g, x ↦ p_{T_xV} is μ-a.e. strongly measurable by (FV3), and evaluation (L, v) ↦ L v is continuous bilinear. H is μ-integrable on B_r, because V has mean curvature H in U (H is locally integrable on U) and B_r is a compact subset of U. Consequently, for every τ ≤ r the functions g, x ↦ |x − y||∇^M g(x)| (bounded by rC₁) and x ↦ ⟨x − y, ∇^M g(x) + g(x)H(x)⟩ (the first part bounded by rC₁, the second dominated by (sup_{B_r} g)·r|H|) are μ-integrable on B_τ.

2. Integrability in τ. On [s, r] the functions τ ↦ ∫_{B_τ} g dμ and τ ↦ ∫_{B_τ} |x − y||∇^M g| dμ are nondecreasing (nonnegative integrands on B_r, nested balls), hence a.e.-measurable for Lebesgue measure on [s, r]; so f and R are a.e.-measurable on [s, r], and they are bounded there by s^{−n}∫_{B_r} g dμ and s^{−(n+1)}∫_{B_r}|x − y||∇^M g| dμ. Hence f and R are integrable on [s, r]. Moreover R(τ) ≥ 0 for τ > 0. Put P := ∫_{(s,r]} R(τ) dτ ≥ 0.

3. Claim: f(σ) ≤ f(r) + P + Λ ∫_{(σ,r]} f(τ) dτ for every σ ∈ [s, r].
(a) Apply (WMI) with (n, ℓ, V, U, H, h := g, ξ := y, σ, ρ := r). Its hypotheses hold: n ≥ 1, (FV1)–(FV3), U open, H a mean curvature of V in U, g ∈ C¹(U), tsupport g ∩ B_r ⊆ B_r ⊆ U, 0 < σ ≤ r. It yields that Q is integrable on (σ, r] and f(r) − f(σ) = W + ∫_{(σ,r]} Q(τ) dτ, where W := ∫_{B_r∖B_σ} g(x) q_y(x)/|x − y|ⁿ dμ(x).
(b) W ≥ 0: on B_r∖B_σ ⊆ U we have g ≥ 0, q_y = |p^⊥(x − y)|²/|x − y|² ≥ 0 and |x − y|ⁿ ≥ 0.
(c) Let τ ∈ (σ, r]. For μ-a.e. x ∈ B_τ we have x ∈ U, hence |H(x)| ≤ Λ, and by Cauchy–Schwarz, g(x) ≥ 0 and |x − y| ≤ τ:
⟨x − y, ∇^M g + gH⟩ = ⟨x − y, ∇^M g⟩ + g⟨x − y, H⟩ ≥ −|x − y||∇^M g| − g|x − y||H| ≥ −|x − y||∇^M g| − τΛg.
Integrating over B_τ (all functions integrable by step 1): ∫_{B_τ}⟨x − y, ∇^M g + gH⟩ dμ ≥ −∫_{B_τ}|x − y||∇^M g| dμ − τΛ∫_{B_τ} g dμ, and dividing by τ^{n+1} > 0: Q(τ) ≥ −R(τ) − Λ f(τ).
(d) Integrating (c) over (σ, r] (Q, R and f are integrable there): ∫_{(σ,r]} Q ≥ −∫_{(σ,r]} R − Λ∫_{(σ,r]} f. Since R ≥ 0 and (σ, r] ⊆ (s, r], ∫_{(σ,r]} R ≤ P.
(e) Therefore f(σ) = f(r) − W − ∫_{(σ,r]} Q ≤ f(r) + P + Λ∫_{(σ,r]} f.

4. Apply the sibling integral_gronwall with a := s, b := r, Λ, C := f(r) + P and the function f (integrable on [s, r] by step 2; hypothesis = step 3). At s ∈ [s, r] it gives f(s) ≤ (f(r) + P) e^{Λ(r−s)}.

5. Claim: P ≤ n^{−1} K_g. Work with lower integrals and ofReal = ENNReal.ofReal.
(a) For τ ∈ (s, r]: R(τ) = τ^{−n−1}·∫_{B_τ}|x − y||∇^M g| dμ with τ^{−n−1} = 1/τ^{n+1} > 0 and an integrable nonnegative integrand, so ofReal(R(τ)) = ofReal(τ^{−n−1}) ∫_{B_τ} ofReal(|x − y||∇^M g(x)|) dμ(x) = ∫_{B_r} ofReal(τ^{−n−1}) 1_{|x−y|≤τ} ofReal(|x − y||∇^M g(x)|) dμ(x) (B_τ ⊆ B_r).
(b) ofReal(P) = ∫_{(s,r]} ofReal(R(τ)) dτ (R is integrable and nonnegative on (s, r]) = ∫_{(s,r]} ∫_{B_r} (…) dμ dτ = ∫_{B_r} ∫_{(s,r]} (…) dτ dμ by Tonelli; the integrand is a.e.-measurable for (Lebesgue on (s, r]) ⊗ (μ⌞B_r) as a product of a measurable function of τ, the indicator of the closed set {(τ, x) : |x − y| ≤ τ}, and an a.e.-measurable function of x.
(c) Fix x ∈ B_r and put d := |x − y|. If d = 0 the integrand vanishes identically. If d > 0, the inner integral is at most ofReal(d|∇^M g(x)|) ∫_{[d,∞)} ofReal(τ^{−n−1}) dτ = ofReal(d|∇^M g(x)|)·ofReal(∫_d^∞ τ^{−n−1} dτ) = ofReal(d|∇^M g(x)|·d^{−n}/n) = ofReal(n^{−1}|∇^M g(x)| d^{1−n}) (the exponent −n−1 < −1, and [d, ∞) and (d, ∞) differ by a null set).
(d) Hence ofReal(P) ≤ ∫_{B_r} ofReal(n^{−1}|∇^M g(x)||x − y|^{1−n}) dμ(x) = ofReal(n^{−1}K_g), the integrand being μ-integrable on B_r by hypothesis; since n^{−1}K_g ≥ 0, P ≤ n^{−1}K_g.

6. As e^{Λ(r−s)} > 0, steps 4 and 5 give f(s) ≤ (f(r) + P)e^{Λ(r−s)} ≤ e^{Λ(r−s)}(f(r) + n^{−1}K_g), which is the assertion. ∎

Remark (used by the parent for the growth bound): for g ≡ 1 one has ∇^M g = 0, so K_g = 0 and the estimate reads μ(B_s(y))/sⁿ ≤ e^{Λ(r−s)} μ(B_r(y))/rⁿ.

Formalization notes (Mathlib/Lean names used in a machine-checked transcription of the numbered argument): IsCompact.exists_bound_of_continuousOn, ContDiffOn.continuousOn_fderiv_of_isOpen, Submodule.norm_starProjection_apply_le, measurable_fderiv, ContinuousLinearMap.aestronglyMeasurable_comp₂, LocallyIntegrableOn.integrableOn_compact_subset, AEStronglyMeasurable.inner, Integrable.bdd_mul, aemeasurable_restrict_of_monotoneOn, Integrable.of_bound, integral_mono_ae, setIntegral_mono_on, setIntegral_mono_set, ofReal_integral_eq_lintegral_ofReal, lintegral_lintegral_swap, AEMeasurable.comp_snd, AEMeasurable.indicator, Ioi_ae_eq_Ici, integrableOn_Ioi_rpow_of_lt, integral_Ioi_rpow_of_lt.

Appendix (machine-checked reference transcription; the numbered argument above is the proof). The following tactic block is the proof (the text after `:= by`) of the declaration `theorem bounded_curvature_ball_average_estimate` with exactly the frozen lean_statement above as its type, inside `namespace Submission` (scope `open MeasureTheory Metric Set Filter Topology`, `open scoped ENNReal ContDiff CompactlySupported`, `namespace GMT.Ch04`, `noncomputable section`, `open RectifiableVarifold`, after `import GMT.Ch04.Submission`), compiles with Lean v4.35.0-rc3 / Mathlib 25730c7c and depends only on propext, Classical.choice and Quot.sound. Extra imports: `Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner`, `Mathlib.Analysis.SpecialFunctions.ImproperIntegrals`. The script calls the sibling child as `Submission.backward_integral_gronwall_Ioc`.
```lean
  intro hWMI n ℓ V U H Λ g y r s hn hFV1 hFV2 hFV3 hU hH hΛ hHΛ hg hg0 hball hs hsr hint
  haveI := hFV1
  set μ := V.weight with hμ
  have hr : 0 < r := hs.trans_le hsr
  have hgcont : ContinuousOn g U := hg.continuousOn
  -- bounds on the closed ball of radius r
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
      (InnerProductSpace.toDual ℝ (Ambient n ℓ)).symm.continuous.measurable.comp (measurable_fderiv ℝ g)
    exact (ContinuousLinearMap.id ℝ (Ambient n ℓ →L[ℝ] Ambient n ℓ)).aestronglyMeasurable_comp₂
      hFV3 hgm.aestronglyMeasurable
  have hfinB : ∀ τ : ℝ, IsFiniteMeasure (μ.restrict (closedBall y τ)) := fun τ => ⟨by
    rw [Measure.restrict_apply_univ]; exact (isCompact_closedBall y τ).measure_lt_top⟩
  have hsubB : ∀ τ ≤ r, closedBall y τ ⊆ closedBall y r := fun τ hτ => closedBall_subset_closedBall hτ
  -- integrability on balls
  have hgint : ∀ τ ≤ r, IntegrableOn g (closedBall y τ) μ := fun τ hτ =>
    (hgcont.mono ((hsubB τ hτ).trans hball)).integrableOn_compact (isCompact_closedBall y τ)
  have hFint : ∀ τ ≤ r, IntegrableOn (fun x => ‖x - y‖ * ‖V.tangentialGradient g x‖) (closedBall y τ) μ := by
    intro τ hτ
    haveI := hfinB τ
    refine Integrable.of_bound (C := r * Cg1)
      (((continuous_id.sub continuous_const).norm.aestronglyMeasurable).mul hTGmeas.norm).restrict ?_
    refine (ae_restrict_iff' measurableSet_closedBall).2 (Eventually.of_forall fun x hx => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    have h1 : ‖x - y‖ ≤ r := by rw [← dist_eq_norm]; exact (mem_closedBall.1 hx).trans hτ
    exact mul_le_mul h1 (hTGbound x (hsubB τ hτ hx)) (norm_nonneg _) hr.le
  have hHint : IntegrableOn H (closedBall y r) μ :=
    hH.1.integrableOn_compact_subset hball (isCompact_closedBall y r)
  -- integrability of the inner integrand on balls
  have hsubm : AEStronglyMeasurable (fun x : Ambient n ℓ => x - y) μ :=
    (continuous_sub_right y).aestronglyMeasurable
  have hQint : ∀ τ ≤ r, IntegrableOn
      (fun x => inner ℝ (x - y) (V.tangentialGradient g x + g x • H x)) (closedBall y τ) μ := by
    intro τ hτ
    haveI := hfinB τ
    have h1 : IntegrableOn (fun x => inner ℝ (x - y) (V.tangentialGradient g x)) (closedBall y τ) μ := by
      refine Integrable.of_bound (C := r * Cg1) ?_ ?_
      · exact (hsubm.inner hTGmeas).restrict
      · refine (ae_restrict_iff' measurableSet_closedBall).2 (Eventually.of_forall fun x hx => ?_)
        refine (norm_inner_le_norm _ _).trans ?_
        have h1 : ‖x - y‖ ≤ r := by rw [← dist_eq_norm]; exact (mem_closedBall.1 hx).trans hτ
        exact mul_le_mul h1 (hTGbound x (hsubB τ hτ hx)) (norm_nonneg _) hr.le
    have hHτ : IntegrableOn (fun x => inner ℝ (x - y) (H x)) (closedBall y τ) μ := by
      have hH' := hHint.mono_set (hsubB τ hτ)
      refine (hH'.norm.const_mul r).mono' (hsubm.restrict.inner hH'.aestronglyMeasurable) ?_
      refine (ae_restrict_iff' measurableSet_closedBall).2 (Eventually.of_forall fun x hx => ?_)
      refine (norm_inner_le_norm _ _).trans ?_
      have h1 : ‖x - y‖ ≤ r := by rw [← dist_eq_norm]; exact (mem_closedBall.1 hx).trans hτ
      exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    have h2 : IntegrableOn (fun x => g x * inner ℝ (x - y) (H x)) (closedBall y τ) μ := by
      refine Integrable.bdd_mul (c := Cg0) hHτ ?_ ?_
      · exact (hgcont.mono ((hsubB τ hτ).trans hball)).aestronglyMeasurable measurableSet_closedBall
      · exact (ae_restrict_iff' measurableSet_closedBall).2 (Eventually.of_forall fun x hx =>
          hCg0 x (hsubB τ hτ hx))
    refine (h1.add h2).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, inner_add_right, inner_smul_right]
  -- the radial functions
  set f : ℝ → ℝ := fun τ => (∫ x in closedBall y τ, g x ∂μ) / τ ^ n with hf
  set R : ℝ → ℝ := fun τ =>
    (∫ x in closedBall y τ, ‖x - y‖ * ‖V.tangentialGradient g x‖ ∂μ) / τ ^ (n + 1) with hR
  have hg0B : ∀ x ∈ closedBall y r, 0 ≤ g x := fun x hx => hg0 x (hball hx)
  -- monotonicity in τ of the ball integrals of nonnegative functions
  have hmonog : MonotoneOn (fun τ => ∫ x in closedBall y τ, g x ∂μ) (Icc s r) := by
    intro a ha b hb hab
    exact setIntegral_mono_set (hgint b hb.2)
      ((ae_restrict_iff' measurableSet_closedBall).2 (Eventually.of_forall fun x hx =>
        hg0B x (hsubB b hb.2 hx)))
      (Eventually.of_forall (closedBall_subset_closedBall hab))
  have hmonoF : MonotoneOn (fun τ => ∫ x in closedBall y τ, ‖x - y‖ * ‖V.tangentialGradient g x‖ ∂μ)
      (Icc s r) := by
    intro a ha b hb hab
    exact setIntegral_mono_set (hFint b hb.2)
      (Eventually.of_forall fun x => by positivity)
      (Eventually.of_forall (closedBall_subset_closedBall hab))
  have hIg_nonneg : ∀ τ, 0 ≤ ∫ x in closedBall y τ, g x ∂μ ∨ r < τ := by
    intro τ
    by_cases hτ : τ ≤ r
    · exact Or.inl (setIntegral_nonneg measurableSet_closedBall fun x hx => hg0B x (hsubB τ hτ hx))
    · exact Or.inr (not_le.1 hτ)
  haveI : IsFiniteMeasure (volume.restrict (Icc s r)) := ⟨by
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
  have hP0 : 0 ≤ P := setIntegral_nonneg measurableSet_Ioc fun τ hτ => hR0 τ (hs.trans hτ.1)
  have hstepA : ∀ σ ∈ Icc s r, f σ ≤ (f r + P) + Λ * ∫ τ in Ioc σ r, f τ := by
    intro σ hσ
    have hσ0 : 0 < σ := hs.trans_le hσ.1
    obtain ⟨hQi, -, hid⟩ := hWMI n ℓ V U H g y σ r hn hFV1 hFV2 hFV3 hU hH hg
      (fun x hx => hball hx.2) hσ0 hσ.2
    have hW0 : 0 ≤ ∫ x in closedBall y r \ closedBall y σ,
        g x * (V.normalRadialSq y x / ‖x - y‖ ^ n) ∂μ := by
      refine setIntegral_nonneg (measurableSet_closedBall.diff measurableSet_closedBall) fun x hx => ?_
      have : 0 ≤ V.normalRadialSq y x := by unfold RectifiableVarifold.normalRadialSq; positivity
      exact mul_nonneg (hg0B x hx.1) (div_nonneg this (by positivity))
    have hQlow : ∀ τ ∈ Ioc σ r, -R τ - Λ * f τ ≤
        (∫ x in closedBall y τ, inner ℝ (x - y) (V.tangentialGradient g x + g x • H x) ∂μ) /
          τ ^ (n + 1) := by
      intro τ hτ
      have hτ0 : 0 < τ := hσ0.trans hτ.1
      have hτr : τ ≤ r := hτ.2
      have hint1 : ∫ x in closedBall y τ, (-(‖x - y‖ * ‖V.tangentialGradient g x‖) - τ * Λ * g x) ∂μ ≤
          ∫ x in closedBall y τ, inner ℝ (x - y) (V.tangentialGradient g x + g x • H x) ∂μ := by
        refine integral_mono_ae ((hFint τ hτr).neg.sub ((hgint τ hτr).const_mul (τ * Λ)))
          (hQint τ hτr) ?_
        filter_upwards [ae_restrict_mem measurableSet_closedBall, ae_restrict_of_ae hHΛ] with x hx hHx
        have hxU : x ∈ U := hball (hsubB τ hτr hx)
        have hgx : 0 ≤ g x := hg0 x hxU
        have hxy : ‖x - y‖ ≤ τ := by rw [← dist_eq_norm]; exact mem_closedBall.1 hx
        have hH1 : ‖H x‖ ≤ Λ := hHx hxU
        have i1 : -(‖x - y‖ * ‖V.tangentialGradient g x‖) ≤ inner ℝ (x - y) (V.tangentialGradient g x) :=
          neg_le_of_abs_le (abs_real_inner_le_norm _ _)
        have i2 : -(‖x - y‖ * ‖H x‖) ≤ inner ℝ (x - y) (H x) := neg_le_of_abs_le (abs_real_inner_le_norm _ _)
        have i3 : ‖x - y‖ * ‖H x‖ ≤ τ * Λ := mul_le_mul hxy hH1 (norm_nonneg _) hτ0.le
        simp only [inner_add_right, inner_smul_right]
        nlinarith [mul_le_mul_of_nonneg_left i3 hgx, mul_le_mul_of_nonneg_left i2 hgx]
      have heq : ∫ x in closedBall y τ, (-(‖x - y‖ * ‖V.tangentialGradient g x‖) - τ * Λ * g x) ∂μ =
          -(∫ x in closedBall y τ, ‖x - y‖ * ‖V.tangentialGradient g x‖ ∂μ) -
            τ * Λ * ∫ x in closedBall y τ, g x ∂μ := by
        rw [integral_sub (f := fun x => -(‖x - y‖ * ‖V.tangentialGradient g x‖))
          (g := fun x => τ * Λ * g x) (hFint τ hτr).neg ((hgint τ hτr).const_mul (τ * Λ)),
          integral_neg, integral_const_mul]
      rw [heq] at hint1
      have hpos : (0 : ℝ) < τ ^ (n + 1) := pow_pos hτ0 _
      have hfτ : f τ = (∫ x in closedBall y τ, g x ∂μ) / τ ^ n := rfl
      have hRτ : R τ = (∫ x in closedBall y τ, ‖x - y‖ * ‖V.tangentialGradient g x‖ ∂μ) / τ ^ (n + 1) := rfl
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
        ∫ τ in Ioc σ r, (∫ x in closedBall y τ, inner ℝ (x - y) (V.tangentialGradient g x + g x • H x) ∂μ) /
          τ ^ (n + 1) := by
      have hsubI : Ioc σ r ⊆ Icc s r := fun τ hτ => ⟨hσ.1.trans hτ.1.le, hτ.2⟩
      have hRi := hRint.mono_set hsubI
      have hfi := hfint.mono_set hsubI
      rw [← integral_neg, ← integral_const_mul, ← integral_sub (f := fun τ => -R τ)
        (g := fun τ => Λ * f τ) hRi.neg (hfi.const_mul Λ)]
      exact setIntegral_mono_on (hRi.neg.sub (hfi.const_mul Λ)) hQi measurableSet_Ioc hQlow
    have hRle : ∫ τ in Ioc σ r, R τ ≤ P := by
      refine setIntegral_mono_set (hRint.mono_set Ioc_subset_Icc_self) ?_ ?_
      · exact (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun τ hτ => hR0 τ (hs.trans hτ.1))
      · exact Eventually.of_forall (Ioc_subset_Ioc_left hσ.1)
    have hfr : f r = (∫ x in closedBall y r, g x ∂μ) / r ^ n := rfl
    have hfσ : f σ = (∫ x in closedBall y σ, g x ∂μ) / σ ^ n := rfl
    rw [hfσ, hfr]
    rw [hfr] at *
    linarith
  have hB := Submission.backward_integral_gronwall_Ioc s r Λ (f r + P) f hsr hΛ hfint hstepA s
    ⟨le_rfl, hsr⟩
  set Kg := ∫ x in closedBall y r, ‖V.tangentialGradient g x‖ * ‖x - y‖ ^ (1 - (n : ℝ)) ∂μ with hKg
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hKg0 : 0 ≤ Kg := setIntegral_nonneg measurableSet_closedBall fun x _ => by positivity
  have hstepC : P ≤ (n : ℝ)⁻¹ * Kg := by
    set Fe : Ambient n ℓ → ℝ≥0∞ := fun x => ENNReal.ofReal (‖x - y‖ * ‖V.tangentialGradient g x‖)
      with hFe
    have hFeae : AEMeasurable Fe μ :=
      ENNReal.measurable_ofReal.comp_aemeasurable ((hsubm.norm.mul hTGmeas.norm).aemeasurable)
    have h1 : ENNReal.ofReal P = ∫⁻ τ in Ioc s r, ENNReal.ofReal (R τ) :=
      ofReal_integral_eq_lintegral_ofReal (hRint.mono_set Ioc_subset_Icc_self)
        ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun τ hτ => hR0 τ (hs.trans hτ.1)))
    have h2 : ∀ τ ∈ Ioc s r, ENNReal.ofReal (R τ) = ∫⁻ x in closedBall y r,
        ENNReal.ofReal (τ ^ (-(n : ℝ) - 1)) * (closedBall y τ).indicator Fe x ∂μ := by
      intro τ hτ
      have hτ0 : 0 < τ := hs.trans hτ.1
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator measurableSet_closedBall,
        Measure.restrict_restrict measurableSet_closedBall, Set.inter_eq_left.2 (hsubB τ hτ.2),
        ← ofReal_integral_eq_lintegral_ofReal (hFint τ hτ.2) (Eventually.of_forall fun x => by positivity),
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
          · have : ‖x - y‖ ∈ Ici τ ∨ True := Or.inr trivial
            rw [Set.indicator_of_mem hm, Set.indicator_of_mem (by
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
          _ = ENNReal.ofReal ((n : ℝ)⁻¹ * (‖V.tangentialGradient g x‖ * ‖x - y‖ ^ (1 - (n : ℝ)))) := by
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
  have hexpos : 0 < Real.exp (Λ * (r - s)) := Real.exp_pos _
  have hfs : f s = (∫ x in closedBall y s, g x ∂μ) / s ^ n := rfl
  have hfr : f r = (∫ x in closedBall y r, g x ∂μ) / r ^ n := rfl
  rw [← hfs, ← hfr]
  calc f s ≤ (f r + P) * Real.exp (Λ * (r - s)) := hB
    _ ≤ (f r + (n : ℝ)⁻¹ * Kg) * Real.exp (Λ * (r - s)) := by gcongr
    _ = Real.exp (Λ * (r - s)) * (f r + (n : ℝ)⁻¹ * Kg) := mul_comm _ _
```

## Key steps

1. WMI at radii σ ≤ r: f(r) − f(σ) = W + ∫_{(σ,r]} Q with W ≥ 0
2. |H| ≤ Λ, Cauchy–Schwarz and |x−y| ≤ τ: Q(τ) ≥ −R(τ) − Λf(τ)
3. f(σ) ≤ f(r) + P + Λ∫_{(σ,r]} f for σ ∈ [s, r], with P = ∫_{(s,r]} R and f, R integrable on [s, r]
4. sibling integral_gronwall: f(s) ≤ (f(r) + P)e^{Λ(r−s)}
5. Tonelli: P ≤ n⁻¹∫_{B_r}|∇^M g||x−y|^{1−n} since ∫_d^∞ τ^{−n−1}dτ = d^{−n}/n

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json`
- `sha256sum GMT/Ch04/Contract.lean GMT/Ch04/Submission.lean <snapshot>/project/GMT/Ch04/Contract.lean`
- `python3: read lean_name/lean_statement of every node in <run>/dag.json and every */decomposition*.json (uncle frozen types; name-collision check)`
- `rg -n 'theorem|lemma' <snapshot>/mathlib/Mathlib/Analysis/ODE/Gronwall.lean; grep -ril gronwall <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem lintegral_eq_lintegral_meas_lt|theorem lintegral_comp_eq_lintegral_meas_lt_mul|theorem lintegral_lintegral_swap|theorem lintegral_prod_swap' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem measurable_fderiv |theorem measurable_deriv |theorem measurableSet_of_differentiableAt ' <snapshot>/mathlib/Mathlib`
- `rg -n '^theorem|^lemma' <snapshot>/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean; rg -n 'gradient_fun_const|gradient_eq' <snapshot>/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean`
- `rg -n 'Integrable.bdd_mul|support_mem_ae|norm_starProjection_apply_le|aestronglyMeasurable_comp₂|apply_continuousLinearMap|Monotone.deriv_nonneg|integral_comp_sub_left|integral_deriv_eq_sub|integral_Ioi_rpow_of_lt|integrableOn_Ioi_rpow_of_lt|rpow_inv_lt_iff_of_neg|lt_rpow_inv_iff_of_neg|continuousOn_primitive_interval_left|integral_hasDerivAt_left|monotoneOn_of_deriv_nonneg|aemeasurable_restrict_of_monotoneOn|integrableOn_of_bounded|setIntegral_mono_set|AEMeasurable.comp_snd' <snapshot>/mathlib/Mathlib`
- `grep -rniE 'gronwall|layercake|poincare|monotonicity' lake-packages-25730c7c/simongmt/Poincare; grep -n '^theorem' simongmt/Poincare/SimonGMT/Chapter04/{Poincare,PoincareKernel,PoincareTruncation,LayerCake}.lean`
- `python3: verifier/gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch04.main_theorem') and lean_contract.validate_lean_statement on all child statements`
- `lake env lean GMT/Ch04/Submission.lean -o /tmp/ch04-poincare-split/olean/GMT/Ch04/Submission.olean`
- `LEAN_PATH=...:/tmp/ch04-poincare-split/olean lean /tmp/ch04-poincare-split/src/ChildTypes.lean`
- `lean /tmp/ch04-poincare-split/asm/A7.lean (parent assembly from sorried children and byte-identical uncle stubs)`
- `lean /tmp/ch04-poincare-split/kids/K1..K7.lean and /tmp/ch04-poincare-split/full/Full.lean with #print axioms`
- `HUMANIZE_RUN_DIR=/tmp/ch04-poincare-split/fakerun python3 verifier/gmt-compare.py --lean-target GMT/Ch04/Submission.lean --verifier-dir verifier --packages lake-packages-25730c7c --frozen-commit ff75f52a4c9deb3b3abbd91eb31d7b02e29a4cef --dry-run root.poincare_inequality-a1.tangentialGradient_comp_of_differentiableAt-a1`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/project/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-poincare-inequality-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/ODE/Gronwall.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/ODE/DiscreteGronwall.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Layercake.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Inner.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/SpecialFunctions/ImproperIntegrals.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/Deriv/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/Deriv/Slope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/Poincare.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/PoincareKernel.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/PoincareTruncation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/LayerCake.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/ch04-poincare-split/src/ChildTypes.lean`
- `/tmp/ch04-poincare-split/asm/A7.lean`
- `/tmp/ch04-poincare-split/full/Full.lean`

The snapshot contract (sha256 6e58e5dd…0f4770b) is byte-identical to the workspace Contract.lean and Submission.lean. The Mathlib (25730c7c) and SimonGMT (2b366308) revisions match the project manifest. The pinned Mathlib has no integral-form Gronwall inequality (only Analysis/ODE/Gronwall.lean, which is differential, and DiscreteGronwall.lean), so integral_gronwall is a genuine new obligation. Mathlib supplies the other ingredients: the layer-cake formula (lintegral_eq_lintegral_meas_lt), Tonelli (lintegral_lintegral_swap), measurable_fderiv for arbitrary functions, Real.smoothTransition, improper rpow integrals (integral_Ioi_rpow_of_lt) and FTC/monotonicity lemmas. SimonGMT has an earlier Poincaré development (Chapter04/Poincare.lean, PoincareKernel.lean, PoincareTruncation.lean), but it is stated for the strengthened Chapter04.RectifiableVarifold, which the Ch04 README says needs a transport construction, so it is not reused. Its generic kernel and truncation lemmas have different hypotheses, and the children were proved without them. All seven child types elaborate in the exact comparator scope and pass the comparator's statement validator, and a comparator dry run generates the expected challenge and solution modules. All children have machine-checked Lean proofs using only propext, Classical.choice and Quot.sound. The selected frozen type compiles from the seven children plus the byte-identical uncle types, with no other sorry.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: https://github.com/ZhengyangZhang06/gmt-formalize/pull/1509

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
