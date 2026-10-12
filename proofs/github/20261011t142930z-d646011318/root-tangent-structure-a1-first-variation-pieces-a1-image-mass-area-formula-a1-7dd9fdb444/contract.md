<!-- theorem-id: gmt-ch04/root.tangent_structure-a1.first_variation_pieces-a1.image_mass_area_formula-a1 -->

## Theorem `Submission.ts_fv_image_mass_area_formula`

Let n ≥ 1, ℓ ≥ 0, E = ℝ^{n+ℓ} with standard orthonormal basis e_i = EuclideanSpace.single i 1 (i ∈ Fin (n+ℓ)), a = (M, θ) an admissible pair, V = v(M, θ), T_x = V.tangentSpace x and p_x = T_x.starProjection. Assume: N₀ ⊆ E is Borel with Hⁿ(N₀) = 0; (C_i, F_i)_{i∈ℕ} are Lipschitz pieces (C_i ⊆ ℝⁿ compact, F_i: ℝⁿ → E Lipschitz, differentiable at each w ∈ C_i with injective DF_i(w), DF_i continuous on C_i, c_i|v − w| ≤ |F_i(v) − F_i(w)| on C_i with c_i > 0) with M ⊆ N₀ ∪ ⋃_i F_i(C_i); and for Hⁿ-a.e. x ∈ M, T_x = DF_i(w)(ℝⁿ) for every i and every w ∈ C_i with F_i(w) = x. Let f: E → E be injective, Lipschitz and differentiable at every point, and K ⊆ E Borel. Then imageMass a f K = ∫⁻_{f(M∩K)} θ(f⁻¹(y)) dHⁿ(y) equals ∫⁻_{M∩K} θ(x)·jac(Df(x), T_x) dHⁿ(x), where for Λ ∈ L(E, E) and a subspace P with orthogonal projection p (q = I − p), jac(Λ, P) := (det[⟨Λpe_i, Λpe_j⟩ + ⟨qe_i, qe_j⟩]_{i,j})^{1/2}, which is the tangential Jacobian J^P(Λ) = normDet(Λ|_P) of Λ along P.

Node: `root.tangent_structure-a1.first_variation_pieces-a1.image_mass_area_formula-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/299

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1220, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1221, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1225

## Lean problem

Declaration: `Submission.ts_fv_image_mass_area_formula`

```lean
∀ (n ℓ : ℕ) (a : RectifiablePair n ℓ) (N₀ : Set (Ambient n ℓ)) (C : ℕ → Set (EuclideanSpace ℝ (Fin n))) (F : ℕ → EuclideanSpace ℝ (Fin n) → Ambient n ℓ) (f : Ambient n ℓ → Ambient n ℓ) (K : Set (Ambient n ℓ)), 0 < n → MeasurableSet N₀ → (μHE[n] : Measure (Ambient n ℓ)) N₀ = 0 → a.M ⊆ N₀ ∪ ⋃ i, F i '' C i → (∀ i, IsCompact (C i) ∧ (∃ K : NNReal, LipschitzWith K (F i)) ∧ (∀ w ∈ C i, DifferentiableAt ℝ (F i) w ∧ Function.Injective (fderiv ℝ (F i) w)) ∧ ContinuousOn (fderiv ℝ (F i)) (C i) ∧ ∃ c : ℝ, 0 < c ∧ ∀ v ∈ C i, ∀ w ∈ C i, c * ‖v - w‖ ≤ ‖F i v - F i w‖) → (∀ᵐ x ∂(μHE[n] : Measure (Ambient n ℓ)).restrict a.M, ∀ i, ∀ w ∈ C i, F i w = x → (mk a).tangentSpace x = LinearMap.range (fderiv ℝ (F i) w).toLinearMap) → Function.Injective f → (∃ L : NNReal, LipschitzWith L f) → (∀ y, DifferentiableAt ℝ f y) → MeasurableSet K → imageMass a f K = ∫⁻ x in a.M ∩ K, ENNReal.ofReal (a.θ x * Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (n + ℓ) ↦ inner ℝ (fderiv ℝ f x (((mk a).tangentSpace x).starProjection (EuclideanSpace.single i (1 : ℝ)))) (fderiv ℝ f x (((mk a).tangentSpace x).starProjection (EuclideanSpace.single j (1 : ℝ)))) + inner ℝ (EuclideanSpace.single i (1 : ℝ) - ((mk a).tangentSpace x).starProjection (EuclideanSpace.single i (1 : ℝ))) (EuclideanSpace.single j (1 : ℝ) - ((mk a).tangentSpace x).starProjection (EuclideanSpace.single j (1 : ℝ)))))) ∂μHE[n]
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

- Parent DAG node: `root.tangent_structure-a1.first_variation_pieces-a1`
- Child DAG node: `root.tangent_structure-a1.first_variation_pieces-a1.image_mass_area_formula-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the parent proof, step 2 ("Area formula on M", Simon Ch. 4, 1.5–1.6 and 2.2, with the area formula of Ch. 3 §2, 2.4–2.5), applied to a single injective Lipschitz map f in place of φ_t, together with the identity J^P(Λ)² = det S_P(Λ) from the parent's conventions. No errata apply.

Notation. E := Ambient n ℓ, N := n + ℓ, e_i := EuclideanSpace.single i 1 (i ∈ Fin N), the standard orthonormal basis of E; ℝⁿ := EuclideanSpace ℝ (Fin n) with Lebesgue measure Lⁿ (volume); Hⁿ := μHE[n]. a = (M, θ) is an admissible pair (IsRectifiablePair: M is Hⁿ-null-measurable, θ > 0 on M); V := mk a, T_x := V.tangentSpace x. For a linear subspace P ⊆ E let p_P := P.starProjection (orthogonal projection onto P: self-adjoint, idempotent, identity on P, zero on P^⊥) and q_P := I − p_P (orthogonal projection onto P^⊥). For Λ ∈ L(E, E) put
S_P(Λ) := [⟨Λp_Pe_i, Λp_Pe_j⟩ + ⟨q_Pe_i, q_Pe_j⟩]_{i,j ∈ Fin N}, jac(Λ, P) := (det S_P(Λ))^{1/2} (Real.sqrt),
so the right-hand side of the claim is ∫⁻_{M∩K} ofReal(θ(x)·jac(Df(x), T_x)) dHⁿ(x). Let J^P(Λ) := normDet(Λ|_P) ≥ 0, where Λ|_P := Λ ∘ ι_P : P → E (LinearMap.domRestrict) and normDet is Mathlib's LinearMap.normDet. For a map G: ℝⁿ → E, JG(v) := normDet(fderiv ℝ G v) (SimonGMT Chapter02.areaJacobianAt). L denotes a Lipschitz constant of f, L_i one of F_i.

0. The tangential Jacobian: jac(Λ, P) = J^P(Λ) for every subspace P and every Λ ∈ L(E, E).
Let k := dim P and β(u, v) := ⟨Λp_Pu, Λp_Pv⟩ + ⟨q_Pu, q_Pv⟩, a bilinear form on E whose matrix in the basis (e_i) is S_P(Λ). Choose an orthonormal basis u_1, …, u_k of P and an orthonormal basis u_{k+1}, …, u_N of P^⊥; together they form an orthonormal basis of E. In this basis the matrix S^u := [β(u_a, u_b)]_{a,b} is block diagonal: for a, b ≤ k, β(u_a, u_b) = ⟨Λu_a, Λu_b⟩ (p_P = I and q_P = 0 on P); for a, b > k, β(u_a, u_b) = ⟨u_a, u_b⟩ = δ_{ab} (p_P = 0 and q_P = I on P^⊥); for a ≤ k < b or b ≤ k < a, β(u_a, u_b) = 0 (in each of the two summands one argument is killed). Hence det S^u = det[⟨Λu_a, Λu_b⟩]_{a,b≤k} = J^P(Λ)², by LinearMap.normDet_sq_eq_det_gram applied to Λ|_P and the orthonormal basis (u_a)_{a≤k} of P (for k = 0 both sides are 1: the empty determinant, and LinearMap.normDet_of_subsingleton). Let O := [⟨e_i, u_a⟩]_{i,a}, an orthogonal matrix since both bases are orthonormal. From e_i = Σ_a ⟨e_i, u_a⟩u_a and bilinearity, S_P(Λ) = O S^u Oᵀ, so det S_P(Λ) = (det O)² det S^u = det S^u = J^P(Λ)². (Equivalently: S_P(Λ) and S^u are the matrices, in the orthonormal bases (e_i) and (u_a), of the operator p_PΛ*Λp_P + q_P, and the determinant of an operator does not depend on the basis, LinearMap.det_toMatrix.) Since J^P(Λ) ≥ 0, jac(Λ, P) = (J^P(Λ)²)^{1/2} = J^P(Λ).

1. Properties of f.
(a) f is injective, so Function.invFun f (f x) = x for all x (Function.leftInverse_invFun). Put u(y) := ofReal(θ(invFun f y)); then imageMass a f K = ∫⁻_{f(M∩K)} u dHⁿ and u(f(x)) = ofReal(θ(x)) for every x.
(b) For every Z ⊆ E, Hⁿ(f(Z)) ≤ L^n·Hⁿ(Z) (SimonGMT Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn with A := Z); in particular f maps Hⁿ-null sets to Hⁿ-null sets.
(c) f is continuous and injective and E is Polish, so f maps Borel sets to Borel sets (MeasurableSet.image_of_continuousOn_injOn).
(d) If Z ⊆ E is Hⁿ-null-measurable, there is a Borel Z₀ ⊆ Z with Hⁿ(Z ∖ Z₀) = 0 (NullMeasurableSet.exists_measurable_subset_ae_eq); then f(Z) = f(Z₀) ∪ f(Z ∖ Z₀) is a Borel set (c) union an Hⁿ-null set (b), hence Hⁿ-null-measurable.

2. Decomposition. For i ∈ ℕ let D_i := F_i(C_i) ∖ (N₀ ∪ ⋃_{j<i} F_j(C_j)). Each F_j(C_j) is compact (continuous image of the compact C_j), hence closed and Borel, and N₀ is Borel, so D_i is Borel. The D_i are pairwise disjoint (for j < i, D_i ∩ F_j(C_j) = ∅ and D_j ⊆ F_j(C_j)) and disjoint from N₀. Let M_i := M ∩ K ∩ D_i; these sets are Hⁿ-null-measurable (M is, K and D_i are Borel), pairwise disjoint and contained in M ∩ K. If x ∈ (M ∩ K) ∖ N₀, then x ∈ F_i(C_i) for some i by the covering hypothesis, and for the least such i, x ∈ D_i; hence M ∩ K = (M ∩ K ∩ N₀) ∪ ⋃_i M_i with Hⁿ(M ∩ K ∩ N₀) ≤ Hⁿ(N₀) = 0. Since f is injective, f(M ∩ K) = f(M ∩ K ∩ N₀) ∪ ⋃_i f(M_i), the sets f(M_i) are pairwise disjoint and Hⁿ-null-measurable (1(d)), and Hⁿ(f(M ∩ K ∩ N₀)) = 0 (1(b)). Set-lintegrals over sets that differ by an Hⁿ-null set coincide (setLIntegral_congr), and the lintegral over a countable union of pairwise disjoint null-measurable sets is the sum of the lintegrals (lintegral_iUnion₀). Therefore
imageMass a f K = Σ_i ∫⁻_{f(M_i)} u dHⁿ and ∫⁻_{M∩K} ofReal(θ(x)·jac(Df(x), T_x)) dHⁿ = Σ_i ∫⁻_{M_i} ofReal(θ(x)·jac(Df(x), T_x)) dHⁿ,
and it suffices to prove, for every i,
(†) ∫⁻_{f(M_i)} u dHⁿ = ∫⁻_{M_i} ofReal(θ(x)·jac(Df(x), T_x)) dHⁿ(x).

3. The area formula on one piece. Fix i.
(a) Since M_i is Hⁿ-null-measurable there is a Borel A' ⊇ M_i with Hⁿ(A' ∖ M_i) = 0 (NullMeasurableSet.exists_measurable_superset_ae_eq); put A := A' ∩ D_i. Then A is Borel, M_i ⊆ A ⊆ D_i ⊆ F_i(C_i), and Hⁿ(A ∖ M_i) = 0.
(b) F_i is injective on C_i: if v, w ∈ C_i and F_i v = F_i w then c_i‖v − w‖ ≤ 0 with c_i > 0, so v = w. Let ψ_i := Function.invFunOn F_i C_i; then ψ_i(F_i v) = v for v ∈ C_i, and ψ_i(y) ∈ C_i, F_i(ψ_i y) = y for y ∈ F_i(C_i). Let B := C_i ∩ F_i⁻¹(A). B is Borel (C_i is compact hence closed, F_i is continuous), F_i(B) = A (because A ⊆ F_i(C_i)), and F_i is injective on B.
(c) G := f ∘ F_i is Lipschitz (constant L·L_i) and injective on B (f is injective). For v ∈ B ⊆ C_i, F_i is differentiable at v and f is differentiable at F_i(v), so fderiv ℝ G v = Df(F_i v) ∘ DF_i(v) (fderiv_comp). By LinearMap.normDet_comp, normDet(Λ ∘ A₀) = normDet(Λ restricted to range A₀)·normDet(A₀); hence, with T_i(v) := range DF_i(v),
JG(v) = J^{T_i(v)}(Df(F_i v))·JF_i(v), both factors ≥ 0.
(d) Define h: E → [0, ∞] by h(y) := ofReal(J^{T_i(ψ_i y)}(Df(y)))·ofReal(θ(y)) if y ∈ F_i(C_i), and h(y) := 0 otherwise. For v ∈ B we have F_i v ∈ F_i(C_i), ψ_i(F_i v) = v and u(G v) = ofReal(θ(F_i v)) (1(a)); since ofReal(αβ) = ofReal(α)·ofReal(β) for α ≥ 0,
ofReal(JG(v))·u(G v) = ofReal(JF_i(v))·h(F_i v).
(e) The weighted area formula for injective Lipschitz maps (SimonGMT Chapter02.weighted_area_formula_lipschitz_injOn, for any weight g: E → [0, ∞], measurable or not; here μHE[finrank ℝ ℝⁿ] = μHE[n] by finrank_euclideanSpace_fin), applied to G on B with weight u and to F_i on B with weight h, gives
∫⁻_{f(A)} u dHⁿ = ∫⁻_{G(B)} u dHⁿ = ∫⁻_B ofReal(JG(v))·u(G v) dLⁿ(v) = ∫⁻_B ofReal(JF_i(v))·h(F_i v) dLⁿ(v) = ∫⁻_{F_i(B)} h dHⁿ = ∫⁻_A h dHⁿ,
using G(B) = f(F_i(B)) = f(A) and (d).

4. From A back to M_i.
(a) Hⁿ(A ∖ M_i) = 0 and M_i ⊆ A give ∫⁻_A h dHⁿ = ∫⁻_{M_i} h dHⁿ. Also f(M_i) ⊆ f(A) ⊆ f(M_i) ∪ f(A ∖ M_i) and Hⁿ(f(A ∖ M_i)) = 0 (1(b)), so ∫⁻_{f(A)} u dHⁿ = ∫⁻_{f(M_i)} u dHⁿ.
(b) The tangent hypothesis holds for Hⁿ⌞M-a.e. x, hence for Hⁿ⌞M_i-a.e. x since M_i ⊆ M (ae_restrict_of_ae_restrict_of_subset). For such x ∈ M_i: x ∈ D_i ⊆ F_i(C_i), so w := ψ_i(x) ∈ C_i and F_i(w) = x, and the hypothesis gives T_x = range DF_i(w) = T_i(ψ_i x). Hence, by step 0 and since J ≥ 0,
h(x) = ofReal(J^{T_x}(Df(x)))·ofReal(θ(x)) = ofReal(θ(x)·J^{T_x}(Df(x))) = ofReal(θ(x)·jac(Df(x), T_x)).
Thus h = ofReal(θ·jac(Df, T)) Hⁿ⌞M_i-a.e., and ∫⁻_{M_i} h dHⁿ = ∫⁻_{M_i} ofReal(θ(x)·jac(Df(x), T_x)) dHⁿ(x) (lintegral_congr_ae).
(c) Combining 3(e), 4(a) and 4(b): ∫⁻_{f(M_i)} u dHⁿ = ∫⁻_{f(A)} u dHⁿ = ∫⁻_A h dHⁿ = ∫⁻_{M_i} h dHⁿ = ∫⁻_{M_i} ofReal(θ·jac(Df, T)) dHⁿ, which is (†).

5. Conclusion. Summing (†) over i ∈ ℕ and using step 2,
imageMass a f K = Σ_i ∫⁻_{f(M_i)} u dHⁿ = Σ_i ∫⁻_{M_i} ofReal(θ·jac(Df, T)) dHⁿ = ∫⁻_{M∩K} ofReal(θ(x)·jac(Df(x), T_x)) dHⁿ(x).
By definition jac(Df(x), T_x) = Real.sqrt (Matrix.det (Matrix.of fun i j ↦ ⟨Df(x)(p_{T_x}e_i), Df(x)(p_{T_x}e_j)⟩ + ⟨e_i − p_{T_x}e_i, e_j − p_{T_x}e_j⟩)) with p_{T_x} = ((mk a).tangentSpace x).starProjection, which is exactly the integrand of the claim. ∎

## Key steps

1. jac(Λ, P) = normDet(Λ|_P): the bilinear form ⟨Λpu, Λpv⟩ + ⟨qu, qv⟩ is block diagonal (Gram of Λ on P, identity on P^⊥) in an orthonormal basis adapted to P ⊕ P^⊥; use normDet_sq_eq_det_gram and basis invariance of the determinant
2. f is injective and Lipschitz, so invFun f ∘ f = id and f maps Borel sets to Borel sets, Hⁿ-null sets to null sets and null-measurable sets to null-measurable sets
3. Disjointify the cover: M ∩ K = (M ∩ K ∩ N₀) ∪ ⋃ M_i with M_i := M ∩ K ∩ D_i; both sides split into sums over i by lintegral_iUnion₀
4. On one piece: Borel A ⊇ M_i in D_i, B := C_i ∩ F_i⁻¹(A); the weighted area formula for f∘F_i and for F_i together with normDet_comp gives ∫⁻_{f(A)} u = ∫⁻_A h
5. Remove the null sets A ∖ M_i and f(A ∖ M_i) and identify h = ofReal(θ·jac(Df, T)) a.e. on M_i using the tangent hypothesis; then sum over i

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `sha256sum GMT/Ch04/Contract.lean GMT/Ch04/Submission.lean <snapshot>/project/GMT/Ch04/Contract.lean`
- `git -C .lake/packages/simongmt rev-parse HEAD`
- `git show 2cce809724fc09db16dc21873e5f9cd1ee6e2dfa:GMT/Ch04/Submission.lean | grep -n '^import\|^theorem'`
- `lake env lean GMT/Ch04/Submission.lean -o /tmp/ch04-fvp/olean/GMT/Ch04/Submission.olean`
- `lean /tmp/ch04-fvp/T0.lean (#check Matrix.det, Matrix.of, Matrix.gram, EuclideanSpace.single, LinearMap.trace, Submodule.starProjection, LinearMap.normDet, ContinuousLinearMap.adjoint in the frozen scope)`
- `grep -n 'theorem\|lemma\|def' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `grep -rn 'weighted_area_formula_lipschitz_injOn|euclideanHausdorffMeasure_image_le_of_lipschitzOn|def areaJacobianAt|continuous_normDet|measurable_areaJacobianAt' .lake/packages/simongmt/Poincare/SimonGMT`
- `grep -rn 'MeasurableSet.image_of_continuousOn_injOn|integral_withDensity_eq_integral_toReal_smul₀|restrict_withDensity|hasDerivAt_integral_of_dominated_loc_of_deriv_le|ContDiffAt.isSymmSndFDerivAt|inverse_continuousAt|lipschitzWith_of_nnnorm_fderiv_le|trace_eq_sum_inner|HasDerivAt.finsetProd|HasDerivAt.inner|HasDerivAt.sqrt|det_eq_prod_eigenvalues|lintegral_iUnion₀|ofReal_integral_eq_lintegral_ofReal|setIntegral_eq_integral_of_forall_compl_eq_zero|exists_measurable_superset_ae_eq|det_apply|fderiv_comp' .lake/packages/mathlib/Mathlib`
- `grep -rn 'continuous_matrix|Continuous.matrix_det|def coeLM|LinearMap.continuous_of_finiteDimensional|Continuous.clm_apply|Continuous.inner' .lake/packages/mathlib/Mathlib`
- `grep -n '^theorem\|^def' .lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DeformationFamily.lean .lake/packages/simongmt/Poincare/SimonGMT/Chapter08/JacobianBounds.lean`
- `python3 -I /tmp/ch04-fvp/scripts/gen.py (verifier gmt-compare.child_modules + lean_contract.validate_lean_statement); lean /tmp/ch04-fvp/gen/Challenge_*.lean`
- `lean /tmp/ch04-fvp/WithImports.lean (child types with the implementation imports added)`
- `lean /tmp/ch04-fvp/Assembly.lean (parent with its frozen type proved from the four sorry'd children)`
- `python3 scan of dag.json for lean_name collisions (ts_fv_*) and for nodes mentioning IsCompactVariation/imageMass`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/project/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-first-variation-pieces-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/DeformationFamily.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/JacobianBounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/InnerProductSpace/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/Normed/Ring/Units.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Topology/Instances/Matrix.lean`
- `/tmp/ch04-fvp/Assembly.lean`
- `/tmp/ch04-fvp/WithImports.lean`
- `/tmp/ch04-fvp/gen/Challenge_ts_fv_compact_variation_bounds.lean`
- `/tmp/ch04-fvp/gen/Challenge_ts_fv_image_mass_area_formula.lean`
- `/tmp/ch04-fvp/gen/Challenge_ts_fv_tangential_jacobian_hasDerivAt.lean`
- `/tmp/ch04-fvp/gen/Challenge_ts_fv_hasDerivAt_of_weighted_jacobian.lean`

Contract and pinned state:
- The snapshot contract (sha256 6e58e5dd…0f4770b) is byte-identical to the workspace Contract.lean and Submission.lean, and to the proof-base Submission at 2cce8097.
- SimonGMT is at the pinned revision 2b366308; Mathlib is at 25730c7c.

What child types can mention:
- In the frozen scope (`import GMT.Ch04.Submission` plus the contract opens), Matrix.det, Matrix.of, EuclideanSpace.single, LinearMap.trace and Submodule.starProjection are available.
- LinearMap.normDet, ContinuousLinearMap.adjoint and Matrix.gram are unknown constants. So no child type mentions normDet or adjoints: the tangential Jacobian is written as √det of the standard-basis matrix [⟪Λpe_i, Λpe_j⟫ + ⟪qe_i, qe_j⟫].

Cited results, each found with the stated meaning:
- SimonGMT Chapter02:
  - weighted_area_formula_lipschitz_injOn (global LipschitzWith, MeasurableSet source, InjOn, arbitrary non-measurable weight; target measure μHE[finrank]);
  - euclideanHausdorffMeasure_image_le_of_lipschitzOn (μHE[n](f '' A) ≤ K^n μHE[n] A);
  - areaJacobianAt = normDet ∘ fderiv.
- SimonGMT Chapter08.Varifold.hasDerivAt_familySpatialDerivative, with familySpatialDerivative_eq_fderiv and initialVelocity_eq_deriv. This gives ∂_t Dφ_t|_{t=0} = DX directly; the reviewer compiled it.
- Mathlib:
  - normDet: LinearMap.normDet_sq_eq_det_gram, LinearMap.normDet_comp;
  - measure theory: MeasurableSet.image_of_continuousOn_injOn, NullMeasurableSet.exists_measurable_superset_ae_eq / exists_measurable_subset_ae_eq, lintegral_iUnion₀, restrict_withDensity, integral_withDensity_eq_integral_toReal_smul₀ (no integrability of g needed), ofReal_integral_eq_lintegral_ofReal, setIntegral_eq_integral_of_forall_compl_eq_zero;
  - calculus: hasDerivAt_integral_of_dominated_loc_of_deriv_le, ContDiffAt.isSymmSndFDerivAt (minSmoothness ℝ 2 ≤ n), lipschitzWith_of_nnnorm_fderiv_le, HasDerivAt.inner, HasDerivAt.finsetProd (finset_prod is deprecated), HasDerivAt.sqrt;
  - algebra: NormedRing.inverse_continuousAt, LinearMap.trace_eq_sum_inner, Matrix.det_apply, Matrix.IsHermitian.det_eq_prod_eigenvalues;
  - continuity used by the assembly: continuous_matrix, Continuous.matrix_det, ContinuousLinearMap.coeLM, LinearMap.continuous_of_finiteDimensional.

Elaboration and assembly:
- All four child types pass validate_lean_statement.
- They compile as comparator-generated NodeChallenge files, with only the sorry warning.
- They still elaborate when the implementation imports are added.
- Assembly.lean proves Submission.ts_first_variation_of_pieces with exactly the frozen type from the four sorry'd children; the only diagnostics are the four child sorry warnings.

Name collisions: none.
- No ts_fv_* name appears in dag.json or in the pinned packages.
- The accepted compactVariation_velocity_isTestField in another branch overlaps only parts (a) and (b) of child A, under a different name and type, and it is not in this node's proof base.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: https://github.com/ZhengyangZhang06/gmt-formalize/pull/1870

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
