<!-- theorem-id: gmt-ch04/root -->

## Theorem `GMT.Ch04.main_theorem`

# Simon GMT, Chapter 4: Rectifiable n-Varifolds

Prove `GMT.Ch04.main_theorem`, stated in the frozen contract `GMT/Ch04/Contract.lean`, by completing `GMT/Ch04/Submission.lean` (initially a byte copy of the contract). The statement is the conjunction of the chapter's headline results; `GMT/Ch04/README.md` maps each conjunct to the book.

Source: Leon Simon, *Introduction to Geometric Measure Theory* (2014), Chapter 4, printed pages 85–102. Read-only copies for workers: `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt` and `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/simon-gmt.pdf` (printed page = PDF page − 7).

The pinned `simongmt` package (`Poincare.SimonGMT.*`) contains an earlier kernel-checked partial formalization of the book; its proofs may be reused as library lemmas where they apply. Do not rely on its definitions that the chapter README marks as unfaithful. Toolchain Lean v4.35.0-rc3, Mathlib 25730c7c. Every definition used by the statement must stay byte-identical; only standard axioms are allowed.

Node: `root`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5

Parent: None (root)

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/54, https://github.com/ZhengyangZhang06/gmt-formalize/issues/55, https://github.com/ZhengyangZhang06/gmt-formalize/issues/56, https://github.com/ZhengyangZhang06/gmt-formalize/issues/57, https://github.com/ZhengyangZhang06/gmt-formalize/issues/58, https://github.com/ZhengyangZhang06/gmt-formalize/issues/59, https://github.com/ZhengyangZhang06/gmt-formalize/issues/60, https://github.com/ZhengyangZhang06/gmt-formalize/issues/61, https://github.com/ZhengyangZhang06/gmt-formalize/issues/62, https://github.com/ZhengyangZhang06/gmt-formalize/issues/63, https://github.com/ZhengyangZhang06/gmt-formalize/issues/64, https://github.com/ZhengyangZhang06/gmt-formalize/issues/65

## Lean problem

Declaration: `GMT.Ch04.main_theorem`

```lean
ApproxTangentAE ∧ FirstVariationFormula ∧ StationaryIffVariational ∧ StationaryMonotonicity ∧ StationaryDensity ∧ CanonicalRepresentative ∧ BoundedCurvatureMonotonicity ∧ LogarithmicMonotonicityError ∧ LpMonotonicity ∧ LpDensity ∧ LpSupportRepresentation ∧ PoincareInequality ∧ SobolevInequality ∧ SupportInBall ∧ ConvexHullProperty ∧ ClassicalTangent
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

<!-- theorem-id: gmt-ch04/root -->

# Final proof of `GMT.Ch04.main_theorem` (Simon, *Introduction to GMT*, Chapter 4)

| | |
| --- | --- |
| Node | `root` of run `20261011T142930Z-d646011318`; issue https://github.com/ZhengyangZhang06/gmt-formalize/issues/5 |
| Declaration | `GMT.Ch04.main_theorem` in `GMT/Ch04/Submission.lean` |
| Frozen problem | `GMT/Ch04/Contract.lean` at `ff75f52a4c9deb3b3abbd91eb31d7b02e29a4cef`, sha256 `6e58e5dd…0f4770b` (unchanged; byte-identical in the candidate) |
| Lean candidate | commit `73ff32799dea2666383f7ed85957fc270afb3351`; `GMT/Ch04/Submission.lean` sha256 `0c7c9e70d89068b988578764887632c17d769ebc39d25d654fc3ff98ec3146d0` |
| Toolchain and libraries | Lean `v4.35.0-rc3`; Mathlib `25730c7c759d108ef87ab70af2342a196760f79d`; `simongmt` (`Poincare.SimonGMT.*`) `2b3663083f3fe399b6296fb8eaee52169170e197` |
| Axioms of `main_theorem` | `propext`, `Classical.choice`, `Quot.sound` only |
| Mathematical source | L. Simon, *Introduction to Geometric Measure Theory* (2014 Tsinghua notes), Ch. 4, printed pp. 85–102, with the Ch. 1–3 results it relies on |

## 0. Summary

`main_theorem` has no hypotheses. Its type is the conjunction of sixteen closed propositions, one
for each headline result of Chapter 4 (§1). The Lean proof (§2) introduces the conjunction from
twelve accepted child theorems, the "section theorems" of the accepted decomposition.

- One of them, `Submission.tangent_structure_first_variation`, has no hypotheses. It proves three
  facts: `ApproxTangentAE` (1.3), the structural facts (GF) about every rectifiable `n`-varifold
  (§2.1), and `FirstVariationFormula` (2.2).
- Eight of the others are stated *conditionally*: on (GF), and also on `ApproxTangentAE` where the
  printed proof uses a representative `(M, θ)`, and on `FirstVariationFormula` for 2.4. The root
  supplies these antecedents from the output of `tangent_structure_first_variation`, so **no
  assumption remains**.
- The remaining three children (`rectifiable_lipschitz_piece_cover`, `radial_first_variation`,
  `weighted_monotonicity_identity`) do not occur in the root proof term; they are used by
  siblings.

All 121 accepted declarations of the run lie in the transitive dependency closure of
`main_theorem`, and every DAG child is used by its parent, directly or through a sibling (§4.1).

Section 3 records how each child proves its conjuncts *as formalized*, naming the sub-lemmas
and the library declarations that the elaborated proofs actually reference, with their pinned
provenance. Several library results cited in the reviewed child prose are **not** what the Lean
proofs use; §4.3 lists these differences. Section 4 also gives the dependency graph and shows
that there is no circularity. Section 6 describes the only change made while implementing the
root: a repair of the file produced by overlaying the twelve accepted child branches.
Sections 5, 7, 8 and 9 cover history, verification, the local-reference search and citations.
Appendix A lists all 121 accepted declarations with their issues, PRs and actual dependencies.

## 1. The statement

`GMT/Ch04/Contract.lean` (frozen) builds rectifiable `n`-varifolds exactly as on Simon p. 85:
`V = v(M, θ)` is the class of an admissible pair (`M` countably `n`-rectifiable in the sense of
SimonGMT `Chapter03.CountablyRectifiable`, `Hⁿ`-measurable, `θ > 0` on `M`, `θ` locally
`Hⁿ`-integrable on `M`) under `Hⁿ`-null modification. Its weight `μ_V = Hⁿ ⌞ θ` is well defined
by the proved contract lemma `pairWeight_eq_of_equiv`. Every other notion is defined from `μ_V`:
- `T_xV` is the approximate tangent space where it exists, with a free multiplicity `c > 0`, and
  `⊥` elsewhere;
- `div_M X = trace(DX ∘ p_{T_xV})` and `∇^M h = p_{T_xV}(∇h)`;
- `Θⁿ(μ_V, ξ)` is the `limUnder` of `μ_V(B_ρ(ξ))/(ωₙρⁿ)` along `ρ ↓ 0`;
- `spt V = spt μ_V`;
- stationarity and generalized mean curvature are stated with Bochner integrals against `μ_V`.

Conventions: `B_ρ(ξ) = closedBall ξ ρ`, `Hⁿ = μHE[n]`, and `ωₙ = omega n`, the Lebesgue measure
of the unit ball of `ℝⁿ`. Every proposition assumes `0 < n`.

The frozen statement is

```lean
theorem main_theorem : ApproxTangentAE ∧ FirstVariationFormula ∧ StationaryIffVariational ∧
  StationaryMonotonicity ∧ StationaryDensity ∧ CanonicalRepresentative ∧
  BoundedCurvatureMonotonicity ∧ LogarithmicMonotonicityError ∧ LpMonotonicity ∧ LpDensity ∧
  LpSupportRepresentation ∧ PoincareInequality ∧ SobolevInequality ∧ SupportInBall ∧
  ConvexHullProperty ∧ ClassicalTangent
```

| # | Proposition | Simon, Ch. 4 |
| --- | --- | --- |
| 1 | `ApproxTangentAE` | 1.3 with Ch. 3, 1.8(2), 1.9 (pp. 75, 86) |
| 2 | `FirstVariationFormula` | 2.2 (p. 88) |
| 3 | `StationaryIffVariational` | 2.4 (p. 88) |
| 4 | `StationaryMonotonicity` | 3.6, 3.8, 3.10 (pp. 90–91) |
| 5 | `StationaryDensity` | 3.9, 3.11 (p. 91) |
| 6 | `CanonicalRepresentative` | 3.12, 3.13 (p. 91) |
| 7 | `BoundedCurvatureMonotonicity` | 3.17 and the remark after it (pp. 92–93) |
| 8 | `LogarithmicMonotonicityError` | 3.18 (p. 93) |
| 9 | `LpMonotonicity` | 4.2, 4.5, 4.7, 4.8 (pp. 93–94) |
| 10 | `LpDensity` | 4.9 (p. 95) |
| 11 | `LpSupportRepresentation` | 4.10(1) (p. 95) |
| 12 | `PoincareInequality` | 5.6 (p. 97) |
| 13 | `SobolevInequality` | 5.7, 5.9 (pp. 98–100) |
| 14 | `SupportInBall` | 6.1 (p. 100) |
| 15 | `ConvexHullProperty` | 6.2 (p. 101) |
| 16 | `ClassicalTangent` | 6.3 (p. 101) |

**Corrections built into the frozen statement.** The proof neither adds to nor removes from these
(see `GMT/Ch04/README.md`, "Errata and corrections"):
- the constant of 4.2 is `κ = (p − n)/(4p)`, not the printed `p/(4(p − n))`;
- 5.7 assumes `n ≥ 2`, which the exponent `n/(n − 1)` requires;
- 6.3 uses `dist(y − x, T_xV)`, because `T_xV` is a linear subspace;
- the remark after 3.17 is stated on `U`; the printed "`N ∩ U`" is a typo.

**No universe parameters.** All objects live in `Type` (`Ambient n ℓ` is
`EuclideanSpace ℝ (Fin (n + ℓ))`), and the sixteen propositions quantify only over `ℕ` and over
such types. Hence `main_theorem` has no universe parameters, and no universe bookkeeping is
needed in the root step. This was checked with `set_option pp.universes true` (§7).

## 2. The root proof (the actual Lean argument)

### 2.1 The interface (GF)

Write (GF) for the proposition

```lean
∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ), 0 < n →
  IsFiniteMeasureOnCompacts V.weight ∧
  (∀ᵐ x ∂V.weight, Module.finrank ℝ (V.tangentSpace x) = n) ∧
  AEStronglyMeasurable (fun x ↦ (V.tangentSpace x).starProjection) V.weight
```

For every rectifiable `n`-varifold `V` it says:
- (FV1) `μ_V` is finite on compact sets;
- (FV2) `T_xV` is `n`-dimensional for `μ_V`-a.e. `x`;
- (FV3) `x ↦ p_{T_xV}` is `μ_V`-a.e. strongly measurable.

**Why (GF) is needed.** The contract states stationarity, mean curvature and the monotonicity
quantities with Bochner integrals of functions built from `p_{T_xV}`. Lean's Bochner integral of a
function that is not integrable is `0`, so without (FV1)–(FV3) these integrals would not carry
their intended meaning. (GF) is the Chapter 3 structure theory that makes them meaningful. It is
proved, not assumed: it is the second conjunct of `Submission.tangent_structure_first_variation`
(§3.2).

### 2.2 The proof

```lean
theorem main_theorem : ApproxTangentAE ∧ FirstVariationFormula ∧ … ∧ ClassicalTangent := by
  -- §1–§2: `T_x V` exists a.e. (1.3, Ch. 3 1.9); (GF); the first variation formula (2.2).
  obtain ⟨hTangent, hStruct, hFirstVar⟩ := Submission.tangent_structure_first_variation
  -- §3: stationary monotonicity and density (3.6–3.11).
  obtain ⟨hStatMono, hStatDensity⟩ := Submission.stationary_monotonicity_density hStruct
  -- 3.12–3.13 and 4.10(1): the canonical representatives.
  obtain ⟨hCanonical, hLpSupport⟩ := Submission.canonical_representatives hTangent hStruct
  -- 3.17, 3.18 and §4: monotonicity in the presence of mean curvature.
  obtain ⟨hBounded, hLog, hLpMono, hLpDensity⟩ := Submission.mean_curvature_monotonicity hStruct
  -- 6.1 and 6.2.
  obtain ⟨hBall, hHull⟩ := Submission.support_in_ball_convex_hull hStruct
  -- 2.4, 5.6, 5.7/5.9 and 6.3.
  exact ⟨hTangent, hFirstVar,
    Submission.stationary_iff_variational_of_first_variation hStruct hFirstVar,
    hStatMono, hStatDensity, hCanonical, hBounded, hLog, hLpMono, hLpDensity, hLpSupport,
    Submission.poincare_inequality hTangent hStruct, Submission.sobolev_inequality hTangent hStruct,
    hBall, hHull, Submission.classical_tangent hTangent hStruct⟩
```

*Proof.* A conjunction is proved by proving each conjunct, and the anonymous constructor builds
the right-nested `And.intro` from sixteen proof terms. The table gives the proof term of each
conjunct and the accepted child's frozen type, as recorded in the workflow DAG. In it, "AT" is
`ApproxTangentAE`, "GF" is the proposition of §2.1 and "FVF" is `FirstVariationFormula`.

| # | Proof term | Child's frozen type |
| --- | --- | --- |
| 1, 2 | `hTangent`, `hFirstVar` (first and third components) | `tangent_structure_first_variation : AT ∧ GF ∧ FVF` |
| 3 | `stationary_iff_variational_of_first_variation hStruct hFirstVar` | `GF → FVF → StationaryIffVariational` |
| 4, 5 | `hStatMono`, `hStatDensity` | `stationary_monotonicity_density : GF → StationaryMonotonicity ∧ StationaryDensity` |
| 6, 11 | `hCanonical`, `hLpSupport` | `canonical_representatives : AT → GF → CanonicalRepresentative ∧ LpSupportRepresentation` |
| 7–10 | `hBounded`, `hLog`, `hLpMono`, `hLpDensity` | `mean_curvature_monotonicity : GF → BoundedCurvatureMonotonicity ∧ LogarithmicMonotonicityError ∧ LpMonotonicity ∧ LpDensity` |
| 12 | `poincare_inequality hTangent hStruct` | `AT → GF → PoincareInequality` |
| 13 | `sobolev_inequality hTangent hStruct` | `AT → GF → SobolevInequality` |
| 14, 15 | `hBall`, `hHull` | `support_in_ball_convex_hull : GF → SupportInBall ∧ ConvexHullProperty` |
| 16 | `classical_tangent hTangent hStruct` | `AT → GF → ClassicalTangent` |

Each proof term has the required type:
- The antecedent "GF" of every conditional child is syntactically the second component of the
  type of `tangent_structure_first_variation`. Hence `hStruct` is a proof of it.
- `hTangent` proves `ApproxTangentAE` and `hFirstVar` proves `FirstVariationFormula`.
- Each `obtain` destructures a right-nested conjunction whose components are, syntactically,
  the corresponding conjuncts of the frozen statement.

The root uses no hypothesis, no lemma other than the nine children named above, and no tactic
besides `obtain` and `exact`. ∎

So the mathematical content of `main_theorem` is exactly the content of the twelve accepted
children, together with their own accepted sub-lemmas. The next section records it.

## 3. Proofs of the conjuncts, as formalized by the accepted children

Each subsection gives the argument actually implemented in `GMT/Ch04/Submission.lean` at the
candidate commit. The reviewed natural-language proof of each node is in
`proofs/github/20261011t142930z-d646011318/<record>/proof.md` on the branch
`proof-workspace/gmt-ch04/20261011t142930z-d646011318/theorems/solutions/<record>` (Appendix B
lists the records).

**Provenance conventions.**
- `simongmt` locations are relative to `Poincare/SimonGMT/` in the pinned package
  (`lake-packages-25730c7c/simongmt`, `git rev-parse HEAD` = `2b3663083f3fe399b6296fb8eaee52169170e197`).
- Mathlib locations are files of the pinned local snapshot `local-references/12153e28d102be5e/mathlib`.
  Its `git rev-parse HEAD` is `25730c7c759d108ef87ab70af2342a196760f79d`, the same revision as
  the build package `lake-packages-25730c7c/mathlib`.
- A library declaration is called **used** only if it occurs in the elaborated proof term of the
  named declaration. This was checked mechanically on the compiled candidate (§7, item 6). Basic
  algebra, order and type-class lemmas are not listed.
- All of these are **existing pinned upstream declarations, reused, not new helpers**.
  `#print axioms GMT.Ch04.main_theorem` traverses the whole dependency closure, including every
  reused Mathlib and SimonGMT declaration, and reports only `propext`, `Classical.choice` and
  `Quot.sound` (§7).

Notation: `E = ℝ^{n+ℓ}`, `μ = μ_V`, `T_x = T_xV`, `p_x = p_{T_x}`, `r = |x − ξ|`,
`q_ξ(x) = |D^⊥r|² = |p_x^⊥(x − ξ)|²/|x − ξ|²` (with `q_ξ(ξ) = 0`), `w_ξ = q_ξ/rⁿ`,
`a(ρ) = ρ⁻ⁿμ(B_ρ(ξ))` and `Θ = Θⁿ(μ, ·)`.

### 3.1 Lipschitz pieces — `rectifiable_lipschitz_piece_cover`

**Statement.** If `n ≥ 1` and `M ⊆ E` is countably `n`-rectifiable, then there are a Borel
`Hⁿ`-null set `N₀`, compact sets `C_i ⊆ ℝⁿ` and Lipschitz maps `F_i : ℝⁿ → E` with
`M ⊆ N₀ ∪ ⋃_i F_i(C_i)`. Moreover each `F_i` is differentiable at every point of `C_i` with
injective derivative, `DF_i` is continuous on `C_i`, and
`c_i|v − w| ≤ |F_i(v) − F_i(w)|` on `C_i` for some `c_i > 0`.

**Role.** This replaces Simon Ch. 3, Lemma 1.2 together with its use of the `C¹` approximation
theorem (Ch. 2, 1.5). That theorem has no kernel-checked counterpart in the pinned references
(see §4.3 and §8).

**Formal argument.**
1. `injective_fderiv_local_lower_bound`. If `f` is differentiable at `w` with injective `Df(w)`,
   then some `c > 0` gives `c|u| ≤ |f(w + u) − f(w)|` for `|u| ≤ c`. The proof uses the
   anti-Lipschitz bound for injective linear maps on finite-dimensional spaces,
   `LinearMap.exists_antilipschitzWith` (`Analysis/Normed/Module/FiniteDimension.lean:231`),
   and the little-o definition of the derivative.
2. `lower_lipschitz_cover_of_local_bound`. The sets
   `G_k = ⋂_{|u| ≤ r_k} {w : r_k|u| ≤ |f(w + u) − f(w)|}` with `r_k = 1/(k + 1)` are closed. A
   dense sequence `(q_m)` (`TopologicalSpace.exists_dense_seq`, `Topology/Bases.lean:364`) gives
   countably many bounded Borel sets `T_p = R ∩ G_k ∩ B_{r_k/2}(q_m)` that cover `R`, each with a
   uniform lower Lipschitz bound.
3. `regular_set_lower_lipschitz_cover`. Here `R` is the regular set
   `Chapter02.areaRegularSet f` (SimonGMT, `Chapter02/AreaLipschitz.lean:31`), which is Borel by
   `Chapter02.measurableSet_areaRegularSet` (`:34`).
4. `lusin_compact_exhaustion_of_measurable` (Lusin, Simon Ch. 1, 1.17). If `g : ℝⁿ → Y` is Borel
   with `Y` finite-dimensional and `Lⁿ(S) < ∞`, then compact sets `C_j ⊆ S` with `g|C_j`
   continuous exhaust `S` up to an `Lⁿ`-null set. This is proved directly:
   - for each set `U` of a countable basis of `Y`, outer regularity
     (`MeasurableSet.exists_isOpen_sdiff_lt`, `MeasureTheory/Measure/Regular.lean:385`) gives an
     open `O_U ⊇ g⁻¹(U)` with small excess;
   - `g` is continuous on `S` minus the union `B` of the excesses;
   - inner regularity (`MeasurableSet.exists_isCompact_sdiff_lt`, `Regular.lean:843`) gives a
     compact `K ⊆ S ∖ B` of almost full measure.
5. `lipschitz_range_piece_cover` handles one Lipschitz `f`:
   - Lusin is applied to `Df` on each `T_p`; `Df` is Borel by `measurable_fderiv`
     (`Analysis/Calculus/FDeriv/Measurable.lean:378`);
   - the image of the non-regular set is `Hⁿ`-null by SimonGMT
     `Chapter02.area_image_compl_regularSet_eq_zero` (`Chapter02/AreaLipschitz.lean:59`);
   - the image of the Lusin remainders is null by the Lipschitz image bound
     `Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn` (SimonGMT,
     `Chapter02/Lipschitz.lean:216`), together with `Hⁿ = Lⁿ` on `ℝⁿ`
     (`EuclideanSpace.euclideanHausdorffMeasure_eq_volume`,
     `Geometry/Euclidean/Volume/Measure.lean:187`).
6. `rectifiable_lipschitz_piece_cover` applies step 5 to every parametrization in the definition
   of `CountablyRectifiable` (Ch. 3, 1.1) and re-indexes the pieces by `Nat.pair`. The null sets
   are absorbed into a Borel null set by `exists_measurable_superset_of_null`
   (`MeasureTheory/Measure/MeasureSpaceDef.lean:219`).

### 3.2 Tangent structure and the first variation formula — `tangent_structure_first_variation`

**Statement.** `ApproxTangentAE ∧ GF ∧ FirstVariationFormula`, with no hypotheses.

**Part A: approximate tangents, density and (GF)** (Ch. 3, 1.6 ⇒, 1.8, 1.9; Ch. 4, 1.3). Fix a
pair `(M, θ)` and its pieces `(C_i, F_i)` from §3.1.

1. **Area formula on a piece** (`ts_pdb_piece_area_formula`). Let `C` be Borel and `F` Lipschitz
   and injective on `C`, with `DF` continuous on `C`. Then
   `J = √det(⟪DF e_i, DF e_j⟫)` is continuous on `C`, `Hⁿ(DF(v)(S)) = J(v)Lⁿ(S)`, and
   `∫_{F(C)} g dHⁿ = ∫_C J·(g∘F)` for continuous `g`. It is proved in the file itself from Mathlib
   results:
   - The linear case: an injective `A` factors as an isometric embedding after an endomorphism of
     `ℝⁿ` (`Isometry.euclideanHausdorffMeasure_image`, `Geometry/Euclidean/Volume/Measure.lean:131`;
     `Measure.addHaar_image_linearMap`, `MeasureTheory/Measure/Lebesgue/EqHaar.lean:297`). A
     non-injective `A` has Gram determinant `0`.
   - `F` is differentiable `Lⁿ`-a.e. by Rademacher (`LipschitzWith.ae_differentiableAt`,
     `Analysis/Calculus/Rademacher.lean:385`).
   - Sets on which `J = 0` have `Hⁿ`-null image, and on sets of injectivity with `J > 0`,
     `Hⁿ(F(s)) = ∫_s J`. Both are proved by partitioning into countably many Borel pieces on
     which `F` is uniformly close to a fixed linear map
     (`exists_partition_approximatesLinearOn_of_hasFDerivWithinAt`,
     `MeasureTheory/Function/Jacobian.lean:255`), using the level sets `cᵏ ≤ J < cᵏ⁺¹` and the
     Lipschitz image bound, and then letting `c → 1`. Images of the Borel pieces are Borel by
     Lusin–Souslin.
2. **Blow-up of a piece** (`ts_piece_density_blowup`). Let `x = F(w)`.
   - (3b) `Hⁿ(F(C) ∩ B_ρ(x)) ≤ Kⁿωₙc⁻ⁿρⁿ` (`ts_pdb_image_closedBall_measure_le`, from the
     Lipschitz image bound and `Measure.addHaar_closedBall`, `EqHaar.lean:500`).
   - (3a) At every Lebesgue density point `w` of `C`,
     `t⁻ⁿ∫_{F(C)} f(t⁻¹(y − F(w))) dHⁿ → ∫_{DF(w)(ℝⁿ)} f dHⁿ` for `f ∈ C_c`. This combines the
     area formula, the rescaling `v = w + tu`, the area formula for the linear map `DF(w)`
     (`ts_pdb_linear_range_integral`), and convergence at density points
     (`ts_pdb_density_point_rescaled_limit`, using `ts_pdb_density_complement_vanish`).
3. **Weighted blow-up** (`ts_piece_weighted_blowup_ae`). For `Hⁿ`-a.e. `x ∈ M` and every piece
   with `F_i(w) = x`, `t⁻ⁿ∫ f(t⁻¹(y − x)) dμ → θ(x)∫_{DF_i(w)(ℝⁿ)} f dHⁿ`. Ingredients:
   - `ts_pwb_pair_weight_integral`: `∫ g dμ = ∫_M θg dHⁿ`, and `μ` is finite on compacts;
   - `ts_pwb_density_points_of_image_ae`: `Hⁿ`-a.e. preimage point is a density point. This uses
     the Lebesgue density theorem `Besicovitch.ae_tendsto_measure_inter_div`
     (`MeasureTheory/Covering/Besicovitch.lean:1105`) and the Lipschitz image bound;
   - `ts_pwb_lusin_compact_cover`: Lusin for `μ ⌞ A`, proved like step 4 of §3.1;
   - `ts_pwb_upper_density_vanish_ae`: the upper density theorem (Simon Ch. 1, 3.6). If `ν` is
     finite on compacts and `A` is Borel, then `ν(A ∩ B_r(x))/rⁿ → 0` for `Hⁿ`-a.e. `x ∉ A`.
     It is proved with the Vitali covering lemma
     `Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall`
     (`MeasureTheory/Covering/Vitali.lean:158`), `Measure.hausdorffMeasure_le_liminf_tsum`
     (`MeasureTheory/Measure/Hausdorff.lean:555`) and closed inner approximation
     (`MeasurableSet.exists_isClosed_sdiff_lt`, `Regular.lean:1036`);
   - `ts_pwb_blowup_at_good_point`: the four-term split of Ch. 3, proof of 1.6.
4. **Uniqueness** (`ts_approx_tangent_plane_unique`). If `P` and `Q` are both approximate
   tangent planes, then `cHⁿ⌞P = c'Hⁿ⌞Q` by `Measure.ext_of_integral_eq_on_compactlySupported`
   (`MeasureTheory/Integral/RieszMarkovKakutani/Real.lean:412`). This needs regularity of
   `Hⁿ⌞P` (SimonGMT `Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule`,
   `Chapter03/Rectifiable.lean:187`). Taking supports gives `P = Q`, using
   `Chapter03.support_euclideanHausdorffMeasure_restrict_submodule` (`Rectifiable.lean:157`).
5. **Density** (`ts_blowup_closedBall_density`, with `ts_blowup_cutoff_closedBall_bounds`,
   `ts_unit_ball_plane_cutoff_approx` and `ts_plane_closedBall_measure`). First,
   `Hⁿ(P ∩ B_s(0)) = ωₙsⁿ`, via an isometry `P ≅ ℝⁿ` (`Isometry.map_euclideanHausdorffMeasure`,
   `Volume/Measure.lean:141`) and `Measure.addHaar_closedBall`. Squeezing `1_{B_t(x)}` between
   blow-ups of cut-offs then gives `μ(B_ρ(x))/(ωₙρⁿ) → θ(x)`.
6. **Ch. 3, 1.7 tangent** (`ts_blowup_weighted_tangent`). The change of variables under the
   blow-up map identifies the limit of item 3 with SimonGMT's
   `Chapter03.HasWeightedApproximateTangentSpaceAt` (`Rectifiable.lean:330`, part of the frozen
   statement of `ApproxTangentAE`). The blow-up map is `Chapter03.blowUpMap` (`Rectifiable.lean:96`).
   Items 3–6 give `ApproxTangentAE`.
7. **(GF).**
   - (FV1) follows from the local integrability of `θ`.
   - (FV2) follows from items 3–4, because `μ ≪ Hⁿ⌞M`.
   - (FV3): `p_x` agrees `μ`-a.e. with the strongly measurable field of
     `ts_piece_tangent_projection_field`. That field is pasted from the fields
     `y ↦ p_{DF_i(ψ_i(y))(ℝⁿ)}`, each continuous on the compact `F_i(C_i)`
     (`ts_piece_projection_continuousOn_image`), along the Borel sets `F_i(C_i) ∖ ⋃_{j<i} F_j(C_j)`
     (`ts_stronglyMeasurable_paste_continuousOn`). Continuity rests on
     `ts_starProjection_range_continuousOn_injective`:
     `p_{range A} = A(A*A)⁻¹A*` is continuous at injective `A`. This uses `InnerProductSpace.toDual`
     for the adjoint and `NormedRing.inverse_continuousAt` (`Analysis/Normed/Ring/Units.lean:183`).

**Part B: the first variation formula** (Ch. 4, 2.2; Ch. 2, 5.2–5.3), via `ts_first_variation_of_pieces`.

8. **Uniform bounds for the variation** (`ts_fv_compact_variation_bounds`, with
   `ts_fv_cv_first_order_regularity`, `ts_fv_cv_slice_fderiv_bounds` and
   `ts_fv_cv_slice_fderiv_time_deriv`):
   - `X = ∂_tφ|_{t=0}` is `C¹` with `DX = 0` off `K`;
   - each `φ_t` is `C¹` and Lipschitz;
   - `Dφ_t`, its inverse (through `Ring.inverse` and `NormedRing.inverse_continuousAt`) and its
     time derivative `Λ'(t, x)` are bounded uniformly for `|t| < ε/2`;
   - `Λ'(0, x) = DX(x)` by symmetry of `D²Φ`. This symmetry is proved directly from the mean value
     inequality (`Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'`,
     `Analysis/Calculus/MeanValue.lean:526`) and the continuity of `D²Φ`, because Mathlib's
     symmetry lemma is not imported by the frozen header.
9. **Image mass by the area formula** (`ts_fv_image_mass_area_formula`, with
   `ts_fv_piece_image_area_formula`, `ts_fv_lintegral_image_eq_of_pieces` and
   `ts_fv_det_tangential_gram_eq`). It shows
   `imageMass a φ_t K = ∫_{M∩K} θ·jac(Dφ_t(x), T_x) dHⁿ`, where
   `jac(Λ, P) = √det(⟪Λpe_i, Λpe_j⟫ + ⟪qe_i, qe_j⟫)`.
   - On one piece, the area formula is applied to `φ_t∘F` and to `F`. Both use the partition
     argument of item 1, with `Measure.addHaar_image_linearMap`.
   - The Gram identity `det(1 + B(GBᵀ − Bᵀ)) = det G` uses the Weinstein–Aronszajn identity
     `Matrix.det_one_add_mul_comm` (`LinearAlgebra/Matrix/SchurComplement.lean:400`) and
     `OrthonormalBasis.starProjection_eq_sum_rankOne` (`Analysis/InnerProductSpace/PiL2.lean:572`).
   - The pieces are glued by countable additivity.
10. **Derivative of the Jacobian** (`ts_fv_tangential_jacobian_hasDerivAt`, with
    `ts_fv_hasDerivAt_det_of_entries`, `ts_fv_det_ge_pow_of_quadForm_ge`,
    `ts_fv_tangential_matrix_estimates` and `ts_fv_sum_inner_starProjection_eq_trace`). It gives
    `J'(0) = trace(Λ'(0)∘p) = div_M X`, with `|J'| ≤ C` uniformly.
    - Jacobi's formula comes from the Leibniz expansion of the determinant.
    - The lower bound `cᴺ ≤ det S` for a `c`-coercive symmetric `S` is proved by induction on
      `N` through the Schur complement.
11. **Differentiation under the integral** (`ts_fv_hasDerivAt_of_weighted_jacobian`). This applies
    `hasDerivAt_integral_of_dominated_loc_of_deriv_le`
    (`Analysis/Calculus/ParametricIntegral.lean:286`) with dominant `Cθ`, and then
    `∫_{M∩K} θ·div_M X dHⁿ = ∫ div_M X dμ` (`integral_withDensity_eq_integral_toReal_smul₀`,
    `MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean:311`). This is `FirstVariationFormula`.

### 3.3 Stationarity — `stationary_iff_variational_of_first_variation`

**Statement.** `GF → FirstVariationFormula → StationaryIffVariational` (2.4).

**(⇒).** `compactVariation_velocity_isTestField`: the initial velocity of a compact variation
with `K ⊆ U` is a test field in `U`. It is `C¹` because `DΦ` is `C¹` on the open set
`(−ε, ε) × E`, and it vanishes off `K`. By `FirstVariationFormula` the mass derivative is
`∫ div_M X dμ`, which is `0` by stationarity.

**(⇐), smooth fields.** `exists_isCompactVariation_add_smul`: for smooth compactly supported `Z`,
`φ_t(y) = y + tZ(y)` is a compact variation for `|t| < 1/(L + 1)`, with initial velocity `Z`.
- `φ_t` is a homeomorphism by `ApproximatesLinearOn.toHomeomorph`
  (`Analysis/Calculus/InverseFunctionTheorem/ApproximatesLinearOn.lean:428`).
- `I + tDZ` is invertible by a Neumann series (`Units.oneSub`).
- The inverse is smooth by `Homeomorph.contDiff_symm` (`Analysis/Calculus/ContDiff/Operations.lean:940`).

Uniqueness of derivatives then gives `∫ div_M Z dμ = 0`.

**(⇐), `C¹` fields.** `exists_smooth_approx_testField_fderiv` mollifies: `Y_k = ψ_k ⋆ X` with
`ContDiffBump` kernels gives smooth fields supported in one compact `K ⊆ U` with `DY_k → DX`
uniformly. It uses `HasCompactSupport.contDiff_convolution_left`
(`Analysis/Calculus/ContDiff/Convolution.lean:427`),
`HasCompactSupport.hasFDerivAt_convolution_right` (`:61`) and `dist_convolution_le`
(`Analysis/Convolution.lean:814`). Then `tendsto_integral_tangentialDiv_of_tendstoUniformly_fderiv`
uses (GF) to show `|∫ div_M Y_k − ∫ div_M X| ≤ (n + ℓ)‖DY_k − DX‖_∞ μ(K) → 0`, so `∫ div_M X = 0`.

### 3.4 Radial first variation — `radial_first_variation`

**Statement.** Assume (FV2), `U` open, `V` with generalized mean curvature `H` in `U`,
`h ∈ C¹(U)` and `γ ∈ C¹(ℝ)`, and let `X(x) = h(x)γ(r)(x − ξ)` be a test field in `U`. Then
`∫_U [h(nγ(r) + rγ'(r)(1 − q_ξ)) + γ(r)⟨x − ξ, ∇^M h⟩] dμ = −∫_U hγ(r)⟨x − ξ, H⟩ dμ`
(Simon 3.2–3.3, 5.1).

**Formal argument.** Three sub-lemmas give the pointwise formula wherever `dim T_x = n`:
- `radial_vector_field_hasFDerivAt` differentiates `γ(|y − ξ|)(y − ξ)`, including at the centre;
- `trace_scalar_add_rankOne_comp_starProjection`: `trace((cI + F(·)v)∘p_P) = c·dim P + F(p_Pv)`;
- `tangentialDiv_weighted_radial_field` combines them.

By (FV2) the pointwise formula holds `μ`-a.e. The mean-curvature identity is then applied to `X`.
Both integrands vanish off `tsupport X ⊆ U`, so the integrals over `E` equal those over `U`.

### 3.5 Weighted monotonicity identity — `weighted_monotonicity_identity`

**Statement.** Assume (FV1)–(FV3), `H` a generalized mean curvature in the open set `U`,
`h ∈ C¹(U)`, `tsupport h ∩ B_ρ(ξ) ⊆ U` and `0 < σ ≤ ρ`. Then both integrands below are
integrable and

`ρ⁻ⁿ∫_{B_ρ} h dμ − σ⁻ⁿ∫_{B_σ} h dμ = ∫_{B_ρ∖B_σ} h·w_ξ dμ + ∫_{(σ,ρ]} τ^{−n−1}∫_{B_τ}⟨x − ξ, ∇^M h + hH⟩ dμ dτ`.

**Formal argument.** This follows the printed route 3.3–3.6 and 5.1.
1. **Cutoff identity** (`weighted_mono_cutoff_first_variation`, with `weighted_mono_local_data`,
   `weighted_mono_radial_test_field` and `weighted_mono_cutoff_identity`). For a `C¹`
   nonincreasing cutoff `φ`, `§3.4` applied to `hφ(r/τ)(x − ξ)` gives
   `n∫hφ(r/τ) + ∫h(1 − q)(r/τ)φ'(r/τ) + ∫φ(r/τ)G = 0`, where `G = ⟨x − ξ, ∇^M h + hH⟩`.
2. **Integration in τ** (`weighted_mono_smoothed_identity`). The pieces are:
   - `weighted_mono_cutoff_hasDerivAt`, by `hasDerivAt_integral_of_dominated_loc_of_deriv_le`;
   - `wm_smoothed_scale_integral_continuousOn`, by `continuousOn_of_dominated`
     (`MeasureTheory/Integral/Bochner/Basic.lean:467`);
   - `wm_smoothed_scaled_ftc`, by the quotient rule and `intervalIntegral.integral_eq_sub_of_hasDerivAt`
     (`MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean:1148`);
   - `wm_smoothed_kernel_fubini`, by `integral_integral_swap` (`MeasureTheory/Integral/Prod.lean:478`).
3. **Removing the cutoff** (`weighted_mono_cutoff_limit`). The cutoffs are
   `φ_m = 1 − smoothTransition((t − 1)/ε_m)` (`weighted_mono_cutoff_seq_exists`). The kernel
   squeeze is the corrected 3.5 (`weighted_mono_kernel_bounds`, `weighted_mono_kernel_limit`).
   The limits use dominated convergence (`tendsto_integral_of_dominated_convergence`,
   `MeasureTheory/Integral/DominatedConvergence.lean:57`) in
   `weighted_mono_cutoff_integral_tendsto`, `weighted_mono_kernel_term_tendsto` and
   `weighted_mono_curvature_term_tendsto`.

With the sign convention 3.14(‡), the curvature term enters with a `+` sign (erratum to 3.16/4.1).

### 3.6 Stationary monotonicity and density — `stationary_monotonicity_density`

**Statement.** `GF → StationaryMonotonicity ∧ StationaryDensity` (3.6–3.11).

**Formal argument.**
- A stationary `V` has generalized mean curvature `0` in `U`. §3.5 with `h ≡ 1` and `H ≡ 0` then
  gives 3.6 for `0 < σ ≤ ρ < R`.
- `stationary_ratio_limit_of_annulus_identity` derives the rest from 3.6:
  - `a` is monotone because `w_ξ ≥ 0` (3.8);
  - `a(s) → L = inf a`, and `Θ(ξ) = L/ωₙ` exists (3.9);
  - monotone convergence on `B_ρ ∖ B_{ρ/(k+1)} ↑ B_ρ ∖ {ξ}` gives the integrability of `w_ξ` on
    `B_ρ` and 3.10;
  - it also gives `Θ(ξ) ≤ μ(B_ρ(ξ))/(ωₙρⁿ)`.
- `stationary_density_usc_of_ratio_bound` gives upper semicontinuity (3.11) from continuity from
  above of `μ` on `B_{ρ+δ}(ξ) ↓ B_ρ(ξ)`.

### 3.7 Monotonicity with mean curvature — `mean_curvature_monotonicity`

**Statement.** `GF → BoundedCurvatureMonotonicity ∧ LogarithmicMonotonicityError ∧ LpMonotonicity ∧ LpDensity`.

**Formal argument.**
- **Unit-weight identity** (`mcm_unit_weight_identity`). §3.5 with `h ≡ 1` gives
  `a(ρ) − a(σ) = ∫_{B_ρ∖B_σ} w_ξ + ∫_σ^ρ e`, where `e(τ) = τ^{−n−1}∫_{B_τ}⟨x − ξ, H⟩`.
- **3.18** (`mcm_log_error_of_identity`). `|e(τ)| ≤ δ/τ`, and `∫_σ^ρ δ/τ = δ log(ρ/σ)`.
- **3.17** (`mcm_bounded_curvature_of_identity`). Since `|e| ≤ Λa`, the quotient `E = e/a`
  satisfies `|E| ≤ Λ`. The integrating factor `F(ρ) = exp(−∫_0^ρ E)` lies in
  `[e^{−Λρ}, e^{Λρ}]`. Integration by parts on the annulus gives
  `F(ρ)a(ρ) − F(σ)a(σ) = ∫ F(r)w_ξ = G·∫ w_ξ` with `G ∈ [e^{−ΛR}, e^{ΛR}]`. The supporting lemmas:
  - `mcm_annulus_integration_by_parts`, built from `mcm_annulus_primitive_fubini` and
    `mcm_interval_primitive_fubini`, both instances of `mcm_primitive_radial_fubini` (Fubini via
    `integral_integral_swap` and `Integrable.mul_prod`, `Integral/Prod.lean:297`);
  - `mcm_exp_neg_integral_ftc`: `F` is absolutely continuous with `F' = −EF`, by a real-induction
    estimate and `intervalIntegral.continuousOn_primitive_interval` (`DominatedConvergence.lean:483`);
  - `mcm_density_usc_of_monotone`: existence and upper semicontinuity of `Θ` from the uniformly
    almost-monotone ratios `F·a`.
- **4.2–4.8** (`mcm_lp_monotonicity_of_identity`, with `mcm_lp_holder_bound`).
  - Hölder (`integral_mul_le_Lp_mul_Lq_of_nonneg`, `Bochner/Basic.lean:1230`) gives
    `|e(τ)| ≤ (κΛ/R)(τ/R)^{−n/p}(1 + a(τ))`.
  - With the corrected `κ`, `F₀ = e/(1 + a)` satisfies `∫_0^ρ|F₀| ≤ (Λ/4)(ρ/R)^{1−n/p}`.
  - `F = exp(−∫F₀)` satisfies the 4.5 bounds.
  - `Fe + F'a = −F'` gives 4.7, with `G ∈ [e^{−Λ}, e^{Λ}]`, and the monotonicity 4.8 on `(0, R]`.
- **4.9** (`mcm_lp_density_of_monotonicity`). It applies `mcm_density_usc_of_monotone` with one
  `Λ` that is uniform on `B_{2R}(ξ)`.

### 3.8 Canonical representatives — `canonical_representatives`

**Statement.** `AT → GF → CanonicalRepresentative ∧ LpSupportRepresentation` (3.12, 3.13, 4.10(1)).

**Formal argument.** Both conclusions use only that `Θ` exists on `U` and is upper
semicontinuous there. That is `StationaryDensity` (§3.6) for stationary `V`, and `LpDensity`
(§3.7) for `H ∈ L^p_loc`, `p > n`.
- `hausdorff_null_of_measure_null_density_ge` (a special case of Simon Ch. 1, 3.3). If `μ` is
  finite on compacts, `μ(A) = 0` and `Θ ≥ t > 0` on `A`, then `Hⁿ(A) = 0`. The proof takes an
  open `O ⊇ A` with `μ(O)` small, applies the Vitali covering (`Vitali.lean:158`), and uses
  `Measure.hausdorffMeasure_le_liminf_tsum` (`Hausdorff.lean:555`).
- `canonicalCarrier_rectifiablePair_weight`.
  - `ApproxTangentAE` gives `Θ = θ` `Hⁿ`-a.e. on `M`, so `Hⁿ((M ∩ U) ∖ M_V) = 0`.
  - `μ(Mᶜ) = 0`, so the density lemma applied to `{x ∈ U ∖ M : Θ(x) ≥ 1/(k + 1)}` gives
    `Hⁿ(M_V ∖ M) = 0`. Hence `M_V = M ∩ U` up to `Hⁿ`-null sets.
  - Admissibility: rectifiability transfers from `M` after enlarging the exceptional null set,
    and null-measurability transfers likewise; positivity holds by definition; local
    integrability follows from `Θ = θ` a.e.
  - The weights agree: `pairWeight n M_V Θ = μ ⌞ U`.
- `canonicalCarrier_closed_support`.
  - Upper semicontinuity gives a closed `C` with `{x ∈ M_V : Θ ≥ α} = C ∩ U`.
  - Under `MultiplicityGE α U`, `Θ ≥ α` holds `μ`-a.e. in `U`, hence on `spt V ∩ U` by upper
    semicontinuity.
  - `Θ > 0` forces `x ∈ spt V`. So `M_V = spt V ∩ U`.
- With `α = 1` and `LpDensity`, this is 4.10(1).

### 3.9 Poincaré inequality — `poincare_inequality`

**Statement.** `AT → GF → PoincareInequality` (5.6), in the frozen quantifier order
`∀ n, ∀ α Γ, ∃ β c, ∀ ℓ V U H Λ h ξ ρ`.

**Formal argument.**
- **Constants.** Given `n, α, Γ`, fix `β ∈ (0, ½)` with `(1 − α²)(1 − β)⁻ⁿ ≤ 1 − α²/2`, and
  `c = 8Γ/(α²ωₙ)`. Both are chosen before `ℓ` and the data.
- **Density facts.** A bounded `H` is in `L^{n+1}_loc`. So `Θ` exists on `U` (`LpDensity`, §3.7)
  and `Θ ≥ 1` on `spt V ∩ U` (`LpSupportRepresentation`, §3.8).
- **5.4 in Gronwall form** (`bounded_curvature_ball_average_estimate`). It is proved from §3.5,
  `backward_integral_gronwall_Ioc`, Tonelli (`lintegral_lintegral_swap`,
  `MeasureTheory/Measure/Prod.lean:1071`) and `integral_Ioi_rpow_of_lt`
  (`Analysis/SpecialFunctions/ImproperIntegrals.lean:178`).
- **Growth and kernel bounds.** 5.4 with `g ≡ 1` gives `μ(B_s(y)) ≤ 2Γsⁿ`. Then
  `closedBall_rpow_kernel_lintegral_le_of_growth` (4.10(2) for full balls) gives
  `∫_{B_s(y)}|x − y|^{1−n} dμ ≤ 2nΓs`, via the layer-cake formula `lintegral_eq_lintegral_meas_lt`
  (`MeasureTheory/Integral/Layercake.lean:496`).
- **Truncations.** `smooth_step_truncation_exists` (`ψ = smoothTransition(·/ε)`),
  `tangentialGradient_comp_of_differentiableAt` (chain rule for `∇^M`) and
  `density_point_mean_value_estimate` (5.4 as `s ↓ 0` at a point of density `≥ 1`) give
  `α²nωₙ/4 ≤ ∫ ψ'(h − t)|∇^M h||x − ζ|^{1−n} dμ` at `μ`-a.e. `ζ ∈ B_{βρ}(ξ)` with `h(ζ) > t + ε`.
- **Integration and limit.** `layer_cake_tonelli_truncation_bound` integrates in `ζ` and `t`
  (layer cake and Tonelli). Finally `ε ↓ 0`.

### 3.10 Sobolev inequality — `sobolev_inequality`

**Statement.** `AT → GF → SobolevInequality` (5.7, 5.9, with `n ≥ 2`), with the constant
`c(n) = 5^{n+1}ωₙ^{−1/n}`.

**Formal argument.**
1. **The superlevel estimate.** For every admissible `g`,
   `∫_{g≥1} g ≤ 5ⁿωₙ^{−1/n}(∫g)^{1/n}∫(|∇^M g| + g|H|)`. Ingredients:
   - `sobolev_energy_integrable` (preliminaries);
   - `sobolev_monotonicity_inequality` (5.5 at all radii, from §3.5);
   - `sobolev_density_ge_one_ae` (`Θ ≥ 1` `μ`-a.e. in `U`, from `ApproxTangentAE` and
     `MultiplicityGE 1 U`);
   - `sobolev_good_radius_calculus` (the corrected Lemma 5.8);
   - `sobolev_covering_inequality` (good balls with the Vitali 5r covering, `Vitali.lean:158`, and
     `exists_measurable_superset_of_null`).
2. **From the superlevel estimate to the Sobolev inequality** (`sobolev_of_superlevel_inequality`).
   Ingredients:
   - `sobolev_truncation_superlevel_bound` (truncations `γ(h − t)`);
   - `sobolev_level_integral_bound`, which uses `sobolev_level_moment_factor`,
     `sobolev_level_energy_tonelli` and `sobolev_level_layer_cake`. The latter rests on the
     layer-cake formula `lintegral_comp_eq_lintegral_meas_lt_mul` (`Layercake.lean:478`) and
     `integral_rpow` (`Analysis/SpecialFunctions/Integrals/Basic.lean:146`);
   - `sobolev_of_level_integral_bounds` (`ε ↓ 0` by dominated convergence, then division by `Q^{1/n}`).
3. **The constant.** The constant obtained is `n/(n − 1)·5ⁿωₙ^{−1/n} ≤ 5^{n+1}ωₙ^{−1/n}`.

### 3.11 Support in a ball and the convex hull property — `support_in_ball_convex_hull`

**Statement.** `GF → SupportInBall ∧ ConvexHullProperty` (6.1, 6.2).

**6.1** (`support_in_ball_of_radial_first_variation`, which takes `radial_first_variation` and GF
as arguments):
- `exists_radial_cutoff_test_field` builds the test field:
  - a `ContDiffBump` `ζ` with `ζ ≡ 1` near `spt V`;
  - the profile `γ(t) = expNegInvGlue(t² − (R + ε)²)`, which vanishes on `[0, R + ε]` and is
    positive and nondecreasing beyond;
  - the test field `X = ζγ(r)(x − ξ)` in `E ∖ B_R(ξ)`.
- `aestronglyMeasurable_normalRadialSq_and_bounds`: `q` is measurable and `0 ≤ q ≤ 1`.
- `support_subset_closedBall_of_radial_identity` is the positivity argument:
  `∫_U γ(r)(n − |⟨H, x − ξ⟩|) dμ ≤ 0` forces `γ(r) = 0` `μ`-a.e. in `U`, hence
  `spt μ ⊆ B_{R+ε}(ξ)`.
- Finally `ε ↓ 0`.

**6.2** (`convex_hull_property_of_support_in_ball`). Suppose `y ∈ spt V ∖ conv K`.
- If `K = ∅`, a ball not containing `y` is chosen directly.
- Otherwise `conv K` is compact by Carathéodory. The Lean proof shows this with
  `convexHull_eq_union_convexHull_finite_subsets` (`Analysis/Convex/Combination.lean:428`),
  `Finset.mem_convexHull'` (`:414`) and
  `Module.exists_nontrivial_relation_sum_zero_of_finrank_succ_lt_card`
  (`LinearAlgebra/Dimension/Finite.lean:305`).
- The nearest point `z₀ ∈ conv K` to `y` (`exists_norm_eq_iInf_of_complete_convex`,
  `Analysis/InnerProductSpace/Projection/Minimal.lean:36`) satisfies `⟪y − z₀, x − z₀⟫ ≤ 0` on
  `conv K`. This yields an explicit closed ball `B_R(c) ⊇ K` with `y ∉ B_R(c)`.
- `V` has mean curvature `0` outside `B_R(c)`, so 6.1 gives `spt V ⊆ B_R(c)`, a contradiction.

### 3.12 Classical tangent — `classical_tangent`

**Statement.** `AT → GF → ClassicalTangent` (6.3). It uses `LpMonotonicity` and `LpDensity`
(§3.7) and `LpSupportRepresentation` (§3.8).

**Formal argument.**
- **Uniform lower density** (`classical_tangent_uniform_lower_density`, 6.3(1)).
  - One `Λ`, computed on `B_{2R}(x)`, works for `LpMonotonicity` at every centre `ζ ∈ B_R(x)`.
  - At `ζ ∈ spt V ∩ B_R(x)`, the monotone `Ψ = Fa + F − 1` satisfies `Ψ ≥ ωₙΘ(ζ) ≥ ωₙ`.
  - Choose `t₀` with `Ct₀ ≤ ωₙ/4` and `e^{Λt₀/2} ≤ 3/2`, and put `ρ₀ = R·t₀^{p/(p−n)}`. This gives
    `μ(B_s(ζ)) ≥ (ωₙ/2)sⁿ` for `ζ ∈ spt V ∩ B_{ρ₀}(x)` and `0 < s ≤ ρ₀`.
- **Off-plane mass decay** (`classical_tangent_off_plane_mass_decay`). Test the approximate
  tangent limit against a cut-off `f ∈ C_c` with `f = 0` on `P` and `f = 1` on
  `{|z| ≤ 1, dist(z, P) ≥ ε}`. The `μ`-mass of `B_ρ(x)` at distance `≥ ερ` from `x + P` is then
  `o(ρⁿ)`.
- **Support flatness** (`classical_tangent_support_flatness`, 6.3(2)). A point of
  `spt V ∩ B_{ρ/2}(x)` at distance `≥ (ε + α)ρ` from `x + P` would place a ball of mass
  `≥ a(αρ)ⁿ` in the off-plane region. With `ε = η/8` and `α = min(η/8, 1/4)` this gives
  `sSup ≤ η/2` for small `ρ`, hence the limit `0`.

## 4. Dependencies, provenance and absence of circularity

### 4.1 Declarations actually referenced by the Lean proofs

The graph was extracted from the compiled candidate, not from the source text (§7, item 6). For
each `GMT.Ch04.Submission.*` declaration, the constants of its elaborated proof term were
collected, following the compiler-generated auxiliary declarations of the same module.
Appendix A lists, for each of the 121 declarations, the `Submission.*` declarations it references
directly. The top of the graph:

| Declaration | Direct `Submission.*` references |
| --- | --- |
| `main_theorem` | `tangent_structure_first_variation`, `stationary_iff_variational_of_first_variation`, `stationary_monotonicity_density`, `mean_curvature_monotonicity`, `canonical_representatives`, `poincare_inequality`, `sobolev_inequality`, `support_in_ball_convex_hull`, `classical_tangent` |
| `tangent_structure_first_variation` | `rectifiable_lipschitz_piece_cover`, `ts_approx_tangent_plane_unique`, `ts_blowup_closedBall_density`, `ts_blowup_weighted_tangent`, `ts_first_variation_of_pieces`, `ts_piece_tangent_projection_field`, `ts_piece_weighted_blowup_ae` |
| `stationary_monotonicity_density` | `weighted_monotonicity_identity`, `stationary_ratio_limit_of_annulus_identity`, `stationary_density_usc_of_ratio_bound` |
| `mean_curvature_monotonicity` | `weighted_monotonicity_identity`, `mcm_unit_weight_identity`, `mcm_bounded_curvature_of_identity`, `mcm_log_error_of_identity`, `mcm_lp_monotonicity_of_identity`, `mcm_lp_density_of_monotonicity` |
| `canonical_representatives` | `stationary_monotonicity_density`, `mean_curvature_monotonicity`, `canonicalCarrier_rectifiablePair_weight`, `canonicalCarrier_closed_support` |
| `poincare_inequality` | `weighted_monotonicity_identity`, `mean_curvature_monotonicity`, `canonical_representatives`, `bounded_curvature_ball_average_estimate`, `density_point_mean_value_estimate`, `closedBall_rpow_kernel_lintegral_le_of_growth`, `layer_cake_tonelli_truncation_bound`, `smooth_step_truncation_exists`, `tangentialGradient_comp_of_differentiableAt` |
| `sobolev_inequality` | `weighted_monotonicity_identity`, `sobolev_energy_integrable`, `sobolev_monotonicity_inequality`, `sobolev_density_ge_one_ae`, `sobolev_covering_inequality`, `sobolev_of_superlevel_inequality` |
| `support_in_ball_convex_hull` | `radial_first_variation`, `support_in_ball_of_radial_first_variation`, `convex_hull_property_of_support_in_ball` |
| `classical_tangent` | `mean_curvature_monotonicity`, `canonical_representatives`, `classical_tangent_uniform_lower_density`, `classical_tangent_off_plane_mass_decay`, `classical_tangent_support_flatness` |
| `stationary_iff_variational_of_first_variation` | `compactVariation_velocity_isTestField`, `exists_isCompactVariation_add_smul`, `exists_smooth_approx_testField_fderiv`, `tendsto_integral_tangentialDiv_of_tendstoUniformly_fderiv` |
| `weighted_monotonicity_identity` | `radial_first_variation`, `weighted_mono_cutoff_first_variation`, `weighted_mono_smoothed_identity`, `weighted_mono_cutoff_limit` |
| `radial_first_variation` | `tangentialDiv_weighted_radial_field` |
| `rectifiable_lipschitz_piece_cover` | `lipschitz_range_piece_cover` |

**Closure.** The transitive `Submission.*` closure of `main_theorem` has exactly 121 members. These
are all the accepted DAG nodes, so no accepted declaration is unused.

**No circularity.**
- Lean elaborates `Submission.lean` from top to bottom, and a declaration can only mention
  declarations that precede it. The candidate compiles, so its order (Appendix A, column "Line")
  is a topological order of the graph, and `main_theorem` is the last declaration.
- The conditional children take (GF), `ApproxTangentAE` and `FirstVariationFormula` as explicit
  antecedents; none of them assumes its own conclusion or a later conjunct.
- The three antecedents are proved by `tangent_structure_first_variation`. That declaration
  depends only on `rectifiable_lipschitz_piece_cover` and on the `ts_*` lemmas, and none of these
  depends on a section theorem.
- Mathlib and `simongmt` are upstream packages pinned before this problem existed, so they
  cannot refer to `GMT.Ch04`.

### 4.2 Library provenance (SimonGMT)

The elaborated proofs reference exactly nine `Poincare.SimonGMT.*` constants, all from the pinned
package at `2b3663083f3fe399b6296fb8eaee52169170e197`:

| Constant | Location | Used by |
| --- | --- | --- |
| `Chapter03.CountablyRectifiable` (def) | `Chapter03/Rectifiable.lean:34` | the contract (`IsRectifiablePair`); `rectifiable_lipschitz_piece_cover`, `canonicalCarrier_rectifiablePair_weight` |
| `Chapter03.HasWeightedApproximateTangentSpaceAt` (def) | `Chapter03/Rectifiable.lean:330` | the contract (`ApproxTangentAE`); `ts_blowup_weighted_tangent`, `tangent_structure_first_variation`, `canonicalCarrier_*`, `sobolev_density_ge_one_ae` |
| `Chapter03.blowUpMap` (def) | `Chapter03/Rectifiable.lean:96` | `ts_blowup_weighted_tangent` |
| `Chapter03.support_euclideanHausdorffMeasure_restrict_submodule` | `Chapter03/Rectifiable.lean:157` | `ts_approx_tangent_plane_unique` |
| `Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule` | `Chapter03/Rectifiable.lean:187` | `ts_approx_tangent_plane_unique` |
| `Chapter02.areaRegularSet` (def) | `Chapter02/AreaLipschitz.lean:31` | `lipschitz_range_piece_cover` |
| `Chapter02.measurableSet_areaRegularSet` | `Chapter02/AreaLipschitz.lean:34` | `regular_set_lower_lipschitz_cover` |
| `Chapter02.area_image_compl_regularSet_eq_zero` | `Chapter02/AreaLipschitz.lean:59` | `lipschitz_range_piece_cover` |
| `Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn` | `Chapter02/Lipschitz.lean:216` | `lipschitz_range_piece_cover`, `ts_pdb_image_closedBall_measure_le`, `ts_pdb_piece_area_formula`, `ts_fv_piece_image_area_formula`, `ts_fv_image_mass_area_formula`, `ts_pwb_density_points_of_image_ae` |

The contract imports `Poincare.SimonGMT.Chapter03.Rectifiable`. `Submission.lean` additionally
imports `Poincare.SimonGMT.Chapter02.AreaLipschitz`. That import was added within the accepted
`root.lipschitz_pieces-a1` subtree (commits `38ba3ce` and `2f4370e`), and it is allowed:
- the comparator byte-checks every frozen input except `Submission.lean`;
- it then compares the elaborated `main_theorem` against the contract's, and that comparison
  passed (§7.1).

No definition of SimonGMT's `Chapter04` is referenced. That includes the strengthened
`Chapter04.RectifiableVarifold`, which the README marks as not reusable for contract pairs.

The Mathlib declarations that carry the main weight are cited with their snapshot locations in §3.
All of them were checked to occur in the elaborated proof terms.

### 4.3 Historical decomposition versus what is actually used

**Decomposition history.**
- **v1** (`nodes/root/decomposition-v1.json`) was rejected by its review
  (`decomposition-review-receipt-v1.json`, `decomposition-audit-v1.json`). The `tangent_structure`
  prose claimed a diffeomorphism from a closed ball onto an open set, and it cited a `C¹`
  approximation theorem without a pinned declaration.
- **v2** (`decomposition-v2.json`) was accepted (`decomposition-review-receipt-v2.json`,
  `decomposition-audit-v2.json`). It introduced the new child `lipschitz_pieces` and stated every
  other conjunct-child conditionally on (GF).

The v2 parent proof is the assembly of §2, and the speculative root draft `1c2e9dc` wrote it
(§5). All twelve v2 children and their 109 descendants are `accepted`. Every one of them is
used (§4.1).

**Declared edges versus actual edges.** Every declared `depends_on` edge between accepted nodes
is an actual reference. Twenty parent→child edges are used only indirectly: the parent references
a sibling that references the child. Examples:
- `canonical_representatives` → `hausdorff_null_of_measure_null_density_ge`, through
  `canonicalCarrier_rectifiablePair_weight`;
- `curvature_monotonicity` → `mcm_annulus_integration_by_parts`, `mcm_density_usc_of_monotone`,
  `mcm_exp_neg_integral_ftc` and `mcm_lp_holder_bound`, through `mcm_bounded_curvature_of_identity`
  and `mcm_lp_monotonicity_of_identity`;
- `poincare_inequality` → `backward_integral_gronwall_Ioc`, through
  `bounded_curvature_ball_average_estimate`.

No reference occurs that the DAG does not declare.

**Library results cited in the reviewed child prose but not used by the Lean proofs.** The
accepted Lean proofs re-derive the following steps from more basic Mathlib results (§3), so the
cited declarations do **not** occur in the elaborated proofs. The reviewed prose is left
unchanged as history.

| Cited in the reviewed prose | What the Lean proof uses instead |
| --- | --- |
| SimonGMT `Chapter02.weighted_area_formula_lipschitz_injOn`, `Chapter02.areaJacobian_comp_eq_parametrization_mul_tangential`, Mathlib `LinearMap.normDet_comp` (area formula and Jacobian chain rule) | own area formula on pieces (§3.2, items 1 and 9) via `exists_partition_approximatesLinearOn_of_hasFDerivWithinAt` and `Measure.addHaar_image_linearMap`; Gram-determinant identity via `Matrix.det_one_add_mul_comm` |
| SimonGMT `Chapter01.exists_isClosed_continuousOn_of_measurable` (Lusin) | `lusin_compact_exhaustion_of_measurable`, `ts_pwb_lusin_compact_cover`, proved from outer and inner regularity (§3.1, item 4) |
| SimonGMT `Chapter01.ae_dimensionalUpperDensity_eq_zero_outside` (upper density theorem), with `measure_toOuterMeasure_isBorelRegular` and `simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure` | `ts_pwb_upper_density_vanish_ae`, proved with the Vitali covering lemma and `Measure.hausdorffMeasure_le_liminf_tsum` |
| SimonGMT `Chapter01.simon_theorem_3_3` | `hausdorff_null_of_measure_null_density_ge`, proved with the Vitali covering lemma |
| SimonGMT `Chapter02.rademacher_ae_differentiableAt` | Mathlib `LipschitzWith.ae_differentiableAt` (in `ts_pdb_piece_area_formula`) |
| Mathlib `ContDiffAt.isSymmSndFDerivAt` (symmetry of `D²Φ`) | proved directly from the mean value inequality (§3.2, item 8); the Mathlib lemma is not imported by the frozen header |
| spectral theorem for `cᴺ ≤ det S` | Schur-complement induction (`ts_fv_det_ge_pow_of_quadForm_ge`) |
| Mathlib `geometric_hahn_banach_point_closed`, `eq_pos_convex_span_of_mem_convexHull` (6.2) | nearest-point projection `exists_norm_eq_iInf_of_complete_convex` and Carathéodory via `Module.exists_nontrivial_relation_sum_zero_of_finrank_succ_lt_card` |
| profile `γ(t) = ((t − R − ε)⁺)²` in the 6.1 prose of `support_convex_hull` | `expNegInvGlue(t² − (R + ε)²)` (the accepted grandchild `exists_radial_cutoff_test_field`) |

These changes affect only how a step is justified. They change no statement, so every accepted
interface is preserved (§7, item 3).

### 4.4 Child records

The record directories of all 121 accepted nodes are in Appendix B, and their issues and PRs in
Appendix A. For the twelve root children:

| Child (`Submission.*`) | DAG node | Issue | Solution PR |
| --- | --- | --- | --- |
| `rectifiable_lipschitz_piece_cover` | `root.lipschitz_pieces-a1` | #54 | #1063 |
| `tangent_structure_first_variation` | `root.tangent_structure-a1` | #55 | #2170 |
| `stationary_iff_variational_of_first_variation` | `root.stationary_iff_variational-a1` | #56 | #725 |
| `radial_first_variation` | `root.radial_first_variation-a1` | #57 | #1587 |
| `weighted_monotonicity_identity` | `root.weighted_monotonicity-a1` | #58 | #1943 |
| `stationary_monotonicity_density` | `root.stationary_monotonicity-a1` | #59 | #2019 |
| `mean_curvature_monotonicity` | `root.curvature_monotonicity-a1` | #60 | #2104 |
| `canonical_representatives` | `root.canonical_representatives-a1` | #61 | #2236 |
| `poincare_inequality` | `root.poincare_inequality-a1` | #62 | #2401 |
| `sobolev_inequality` | `root.sobolev_inequality-a1` | #63 | #2113 |
| `support_in_ball_convex_hull` | `root.support_convex_hull-a1` | #64 | #1729 |
| `classical_tangent` | `root.classical_tangent-a1` | #65 | #2323 |

## 5. History (preserved, not rewritten)

The following records under `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root/`
are left untouched:
- **Plan.** `plan-draft-v1.md`, `plan-v1.md`, `plan-source.md`, and the implementation plan
  `rlcr-plan-v1.md`.
- **Accepted natural-language source.** `natural-proof-source.md` and `natural-proof-source.json`:
  the operator-supplied published proof `chapter-04-source.txt` (sha256 `20687e83…1e6`), whose key
  steps are "follow the published proof" of each of the sixteen conjuncts.
- **Decomposition.**
  - `decomposition-v1.json`, with `decomposition-review-receipt-v1.json` and
    `decomposition-audit-v1.json` (rejected);
  - `decomposition-v2.json`, with `decomposition-review-receipt-v2.json`,
    `decomposition-audit-v2.json` and `decomposition-scope-v2.json` (accepted).
- **Speculative root draft.** Commit `1c2e9dce5b4809a556cfafce64c648f9b9c3b09b`
  (`speculative-process-v2.log`, `speculative-prompt-v2.md`) wrote the present `main_theorem`
  body. It is recorded with candidate `84bf131` in
  `speculative-finalization-1c2e9dce5b4809a556cfafce64c648f9b9c3b09b.json`.
- **Rejected candidate.** The comparator rejected `84bf13196cf99c43d63c676c7637001ce4908e7e`
  (`comparator-v1.log`). Its evidence directory is
  `cluster-state/verification/results/hoa58/20261012T144635Z-ch04-root-7e83uzt0/`, with
  `status: failed`. §6 describes the repair.

The final Lean route agrees with the accepted v2 outline: the root step is exactly the v2 parent
proof. The refinements inside the children are listed in §4.3.

## 6. Changes made while implementing the root (commit `73ff327`)

**The failure.** Candidate `84bf131` was the overlay, by merge commits, of the twelve accepted
child branches and the speculative root draft onto the frozen commit. The comparator rejected it
with these errors in `GMT/Ch04/Submission.lean`:
- unsolved goals and parse errors at lines 1496–1525;
- "No goals to be solved" at 4828 and 4830;
- "declaration uses `sorry`" at 5133;
- "`GMT.Ch04.main_theorem` has already been declared" at 7491 and 7492.

**The cause.** The overlay was checked block by block at each merge of the branch's first-parent
chain (§7, item 5).
- **Interleaving.** Merge `b820620` brought in `root.stationary_iff_variational-a1` (commit
  `4f0a6ec`) after `root.tangent_structure-a1` (`6daa923`) had been merged at `e689bbf`. The
  textual three-way merge interleaved two declarations: `Submission.ts_fv_cv_first_order_regularity`
  from the tangent-structure side and `Submission.compactVariation_velocity_isTestField` from the
  other. The five tail lines of the second landed after `Submission.lipschitz_range_piece_cover`.
  At `e689bbf` every block was still byte-identical to an accepted child block; at `b820620`
  exactly these three were not, and they stayed so up to `84bf131`.
- **Three `main_theorem`s.**
  - The contract's `:= by sorry` appeared a second time at merge `b4cd8fb` (of
    `root.radial_first_variation-a1`, commit `7ddd089`). These two copies are at lines 5133 and
    7491 of `84bf131`.
  - The speculative draft came with the final merge `84bf131` (of `1c2e9dc`). It sits at line
    7492, *before* several declarations it uses, for example `support_in_ball_convex_hull` and
    `classical_tangent`.

**The fix.** The file was split mechanically into top-level declaration blocks and compared with
the `Submission.lean` of each of the twelve accepted child solution branches (the commits of
Appendix B's records):
- every declaration name had exactly **one** version across all twelve children;
- every block of the overlay except four was byte-identical to a child block;
- the four exceptions were the two interleaved declarations, `lipschitz_range_piece_cover` with
  its foreign tail, and the draft `main_theorem`.

The repair:
1. replaced the three corrupted declarations by their unique accepted texts;
2. removed all three `main_theorem`s;
3. appended the single `main_theorem` of §2.2 as the last declaration before the closing `end`
   and `end GMT.Ch04`.

Its text is the speculative draft's, with a docstring and one comment line added. The diff
against `84bf131` is `66 insertions(+), 46 deletions(-)`. No statement, definition, import or
other proof text changed.

## 7. Verification by the author

All checks used the pinned toolchain and the shared package tree `lake-packages-25730c7c`.

1. **Compilation.** `lean GMT/Ch04/Submission.lean` succeeds with exit status 0 and no error or
   warning (7.5 min wall time).
2. **Axioms.** `#print axioms GMT.Ch04.main_theorem` reports `[propext, Classical.choice, Quot.sound]`.
   With `set_option pp.universes true`, `#check @GMT.Ch04.main_theorem` shows no universe parameters.
3. **Child interfaces preserved.** For each of the 121 accepted DAG nodes, the frozen
   `lean_statement` was taken verbatim from `dag.json` and passed through the workflow's
   `validate_lean_statement`. It was elaborated in the contract scope that the child comparator
   replays: `contract_scope` of `gmt-compare.py`, that is, the contract's `open` lines,
   `namespace GMT.Ch04`, `noncomputable section` and `open RectifiableVarifold`. Each statement was
   proved by `exact Submission.<lean_name>`, as `theorem _root_.HumanizeNodeComparator.target_i`.
   All 121 type-check, and each reports only `[propext, Classical.choice, Quot.sound]`.
4. **Overlay hygiene.**
   - One `namespace GMT.Ch04` / `end GMT.Ch04`, and exactly one `main_theorem`.
   - No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `implemented_by`, `extern`, `native_decide`
     or `partial` in the code, with comments stripped.
   - 165 declarations, with no duplicate name.
   - Every blank-line-separated block of `Contract.lean` other than `main_theorem` occurs
     verbatim exactly once. The bare `end` line also occurs as a substring of `end Submission`
     and `end RectifiableVarifold`.
   - `Contract.lean`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` and `GMT.lean` are
     byte-identical to `ff75f52`.
   - Apart from `GMT/Ch04/Submission.lean` and this prose file, the only paths that differ from
     the frozen commit are workflow state under `.humanize-workspace/`. That is a dot-directory,
     which the comparator ignores.
5. **Overlay provenance.** Every top-level block of the candidate except the new `main_theorem` is
   byte-identical to a block of an accepted child solution commit, up to trailing blank lines.
   The import header is identical to that of the accepted child `root.tangent_structure-a1` (§6).
6. **Dependency extraction.** A Lean metaprogram run on the compiled candidate olean listed, for
   every constant of module `GMT.Ch04.Submission`, the constants used by its type and by its value
   (`ConstantInfo.value? (allowOpaque := true)`), following compiler-generated auxiliary
   declarations of the same module. This produced §4.1, Appendix A, the SimonGMT table of §4.2 and
   the "used" checks of §3 and §4.3.
7. **Comparator.** The exact configured command was run on the committed candidate; see §7.1.

### 7.1 Comparator result

The exact configured command was run from the worktree root on the committed candidate:
`env -u HF_TOKEN HUMANIZE_NODE_ID=root … python3 …/verifier/gmt-compare.py --lean-target GMT/Ch04/Submission.lean … --frozen-commit ff75f52a4c9deb3b3abbd91eb31d7b02e29a4cef root`,
with the configured `HUMANIZE_*` environment. **It passed.**

- **Candidate:** commit `73ff32799dea2666383f7ed85957fc270afb3351`, tree
  `e9c33cdca72d94aa650b22be173f39050a27ff87`. The comparator input `GMT/Ch04/Submission.lean` has
  sha256 `0c7c9e70d89068b988578764887632c17d769ebc39d25d654fc3ff98ec3146d0`.
- **Result:** exit status 0. The wrapper printed "GMT comparator: comparator and Lean kernel
  accepted GMT.Ch04.main_theorem" and then the final line `Your solution is okay!`.
- **`result.json`:** `status: passed`; checks `exit_zero`, `lean_kernel_accepted` and
  `final_marker` all `true`; `post_check_failures: []`; verdict key
  `3cfe1e205bc49da65db1b377b4c078335fbef5cfa4815c10f5735e96c8e04ff5`.
- **Comparator config:** challenge `GMT.Ch04.Contract`, solution `GMT.Ch04.Submission`, theorem
  `GMT.Ch04.main_theorem`, permitted axioms `propext`, `Quot.sound` and `Classical.choice`. Nanoda
  was disabled, which is the wrapper's default for this campaign; the Lean-kernel check is
  mandatory.
- **Log tail:**
  ```
  Building GMT.Ch04.Contract … Build completed successfully (3010 jobs).
  Building GMT.Ch04.Submission … Build completed successfully (3244 jobs).
  Running Lean default kernel on solution.
  Lean default kernel accepts the solution
  Your solution is okay!
  ```
- **Evidence:** `cluster-state/verification/results/hoa58/20261012T152409Z-ch04-root-2996hgcy/`
  (started 2026-10-12T15:23:54Z, finished 15:42:11Z).

Commits after `73ff327` change only this prose file. That file is not a comparator input: the
wrapper reads only `.lean` files and the build inputs. The verdict therefore applies to those
commits unchanged.

The previous candidate `84bf131` was rejected; see §5 and §6.

## 8. Reference use

There is exactly one entry, and its source is `local-project`.

- **source:** `local-project`
- **snapshot:** `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e`.
  Its `manifest.json` records mode `local-project`, project
  `ff75f52a4c9deb3b3abbd91eb31d7b02e29a4cef` and Mathlib `25730c7c759d108ef87ab70af2342a196760f79d`.
- **queries** (paths relative to the snapshot unless stated):
  - `cat manifest.json` → the three fields above.
  - `rg -n "^theorem main_theorem|^namespace|^end|^open|^noncomputable section|^variable" project/GMT/Ch04/Contract.lean`
    → `open` at 32–33, `namespace GMT.Ch04` at 35, `noncomputable section` at 37,
    `variable {n ℓ : ℕ}` at 45, `namespace RectifiableVarifold` at 100, `open Classical in` at 122,
    `end RectifiableVarifold` at 187, `open RectifiableVarifold` at 189,
    `theorem main_theorem … := by sorry` at 437, `end` at 439, `end GMT.Ch04` at 441. Of these, the
    interface check of §7 (item 3) replays the `open`, `namespace`, `noncomputable section` and
    `RectifiableVarifold` scope commands, as the child comparator's `contract_scope` does.
  - `sha256sum project/GMT/Ch04/Contract.lean project/GMT/Ch04/Submission.lean <candidate>/GMT/Ch04/Contract.lean`
    → all three are `6e58e5dddd9625ccb2898e58a3d39eab0b036f027f9b415f51d8702aa0f4770b`. The
    snapshot's `Submission.lean` is the unsolved contract copy (`rg -c sorry` → 1).
  - `cmp` of `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `GMT.lean` and
    `GMT/Ch04/Contract.lean` between the snapshot project and the candidate → identical.
  - `rg -n "Submission\.(rectifiable_lipschitz_piece_cover|tangent_structure_first_variation|stationary_iff_variational_of_first_variation|radial_first_variation|weighted_monotonicity_identity|stationary_monotonicity_density|mean_curvature_monotonicity|canonical_representatives|poincare_inequality|sobolev_inequality|support_in_ball_convex_hull|classical_tangent)" project`
    → **no match** (exit status 1). The accepted children exist only on the run's branches, not
    in the snapshot. A broader `rg -n "Submission\." project/GMT` matches only README prose
    (`GMT/Ch0{1,2,4,5,8}/README.md`).
  - `cat project/GMT/Ch04/README.md` → the statement map, errata and the reuse warning about
    SimonGMT `Chapter04.RectifiableVarifold` used in §1 and §4.2.
  - `git -C mathlib rev-parse HEAD` and `git -C lake-packages-25730c7c/mathlib rev-parse HEAD`
    → both `25730c7c759d108ef87ab70af2342a196760f79d`.
  - `git -C mathlib grep -n -E "^(theorem|lemma|def|…) (Besicovitch\.)?(ae_tendsto_measure_inter_div|exists_disjoint_subfamily_covering_enlargement_closedBall|hausdorffMeasure_le_liminf_tsum|exists_partition_approximatesLinearOn_of_hasFDerivWithinAt|addHaar_image_linearMap|…)\b" HEAD -- Mathlib`,
    followed by looser patterns for declarations with namespace prefixes, `_root_.` or `alias`.
    `git grep` was used because a recursive `rg` over the whole Mathlib tree on this file system
    exceeds the two-minute command limit. The results are the Mathlib `file:line` citations of
    §3, among them:
    - `Covering/Besicovitch.lean:1105`, `Covering/Vitali.lean:158`, `Measure/Hausdorff.lean:555`;
    - `Function/Jacobian.lean:255`, `Measure/Lebesgue/EqHaar.lean:297,500`,
      `Calculus/Rademacher.lean:385`;
    - `Geometry/Euclidean/Volume/Measure.lean:131,141,187`,
      `Integral/RieszMarkovKakutani/Real.lean:412`, `Measure/Regular.lean:385,843,1036`,
      `Measure/MeasureSpaceDef.lean:219`, `Calculus/FDeriv/Measurable.lean:378`;
    - `Integral/Layercake.lean:478,496`, `Integral/Prod.lean:297,478`, `Measure/Prod.lean:1071`,
      `Calculus/ParametricIntegral.lean:286`, `IntervalIntegral/FundThmCalculus.lean:1148`,
      `Integral/DominatedConvergence.lean:57,483`, `Integral/Bochner/Basic.lean:467,1230`,
      `Integral/Bochner/ContinuousLinearMap.lean:311`;
    - `Matrix/SchurComplement.lean:400`, `ContDiff/Convolution.lean:61,427`,
      `Analysis/Convolution.lean:814`, `InverseFunctionTheorem/ApproximatesLinearOn.lean:428`,
      `ContDiff/Operations.lean:940`;
    - `Convex/Combination.lean:414,428`, `Dimension/Finite.lean:305`,
      `Projection/Minimal.lean:36`, `Normed/Ring/Units.lean:183`, `Calculus/MeanValue.lean:526`,
      `Normed/Module/FiniteDimension.lean:231`, `Topology/Bases.lean:364`, `PiL2.lean:572`,
      `ImproperIntegrals.lean:178` and `Integrals/Basic.lean:146`.
  - In the pinned package `lake-packages-25730c7c/simongmt` (not part of the snapshot):
    - `git rev-parse HEAD` → `2b3663083f3fe399b6296fb8eaee52169170e197`, as in
      `project/lake-manifest.json`;
    - `grep -rn -E "^(theorem|lemma|def|noncomputable def|abbrev) (areaRegularSet|…|support_euclideanHausdorffMeasure_restrict_submodule)\b" Poincare/SimonGMT/`
      → the locations in §4.2.
  - `grep` of `GMT/Ch04/Submission.lean` (comments stripped) for the SimonGMT names cited in the
    reviewed child prose (`weighted_area_formula_lipschitz_injOn`,
    `exists_isClosed_continuousOn_of_measurable`, `ae_dimensionalUpperDensity_eq_zero_outside`,
    `simon_theorem_3_3`, `simonHausdorffMeasureReal`, `rademacher`) → **no match**. Together with
    the dependency extraction of §7, this is the basis of the table in §4.3.
  - For each Mathlib citation whose short name is declared more than once, an `awk` scan of the
    `namespace`/`section`/`end` lines up to the cited line → the cited line declares exactly the
    constant that the proofs use. For example, `MeasureTheory.integral_integral_swap` is
    `Integral/Prod.lean:478`, not `MeasureTheory.VectorMeasure.integral_integral_swap`
    (`VectorMeasure/Prod.lean:434`). Likewise `MeasureTheory.continuousOn_of_dominated` is
    `Bochner/Basic.lean:467`, not `VectorMeasure/Integral.lean:758`, and the root-namespace
    `hasDerivAt_integral_of_dominated_loc_of_deriv_le` is `Calculus/ParametricIntegral.lean:286`,
    not the `intervalIntegral` version.
- **files inspected:**
  - `local-references/12153e28d102be5e/manifest.json`;
  - in `project/`: `GMT/Ch04/Contract.lean`, `GMT/Ch04/Submission.lean`, `GMT/Ch04/README.md`,
    and, by `cmp`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` and `GMT.lean`;
  - in `mathlib/Mathlib/`, examined at the cited lines for the namespace check:
    - `MeasureTheory/Integral/Bochner/Basic.lean`, `MeasureTheory/Integral/DominatedConvergence.lean`,
      `MeasureTheory/Integral/Prod.lean`, `MeasureTheory/Measure/Prod.lean`;
    - `MeasureTheory/VectorMeasure/Integral.lean`, `MeasureTheory/VectorMeasure/Prod.lean`;
    - `Analysis/Calculus/InverseFunctionTheorem/ApproximatesLinearOn.lean`,
      `Analysis/Calculus/ParametricIntegral.lean`,
      `MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`, `Analysis/Normed/Ring/Units.lean`;
    - `MeasureTheory/Measure/Lebesgue/EqHaar.lean`, `MeasureTheory/Measure/Hausdorff.lean`,
      `Analysis/Convolution.lean`, `MeasureTheory/Integral/Layercake.lean`,
      `MeasureTheory/Measure/MeasureSpaceDef.lean`, `Analysis/InnerProductSpace/PiL2.lean`;
    - `Analysis/Calculus/MeanValue.lean` and `Analysis/Convex/Combination.lean`;
  - in `lake-packages-25730c7c/simongmt/Poincare/SimonGMT/`: `Chapter02/AreaLipschitz.lean`,
    `Chapter02/Lipschitz.lean`, `Chapter03/Rectifiable.lean`, `Chapter04/Basic.lean` (a grep hit for
    an unrelated `CountablyRectifiable` abbreviation, not used) and `Chapter01/Lusin.lean` (namespace
    check).
- **conclusion:** The snapshot contract is byte-identical to the candidate's `Contract.lean`, and
  the project and Mathlib revisions match the build. No accepted child declaration exists in the
  snapshot. Every library declaration that the final proofs reuse is located at the pinned
  revisions, and the axiom check of `main_theorem` covers all of them.

## 9. Citations

- L. Simon, *Introduction to Geometric Measure Theory*, Tsinghua lecture notes, 2014, Ch. 4
  (printed pp. 85–102), with Ch. 1–3. The run's read-only copy is `book/chapter-04.txt`; a later
  revision of the text is at https://math.stanford.edu/~lms/ntu-gmt-text.pdf.
- W. K. Allard, *On the first variation of a varifold*, Ann. of Math. (2) **95** (1972), 417–491,
  doi:10.2307/1970868. This is the origin of the monotonicity and first-variation theory of
  Ch. 4, §§2–4, cited for background only.
- J. H. Michael and L. M. Simon, *Sobolev and mean-value inequalities on generalized submanifolds
  of ℝⁿ*, Comm. Pure Appl. Math. (1973). This is the origin of 5.7, cited for background only.
- The Mathlib community, Mathlib at `25730c7c759d108ef87ab70af2342a196760f79d`, and the SimonGMT
  library at `2b3663083f3fe399b6296fb8eaee52169170e197` (repository
  `ZhengyangZhang06/gmt-formalize`, branch `simongmt-library`). These are the reused declarations
  of §3 and §4.2.

## Appendix A. The 121 accepted declarations (topological order in the candidate)

"Line" is the line of the `theorem` keyword in `GMT/Ch04/Submission.lean` at `73ff327`. The last
column comes from the dependency extraction (§7, item 6). `main_theorem` (line 11564) follows them
all.

| # | Line | Declaration (`GMT.Ch04.Submission.*`) | DAG node | Issue | PR | Direct `Submission.*` references in its proof |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | 441 | `ts_pwb_pair_weight_integral` | `root.tangent_structure-a1.piece_weighted_blowup-a1.pair_weight_integral-a1` | #820 | #1573 | — |
| 2 | 480 | `ts_pwb_upper_density_vanish_ae` | `root.tangent_structure-a1.piece_weighted_blowup-a1.upper_density_vanish-a1` | #825 | #1574 | — |
| 3 | 627 | `ts_pwb_lusin_compact_cover` | `root.tangent_structure-a1.piece_weighted_blowup-a1.lusin_compact_cover-a1` | #833 | #1417 | — |
| 4 | 705 | `ts_pwb_density_points_of_image_ae` | `root.tangent_structure-a1.piece_weighted_blowup-a1.density_point_image-a1` | #838 | #1565 | — |
| 5 | 730 | `ts_pdb_image_closedBall_measure_le` | `root.tangent_structure-a1.piece_density_blowup-a1.image_ball_bound-a1` | #746 | #1556 | — |
| 6 | 764 | `ts_pdb_piece_area_formula` | `root.tangent_structure-a1.piece_density_blowup-a1.piece_area_formula-a1` | #748 | #1575 | — |
| 7 | 1496 | `ts_fv_cv_first_order_regularity` | `root.tangent_structure-a1.first_variation_pieces-a1.variation_bounds-a1.first_order_regularity-a1` | #1194 | #1796 | — |
| 8 | 1567 | `compactVariation_velocity_isTestField` | `root.stationary_iff_variational-a1.variation_velocity_test_field-a1` | #202 | #345 | — |
| 9 | 1608 | `ts_fv_cv_slice_fderiv_bounds` | `root.tangent_structure-a1.first_variation_pieces-a1.variation_bounds-a1.slice_fderiv_bounds-a1` | #1196 | #1454 | — |
| 10 | 1697 | `ts_fv_cv_slice_fderiv_time_deriv` | `root.tangent_structure-a1.first_variation_pieces-a1.variation_bounds-a1.slice_fderiv_time_deriv-a1` | #1197 | #1842 | — |
| 11 | 1883 | `ts_fv_compact_variation_bounds` | `root.tangent_structure-a1.first_variation_pieces-a1.variation_bounds-a1` | #884 | #1856 | `ts_fv_cv_first_order_regularity`, `ts_fv_cv_slice_fderiv_bounds`, `ts_fv_cv_slice_fderiv_time_deriv` |
| 12 | 1905 | `ts_fv_det_tangential_gram_eq` | `root.tangent_structure-a1.first_variation_pieces-a1.image_mass_area_formula-a1.det_tangential_gram-a1` | #1220 | #1476 | — |
| 13 | 1966 | `ts_fv_piece_image_area_formula` | `root.tangent_structure-a1.first_variation_pieces-a1.image_mass_area_formula-a1.piece_image_area_formula-a1` | #1221 | #1841 | `ts_fv_det_tangential_gram_eq` |
| 14 | 2740 | `ts_pdb_linear_range_integral` | `root.tangent_structure-a1.piece_density_blowup-a1.linear_range_integral-a1` | #751 | #1581 | — |
| 15 | 2758 | `ts_pdb_density_complement_vanish` | `root.tangent_structure-a1.piece_density_blowup-a1.density_complement-a1` | #752 | #1532 | — |
| 16 | 2822 | `ts_pdb_density_point_rescaled_limit` | `root.tangent_structure-a1.piece_density_blowup-a1.rescaled_limit-a1` | #753 | #1586 | `ts_pdb_density_complement_vanish` |
| 17 | 3051 | `ts_piece_density_blowup` | `root.tangent_structure-a1.piece_density_blowup-a1` | #291 | #1723 | `ts_pdb_density_point_rescaled_limit`, `ts_pdb_image_closedBall_measure_le`, `ts_pdb_linear_range_integral`, `ts_pdb_piece_area_formula` |
| 18 | 3101 | `ts_approx_tangent_plane_unique` | `root.tangent_structure-a1.approx_tangent_unique-a1` | #293 | #554 | — |
| 19 | 3134 | `ts_plane_closedBall_measure` | `root.tangent_structure-a1.blowup_density-a1.plane_ball_measure-a1` | #778 | #1585 | — |
| 20 | 3167 | `ts_blowup_cutoff_closedBall_bounds` | `root.tangent_structure-a1.blowup_density-a1.cutoff_ball_bounds-a1` | #780 | #1582 | — |
| 21 | 3203 | `ts_unit_ball_plane_cutoff_approx` | `root.tangent_structure-a1.blowup_density-a1.plane_cutoff_approx-a1` | #782 | #1818 | `ts_plane_closedBall_measure` |
| 22 | 3310 | `ts_blowup_closedBall_density` | `root.tangent_structure-a1.blowup_density-a1` | #295 | #1849 | `ts_blowup_cutoff_closedBall_bounds`, `ts_unit_ball_plane_cutoff_approx` |
| 23 | 3346 | `ts_blowup_weighted_tangent` | `root.tangent_structure-a1.blowup_weighted_tangent-a1` | #297 | #600 | — |
| 24 | 3433 | `ts_fv_lintegral_image_eq_of_pieces` | `root.tangent_structure-a1.first_variation_pieces-a1.image_mass_area_formula-a1.image_lintegral_gluing-a1` | #1225 | #1447 | — |
| 25 | 3474 | `ts_fv_image_mass_area_formula` | `root.tangent_structure-a1.first_variation_pieces-a1.image_mass_area_formula-a1` | #886 | #1870 | `ts_fv_lintegral_image_eq_of_pieces`, `ts_fv_piece_image_area_formula` |
| 26 | 3581 | `ts_fv_det_ge_pow_of_quadForm_ge` | `root.tangent_structure-a1.first_variation_pieces-a1.jacobian_derivative-a1.det_lower_bound-a1` | #1129 | #1852 | — |
| 27 | 3711 | `ts_fv_hasDerivAt_det_of_entries` | `root.tangent_structure-a1.first_variation_pieces-a1.jacobian_derivative-a1.jacobi_formula-a1` | #1130 | #1820 | — |
| 28 | 3784 | `ts_fv_sum_inner_starProjection_eq_trace` | `root.tangent_structure-a1.first_variation_pieces-a1.jacobian_derivative-a1.projection_trace-a1` | #1131 | #1440 | — |
| 29 | 3807 | `ts_fv_tangential_matrix_estimates` | `root.tangent_structure-a1.first_variation_pieces-a1.jacobian_derivative-a1.tangential_estimates-a1` | #1132 | #1816 | — |
| 30 | 3892 | `ts_fv_tangential_jacobian_hasDerivAt` | `root.tangent_structure-a1.first_variation_pieces-a1.jacobian_derivative-a1` | #889 | #1876 | `ts_fv_det_ge_pow_of_quadForm_ge`, `ts_fv_hasDerivAt_det_of_entries`, `ts_fv_sum_inner_starProjection_eq_trace`, `ts_fv_tangential_matrix_estimates` |
| 31 | 4074 | `ts_fv_hasDerivAt_of_weighted_jacobian` | `root.tangent_structure-a1.first_variation_pieces-a1.weighted_integral_derivative-a1` | #892 | #1498 | — |
| 32 | 4147 | `ts_first_variation_of_pieces` | `root.tangent_structure-a1.first_variation_pieces-a1` | #299 | #1935 | `ts_fv_compact_variation_bounds`, `ts_fv_hasDerivAt_of_weighted_jacobian`, `ts_fv_image_mass_area_formula`, `ts_fv_tangential_jacobian_hasDerivAt` |
| 33 | 4218 | `ts_pwb_blowup_at_good_point` | `root.tangent_structure-a1.piece_weighted_blowup-a1.good_point_blowup-a1` | #843 | #1571 | `ts_pwb_pair_weight_integral` |
| 34 | 4419 | `ts_piece_weighted_blowup_ae` | `root.tangent_structure-a1.piece_weighted_blowup-a1` | #292 | #1784 | `ts_piece_density_blowup`, `ts_pwb_blowup_at_good_point`, `ts_pwb_density_points_of_image_ae`, `ts_pwb_lusin_compact_cover`, `ts_pwb_pair_weight_integral`, `ts_pwb_upper_density_vanish_ae` |
| 35 | 4468 | `ts_starProjection_range_continuousOn_injective` | `root.tangent_structure-a1.piece_tangent_field-a1.projection_continuity-a1` | #856 | #1584 | — |
| 36 | 4548 | `ts_piece_projection_continuousOn_image` | `root.tangent_structure-a1.piece_tangent_field-a1.piece_projection_continuity-a1` | #860 | #1580 | `ts_starProjection_range_continuousOn_injective` |
| 37 | 4585 | `ts_stronglyMeasurable_paste_continuousOn` | `root.tangent_structure-a1.piece_tangent_field-a1.borel_pasting-a1` | #865 | #1576 | — |
| 38 | 4625 | `ts_piece_tangent_projection_field` | `root.tangent_structure-a1.piece_tangent_field-a1` | #298 | #1431 | `ts_piece_projection_continuousOn_image`, `ts_stronglyMeasurable_paste_continuousOn` |
| 39 | 4651 | `injective_fderiv_local_lower_bound` | `root.lipschitz_pieces-a1.regular_set_cover-a1.pointwise_lower_bound-a1` | #246 | #524 | — |
| 40 | 4682 | `lower_lipschitz_cover_of_local_bound` | `root.lipschitz_pieces-a1.regular_set_cover-a1.local_bound_cover-a1` | #248 | #479 | — |
| 41 | 4727 | `regular_set_lower_lipschitz_cover` | `root.lipschitz_pieces-a1.regular_set_cover-a1` | #145 | #700 | `injective_fderiv_local_lower_bound`, `lower_lipschitz_cover_of_local_bound` |
| 42 | 4746 | `lusin_compact_exhaustion_of_measurable` | `root.lipschitz_pieces-a1.lusin_exhaustion-a1` | #146 | #305 | — |
| 43 | 4803 | `lipschitz_range_piece_cover` | `root.lipschitz_pieces-a1.single_map_cover-a1` | #148 | #991 | `lusin_compact_exhaustion_of_measurable`, `regular_set_lower_lipschitz_cover` |
| 44 | 4856 | `exists_isCompactVariation_add_smul` | `root.stationary_iff_variational-a1.linear_compact_variation-a1` | #203 | #437 | — |
| 45 | 4935 | `exists_smooth_approx_testField_fderiv` | `root.stationary_iff_variational-a1.smooth_c1_approximation-a1` | #204 | #415 | — |
| 46 | 5015 | `tendsto_integral_tangentialDiv_of_tendstoUniformly_fderiv` | `root.stationary_iff_variational-a1.first_variation_continuity-a1` | #205 | #421 | — |
| 47 | 5118 | `stationary_iff_variational_of_first_variation` | `root.stationary_iff_variational-a1` | #56 | #725 | `compactVariation_velocity_isTestField`, `exists_isCompactVariation_add_smul`, `exists_smooth_approx_testField_fderiv`, `tendsto_integral_tangentialDiv_of_tendstoUniformly_fderiv` |
| 48 | 5156 | `rectifiable_lipschitz_piece_cover` | `root.lipschitz_pieces-a1` | #54 | #1063 | `lipschitz_range_piece_cover` |
| 49 | 5195 | `tangent_structure_first_variation` | `root.tangent_structure-a1` | #55 | #2170 | `rectifiable_lipschitz_piece_cover`, `ts_approx_tangent_plane_unique`, `ts_blowup_closedBall_density`, `ts_blowup_weighted_tangent`, `ts_first_variation_of_pieces`, `ts_piece_tangent_projection_field`, `ts_piece_weighted_blowup_ae` |
| 50 | 5320 | `backward_integral_gronwall_Ioc` | `root.poincare_inequality-a1.integral_gronwall-a1` | #384 | #764 | — |
| 51 | 5402 | `smooth_step_truncation_exists` | `root.poincare_inequality-a1.smooth_truncation-a1` | #387 | #932 | — |
| 52 | 5473 | `closedBall_rpow_kernel_lintegral_le_of_growth` | `root.poincare_inequality-a1.kernel_bound-a1` | #389 | #791 | — |
| 53 | 5586 | `layer_cake_tonelli_truncation_bound` | `root.poincare_inequality-a1.layer_cake_bound-a1` | #394 | #816 | — |
| 54 | 5690 | `bounded_curvature_ball_average_estimate` | `root.poincare_inequality-a1.ball_average_estimate-a1` | #396 | #1509 | `backward_integral_gronwall_Ioc` |
| 55 | 6018 | `density_point_mean_value_estimate` | `root.poincare_inequality-a1.mean_value_estimate-a1` | #399 | #1722 | `bounded_curvature_ball_average_estimate` |
| 56 | 6112 | `tangentialGradient_comp_of_differentiableAt` | `root.poincare_inequality-a1.gradient_chain_rule-a1` | #401 | #771 | — |
| 57 | 6123 | `classical_tangent_uniform_lower_density` | `root.classical_tangent-a1.uniform_lower_density-a1` | #180 | #381 | — |
| 58 | 6290 | `classical_tangent_off_plane_mass_decay` | `root.classical_tangent-a1.off_plane_mass_decay-a1` | #181 | #369 | — |
| 59 | 6366 | `classical_tangent_support_flatness` | `root.classical_tangent-a1.support_flatness-a1` | #182 | #356 | — |
| 60 | 6450 | `hausdorff_null_of_measure_null_density_ge` | `root.canonical_representatives-a1.hausdorff_null_density-a1` | #183 | #495 | — |
| 61 | 6555 | `canonicalCarrier_rectifiablePair_weight` | `root.canonical_representatives-a1.canonical_pair_weight-a1` | #184 | #1085 | `hausdorff_null_of_measure_null_density_ge` |
| 62 | 6625 | `canonicalCarrier_closed_support` | `root.canonical_representatives-a1.canonical_closed_support-a1` | #185 | #418 | — |
| 63 | 6690 | `stationary_ratio_limit_of_annulus_identity` | `root.stationary_monotonicity-a1.ratio_limit-a1` | #253 | #501 | — |
| 64 | 6830 | `stationary_density_usc_of_ratio_bound` | `root.stationary_monotonicity-a1.density_usc-a1` | #254 | #464 | — |
| 65 | 6877 | `mcm_unit_weight_identity` | `root.curvature_monotonicity-a1.unit_identity-a1` | #206 | #507 | — |
| 66 | 6898 | `mcm_primitive_radial_fubini` | `root.curvature_monotonicity-a1.annulus_ibp-a1.primitive_fubini-a1` | #468 | #1539 | — |
| 67 | 6964 | `mcm_exp_neg_integral_ftc` | `root.curvature_monotonicity-a1.exp_integral_ftc-a1` | #208 | #459 | — |
| 68 | 7167 | `mcm_density_usc_of_monotone` | `root.curvature_monotonicity-a1.density_usc-a1` | #209 | #497 | — |
| 69 | 7311 | `mcm_log_error_of_identity` | `root.curvature_monotonicity-a1.log_error-a1` | #212 | #362 | — |
| 70 | 7364 | `mcm_lp_holder_bound` | `root.curvature_monotonicity-a1.lp_holder_bound-a1` | #213 | #417 | — |
| 71 | 7452 | `mcm_lp_density_of_monotonicity` | `root.curvature_monotonicity-a1.lp_density-a1` | #215 | #694 | `mcm_density_usc_of_monotone` |
| 72 | 7514 | `mcm_annulus_primitive_fubini` | `root.curvature_monotonicity-a1.annulus_ibp-a1.annulus_fubini-a1` | #469 | #1047 | `mcm_primitive_radial_fubini` |
| 73 | 7549 | `mcm_interval_primitive_fubini` | `root.curvature_monotonicity-a1.annulus_ibp-a1.interval_fubini-a1` | #470 | #983 | `mcm_primitive_radial_fubini` |
| 74 | 7575 | `mcm_annulus_integration_by_parts` | `root.curvature_monotonicity-a1.annulus_ibp-a1` | #207 | #1526 | `mcm_annulus_primitive_fubini`, `mcm_interval_primitive_fubini` |
| 75 | 7641 | `mcm_bounded_curvature_of_identity` | `root.curvature_monotonicity-a1.bounded_curvature-a1` | #210 | #1382 | `mcm_annulus_integration_by_parts`, `mcm_density_usc_of_monotone`, `mcm_exp_neg_integral_ftc` |
| 76 | 7859 | `mcm_lp_monotonicity_of_identity` | `root.curvature_monotonicity-a1.lp_monotonicity-a1` | #214 | #1726 | `mcm_annulus_integration_by_parts`, `mcm_exp_neg_integral_ftc`, `mcm_lp_holder_bound` |
| 77 | 8118 | `sobolev_truncation_superlevel_bound` | `root.sobolev_inequality-a1.truncation_layer_cake-a1.truncation_bound-a1` | #540 | #1543 | — |
| 78 | 8217 | `sobolev_level_moment_factor` | `root.sobolev_inequality-a1.truncation_layer_cake-a1.level_integral_bound-a1.moment_factor-a1` | #1049 | #1502 | — |
| 79 | 8264 | `sobolev_level_energy_tonelli` | `root.sobolev_inequality-a1.truncation_layer_cake-a1.level_integral_bound-a1.energy_tonelli-a1` | #1052 | #1551 | — |
| 80 | 8422 | `sobolev_level_layer_cake` | `root.sobolev_inequality-a1.truncation_layer_cake-a1.level_integral_bound-a1.layer_cake-a1` | #1055 | #1865 | — |
| 81 | 8510 | `sobolev_level_integral_bound` | `root.sobolev_inequality-a1.truncation_layer_cake-a1.level_integral_bound-a1` | #543 | #1942 | `sobolev_level_energy_tonelli`, `sobolev_level_layer_cake`, `sobolev_level_moment_factor` |
| 82 | 8560 | `sobolev_of_level_integral_bounds` | `root.sobolev_inequality-a1.truncation_layer_cake-a1.shift_limit-a1` | #547 | #1465 | — |
| 83 | 8654 | `sobolev_energy_integrable` | `root.sobolev_inequality-a1.energy_integrable-a1` | #228 | #439 | — |
| 84 | 8689 | `sobolev_density_ge_one_ae` | `root.sobolev_inequality-a1.density_lower_bound-a1` | #229 | #431 | — |
| 85 | 8714 | `sobolev_good_radius_calculus` | `root.sobolev_inequality-a1.good_radius_calculus-a1` | #230 | #499 | — |
| 86 | 8877 | `sobolev_monotonicity_inequality` | `root.sobolev_inequality-a1.monotonicity_inequality-a1` | #231 | #1590 | `sobolev_energy_integrable` |
| 87 | 8957 | `sobolev_covering_inequality` | `root.sobolev_inequality-a1.covering_inequality-a1` | #232 | #709 | `sobolev_good_radius_calculus` |
| 88 | 9132 | `sobolev_of_superlevel_inequality` | `root.sobolev_inequality-a1.truncation_layer_cake-a1` | #233 | #2029 | `sobolev_energy_integrable`, `sobolev_level_integral_bound`, `sobolev_of_level_integral_bounds`, `sobolev_truncation_superlevel_bound` |
| 89 | 9170 | `weighted_mono_local_data` | `root.weighted_monotonicity-a1.cutoff_first_variation-a1.local_data-a1` | #714 | #1572 | — |
| 90 | 9307 | `weighted_mono_cutoff_identity` | `root.weighted_monotonicity-a1.cutoff_first_variation-a1.cutoff_identity-a1` | #715 | #1493 | — |
| 91 | 9428 | `weighted_mono_radial_test_field` | `root.weighted_monotonicity-a1.radial_test_field-a1` | #283 | #682 | — |
| 92 | 9474 | `weighted_mono_cutoff_first_variation` | `root.weighted_monotonicity-a1.cutoff_first_variation-a1` | #284 | #1725 | `weighted_mono_cutoff_identity`, `weighted_mono_local_data`, `weighted_mono_radial_test_field` |
| 93 | 9506 | `wm_smoothed_scale_integral_continuousOn` | `root.weighted_monotonicity-a1.smoothed_identity-a1.scale_continuity-a1` | #567 | #1523 | — |
| 94 | 9559 | `wm_smoothed_kernel_fubini` | `root.weighted_monotonicity-a1.smoothed_identity-a1.kernel_fubini-a1` | #568 | #1860 | — |
| 95 | 9639 | `wm_smoothed_scaled_ftc` | `root.weighted_monotonicity-a1.smoothed_identity-a1.scaled_ftc-a1` | #570 | #1547 | — |
| 96 | 9681 | `weighted_mono_cutoff_hasDerivAt` | `root.weighted_monotonicity-a1.cutoff_integral_deriv-a1` | #285 | #1518 | — |
| 97 | 9808 | `weighted_mono_cutoff_seq_exists` | `root.weighted_monotonicity-a1.cutoff_limit-a1.cutoff_seq-a1` | #632 | #1579 | — |
| 98 | 9838 | `weighted_mono_cutoff_integral_tendsto` | `root.weighted_monotonicity-a1.cutoff_limit-a1.cutoff_integral-a1` | #635 | #1578 | — |
| 99 | 9902 | `weighted_mono_kernel_limit` | `root.weighted_monotonicity-a1.cutoff_limit-a1.kernel_limit-a1` | #637 | #1583 | — |
| 100 | 10004 | `weighted_mono_kernel_term_tendsto` | `root.weighted_monotonicity-a1.cutoff_limit-a1.kernel_term-a1` | #638 | #981 | — |
| 101 | 10085 | `weighted_mono_curvature_term_tendsto` | `root.weighted_monotonicity-a1.cutoff_limit-a1.curvature_term-a1` | #639 | #1415 | `weighted_mono_cutoff_integral_tendsto` |
| 102 | 10184 | `weighted_mono_kernel_bounds` | `root.weighted_monotonicity-a1.kernel_bounds-a1` | #287 | #525 | — |
| 103 | 10279 | `weighted_mono_smoothed_identity` | `root.weighted_monotonicity-a1.smoothed_identity-a1` | #288 | #1877 | `weighted_mono_cutoff_hasDerivAt`, `wm_smoothed_kernel_fubini`, `wm_smoothed_scale_integral_continuousOn`, `wm_smoothed_scaled_ftc` |
| 104 | 10358 | `weighted_mono_cutoff_limit` | `root.weighted_monotonicity-a1.cutoff_limit-a1` | #289 | #1724 | `weighted_mono_curvature_term_tendsto`, `weighted_mono_cutoff_integral_tendsto`, `weighted_mono_cutoff_seq_exists`, `weighted_mono_kernel_bounds`, `weighted_mono_kernel_limit`, `weighted_mono_kernel_term_tendsto` |
| 105 | 10414 | `exists_radial_cutoff_test_field` | `root.support_convex_hull-a1.support_in_ball-a1.radial_cutoff_test_field-a1` | #583 | #1577 | — |
| 106 | 10460 | `aestronglyMeasurable_normalRadialSq_and_bounds` | `root.support_convex_hull-a1.support_in_ball-a1.normal_radial_measurable-a1` | #587 | #1487 | — |
| 107 | 10493 | `support_subset_closedBall_of_radial_identity` | `root.support_convex_hull-a1.support_in_ball-a1.radial_vanishing-a1` | #589 | #1561 | — |
| 108 | 10609 | `support_in_ball_of_radial_first_variation` | `root.support_convex_hull-a1.support_in_ball-a1` | #235 | #1721 | `aestronglyMeasurable_normalRadialSq_and_bounds`, `exists_radial_cutoff_test_field`, `support_subset_closedBall_of_radial_identity` |
| 109 | 10659 | `convex_hull_property_of_support_in_ball` | `root.support_convex_hull-a1.convex_hull_from_ball-a1` | #237 | #577 | — |
| 110 | 10794 | `radial_vector_field_hasFDerivAt` | `root.radial_first_variation-a1.radial_derivative-a1` | #216 | #608 | — |
| 111 | 10830 | `trace_scalar_add_rankOne_comp_starProjection` | `root.radial_first_variation-a1.projection_trace-a1` | #217 | #426 | — |
| 112 | 10855 | `tangentialDiv_weighted_radial_field` | `root.radial_first_variation-a1.pointwise_divergence-a1` | #218 | #907 | `radial_vector_field_hasFDerivAt`, `trace_scalar_add_rankOne_comp_starProjection` |
| 113 | 10910 | `radial_first_variation` | `root.radial_first_variation-a1` | #57 | #1587 | `tangentialDiv_weighted_radial_field` |
| 114 | 10943 | `weighted_monotonicity_identity` | `root.weighted_monotonicity-a1` | #58 | #1943 | `radial_first_variation`, `weighted_mono_cutoff_first_variation`, `weighted_mono_cutoff_limit`, `weighted_mono_smoothed_identity` |
| 115 | 10970 | `stationary_monotonicity_density` | `root.stationary_monotonicity-a1` | #59 | #2019 | `stationary_density_usc_of_ratio_bound`, `stationary_ratio_limit_of_annulus_identity`, `weighted_monotonicity_identity` |
| 116 | 11032 | `mean_curvature_monotonicity` | `root.curvature_monotonicity-a1` | #60 | #2104 | `mcm_bounded_curvature_of_identity`, `mcm_log_error_of_identity`, `mcm_lp_density_of_monotonicity`, `mcm_lp_monotonicity_of_identity`, `mcm_unit_weight_identity`, `weighted_monotonicity_identity` |
| 117 | 11056 | `canonical_representatives` | `root.canonical_representatives-a1` | #61 | #2236 | `canonicalCarrier_closed_support`, `canonicalCarrier_rectifiablePair_weight`, `mean_curvature_monotonicity`, `stationary_monotonicity_density` |
| 118 | 11096 | `poincare_inequality` | `root.poincare_inequality-a1` | #62 | #2401 | `bounded_curvature_ball_average_estimate`, `canonical_representatives`, `closedBall_rpow_kernel_lintegral_le_of_growth`, `density_point_mean_value_estimate`, `layer_cake_tonelli_truncation_bound`, `mean_curvature_monotonicity`, `smooth_step_truncation_exists`, `tangentialGradient_comp_of_differentiableAt`, `weighted_monotonicity_identity` |
| 119 | 11470 | `sobolev_inequality` | `root.sobolev_inequality-a1` | #63 | #2113 | `sobolev_covering_inequality`, `sobolev_density_ge_one_ae`, `sobolev_energy_integrable`, `sobolev_monotonicity_inequality`, `sobolev_of_superlevel_inequality`, `weighted_monotonicity_identity` |
| 120 | 11523 | `support_in_ball_convex_hull` | `root.support_convex_hull-a1` | #64 | #1729 | `convex_hull_property_of_support_in_ball`, `radial_first_variation`, `support_in_ball_of_radial_first_variation` |
| 121 | 11536 | `classical_tangent` | `root.classical_tangent-a1` | #65 | #2323 | `canonical_representatives`, `classical_tangent_off_plane_mass_decay`, `classical_tangent_support_flatness`, `classical_tangent_uniform_lower_density`, `mean_curvature_monotonicity` |

## Appendix B. Record directories of the accepted nodes

Each record is `proofs/github/20261011t142930z-d646011318/<record>/` (`proof.md`, `contract.md`,
`lean-audit.json` and `verification.json`) on the branch
`proof-workspace/gmt-ch04/20261011t142930z-d646011318/theorems/solutions/<record>`.

| DAG node | Record directory (`proofs/github/20261011t142930z-d646011318/<record>/`) |
| --- | --- |
| `root.canonical_representatives-a1` | `root-canonical-representatives-a1-4b7c2d4536` |
| `root.canonical_representatives-a1.canonical_closed_support-a1` | `root-canonical-representatives-a1-canonical-closed-support-a1-98d3e08d0d` |
| `root.canonical_representatives-a1.canonical_pair_weight-a1` | `root-canonical-representatives-a1-canonical-pair-weight-a1-12e71f795c` |
| `root.canonical_representatives-a1.hausdorff_null_density-a1` | `root-canonical-representatives-a1-hausdorff-null-density-a1-5050faebb8` |
| `root.classical_tangent-a1` | `root-classical-tangent-a1-2d3c3e34e2` |
| `root.classical_tangent-a1.off_plane_mass_decay-a1` | `root-classical-tangent-a1-off-plane-mass-decay-a1-ceda7bb7da` |
| `root.classical_tangent-a1.support_flatness-a1` | `root-classical-tangent-a1-support-flatness-a1-7183a6691d` |
| `root.classical_tangent-a1.uniform_lower_density-a1` | `root-classical-tangent-a1-uniform-lower-density-a1-3419100769` |
| `root.curvature_monotonicity-a1` | `root-curvature-monotonicity-a1-be9b600039` |
| `root.curvature_monotonicity-a1.annulus_ibp-a1` | `root-curvature-monotonicity-a1-annulus-ibp-a1-80e1285a12` |
| `root.curvature_monotonicity-a1.annulus_ibp-a1.annulus_fubini-a1` | `root-curvature-monotonicity-a1-annulus-ibp-a1-annulus-fubini-a1-631cd36e7c` |
| `root.curvature_monotonicity-a1.annulus_ibp-a1.interval_fubini-a1` | `root-curvature-monotonicity-a1-annulus-ibp-a1-interval-fubini-a1-19fd25662f` |
| `root.curvature_monotonicity-a1.annulus_ibp-a1.primitive_fubini-a1` | `root-curvature-monotonicity-a1-annulus-ibp-a1-primitive-fubini-a1-00f22631e0` |
| `root.curvature_monotonicity-a1.bounded_curvature-a1` | `root-curvature-monotonicity-a1-bounded-curvature-a1-2426fe8be1` |
| `root.curvature_monotonicity-a1.density_usc-a1` | `root-curvature-monotonicity-a1-density-usc-a1-4d6290f999` |
| `root.curvature_monotonicity-a1.exp_integral_ftc-a1` | `root-curvature-monotonicity-a1-exp-integral-ftc-a1-544504f938` |
| `root.curvature_monotonicity-a1.log_error-a1` | `root-curvature-monotonicity-a1-log-error-a1-14cc4fbe5b` |
| `root.curvature_monotonicity-a1.lp_density-a1` | `root-curvature-monotonicity-a1-lp-density-a1-515f66a08a` |
| `root.curvature_monotonicity-a1.lp_holder_bound-a1` | `root-curvature-monotonicity-a1-lp-holder-bound-a1-bcba6e3cbc` |
| `root.curvature_monotonicity-a1.lp_monotonicity-a1` | `root-curvature-monotonicity-a1-lp-monotonicity-a1-19cc3a4c0c` |
| `root.curvature_monotonicity-a1.unit_identity-a1` | `root-curvature-monotonicity-a1-unit-identity-a1-90e260a074` |
| `root.lipschitz_pieces-a1` | `root-lipschitz-pieces-a1-2604677eaf` |
| `root.lipschitz_pieces-a1.lusin_exhaustion-a1` | `root-lipschitz-pieces-a1-lusin-exhaustion-a1-16576c277e` |
| `root.lipschitz_pieces-a1.regular_set_cover-a1` | `root-lipschitz-pieces-a1-regular-set-cover-a1-1da85b91a1` |
| `root.lipschitz_pieces-a1.regular_set_cover-a1.local_bound_cover-a1` | `root-lipschitz-pieces-a1-regular-set-cover-a1-local-bound-cover-a1-0f08d29aad` |
| `root.lipschitz_pieces-a1.regular_set_cover-a1.pointwise_lower_bound-a1` | `root-lipschitz-pieces-a1-regular-set-cover-a1-pointwise-lower-bound-a1-5dbd617e1b` |
| `root.lipschitz_pieces-a1.single_map_cover-a1` | `root-lipschitz-pieces-a1-single-map-cover-a1-77840ffef1` |
| `root.poincare_inequality-a1` | `root-poincare-inequality-a1-a376040713` |
| `root.poincare_inequality-a1.ball_average_estimate-a1` | `root-poincare-inequality-a1-ball-average-estimate-a1-b2789b7325` |
| `root.poincare_inequality-a1.gradient_chain_rule-a1` | `root-poincare-inequality-a1-gradient-chain-rule-a1-8404d9b170` |
| `root.poincare_inequality-a1.integral_gronwall-a1` | `root-poincare-inequality-a1-integral-gronwall-a1-86f481a311` |
| `root.poincare_inequality-a1.kernel_bound-a1` | `root-poincare-inequality-a1-kernel-bound-a1-09aefd57a8` |
| `root.poincare_inequality-a1.layer_cake_bound-a1` | `root-poincare-inequality-a1-layer-cake-bound-a1-410413d862` |
| `root.poincare_inequality-a1.mean_value_estimate-a1` | `root-poincare-inequality-a1-mean-value-estimate-a1-a2e3ea25d3` |
| `root.poincare_inequality-a1.smooth_truncation-a1` | `root-poincare-inequality-a1-smooth-truncation-a1-0ceeb0bb58` |
| `root.radial_first_variation-a1` | `root-radial-first-variation-a1-ea3800fd29` |
| `root.radial_first_variation-a1.pointwise_divergence-a1` | `root-radial-first-variation-a1-pointwise-divergence-a1-940d2b31e9` |
| `root.radial_first_variation-a1.projection_trace-a1` | `root-radial-first-variation-a1-projection-trace-a1-61a8b7597d` |
| `root.radial_first_variation-a1.radial_derivative-a1` | `root-radial-first-variation-a1-radial-derivative-a1-566690d091` |
| `root.sobolev_inequality-a1` | `root-sobolev-inequality-a1-29d902be27` |
| `root.sobolev_inequality-a1.covering_inequality-a1` | `root-sobolev-inequality-a1-covering-inequality-a1-42cec26d0b` |
| `root.sobolev_inequality-a1.density_lower_bound-a1` | `root-sobolev-inequality-a1-density-lower-bound-a1-e75759ece4` |
| `root.sobolev_inequality-a1.energy_integrable-a1` | `root-sobolev-inequality-a1-energy-integrable-a1-3ab6205423` |
| `root.sobolev_inequality-a1.good_radius_calculus-a1` | `root-sobolev-inequality-a1-good-radius-calculus-a1-861d848bae` |
| `root.sobolev_inequality-a1.monotonicity_inequality-a1` | `root-sobolev-inequality-a1-monotonicity-inequality-a1-9ed681648b` |
| `root.sobolev_inequality-a1.truncation_layer_cake-a1` | `root-sobolev-inequality-a1-truncation-layer-cake-a1-56656eacf8` |
| `root.sobolev_inequality-a1.truncation_layer_cake-a1.level_integral_bound-a1` | `root-sobolev-inequality-a1-truncation-layer-cake-a1-level-integral-bound-a1-3c3b81d7ea` |
| `root.sobolev_inequality-a1.truncation_layer_cake-a1.level_integral_bound-a1.energy_tonelli-a1` | `root-sobolev-inequality-a1-truncation-layer-cake-a1-level-integral-bo-2bd75605fb-2a79956620` |
| `root.sobolev_inequality-a1.truncation_layer_cake-a1.level_integral_bound-a1.layer_cake-a1` | `root-sobolev-inequality-a1-truncation-layer-cake-a1-level-integral-bo-4e69efe26e-f40075a3da` |
| `root.sobolev_inequality-a1.truncation_layer_cake-a1.level_integral_bound-a1.moment_factor-a1` | `root-sobolev-inequality-a1-truncation-layer-cake-a1-level-integral-bo-b0faa9c73e-976487daf8` |
| `root.sobolev_inequality-a1.truncation_layer_cake-a1.shift_limit-a1` | `root-sobolev-inequality-a1-truncation-layer-cake-a1-shift-limit-a1-67eac68fb6` |
| `root.sobolev_inequality-a1.truncation_layer_cake-a1.truncation_bound-a1` | `root-sobolev-inequality-a1-truncation-layer-cake-a1-truncation-bound-a1-a9f268e3bf` |
| `root.stationary_iff_variational-a1` | `root-stationary-iff-variational-a1-293054675e` |
| `root.stationary_iff_variational-a1.first_variation_continuity-a1` | `root-stationary-iff-variational-a1-first-variation-continuity-a1-c300cca0c4` |
| `root.stationary_iff_variational-a1.linear_compact_variation-a1` | `root-stationary-iff-variational-a1-linear-compact-variation-a1-5de9be365b` |
| `root.stationary_iff_variational-a1.smooth_c1_approximation-a1` | `root-stationary-iff-variational-a1-smooth-c1-approximation-a1-c1aad4886c` |
| `root.stationary_iff_variational-a1.variation_velocity_test_field-a1` | `root-stationary-iff-variational-a1-variation-velocity-test-field-a1-d2785ce8e1` |
| `root.stationary_monotonicity-a1` | `root-stationary-monotonicity-a1-f074818fcb` |
| `root.stationary_monotonicity-a1.density_usc-a1` | `root-stationary-monotonicity-a1-density-usc-a1-50219a7bd9` |
| `root.stationary_monotonicity-a1.ratio_limit-a1` | `root-stationary-monotonicity-a1-ratio-limit-a1-4c311b2ec5` |
| `root.support_convex_hull-a1` | `root-support-convex-hull-a1-37c1964191` |
| `root.support_convex_hull-a1.convex_hull_from_ball-a1` | `root-support-convex-hull-a1-convex-hull-from-ball-a1-138892b1d5` |
| `root.support_convex_hull-a1.support_in_ball-a1` | `root-support-convex-hull-a1-support-in-ball-a1-935dc91854` |
| `root.support_convex_hull-a1.support_in_ball-a1.normal_radial_measurable-a1` | `root-support-convex-hull-a1-support-in-ball-a1-normal-radial-measurable-a1-13ad691786` |
| `root.support_convex_hull-a1.support_in_ball-a1.radial_cutoff_test_field-a1` | `root-support-convex-hull-a1-support-in-ball-a1-radial-cutoff-test-field-a1-170a0c317e` |
| `root.support_convex_hull-a1.support_in_ball-a1.radial_vanishing-a1` | `root-support-convex-hull-a1-support-in-ball-a1-radial-vanishing-a1-37eb314591` |
| `root.tangent_structure-a1` | `root-tangent-structure-a1-8f1f47aeec` |
| `root.tangent_structure-a1.approx_tangent_unique-a1` | `root-tangent-structure-a1-approx-tangent-unique-a1-d03e5e4451` |
| `root.tangent_structure-a1.blowup_density-a1` | `root-tangent-structure-a1-blowup-density-a1-3db7b0512c` |
| `root.tangent_structure-a1.blowup_density-a1.cutoff_ball_bounds-a1` | `root-tangent-structure-a1-blowup-density-a1-cutoff-ball-bounds-a1-3acab8b7f3` |
| `root.tangent_structure-a1.blowup_density-a1.plane_ball_measure-a1` | `root-tangent-structure-a1-blowup-density-a1-plane-ball-measure-a1-74881643ef` |
| `root.tangent_structure-a1.blowup_density-a1.plane_cutoff_approx-a1` | `root-tangent-structure-a1-blowup-density-a1-plane-cutoff-approx-a1-9d0e917a5a` |
| `root.tangent_structure-a1.blowup_weighted_tangent-a1` | `root-tangent-structure-a1-blowup-weighted-tangent-a1-1d6240bd5c` |
| `root.tangent_structure-a1.first_variation_pieces-a1` | `root-tangent-structure-a1-first-variation-pieces-a1-2b25065918` |
| `root.tangent_structure-a1.first_variation_pieces-a1.image_mass_area_formula-a1` | `root-tangent-structure-a1-first-variation-pieces-a1-image-mass-area-formula-a1-7dd9fdb444` |
| `root.tangent_structure-a1.first_variation_pieces-a1.image_mass_area_formula-a1.det_tangential_gram-a1` | `root-tangent-structure-a1-first-variation-pieces-a1-image-mass-area-f-6c3c5ff75b-9ba72be651` |
| `root.tangent_structure-a1.first_variation_pieces-a1.image_mass_area_formula-a1.image_lintegral_gluing-a1` | `root-tangent-structure-a1-first-variation-pieces-a1-image-mass-area-f-a5f97e29ab-03de01c8ca` |
| `root.tangent_structure-a1.first_variation_pieces-a1.image_mass_area_formula-a1.piece_image_area_formula-a1` | `root-tangent-structure-a1-first-variation-pieces-a1-image-mass-area-f-8a75267b12-20b59fab54` |
| `root.tangent_structure-a1.first_variation_pieces-a1.jacobian_derivative-a1` | `root-tangent-structure-a1-first-variation-pieces-a1-jacobian-derivative-a1-d78101e959` |
| `root.tangent_structure-a1.first_variation_pieces-a1.jacobian_derivative-a1.det_lower_bound-a1` | `root-tangent-structure-a1-first-variation-pieces-a1-jacobian-derivati-ff844f2cab-2ae9a79291` |
| `root.tangent_structure-a1.first_variation_pieces-a1.jacobian_derivative-a1.jacobi_formula-a1` | `root-tangent-structure-a1-first-variation-pieces-a1-jacobian-derivati-e8c562cade-6911fb9060` |
| `root.tangent_structure-a1.first_variation_pieces-a1.jacobian_derivative-a1.projection_trace-a1` | `root-tangent-structure-a1-first-variation-pieces-a1-jacobian-derivati-4ae8ee24d0-10c37a6d57` |
| `root.tangent_structure-a1.first_variation_pieces-a1.jacobian_derivative-a1.tangential_estimates-a1` | `root-tangent-structure-a1-first-variation-pieces-a1-jacobian-derivati-12a68937a7-4dafd46156` |
| `root.tangent_structure-a1.first_variation_pieces-a1.variation_bounds-a1` | `root-tangent-structure-a1-first-variation-pieces-a1-variation-bounds-a1-c2eae0c55c` |
| `root.tangent_structure-a1.first_variation_pieces-a1.variation_bounds-a1.first_order_regularity-a1` | `root-tangent-structure-a1-first-variation-pieces-a1-variation-bounds-f9645069b0-00aea3918e` |
| `root.tangent_structure-a1.first_variation_pieces-a1.variation_bounds-a1.slice_fderiv_bounds-a1` | `root-tangent-structure-a1-first-variation-pieces-a1-variation-bounds-377c1942f8-caa051cfb2` |
| `root.tangent_structure-a1.first_variation_pieces-a1.variation_bounds-a1.slice_fderiv_time_deriv-a1` | `root-tangent-structure-a1-first-variation-pieces-a1-variation-bounds-902cbbc02b-2195a0be8b` |
| `root.tangent_structure-a1.first_variation_pieces-a1.weighted_integral_derivative-a1` | `root-tangent-structure-a1-first-variation-pieces-a1-weighted-integral-2ea392d1ea-ceafdf02eb` |
| `root.tangent_structure-a1.piece_density_blowup-a1` | `root-tangent-structure-a1-piece-density-blowup-a1-a093e60f8d` |
| `root.tangent_structure-a1.piece_density_blowup-a1.density_complement-a1` | `root-tangent-structure-a1-piece-density-blowup-a1-density-complement-a1-28d3f81219` |
| `root.tangent_structure-a1.piece_density_blowup-a1.image_ball_bound-a1` | `root-tangent-structure-a1-piece-density-blowup-a1-image-ball-bound-a1-d2130048ad` |
| `root.tangent_structure-a1.piece_density_blowup-a1.linear_range_integral-a1` | `root-tangent-structure-a1-piece-density-blowup-a1-linear-range-integral-a1-3f09e2af30` |
| `root.tangent_structure-a1.piece_density_blowup-a1.piece_area_formula-a1` | `root-tangent-structure-a1-piece-density-blowup-a1-piece-area-formula-a1-64be6032ff` |
| `root.tangent_structure-a1.piece_density_blowup-a1.rescaled_limit-a1` | `root-tangent-structure-a1-piece-density-blowup-a1-rescaled-limit-a1-0d7336904b` |
| `root.tangent_structure-a1.piece_tangent_field-a1` | `root-tangent-structure-a1-piece-tangent-field-a1-f81b58b346` |
| `root.tangent_structure-a1.piece_tangent_field-a1.borel_pasting-a1` | `root-tangent-structure-a1-piece-tangent-field-a1-borel-pasting-a1-130ac52579` |
| `root.tangent_structure-a1.piece_tangent_field-a1.piece_projection_continuity-a1` | `root-tangent-structure-a1-piece-tangent-field-a1-piece-projection-continuity-a1-3395b8a186` |
| `root.tangent_structure-a1.piece_tangent_field-a1.projection_continuity-a1` | `root-tangent-structure-a1-piece-tangent-field-a1-projection-continuity-a1-645f72b5e0` |
| `root.tangent_structure-a1.piece_weighted_blowup-a1` | `root-tangent-structure-a1-piece-weighted-blowup-a1-36e7ef6764` |
| `root.tangent_structure-a1.piece_weighted_blowup-a1.density_point_image-a1` | `root-tangent-structure-a1-piece-weighted-blowup-a1-density-point-image-a1-fe62ba204e` |
| `root.tangent_structure-a1.piece_weighted_blowup-a1.good_point_blowup-a1` | `root-tangent-structure-a1-piece-weighted-blowup-a1-good-point-blowup-a1-4a508d4cc0` |
| `root.tangent_structure-a1.piece_weighted_blowup-a1.lusin_compact_cover-a1` | `root-tangent-structure-a1-piece-weighted-blowup-a1-lusin-compact-cover-a1-22e6a3bf2f` |
| `root.tangent_structure-a1.piece_weighted_blowup-a1.pair_weight_integral-a1` | `root-tangent-structure-a1-piece-weighted-blowup-a1-pair-weight-integral-a1-a8a79e7351` |
| `root.tangent_structure-a1.piece_weighted_blowup-a1.upper_density_vanish-a1` | `root-tangent-structure-a1-piece-weighted-blowup-a1-upper-density-vanish-a1-1d6ffc8b0b` |
| `root.weighted_monotonicity-a1` | `root-weighted-monotonicity-a1-bc4483b80c` |
| `root.weighted_monotonicity-a1.cutoff_first_variation-a1` | `root-weighted-monotonicity-a1-cutoff-first-variation-a1-0e758a707c` |
| `root.weighted_monotonicity-a1.cutoff_first_variation-a1.cutoff_identity-a1` | `root-weighted-monotonicity-a1-cutoff-first-variation-a1-cutoff-identity-a1-0c4b7a4576` |
| `root.weighted_monotonicity-a1.cutoff_first_variation-a1.local_data-a1` | `root-weighted-monotonicity-a1-cutoff-first-variation-a1-local-data-a1-3b2c5ae11a` |
| `root.weighted_monotonicity-a1.cutoff_integral_deriv-a1` | `root-weighted-monotonicity-a1-cutoff-integral-deriv-a1-9c6e8e6cee` |
| `root.weighted_monotonicity-a1.cutoff_limit-a1` | `root-weighted-monotonicity-a1-cutoff-limit-a1-4948d9bd84` |
| `root.weighted_monotonicity-a1.cutoff_limit-a1.curvature_term-a1` | `root-weighted-monotonicity-a1-cutoff-limit-a1-curvature-term-a1-3cd06d964c` |
| `root.weighted_monotonicity-a1.cutoff_limit-a1.cutoff_integral-a1` | `root-weighted-monotonicity-a1-cutoff-limit-a1-cutoff-integral-a1-e813b8a0b0` |
| `root.weighted_monotonicity-a1.cutoff_limit-a1.cutoff_seq-a1` | `root-weighted-monotonicity-a1-cutoff-limit-a1-cutoff-seq-a1-812fb3eb9f` |
| `root.weighted_monotonicity-a1.cutoff_limit-a1.kernel_limit-a1` | `root-weighted-monotonicity-a1-cutoff-limit-a1-kernel-limit-a1-28e3aea9da` |
| `root.weighted_monotonicity-a1.cutoff_limit-a1.kernel_term-a1` | `root-weighted-monotonicity-a1-cutoff-limit-a1-kernel-term-a1-2b7f3e4181` |
| `root.weighted_monotonicity-a1.kernel_bounds-a1` | `root-weighted-monotonicity-a1-kernel-bounds-a1-f29b1cb504` |
| `root.weighted_monotonicity-a1.radial_test_field-a1` | `root-weighted-monotonicity-a1-radial-test-field-a1-c9541c31b2` |
| `root.weighted_monotonicity-a1.smoothed_identity-a1` | `root-weighted-monotonicity-a1-smoothed-identity-a1-af41c66ed0` |
| `root.weighted_monotonicity-a1.smoothed_identity-a1.kernel_fubini-a1` | `root-weighted-monotonicity-a1-smoothed-identity-a1-kernel-fubini-a1-ad754fb371` |
| `root.weighted_monotonicity-a1.smoothed_identity-a1.scale_continuity-a1` | `root-weighted-monotonicity-a1-smoothed-identity-a1-scale-continuity-a1-41dcab67a6` |
| `root.weighted_monotonicity-a1.smoothed_identity-a1.scaled_ftc-a1` | `root-weighted-monotonicity-a1-smoothed-identity-a1-scaled-ftc-a1-98a70f6e4a` |

## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Root delivery: merge the exact checked root PR, confirm the remote tree, then link and close child review PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
