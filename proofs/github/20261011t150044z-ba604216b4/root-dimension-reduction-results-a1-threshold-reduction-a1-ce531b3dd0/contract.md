<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.threshold_reduction-a1 -->

## Theorem `Submission.dimred_threshold_reduction`

Let n, k, ℓ ∈ ℕ with 1 ≤ n and ℓ ≤ k, let U ⊆ ℝ^{n+k} be open, let N be an embedded C² (n+ℓ)-dimensional submanifold with (closure N ∖ N) ∩ U = ∅, and let T ∈ 𝒟_n(U) be minimizing in U ∩ N with spt T ⊆ U ∩ N and ∂T = 0 in U. Let c > 0, d₀ ∈ ℕ, z ∈ ℝ^{n+k} and r > 0 with closedBall z (2r) ⊆ U. Call S ∈ 𝒟_n(ℝ^{n+k}) an admissible zero-scale limit if S is the weak limit in ℝ^{n+k} (ConvergesWeakly) of the blow-ups η_{x_i,λ_i#}T (blowUp T x_i λ_i) for some points x_i ∈ B_r(z) and scales λ_i > 0 with λ_i → 0, and S is minimizing in ℝ^{n+k} with ∂S = 0. Assume (H1): no admissible zero-scale limit S has Θ^n(μ_S, y) = c'·1_Q(y) for all y (HasMassDensity S y (indicator of Q with value c')) for some n-dimensional linear subspace Q and some real c' ≥ c; and (H2): no admissible zero-scale limit S admits a linear subspace L with d₀ ≤ dim L < n such that HasMassDensity S w θ implies HasMassDensity S (y + λw) θ for all y ∈ L, λ > 0, w, θ, and such that {y : ∃θ ≥ c, HasMassDensity S y θ} = L. Let Z(s) := {x ∈ B_s(z) : ∃θ ≥ c, HasMassDensity T x θ} (the points of B_s(z) with Θ^n(μ_T, x) ≥ c). Then μH[d₀ − 1 + α](Z(r)) = 0 for every real α > 0; Z(r) = ∅ if d₀ = 0; and Z(r/2) is finite if d₀ = 1.

Node: `root.dimension_reduction_results-a1.threshold_reduction-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/374

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1016, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1018, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1022

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/385, https://github.com/ZhengyangZhang06/gmt-formalize/issues/996, https://github.com/ZhengyangZhang06/gmt-formalize/issues/837, https://github.com/ZhengyangZhang06/gmt-formalize/issues/839, https://github.com/ZhengyangZhang06/gmt-formalize/issues/864, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7927, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7930, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1240, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7935, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7938, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7943, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7948

## Lean problem

Declaration: `Submission.dimred_threshold_reduction`

```lean
∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n), 1 ≤ n → IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ → IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T → ∀ (c : ℝ) (d₀ : ℕ) (z : Euclid (n + k)) (r : ℝ), 0 < c → 0 < r → closedBall z (2 * r) ⊆ U → (∀ (S : GeometricCurrentOn (univ : Set (Euclid (n + k))) n) (xs : ℕ → Euclid (n + k)) (lams : ℕ → ℝ) (hlams : ∀ i, 0 < lams i) (Q : Submodule ℝ (Euclid (n + k))) (c' : ℝ), (∀ i, xs i ∈ ball z r) → Tendsto lams atTop (𝓝 0) → ConvergesWeakly (fun i => blowUp T (xs i) (lams i) (hlams i).ne') S → IsMinimizingIn S univ → BoundaryVanishes S → Module.finrank ℝ Q = n → c ≤ c' → (∀ y, HasMassDensity S y (Set.indicator (Q : Set (Euclid (n + k))) (fun _ => c') y)) → False) → (∀ (S : GeometricCurrentOn (univ : Set (Euclid (n + k))) n) (xs : ℕ → Euclid (n + k)) (lams : ℕ → ℝ) (hlams : ∀ i, 0 < lams i) (L : Submodule ℝ (Euclid (n + k))), (∀ i, xs i ∈ ball z r) → Tendsto lams atTop (𝓝 0) → ConvergesWeakly (fun i => blowUp T (xs i) (lams i) (hlams i).ne') S → IsMinimizingIn S univ → BoundaryVanishes S → d₀ ≤ Module.finrank ℝ L → Module.finrank ℝ L < n → (∀ y ∈ L, ∀ lam : ℝ, 0 < lam → ∀ (w : Euclid (n + k)) (θ : ℝ), HasMassDensity S w θ → HasMassDensity S (y + lam • w) θ) → (∀ y, (∃ θ : ℝ, c ≤ θ ∧ HasMassDensity S y θ) ↔ y ∈ L) → False) → (∀ α : ℝ, 0 < α → μH[(d₀ : ℝ) - 1 + α] {x | x ∈ ball z r ∧ ∃ θ : ℝ, c ≤ θ ∧ HasMassDensity T x θ} = 0) ∧ (d₀ = 0 → {x | x ∈ ball z r ∧ ∃ θ : ℝ, c ≤ θ ∧ HasMassDensity T x θ} = ∅) ∧ (d₀ = 1 → {x | x ∈ ball z (r / 2) ∧ ∃ θ : ℝ, c ≤ θ ∧ HasMassDensity T x θ}.Finite)
```

### Frozen project context

`GMT/Ch07/Contract.lean` at `b4d606db1da5da8fa2c0292ad4924d97de8b3c4b` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.LinearAlgebra.Trace
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter06.Mass
import Poincare.SimonGMT.Chapter06.CurrentLocalEquality
import Poincare.SimonGMT.Chapter06.AffineCurrentPushforward

/-!
# Simon, *Introduction to Geometric Measure Theory*, Chapter 7 "Area Minimizing Currents"
(printed pp. 181–204)

Frozen contract.  Currents, boundary, mass, support and weak convergence are the clean SimonGMT
objects of `Poincare.SimonGMT.Chapter06`: `GeometricCurrentOn U n` (Simon 6.2.1), `T.boundary`
(6.2.3), `T.massOn W` = `M_W(T)` (6.2.5, Euclidean coefficient norm), `T.mass` (6.2.4),
`T.support` (6.2.11), `WeaklyConvergesOn` (6.2.13), and the proper affine push-forward
`GeometricCurrentOn.affinePushforward` (6.2.23).  Everything else (integer multiplicity currents,
minimizing currents, densities, blow-ups, tangent cones, `reg T`, `sing T`, the associated
varifold) is defined below from primitive data.  `Hⁿ` is Mathlib's normalized `μHE[n]`; null-set
statements use Mathlib's `μH[s]` (same null sets as Simon's `Hˢ`).

**Conventions.**  The ambient space is `ℝ^{n+k}` (`Euclid (n + k)`); when a submanifold `N` is
present it has dimension `n + ℓ`, `ℓ ≤ k` (Simon writes `N^{n+ℓ} ⊂ ℝ^{n+ℓ}`, `ℓ ≤ k`, a
misprint for `ℝ^{n+k}`; `N = ℝ^{n+k}` is the case `ℓ = k`).  For an `n`-current, `∂T = 0`,
`∂S = ∂T`, `spt ∂T`, `M_W(∂T)` are read with Simon's convention `∂T = 0` if `n = 0` (6.2.3).
-/

open Filter Function Set MeasureTheory Metric
open scoped ENNReal Topology

namespace GMT.Ch07

open Poincare.SimonGMT.Chapter06
open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt)

noncomputable section

/-- Euclidean space `ℝᴾ`. -/
abbrev Euclid (P : ℕ) := EuclideanSpace ℝ (Fin P)

variable {P : ℕ}

/-! ## Multivectors and integer multiplicity currents (Simon Ch. 6, §1 and 3.1) -/

/-- `n`-vectors `Λₙ(ℝᴾ)`, realized as the dual of `n`-covectors (Simon 6.1, `Λₙ ≅ (Λⁿ)*`);
`ξ α` is the pairing `⟨α, ξ⟩` of Simon (6.1.7). -/
abbrev MultiVector (P n : ℕ) := Covector (Euclid P) n →L[ℝ] ℝ

/-- `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` for an orthonormal basis `τ` of the subspace `Q`, i.e.
`⟨α, ξ⟩ = ±α(τ₁, …, τₙ)` (Simon 6.1.1, 6.1.7; 6.2.2).  The sign matters only for `n = 0`. -/
def IsUnitOrientationOf {n : ℕ} (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)) : Prop :=
  ∃ τ : Fin n → Euclid P, Orthonormal ℝ τ ∧ Submodule.span ℝ (range τ) = Q ∧
    ((∀ α : Covector (Euclid P) n, ξ α = α τ) ∨ ∀ α : Covector (Euclid P) n, ξ α = -α τ)

/-- Simon Ch. 6, Definition 3.1 (p. 146): a triple `(M, θ, ξ)` in `U`.  `M ⊆ U` is
`Hⁿ`-measurable (taken Borel; this loses nothing, `Hⁿ⌞M` being σ-finite) and countably
`n`-rectifiable; `θ` is positive integer-valued on `M` and locally `Hⁿ`-integrable in `U`; `ξ` is
`Hⁿ`-measurable and, `Hⁿ`-a.e. on `M`, orients the approximate tangent space `TₓM`
(Ch. 3, 1.4). -/
structure IMRep (U : Set (Euclid P)) (n : ℕ) where
  carrier : Set (Euclid P)
  mult : Euclid P → ℕ
  orient : Euclid P → MultiVector P n
  measurableSet_carrier : MeasurableSet carrier
  carrier_subset : carrier ⊆ U
  rectifiable : CountablyRectifiable n carrier
  measurable_mult : Measurable mult
  mult_pos : ∀ x ∈ carrier, 0 < mult x
  locallyIntegrable_mult : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
    ∫⁻ x in carrier ∩ K, (mult x : ℝ≥0∞) ∂μHE[n] ≠ ∞
  aestronglyMeasurable_orient : AEStronglyMeasurable orient (μHE[n].restrict carrier)
  orients : ∀ᵐ x ∂(μHE[n].restrict carrier), ∃ Q : Submodule ℝ (Euclid P),
    HasApproximateTangentSpaceAt n carrier x Q ∧ IsUnitOrientationOf (orient x) Q

variable {U : Set (Euclid P)} {n : ℕ}

/-- `τ(M, θ, ξ)(ω) = ∫_M ⟨ω(x), ξ(x)⟩ θ(x) dHⁿ(x)` (Simon 6.3.1 (‡)). -/
def IMRep.action (R : IMRep U n) (ω : DifferentialForm (Euclid P) n) : ℝ :=
  ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (ω x) ∂μHE[n]

/-- `T = τ(M, θ, ξ)` in `U`. -/
def IMRep.Represents (R : IMRep U n) (T : GeometricCurrentOn U n) : Prop :=
  ∀ ω : TestFormOn U n, T ω = R.action (ω : DifferentialForm (Euclid P) n)

/-- The weight `μ_V = θ Hⁿ⌞M` of the associated varifold `V = v(M, θ)`; it equals the mass
measure `μ_T` of `T = τ(M, θ, ξ)` (Simon 6.3.2(3), 4.1.1). -/
def IMRep.measure (R : IMRep U n) : Measure (Euclid P) :=
  (μHE[n].restrict R.carrier).withDensity fun x => (R.mult x : ℝ≥0∞)

/-- Simon 6.3.1: `T` is an integer multiplicity (rectifiable) current. -/
def IsIntegerMultiplicity (T : GeometricCurrentOn U n) : Prop :=
  ∃ R : IMRep U n, R.Represents T

/-- Difference of currents (needed for `spt(S − T)` in 7.1.1). -/
instance : Sub (GeometricCurrentOn U n) where
  sub S T :=
    { toCurrent := S.toCurrent - T.toCurrent
      continuous' := fun ωs h => by
        simpa using (S.continuous' ωs h).sub (T.continuous' ωs h) }

/-! ## Boundary conventions in arbitrary degree -/

/-- `∂S = ∂T` in `U` (vacuous for `n = 0`, where `∂ = 0`). -/
def SameBoundary : {n : ℕ} → GeometricCurrentOn U n → GeometricCurrentOn U n → Prop
  | 0, _, _ => True
  | _ + 1, S, T => S.boundary = T.boundary

/-- `∂T = 0` in `U`. -/
def BoundaryVanishes : {n : ℕ} → GeometricCurrentOn U n → Prop
  | 0, _ => True
  | _ + 1, T => T.boundary = 0

/-- `spt ∂T` (empty for `n = 0`). -/
def boundarySupport : {n : ℕ} → GeometricCurrentOn U n → Set (Euclid P)
  | 0, _ => ∅
  | _ + 1, T => T.boundary.support

/-- `M_W(∂T)` (zero for `n = 0`). -/
def boundaryMassOn : {n : ℕ} → GeometricCurrentOn U n → Set (Euclid P) → ℝ≥0∞
  | 0, _, _ => 0
  | _ + 1, T, W => T.boundary.massOn W

/-! ## Minimizing currents (Simon 7.1.1) -/

/-- `W ⊂⊂ U`: `closure W` is a compact subset of `U`. -/
def CompactlyContained (W U : Set (Euclid P)) : Prop :=
  IsCompact (closure W) ∧ closure W ⊆ U

/-- **Simon 7.1.1 (p. 181).**  The integer multiplicity `T ∈ 𝒟ₙ(U)` is *minimizing in `A`*
(`A ⊆ U`): `M_W(T) ≤ M_W(S)` whenever `W ⊂⊂ U` is open, `S ∈ 𝒟ₙ(U)` is integer multiplicity,
`∂S = ∂T` in `U` and `spt(S − T)` is a compact subset of `A ∩ W`.  Competitors are integer
multiplicity, as required by Remark 7.2.2(1) and the proofs of 7.1.4 and 7.2.4. -/
def IsMinimizingIn (T : GeometricCurrentOn U n) (A : Set (Euclid P)) : Prop :=
  IsIntegerMultiplicity T ∧
    ∀ (W : Set (Euclid P)) (S : GeometricCurrentOn U n), IsOpen W → CompactlyContained W U →
      IsIntegerMultiplicity S → SameBoundary S T → IsCompact (S - T).support →
        (S - T).support ⊆ A ∩ W → T.massOn W ≤ S.massOn W

/-! ## Densities, blow-ups, tangent cones (Simon 7.3) -/

/-- `ωₙ`, the Lebesgue measure of the unit ball of `ℝⁿ`. -/
def unitBallVolume (n : ℕ) : ℝ≥0∞ := volume (ball (0 : Euclid n) 1)

/-- `Θⁿ(μ_T, x) = θ`: `(ωₙρⁿ)⁻¹ μ_T(B_ρ(x)) → θ` as `ρ ↓ 0`, with `μ_T(B_ρ(x)) = M_{B_ρ(x)}(T)`
for small `ρ` (Simon 6.2.8; open and closed balls give the same limit). -/
def HasMassDensity (T : GeometricCurrentOn U n) (x : Euclid P) (θ : ℝ) : Prop :=
  0 ≤ θ ∧ Tendsto (fun ρ : ℝ => T.massOn (ball x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n)))
    (𝓝[>] 0) (𝓝 (ENNReal.ofReal θ))

/-- Value of a current in `U` on an ambient form: `T(ω)` if `ω ∈ 𝒟ⁿ(U)`, else `0`.  Used for
convergence of currents on varying domains (Simon: "`η_{x,λⱼ#}T ⇀ C` in `ℝ^{n+ℓ}`"). -/
def currentEval (T : GeometricCurrentOn U n) (ω : DifferentialForm (Euclid P) n) : ℝ := by
  classical
  exact if h : IsTestForm ω ∧ tsupport ω ⊆ U then T ⟨ω, h⟩ else 0

/-- `Tⱼ ⇀ T` in `V`, for currents `Tⱼ ∈ 𝒟ₙ(Uⱼ)` whose domains eventually contain every compact
subset of `V` (as for blow-ups): `Tⱼ(ω) → T(ω)` for every `ω ∈ 𝒟ⁿ(V)` (Simon 6.2.13). -/
def ConvergesWeakly {Us : ℕ → Set (Euclid P)} (Ts : (j : ℕ) → GeometricCurrentOn (Us j) n)
    {V : Set (Euclid P)} (T : GeometricCurrentOn V n) : Prop :=
  ∀ ω : TestFormOn V n,
    Tendsto (fun j => currentEval (Ts j) (ω : DifferentialForm (Euclid P) n)) atTop (𝓝 (T ω))

/-- `μ_{Tⱼ} → μ_T` as Radon measures in `V` (Simon 7.2.4, Remark 7.2.5(1)): for all integer
multiplicity representations of the `Tⱼ` and of `T`, `∫ f dμ_{Tⱼ} → ∫ f dμ_T` for every
continuous `f` with compact support in `V`. -/
def MassMeasuresConverge {Us : ℕ → Set (Euclid P)} (Ts : (j : ℕ) → GeometricCurrentOn (Us j) n)
    {V : Set (Euclid P)} (T : GeometricCurrentOn V n) : Prop :=
  ∀ Rs : (j : ℕ) → IMRep (Us j) n, (∀ j, (Rs j).Represents (Ts j)) →
    ∀ R : IMRep V n, R.Represents T →
      ∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ V →
        Tendsto (fun j => ∫ x, f x ∂(Rs j).measure) atTop (𝓝 (∫ x, f x ∂R.measure))

/-- The linear part `y ↦ λ⁻¹y` of the dilation `η_{x,λ}`. -/
def dilationCLM (P : ℕ) (lam : ℝ) : Euclid P →L[ℝ] Euclid P :=
  lam⁻¹ • ContinuousLinearMap.id ℝ (Euclid P)

/-- Simon's dilation `η_{x,λ}(y) = λ⁻¹(y − x)`, written `y ↦ −λ⁻¹x + λ⁻¹y`. -/
def dilation (x : Euclid P) (lam : ℝ) : Euclid P → Euclid P :=
  fun y => -(lam⁻¹ • x) + dilationCLM P lam y

/-- The blow-up `η_{x,λ#}T ∈ 𝒟ₙ(η_{x,λ}(U))`, `η_{x,λ#}T(ω) = T(η_{x,λ}^# ω)` (Simon 6.2.23 for
the proper affine diffeomorphism `η_{x,λ}`, `λ ≠ 0`). -/
def blowUp (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : lam ≠ 0) :
    GeometricCurrentOn (dilation x lam '' U) n :=
  (T.restrictDomain (show (fun y => -(lam⁻¹ • x) + dilationCLM P lam y) ⁻¹'
      (dilation x lam '' U) ⊆ U by
    rintro y ⟨z, hz, hzy⟩
    have hzy' : lam⁻¹ • z = lam⁻¹ • y := by
      simpa [dilation, dilationCLM] using hzy
    rwa [← smul_right_injective (Euclid P) (inv_ne_zero hlam) hzy'])).affinePushforward
    (dilationCLM P lam) (-(lam⁻¹ • x)) (by
      convert ((Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hlam)).trans
        (Homeomorph.addLeft (-(lam⁻¹ • x)))).isProperMap using 1
      funext y
      simp [dilationCLM])

/-- `C ∈ 𝒟ₙ(ℝᴾ)` is a cone: `η_{0,λ#}C = C` for every `λ > 0` (Simon 7.3.1(2)). -/
def IsConeCurrent (C : GeometricCurrentOn (univ : Set (Euclid P)) n) : Prop :=
  ∀ (lam : ℝ) (hlam : 0 < lam) (ω : TestFormOn (univ : Set (Euclid P)) n),
    currentEval (blowUp C 0 lam hlam.ne') (ω : DifferentialForm (Euclid P) n) = C ω

/-- Simon 7.3.2(1): `C` is a tangent cone of `T` at `x`, i.e. `η_{x,λⱼ#}T ⇀ C` in `ℝᴾ` for some
sequence `λⱼ > 0`, `λⱼ → 0`. -/
def IsTangentConeAt (T : GeometricCurrentOn U n) (x : Euclid P)
    (C : GeometricCurrentOn (univ : Set (Euclid P)) n) : Prop :=
  ∃ (lams : ℕ → ℝ) (hlams : ∀ j, 0 < lams j), Tendsto lams atTop (𝓝 0) ∧
    ConvergesWeakly (fun j => blowUp T x (lams j) (hlams j).ne') C

/-- Simon 7.3.2(1): `T` has a (multiplicity `m`) tangent plane at `x`: some tangent cone has
support an `n`-dimensional subspace. -/
def HasTangentPlaneAt (T : GeometricCurrentOn U n) (x : Euclid P) : Prop :=
  ∃ C : GeometricCurrentOn (univ : Set (Euclid P)) n, IsTangentConeAt T x C ∧
    ∃ Q : Submodule ℝ (Euclid P), Module.finrank ℝ Q = n ∧ C.support = (Q : Set (Euclid P))

/-! ## Submanifolds, `reg T`, `sing T` (Simon Ch. 2, §4 and 7.4.1) -/

/-- Simon Ch. 2, §4, (4.1) (p. 55): `M ⊂ ℝᴾ` is a `d`-dimensional (embedded) `Cʳ` submanifold:
each `y ∈ M` has an open `W ∋ y` and a 1:1 `Cʳ` map `ψ : V → W`, `V ⊆ ℝᵈ` open, with
`ψ(V) = W ∩ M`, `ψ` proper, and `Dψ` of rank `d` on `V`. -/
def IsEmbeddedSubmanifold (r d : ℕ) (M : Set (Euclid P)) : Prop :=
  ∀ y ∈ M, ∃ (V : Set (Euclid d)) (W : Set (Euclid P)) (ψ : Euclid d → Euclid P),
    IsOpen V ∧ IsOpen W ∧ y ∈ W ∧ ContDiffOn ℝ r ψ V ∧ InjOn ψ V ∧ ψ '' V = W ∩ M ∧
      (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) ∧
      ∀ z ∈ V, Injective (fderiv ℝ ψ z)

/-- Simon Ch. 2, §4 (p. 55): `T_yM = {γ'(0) : γ ∈ C¹((−1,1); ℝᴾ), γ((−1,1)) ⊆ M, γ(0) = y}`. -/
def tangentSpace (M : Set (Euclid P)) (y : Euclid P) : Set (Euclid P) :=
  {v | ∃ γ : ℝ → Euclid P, ContDiffOn ℝ 1 γ (Ioo (-1) 1) ∧ MapsTo γ (Ioo (-1) 1) M ∧
    γ 0 = y ∧ HasDerivAt γ v 0}

/-- An orientation of the `d`-dimensional submanifold `M` (Simon 6.2.2): `ξ` is continuous on
`M` and `ξ(y) = ±τ₁ ∧ ⋯ ∧ τ_d` for an orthonormal basis `τ` of `T_yM`, for every `y ∈ M`. -/
def IsOrientation (d : ℕ) (M : Set (Euclid P)) (ξ : Euclid P → MultiVector P d) : Prop :=
  ContinuousOn ξ M ∧ ∀ y ∈ M, ∃ Q : Submodule ℝ (Euclid P),
    (Q : Set (Euclid P)) = tangentSpace M y ∧ IsUnitOrientationOf (ξ y) Q

/-- **Simon 7.4.1 (p. 193)**: `reg T` is the set of `y ∈ spt T` such that, for some `ρ > 0`
(with `B_ρ(y) ⊆ U`), `m ∈ ℤ \ {0}` and embedded `n`-dimensional oriented `C¹` submanifold `M`
(of locally finite `Hⁿ`-measure in `B_ρ(y)`, as `[[M]]` requires, 6.2.2), `T = m[[M]]` in
`B_ρ(y)` (6.2.16), i.e. `T(ω) = m ∫_M ⟨ω, ξ_M⟩ dHⁿ` whenever `spt ω ⊆ B_ρ(y)`.
The point `y` itself must lie on `M` (as in 4.4(8) and the proof of 5.8): otherwise a singular
point could be declared regular by deleting it from `M`, e.g. the vertex of the Simons cone. -/
def regularSet (T : GeometricCurrentOn U n) : Set (Euclid P) :=
  {y | y ∈ T.support ∧ ∃ ρ : ℝ, 0 < ρ ∧ ball y ρ ⊆ U ∧
    ∃ (m : ℤ) (M : Set (Euclid P)) (ξ : Euclid P → MultiVector P n), m ≠ 0 ∧ y ∈ M ∧
      IsEmbeddedSubmanifold 1 n M ∧ IsOrientation n M ξ ∧
      (∀ K : Set (Euclid P), IsCompact K → K ⊆ ball y ρ → μHE[n] (M ∩ K) ≠ ∞) ∧
      ∀ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Euclid P) n) ⊆ ball y ρ →
        T ω = m * ∫ x in M, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]}

/-- **Simon 7.4.1**: `sing T = spt T \ reg T`. -/
def singularSet (T : GeometricCurrentOn U n) : Set (Euclid P) :=
  T.support \ regularSet T

/-! ## The associated varifold `V = v(M, θ)` (Simon Ch. 4, 2.3–2.7 and 3.14) -/

/-- The approximate tangent plane `TₓM` (Ch. 3, 1.4; unique when it exists), `⊥` otherwise. -/
def approxTangentPlane (n : ℕ) (M : Set (Euclid P)) (x : Euclid P) :
    Submodule ℝ (Euclid P) := by
  classical
  exact if h : ∃ Q, HasApproximateTangentSpaceAt n M x Q then h.choose else ⊥

/-- `div_M X(x) = Σⱼ eⱼ · ∇^M Xʲ = trace(p_{TₓM} ∘ DX(x))` (Simon Ch. 4, 2.3). -/
def tangentialDivergence (n : ℕ) (M : Set (Euclid P)) (X : Euclid P → Euclid P)
    (x : Euclid P) : ℝ :=
  LinearMap.trace ℝ (Euclid P)
    ((approxTangentPlane n M x).starProjection.toLinearMap ∘ₗ (fderiv ℝ X x).toLinearMap)

/-- First variation `δV(X) = ∫_M div_M X dμ_V` of `V = v(M, θ)` (Simon Ch. 4, 2.2). -/
def IMRep.firstVariation (R : IMRep U n) (X : Euclid P → Euclid P) : ℝ :=
  ∫ x in R.carrier, (R.mult x : ℝ) * tangentialDivergence n R.carrier X x ∂μHE[n]

/-- Simon Ch. 4, 2.6 (computed form, p. 88): `V` is stationary in `U ∩ N`: `δV(X) = 0` for all
`X ∈ C¹_c(U; ℝᴾ)` with `X(x) ∈ TₓN` for every `x ∈ N ∩ U`. -/
def IMRep.IsStationaryAlong (R : IMRep U n) (N : Set (Euclid P)) : Prop :=
  ∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U →
    (∀ x ∈ N ∩ U, X x ∈ tangentSpace N x) → R.firstVariation X = 0

/-- Simon Ch. 4, 3.14: `V` has generalized mean curvature `H` in `U`
(`∫ div_M X dμ_V = −∫ X · H dμ_V`, `X ∈ C¹_c(U; ℝᴾ)`), with `H` bounded on compact subsets. -/
def IMRep.HasLocallyBoundedMeanCurvature (R : IMRep U n) : Prop :=
  ∃ H : Euclid P → Euclid P, AEStronglyMeasurable H R.measure ∧
    (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ∃ Λ : ℝ, ∀ᵐ x ∂R.measure, x ∈ K → ‖H x‖ ≤ Λ) ∧
    ∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U →
      R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure

/-! ## Codimension one (Simon 7.5) -/

/-- Simon 7.5 (p. 197): `N ∈ 𝒪`, an oriented embedded `C²` submanifold of dimension `n + 1` with
`(N̄ \ N) ∩ U = ∅` and `N ∩ U ≠ ∅`, with chosen orientation `ξN`. -/
def InClassO (n : ℕ) (U N : Set (Euclid P)) (ξN : Euclid P → MultiVector P (n + 1)) : Prop :=
  IsEmbeddedSubmanifold 2 (n + 1) N ∧ IsOrientation (n + 1) N ξN ∧ (closure N \ N) ∩ U = ∅ ∧
    (N ∩ U).Nonempty

/-- Simon 7.5.1: `T = ∂[[E]]` in `U`, where `[[E]](ω) = ∫_E ⟨ω, ξ_N⟩ dH^{n+1}`. -/
def IsBoundaryOfRegion (T : GeometricCurrentOn U n) (E : Set (Euclid P))
    (ξN : Euclid P → MultiVector P (n + 1)) : Prop :=
  ∀ ω : TestFormOn U n,
    T ω = ∫ x in E, ξN x (exteriorDerivative (ω : DifferentialForm (Euclid P) n) x) ∂μHE[n + 1]

/-! ## Headline results -/

/-- **Simon 7.1.2 (Lemma, pp. 181–182).**  Let `N` be an embedded `C²` `(n+ℓ)`-dimensional
submanifold of `ℝ^{n+k}`, `(N̄ \ N) ∩ U = ∅`.  If `T ∈ 𝒟ₙ(U)` is minimizing in `N ∩ U`,
`spt T ⊆ N` and `∂T = 0` in `U`, then the associated varifold `V = v(M, θ)` (for any
representation `T = τ(M, θ, ξ)`) is stationary in `N ∩ U` (Ch. 4, 2.6) and has locally bounded
generalized mean curvature in `U` (Ch. 4, 3.14).
*Correction*: `spt T ⊆ N` and `(N̄ \ N) ∩ U = ∅` are implicit in the book (they are part of the
setting of Ch. 4, 2.5–2.6 and of §3); without `spt T ⊆ N` the lemma is false. -/
def MinimizingImpliesStationary : Prop :=
  ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n),
    IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ →
    T.support ⊆ N → IsMinimizingIn T (N ∩ U) → BoundaryVanishes T →
    ∀ R : IMRep U n, R.Represents T → R.IsStationaryAlong N ∧ R.HasLocallyBoundedMeanCurvature

/-- **Simon 7.2.1 (Lemma, p. 183).**  Let `S ∈ 𝒟_{n−1}(ℝ^{n+ℓ})` be integer multiplicity with
`spt S` compact and `∂S = 0`.  Then there is an integer multiplicity `T ∈ 𝒟ₙ(ℝ^{n+ℓ})` with
`spt T` compact, `∂T = S`, and `M(T) ≤ M(R)` for every integer multiplicity `R` with `spt R`
compact and `∂R = S`.  Here `n = m + 2`: integer multiplicity currents have dimension `≥ 1`
(Ch. 6, §3).  *Correction*: the printed statement omits the conclusion `∂T = S` (proved: `T ∈ 𝓘_S`);
without it `T = 0` would do. -/
def ExistenceOfMinimizingFilling : Prop :=
  ∀ (m ℓ : ℕ) (S : GeometricCurrentOn (univ : Set (Euclid (m + 2 + ℓ))) (m + 1)),
    IsIntegerMultiplicity S → IsCompact S.support → S.boundary = 0 →
    ∃ T : GeometricCurrentOn (univ : Set (Euclid (m + 2 + ℓ))) (m + 2),
      IsIntegerMultiplicity T ∧ IsCompact T.support ∧ T.boundary = S ∧
      ∀ R : GeometricCurrentOn (univ : Set (Euclid (m + 2 + ℓ))) (m + 2),
        IsIntegerMultiplicity R → IsCompact R.support → R.boundary = S → T.mass ≤ R.mass

/-- **Simon 7.2.4 (Theorem, p. 184).**  If `Tⱼ` are minimizing in `U`,
`supⱼ (M_W(Tⱼ) + M_W(∂Tⱼ)) < ∞` for each open `W ⊂⊂ U`, and `Tⱼ ⇀ T ∈ 𝒟ₙ(U)`, then `T` is
(integer multiplicity, Remark 7.2.5(1), and) minimizing in `U`, and `μ_{Tⱼ} → μ_T` as Radon
measures in `U`. -/
def CompactnessOfMinimizingCurrents : Prop :=
  ∀ (n k : ℕ) (U : Set (Euclid (n + k))) (Ts : ℕ → GeometricCurrentOn U n)
      (T : GeometricCurrentOn U n),
    IsOpen U → (∀ j, IsMinimizingIn (Ts j) U) →
    (∀ W : Set (Euclid (n + k)), IsOpen W → CompactlyContained W U →
      ⨆ j, ((Ts j).massOn W + boundaryMassOn (Ts j) W) < ∞) →
    WeaklyConvergesOn Ts T → IsMinimizingIn T U ∧ MassMeasuresConverge (Us := fun _ => U) Ts T

/-- **Simon 7.3.1 (Theorem, p. 187).**  `N` as in 7.1.2 (`C²`).  If `T ∈ 𝒟ₙ(U)` is minimizing in
`U ∩ N` and `spt T ⊆ U ∩ N`, then (1) `Θⁿ(μ_T, x)` exists at every `x ∈ U \ spt ∂T` and is upper
semicontinuous there; (2) for `x ∈ spt T \ spt ∂T` and `λⱼ ↓ 0` (any `λⱼ > 0`, `λⱼ → 0`) there
are a subsequence `λⱼ'` and an integer multiplicity `C ∈ 𝒟ₙ(ℝ^{n+k})`, minimizing in `ℝ^{n+k}`,
with `η_{x,λⱼ'#}T ⇀ C`, `μ_{η_{x,λⱼ'#}T} → μ_C`, `η_{0,λ#}C = C` (`λ > 0`) and
`Θⁿ(μ_C, 0) = Θⁿ(μ_T, x)`.
*Correction*: the printed hypothesis "`x ∈ spt T \ spt ∂T`" and "(1) … everywhere in `U`" are
garbled; the monotonicity proof gives (1) on `U \ spt ∂T`, which is what is stated. -/
def DensityAndTangentCones : Prop :=
  ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n),
    IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ →
    IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N →
    (∃ Θ : Euclid (n + k) → ℝ, (∀ x ∈ U \ boundarySupport T, HasMassDensity T x (Θ x)) ∧
        UpperSemicontinuousOn Θ (U \ boundarySupport T)) ∧
    ∀ x ∈ T.support \ boundarySupport T, ∀ (lams : ℕ → ℝ) (hlams : ∀ j, 0 < lams j),
      Tendsto lams atTop (𝓝 0) →
      ∃ (φ : ℕ → ℕ) (C : GeometricCurrentOn (univ : Set (Euclid (n + k))) n), StrictMono φ ∧
        ConvergesWeakly (fun j => blowUp T x (lams (φ j)) (hlams (φ j)).ne') C ∧
        MassMeasuresConverge (fun j => blowUp T x (lams (φ j)) (hlams (φ j)).ne') C ∧
        IsMinimizingIn C univ ∧ IsConeCurrent C ∧
        ∃ θ : ℝ, HasMassDensity T x θ ∧ HasMassDensity C 0 θ

/-- **Simon 7.3.3 (Theorem, p. 189).**  `N` as in 7.3.1.  If `T` is minimizing in `U ∩ N`,
`spt T ⊆ U ∩ N` and `∂T = 0` in `U`, then (1) `Θⁿ(μ_T, x) ∈ ℤ` for all `x ∈ U \ E`, where
`H^{n−3+α}(E) = 0` for all `α > 0`; (2) there is `F ⊇ E` with `H^{n−2+α}(F) = 0` for all `α > 0`
such that `T` has a tangent plane at each `x ∈ spt T \ F`.
*Correction*: printed "`F ⊂ E`" must read `F ⊃ E` (non-integer density excludes tangent planes). -/
def IntegerDensityAndTangentPlanes : Prop :=
  ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n),
    IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ →
    IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T →
    ∃ E F : Set (Euclid (n + k)), E ⊆ F ∧
      (∀ α : ℝ, 0 < α → μH[(n : ℝ) - 3 + α] E = 0) ∧
      (∀ x ∈ U \ E, ∃ m : ℤ, HasMassDensity T x m) ∧
      (∀ α : ℝ, 0 < α → μH[(n : ℝ) - 2 + α] F = 0) ∧
      ∀ x ∈ T.support \ F, HasTangentPlaneAt T x

/-- **Simon 7.4.2 (Theorem, p. 194).**  If `T ∈ 𝒟ₙ(U)` is integer multiplicity and minimizing in
`U ∩ N` (`N` an embedded `C²` `(n+ℓ)`-submanifold, `(N̄ \ N) ∩ U = ∅`), `spt T ⊆ U ∩ N` and
`∂T = 0` in `U`, then `reg T` is dense in `spt T`. -/
def RegularSetDense : Prop :=
  ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n),
    IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ →
    IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T →
    T.support ⊆ closure (regularSet T)

/-- **Simon 7.4.3 (Theorem, p. 194)**, for a fixed `N` (`Nᵢ = N`).  Let `Tᵢ, T` be minimizing in
`U ∩ N`, `spt Tᵢ, spt T ⊆ N`, `∂Tᵢ = ∂T = 0` in `U`, `Tᵢ ⇀ T`, with
`supᵢ M_W(Tᵢ) < ∞` for `W ⊂⊂ U`.  If `y ∈ N ∩ U`, `Θⁿ(μ_T, y) = 1`, `y = lim yⱼ`, `yⱼ ∈ spt Tⱼ`,
then `y ∈ reg T` and `yⱼ ∈ reg Tⱼ` for all large `j`.
*Deviations*: the book allows `Nᵢ → N` "in the `C²` sense" (not defined at this point of the
book); we take `Nᵢ = N`.  The local mass bound is the hypothesis of 7.2.4, which the proof uses
for `μ_{Tⱼ} → μ_T`; it is added explicitly. -/
def DensityOneImpliesRegular : Prop :=
  ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (Ts : ℕ → GeometricCurrentOn U n)
      (T : GeometricCurrentOn U n) (ys : ℕ → Euclid (n + k)) (y : Euclid (n + k)),
    IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ →
    (∀ j, IsMinimizingIn (Ts j) (U ∩ N)) → IsMinimizingIn T (U ∩ N) →
    (∀ j, (Ts j).support ⊆ N) → T.support ⊆ N →
    (∀ j, BoundaryVanishes (Ts j)) → BoundaryVanishes T →
    (∀ W : Set (Euclid (n + k)), IsOpen W → CompactlyContained W U → ⨆ j, (Ts j).massOn W < ∞) →
    WeaklyConvergesOn Ts T → y ∈ N ∩ U → HasMassDensity T y 1 →
    Tendsto ys atTop (𝓝 y) → (∀ j, ys j ∈ (Ts j).support) →
    y ∈ regularSet T ∧ ∀ᶠ j in atTop, ys j ∈ regularSet (Ts j)

/-- **Simon 7.4.4 (Theorem, p. 194).**  If `T` is as in 7.4.2 and `ξ ∈ spt T` has
`Θⁿ(μ_T, ξ) < 2`, then there is `ρ > 0` with `H^{n−2+α}(sing T ∩ B_ρ(ξ)) = 0` for all `α > 0`. -/
def SingularSetSmallWhereDensityBelowTwo : Prop :=
  ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n),
    IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ →
    IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T →
    ∀ ξ ∈ T.support, ∀ θ : ℝ, HasMassDensity T ξ θ → θ < 2 →
      ∃ ρ : ℝ, 0 < ρ ∧ ∀ α : ℝ, 0 < α → μH[(n : ℝ) - 2 + α] (singularSet T ∩ ball ξ ρ) = 0

/-- **Simon 7.4.5 (Theorem, p. 195).**  If `C ∈ 𝒟ₙ(ℝ^{n+k})` is minimizing in `ℝ^{n+k}`, `∂C = 0`,
`C` is a cone, and `spt C ⊆ H̄` for an open half-space `H = {x : v · x > 0}` (`v ≠ 0`, so
`0 ∈ ∂H`), then `spt C ⊆ ∂H`. -/
def HalfSpaceConeLiesInBoundary : Prop :=
  ∀ (n k : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid (n + k))) n) (v : Euclid (n + k)),
    IsMinimizingIn C univ → BoundaryVanishes C → IsConeCurrent C → v ≠ 0 →
    C.support ⊆ closure {x | 0 < inner ℝ v x} → C.support ⊆ frontier {x | 0 < inner ℝ v x}

/-- **Simon 7.5.8 (Theorem, p. 200).**  Let `N ∈ 𝒪` (oriented by `ξN`), `E ⊆ N ∩ U`
`H^{n+1}`-measurable, `T = ∂[[E]] ∈ 𝒟ₙ(U)` integer multiplicity and minimizing in `N ∩ U`.  Then
`sing T = ∅` if `n ≤ 6`; `sing T` is locally finite in `U` (finite on compact subsets of `U`) if
`n = 7`; `H^{n−7+α}(sing T) = 0` for all `α > 0` if `n > 7`.  (`N = ℝ^{n+1}` is the case `k = 1`.)
-/
def CodimensionOneRegularity : Prop :=
  ∀ (n k : ℕ) (U N E : Set (Euclid (n + k))) (ξN : Euclid (n + k) → MultiVector (n + k) (n + 1))
      (T : GeometricCurrentOn U n),
    IsOpen U → InClassO n U N ξN → MeasurableSet E → E ⊆ N ∩ U → IsBoundaryOfRegion T E ξN →
    IsMinimizingIn T (N ∩ U) →
    (n ≤ 6 → singularSet T = ∅) ∧
    (n = 7 → ∀ K : Set (Euclid (n + k)), IsCompact K → K ⊆ U → (singularSet T ∩ K).Finite) ∧
    (7 < n → ∀ α : ℝ, 0 < α → μH[(n : ℝ) - 7 + α] (singularSet T) = 0)

/-- **Simon 7.5.11 (Corollary, p. 202).**  If `T` is as in 7.5.8, `T = τ(M, θ, ξ)`, and
`T₁ ∈ 𝒟ₙ(U)` is obtained by equipping a connected component `M₁` of `reg T` with multiplicity
`1` and the orientation `ξ` of `T`, then `∂T₁ = 0` in `U` and `T₁` is minimizing in `U ∩ N`. -/
def RegularComponentsAreMinimizing : Prop :=
  ∀ (n k : ℕ) (U N E : Set (Euclid (n + k))) (ξN : Euclid (n + k) → MultiVector (n + k) (n + 1))
      (T : GeometricCurrentOn U n),
    IsOpen U → InClassO n U N ξN → MeasurableSet E → E ⊆ N ∩ U → IsBoundaryOfRegion T E ξN →
    IsMinimizingIn T (N ∩ U) →
    ∀ R : IMRep U n, R.Represents T → ∀ y ∈ regularSet T, ∀ T₁ : GeometricCurrentOn U n,
      (∀ ω : TestFormOn U n, T₁ ω = ∫ x in connectedComponentIn (regularSet T) y,
        R.orient x ((ω : DifferentialForm (Euclid (n + k)) n) x) ∂μHE[n]) →
      BoundaryVanishes T₁ ∧ IsMinimizingIn T₁ (U ∩ N)

end

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `accepted`.

# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1`
- Child DAG node: `root.dimension_reduction_results-a1.threshold_reduction-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the common part of the proofs of Simon 7.3.3(1), 7.4.4 and 7.5.8 (chapter-07.txt lines 420–510, 641–684, 919–974) as organised in parent steps T3, T4, T5 and T9 (departure [D1]: Appendix A is applied to scalar density functions with the threshold map sing^c φ := closure{⟨φ, e₁⟩ ≥ c}, so that A.3(2) holds exactly), followed by the sibling abstract_dimension_reduction (DAG node root.abstract_dimension_reduction-a1, Appendix A.4 with (H0)). Notation: P := n + k; η_{y,λ}(w) := λ^{−1}(w − y); for an integer multiplicity current A, μ_A is the measure of any representation (sibling child im_mass_measure: all representations have the same measure (c), M_W(A) = μ_A(W) for open W in the domain (a), spt A = spt μ_A there (b)), and Θ_A := Θ^n(μ_A, ·); ω_n := unitBallVolume n; H^n := μHE[n] = c_n·μH[n] with c_n ∈ (0, ∞).
1. (Facts for T and rescaling.) By the sibling child monotonicity (with d := n + ℓ): Θ_T exists at every point of U, Θ_T ≥ 1 on spt T, and for K := closedBall z (2r) there is Λ_K ≥ 0 with e^{Λ_Kρ}ρ^{−n}μ_T(B_ρ(y)) nondecreasing on (0, R) whenever closedBall y R ⊆ K; Θ_T is upper semicontinuous on U (part (iii) of that child). Let T' be the restriction of η_{z,r#}T (blowUp T z r) to B_2(0) ⊆ η_{z,r}(U) (restrictDomain). T' is integer multiplicity, minimizing in B_2(0) ∩ N' with N' := η_{z,r}(N) an embedded C² (n+ℓ)-submanifold, (closure N' ∖ N') ∩ B_2(0) = ∅, spt T' ⊆ N', ∂T' = 0 in B_2(0) (a competitor of T' in W ⊂⊂ B_2(0) differs from T' by a compactly supported current, so pushing it forward by η_{z,r}^{−1} and adding T gives a competitor of T; masses scale by r^n). m₀ := μ_{T'}(B_2(0)) = r^{−n}μ_T(B_{2r}(z)) < ∞, Θ_{T'}(w) = Θ_T(z + rw), and with Λ₀ := rΛ_K: e^{Λ₀ρ}ρ^{−n}μ_{T'}(B_ρ(y)) is nondecreasing on (0, R) whenever closedBall y R ⊆ closedBall 0 2. Under any dilation, μ_{η_{y,λ#}A} = λ^{−n}(η_{y,λ})_#μ_A and Θ_{η_{y,λ#}A}(w) = Θ_A(y + λw). If T' = 0 then Θ_T = 0 < c on B_{2r}(z), so Z(r) = ∅ and all conclusions hold; assume T' ≠ 0, so m₀ > 0, and let b₀ be the barycenter of the finite measure μ_{T'}.
2. (The class 𝒯; parent T4.) 𝒯 is the set of pairs (S, U_S) for which there are x_i ∈ ℝ^P and λ_i ∈ (0, 1) with |x_i| < 1 − λ_i, x_i → x, λ_i → λ ∈ [0, 1], U_S := η_{x,λ}(B_2(0)) = B_{2/λ}(−x/λ) if λ > 0 and U_S := ℝ^P if λ = 0, S ∈ 𝒟_n(U_S), and for every ω ∈ 𝒟^n(U_S) eventually tsupport ω ⊆ η_{x_i,λ_i}(B_2(0)) and (η_{x_i,λ_i#}T')(ω) → S(ω); (x, λ) are the parameters. Properties: (a) If λ > 0 then S = η_{x,λ#}T' (as η_{x_i,λ_i}^#ω → η_{x,λ}^#ω in 𝒟^n(B_2(0))); U_S ⊇ B_2(0) because |x| ≤ 1 − λ; μ_S(ℝ^P) = λ^{−n}m₀ ∈ (0, ∞); spt μ_S ⊆ closedBall (−x/λ) (2/λ); the barycenter of μ_S is (b₀ − x)/λ; Θ_S(w) = Θ_T(z + r(x + λw)) on U_S; and e^{Λ₀ρ}ρ^{−n}μ_S(B_ρ(y)) is nondecreasing on (0, R) whenever closedBall y R ⊆ closedBall 0 2 (since η_{x,λ}^{−1}(closedBall y R) = closedBall (x + λy) (λR) ⊆ closedBall 0 2 and λΛ₀ ≤ Λ₀). (T', B_2(0)) ∈ 𝒯 (x_i = 0, λ_i = 1 − 1/(i + 2)). (b) If λ = 0 then, since η_{x_i,λ_i}∘η_{z,r} = η_{z+rx_i, rλ_i} and the domains η_{x_i,λ_i}(B_2(0)) eventually contain every compact set, S is the ConvergesWeakly-limit of blowUp T (z + rx_i) (rλ_i), with z + rx_i ∈ B_r(z) and rλ_i → 0. By the sibling child moving_blowups (centre z + rx ∈ closedBall z r ⊆ U) a subsequence converges to an integer multiplicity C, minimizing in ℝ^P with ∂C = 0 and mass measure convergence; weak limits are unique, so S = C. Hence S is an admissible zero-scale limit, and (every subsequence having a further subsequence with measure convergence) μ_{η_{x_i,λ_i#}T'} → μ_S vaguely on ℝ^P. By the sibling child monotonicity applied to S (U = N = ℝ^P, d := P; ℝ^P is an embedded C² P-dimensional submanifold via the identity chart): ρ^{−n}μ_S(B_ρ(w)) is nondecreasing on (0, ∞), Θ_S exists everywhere and is upper semicontinuous on ℝ^P (part (iii)), Θ_S ≥ 1 on spt S, so μ_S(B_ρ(w)) ≥ ω_nρ^n for w ∈ spt S and μ_S(ℝ^P) ∈ {0, ∞}. (c) For (S, U_S) ∈ 𝒯 with parameters (x, λ), 0 < λ' < 1 and |y| ≤ 1 − λ': (η_{y,λ'#}S, η_{y,λ'}(U_S)) ∈ 𝒯 with parameters (x + λy, λλ'), because η_{y,λ'}∘η_{x_i,λ_i} = η_{x_i+λ_iy, λ_iλ'} and |x_i + λ_iy| < 1 − λ_iλ'. (d) (Uniform bounds; countable-test convergence criterion.) c₁ := e^{Λ₀}(4/3)^nm₀ bounds e^{Λ₀ρ}ρ^{−n}μ_{T'}(B_ρ(y)) for |y| ≤ 1 and 0 < ρ ≤ 3/4 (monotonicity on (0, 1) at y, as closedBall y 1 ⊆ closedBall 0 2, compared with ρ = 3/4). Put c₂ := max(c₁, 2^nm₀). Then μ_A(B_R(0)) ≤ c₂R^n for every R > 0 whenever A = η_{x',λ'#}T' with |x'| ≤ 1 and λ' ∈ (0, 1] (μ_A extended by 0 off the domain of A: μ_A(B_R(0)) = λ'^{−n}μ_{T'}(B_{λ'R}(x')), which is ≤ c₁R^n if λ'R ≤ 1/2 and ≤ λ'^{−n}m₀ < (2R)^nm₀ otherwise); in particular for every member with λ > 0 (A = η_{x,λ#}T', |x| ≤ 1 − λ, λ ≤ 1) and for every blow-up η_{x_i,λ_i#}T' occurring in the definition of 𝒯; for members with λ = 0 the bound follows by lower semicontinuity of mass under the defining convergence (for ω admissible for M_{B_R(0)}(S), S(ω) = lim_i (η_{x_i,λ_i#}T')(ω) ≤ liminf_i M_{B_R(0)}(η_{x_i,λ_i#}T') ≤ c₂R^n); and M_{B_R(0)}(A) = μ_A(B_R(0)) whenever B_R(0) lies in the domain of A (sibling child im_mass_measure (a)). (Countable-test criterion for limits on ℝ^P approximated by currents whose domains exhaust ℝ^P.) Fix a countable family {ω_m} ⊆ 𝒟^n(ℝ^P) such that for every R ∈ ℕ, every ω ∈ 𝒟^n(ℝ^P) with tsupport ω ⊆ B_R(0) and every ε > 0 there is m with tsupport ω_m ⊆ B_{R+1}(0) and sup_w |ω(w) − ω_m(w)| < ε (|·| the Euclidean coefficient norm); for instance the forms χ_R·Σ_I p_I dx^I (R ∈ ℕ, I increasing multi-indices) with a fixed χ_R ∈ C^∞_c(B_{R+1}(0); [0, 1]) equal to 1 on closedBall 0 R and polynomials p_I with rational coefficients: approximate the coefficients of ω uniformly on closedBall 0 (R + 1) by such p_I (Weierstrass); since ω = 0 off B_R(0) and χ_R = 1 on closedBall 0 R, sup|ω − χ_R·p| ≤ sup_{closedBall 0 (R+1)}|ω − p|. Criterion (C): let V_k ⊆ ℝ^P be open, A_k ∈ 𝒟_n(V_k) and A ∈ 𝒟_n(ℝ^P), and suppose that for every R ∈ ℕ there are k_R ∈ ℕ and Γ_R < ∞ with B_{R+1}(0) ⊆ V_k and M_{B_{R+1}(0)}(A_k) ≤ Γ_R for all k ≥ k_R, and M_{B_{R+1}(0)}(A) ≤ Γ_R. If A_k(ω_m) → A(ω_m) for every m (for k ≥ k_R these values are defined when tsupport ω_m ⊆ B_{R+1}(0)), then currentEval(A_k, ω) → A(ω) for every ω ∈ 𝒟^n(ℝ^P), i.e. A_k ⇀ A in ℝ^P (ConvergesWeakly). Proof: let tsupport ω ⊆ B_R(0) and ε > 0, and choose ω_m as above. For k ≥ k_R, tsupport ω ⊆ V_k, so currentEval(A_k, ω) = A_k(ω); a test form β with tsupport β ⊆ W (W open) and sup|β| ≤ s satisfies |A'(β)| ≤ s·M_W(A') for every current A' (if s > 0, ±β/s is admissible for M_W(A')), so |A_k(ω) − A_k(ω_m)| ≤ Γ_Rε and |A(ω) − A(ω_m)| ≤ Γ_Rε; hence limsup_k |currentEval(A_k, ω) − A(ω)| ≤ 2Γ_Rε for every ε > 0. (The criterion is used only for limits on all of ℝ^P approximated by currents whose domains exhaust ℝ^P, and no metric for weak convergence on varying bounded domains is used: for a limit on a bounded domain, currentEval vanishes at the limit on a form whose support meets the boundary of the limit domain, although it need not vanish along the approximants. For example, in ℝ (n = P = 1) let λ_i ↑ 1, A_i := [[(−2/λ_i, 2/λ_i)]] ∈ 𝒟_1((−2/λ_i, 2/λ_i)) and A := [[(−2, 2)]] ∈ 𝒟_1((−2, 2)): A_i ⇀ A in (−2, 2) and μ_{A_i} → μ_A vaguely there, but for ω = g dx with spt g = [−2, 2] and ∫g > 0, currentEval(A_i, ω) = ∫g > 0 for every i while currentEval(A, ω) = 0.) (e) (Tangent cones of members.) Let (S, U_S) ∈ 𝒯 have parameters (x, λ), |y| < 1 and λ_k ↓ 0. Case λ > 0. Since η_{y,λ_k}∘η_{x,λ} = η_{x+λy,λλ_k}, η_{y,λ_k#}S = η_{x+λy,λλ_k#}T'; these are the restrictions to η_{x+λy,λλ_k}(B_2(0)) of the blow-ups blowUp T (z + r(x + λy)) (rλλ_k) of T at z + r(x + λy) ∈ B_r(z) (|x + λy| < 1 − λ + λ = 1) with scales rλλ_k → 0, and their domains η_{x+λy,λλ_k}(B_2(0)) ⊇ B_{(2−|x+λy|)/(λλ_k)}(0) exhaust ℝ^P. If z + r(x + λy) ∈ spt T, the sibling density_and_tangent_cones (2) (boundarySupport T = ∅) gives a strictly increasing subsequence along which these blow-ups converge weakly in ℝ^P (ConvergesWeakly), with convergence of the mass measures (MassMeasuresConverge), to a minimizing cone C; otherwise T vanishes on a ball around z + r(x + λy), the blow-ups vanish on every ball B_R(0) for large k, and C := 0. Because every compact set eventually lies in η_{x+λy,λλ_k}(B_2(0)), on which η_{y,λ_k#}S agrees with the blow-up of T, η_{y,λ_k#}S ⇀ C in ℝ^P and μ_{η_{y,λ_k#}S} → μ_C vaguely on ℝ^P along the subsequence; and C is a member with parameters (x + λy, 0) via the sequence x'_k := x + λy, λ'_k := λλ_k (k so large that λλ_k < 1 − |x + λy|): for every ω ∈ 𝒟^n(ℝ^P), tsupport ω ⊆ η_{x'_k,λ'_k}(B_2(0)) for large k and (η_{x'_k,λ'_k#}T')(ω) = currentEval(blowUp T (z + r(x + λy)) (rλλ_k), ω) → C(ω). Case λ = 0. By (b), S is integer multiplicity and minimizing in ℝ^P with ∂S = 0. If y ∈ spt S, the sibling density_and_tangent_cones (2) (U = N = ℝ^P, ℓ := k, the codimension P − n) gives a strictly increasing subsequence along which η_{y,λ_k#}S ⇀ C in ℝ^P and μ_{η_{y,λ_k#}S} → μ_C vaguely, C a minimizing cone; if y ∉ spt S, η_{y,λ_k#}S vanishes on every B_R(0) for large k and C := 0. Diagonal selection: pass to that subsequence, discard the k with λ_k ≥ 1 − |y|, and let (x_i, s_i) be a defining sequence of S (x_i → x, s_i ∈ (0, 1), s_i → 0, |x_i| < 1 − s_i, and η_{x_i,s_i#}T' → S in the sense of the definition of 𝒯; the letter s_i is used to distinguish these scales from the tangent scales λ_k). For each k and i put A_{k,i} := η_{x_i+s_iy,s_iλ_k#}T', a current on η_{x_i+s_iy,s_iλ_k}(B_2(0)). As η_{y,λ_k}∘η_{x_i,s_i} = η_{x_i+s_iy,s_iλ_k}, A_{k,i}(ω) = (η_{x_i,s_i#}T')(η_{y,λ_k}^#ω) whenever tsupport ω lies in the domain of A_{k,i}; since η_{y,λ_k}^#ω ∈ 𝒟^n(ℝ^P), the defining property of S gives, for fixed k and ω ∈ 𝒟^n(ℝ^P): tsupport ω lies in the domain of A_{k,i} for all large i, and A_{k,i}(ω) → S(η_{y,λ_k}^#ω) = (η_{y,λ_k#}S)(ω) as i → ∞. Choose i(1) < i(2) < ⋯ with s_{i(k)} < 1/k, |x_{i(k)} − x| < 1/k, and, for all m ≤ k, tsupport ω_m inside the domain of A_{k,i(k)} and |A_{k,i(k)}(ω_m) − (η_{y,λ_k#}S)(ω_m)| < 1/k (finitely many conditions, each holding for all large i). Put D_k := A_{k,i(k)}, x'_k := x_{i(k)} + s_{i(k)}y and λ'_k := s_{i(k)}λ_k. Then λ'_k ∈ (0, 1), λ'_k → 0, x'_k → x, and |x'_k| < 1 − s_{i(k)} + s_{i(k)}|y| ≤ 1 − s_{i(k)}λ_k = 1 − λ'_k (as |y| ≤ 1 − λ_k). Eventual support containment: the domain of D_k is η_{x'_k,λ'_k}(B_2(0)) = B_{2/λ'_k}(−x'_k/λ'_k) ⊇ B_{1/λ'_k}(0) because |x'_k| < 1, so every compact subset of ℝ^P lies in the domain of D_k for all large k. Mass bounds: by (d), M_{B_{R+1}(0)}(D_k) ≤ c₂(R + 1)^n as soon as B_{R+1}(0) lies in the domain of D_k, and M_{B_{R+1}(0)}(C) ≤ liminf_k M_{B_{R+1}(0)}(η_{y,λ_k#}S) ≤ c₂(R + 1)^n by lower semicontinuity of mass, η_{y,λ_k#}S being a member by (c) (0 < λ_k < 1, |y| ≤ 1 − λ_k). Tests: for each m and all k ≥ m, |D_k(ω_m) − C(ω_m)| < 1/k + |(η_{y,λ_k#}S)(ω_m) − C(ω_m)| → 0. By criterion (C) of (d), D_k ⇀ C in ℝ^P, i.e. for every ω ∈ 𝒟^n(ℝ^P), tsupport ω ⊆ η_{x'_k,λ'_k}(B_2(0)) for large k and (η_{x'_k,λ'_k#}T')(ω) → C(ω): C is a member with parameters (x, 0) = (x + λy, 0). In both cases, along the chosen strictly increasing subsequence, μ_{η_{y,λ_k#}S} → μ_C vaguely on ℝ^P and C is a cone. (f) A member with μ_S ≠ 0 and μ_S(λA) = λ^nμ_S(A) for all λ > 0, or with μ_S(ℝ^P) = ∞, has parameter λ = 0 (members with λ > 0 have finite positive total mass, which a nonzero n-homogeneous measure cannot have).
3. (Density functions; parent T5.) Let e₁ be the unit vector of Euclid 1, H^n := μHE[n], and c_n := addHaarScalarFactor(volume, μH[n]) ∈ ℝ≥0 (the scalar in Mathlib's definition μHE[n] = c_n·μH[n]); c_n ≠ 0 (addHaarScalarFactor_volume_hausdorffMeasure_ne_zero), so c_n ∈ (0, ∞) and H^n = c_n·μH[n]. Consider integer multiplicity currents A on open sets V_A ⊆ ℝ^P whose mass measure μ_A, extended by 0 outside V_A, is locally finite on ℝ^P; these include all members (finite total mass if λ > 0, μ_S(B_R(0)) ≤ c₂R^n if λ = 0, by 2(d)), all their rescalings η_{y,λ#}S, and the cones C of 2(e). For such A put ϑ_A(w) := limsup_{ρ↓0} μ_A(B_ρ(w))/(ω_nρ^n) when finite and 0 otherwise, and φ_A(w) := ϑ_A(w)·e₁; write ϑ_S, φ_S for members. Then: (i) ϑ_S = Θ_S on U_S (densities exist there by 2(a), 2(b)). (ii) ϑ_A is Borel. (iii) μ_A = ϑ_A·H^n as measures on ℝ^P (Θ^n(μ_A, ·) equals the multiplicity H^n-a.e. on the carrier by Simon Ch. 3, Theorem 1.9 and Ch. 4, Remark 1.8(2), and the upper density vanishes H^n-a.e. off the carrier by Simon Ch. 1, Theorem 3.6 with Remark 3.7(2), applied to the locally finite measure μ_A on ℝ^P). (iv) (Normalization.) Since H^n = c_n·μH[n], (iii) gives μ_A = c_n·ϑ_A·μH[n], i.e. ∫ g·ϑ_A dμH[n] = c_n^{−1}·∫ g dμ_A for every bounded Borel g with compact support; in particular ∫_K ϑ_A dμH[n] = c_n^{−1}·μ_A(K) < ∞ for every compact K, so φ_A (Borel, ‖φ_A‖ = ϑ_A) is locally μH[n]-integrable. (H0) holds for members: if φ_S = φ_{S'} μH[n]-a.e., then ϑ_S = ϑ_{S'} H^n-a.e. (e₁ ≠ 0) (H^n and μH[n] have the same null sets), so μ_S = μ_{S'} by (iii), hence ϑ_S = ϑ_{S'} everywhere (ϑ is computed from μ) and φ_S = φ_{S'}. (v) (Correctly normalized weak pairings.) For every continuous compactly supported f : ℝ^P → ℝ, ∫ f·φ_A dμH[n] = (∫ f·ϑ_A dμH[n])·e₁ = c_n^{−1}(∫ f dμ_A)·e₁. Hence, for currents A_k, A as above, φ_{A_k} ⇀ φ_A in the sense of the sibling abstract_dimension_reduction (∫ f·φ_{A_k} dμH[n] → ∫ f·φ_A dμH[n] for all such f) if and only if ∫ f dμ_{A_k} → ∫ f dμ_A for all such f, i.e. μ_{A_k} → μ_A vaguely on ℝ^P (the factor c_n^{−1} ∈ (0, ∞) and the vector e₁ are fixed). (vi) φ_{η_{y,λ#}A}(w) = φ_A(y + λw) for all w (μ_{η_{y,λ#}A} = λ^{−n}(η_{y,λ})_#μ_A, so μ_{η_{y,λ#}A}(B_ρ(w)) = λ^{−n}μ_A(B_{λρ}(y + λw))). (vii) φ_C(λw) = φ_C(w) for cones C (μ_C(λB) = λ^nμ_C(B) for Borel B and λ > 0). Put F := {φ_S : (S, U_S) ∈ 𝒯}, a set of functions ℝ^P → Euclid 1. Then F satisfies (H0) and local integrability by (iv), A.1 by 2(c) and (vi), and A.2: given φ_S ∈ F, |y| < 1 and a strictly decreasing sequence λ_k > 0 with λ_k → 0, 2(e) gives a strictly increasing subsequence k_i and a member cone C with μ_{η_{y,λ_{k_i}#}S} → μ_C vaguely on ℝ^P, so φ_S(y + λ_{k_i}·) = φ_{η_{y,λ_{k_i}#}S} ⇀ φ_C ∈ F by (vi) and (v), and φ_C is homogeneous by (vii).
4. (Semicontinuity along members; parent T3.) Let (S_k, U_{S_k}), (S, U_S) ∈ 𝒯 with μ_{S_k} → μ_S vaguely on ℝ^P, and w_k → w with |w| ≤ 1. Then Θ_S(w) ≥ limsup_k Θ_{S_k}(w_k). Indeed B_2(0) ⊆ U_{S_k} ∩ U_S, and all members satisfy the monotonicity of 2(a)/(b) with the common constant Λ₀ on balls inside closedBall 0 2. For ρ, η > 0 with ρ + η < 1/2 and large k (|w_k − w| < η): Θ_{S_k}(w_k) ≤ e^{Λ₀ρ}μ_{S_k}(B_ρ(w_k))/(ω_nρ^n) ≤ e^{Λ₀ρ}μ_{S_k}(closedBall w (ρ + η))/(ω_nρ^n), and limsup_k μ_{S_k}(closedBall w (ρ + η)) ≤ μ_S(closedBall w (ρ + η)) (vague convergence, compact set); let η ↓ 0 and then ρ ↓ 0.
5. (The threshold map; parent T9.) For any φ : ℝ^P → Euclid 1 put sing φ := closure{w : ⟨φ(w), e₁⟩ ≥ c}. (α) sing φ is closed. (β) A.3(2) holds exactly for every φ: sing(φ(y + λ·)) = {w : y + λw ∈ sing φ}, since w ↦ y + λw is a homeomorphism. (γ) For members, {w ∈ U_S : Θ_S(w) ≥ c} is relatively closed in U_S (upper semicontinuity of Θ_S on U_S: for λ > 0 inherited from Θ_T, for λ = 0 from 2(b)) and U_S is open, so sing φ_S ∩ U_S = {w ∈ U_S : Θ_S(w) ≥ c}; for parameter-0 members sing φ_S = {w : Θ_S(w) ≥ c}. (δ) A.3(1): let φ_S ∈ F with φ_S = 1_Q·c'' for an n-dimensional subspace Q and c'' ∈ Euclid 1; write c' := ⟨c'', e₁⟩, so φ_S takes the values c'e₁ on Q and 0 off Q. If c' < c, then {⟨φ_S, e₁⟩ ≥ c} = ∅ (c > 0), so sing φ_S = ∅. If c' ≥ c > 0, then ϑ_S = c'·1_Q and μ_S = c'H^n⌞Q by 3(iii), which has infinite total mass; by 2(f) S has parameter 0, so by 2(b) S is an admissible zero-scale limit (with centres z + rx_i ∈ B_r(z), scales rλ_i → 0), minimizing in ℝ^P with ∂S = 0, and by 3(i) HasMassDensity S y (1_Q(y)·c') for every y; this contradicts (H1). So sing φ = ∅ for every such φ ∈ F. (ε) A.3(3): let φ_{S_k} ⇀ φ_S in F (so μ_{S_k} → μ_S vaguely by 3(v)) and ε > 0, and suppose that for infinitely many k there is w_k ∈ B_1(0) ∩ sing φ_{S_k} with dist(w_k, sing φ_S) ≥ ε. As B_1(0) ⊆ B_2(0) ⊆ U_{S_k}, (γ) gives Θ_{S_k}(w_k) ≥ c. Passing to a subsequence, w_k → w with |w| ≤ 1, and step 4 gives Θ_S(w) ≥ c, so w ∈ sing φ_S by (γ) (w ∈ B_2(0) ⊆ U_S), contradicting dist(w_k, sing φ_S) ≥ ε for large k. Hence for large k, B_1(0) ∩ sing φ_{S_k} ⊆ {x : ∃ z' ∈ sing φ_S, dist(x, z') < ε}.
6. (Applying Appendix A.4.) The sibling abstract_dimension_reduction applies to (P, n, Q := 1, F, sing): (H0), local integrability, A.1, A.2 by step 3; closedness, A.3(1), A.3(2), A.3(3) by step 5. So either (I) B_1(0) ∩ sing φ = ∅ for every φ ∈ F, or (II) there is d ∈ ℕ with d + 1 ≤ n such that μH[d + α](sing φ ∩ B_1(0)) = 0 for all φ ∈ F and α > 0, there are ψ ∈ F and a linear subspace L with dim L = d, sing ψ = L and ψ(y + λx) = ψ(x) for all y ∈ L, λ > 0, x, and, if d = 0, sing φ ∩ B_σ(0) is finite for all φ ∈ F and σ < 1.
7. (Case (II) forces d < d₀.) Suppose (II) holds with d₀ ≤ d, and write ψ = φ_S with (S, U_S) ∈ 𝒯. Since c > 0, sing 0 = ∅ ≠ L (0 ∈ L), so ψ ≠ 0 and μ_S ≠ 0; ψ is homogeneous (take y = 0), so by 3(iii) μ_S(λA) = λ^nμ_S(A), and by 2(f) S has parameter 0. By 2(b), S is an admissible zero-scale limit: S is the ConvergesWeakly-limit of blowUp T (z + rx_i) (rλ_i) with z + rx_i ∈ B_r(z), rλ_i → 0, and S is minimizing in ℝ^P with ∂S = 0. By 3(i), ϑ_S = Θ_S everywhere, so the invariance of ψ gives: HasMassDensity S w θ implies HasMassDensity S (y + λw) θ for y ∈ L, λ > 0 (Θ_S exists everywhere and Θ_S(y + λw) = Θ_S(w)); and by 5(γ), {y : Θ_S(y) ≥ c} = sing ψ = L. Moreover d₀ ≤ d = dim L < n. This contradicts (H2). Hence in case (II), d ≤ d₀ − 1 (in particular d₀ ≥ 1).
8. (Conclusions.) By 5(γ) and the scaling of densities, sing φ_{T'} ∩ B_1(0) = {w ∈ B_1(0) : Θ_{T'}(w) ≥ c} = {w : z + rw ∈ Z(r)}, i.e. Z(r) = z + r·(sing φ_{T'} ∩ B_1(0)) (for x ∈ B_r(z), ∃θ ≥ c with HasMassDensity T x θ iff Θ_T(x) ≥ c, as densities exist and are unique). In case (I), Z(r) = ∅, and all three conclusions hold (μH[s](∅) = 0 for every real s). In case (II), d ≤ d₀ − 1 by step 7; for α > 0, s := d₀ − 1 + α = d + α' with α' := d₀ − 1 − d + α > 0, so μH[s](sing φ_{T'} ∩ B_1(0)) = 0 and, since w ↦ z + rw is a similarity with ratio r and s > 0, μH[s](Z(r)) = r^s·0 = 0. If d₀ = 0, case (II) is impossible (d ≤ −1), so Z(r) = ∅. If d₀ = 1 then, in case (II), d = 0 and sing φ_{T'} ∩ B_{1/2}(0) is finite, so Z(r/2) = z + r·(sing φ_{T'} ∩ B_{1/2}(0)) is finite; in case (I), Z(r/2) = ∅.

## Key steps

1. Rescale to T' = (η_{z,r#}T)⌞B_2(0) and form Simon's class 𝒯 of limits of η_{x_i,λ_i#}T'; parameter-0 members are admissible zero-scale limits of blow-ups of T (via moving_blowups), minimizing with ∂ = 0.
2. Scalar density functions φ_S = ϑ_S·e₁ with the correct normalization μ_S = c_n·ϑ_S·μH[n] (H^n = μHE[n] = c_n·μH[n]), so ∫_K ϑ_S dμH[n] = c_n⁻¹·μ_S(K) and weak convergence of the φ_S is vague convergence of the μ_S; they satisfy (H0), local integrability, A.1 and A.2 (tangent cones of members are members, via an explicit diagonal selection with a countable-test criterion for limits on ℝ^P with exhausting domains).
3. The threshold map sing φ = closure{⟨φ, e₁⟩ ≥ c} is closed, satisfies A.3(2) exactly, A.3(1) by hypothesis (H1), and A.3(3) by upper semicontinuity of densities along members.
4. Appendix A.4 (sibling abstract_dimension_reduction) gives (I) or (II); in (II) the extremal ψ = φ_S is a homogeneous L-invariant parameter-0 member with {Θ_S ≥ c} = L, so hypothesis (H2) forces dim L < d₀.
5. Rescaling back gives μH[d₀ − 1 + α](Z(r)) = 0, Z(r) = ∅ if d₀ = 0, and finiteness of Z(r/2) if d₀ = 1.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD (compared with manifest.json)`
- `grep -n 'μHE\|euclideanHausdorffMeasure' local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean; rg -n addHaarScalarFactor_volume_hausdorffMeasure_ne_zero (same file)`
- `grep -rn 'theorem massOn_le_liminf\|theorem boundary_affinePushforward\|exp_normalizedBallMass_monotoneOn\|theorem bvVariationOn_le_liminf_of_locallyL1\|theorem cone_simonsDefect_lower_bound' simongmt/Poincare`
- `grep -n 'def support\|zeroRegion\|def massOn' simongmt/Poincare/SimonGMT/Chapter06/*.lean`
- `grep -rn dimred --include=*.lean GMT .lake/packages/simongmt/Poincare; grep -c dimred dag.json; grep -rln dimred_ .swarm-worktrees/*/gmt-ch07/GMT (no match anywhere)`
- `python3 inspection of dag.json: sibling lean_statements (abstract_dimension_reduction, density_and_tangent_cones, density_one_implies_regular, compactness_of_minimizing_currents, minimizing_implies_stationary) and similar lemma nodes in other branches (dtc_mass_eq_measure, dor_imrep_massOn_eq_measure_and_support, dtc_dim_zero_eq_zero, imrep_measure_eq_of_represents_same_current, rsd_massOn_eq_measure)`
- `lean -R /tmp/dr-v2-check/src /tmp/dr-v2-check/src/CheckV2Types.lean (private olean of GMT.Ch07.Submission; 12 child types declared as Submission.X in namespace GMT.Ch07 with the contract opens; assembly ⟨A, B, C⟩; #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/MeanCurvature.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/AppendixB/ConeDefect.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1/decomposition-review-receipt-v1.json`
- `/tmp/dr-v2-check/src/CheckV2Types.lean`

Pins match. The snapshot has project b4d606d (equal to workspace HEAD), mathlib 25730c7c and simongmt 2b36630. The snapshot contract is byte-identical to the workspace Contract.lean and Submission.lean; its only sorry is the frozen main_theorem.

Normalization (decides correction R1). Mathlib defines μHE[d] = addHaarScalarFactor(volume, μH[d]) • μH[d] (Measure.lean, lines 68–101). The scalar is in ℝ≥0 and nonzero (addHaarScalarFactor_volume_hausdorffMeasure_ne_zero), so μ_A = ϑ_A·μHE[n] gives ∫_K ϑ_A dμH[n] = c_n⁻¹·μ_A(K).

SimonGMT definitions used:
- massOn is the sSup over admissible forms with Euclidean coefficient norm ≤ 1 (Mass.lean).
- support = U \ zeroRegion (CurrentLocalEquality.lean, lines 108–117).
- WeaklyConvergesOn.massOn_le_liminf (Mass.lean:100) gives the lower semicontinuity used for the new mass bounds.

Other cited library facts exist:
- GeometricCurrentOn.boundary_affinePushforward (AffineCurrentPushforward.lean:188);
- HasGeneralizedMeanCurvatureIn.exp_normalizedBallMass_monotoneOn (Chapter04/MeanCurvature.lean:361);
- bvVariationOn_le_liminf_of_locallyL1 (Chapter02/BV.lean:225);
- cone_simonsDefect_lower_bound (AppendixB/ConeDefect.lean:228).

The library provides none of the following for the contract's IMRep currents: the mass–measure identity, product currents, Federer–Fleming compactness, or Appendix A.4. These are children or sibling prerequisites.

Lean check. All twelve child types elaborate after import GMT.Ch07.Submission, in namespace GMT.Ch07 with the contract opens, with only the stub sorry warnings. The assembly ⟨A, B, C⟩ proves IntegerDensityAndTangentPlanes ∧ SingularSetSmallWhereDensityBelowTwo ∧ CodimensionOneRegularity, and the conditional assembly depends only on propext, Classical.choice and Quot.sound.

Names. No dimred_ identifier occurs in the workspace, SimonGMT, any speculative worktree or dag.json. Similar lemmas in other branches have different types and names, so there is neither reuse nor collision.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
