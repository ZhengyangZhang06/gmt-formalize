<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1.retraction_comparison-a1 -->

## Theorem `Submission.dimred_mbl_lc_retraction_comparison`

Let P, m ∈ ℕ, n := m + 1, U ⊆ ℝ^P open, A ⊆ ℝ^P, and T ∈ 𝒟_n(U) minimizing in A (contract IsMinimizingIn T A) with spt T ⊆ A. Let G, G₃, L ∈ ℝ with 0 < G ≤ G₃, closedBall(0, G₃) ⊆ U and M_{B_{G₃}(0)}(T) < ∞. Let π : ℝ^P → ℝ^P be C¹ on B_{2G}(0) (ContDiffOn ℝ 1), with π(B_{2G}(0)) ⊆ A ∩ B_{G₃}(0), π(y) = y for every y ∈ A ∩ B_{2G}(0), and ‖Dπ(y)‖ ≤ L (operator norm of fderiv) for every y ∈ B_{2G}(0). Let Y ∈ 𝒟_n(ℝ^P) be integer multiplicity with ∂Y = 0 and spt Y compact and contained in B_G(0), and let Z ∈ 𝒟_n(U) satisfy Z(ω) = T(ω) + Y(ω) for every ω ∈ 𝒟ⁿ(U) (Y evaluated on the same form regarded as a test form on ℝ^P, testFormOnInclusion). Assume the push-forward theorem (PF) for (P, m): for every open O ⊆ ℝ^P, every f : ℝ^P → ℝ^P that is C¹ on O and every c ∈ ℝ with ‖Df(y)‖ ≤ c for y ∈ O, there is a map push : 𝒟_n(ℝ^P) → 𝒟_n(ℝ^P) such that (A) for every X ∈ 𝒟_n(ℝ^P) with spt X compact and contained in O and every IMRep R = (M, θ, ξ) of X in ℝ^P: (i) push X(ω) = ∫_M θ(x)·ξ(x)(ω(f(x)) ∘ Λⁿ Df(x)) dHⁿ(x) for every ω ∈ 𝒟ⁿ(ℝ^P), (ii) push X is integer multiplicity, (iii) spt(push X) ⊆ f(spt X), (iv) M(push X) ≤ cⁿ·M(X) (ENNReal.ofReal(cⁿ)), (v) ∂X = 0 implies ∂(push X) = 0, (vi) if f(y) = y for every y ∈ spt X then push X = X; and (B) push(X₁ − X₂) = push X₁ − push X₂ for all integer multiplicity X₁, X₂ ∈ 𝒟_n(ℝ^P) with compact supports contained in O. Then M_{B_G(0)}(T) ≤ Lⁿ·M_{B_G(0)}(Z) in [0, ∞] (Lⁿ read as ENNReal.ofReal(Lⁿ)).

Node: `root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1.retraction_comparison-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5076

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/810, https://github.com/ZhengyangZhang06/gmt-formalize/issues/667, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4196, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1308, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4695, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4704, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4728

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/667, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4196, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1308, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4695, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4704, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4728, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7181, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7183, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7185, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7188, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7190

## Lean problem

Declaration: `Submission.dimred_mbl_lc_retraction_comparison`

```lean
∀ (P m : ℕ) (U A : Set (Euclid P)) (T Z : GeometricCurrentOn U (m + 1)) (Y : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (π : Euclid P → Euclid P) (G G₃ L : ℝ), IsOpen U → IsMinimizingIn T A → T.support ⊆ A → 0 < G → G ≤ G₃ → closedBall (0 : Euclid P) G₃ ⊆ U → T.massOn (ball 0 G₃) ≠ ∞ → ContDiffOn ℝ 1 π (ball 0 (2 * G)) → MapsTo π (ball 0 (2 * G)) (A ∩ ball 0 G₃) → (∀ y ∈ A ∩ ball 0 (2 * G), π y = y) → (∀ y ∈ ball (0 : Euclid P) (2 * G), ‖fderiv ℝ π y‖ ≤ L) → IsIntegerMultiplicity Y → Y.boundary = 0 → IsCompact Y.support → Y.support ⊆ ball 0 G → (∀ ω : TestFormOn U (m + 1), Z ω = T ω + Y (testFormOnInclusion (subset_univ U) (m + 1) ω)) → (∀ (O : Set (Euclid P)) (f : Euclid P → Euclid P) (c : ℝ), IsOpen O → ContDiffOn ℝ 1 f O → (∀ y ∈ O, ‖fderiv ℝ f y‖ ≤ c) → ∃ push : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1) → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), (∀ (X : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (R : IMRep (univ : Set (Euclid P)) (m + 1)), R.Represents X → IsCompact X.support → X.support ⊆ O → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), push X ω = ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (((ω : DifferentialForm (Euclid P) (m + 1)) (f x)).compContinuousLinearMap (fderiv ℝ f x)) ∂μHE[m + 1]) ∧ IsIntegerMultiplicity (push X) ∧ (push X).support ⊆ f '' X.support ∧ (push X).mass ≤ ENNReal.ofReal (c ^ (m + 1)) * X.mass ∧ (X.boundary = 0 → (push X).boundary = 0) ∧ ((∀ y ∈ X.support, f y = y) → push X = X)) ∧ ∀ X₁ X₂ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), IsIntegerMultiplicity X₁ → IsIntegerMultiplicity X₂ → IsCompact X₁.support → X₁.support ⊆ O → IsCompact X₂.support → X₂.support ⊆ O → push (X₁ - X₂) = push X₁ - push X₂) → T.massOn (ball 0 G) ≤ ENNReal.ofReal (L ^ (m + 1)) * Z.massOn (ball 0 G)
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

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1.retraction_comparison-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 7, case (P), items (a)–(e), up to the inequality (I) (Simon 7.2.4 (8)–(9), chapter-07.txt lines 220–246, modified as indicated in Remark 7.2.5(2), lines 165–174: competitors are pushed into A by the retraction π). Specialization: (I) is stated for masses, M_{B_G}(T) ≤ Lⁿ M_{B_G}(Z) with Z = T + Y; the parent's identification μ_{Q+Y}(B_G) = μ_{S_j+Y}(B_G) through (F2) is replaced by the direct inequality M_{B_G}(Q + Y) ≤ M_{B_G}(Z) (the two currents agree on forms supported in B_G), and the parent's μ_{Q+Y}(ℝ^P ∖ B_G) = 0 is proved by splitting ℝ^P ∖ B_G into the open set ℝ^P ∖ B̄_G and the compact sphere.
Siblings: (VO) vanish_off_support; (MR) mass_and_support; (IMC) im_calculus ((b) restriction, (c) differences, (d) orientation bound); (RO) restrict_open_im; (IR) imrep_restriction; (MT) mass_triangle; (COB) compact_outer_bound.
Conventions. B_r := B_r(0), B̄_r := closedBall(0, r), S_G := {x : |x| = G}. A test form ω ∈ 𝒟ⁿ(U) is also regarded as an element of 𝒟ⁿ(ℝ^P) (same form; testFormOnInclusion), and for X ∈ 𝒟_n(ℝ^P), X|_U := X.restrictDomain(U ⊆ ℝ^P), so X|_U(ω) = X(ω). For an IMRep R write μ_R := R.measure, ξ_R := R.orient. Note B̄_G ⊆ B̄_{G₃} ⊆ U, B̄_G ⊆ B_{2G} (G > 0) and B_G ⊆ B_{G₃}.
Preliminaries.
(p1) If X is a current in an open V and X(ω) = 0 for every ω ∈ 𝒟ⁿ(V) with tsupport ω ⊆ G, then M_G(X) = 0 (every term of the supremum is ofReal 0), and, if G is open and R is an IMRep of X, μ_R(G) = 0 by (MR).
(p2) (Support from vanishing.) If X ∈ 𝒟_n(ℝ^P), E ⊆ ℝ^P is closed and X(ω) = 0 whenever tsupport ω ∩ E = ∅, then spt X ⊆ E: a point x ∉ E has a ball B_r(x) disjoint from E, an open set with compact closure on which X vanishes, so x lies in the zero region. spt X is closed; if E is compact, spt X is compact.
(p3) (Sums.) For an integer multiplicity X in an open V, X − X = 0 is integer multiplicity by (IMC)(c); hence for integer multiplicity X, X′ in V, 0 − X′ and X + X′ := X − (0 − X′) are integer multiplicity, and (X + X′)(ω) = X(ω) + X′(ω).
(p4) (Restriction.) If X ∈ 𝒟_n(ℝ^P), then M_G(X|_U) ≤ M_G(X) for every G: a form admissible for M_G(X|_U) is admissible for M_G(X), with the same value.
(p5) (Local finiteness.) For an IMRep R in an open V and compact K′ ⊆ V, μ_R(K′) = ∫_{M∩K′} θ dHⁿ < ∞.
(p6) (Boundaries.) ∂(X − X′) = ∂X − ∂X′ and ∂(X|_U) = (∂X)|_U, by evaluation on dη.
1. (Push-forward.) Apply (PF) with O := B_{2G}, f := π, c := L, and obtain push. Fix an IMRep R_T = (M_T, θ_T, ξ_T) of T in U (T is integer multiplicity by minimality) and write μ_T := μ_{R_T}.
2. (The current Q := T⌞B_G in ℝ^P.) By (IMC)(b) in U with E := B_G there is an IMRep R₁ in U with carrier M_T ∩ B_G, multiplicity θ_T and orientation ξ_T; by (IR)(c), μ_{R₁} = μ_T⌞B_G and R₁.action(ω) = ∫_{B_G} ξ_T(ω) dμ_T for every n-form ω. The same carrier, multiplicity and orientation form an IMRep R₂ in ℝ^P: the fields of IMRep other than carrier ⊆ U and local integrability do not involve U; the carrier lies in ℝ^P; and for compact K′, ∫_{M_T∩B_G∩K′} θ_T dHⁿ ≤ ∫_{M_T∩B̄_G} θ_T dHⁿ < ∞ because B̄_G is a compact subset of U. By (IMC)(b) in ℝ^P with E := ℝ^P there is a current Q ∈ 𝒟_n(ℝ^P) represented by an IMRep R₃ with the same carrier (∩ ℝ^P), multiplicity and orientation. Hence Q is integer multiplicity, Q(ω) = R₁.action(ω) = ∫_{B_G} ξ_T(ω) dμ_T for every ω ∈ 𝒟ⁿ(ℝ^P), and μ_{R₃}(ℝ^P ∖ B_G) = 0 (its carrier lies in B_G).
 (Q1) If tsupport ω ⊆ B_G, then Q(ω) = T(ω): T(ω) = R_T.action(ω) = ∫ ξ_T(ω) dμ_T ((IR)(c), E := ℝ^P), and ω = 0 off B_G.
 (Q2) If tsupport ω ∩ B̄_G = ∅, then Q(ω) = 0, since ω = 0 on B_G.
 (Q3) spt Q ⊆ B̄_G ∩ spt T, and spt Q is compact. Let x ∉ B̄_G ∩ spt T. If x ∉ B̄_G, (Q2) and the argument of (p2) give x ∉ spt Q. If x ∈ B̄_G ∖ spt T, then x ∈ U ∖ spt T, so x lies in an open V with compact closure in U on which T vanishes; μ_T(V) = 0 by (p1); for ω with tsupport ω ⊆ V the integrand ξ_T(ω)·1_{B_G} vanishes off the μ_T-null set V, so Q(ω) = 0; hence x is in the zero region of Q. spt Q is closed and contained in the compact set B̄_G, hence compact.
 (Q4) spt Q ⊆ B̄_G ∩ spt T ⊆ B_{2G} ∩ A, where π is the identity. Q is admissible for (PF) and push Q = Q by (PF)(vi).
3. (Push of Y.) Y is admissible: integer multiplicity, spt Y compact and ⊆ B_G ⊆ O. By (PF): push Y is integer multiplicity, ∂(push Y) = 0, and spt(push Y) ⊆ π(spt Y) ⊆ π(B_{2G}) ⊆ A ∩ B_{G₃}. π is continuous on O (C¹) and spt Y ⊆ O is compact, so π(spt Y) is compact; spt(push Y) is closed and contained in it, hence compact; and spt(push Y) ⊆ B_{G₃} ⊆ U.
4. (Q + Y.) Put QY := Q − (0 − Y); it is integer multiplicity (p3) and QY(ω) = Q(ω) + Y(ω). If tsupport ω ∩ B̄_G = ∅ then Q(ω) = 0 by (Q2) and Y(ω) = 0 by (VO) (spt Y ⊆ B_G), so by (p2) spt QY ⊆ B̄_G is compact and contained in O. The currents 0 and 0 − Y are admissible: they are integer multiplicity (p3), spt 0 = ∅, and spt(0 − Y) = spt Y (both vanish on the same forms). By (PF)(B): push 0 = push(0 − 0) = push 0 − push 0, hence push 0 = 0 (evaluate at each ω); push(0 − Y) = push 0 − push Y = 0 − push Y; and push QY = push Q − push(0 − Y) = Q − (0 − push Y). So push QY(ω) = Q(ω) + push Y(ω) for every ω, and, QY being integer multiplicity, (PF)(iv) gives M(push QY) ≤ Lⁿ M(QY).
5. (The competitor.) (push Y)|_U is integer multiplicity by (RO) (U open), and Z₁ := T − (0 − (push Y)|_U) ∈ 𝒟_n(U) is integer multiplicity by (p3), with Z₁(ω) = T(ω) + push Y(ω).
 (i) ∂Z₁ = ∂T by (p6) and ∂(push Y) = 0; so SameBoundary Z₁ T.
 (ii) (Z₁ − T)(ω) = push Y(ω) for ω ∈ 𝒟ⁿ(U). If x ∈ U ∖ spt(push Y), push Y vanishes on an open V ∋ x; choosing r > 0 with closedBall(x, r) ⊆ U, the open set V ∩ B_r(x) has compact closure in U and Z₁ − T vanishes on it. Hence spt(Z₁ − T) ⊆ spt(push Y) ⊆ A ∩ B_{G₃}.
 (iii) spt(Z₁ − T) = U ∖ (zero region) is relatively closed in U and contained in the compact set spt(push Y) ⊆ U, so it equals spt(push Y) minus an open set and is compact.
 (iv) W′ := B_{G₃} is open and closure(W′) ⊆ B̄_{G₃} ⊆ U is compact (CompactlyContained W′ U).
 By minimality of T in A (with W′ and the competitor Z₁), M_{B_{G₃}}(T) ≤ M_{B_{G₃}}(Z₁).
6. (Upper bound for Z₁.) By (IMC)(b) in U with E := ℝ^P ∖ B_G there is a current T₁ ∈ 𝒟_n(U) represented by an IMRep R₄ with carrier M_T ∖ B_G; by (IR)(c), μ_{R₄} = μ_T⌞(ℝ^P ∖ B_G) and T₁(ω) = ∫_{ℝ^P∖B_G} ξ_T(ω) dμ_T. For ω ∈ 𝒟ⁿ(U) the function ξ_T(ω) is μ_T-integrable: it is μ_T-a.e. strongly measurable ((IR)(b), ω continuous), bounded μ_T-a.e. by sup_x|ω(x)| < ∞ ((IMC)(d) and (IR)(a)), and vanishes off the compact set tsupport ω ⊆ U, which has finite μ_T-measure (p5). So T(ω) = ∫ ξ_T(ω) dμ_T = ∫_{B_G} ξ_T(ω) dμ_T + ∫_{ℝ^P∖B_G} ξ_T(ω) dμ_T = Q(ω) + T₁(ω), and therefore Z₁(ω) = T₁(ω) + (push QY)|_U(ω) for every ω ∈ 𝒟ⁿ(U). (MT) with c = 1, (MR) for T₁ and (p4) give
 M_{B_{G₃}}(Z₁) ≤ M_{B_{G₃}}(T₁) + M_{B_{G₃}}((push QY)|_U) ≤ μ_T(B_{G₃} ∖ B_G) + M(push QY) ≤ μ_T(B_{G₃} ∖ B_G) + Lⁿ M(QY).
7. (Cancellation.) By (MR), M_{B_{G₃}}(T) = μ_T(B_{G₃}) = μ_T(B_G) + μ_T(B_{G₃} ∖ B_G), and this is finite by hypothesis. Steps 5 and 6 give μ_T(B_G) + μ_T(B_{G₃} ∖ B_G) ≤ μ_T(B_{G₃} ∖ B_G) + Lⁿ M(QY); cancelling the finite term, M_{B_G}(T) = μ_T(B_G) ≤ Lⁿ M(QY) ((MR) again).
8. (M(QY) ≤ M_{B_G}(Z).) Let R_{QY} be an IMRep of QY and R_Y one of Y. By (MR), M(QY) = μ_{R_{QY}}(ℝ^P) = μ_{R_{QY}}(B_G) + μ_{R_{QY}}(S_G) + μ_{R_{QY}}(ℝ^P ∖ B̄_G).
 (a) QY vanishes on forms supported in the open set ℝ^P ∖ B̄_G (step 4), so μ_{R_{QY}}(ℝ^P ∖ B̄_G) = 0 by (p1).
 (b) For every open G′ ⊇ S_G with compact closure, (MR) and (MT) with c = 1 give μ_{R_{QY}}(G′) = M_{G′}(QY) ≤ M_{G′}(Q) + M_{G′}(Y) = μ_{R₃}(G′) + μ_{R_Y}(G′). (COB) with U := ℝ^P, the compact set E := S_G, ν := μ_{R₃} + μ_{R_Y} (finite on compact sets, (p5)) and c := 0 gives μ_{R_{QY}}(S_G) ≤ μ_{R₃}(S_G) + μ_{R_Y}(S_G). Here μ_{R₃}(S_G) = 0 (carrier of R₃ ⊆ B_G); and Y vanishes on forms supported in the open set ℝ^P ∖ spt Y (VO), so μ_{R_Y}(ℝ^P ∖ spt Y) = 0 by (p1), while S_G ⊆ ℝ^P ∖ spt Y because spt Y ⊆ B_G. So μ_{R_{QY}}(S_G) = 0.
 (c) μ_{R_{QY}}(B_G) = M_{B_G}(QY) by (MR). If ω ∈ 𝒟ⁿ(ℝ^P) is admissible for M_{B_G}(QY), then, as tsupport ω ⊆ B_G ⊆ U, ω ∈ 𝒟ⁿ(U) is admissible for M_{B_G}(Z) and QY(ω) = Q(ω) + Y(ω) = T(ω) + Y(ω) = Z(ω) by (Q1). Hence M_{B_G}(QY) ≤ M_{B_G}(Z).
 So M(QY) ≤ M_{B_G}(Z), and step 7 gives M_{B_G}(T) ≤ Lⁿ M_{B_G}(Z). ∎

## Key steps

1. (PF) on B_{2G} gives push; Q := T⌞B_G is an integer multiplicity current in ℝ^P with spt Q ⊆ B̄_G ∩ spt T ⊆ A ∩ B_{2G}, so push Q = Q.
2. push(Q + Y) = Q + push Y (linearity, push 0 = 0) and M(push(Q + Y)) ≤ Lⁿ M(Q + Y).
3. Competitor Z₁ = T + (push Y)|_U: integer multiplicity, ∂Z₁ = ∂T, spt(Z₁ − T) compact in A ∩ B_{G₃}; minimality on B_{G₃}.
4. T = T⌞(ℝ^P ∖ B_G) + Q on 𝒟ⁿ(U); cancel the finite μ_T(B_{G₃} ∖ B_G) to get M_{B_G}(T) ≤ Lⁿ M(Q + Y).
5. M(Q + Y) ≤ M_{B_G}(Z): no mass off B̄_G, none on the sphere (compact_outer_bound), and Q + Y = Z on forms supported in B_G.

## Reference use

### local-project

Queries:
- `cat RUN/local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; cmp GMT/Ch07/Submission.lean GMT/Ch07/Contract.lean`
- `python3 scans of RUN/dag.json: accepted nodes (status accepted, candidate_commit set) whose lean_statement mentions IsIntegerMultiplicity, IMRep, restrictDomain or .support; children of root.compactness_of_minimizing_currents-a1.local_comparison-a1; lean_name collisions for dimred_mbl_lc_slice_decomposition / dimred_mbl_lc_retraction_comparison / dimred_mbl_lc_index_comparison (no match); string comparison of cmc_imRep_locality_restrict_sub with the second conjunct of dimred_mbl_current_foundations (identical)`
- `grep -n '_existing_lean_name_problem\|_accepted_checkpoint' /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py; grep -n 'contract_scope\|child_modules' verifier/gmt-compare.py`
- `grep -n 'def GeometricCurrentOn.massOn\|def GeometricCurrentOn.support\|def GeometricCurrentOn.restrictDomain\|def testFormOnInclusion\|def HasApproximateTangentSpaceAt\|def blowUpMap' in lake-packages-25730c7c/simongmt/Poincare/SimonGMT`
- `grep -rn "norm_fderiv_le_of_lip'\|iSup_comp_le\|protected theorem Tendsto.const_mul\|theorem limsup_le_limsup" lake-packages-25730c7c/mathlib/Mathlib`
- `sed -n 150,275p book/chapter-07.txt (Simon 7.2.4–7.2.5)`
- `lake env lean /tmp/lc_dec/Types.lean (all 12 child types as _root_ theorems after import GMT.Ch07.Submission in the replayed contract scope); lake env lean /tmp/lc_dec/Assembly.lean (#print axioms assembly_check)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-local-comparison-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-im-calculus-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-localize-a1-restrict-im-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-local-comparison-a1-imrep-1bd5f15878/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-local-comparison-a1-mass-triangle-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-local-comparison-a1-compac-a4168491cb/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-local-comparison-a1-mass-l-9981f1246a/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-local-comparison-a1-good-s-2d2986292d/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/lc_dec/Types.lean`
- `/tmp/lc_dec/Assembly.lean`

Pins match the manifest (project b4d606d, Mathlib 25730c7c, SimonGMT 2b366308) and Submission.lean equals the frozen contract. Nine comparator-accepted declarations with candidate commits supply this proof's foundational facts and are reused with byte-identical types: dtc_vanish_off_support (VO), dor_imrep_massOn_eq_measure_and_support (MR), cmc_imRep_locality_restrict_sub (IMC; equal to the second conjunct of the decomposing sibling foundations), dtc_restrictDomain_isIntegerMultiplicity (F5), lcmp_imRep_measure_restrict (F4), lcmp_massOn_le_add_of_eval_eq and lcmp_measure_le_add_of_open_nhds (F3), lcmp_massOn_le_of_vanish_off_compact (step 5(a)) and lcmp_exists_good_slice_level (step 5(c)). The siblings flat_convergence, slicing, closure_and_boundary_rectifiability and pushforward are decomposing, and a child may only use its own children and depends_on, so the new children take them as hypotheses. Neither the pinned libraries nor accepted nodes contain the slice decomposition, the retraction comparison or the per-index comparison, so these are new; the three dimred_mbl_lc_* names are unused in the DAG. Lean checks: all 12 child types elaborate in the comparator scope. The conditional assembly proves the exact parent type from slice_decomposition and index_comparison plus the parent's sibling types FL, SL, BR, PF and MR, with axioms propext, Classical.choice and Quot.sound.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
