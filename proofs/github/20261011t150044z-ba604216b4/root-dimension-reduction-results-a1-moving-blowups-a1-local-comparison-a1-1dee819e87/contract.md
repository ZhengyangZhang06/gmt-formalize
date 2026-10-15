<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1 -->

## Theorem `Submission.dimred_mbl_local_comparison`

Let P, m ∈ ℕ and n := m + 1. For j ∈ ℕ let U_j ⊆ ℝ^P be open, A_j ⊆ ℝ^P, S_j ∈ 𝒟_n(U_j) and Ŝ_j ∈ 𝒟_n(ℝ^P); let C ∈ 𝒟_n(ℝ^P) and ρ_j ∈ ℝ. Assume: (1) every S_j is minimizing in A_j (IsMinimizingIn S_j A_j) and spt S_j ⊆ A_j; (2) for every R ∈ ℝ there is c ∈ [0, ∞) with M_{B_R(0)}(S_j) ≤ c for all large j; (3) for every G > 0 there are maps π_j : ℝ^P → ℝ^P (j ∈ ℕ) and G' ∈ ℝ such that, for all large j, either A_j ∩ B_G(0) = ∅, or π_j is C¹ on B_G(0), maps B_G(0) into A_j ∩ B_{G'}(0) and is the identity on A_j ∩ B_G(0); and such that for every η > 0, for all large j, either A_j ∩ B_G(0) = ∅ or |π_j(y) − π_j(z)| ≤ (1 + η)|y − z| for all y, z ∈ B_G(0); (4) C and every Ŝ_j are integer multiplicity, sup_j (M_W(Ŝ_j) + M_W(∂Ŝ_j)) < ∞ for every bounded open W ⊆ ℝ^P, and Ŝ_j ⇀ C in ℝ^P (WeaklyConvergesOn); (5) ρ_j → ∞, closedBall(0, ρ_j) ⊆ U_j, and Ŝ_j(ω) = currentEval(S_j, ω) for every ω ∈ 𝒟ⁿ(ℝ^P) with tsupport ω ⊆ B_{ρ_j}(0). Then for every compact K ⊆ ℝ^P, every ε > 0 and every strictly increasing ψ : ℕ → ℕ there are an open W ⊆ ℝ^P with K ⊆ W ⊆ thickening(ε, K) = {y : dist(y, K) < ε} and a strictly increasing φ' : ℕ → ℕ such that limsup_i M_W(S_{ψ(φ'(i))}) ≤ M_W(S) for every integer multiplicity S ∈ 𝒟_n(ℝ^P) with ∂S = ∂C (SameBoundary S C) and spt(S − C) ⊆ K.

Node: `root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1022

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/810, https://github.com/ZhengyangZhang06/gmt-formalize/issues/667, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5014, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5023, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5040, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5049, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5055

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/810, https://github.com/ZhengyangZhang06/gmt-formalize/issues/667, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4196, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1308, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4695, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4704, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4728, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4710, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4718, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6173, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6180, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6192

## Lean problem

Declaration: `Submission.dimred_mbl_local_comparison`

```lean
∀ (P m : ℕ) (Us As : ℕ → Set (Euclid P)) (Ss : (j : ℕ) → GeometricCurrentOn (Us j) (m + 1)) (Ŝ : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (C : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (ρ : ℕ → ℝ), (∀ j, IsOpen (Us j)) → (∀ j, IsMinimizingIn (Ss j) (As j)) → (∀ j, (Ss j).support ⊆ As j) → (∀ R : ℝ, ∃ c : ℝ≥0∞, c ≠ ∞ ∧ ∀ᶠ j in atTop, (Ss j).massOn (ball 0 R) ≤ c) → (∀ G : ℝ, 0 < G → ∃ (πs : ℕ → Euclid P → Euclid P) (G' : ℝ), (∀ᶠ j in atTop, As j ∩ ball 0 G = ∅ ∨ (ContDiffOn ℝ 1 (πs j) (ball 0 G) ∧ MapsTo (πs j) (ball 0 G) (As j ∩ ball 0 G') ∧ ∀ y ∈ As j ∩ ball 0 G, πs j y = y)) ∧ ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, As j ∩ ball 0 G = ∅ ∨ ∀ y ∈ ball 0 G, ∀ z ∈ ball 0 G, ‖πs j y - πs j z‖ ≤ (1 + η) * ‖y - z‖) → IsIntegerMultiplicity C → (∀ j, IsIntegerMultiplicity (Ŝ j)) → (∀ W : Set (Euclid P), IsOpen W → Bornology.IsBounded W → ⨆ j, ((Ŝ j).massOn W + (Ŝ j).boundary.massOn W) < ∞) → WeaklyConvergesOn Ŝ C → Tendsto ρ atTop atTop → (∀ j, closedBall (0 : Euclid P) (ρ j) ⊆ Us j) → (∀ (j : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) (m + 1)), tsupport (ω : DifferentialForm (Euclid P) (m + 1)) ⊆ ball 0 (ρ j) → Ŝ j ω = currentEval (Ss j) (ω : DifferentialForm (Euclid P) (m + 1))) → ∀ (K : Set (Euclid P)) (ε : ℝ), IsCompact K → 0 < ε → ∀ ψ : ℕ → ℕ, StrictMono ψ → ∃ W : Set (Euclid P), IsOpen W ∧ K ⊆ W ∧ W ⊆ thickening ε K ∧ ∃ φ' : ℕ → ℕ, StrictMono φ' ∧ ∀ S : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), IsIntegerMultiplicity S → SameBoundary S C → (S - C).support ⊆ K → limsup (fun j => (Ss (ψ (φ' j))).massOn W) atTop ≤ S.massOn W
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

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon 7.2.4 (1)–(11) with Remark 7.2.5(2). Errata: S̃_j = S'_j⌞W_α − P_j (printed +); the printed sets W_γ (γ>α, γ ↓ 0; correct: γ<α) are not needed: we compare on B_{G₃} (step 7). Siblings: (VO) vanish_off_support; (MR) mass_and_support (first conjunct); (IMC)(b)–(d) foundations; (SL) slicing; (BR) closure_and_boundary_rectifiability (second conjunct); (FL) flat_convergence; (PF) pushforward.
Conventions. n:=m+1; IM:=integer multiplicity; B_r:=ball(0,r), B̄_r:=closedBall(0,r); A(ω):=currentEval A ω; X+Y:=X−(0−Y) for currents in one domain (contract Sub; IM by IMC(c), 0 being IM via the empty IMRep); M(X):=X.mass; μ_A:=R_A.measure for an IMRep R_A of an IM A; μ_j:=μ_{S_j}.
(F1) For A IM in an open V: M_G(A) = μ_A(G) for open G (MR); μ_A(ℝ^P∖V)=0 (carrier⊆V); μ_A(K')<∞ for compact K'⊆V (locallyIntegrable_mult); μ_A(V∖spt A)=0, as V∖spt A = V∩zeroRegion(A) is open and A kills the forms admissible for it, whose tsupports miss spt A (VO).
(F2) (Locality.) If A₁, A₂ are IM in open V₁, V₂, O⊆V₁∩V₂ is open and A₁(ω) = A₂(ω) for test ω with tsupport ω⊆O, then μ_{A₁} = μ_{A₂} on Borel subsets of O: μ_{A₁}(G) = M_G(A₁) = M_G(A₂) = μ_{A₂}(G) for open G⊆O (F1; same admissible forms, same values); the open O_q:=B_q∖cthickening(1/q, ℝ^P∖O) (q≥1; O_q=B_q if O=ℝ^P) increase to O and have compact closures in O, so the finite (F1) μ_{A_i}⌞O_q, agreeing on open sets (a π-system generating the Borel sets) and on ℝ^P, coincide; let q→∞ (continuity from below).
(F3) (Subadditivity.) For A, B IM in an open V and Borel E, μ_{A±B}(E)≤μ_A(E)+μ_B(E): for open E by F1 and M_E(A±B)≤M_E(A)+M_E(B) (ofReal((A±B)(ω))≤ofReal(A(ω))+ofReal(±B(ω)) for admissible ω; −ω is admissible); for Borel E⊆O_q (F2, O:=V) by outer regularity of the finite μ_A⌞O_q, μ_B⌞O_q, μ_{A±B}⌞O_q (intersect the open approximants), then q→∞, all three vanishing off V. The same ofReal bound gives M_G(X+Y)≤M_G(X)+M_G(Y) for any currents, G open.
(F4) (Restriction.) For A IM in an open V with IMRep (M_A,θ_A,ξ_A) and E Borel, (M_A∩E,θ_A,ξ_A) is an IMRep in V (IMC(b)) of a current A⌞E, (A⌞E)(ω) = ∫_{M_A∩E}θ_Aξ_A(ω) dHⁿ: A⌞E is IM, μ_{A⌞E} = μ_A⌞E, A⌞E = A on forms vanishing off E, and A⌞E kills forms vanishing on E. If E⊆E'⊆V, E' compact, the triple is also an IMRep in ℝ^P (∫_{M_A∩E∩K'}θ_A≤μ_A(E')<∞ for compact K'; other fields unchanged) of a current in ℝ^P (IMC(b) in ℝ^P, E:=ℝ^P), again A⌞E. (R.measure, R.orient) is a representation as in (SL): R.measure = θ_AHⁿ⌞M_A is finite on compact subsets of V, R.orient is a.e. strongly measurable for Hⁿ⌞M_A, hence for R.measure, |R.orient α|≤|α| a.e. (IMC(d)), A(ω) = ∫R.orient(ω) dR.measure; the currents ∫_Eξ(ω)dμ of (SL) are exactly the A⌞E.
(F5) (Domain restriction.) If X is IM in ℝ^P and spt X is a compact subset of an open V, X|_V:=X.restrictDomain (subset_univ V)∈𝒟_n(V) is IM: IMC(b) in ℝ^P (E:=V) gives an IMRep (all fields) with carrier (carrier of X)∩V, a μ_X-null change (F1), so still representing X; its carrier lies in V and its multiplicity is integrable on compact subsets of V, so the same data are an IMRep in V of X|_V. Also ∂(X|_V) = (∂X)|_V, spt X|_V⊆spt X, μ_{X|_V} = μ_X on Borel subsets of V (F2), M_G(X|_V)≤M_G(X) for open G (forms admissible for X|_V are admissible for X).
Proof. Fix K compact, ε>0, ψ strictly increasing.
1. (Reduction to ψ=id.) Re-indexing all data and the π_j by ψ keeps the hypotheses (eventual statements and limits pass to ψ(j)→∞; subsequences of weakly convergent sequences have the same limit; suprema over subsequences are smaller), and a φ' for the new data gives the claim for S_{ψ(φ'(i))}. So let ψ = id. If K=∅, W:=∅, φ':=id work (M_∅=0: only the zero form is admissible). Let K ≠ ∅.
2. (Cut-off.) ε₁:=min(ε,1)/2; ψ_c : ℝ^P→[0,1] is smooth with ψ_c=1 on K, tsupport ψ_c⊆thickening(ε₁, K) (mollify the indicator of thickening(ε₁/2, K) at scale ε₁/4); tsupport ψ_c is compact and L₀:=sup|Dψ_c|<∞ is a Lipschitz constant of ±ψ_c. For 0≤s<1: W_s:={ψ_c>s} (open, bounded, K⊆W_s⊆thickening(ε, K)), Σ_s:={ψ_c=s}, F_s:={ψ_c≥s}; for 0<s<1, Σ_s, F_s are compact subsets of tsupport ψ_c, closure(W_s)⊆F_s, K∩Σ_s=∅, Σ_s⊆W₀. Fix G≥1 with tsupport ψ_c⊆B_G.
3. (Good indices.) The retraction hypothesis for radius 2G gives π_j, G'; enlarging G' (MapsTo only weakens), G'≥2G; G₃:=G'+1. By ρ_j→∞, B̄_{ρ_j}⊆U_j and the mass bound for R:=G₃, there are c∈[0,∞), j₀ with, for j≥j₀: (R1) A_j∩B_{2G}=∅, or π_j is C¹ on B_{2G}, maps B_{2G} into A_j∩B_{G'} and fixes A_j∩B_{2G}; (R2) ρ_j>G₃, so B̄_{G₃}⊆U_j; (R3) M_{B_{G₃}}(S_j)≤c. For η>0 take j(η)≥j₀ such that for j≥j(η), A_j∩B_{2G}=∅ or π_j is (1+η)-Lipschitz on B_{2G}, whence ‖Dπ_j‖≤1+η there (π_j is C¹ by R1, |Dπ_j(y)v|=lim_{t↓0}|π_j(y+tv)−π_j(y)|/t≤(1+η)|v|).
4. (Flat convergence.) W₀ is open and bounded, so CompactlyContained W₀ univ; as bounded open sets are exactly those ⊂⊂ ℝ^P, hypothesis (4) and (FL) (U:=ℝ^P, T_j:=Ŝ_j, T:=C, W:=W₀) gives IM R_j∈𝒟_{n+1}(ℝ^P), S'_j∈𝒟_n(ℝ^P) with C−Ŝ_j−S'_j = ∂R_j and a_j:=M_{W₀}(R_j)+M_{W₀}(S'_j)→0; ∂R_j is IM (IMC(c)).
5. (Slicing; α and φ'.) Fix j; apply (SL) to R_j with the representations (μ_{R_j}, ξ_{R_j}), (μ_{∂R_j}, ξ_{∂R_j}) of IMReps (F4) and f:=−ψ_c (constant L₀). For t:=−s, {f<t} = W_s, so A_{−s} = R_j⌞W_s, B_{−s} = (∂R_j)⌞W_s (F4), and P_{j,s}:=∂(R_j⌞W_s)−(∂R_j)⌞W_s has P_{j,s}(η)=0 if tsupport η∩Σ_s=∅, and, as {t−h<f<t} = {s<ψ_c<s+h}, M_{W₀}(P_{j,s})≤L₀·liminf_{h↓0}h⁻¹μ_{R_j}(W₀∩{s<ψ_c<s+h}) for s∈(0,1).
 (a) For s∈(0,1) let χ∈C_c^∞(W₀; [0,1]), χ = 1 near the compact Σ_s⊆W₀. For open G and ω admissible for M_G, (1−χ)ω vanishes near Σ_s, so P_{j,s}(ω) = P_{j,s}(χω) with χω admissible for M_{W₀}: M_G(P_{j,s})≤M_{W₀}(P_{j,s}); in particular M(P_{j,s})≤M_{W₀}(P_{j,s}).
 (b) If M_{W₀}(P_{j,s})<∞, ∂(R_j⌞W_s) = (∂R_j)⌞W_s+P_{j,s} has locally finite mass (M_G((∂R_j)⌞W_s)≤μ_{∂R_j}(G)<∞ for bounded open G; (a)) and R_j⌞W_s is IM (F4), so ∂(R_j⌞W_s) is IM by (BR) (U:=ℝ^P) and P_{j,s} is IM (IMC(c)); spt P_{j,s}⊆Σ_s (vanishing property) is compact.
 (c) H_j(s):=μ_{R_j}(W₀∩{s<ψ_c<1}) is nonincreasing, ≤μ_{R_j}(W₀)≤μ_{R_j}(closure W₀)<∞ (F1; closure W₀⊆tsupport ψ_c, compact), and μ_{R_j}(W₀) = M_{W₀}(R_j)≤a_j. As {s<ψ_c<s+h}⊆{s<ψ_c<1}∖{s+h<ψ_c<1} for 0<h<1−s, μ_{R_j}(W₀∩{s<ψ_c<s+h})≤H_j(s)−H_j(s+h); H_j is a.e. differentiable (Lebesgue), and there M_{W₀}(P_{j,s})≤g_j(s):=−L₀H_j'(s). The g_j≥0 are measurable (measurable_deriv), ∫_0^1 g_j≤L₀(H_j(0)−H_j(1))≤L₀a_j (MonotoneOn.intervalIntegral_deriv_mem_uIcc, −H_j) and a_j→0, so by Fatou ∫_0^1 liminf_j g_j≤liminf_j ∫_0^1 g_j=0: liminf_j g_j=0 a.e. on (0,1). For j≥j₀ the Σ_s (0<s<1) are disjoint subsets of the compact tsupport ψ_c⊆B_G⊆U_j (R2), where μ_j is finite (F1), so μ_j(Σ_s)>0 for at most countably many s (Measure.countable_meas_level_set_pos). Hence some α∈(0,1) has: each H_j differentiable at α (so M_{W₀}(P_{j,α})≤g_j(α)<∞, and (b) applies for all j), liminf_j g_j(α)=0, μ_j(Σ_α)=0 for j≥j₀. Choose φ' strictly increasing, φ'(i)≥j₀, g_{φ'(i)}(α)→0; so M(P_{φ'(i),α})≤M_{W₀}(P_{φ'(i),α})→0 by (a). Put W:=W_α, Σ:=Σ_α, F:=F_α: W is open, K⊆W⊆thickening(ε, K) (step 2); W, φ' depend only on K, ε and the data, not on the competitor S.
6. (Decomposition, corrected sign.) For i∈ℕ, j:=φ'(i): R̃_i:=R_j⌞W, P_i:=P_{j,α}, S̃_i:=S'_j⌞W−P_i are IM (F4, 5(b), IMC(c)), ∂R̃_i = (∂R_j)⌞W+P_i is IM, spt R̃_i⊆closure(W)⊆F (R̃_i kills forms vanishing on W). For test ω with tsupport ω⊆W: R̃_i(dω) = R_j(dω) (tsupport dω⊆W), (S'_j⌞W)(ω) = S'_j(ω), P_i(ω)=0 (W∩Σ=∅); so C−Ŝ_j−S'_j = ∂R_j gives
 (★) C(ω) = Ŝ_j(ω)+∂R̃_i(ω)+S̃_i(ω) for test ω with tsupport ω⊆W.
e_i:=M(S̃_i)+M(P_i)∈[0,∞) has e_i≤a_{φ'(i)}+2M(P_{φ'(i),α})→0, as M(S̃_i)≤M(S'_j⌞W)+M(P_i) = μ_{S'_j}(W)+M(P_i)≤M_{W₀}(S'_j)+M(P_i) (F3, F4, F1).
7. (Competitor.) Let S be IM in ℝ^P with SameBoundary S C (∂S=∂C) and spt(S−C)⊆K. X:=S−C is IM (IMC(c)), ∂X=0, spt X⊆K; Y_i:=X+∂R̃_i is IM, ∂Y_i=0 (∂∂=0), spt Y_i⊆K∪spt R̃_i⊆F, compact⊆B_G (ψ_c=1 on K, α<1). Fix η∈(0,1] and i with j:=φ'(i)≥j(η).
 Case (E): A_j∩B_{2G}=∅. Then spt S_j∩B_{2G}=∅ (spt S_j⊆A_j) and B_{2G}⊆U_j (R2), so S_j kills forms supported in B_{2G} (VO) and μ_j(B_{2G}) = M_{B_{2G}}(S_j)=0 (F1); so μ_j(W)=0.
 Case (P): otherwise: π_j is C¹ on O:=B_{2G}, maps O into A_j∩B_{G'}, fixes A_j∩O, ‖Dπ_j‖≤1+η on O (step 3). Let push be given by (PF) for (P, m, O, f:=π_j, L:=1+η); admissible:=IM in ℝ^P with compact support in O.
 (a) Y_i is admissible (spt Y_i⊆F⊆B_G); by (PF) push Y_i is IM, ∂(push Y_i)=0, M(push Y_i)≤(1+η)ⁿM(Y_i), spt(push Y_i)⊆π_j(spt Y_i)⊆π_j(F)⊆A_j∩B_{G'}, and π_j(F) is compact (π_j continuous on O ⊇ F), so spt(push Y_i) is compact.
 (b) Let (M_j,θ_j,ξ_j) be an IMRep of S_j, Q_i:=S_j⌞B_G∈𝒟_n(ℝ^P) (F4; B_G⊆B̄_G, compact⊆U_j by R2): Q_i is IM, Q_i(ω) = S_j(ω) if tsupport ω⊆B_G, and spt Q_i⊆B̄_G∩spt S_j (compact: spt S_j is relatively closed in U_j ⊇ B̄_G), since Q_i kills forms vanishing on B_G and those with tsupport ω∩spt S_j=∅ (the integrand vanishes off M_j∩spt S_j, μ_j(M_j∖spt S_j)=0 by F1, M_j⊆U_j). As spt S_j⊆A_j and G<2G, π_j = id on spt Q_i: Q_i is admissible and push Q_i = Q_i (identity clause of PF).
 (c) Q_i+Y_i is admissible; the linearity clause of (PF) for Q_i, 0−Y_i, 0, Y_i (all admissible; push 0=push(0−0)=push 0−push 0=0) gives push(Q_i+Y_i) = push Q_i−(push 0−push Y_i) = Q_i+push Y_i, and M(push(Q_i+Y_i))≤(1+η)ⁿM(Q_i+Y_i).
 (d) Z_i:=S_j+(push Y_i)|_{U_j}∈𝒟_n(U_j) (F5; spt push Y_i⊆B_{G'}⊆B̄_{G₃}⊆U_j) is IM (F5, IMC(c)); ∂Z_i = ∂S_j+(∂ push Y_i)|_{U_j} = ∂S_j: SameBoundary Z_i S_j; Z_i−S_j = (push Y_i)|_{U_j} (pointwise) has support⊆spt(push Y_i)⊆A_j∩B_{G'}, compact (relatively closed in U_j inside the compact spt(push Y_i)⊆U_j). As B_{G₃} has compact closure B̄_{G₃}⊆U_j (R2) and A_j∩B_{G'}⊆A_j∩B_{G₃}, minimality of S_j in A_j gives M_{B_{G₃}}(S_j)≤M_{B_{G₃}}(Z_i).
 (e) By (c), Z_i = (S_j−Q_i|_{U_j})+(push(Q_i+Y_i))|_{U_j} on 𝒟ⁿ(U_j), where (S_j−Q_i|_{U_j})(ω) = ∫_{M_j∖B_G}θ_jξ_j(ω) dHⁿ has M_{G''}≤μ_j(G''∖B_G) for open G'' (|ξ_j(ω)|≤|ω|≤1 a.e. for admissible ω, IMC(d)), and M_{G''}((push(Q_i+Y_i))|_{U_j})≤M(push(Q_i+Y_i)) (F5). By F3, (c), (d), F1,
 μ_j(B_G)+μ_j(B_{G₃}∖B_G) = M_{B_{G₃}}(S_j)≤μ_j(B_{G₃}∖B_G)+(1+η)ⁿM(Q_i+Y_i),
all terms finite (R3), so μ_j(B_G)≤(1+η)ⁿM(Q_i+Y_i). Here M(Q_i+Y_i) = μ_{Q_i+Y_i}(B_G) (F1; μ_{Q_i+Y_i}(ℝ^P∖B_G)≤μ_{Q_i}(ℝ^P∖B_G)+μ_{Y_i}(ℝ^P∖B_G)=0 by F3, the carrier of Q_i lying in B_G and spt Y_i⊆B_G, F1), and Q_i+Y_i agrees with S_j+Y_i|_{U_j} on forms supported in B_G (b), so μ_{Q_i+Y_i}(B_G) = μ_{S_j+Y_i}(B_G) (F2), S_j+Y_i meaning S_j+Y_i|_{U_j} (IM by F5, IMC(c)). Hence
 (I) μ_j(B_G)≤(1+η)ⁿμ_{S_j+Y_i}(B_G) in case (P).
8. (Comparison off W.) In case (P) (η, i, j as in step 7), B_G is the disjoint union of W, Σ and the open O':=B_G∩{ψ_c<α}, as tsupport ψ_c⊆B_G.
 (a) μ_j(B_G) = μ_j(W)+μ_j(Σ)+μ_j(O') = μ_j(W)+μ_j(O') (choice of α, j≥j₀).
 (b) Y_i kills forms supported in O' (spt Y_i⊆F misses O'; VO), so μ_{S_j+Y_i}(O') = μ_j(O') (F2).
 (c) μ_{S_j+Y_i}(Σ)≤μ_j(Σ)+μ_{Y_i|_{U_j}}(Σ) = μ_{Y_i}(Σ) (F3 in U_j; μ_{Y_i|_{U_j}}=μ_{Y_i} on Borel subsets of U_j by F5, Σ⊆B_G⊆U_j; μ_j(Σ)=0), and as Y_i = X+(∂R_j)⌞W+P_i, μ_{Y_i}(Σ)≤μ_X(Σ)+μ_{(∂R_j)⌞W}(Σ)+μ_{P_i}(Σ)≤0+0+M(P_i): spt X⊆K, K∩Σ=∅ (F1); μ_{(∂R_j)⌞W} = μ_{∂R_j}⌞W, W∩Σ=∅ (F4); μ_{P_i}(Σ)≤μ_{P_i}(ℝ^P) = M(P_i) (F1).
 (d) For test ω with tsupport ω⊆W (⊆B_G⊆B_{ρ_j}∩U_j by R2): (S_j+Y_i)(ω) = S_j(ω)+Y_i(ω) = Ŝ_j(ω)+X(ω)+∂R̃_i(ω) (hypothesis on Ŝ_j) = C(ω)−S̃_i(ω)+X(ω) (★) = S(ω)−S̃_i(ω). So S_j+Y_i (in U_j) and S−S̃_i (in ℝ^P) agree on W: μ_{S_j+Y_i}(W) = μ_{S−S̃_i}(W)≤μ_S(W)+μ_{S̃_i}(W)≤μ_S(W)+M(S̃_i) (F2, F3 in ℝ^P, F1).
 (e) By (I), (a)–(d): μ_j(W)+μ_j(O')≤(1+η)ⁿ[μ_S(W)+M(S̃_i)+M(P_i)+μ_j(O')]; as μ_j(O')≤μ_j(B_{G₃})≤c (R3, F1) and μ_S(W)<∞ (W bounded, F1),
 μ_j(W)≤μ_S(W)+e_i+((1+η)ⁿ−1)(μ_S(W)+e_i+c),
also in case (E), whose left side is 0.
 (f) This holds for all i with φ'(i)≥j(η), and μ_j(W) = M_W(S_j), μ_S(W) = M_W(S) (F1). As i→∞ (e_i→0), limsup_i M_W(S_{φ'(i)})≤M_W(S)+((1+η)ⁿ−1)(M_W(S)+c) for every η∈(0,1]; as η ↓ 0, limsup_i M_W(S_{φ'(i)})≤M_W(S) (all finite; read in [0,∞]).
9. (Output.) W, φ' (step 5, fixed before S) satisfy the claim by step 8; undoing step 1 gives it for S_{ψ(φ'(i))}. ∎

## Key steps

1. Reduce to ψ=id; cut-off ψ_c, good indices (R1)–(R3), G₃=G'+1.
2. (FL): C−Ŝ_j−S'_j=∂R_j, M_{W₀}(R_j)+M_{W₀}(S'_j)→0.
3. Slice R_j by ψ_c (SL, BR); Lebesgue and Fatou fix α, φ' with M(P_{j,α})→0, μ_j(Σ_α)=0, before S.
4. Identity (★), corrected sign; competitor Z_i=S_j+push Y_i (PF) and minimality give (I).
5. Split B_G into W, Σ, O'; let i→∞, η↓0: limsup M_W(S_{φ'(i)})≤M_W(S).

## Reference use

### local-project

Queries:
- `cat RUN/local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; cmp GMT/Ch07/Submission.lean GMT/Ch07/Contract.lean`
- `python3 scans of RUN/dag.json: selected node, prerequisite types, accepted reusable declarations and their lean_statement, status of the children of root.compactness_of_minimizing_currents-a1, lean_name collisions (dimred_mbl_: no match)`
- `grep -n _existing_lean_name_problem _accepted_checkpoint contract in /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py and speculation.py`
- `grep -rn of every cited Mathlib/SimonGMT lemma name in the pinned lake packages`
- `lean (v4.35.0-rc3) on AllTypes.lean, AssemblyCond.lean (#print axioms) and 12 Challenge_<key>.lean modules; lean_contract.validate_lean_statement on all child types`
- `sed -n on book/chapter-06.txt (2.15, 2.23–2.33, 3.3–3.10, 4.6–4.11) and book/chapter-07.txt (7.2.4–7.2.5)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1/decomposition-v5.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/mb2/lean/src/AssemblyCond.lean`

Pins match (HEAD b4d606d, Mathlib 25730c7c, SimonGMT 2b366308) and Submission.lean is byte-identical to the frozen contract. The pinned libraries lack Federer–Fleming compactness, the deformation theorem, flat convergence, Lipschitz slicing and integral push-forward by nonlinear maps; SimonGMT supplies currents, mass, support, weak convergence, affine push-forward, the Lipschitz area formula and approximate tangent spaces, and every cited library name exists. Accepted declarations with exact types: dtc_vanish_off_support and dor_imrep_massOn_eq_measure_and_support (reused). The children of root.compactness_of_minimizing_currents-a1 are decomposing, not accepted, so they cannot be shared; identical types with unique dimred_mbl_* names are used. A child's prerequisites are its children plus depends_on, so monotonicity enters as a hypothesis. All 12 child types elaborate and the conditional assembly proves the parent type (axioms propext, Classical.choice, Quot.sound).


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
