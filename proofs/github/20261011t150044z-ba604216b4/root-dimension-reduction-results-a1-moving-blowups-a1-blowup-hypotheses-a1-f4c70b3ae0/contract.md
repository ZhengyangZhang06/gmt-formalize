<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.moving_blowups-a1.blowup_hypotheses-a1 -->

## Theorem `Submission.dimred_mbl_blowUp_hypotheses`

Let m, k, ℓ ∈ ℕ with ℓ ≤ k, n := m + 1, P := n + k; let U ⊆ ℝ^P be open, N ⊆ ℝ^P an embedded C² (n+ℓ)-dimensional submanifold (IsEmbeddedSubmanifold 2 (n + ℓ) N) with (closure N ∖ N) ∩ U = ∅, and T ∈ 𝒟_n(U) minimizing in U ∩ N (IsMinimizingIn T (U ∩ N)) with spt T ⊆ U ∩ N and ∂T = 0 in U (BoundaryVanishes T). Assume moreover (hmon): for every compact K ⊆ U there is Λ ≥ 0 such that for all y ∈ ℝ^P and R ∈ ℝ with closedBall(y, R) ⊆ K the function ρ ↦ ofReal(e^{Λρ}/ρⁿ)·M_{B_ρ(y)}(T) (in [0, ∞]) is monotone on (0, R) — this is conclusion (i) of the monotonicity theorem dimred_minimizing_monotonicity for P = n + k and d = n + ℓ. Let x ∈ U, let x_j ∈ ℝ^P with x_j → x, and let λ_j > 0 with λ_j → 0. Write η_j := dilation x_j λ_j (η_j(y) = λ_j⁻¹(y − x_j)), U_j := η_j(U), A_j := η_j(U ∩ N) and S_j := blowUp T x_j λ_j ∈ 𝒟_n(U_j). Then: (1) every U_j is open; (2) for every R ∈ ℝ, closedBall(0, R) ⊆ U_j for all large j; (3) every S_j is minimizing in A_j; (4) spt S_j ⊆ A_j for every j; (5) for every R ∈ ℝ there is c ∈ [0, ∞) with M_{B_R(0)}(S_j) ≤ c for all large j; (6) ∂S_j = 0 for every j; (7) for every G > 0 there are maps π_j : ℝ^P → ℝ^P (j ∈ ℕ) and G' ∈ ℝ such that, for all large j, either A_j ∩ B_G(0) = ∅, or π_j is C¹ on B_G(0), maps B_G(0) into A_j ∩ B_{G'}(0) and is the identity on A_j ∩ B_G(0); and such that for every η > 0, for all large j, either A_j ∩ B_G(0) = ∅ or |π_j(y) − π_j(z)| ≤ (1 + η)|y − z| for all y, z ∈ B_G(0). (B_R(0) = ball 0 R; 'for all large j' means 'eventually in atTop'.)

Node: `root.dimension_reduction_results-a1.moving_blowups-a1.blowup_hypotheses-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1022

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/667

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1244, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1241, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1237, https://github.com/ZhengyangZhang06/gmt-formalize/issues/667, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5588, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5598, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5621

## Lean problem

Declaration: `Submission.dimred_mbl_blowUp_hypotheses`

```lean
∀ (m k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (m + 1 + k))) (T : GeometricCurrentOn U (m + 1)), IsOpen U → IsEmbeddedSubmanifold 2 (m + 1 + ℓ) N → (closure N \ N) ∩ U = ∅ → IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T → (∀ K : Set (Euclid (m + 1 + k)), IsCompact K → K ⊆ U → ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ (y : Euclid (m + 1 + k)) (R : ℝ), closedBall y R ⊆ K → MonotoneOn (fun ρ : ℝ => ENNReal.ofReal (Real.exp (Λ * ρ) / ρ ^ (m + 1)) * T.massOn (ball y ρ)) (Ioo 0 R)) → ∀ (x : Euclid (m + 1 + k)) (xs : ℕ → Euclid (m + 1 + k)) (lams : ℕ → ℝ) (hlams : ∀ j, 0 < lams j), x ∈ U → Tendsto xs atTop (𝓝 x) → Tendsto lams atTop (𝓝 0) → (∀ j, IsOpen (dilation (xs j) (lams j) '' U)) ∧ (∀ R : ℝ, ∀ᶠ j in atTop, closedBall (0 : Euclid (m + 1 + k)) R ⊆ dilation (xs j) (lams j) '' U) ∧ (∀ j, IsMinimizingIn (blowUp T (xs j) (lams j) (hlams j).ne') (dilation (xs j) (lams j) '' (U ∩ N))) ∧ (∀ j, (blowUp T (xs j) (lams j) (hlams j).ne').support ⊆ dilation (xs j) (lams j) '' (U ∩ N)) ∧ (∀ R : ℝ, ∃ c : ℝ≥0∞, c ≠ ∞ ∧ ∀ᶠ j in atTop, (blowUp T (xs j) (lams j) (hlams j).ne').massOn (ball 0 R) ≤ c) ∧ (∀ j, (blowUp T (xs j) (lams j) (hlams j).ne').boundary = 0) ∧ ∀ G : ℝ, 0 < G → ∃ (πs : ℕ → Euclid (m + 1 + k) → Euclid (m + 1 + k)) (G' : ℝ), (∀ᶠ j in atTop, dilation (xs j) (lams j) '' (U ∩ N) ∩ ball 0 G = ∅ ∨ (ContDiffOn ℝ 1 (πs j) (ball 0 G) ∧ MapsTo (πs j) (ball 0 G) (dilation (xs j) (lams j) '' (U ∩ N) ∩ ball 0 G') ∧ ∀ y ∈ dilation (xs j) (lams j) '' (U ∩ N) ∩ ball 0 G, πs j y = y)) ∧ ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, dilation (xs j) (lams j) '' (U ∩ N) ∩ ball 0 G = ∅ ∨ ∀ y ∈ ball 0 G, ∀ z ∈ ball 0 G, ‖πs j y - πs j z‖ ≤ (1 + η) * ‖y - z‖
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
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.blowup_hypotheses-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon 7.2.5(2), 7.3.1(1); Ch. 6, 2.23–2.24, 3.3–3.9. Sibling: mass_and_support, first conjunct (MR). The parent's subsequence Cases A/B become the disjunction in (7); its nearest-point projection is replaced by Part III.
Notation: n := m + 1, P := n + k, η_j := dilation x_j λ_j (η_j(y) = λ_j⁻¹(y − x_j)), U_j := η_j(U), A_j := η_j(U ∩ N), S_j := blowUp T x_j λ_j, Hⁿ := μHE[n], B_s(y) := ball(y, s). Fix r > 0 with closedBall(x, 2r) ⊆ U.

Part I (one dilation). a ∈ ℝ^P, λ > 0, η := dilation a λ, Y ∈ 𝒟_n(U), η_#Y := blowUp Y a λ ∈ 𝒟_n(η(U)).
(S0) η is an affine homeomorphism, η⁻¹(z) = a + λz, |η(y) − η(y′)| = λ⁻¹|y − y′|, η(B_s(y)) = B_{s/λ}(η(y)), η(E ∩ F) = η(E) ∩ η(F), η(U) open. (i) Hⁿ(η(E)) = λ^{−n}Hⁿ(E) (translation invariance, Hⁿ(cE) = cⁿHⁿ(E): euclideanHausdorffMeasure_smul₀), so ∫_{η(E)} g dHⁿ = λ^{−n}∫_E g∘η dHⁿ (E, g Borel, g ≥ 0 or integrable). (ii) Unfolding blowUp (affinePushforward_apply, restrictDomain_apply; η⁻¹(η(U)) = U), η_#Y(ω) = Y(η^#ω) (ω ∈ 𝒟ⁿ(η(U))), η^#ω := affinePullbackForm (dilationCLM P λ) (−λ⁻¹a) ω, (η^#ω)(y)(v₁, …, vₙ) = ω(η(y))(λ⁻¹v₁, …, λ⁻¹vₙ); so η^#ω = λ^{−n}(ω∘η), tsupport(η^#ω) = η⁻¹(tsupport ω), and every ω′ ∈ 𝒟ⁿ(U) is η^#ω for exactly one ω, namely λⁿ(ω′∘η⁻¹). (iii) ζ(λ^{−n}α) = λ^{−n}ζ(α) if ζ(α) = ±α(τ).
(S1) M_{η(W)}(η_#Y) = ofReal(λ^{−n})·M_W(Y) for all W: ω ↦ ω∘η (inverse ω′ ↦ ω′∘η⁻¹) maps the forms admissible for η_#Y on η(W) bijectively onto those for Y on W (tsupport(ω∘η) = η⁻¹(tsupport ω) ⊆ W ∩ U, same norms), η_#Y(ω) = λ^{−n}Y(ω∘η), ofReal(λ^{−n}t) = ofReal(λ^{−n})ofReal(t), and multiplying by a finite constant commutes with suprema in [0, ∞].
(S2) spt(η_#Y) = η(spt Y): for open W₀ with compact closure in U, Y vanishes on W₀ iff η_#Y does on η(W₀) ((S0)(ii): tsupport ω ⊆ η(W₀) iff tsupport(η^#ω) ⊆ W₀, and every test form in U is some η^#ω), and η maps these W₀ bijectively onto the open sets with compact closure in η(U); so zeroRegion(η_#Y) = η(zeroRegion Y) and spt(η_#Y) = η(U) ∖ η(zeroRegion Y) = η(spt Y).
(S3) For n = m + 1, (η_#Y).boundary = η_#(Y.boundary): ∂(η_#Y)(β) = Y(η^#dβ) = Y(d(η^#β)) = ∂Y(η^#β) (affine pull-back commutes with d: exteriorDerivative_affinePullbackForm). So BoundaryVanishes Y gives (η_#Y).boundary = 0.
(S4) If R = (M, θ, ξ) is an IMRep of Y, R′ := (η(M), θ∘η⁻¹, ξ∘η⁻¹) is an IMRep in η(U) of η_#Y, R′.measure(E) = ofReal(λ^{−n})R.measure(η⁻¹(E)): η(M) ⊆ η(U) is Borel (homeomorphic image) and countably n-rectifiable (M ⊆ M₀ ∪ ⋃_i F_i(ℝⁿ), Hⁿ(M₀) = 0, F_i Lipschitz give η(M) ⊆ η(M₀) ∪ ⋃_i (η∘F_i)(ℝⁿ), Hⁿ(η(M₀)) = 0 by (S0)(i)); θ∘η⁻¹ is measurable, ℕ-valued, ≥ 1 on η(M); ∫_{η(M)∩K} θ∘η⁻¹ dHⁿ = λ^{−n}∫_{M∩η⁻¹(K)} θ dHⁿ < ∞ for compact K ⊆ η(U) (η⁻¹(K) ⊆ U compact). Measurability: ξ∘η⁻¹ is a.e. strongly measurable for Hⁿ⌞η(M): η is a measurable equivalence with η_*(Hⁿ⌞M) = λⁿHⁿ⌞η(M) ((S0)(i)), and composition with η⁻¹ preserves a.e. strong measurability. Orientation: if ξ(y) orients Q := T_yM and z := η(y), then η_{z,ρ}(η(w)) = (w − y)/(λρ) = η_{y,λρ}(w), so η_{z,ρ}(η(M)) = η_{y,λρ}(M), the blow-up integrals of η(M) at z tend to ∫_Q f dHⁿ (HasApproximateTangentSpaceAt n η(M) z Q) and ξ∘η⁻¹(z) = ξ(y) orients Q; the exceptional set is the η-image of a null set. Representation: η_#Y(ω) = Y(η^#ω) = ∫_M θξ(λ^{−n}ω(η(y))) dHⁿ = ∫_{η(M)} (θ∘η⁻¹)(ξ∘η⁻¹)(ω) dHⁿ ((S0)(i),(iii)).
Direct form. (S1)–(S4) used only that η is a similarity, so they hold for η⁻¹ = dilation (−λ⁻¹a) λ⁻¹; to avoid transport along η⁻¹(η(U)) = U we use them directly: for X ∈ 𝒟_n(η(U)) let X^♭ ∈ 𝒟_n(U), X^♭(ω′) := X(λⁿ(ω′∘η⁻¹)) (linear; sequentially continuous, as ω′ ↦ λⁿ(ω′∘η⁻¹) maps convergent test-form sequences in U to convergent ones in η(U): supports move by the homeomorphism η, derivatives by the chain rule). The computations of (S1)–(S4) with λ ↦ λ⁻¹, U ↔ η(U) give: M_W(X^♭) = ofReal(λⁿ)M_{η(W)}(X); spt X^♭ = η⁻¹(spt X); if X is IM, so is X^♭, represented by (η⁻¹(M_X), θ_X∘η, ξ_X∘η); (X^♭).boundary = (X.boundary)^♭ with ♭ in degree n − 1 using the factor λ^{n−1}: ∂X^♭(β) = X(λⁿ((dβ)∘η⁻¹)) = X(d(λ^{n−1}(β∘η⁻¹))) = ∂X(λ^{n−1}(β∘η⁻¹)), as d(β∘η⁻¹) = λ·((dβ)∘η⁻¹) (chain rule for z ↦ a + λz; exteriorDerivative_affinePullbackForm for η⁻¹, whose pull-back of a k-form γ is λᵏ(γ∘η⁻¹)). Also η_#(X^♭) = X, (η_#Y)^♭ = Y in every degree k (factors λ^{−k} in η_#, λᵏ in ♭), the pull-backs λ^{−k}(ω∘η), λᵏ(ω′∘η⁻¹) being mutually inverse.
(S5) IsMinimizingIn Y A ⟹ IsMinimizingIn (η_#Y) (η(A)). η_#Y is IM by (S4). Let W′ be open with compact closure in η(U), S′ ∈ 𝒟_n(η(U)) IM, SameBoundary S′ (η_#Y), spt(S′ − η_#Y) ⊆ η(A) ∩ W′ compact. (a) S″ := (S′)^♭: η_#S″ = S′, S″ − Y = (S′ − η_#Y)^♭ (pointwise, (S0)(ii)). (b) S″ is IM (direct (S4)). (c) SameBoundary S″ Y (vacuous in degree 0): ∂S″ = (∂S′)^♭ = (∂(η_#Y))^♭ = (η_#∂Y)^♭ = ∂Y ((S3), direct form, (η_#Z)^♭ = Z in degree m). (d) spt(S″ − Y) = η⁻¹(spt(S′ − η_#Y)) (direct (S2)) is a compact subset of A ∩ W, W := η⁻¹(W′) open with closure η⁻¹(closure W′) compact in U. (e) Minimality of Y: M_W(Y) ≤ M_W(S″); by (S1), η(W) = W′: M_{W′}(η_#Y) = ofReal(λ^{−n})M_W(Y) ≤ ofReal(λ^{−n})M_W(S″) = M_{W′}(S′).

Part II.
1. ((1)) U_j = η_j(U) is open, as η_j is a homeomorphism and U is open.
2. ((2)) If R < 0, closedBall(0, R) = ∅. If R ≥ 0, |x_j − x| < r and λ_jR ≤ r (all large j), each z ∈ closedBall(0, R) has |x_j + λ_jz − x| ≤ |x_j − x| + λ_jR < 2r, so x_j + λ_jz ∈ U and z = η_j(x_j + λ_jz) ∈ U_j.
3. ((3), (4), (6)) (S5) with Y := T, A := U ∩ N gives IsMinimizingIn S_j A_j; (S2): spt S_j = η_j(spt T) ⊆ A_j (spt T ⊆ U ∩ N); (S3) with BoundaryVanishes T: S_j.boundary = 0.
4. ((5)) K := closedBall(x, 2r) ⊆ U is compact; (hmon) gives Λ ≥ 0 with ρ ↦ ofReal(e^{Λρ}/ρⁿ)M_{B_ρ(y)}(T) nondecreasing on (0, s) if closedBall(y, s) ⊆ K. T is IM (IsMinimizingIn) with an IMRep R; (MR): M_{B_{2r}(x)}(T) = R.measure(B_{2r}(x)) ≤ R.measure(K) = ∫⁻_{K∩M} θ dHⁿ < ∞ (locallyIntegrable_mult). Let c₁ := ofReal(e^{Λr}(2/r)ⁿ)M_{B_{2r}(x)}(T) < ∞. If |x_j − x| < r, closedBall(x_j, r) ⊆ K, so for 0 < ρ < r/2 (monotonicity on (0, r); Λ ≥ 0; B_{r/2}(x_j) ⊆ B_{2r}(x), massOn monotone) ofReal(e^{Λρ}/ρⁿ)M_{B_ρ(x_j)}(T) ≤ ofReal(e^{Λr/2}/(r/2)ⁿ)M_{B_{r/2}(x_j)}(T) ≤ c₁, so M_{B_ρ(x_j)}(T) ≤ ofReal(ρⁿ)c₁ (e^{Λρ} ≥ 1). Let R′ ∈ ℝ. If R′ ≤ 0, B_{R′}(0) = ∅, M_∅(S_j) = 0 (only the zero form is admissible), c := 0. If R′ > 0 and |x_j − x| < r, λ_jR′ < r/2 (all large j), (S1) with W := B_{λ_jR′}(x_j), η_j(W) = B_{R′}(0), gives M_{B_{R′}(0)}(S_j) = ofReal(λ_j^{−n})M_W(T) ≤ ofReal(λ_j^{−n})ofReal((λ_jR′)ⁿ)c₁ = ofReal(R′ⁿ)c₁ =: c < ∞.
5. ((7), x ∉ N: Case A) x ∈ U and (closure N ∖ N) ∩ U = ∅ give x ∉ closure N, so B_{r_N}(x) ∩ N = ∅ for some r_N > 0. Given G > 0 let π_j := id, G′ := 0. If |x_j − x| + λ_jG < r_N (all large j), A_j ∩ B_G(0) = ∅: z in it gives u := x_j + λ_jz ∈ N with |u − x| ≤ |x_j − x| + λ_j|z| < r_N, impossible. Both eventual statements of (7) hold by the first alternative.
6. ((7), x ∈ N: Case B) Part III at x (d := m + 1 + ℓ) gives δ, π with (i)–(iv); s₁ := s(1), so π is 2-Lipschitz on B_{s₁}(x). Given G > 0 let π_j := η_j∘π∘η_j⁻¹ (π_j(z) = λ_j⁻¹(π(x_j + λ_jz) − x_j)), G′ := 5G. Let j satisfy |x_j − x| + λ_jG < s₁ and |x_j − x| + 5λ_jG < r (all large j); then B_{λ_jG}(x_j) ⊆ B_{s₁}(x) ⊆ B_δ(x).
 (a) z ↦ x_j + λ_jz maps B_G(0) into B_{λ_jG}(x_j) ⊆ B_δ(x), where π is C¹, and η_j is affine: π_j is C¹ on B_G(0).
 (b) z ∈ A_j ∩ B_G(0) gives u := x_j + λ_jz ∈ U ∩ N ∩ B_δ(x), π(u) = u by (iii), π_j(z) = η_j(u) = z.
 (c) If z₀ ∈ A_j ∩ B_G(0), then w := x_j + λ_jz₀ ∈ U ∩ N ∩ B_{s₁}(x), π(w) = w. For z ∈ B_G(0), y := x_j + λ_jz ∈ B_{s₁}(x) has π(y) ∈ N by (ii) and |π(y) − x_j| ≤ |π(y) − π(w)| + |w − x_j| ≤ 2λ_j|z − z₀| + λ_j|z₀| < 5λ_jG, so |π(y) − x| < 5λ_jG + |x_j − x| < r, π(y) ∈ U ∩ N, π_j(z) ∈ A_j, |π_j(z)| = λ_j⁻¹|π(y) − x_j| < 5G = G′. With (a), (b) this gives the first eventual statement of (7).
 (d) Given η > 0, for j with |x_j − x| + λ_jG < s(η) (all large j) and y, z ∈ B_G(0): x_j + λ_jy, x_j + λ_jz ∈ B_{s(η)}(x), so |π_j(y) − π_j(z)| = λ_j⁻¹|π(x_j + λ_jy) − π(x_j + λ_jz)| ≤ (1 + η)|y − z|: the second statement of (7).

Part III (RET). Claim: if IsEmbeddedSubmanifold 2 d N and x ∈ N, there are δ > 0 and π : ℝ^P → ℝ^P with (i) π C¹ on B_δ(x); (ii) π(B_δ(x)) ⊆ N; (iii) π(y) = y for y ∈ N ∩ B_δ(x); (iv) for every η > 0 some s(η) ∈ (0, δ] with π (1 + η)-Lipschitz on B_{s(η)}(x).
1. IsEmbeddedSubmanifold at x gives V, W, ψ; pick v₀ ∈ V with ψ(v₀) = x (x ∈ W ∩ N = ψ(V)). ψ is C² on the open V. L := Dψ(v₀) : ℝ^d → ℝ^P is injective, Q := L(ℝ^d), L : ℝ^d → Q an isomorphism; p : ℝ^P → Q the orthogonal projection (‖p‖ ≤ 1, p∘L = L); A := L⁻¹∘p (continuous linear).
2. h(v) := A(ψ(v) − x) is C² near v₀, h(v₀) = 0, Dh(v₀) = A∘L = id. Inverse function theorem: open V₀ ⊆ V, v₀ ∈ V₀, and open O ∋ 0 with h : V₀ → O bijective, C¹ inverse k (k∘h = id on V₀, h∘k = id on O).
3. Φ := ψ∘k : O → ℝ^P is C¹, Φ(0) = x, Φ(O) = ψ(V₀) ⊆ N, DΦ(0) = Dψ(v₀)∘Dk(0) = L∘(Dh(v₀))⁻¹ = L.
4. F := V ∖ V₀ is closed in V; ψ(F) is closed in W: if W ∋ y = lim ψ(f_i), f_i ∈ F, the f_i lie in the compact V ∩ ψ⁻¹(K), K := {y} ∪ {ψ(f_i)} ⊆ W compact, so a subsequence tends to f ∈ V ∩ ψ⁻¹(K), f ∈ F (closed in V), ψ(f) = y (continuity). So W₀ := W ∖ ψ(F) is open, x ∈ W₀ (v₀ ∉ F, ψ injective on V), and W₀ ∩ N = ψ(V₀) (y ∈ W₀ ∩ N ⊆ ψ(V) is ψ(v) with v ∉ F; ψ(V₀) ⊆ W ∩ N misses ψ(F) by injectivity).
5. Choose r₀ > 0 with B^d_{r₀}(0) ⊆ O and δ > 0 with B_δ(x) ⊆ W₀, ‖A‖δ < r₀. Put π(y) := Φ(A(y − x)) on B_δ(x), π(y) := y elsewhere; for y ∈ B_δ(x), |A(y − x)| < r₀, so A(y − x) ∈ O.
6. (i) On B_δ(x), π is Φ (C¹) composed with an affine map into O. (ii) π(y) ∈ Φ(O) ⊆ N. (iii) If y ∈ N ∩ B_δ(x) ⊆ N ∩ W₀ = ψ(V₀), y = ψ(v), v ∈ V₀, then A(y − x) = h(v) ∈ O and π(y) = ψ(k(h(v))) = y; so π(x) = x.
7. (iv) On B_δ(x), Dπ(y) = DΦ(A(y − x))∘A is continuous (π C¹), and Dπ(x) = L∘L⁻¹∘p = p, ‖Dπ(x)‖ ≤ 1. Given η > 0 choose s ∈ (0, δ] with ‖Dπ(y) − Dπ(x)‖ ≤ η, so ‖Dπ(y)‖ ≤ 1 + η, on B_s(x); B_s(x) is convex, so the mean value inequality gives (iv). (d = 0 is included: L = 0 is injective, p = A = 0, Φ ≡ x, π ≡ x on B_δ(x), B_δ(x) ∩ N = {x} by step 4.) ∎

## Key steps

1. I: dilation scales mass by λ^{−n} (S1), transports support, ∂, IMReps (S2)–(S4); direct form ♭ pulls competitors back: minimality (S5).
2. II.1–3: U_j open, exhausting; (3), (4), (6) by (S5), (S2), (S3).
3. II.4: (hmon), (MR): M_{B_ρ(x_j)}(T) ≤ c₁ρⁿ; (5) by (S1).
4. II.5–6: x ∉ N: A_j ∩ B_G(0) = ∅ eventually; x ∈ N: π_j := η_j∘π∘η_j⁻¹, G′ := 5G.
5. III: chart, A := L⁻¹p, inverse function theorem: C¹ retraction π := Φ(A(· − x)), Dπ(x) = p.

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
