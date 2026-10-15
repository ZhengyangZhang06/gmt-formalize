<!-- theorem-id: gmt-ch07/root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1 -->

## Theorem `Submission.dtc_bc_local_comparison`

Let P, m ∈ ℕ with n := m + 1 < P. For j ∈ ℕ let U_j ⊆ ℝ^P be open, A_j ⊆ ℝ^P, S_j ∈ 𝒟_n(U_j) and Ŝ_j ∈ 𝒟_n(ℝ^P); let C ∈ 𝒟_n(ℝ^P) and ρ_j ∈ ℝ. Assume: (1) every S_j is minimizing in A_j (IsMinimizingIn S_j A_j) and spt S_j ⊆ A_j; (2) for every R ∈ ℝ there is c ∈ [0, ∞) with M_{B_R(0)}(S_j) ≤ c for all large j; (3) for every G > 0 there are maps π_j : ℝ^P → ℝ^P such that, for all large j, π_j is C¹ on B_G(0), maps B_G(0) into A_j, is the identity on A_j ∩ B_G(0) and satisfies |π_j(y)| ≤ 2|y| on B_G(0), and such that for every η > 0, for all large j, |π_j(y) − π_j(z)| ≤ (1 + η)|y − z| for y, z ∈ B_G(0); (4) C and every Ŝ_j are integer multiplicity, sup_j (M_W(Ŝ_j) + M_W(∂Ŝ_j)) < ∞ for every bounded open W ⊆ ℝ^P, and Ŝ_j ⇀ C in ℝ^P (WeaklyConvergesOn); (5) ρ_j → ∞, closedBall(0, ρ_j) ⊆ U_j, and Ŝ_j(ω) = currentEval(S_j, ω) for every ω ∈ 𝒟ⁿ(ℝ^P) with tsupport ω ⊆ B_{ρ_j}(0). Then for every compact K ⊆ ℝ^P, every ε > 0 and every strictly increasing ψ : ℕ → ℕ there are an open W ⊆ ℝ^P with K ⊆ W ⊆ {y : dist(y, K) < ε} (thickening ε K) and a strictly increasing φ' : ℕ → ℕ such that limsup_i M_W(S_{ψ(φ'(i))}) ≤ M_W(S) for every integer multiplicity S ∈ 𝒟_n(ℝ^P) with ∂S = ∂C (SameBoundary S C) and spt(S − C) ⊆ K.

Node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/832

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4711

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5377, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5385, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5388, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5391, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5392, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5396, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5398, https://github.com/ZhengyangZhang06/gmt-formalize/issues/808, https://github.com/ZhengyangZhang06/gmt-formalize/issues/810, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4196, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1308, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1174

## Lean problem

Declaration: `Submission.dtc_bc_local_comparison`

```lean
∀ (P m : ℕ) (Us As : ℕ → Set (Euclid P)) (Ss : (j : ℕ) → GeometricCurrentOn (Us j) (m + 1)) (Ŝ : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (C : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (ρ : ℕ → ℝ), m + 1 < P → (∀ j, IsOpen (Us j)) → (∀ j, IsMinimizingIn (Ss j) (As j)) → (∀ j, (Ss j).support ⊆ As j) → (∀ R : ℝ, ∃ c : ℝ≥0∞, c ≠ ∞ ∧ ∀ᶠ j in atTop, (Ss j).massOn (ball 0 R) ≤ c) → (∀ G : ℝ, 0 < G → ∃ πs : ℕ → Euclid P → Euclid P, (∀ᶠ j in atTop, ContDiffOn ℝ 1 (πs j) (ball 0 G) ∧ MapsTo (πs j) (ball 0 G) (As j) ∧ (∀ y ∈ As j ∩ ball 0 G, πs j y = y) ∧ ∀ y ∈ ball 0 G, ‖πs j y‖ ≤ 2 * ‖y‖) ∧ ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∀ y ∈ ball 0 G, ∀ z ∈ ball 0 G, ‖πs j y - πs j z‖ ≤ (1 + η) * ‖y - z‖) → IsIntegerMultiplicity C → (∀ j, IsIntegerMultiplicity (Ŝ j)) → (∀ W : Set (Euclid P), IsOpen W → Bornology.IsBounded W → ⨆ j, ((Ŝ j).massOn W + (Ŝ j).boundary.massOn W) < ∞) → WeaklyConvergesOn Ŝ C → Tendsto ρ atTop atTop → (∀ j, closedBall (0 : Euclid P) (ρ j) ⊆ Us j) → (∀ (j : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) (m + 1)), tsupport (ω : DifferentialForm (Euclid P) (m + 1)) ⊆ ball 0 (ρ j) → Ŝ j ω = currentEval (Ss j) (ω : DifferentialForm (Euclid P) (m + 1))) → ∀ (K : Set (Euclid P)) (ε : ℝ), IsCompact K → 0 < ε → ∀ ψ : ℕ → ℕ, StrictMono ψ → ∃ W : Set (Euclid P), IsOpen W ∧ K ⊆ W ∧ W ⊆ thickening ε K ∧ ∃ φ' : ℕ → ℕ, StrictMono φ' ∧ ∀ S : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), IsIntegerMultiplicity S → SameBoundary S C → (S - C).support ⊆ K → limsup (fun j => (Ss (ψ (φ' j))).massOn W) atTop ≤ S.massOn W
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

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 4.1–4.6 of the parent proof, i.e. Simon's proof of 7.2.4, displays (1)–(11) (chapter-07.txt lines 176–258), run with the retractions of Remark 7.2.5(2) (lines 166–174) and with the subsequence-of-a-subsequence argument of lines 278–280 built into the quantifier over ψ. Cited results of the source text — the same ones the parent proof cites — each used in its stated range (n ≥ 1, P − n ≥ 1, U = ℝ^P):
(C1) Simon Ch. 6, 7.1–7.2 (chapter-06.txt lines 2004–2040). For W ⊂⊂ U and T₁, T₂ in the class I of integer multiplicity n-currents with M_W(∂T) < ∞ for all W ⊂⊂ U, d_W(T₁, T₂) := inf{M_W(S) + M_W(R) : T₁ − T₂ = ∂R + S, R ∈ 𝒟_{n+1}(U), S ∈ 𝒟_n(U) integer multiplicity}. If T, T_j are integer multiplicity, sup_j (M_W(T_j) + M_W(∂T_j)) < ∞ for all W ⊂⊂ U and T_j ⇀ T, then d_W(T_j, T) → 0 for every W ⊂⊂ U.
(C2) Simon Ch. 6, 4.4–4.5 and 4.8 (lines 1151–1300, 1353). If R ∈ 𝒟_{n+1}(U) is integer multiplicity with M_W(∂R) < ∞ for all W ⊂⊂ U and f is Lipschitz, then for L¹-a.e. t the slice ⟨R, f, t⟩ of 4.4 is an integer multiplicity n-current carried by f⁻¹(t) (so its support lies in f⁻¹(t)) and ⟨R, f, t⟩ = ∂(R⌞{f < t}) − (∂R)⌞{f < t} (4.5(2)); and ∫_ℝ M_W(⟨R, f, t⟩) dt ≤ Lip(f)·M_W(R) for every open W (4.5(1)).
(C3) Simon Ch. 6, 2.23–2.24, 2.29 and 3.3–3.9 (lines 404–530, 776–860), push-forward of an integer multiplicity current with compact support by a map that is C¹ on an open neighbourhood of the support; its properties are listed where it is used, in step 6.
Sibling used: measure_locality (MEAS). Inherited dependencies: dtc_mass_eq_measure (M), dtc_vanish_off_support (V), dtc_isIntegerMultiplicity_sub (G).
0. (Facts about integer multiplicity currents.) For an IM current Y in an open V with representation R_Y = (M_Y, θ_Y, ξ_Y), μ_Y := R_Y.measure. (F1) M_O(Y) = μ_Y(O) for every open O (M applied to O ∩ V, and M_O(Y) = M_{O∩V}(Y)); μ_Y(K) < ∞ for compact K ⊆ V. (F2) If Y, Y' are IM (in open V, V') and agree on the forms supported in an open O ⊆ V ∩ V', then μ_Y = μ_{Y'} on Borel subsets of O (MEAS); in particular μ_Y does not depend on R_Y. (F3) μ_Y(V ∖ spt Y) = 0: V ∖ spt Y is open, Y vanishes on forms supported there (V), so its mass there is 0 (F1). (F4) If A, B are IM in V then A ± B are IM (G; A + B = A − (0 − B)) and μ_{A±B}(E) ≤ μ_A(E) + μ_B(E) for every Borel E: for open E because M_E(A ± B) ≤ M_E(A) + M_E(B) (each admissible ω gives (A ± B)(ω) ≤ M_E(A) + M_E(B), as ±ω is admissible), and for Borel E by outer regularity of these locally finite Borel measures (choose open O_q ↓ approximating E for μ_A, μ_B and μ_{A±B} simultaneously). (F5) For an IM A and open O, A⌞O := the current represented by (M_A ∩ O, θ_A, ξ_A) is IM (approximate tangent spaces at points of the open O are those of M_A), μ_{A⌞O} = μ_A⌞O, (A⌞O)(ω) = A(ω) if tsupport ω ⊆ O, spt(A⌞O) ⊆ closure O, and M(A⌞O) = μ_A(O). An IM current in ℝ^P whose support is a compact subset of U_j is regarded as an IM current in U_j (restrictDomain; represented by its triple with the carrier intersected with U_j).
Fix K, ε and ψ.
1. (Reduction to ψ = id.) Hypotheses (1)–(5) are preserved when (U_j, A_j, S_j, Ŝ_j, ρ_j) is replaced by (U_{ψ(j)}, A_{ψ(j)}, S_{ψ(j)}, Ŝ_{ψ(j)}, ρ_{ψ(j)}): statements for all large j and limits transfer along ψ(j) → ∞, a subsequence of a weakly convergent sequence converges weakly, and a supremum over a subsequence is smaller. A strictly increasing φ' that works for the re-indexed sequence gives the claim for S_{ψ(φ'(i))}. So assume ψ = id. If K = ∅ take W := ∅ and φ' := id: M_∅(·) = 0 (the only admissible form is 0). Assume K ≠ ∅.
2. (Cut-off; book (1).) Let ε₁ := min(ε, 1)/2 and choose ψ_c ∈ C^∞(ℝ^P; [0, 1]) with ψ_c = 1 on a neighbourhood of K and tsupport ψ_c ⊆ thickening(ε₁, K) (compact). Put W_s := {ψ_c > s} for 0 ≤ s < 1 (open, K ⊆ W_s ⊆ thickening(ε, K)), Σ_s := {ψ_c = s} and F_s := {ψ_c ≥ s} (compact for s > 0), and L₀ := sup|Dψ_c| (a Lipschitz constant of ψ_c). Fix G ≥ 1 with tsupport ψ_c ⊆ ball(0, G/3) and write B_G := ball(0, G).
3. (Good indices.) Apply hypothesis (3) with radius 2G to get maps π_j. There is j₀ such that for j ≥ j₀: (R1) π_j is C¹ on ball(0, 2G), maps it into A_j, fixes A_j ∩ ball(0, 2G) and satisfies |π_j(y)| ≤ 2|y| there; (R2) ρ_j > G, so closedBall(0, G) ⊆ ball(0, ρ_j) ⊆ U_j; (R3) M_{B_G}(S_j) ≤ c_G (hypothesis (2) with R = G). For η > 0 let j(η) ≥ j₀ be such that π_j is (1 + η)-Lipschitz on ball(0, 2G) for j ≥ j(η); then ‖Dπ_j(y)‖ ≤ 1 + η for y ∈ ball(0, 2G).
4. (Flat convergence; book (2).) M_W(∂C) ≤ liminf_j M_W(∂Ŝ_j) < ∞ for bounded open W (lower semicontinuity of mass, SimonGMT WeaklyConvergesOn.massOn_le_liminf applied to ∂Ŝ_j ⇀ ∂C), so C and the Ŝ_j belong to Simon's class I in U = ℝ^P, and by 7.2, d_{W₀}(Ŝ_j, C) → 0 for W₀ := {ψ_c > 0} (bounded open). By the definition 7.1 of d_{W₀} (take decompositions within 1/j of the infimum and change signs) there are IM R_j ∈ 𝒟_{n+1}(ℝ^P) (n + 1 ≤ P) and IM S'_j ∈ 𝒟_n(ℝ^P) with C − Ŝ_j = ∂R_j + S'_j and a_j := M_{W₀}(R_j) + M_{W₀}(S'_j) → 0. ∂R_j = C − Ŝ_j − S'_j is IM (F4) and has locally finite mass (F1).
5. (Slicing and choice of α; book (3)–(5).) Choose φ₁ strictly increasing with φ₁(i) ≥ j₀ and Σ_i a_{φ₁(i)} < ∞. For each i apply 4.4–4.5 to the IM current R_{φ₁(i)} (its boundary has locally finite mass) and the Lipschitz function f := −ψ_c: for a.e. t the slice ⟨R_{φ₁(i)}, f, t⟩ is IM, carried by f⁻¹(t), and equals ∂(R_{φ₁(i)}⌞{f < t}) − (∂R_{φ₁(i)})⌞{f < t}; and ∫ M_{W₀}(⟨R_{φ₁(i)}, f, t⟩) dt ≤ L₀·M_{W₀}(R_{φ₁(i)}). For α ∈ (0, 1) and t = −α, {f < t} = W_α and f⁻¹(t) = Σ_α ⊆ W₀, so P_i(α) := ⟨R_{φ₁(i)}, f, −α⟩ satisfies M(P_i(α)) = M_{W₀}(P_i(α)) and ∫_0^1 Σ_i M(P_i(α)) dα ≤ L₀Σ_i a_{φ₁(i)} < ∞. Choose α ∈ (0, 1) outside the union of the following null sets: the levels where for some i the slice is not IM or the slice identity fails (countably many null sets); the levels with Σ_i M(P_i(α)) = ∞; and the levels with μ_{S_{φ₁(i)}}(Σ_α) > 0 for some i (for each i these are countably many, because the Σ_α are pairwise disjoint subsets of the compact set tsupport ψ_c ⊆ U_{φ₁(i)}, which has finite μ_{S_{φ₁(i)}}-measure). Fix such α, put W := W_α, Σ := Σ_α, F := F_α, O' := B_G ∩ {ψ_c < α} (open), so B_G is the disjoint union of W, Σ and O', and F ⊆ tsupport ψ_c ⊆ ball(0, G/3). Set φ' := φ₁ and re-index: S_i := S_{φ₁(i)}, Ŝ_i, R_i, S'_i, U_i, A_i, π_i accordingly, P_i := P_i(α). Then P_i is IM, spt P_i ⊆ Σ (4.8), M(P_i) → 0, μ_{S_i}(Σ) = 0, and ∂(R_i⌞W) = (∂R_i)⌞W + P_i. With R̃_i := R_i⌞W and S̃_i := S'_i⌞W − P_i (IM by F5, F4), restricting C − Ŝ_i = ∂R_i + S'_i to W gives book (6): C⌞W = Ŝ_i⌞W + ∂R̃_i + S̃_i, and M(S̃_i) ≤ μ_{S'_i}(W) + M(P_i) ≤ a_i + M(P_i) → 0 (book (7)).
6. (The competitor.) Let S be IM with SameBoundary S C and spt(S − C) ⊆ K. Then X := S − C is IM (G), ∂X = 0, spt X ⊆ K ⊆ W. Y_i := X + ∂R̃_i, where ∂R̃_i = (C − Ŝ_i)⌞W − S̃_i is IM (F4, F5); so Y_i is IM, ∂Y_i = 0, and spt Y_i ⊆ closure W ∪ spt P_i ⊆ F ⊆ ball(0, G/3) is compact. Push-forward (Simon 2.24(2), 3.3–3.9, 2.29): for an IM Q ∈ 𝒟_n(ℝ^P) whose support is a compact subset of ball(0, 2G) and i ≥ j₀, π_{i#}Q(ω) := ∫_{M_Q} θ_Q⟨ω(π_i(y)), Dπ_i(y)_#ξ_Q(y)⟩ dHⁿ(y) defines an IM current (3.9) with spt π_{i#}Q ⊆ π_i(spt Q) (ω ∘ π_i vanishes on spt Q if ω vanishes near π_i(spt Q); F3); it is additive in Q; ∂π_{i#}Q = π_{i#}∂Q if ∂Q has finite mass (2.24(1) for the mollified maps and 2.29), so π_{i#}Y_i is a cycle; and M(π_{i#}Q) ≤ L^n·M(Q) if ‖Dπ_i‖ ≤ L on ball(0, 2G), because |Dπ_i(y)_#(τ₁∧⋯∧τₙ)| ≤ ‖Dπ_i(y)‖ⁿ (Hadamard) and |⟨α, v⟩| ≤ |α||v| for the Euclidean norms. Now spt π_{i#}Y_i ⊆ π_i(F) ⊆ A_i ∩ closedBall(0, 2G/3) ⊆ A_i ∩ B_G (R1). Let Z_i := S_i + π_{i#}Y_i ∈ 𝒟_n(U_i) (π_{i#}Y_i regarded in U_i). Z_i is IM (F4), ∂Z_i = ∂S_i, and spt(Z_i − S_i) is a compact subset of A_i ∩ B_G, while B_G is open with compact closure in U_i (R2). Minimality of S_i in A_i (with the open set B_G) gives M_{B_G}(S_i) ≤ M_{B_G}(Z_i).
7. (π_i fixes S_i near B_G; parent step 4.5.) Let (M_i, θ_i, ξ_i) represent S_i and Q_i := S_i⌞B_G (IM, support ⊆ closedBall(0, G)). Claim: π_{i#}Q_i = Q_i. By F3 and spt S_i ⊆ A_i, Hⁿ-a.e. y ∈ M_i lies in A_i; let M'_i := M_i ∩ B_G ∩ A_i, so Hⁿ((M_i ∩ B_G) ∖ M'_i) = 0 and π_i(z) = z for z ∈ M'_i (R1). Let y ∈ M'_i be a point (Hⁿ-a.e. point of M_i ∩ B_G) where HasApproximateTangentSpaceAt n M_i y Q_y holds and ξ_i(y) = ±τ₁∧⋯∧τₙ for an orthonormal basis τ of Q_y. (a) HasApproximateTangentSpaceAt n M'_i y Q_y: inside any bounded set and for small r, η_{y,r}(M_i) and η_{y,r}(M'_i) differ by the image of an Hⁿ-null set (Hⁿ(η_{y,r}(Z)) = r^{−n}Hⁿ(Z)) because y lies in the open B_G. (b) Every unit v ∈ Q_y is a limit of (z_k − y)/|z_k − y| with z_k ∈ M'_i ∖ {y}, z_k → y: otherwise there are ε', r' > 0 such that M'_i ∩ (ball(y, r') ∖ {y}) avoids the cone {z : |(z − y)/|z − y| − v| < ε'}, so for r < r' the set η_{y,r}(M'_i) misses the open set Ω := {w : 1/2 < |w| < 1, |w/|w| − v| < ε'}; testing (a) with f ∈ C_c, 0 ≤ f, supported in Ω and positive at (3/4)v gives 0 → ∫_{Q_y} f dHⁿ > 0, a contradiction. (c) π_i is differentiable at y and π_i(z_k) = z_k, π_i(y) = y, so (I − Dπ_i(y))(z_k − y) = o(|z_k − y|) and hence (I − Dπ_i(y))v = 0. Thus Dπ_i(y) is the identity on Q_y, Dπ_i(y)_#ξ_i(y) = ξ_i(y) and ω(π_i(y)) = ω(y), so π_{i#}Q_i(ω) = ∫_{M_i ∩ B_G} θ_i⟨ω(y), ξ_i(y)⟩ dHⁿ = Q_i(ω). Consequently, for ω supported in B_G, Z_i(ω) = Q_i(ω) + π_{i#}Y_i(ω) = π_{i#}(Q_i + Y_i)(ω), so for i ≥ j(η): M_{B_G}(Z_i) ≤ M(π_{i#}(Q_i + Y_i)) ≤ (1 + η)ⁿM(Q_i + Y_i). Moreover M(Q_i + Y_i) = μ_{Q_i+Y_i}(ℝ^P) = μ_{S_i+Y_i}(B_G): on B_G the IM currents Q_i + Y_i and S_i + Y_i agree (F2), and μ_{Q_i+Y_i}(ℝ^P ∖ B_G) ≤ μ_{Q_i}(ℝ^P ∖ B_G) + μ_{Y_i}(ℝ^P ∖ B_G) = 0 (F4, F3). Hence (I) μ_{S_i}(B_G) = M_{B_G}(S_i) ≤ (1 + η)ⁿ μ_{S_i+Y_i}(B_G) for i ≥ j(η).
8. (Comparison off W; book (8)–(11).) (a) μ_{S_i}(B_G) = μ_{S_i}(W) + μ_{S_i}(Σ) + μ_{S_i}(O') = μ_{S_i}(W) + μ_{S_i}(O'). (b) Y_i vanishes on forms supported in O' (spt Y_i ⊆ F is disjoint from O'; V), so μ_{S_i+Y_i}(O') = μ_{S_i}(O') (F2). (c) μ_{S_i+Y_i}(Σ) ≤ μ_{S_i}(Σ) + μ_{Y_i}(Σ) = μ_{Y_i}(Σ) (F4), and from Y_i = X + (C − Ŝ_i)⌞W − S'_i⌞W + P_i, μ_{Y_i}(Σ) ≤ μ_X(Σ) + μ_{(C−Ŝ_i)⌞W}(Σ) + μ_{S'_i⌞W}(Σ) + μ_{P_i}(Σ) ≤ 0 + 0 + 0 + M(P_i): Σ ∩ K = ∅ (ψ_c = 1 on K, α < 1) and spt X ⊆ K (F3); restrictions to W are carried by W (F5). (d) For ω supported in W ⊆ ball(0, ρ_i): (S_i + Y_i)(ω) = Ŝ_i(ω) + X(ω) + ∂R̃_i(ω) (hypothesis (5)) = C(ω) − S̃_i(ω) + X(ω) (book (6) evaluated at ω) = (S − S̃_i)(ω); so μ_{S_i+Y_i}(W) = μ_{S−S̃_i}(W) ≤ μ_S(W) + M(S̃_i) (F2, F4). (e) By (I) and (a)–(d), for i ≥ j(η): μ_{S_i}(W) + μ_{S_i}(O') ≤ (1 + η)ⁿ[μ_S(W) + M(S̃_i) + M(P_i) + μ_{S_i}(O')]. All terms are finite (μ_{S_i}(O') ≤ μ_{S_i}(B_G) ≤ c_G by (R3); μ_S(W) < ∞ as W is bounded), so μ_{S_i}(W) ≤ μ_S(W) + M(S̃_i) + M(P_i) + ((1 + η)ⁿ − 1)(μ_S(W) + M(S̃_i) + M(P_i) + c_G). (f) Letting i → ∞ (M(S̃_i), M(P_i) → 0): limsup_i μ_{S_i}(W) ≤ μ_S(W) + ((1 + η)ⁿ − 1)(μ_S(W) + c_G) for every η > 0, hence limsup_i μ_{S_i}(W) ≤ μ_S(W). By F1, μ_{S_i}(W) = M_W(S_i) and μ_S(W) = M_W(S).
9. (Output.) W = W_α is open with K ⊆ W ⊆ thickening(ε, K); φ' = φ₁ is strictly increasing and was chosen before S (it depends only on K, ε, ψ and the data); and limsup_i M_W(S_{φ'(i)}) ≤ M_W(S) for every admissible S. Undoing step 1 gives the claim for S_{ψ(φ'(i))}. ∎

## Key steps

1. Reduce to ψ = id (hypotheses are stable under subsequences) and fix a cut-off ψ_c with level sets W_s ⊇ K inside thickening(ε, K) and inside B_{G/3}(0).
2. Flat convergence (Simon 6.7.2) writes C − Ŝ_j = ∂R_j + S'_j with masses on W₀ tending to 0; slicing R_j by ψ_c (Simon 6.4.5) at a good level α along a further subsequence gives C⌞W_α = Ŝ_i⌞W_α + ∂R̃_i + S̃_i with M(S̃_i), M(P_i) → 0 and no S_i-mass on {ψ_c = α}.
3. For a competitor S, Y_i := (S − C) + ∂R̃_i is a compactly supported IM cycle; Z_i := S_i + π_{i#}Y_i is an admissible competitor in A_i ∩ B_G, and since π_i fixes S_i⌞B_G a.e. with Dπ_i = id on its tangent planes, M_{B_G}(S_i) ≤ (1+η)ⁿμ_{S_i+Y_i}(B_G).
4. Splitting B_G into W_α, {ψ_c = α} and the rest (book (9)–(11)) yields μ_{S_i}(W_α) ≤ μ_S(W_α) + errors → limsup ≤ M_{W_α}(S).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db, mathlib 25730c7c); cmp project/GMT/Ch07/Contract.lean against workspace GMT/Ch07/Contract.lean and GMT/Ch07/Submission.lean (identical)`
- `grep -n 'def GeometricCurrentOn.massOn|massAdmissibleOn|massOn_le_liminf|massOn_mono|le_massOn' simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `grep -n 'restrictDomain|VanishesOn|zeroRegion|def GeometricCurrentOn.support' simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean; grep -n 'GeometricCurrentOn.boundary|instance .*Zero|tsupport_exteriorDerivative_subset|WeaklyConvergesOn' simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `grep -n 'affinePullbackForm|affinePushforward|boundary_affinePushforward|tsupport_affinePullbackForm_subset|exteriorDerivative_affinePullbackForm' simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `grep -n 'def CountablyRectifiable|CountablyRectifiable.mono|countablyRectifiable_range|def HasApproximateTangentSpaceAt|hasApproximateTangentSpaceAt_submodule|HasApproximateTangentSpaceAt.unique' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -rn 'ae_eq_const_of_weak_coordinate_derivatives_zero|WeakDerivativesZero' simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean; #print axioms Poincare.SimonGMT.Chapter08.ae_eq_const_of_weak_coordinate_derivatives_zero`
- `grep -n '^theorem' simongmt/Poincare/SimonGMT/Chapter02/{AreaLipschitz,AreaFormula,CoareaLinear,BV,Lipschitz}.lean simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean (no Federer–Fleming compactness, slicing, flat metric, rectifiable area/coarea formula or C¹ push-forward of currents)`
- `grep -rn 'lintegral_eq_lintegral_meas_lt|lintegral_eq_lintegral_meas_le|lintegral_liminf_le|limsup_lintegral_le|ext_of_generate_finite|isPiSystem_isOpen|tendsto_measure_thickening_of_isClosed|extraction_of_frequently_atTop|toOpenPartialHomeomorph|norm_image_sub_le_of_norm_fderiv_le|euclideanHausdorffMeasure_eq_volume|eq_smul_basis_det|det_to_matrix_orthonormalBasis_real|exists_thickening_subset_open|setIntegral_eq_integral_of_forall_compl_eq_zero|restrict_withDensity' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `grep -rl 'dtc_bc_' .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4 GMT simongmt/Poincare (no match); lean_name inventory of dag.json (198 nodes, no collision)`
- `python3 -I: verifier/gmt-compare.py contract_scope + child_modules (contract mode) and verifier/lean_contract.py validate_lean_statement on all eight child types`
- `lake env lean /tmp/dtcbc/check/Challenge_<key>.lean (8 files), /tmp/dtcbc/check/Assembly.lean, /tmp/dtcbc/check/Iface.lean, /tmp/dtcbc/check/Lib.lean, /tmp/dtcbc/check/Lib2.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Layercake.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/dtcbc/check/Assembly.lean`
- `/tmp/dtcbc/check/Iface.lean`
- `/tmp/dtcbc/stmts/stmts.py`
- `/tmp/dtcbc/stmts/children.py`

The snapshot contract (project b4d606d, Mathlib 25730c7c) is byte-identical to the workspace Contract.lean and Submission.lean. The pinned SimonGMT library provides the objects the children use: GeometricCurrentOn, boundary, massOn/massAdmissibleOn, WeaklyConvergesOn.massOn_le_liminf, support/zeroRegion, restrictDomain, affinePushforward with boundary_affinePushforward and tsupport_affinePullbackForm_subset, CountablyRectifiable with countablyRectifiable_range, and HasApproximateTangentSpaceAt with hasApproximateTangentSpaceAt_submodule. It also provides the distributional constancy theorem Chapter08.ae_eq_const_of_weak_coordinate_derivatives_zero (standard axioms), which makes the k = 0 child self-contained. The library has no Federer–Fleming compactness, slicing, flat-metric theorem, rectifiable area/coarea formula or C¹ push-forward of currents. Those Simon Ch. 6 results are cited only by truncated_compactness and local_comparison, exactly as in the accepted parent proof. Every Mathlib lemma named in the proofs exists at the pin. All eight child types elaborate in the comparator scope, and the conditional assembly of the selected type from five of them uses only propext, Classical.choice and Quot.sound. No dtc_bc_ name occurs elsewhere.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
