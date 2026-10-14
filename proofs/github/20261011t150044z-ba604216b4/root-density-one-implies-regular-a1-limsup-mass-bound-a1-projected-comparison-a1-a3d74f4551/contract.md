<!-- theorem-id: gmt-ch07/root.density_one_implies_regular-a1.limsup_mass_bound-a1.projected_comparison-a1 -->

## Theorem `Submission.dor_lmb_projected_competitor_comparison`

Assume (C1), the frozen statement of the sibling-of-parent node dor_imrep_massOn_eq_measure_and_support: for all P, n ∈ ℕ, open U ⊆ ℝ^P, T ∈ 𝒟_n(U) and every integer multiplicity triple R in U representing T, M_W(T) = μ_R(W) for every open W ⊆ ℝ^P, and spt T = U ∩ spt μ_R. Let P, d, n ∈ ℕ with n ≥ 1, U ⊆ ℝ^P open, N ⊆ ℝ^P an embedded C² d-dimensional submanifold, and y ∈ N. Let r, c, ρ, t ∈ ℝ with c ≥ 0, ρ > 0, 3ρ < r, 4cρ ≤ 1, t < 2ρ and B̄_{3ρ}(y) ⊆ U.
Let π : ℝ^P → ℝ^P be C¹ on B_r(y) with π(B_r(y)) ⊆ N. Assume π(x) = x and Dπ(x)v = v for x ∈ N ∩ B_r(y) and v ∈ T_xN (tangentSpace), and ‖Dπ(x)‖ ≤ 1 + c|x − y| for x ∈ B_r(y).
Let Z ∈ 𝒟_n(U) be minimizing in U ∩ N (7.1.1) with spt Z ⊆ N and ∂Z = 0, represented by an integer multiplicity triple RZ. Let X ∈ 𝒟_n(U) be integer multiplicity with ∂X = 0 and X(ω) = 0 for every ω ∈ 𝒟ⁿ(U) whose support is disjoint from B̄_t(y). Let Y ∈ 𝒟_n(U) with Y = Z + X, represented by an integer multiplicity triple RY. Then
μ_{RZ}(B̄_t(y)) ≤ (1 + 3cρ)ⁿ μ_{RY}(B̄_t(y)) + ((1 + 3cρ)ⁿ − 1) μ_{RZ}(B_{3ρ}(y)).

Node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.projected_comparison-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/677

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4705, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4709

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5225, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5239, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5247, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5254, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5261, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5264, https://github.com/ZhengyangZhang06/gmt-formalize/issues/998, https://github.com/ZhengyangZhang06/gmt-formalize/issues/986, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4544, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1083, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1084, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1355

## Lean problem

Declaration: `Submission.dor_lmb_projected_competitor_comparison`

```lean
(∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → (∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) ∧ T.support = U ∩ R.measure.support) → ∀ (P d n : ℕ) (U N : Set (Euclid P)) (Z X Y : GeometricCurrentOn U n) (RZ RY : IMRep U n) (proj : Euclid P → Euclid P) (y : Euclid P) (r c ρ t : ℝ), IsOpen U → 0 < n → IsEmbeddedSubmanifold 2 d N → IsMinimizingIn Z (U ∩ N) → Z.support ⊆ N → BoundaryVanishes Z → RZ.Represents Z → IsIntegerMultiplicity X → BoundaryVanishes X → (∀ ω : TestFormOn U n, Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) (closedBall y t) → X ω = 0) → (∀ ω : TestFormOn U n, Y ω = Z ω + X ω) → RY.Represents Y → y ∈ N → 0 ≤ c → 0 < ρ → 3 * ρ < r → 4 * c * ρ ≤ 1 → t < 2 * ρ → closedBall y (3 * ρ) ⊆ U → ContDiffOn ℝ 1 proj (ball y r) → MapsTo proj (ball y r) N → (∀ x ∈ N ∩ ball y r, proj x = x) → (∀ x ∈ N ∩ ball y r, ∀ v ∈ tangentSpace N x, fderiv ℝ proj x v = v) → (∀ x ∈ ball y r, ‖fderiv ℝ proj x‖ ≤ 1 + c * dist x y) → RZ.measure (closedBall y t) ≤ ENNReal.ofReal ((1 + 3 * c * ρ) ^ n) * RY.measure (closedBall y t) + ENNReal.ofReal ((1 + 3 * c * ρ) ^ n - 1) * RZ.measure (ball y (3 * ρ))
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

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.projected_comparison-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 6–8 of the parent proof. This is the comparison (8)–(9) in Simon's proof of 7.2.4 (chapter-07.txt lines 222–246), with the competitor projected into N by π (README erratum 5, N_i = N). It uses Simon Ch. 6, 2.23–2.24 and 3.3–3.9 for push-forward (chapter-06.txt lines 408–440 and 763–860); Ch. 3, 1.2–1.6 and 2.3–2.6 (C¹ covers of rectifiable sets, approximate tangent spaces, area formula; chapter-03.txt lines 1–143 and 330–410); (C1); and the siblings int_combination and tangent_locality.
Correction of Simon 3.9, used in step 5(c): the multiplicity N of f_#τ(M, θ, ξ) in 3.8 is only a non-negative integer, because oppositely oriented sheets with the same image cancel. For example, an oriented rectangle boundary projected onto a line has zero push-forward, although its image has positive H¹-measure. So Simon's triple (f(M), ζ, N) need not have positive multiplicity on its carrier, as IMRep.mult_pos requires. Step 5(c) chooses Borel versions and restricts the carrier to {N ≥ 1}.
Notation: F := B̄_t(y), G := B_{3ρ}(y), Λ := 1 + 3cρ, μ_Z := μ_{RZ}, μ_Y := μ_{RY}. Write RZ = (M_Z, θ_Z, ξ_Z), RY = (M_Y, θ_Y, ξ_Y), and fix a representation RX = (M_X, θ_X, ξ_X) of X. Dπ(x) is the Fréchet derivative (fderiv) of π at x, and ‖·‖ is the operator norm.
Multilinear algebra:
- For an n-covector α and a linear map L, α∘L is the covector (v₁, …, vₙ) ↦ α(Lv₁, …, Lvₙ).
- An n-vector is a linear functional ζ on n-covectors (MultiVector), and (∧ₙL)ζ is the n-vector α ↦ ζ(α∘L).
- For increasing I = (i₁ < ⋯ < iₙ), dx^I is the coordinate covector (v₁, …, vₙ) ↦ det[(v_j)_{i_k}], and e_I := (e_{i₁}, …, e_{iₙ}). Then α = Σ_I α(e_I)dx^I, and the coordinates ζ(dx^I) determine ζ.
- |α|_E := (Σ_I α(e_I)²)^{1/2} is the Euclidean coefficient norm used in M_W, and |ζ| := (Σ_I ζ(dx^I)²)^{1/2}.
- A unit orientation of an n-dimensional subspace Π is an n-vector ζ with ζ(α) = ±α(σ₁, …, σₙ) for all α, for an orthonormal basis σ of Π (IsUnitOrientationOf).
Four facts are used below.
 (L1) |α(v₁, …, vₙ)| ≤ |α|_E·Π_j|v_j|. This follows from α(v) = Σ_I α(e_I)det[(v_j)_I], Cauchy–Schwarz, Cauchy–Binet (Σ_I det[(v_j)_I]² = det(v_i·v_j)) and Hadamard (det(v_i·v_j) ≤ Π_j|v_j|²). Also |α(v)| ≤ ‖α‖·Π_j|v_j| for the operator norm ‖α‖.
 (L2) A unit orientation ζ of Π has |ζ| = 1, by Cauchy–Binet. For every n-vector ζ, |ζ(α)| ≤ |ζ||α|_E, by Cauchy–Schwarz in the coordinates.
 (L3) Two unit orientations of the same Π differ by a sign: orthonormal bases of Π differ by an orthogonal matrix O, and α(σO) = det(O)α(σ) with det(O) = ±1.
 (L4) Let ζ(α) = ±α(τ₁, …, τₙ) for an orthonormal basis τ of an n-plane P₀, and let L be linear. Then (∧ₙL)ζ(α) = ±α(Lτ₁, …, Lτₙ) and |(∧ₙL)ζ| = det(Lτ_i·Lτ_j)^{1/2} ≤ ‖L‖ⁿ. If |(∧ₙL)ζ| = 0, then (∧ₙL)ζ = 0. If |(∧ₙL)ζ| > 0, then L is injective on P₀ and L(P₀) is an n-plane. Writing Lτ_j = Σ_l B_{lj}σ_l for an orthonormal basis σ of L(P₀) gives (∧ₙL)ζ(α) = ±det(B)α(σ) with |det B| = |(∧ₙL)ζ|. So (∧ₙL)ζ/|(∧ₙL)ζ| is a unit orientation of L(P₀).
If t < 0 then F = ∅ and the claim is trivial, so assume t ≥ 0. Then F ⊆ B_{2ρ}(y) ⊆ G, and Ḡ = B̄_{3ρ}(y) ⊆ B_r(y) ∩ U is compact.
1. Lipschitz bounds and π(F).
 (a) For 0 < s < r the closed ball B̄_s(y) ⊆ B_r(y) is convex, π is differentiable on it, and ‖Dπ‖ ≤ 1 + cs there. By the mean value inequality (Mathlib Convex.norm_image_sub_le_of_norm_fderiv_le), |π(x) − π(x')| ≤ (1 + cs)|x − x'| for x, x' ∈ B̄_s(y). In particular π is Λ-Lipschitz on B̄_{2ρ}(y), since 2ρ < r and 1 + 2cρ ≤ Λ. Hence Hⁿ(π(A)) ≤ ΛⁿHⁿ(A) for every A ⊆ B̄_{2ρ}(y).
 (b) π(y) = y, since y ∈ N ∩ B_r(y).
 (c) For x ∈ F: |π(x) − y| ≤ (1 + ct)t ≤ (1 + 2cρ)t < (3/2)(2ρ) = 3ρ, using 4cρ ≤ 1. Also π(x) ∈ N, since F ⊆ B_r(y). So K' := π(F) is a compact subset of N ∩ G ⊆ U.
 (d) Let p₀ be the nearest point projection of ℝ^P onto the closed convex ball B̄_{2ρ}(y); it is 1-Lipschitz. Then π̃ := π∘p₀ is Λ-Lipschitz on ℝ^P and agrees with π on B̄_{2ρ}(y) ⊇ F.
2. Consequences of (C1).
 (a) μ_X(ℝ^P ∖ F) = 0. U ∖ F is open, and X vanishes on every form admissible for M_{U∖F}(X), since such a form has support disjoint from F. So μ_X(U ∖ F) = M_{U∖F}(X) = 0, and μ_X(ℝ^P ∖ U) = 0. Since θ_X ≥ 1, Hⁿ(M_X ∖ F) = 0.
 (b) μ_Z(U ∖ N) = 0. By (C1), U ∩ spt μ_Z = spt Z ⊆ N. So U ∖ N ⊆ ℝ^P ∖ spt μ_Z, which is μ_Z-null (Mathlib measure_compl_support). Hence Hⁿ(M_Z ∖ N) = 0.
 (c) For every open V ⊆ U ∖ F we have Y(ω) = Z(ω) + X(ω) = Z(ω) when spt ω ⊆ V. Hence μ_Y(V) = M_V(Y) = M_V(Z) = μ_Z(V).
 (d) μ_Z(G) = M_G(Z) < ∞, μ_Y(G) < ∞ and ∫_{M_X∩F} θ_X dHⁿ < ∞. These follow from local integrability on the compact sets Ḡ ⊆ U and F ⊆ U.
3. Tangent inclusion. Claim: for Hⁿ-a.e. x ∈ M_Z, x ∈ N, T_xM_Z =: Q exists, ξ_Z(x) orients Q, and Q ⊆ tangentSpace N x. The first three hold a.e. by 2(b) and the IMRep property. Fix such an x, a chart ψ : V → W of N at x with x = ψ(v_x), and put L := range Dψ(v_x).
 (a) L ⊆ tangentSpace N x. Let w ∈ ℝ^d and choose δ > 0 with B̄_δ(v_x) ⊆ V. Let κ(s) := (δ/(1 + |w|)) tanh(s(1 + |w|)/δ). Then γ(s) := ψ(v_x + κ(s)w) is C¹ on ℝ, γ(ℝ) ⊆ ψ(V) ⊆ N, γ(0) = x and γ'(0) = Dψ(v_x)w.
 (b) Flatness of N at x. ψ|_V is a homeomorphism onto N ∩ W and Dψ(v_x) is injective. So for z ∈ N near x, z = ψ(v) with v near v_x, |v − v_x| ≤ C|z − x|, and dist(z − x, L) = o(|z − x|) as z → x.
 (c) Q ⊆ L. Suppose p ∈ Q ∖ L. Choose δ' > 0 with B_{3δ'}(p) ∩ L = ∅. By (b), for small λ > 0 every z ∈ N with (z − x)/λ ∈ B_{δ'}(p) has dist((z − x)/λ, L) < δ', which is impossible. So η_{x,λ}(N) ∩ B_{δ'}(p) = ∅, and η_{x,λ}(M_Z) ∩ B_{δ'}(p) ⊆ η_{x,λ}(M_Z ∖ N), an Hⁿ-null set.
 (d) Contradiction. Take f ∈ C_c(ℝ^P) with 0 ≤ f ≤ 1, f = 1 on B_{δ'/2}(p) and spt f ⊆ B_{δ'}(p). Then ∫_{η_{x,λ}(M_Z)} f dHⁿ = 0 for small λ, whereas its limit must be ∫_Q f dHⁿ ≥ Hⁿ(Q ∩ B_{δ'/2}(p)) > 0. Hence Q ⊆ L ⊆ tangentSpace N x.
4. π fixes Z. For Hⁿ-a.e. x ∈ M_Z ∩ G we have x ∈ N ∩ B_r(y) and π(x) = x. Write ξ_Z(x)(α) = ±α(τ) with τ an orthonormal basis of Q ⊆ tangentSpace N x. Then Dπ(x)τᵢ = τᵢ, so ξ_Z(x)(α∘Dπ(x)) = ξ_Z(x)(α) for every n-covector α. In particular ξ_Z(x)(ω(x)) = ξ_Z(x)(ω(π(x))∘Dπ(x)) for ω ∈ 𝒟ⁿ(U).
5. The projected cycle Q_π := π_#X. Define Q_π(ω) := ∫_{M_X∩F} θ_X ξ_X(ω(π(x))∘Dπ(x)) dHⁿ(x) for ω ∈ 𝒟ⁿ(U). This is Simon 2.24(2), 3.3–3.6 for the C¹ map π, which is proper on the compact F; μ_X is carried by F by 2(a).
 (a) Current. The integrand is Hⁿ⌞(M_X ∩ F)-a.e. strongly measurable, since x ↦ ω(π(x))∘Dπ(x) is continuous on B_r(y) ⊇ F. For Hⁿ-a.e. x ∈ M_X, ξ_X(x) is a unit orientation. So by (L1) and ‖Dπ‖ ≤ Λ on F, |ξ_X(x)(α∘Dπ(x))| ≤ ‖α‖Λⁿ. Hence |Q_π(ω)| ≤ Λⁿ·sup_x‖ω(x)‖·∫_{M_X∩F} θ_X dHⁿ, which is finite by 2(d). Q_π is linear. If ω_j → 0 in 𝒟ⁿ(U), then sup‖ω_j‖ → 0, so Q_π(ω_j) → 0. Thus Q_π is a GeometricCurrentOn U n.
 (b) Support. If ω ∈ 𝒟ⁿ(U) vanishes on K' = π(F), then Q_π(ω) = 0. Every z ∈ U ∖ K' has a ball B_s(z) whose closure is a compact subset of the open set U ∖ K'. Q_π vanishes on forms supported in B_s(z), so z lies in the zero region of Q_π. Hence spt Q_π ⊆ K'. As spt Q_π is relatively closed in U and contained in the compact K' ⊆ U, it is compact. It is contained in K' ⊆ (U ∩ N) ∩ G.
 (c) Integer multiplicity. We construct an IMRep R_Q = (C, N', ζ') in U representing Q_π. This is Simon 3.3–3.9 with the correction stated at the top.
  (c1) Set-up. Put M := M_X ∩ F and θ := θ_X. M is Borel and countably n-rectifiable, being a subset of M_X (SimonGMT CountablyRectifiable.mono). By 2(d), Hⁿ(M) ≤ ∫_M θ dHⁿ < ∞. Fix a Borel map ξ̃ : ℝ^P → Λ_n with ξ̃ = ξ_X Hⁿ-a.e. on M. Call x ∈ M oriented if T_xM exists and ξ̃(x) is a unit orientation of it. Hⁿ-a.e. x ∈ M is oriented: a.e. on M, T_xM_X exists and is oriented by ξ_X(x) = ξ̃(x) (IMRep), and tangent_locality with (A, B) = (M, M_X) gives T_xM = T_xM_X. Define the Borel function J(x) := |(∧ₙDπ(x))ξ̃(x)| on M. By (L4), at an oriented x, J(x) is the Jacobian J^M_π(x) of Simon Ch. 3, 2.3, and J(x) ≤ ‖Dπ(x)‖ⁿ ≤ Λⁿ. Let M₊ := {x ∈ M : J(x) > 0}, a Borel set. For x ∈ M ∖ M₊ the n-vector (∧ₙDπ(x))ξ̃(x) is 0, since its norm is 0.
  (c2) C¹ pieces on which π is injective. By Simon Ch. 3, Lemma 1.2 and Remark 1.3, M = ⋃_{j≥0} M_j disjointly, with M_j Borel, Hⁿ(M₀) = 0, and M_j ⊆ N_j for embedded C¹ n-submanifolds N_j (j ≥ 1). SimonGMT simon_remark_1_3 gives the disjoint Borel pieces: the N_j are Borel (SimonGMT measurableSet_of_isSimonSubmanifold), and a Borel null N₀ ⊇ M₀ exists because Hⁿ is Borel regular. By Remark 1.5(2), T_xM = T_xN_j for Hⁿ-a.e. x ∈ M_j.
   Let x₀ ∈ N_j ∩ B_{2ρ}(y) with Dπ(x₀) injective on T_{x₀}N_j. Take a C¹ parametrization φ of N_j near x₀, with φ(v₀) = x₀ and Dφ(v₀) an isomorphism onto T_{x₀}N_j. Then π∘φ is C¹ with injective derivative at v₀. By the inverse function theorem, in the form of the local immersion theorem (Simon Ch. 6, 3.4), there is an open set O ∋ x₀ with O ⊆ B_{2ρ}(y) such that:
   - π is injective on N_j ∩ O;
   - Σ := π(N_j ∩ O) is an embedded C¹ n-submanifold with Hⁿ(Σ) < ∞ (take N_j ∩ O = φ(V'') with V'' bounded, of compact closure in the domain of φ);
   - T_{π(z)}Σ = Dπ(z)(T_zN_j) for z ∈ N_j ∩ O.
   By Lindelöf's theorem, for each j countably many such O cover {x ∈ N_j ∩ B_{2ρ}(y) : Dπ(x) is injective on T_xN_j}. Enumerate all of them, over all j, as (j(k), O_k, Σ_k), k = 1, 2, …. Put A_k := (M₊ ∩ M_{j(k)} ∩ O_k) ∖ ⋃_{k'<k} A_{k'}; these are Borel and pairwise disjoint.
   Let x ∈ M₊ ∩ M_j (j ≥ 1) be oriented with T_xM = T_xN_j. Then Dπ(x) is injective on T_xN_j, by (L4) as J(x) > 0, and x ∈ F ⊆ B_{2ρ}(y); so x ∈ ⋃_k A_k. Hence Hⁿ(M₊ ∖ ⋃_k A_k) = 0. Moreover, π is injective on each A_k, π(A_k) ⊆ Σ_k, and Dπ(x)(T_xM) = T_{π(x)}Σ_k for Hⁿ-a.e. x ∈ A_k.
  (c3) Compact pieces and the image set. Hⁿ⌞M is a finite Borel measure on ℝ^P, hence inner regular. For each k choose compact sets K_{k,1}, K_{k,2}, … with K_{k,i} ⊆ A_k ∖ (K_{k,1} ∪ ⋯ ∪ K_{k,i−1}) and Hⁿ(A_k ∖ (K_{k,1} ∪ ⋯ ∪ K_{k,i})) < 2^{−i}. Enumerate all K_{k,i} as K₁, K₂, …; they are pairwise disjoint, with K_m ⊆ A_{k(m)}.
   Put M' := ⋃_m K_m ⊆ M₊, a Borel set with Hⁿ(M₊ ∖ M') = 0, and E := π(M') = ⋃_m π(K_m). Each π(K_m) is compact, so E is σ-compact, hence Borel. Also E ⊆ K' ⊆ G ⊆ U, E ⊆ ⋃_k Σ_k, and Hⁿ(E) ≤ ΛⁿHⁿ(M) < ∞ by 1(a). Since π|K_m is a continuous injection of a compact set, x_m := (π|K_m)⁻¹ : π(K_m) → K_m is continuous.
   Countable rectifiability: M ⊆ M₀'' ∪ ⋃_i F_i(ℝⁿ) with Hⁿ(M₀'') = 0 and F_i Lipschitz. So E ⊆ π̃(M) ⊆ π̃(M₀'') ∪ ⋃_i (π̃∘F_i)(ℝⁿ), where Hⁿ(π̃(M₀'')) = 0 by 1(d) and each π̃∘F_i is Lipschitz. Hence every subset of E is countably n-rectifiable.
   Call x ∈ M' good if x is oriented, x ∈ M_{j(k)} with T_xM = T_xN_{j(k)}, and Dπ(x)(T_xM) = T_{π(x)}Σ_k; here k := k(m) for the m with x ∈ K_m. By (c1) and (c2), Hⁿ(M' ∖ good) = 0.
  (c4) Area formula. Fix m. π is C¹, hence locally Lipschitz, on B_r(y) ⊇ K_m, and π is injective on K_m. By tangent_locality with (A, B) = (K_m, M), T_xK_m = T_xM for Hⁿ-a.e. x ∈ K_m; so the Jacobian J^{K_m}_π equals J Hⁿ-a.e. on K_m. Simon Ch. 3, 2.6 gives ∫_{K_m} hJ dHⁿ = ∫_{π(K_m)} h∘x_m dHⁿ for every Borel h ≥ 0. Sum over m, using monotone convergence (the K_m are disjoint and π is injective on each):
   (A) ∫_{M'} hJ dHⁿ = ∫ Σ_m 1_{π(K_m)}(w)·h(x_m(w)) dHⁿ(w) = ∫ Σ_{x∈π⁻¹(w)∩M'} h(x) dHⁿ(w).
   The integrand on the right is Borel. With h = θ, ∫ Σ_{x∈π⁻¹(w)∩M'} θ(x) dHⁿ(w) = ∫_{M'} θJ dHⁿ ≤ Λⁿ∫_M θ dHⁿ < ∞. So the Borel set E₁ := {w : Σ_{x∈π⁻¹(w)∩M'} θ(x) < ∞} satisfies Hⁿ(ℝ^P ∖ E₁) = 0. For w ∈ E₁ the fibre π⁻¹(w) ∩ M' is finite, as θ ≥ 1.
  (c5) The image integral. For x ∈ M' put ζ̂(x) := J(x)⁻¹(∧ₙDπ(x))ξ̃(x), and ζ̂(x) := 0 elsewhere. Then ζ̂ is Borel and |ζ̂(x)| = 1 on M'. By (L4), ζ̂(x) is a unit orientation of Dπ(x)(T_xM) at every good x.
   Define V(w) := Σ_{x∈π⁻¹(w)∩M'} θ(x)ζ̂(x) = Σ_m 1_{π(K_m)}(w)·θ(x_m(w))·ζ̂(x_m(w)) for w ∈ E₁, and V(w) := 0 for w ∉ E₁. The series converges absolutely on E₁, because |ζ̂(x)(dx^I)| ≤ 1. So each coordinate V(·)(dx^I) is Borel, and V is Borel.
   Let ω ∈ 𝒟ⁿ(U). For Hⁿ-a.e. x ∈ M we have ξ_X(x) = ξ̃(x), hence θ(x)ξ_X(x)(ω(π(x))∘Dπ(x)) = θ(x)((∧ₙDπ(x))ξ̃(x))(ω(π(x))). This is 0 on M ∖ M₊ by (c1), and equals θ(x)J(x)ζ̂(x)(ω(π(x))) on M'. By 2(a) and Hⁿ(M₊ ∖ M') = 0,
   Q_π(ω) = ∫_{M'} θ(x)J(x)ζ̂(x)(ω(π(x))) dHⁿ(x).
   Apply (A) to the positive and negative parts of h(x) := θ(x)ζ̂(x)(ω(π(x))). Both have finite integral against J, since |h| ≤ θ·sup_z|ω(z)|_E by (L2). On the fibre over w we have π(x) = w, so
   (B) Q_π(ω) = ∫ V(w)(ω(w)) dHⁿ(w).
  (c6) Tangent planes of the image. Fix k. Apply tangent_locality, with U := ℝ^P, to (A, B) = (E ∩ Σ_k, E) and to (A, B) = (E ∩ Σ_k, Σ_k). These sets are Borel (Σ_k is locally closed), and Hⁿ(E), Hⁿ(Σ_k) < ∞. The C¹ submanifold Σ_k has approximate tangent space T_wΣ_k at every w ∈ Σ_k, as in the proof of Simon Ch. 3, 1.6. So for Hⁿ-a.e. w ∈ E ∩ Σ_k, T_wE exists and equals T_wΣ_k.
   Let Bad_E be the union of three null sets: these countably many exceptional sets; ℝ^P ∖ E₁; and π(M' ∖ good), which is null by 1(a). Since E ⊆ ⋃_k Σ_k, for every w ∈ E ∖ Bad_E the approximate tangent space Π_w := T_wE exists, and Π_w = T_wΣ_k whenever w ∈ Σ_k.
  (c7) Integer multiplicity in the fibres (Simon 3.7–3.8). Let w ∈ E ∖ Bad_E, and fix a unit orientation ζ_w of Π_w. Every x ∈ π⁻¹(w) ∩ M' is good, since w ∉ π(M' ∖ good). If x ∈ K_m and k := k(m), then w = π(x) ∈ Σ_k, so Dπ(x)(T_xM) = T_wΣ_k = Π_w. By (c5) and (L3), ζ̂(x) = ε(x)ζ_w with ε(x) ∈ {1, −1}. Hence V(w) = m(w)ζ_w, where m(w) := Σ_{x∈π⁻¹(w)∩M'} ε(x)θ(x) ∈ ℤ is a finite sum (w ∈ E₁) and |m(w)| ≤ Σ_{x∈π⁻¹(w)∩M'} θ(x).
  (c8) Borel versions; restriction to positive multiplicity. Let ν(w) := |V(w)|, a Borel function. By (c7) and (L2), ν(w) = |m(w)| for w ∈ E ∖ Bad_E. Define:
   - the Borel function N' : ℝ^P → ℕ, N'(w) := ⌊ν(w) + 1/2⌋, so N'(w) = |m(w)| on E ∖ Bad_E;
   - the Borel map ζ' : ℝ^P → Λ_n, ζ'(w) := ν(w)⁻¹V(w) if ν(w) > 0, and ζ'(w) := 0 otherwise;
   - the carrier C := {w ∈ E : N'(w) ≥ 1}, a Borel set.
   For w ∈ C ∖ Bad_E: m(w) ≠ 0, ζ'(w) = sgn(m(w))ζ_w is a unit orientation of Π_w, and N'(w)ζ'(w) = m(w)ζ_w = V(w). For w ∈ E ∖ (C ∪ Bad_E): m(w) = N'(w) = 0, so V(w) = 0. Off E, V = 0. Hence V = 1_C·N'·ζ' Hⁿ-a.e. The points of E where Simon's multiplicity N = |m| vanishes are thus removed from the carrier.
  (c9) R_Q := (C, N', ζ') is an IMRep in U representing Q_π. We check each field.
   - measurableSet_carrier: C is Borel.
   - carrier_subset: C ⊆ E ⊆ U.
   - rectifiable: C ⊆ E is countably n-rectifiable by (c3).
   - measurable_mult: N' is Borel.
   - mult_pos: N' ≥ 1 on C, by the definition of C.
   - locallyIntegrable_mult: for compact K ⊆ U, ∫_{C∩K} N' dHⁿ ≤ ∫_{E∖Bad_E} |m| dHⁿ ≤ ∫ Σ_{x∈π⁻¹(w)∩M'} θ(x) dHⁿ(w) < ∞, by (c7) and (c4).
   - aestronglyMeasurable_orient: ζ' is Borel with values in the finite-dimensional space Λ_n, hence strongly measurable.
   - orients, on the smaller carrier: apply tangent_locality (U := ℝ^P) to (A, B) = (C, E). This is legitimate, as C ⊆ E are Borel and Hⁿ(E) < ∞. So for Hⁿ-a.e. w ∈ C, C and E have the same approximate tangent spaces at w. For such w outside Bad_E, T_wE = Π_w exists, hence T_wC = Π_w, and ζ'(w) is a unit orientation of Π_w by (c8). So for Hⁿ⌞C-a.e. w there is Q := Π_w with HasApproximateTangentSpaceAt n C w Q and IsUnitOrientationOf (ζ'(w)) Q.
   - Represents, with the action unchanged: for ω ∈ 𝒟ⁿ(U), the integrand N'ζ'(ω) is bounded by N'·sup|ω|_E, which is integrable on C. By (c8) and (B), ∫_C N'(w)ζ'(w)(ω(w)) dHⁿ(w) = ∫ V(w)(ω(w)) dHⁿ(w) = Q_π(ω).
   So Q_π is integer multiplicity.
 (d) ∂Q_π = 0. Fix r'' with t < r'' < 2ρ. Let η ∈ 𝒟^{n−1}(U), and fix χ ∈ C_c^∞(B_{r''}(y)) with χ = 1 near F. Let π_k := π * φ_{1/k} be standard mollifications; they only use the values of π on B_r(y). For large k they are smooth on a neighbourhood of B̄_{r''}(y), and π_k → π, Dπ_k → Dπ uniformly on B̄_{r''}(y), because π is C¹ on B_r(y) ⊋ B̄_{r''}(y). Then χπ_k^#η ∈ 𝒟^{n−1}(U), where (π_k^#η)(x) = η(π_k(x))∘Dπ_k(x), and d(χπ_k^#η) = dχ ∧ π_k^#η + χπ_k^#dη. Now ∂X = 0 gives X(d(χπ_k^#η)) = 0. Also X(dχ ∧ π_k^#η) = 0 by the vanishing hypothesis, since dχ = 0 near F. Hence X(χπ_k^#dη) = 0, i.e. ∫_{M_X∩F} θ_X ξ_X((dη)(π_k(x))∘Dπ_k(x)) dHⁿ = 0. As k → ∞ the integrands converge uniformly on F and are bounded by a constant multiple of θ_X. So Q_π(dη) = 0 by dominated convergence.
6. Competitor and minimality.
 (a) Let Z' := Z + Q_π ∈ 𝒟_n(U). It is integer multiplicity by int_combination, applied to RZ and the representation R_Q of 5(c) with (p₁, p₂) = (1, 1).
 (b) ∂Z' = ∂Z + ∂Q_π = ∂Z, i.e. SameBoundary Z' Z.
 (c) Z' − Z = Q_π, so spt(Z' − Z) = spt Q_π is a compact subset of (U ∩ N) ∩ G.
 (d) G is open and its closure B̄_{3ρ}(y) is a compact subset of U (CompactlyContained). Since Z is minimizing in U ∩ N, M_G(Z) ≤ M_G(Z').
7. Mass of the competitor. Let ω ∈ 𝒟ⁿ(U) with spt ω ⊆ G and |ω(x)|_E ≤ 1 for all x. Define the bounded Borel n-form φ(x) := ω(π(x))∘Dπ(x) for x ∈ G and φ(x) := 0 otherwise; it is supported in the compact Ḡ ⊆ U.
 (a) By step 4 and ω = 0 off G, Z(ω) = ∫_{M_Z} θ_Z ξ_Z(φ) dHⁿ.
 (b) By 2(a) and F ⊆ G, Q_π(ω) = ∫_{M_X} θ_X ξ_X(φ) dHⁿ.
 (c) Y = Z + X on 𝒟ⁿ(U). So the Λ_n-valued Radon measures θ_Yξ_YHⁿ⌞M_Y and θ_Zξ_ZHⁿ⌞M_Z + θ_Xξ_XHⁿ⌞M_X agree on smooth compactly supported forms. Smooth forms are uniformly dense in C_c(U; Λⁿ) (with supports in a fixed compact), and signed Radon measures are determined by C_c(U) (componentwise in the basis dx^I). Hence the two measures coincide and also agree on the bounded Borel form φ with compact support in U:
 Z'(ω) = Z(ω) + Q_π(ω) = ∫_{M_Y} θ_Y ξ_Y(φ) dHⁿ = ∫_{M_Y∩G} θ_Y ξ_Y(x)(ω(π(x))∘Dπ(x)) dHⁿ.
 (d) For Hⁿ-a.e. x ∈ M_Y, ξ_Y(x) = ±τ₁∧⋯∧τₙ with τ orthonormal. Then |ξ_Y(x)(α∘L)| = |α(Lτ₁, …, Lτₙ)| ≤ |α|_E |Lτ₁|⋯|Lτₙ| ≤ |α|_E ‖L‖ⁿ. This uses Cauchy–Binet (α(v) = Σ_I α(e_I) det[(v_j)_I]), Cauchy–Schwarz, and Σ_I det[(v_j)_I]² = det(vᵀv) ≤ Π|v_j|² (Hadamard).
 (e) For x ∈ G, ‖Dπ(x)‖ ≤ 1 + c|x − y| ≤ Λ and |ω(π(x))|_E ≤ 1. So Z'(ω) ≤ Λⁿ ∫_{M_Y∩G} θ_Y dHⁿ = Λⁿ μ_Y(G).
 Taking the supremum over such ω gives M_G(Z') ≤ Λⁿ μ_Y(G).
8. By steps 6, 7 and (C1): μ_Z(G) = M_G(Z) ≤ M_G(Z') ≤ Λⁿ μ_Y(G).
9. Splitting off G ∖ F. G ∖ F is open and contained in U ∖ F, so μ_Y(G ∖ F) = μ_Z(G ∖ F) by 2(c). All quantities are finite by 2(d). Since F ⊆ G,
 μ_Z(F) = μ_Z(G) − μ_Z(G ∖ F)
 ≤ Λⁿ μ_Y(G) − μ_Y(G ∖ F)
 = Λⁿ μ_Y(F) + (Λⁿ − 1) μ_Y(G ∖ F)
 = Λⁿ μ_Y(F) + (Λⁿ − 1) μ_Z(G ∖ F)
 ≤ Λⁿ μ_Y(F) + (Λⁿ − 1) μ_Z(G).
 With Λ = 1 + 3cρ and Λⁿ − 1 ≥ 0, this is the claim. ∎

## Key steps

1. π maps F = B̄_t(y) into N ∩ B_{3ρ}(y), since Lip(π|B̄_s) ≤ 1 + cs, π(y) = y and 4cρ ≤ 1; via (C1), μ_X is carried by F and μ_Z by N.
2. Approximate tangent planes of Z lie in T_xN (blow-up against a C² chart), so π_# fixes Z on G.
3. Q_π = π_#X is a current with compact support in N ∩ G. On disjoint compact pieces where π is injective (C¹ cover, local immersion), the area formula gives Q_π(ω) = ∫ V(ω) dHⁿ with V(w) = m(w)ζ_w, m(w) ∈ ℤ.
4. Borel versions N' = |m| and ζ' = V/|V| on the carrier C = {w : N'(w) ≥ 1} form an IMRep representing Q_π; tangent_locality gives the orientation on C, and the area formula its local integrability.
5. ∂Q_π = 0 by mollifying π; Z + Q_π is an admissible competitor, so M_G(Z) ≤ M_G(Z + Q_π).
6. Z + Q_π = π_#(Y⌞G) as vector measures, so M_G(Z + Q_π) ≤ (1 + 3cρ)ⁿμ_Y(G) by Hadamard; then subtract G ∖ F, where μ_Y = μ_Z.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical)`
- `rg -c sorry local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean (1, the final main_theorem)`
- `rg -l -i 'slice|slicing|flat metric|flat norm|deformation theorem|nearest.point|tubular' simongmt/Poincare/SimonGMT local-references/123e8435b4a2469b/project -t lean`
- `rg -n 'def .*[Pp]ushforward' simongmt/Poincare/SimonGMT -t lean`
- `rg -n -i 'theorem .*area.*rectifiable|rectifiable.*area_formula|areaFormula.*Rectifiable' simongmt/Poincare/SimonGMT -t lean (no match)`
- `grep -n '^theorem|^def' simongmt Chapter02/AreaNoninjective.lean, Chapter03/{SubmanifoldCover,DisjointCover,Rectifiable,Differential}.lean, Chapter06/{Currents,Mass,CurrentLocalEquality,Forms}.lean`
- `grep -n 'measure_compl_support|hausdorffMeasure_image_le|norm_image_sub_le_of_norm_fderiv_le|toOpenPartialHomeomorph|exists_isCompact_diff_lt' in snapshot mathlib Support.lean, Hausdorff.lean, MeanValue.lean, InverseFunctionTheorem/ContDiff.lean, Regular.lean`
- `grep -rln 'def compContinuousLinearMap' snapshot mathlib Topology/Algebra/Module/Alternating`
- `dag.json lean_name scan for the eight proposed dor_lmb_* names (164 nodes at 2026-10-12T01:39Z; no collision); git grep dor_lmb over all branches (no match)`
- `python3 -I: verifier/lean_contract.py validate_lean_statement and verifier/gmt-compare.py contract_scope on all eight lean_statement strings`
- `lake env lean /tmp/lmb-decomp-v2/Types.lean (eight child types in the exact comparator scope, each also checked as `example : Prop`)`
- `lake env lean /tmp/lmb-decomp-v2/Assembly.lean (#print axioms Submission.dor_minimizing_limsup_mass_bound)`
- `lake env lean /tmp/lmb-decomp-v2/Inst.lean (implicit volume on ℝ, Measure.le_iff', ENNReal smul of measures)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaNoninjective.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaLinear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/DisjointCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Product.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/DeformationIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1/decomposition-audit-v1.json`
- `/tmp/lmb-decomp-v2/v2_subproblems.json`
- `/tmp/lmb-decomp-v2/Types.lean`
- `/tmp/lmb-decomp-v2/Assembly.lean`
- `/tmp/lmb-decomp-v2/Inst.lean`

Snapshot: project b4d606d, mathlib 25730c7c; simongmt is pinned at 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. Its only sorry is main_theorem.

Reusable facts found:
- SimonGMT Chapter03/Rectifiable.lean: HasApproximateTangentSpaceAt (Simon 1.4, unweighted), .unique, CountablyRectifiable and CountablyRectifiable.mono.
- Chapter03/DisjointCover.lean: simon_remark_1_3 (disjoint Borel pieces).
- Chapter03/SubmanifoldCover.lean: countablyRectifiable_of_submanifold_cover, measurableSet_of_isSimonSubmanifold, countablyRectifiable_image_contDiffOn_open. Its header says the converse direction of Lemma 1.2 "remains a separate theorem".
- Chapter02/AreaNoninjective.lean: weighted_area_formula_lipschitz_fiberSum, a non-injective weighted Lipschitz area formula. It is for maps on a Euclidean domain, not on rectifiable subsets of ℝ^P.
- Chapter06: massOn and massAdmissibleOn (Mass.lean); support as U minus the zero region (CurrentLocalEquality.lean); GeometricCurrentOn with sequential continuity, and boundary (Currents.lean).
- Mathlib: measure_compl_support, LipschitzOnWith.hausdorffMeasure_image_le, Convex.norm_image_sub_le_of_norm_fderiv_le, ContDiffAt.toOpenPartialHomeomorph, MeasurableSet.exists_isCompact_diff_lt, ContinuousAlternatingMap.compContinuousLinearMap, μHE[d].

Not available, so cited from Simon in the child proofs:
- current slicing (6.4) and flat convergence (6.7.2): the keyword hits are only linear co-area slices, product point slices and varifold deformation slices;
- the Deformation Theorem (6.5.3) and completeness (6.3.13);
- C¹ or Lipschitz push-forward of currents: only affinePushforward and varifold push-forwards exist;
- the rectifiable-set area formula (Ch. 3, 2.6), the only-if direction of Lemma 1.2, and a nonlinear tubular-neighbourhood retraction.

Lean checks:
- All eight child types elaborate as Prop in the exact comparator scope and pass validate_lean_statement.
- The conditional assembly of the exact frozen parent type compiles. It depends only on propext, Classical.choice, Quot.sound and the stubs' sorryAx.
- No proposed name collides.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
