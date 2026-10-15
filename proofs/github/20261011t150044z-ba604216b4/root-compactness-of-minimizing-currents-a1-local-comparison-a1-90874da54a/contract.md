<!-- theorem-id: gmt-ch07/root.compactness_of_minimizing_currents-a1.local_comparison-a1 -->

## Theorem `Submission.cmc_local_comparison_inequality`

Let P, m ∈ ℕ, n := m + 1, U ⊆ ℝ^P open, and T_j (j ∈ ℕ), T ∈ 𝒟_n(U). Assume: (i) each T_j is minimizing in U (contract IsMinimizingIn T_j U: T_j is integer multiplicity and M_W(T_j) ≤ M_W(S') whenever W is open with closure(W) compact and contained in U, S' ∈ 𝒟_n(U) is integer multiplicity, ∂S' = ∂T_j, and spt(S' − T_j) is a compact subset of U ∩ W); (ii) sup_j (M_W(T_j) + M_W(∂T_j)) < ∞ for every open W with closure(W) compact and contained in U; (iii) T_j ⇀ T in U; (iv) T is integer multiplicity. Then for every compact K ⊆ U and every ε > 0 there exist an open set W with K ⊆ W ⊆ thickening(ε, K) := {x : |x − y| < ε for some y ∈ K} (Mathlib Metric.thickening ε K) and closure(W) compact and contained in U, a strictly increasing φ : ℕ → ℕ and numbers e_j ∈ [0, ∞] with e_j → 0, such that M_W(T_{φ(j)}) ≤ M_W(S) + e_j for every j ∈ ℕ and every integer multiplicity S ∈ 𝒟_n(U) with ∂S = ∂T and spt(S − T) ⊆ K.

Node: `root.compactness_of_minimizing_currents-a1.local_comparison-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/370

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/810, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4168, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4196, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4200, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4232, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4271

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4684, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1258, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4695, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4704, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4710, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4718, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1174, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4728

## Lean problem

Declaration: `Submission.cmc_local_comparison_inequality`

```lean
∀ (P m : ℕ) (U : Set (Euclid P)) (Ts : ℕ → GeometricCurrentOn U (m + 1)) (T : GeometricCurrentOn U (m + 1)), IsOpen U → (∀ j, IsMinimizingIn (Ts j) U) → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → ⨆ j, ((Ts j).massOn W + (Ts j).boundary.massOn W) < ∞) → WeaklyConvergesOn Ts T → IsIntegerMultiplicity T → ∀ (K : Set (Euclid P)) (ε : ℝ), IsCompact K → K ⊆ U → 0 < ε → ∃ W : Set (Euclid P), IsOpen W ∧ K ⊆ W ∧ W ⊆ thickening ε K ∧ CompactlyContained W U ∧ ∃ (φ : ℕ → ℕ) (e : ℕ → ℝ≥0∞), StrictMono φ ∧ Tendsto e atTop (𝓝 0) ∧ ∀ S : GeometricCurrentOn U (m + 1), IsIntegerMultiplicity S → S.boundary = T.boundary → (S - T).support ⊆ K → ∀ j, (Ts (φ j)).massOn W ≤ S.massOn W + e j
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

- Parent DAG node: `root.compactness_of_minimizing_currents-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.local_comparison-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon 7.2.4, proof of (1)–(11) (chapter-07.txt lines 176–258); these are steps 3–7 of the parent proof. Departures from the printed text are marked “Correction”.

Conventions. n = m + 1 ≥ 1; “W ⊂⊂ U” means W open with closure(W) compact and contained in U; M(A) := M_{ℝ^P}(A) = A.mass; IM means integer multiplicity; for currents X, Y in U, X + Y := X − (0 − Y) (contract Sub). For an IM current A ∈ 𝒟_d(U) with an IMRep R_A put μ_A := R_A.measure.

Sibling facts used.
(F1) [mass_equals_rep_measure] M_G(A) = μ_A(G) for every open G ⊆ ℝ^P (U open). Hence μ_A does not depend on the representation on open sets, hence (finite on compact subsets of U, outer regular) on Borel subsets of U; μ_A(ℝ^P ∖ U) = 0; M(A) = μ_A(ℝ^P); and for compact E ⊆ U, μ_A(E) = lim_{δ↓0} μ_A(E_δ), E_δ := {x : dist(x, E) < δ}.
(F2) [vanish_off_support] A(ω) = 0 whenever tsupport ω ∩ spt A = ∅. With (F1): μ_A(ℝ^P ∖ spt A) = μ_A(U ∖ spt A) = 0 (U ∖ spt A is open and every admissible form for M_{U∖spt A}(A) is killed).
(F3) (Simon 2.11, definitional) spt ∂A ⊆ spt A (∂A(ω) = A(dω), tsupport dω ⊆ tsupport ω); spt(A ± B) ⊆ spt A ∪ spt B; a support contained in a compact subset of U is compact (supports are relatively closed in U).
(F4) [im_calculus (c)] A − B (hence A + B and integer combinations) is IM if A, B are; and M_G(A ± B) ≤ M_G(A) + M_G(B) for open G (definition of M_G), so by (F1) μ_{A±B}(E) ≤ μ_A(E) + μ_B(E) for compact E ⊆ U (apply to E_δ, let δ ↓ 0).
(F5) [im_calculus (b)] For IM A and Borel B, A⌞B, represented by (M_A ∩ B, θ_A, ξ_A), is IM; (A⌞B)(ω) = A(ω) if ω vanishes outside B (in particular if B is open and tsupport ω ⊆ B); μ_{A⌞B} = μ_A⌞B; spt(A⌞B) ⊆ closure(B) ∩ U; M(A⌞B) = μ_A(B).
(F6) [flat_convergence] If T, T_j ∈ 𝒟_n(U) are IM, sup_j (M_G(T_j) + M_G(∂T_j)) < ∞ for G ⊂⊂ U and T_j ⇀ T, then for every G ⊂⊂ U there are IM R_j ∈ 𝒟_{n+1}(U), S_j ∈ 𝒟_n(U) with T − T_j − S_j = ∂R_j and M_G(R_j) + M_G(S_j) → 0.
(F7) [slicing] For a current R ∈ 𝒟_{n+1}(U) with representations (μ, ξ) of R and (μ', ξ') of ∂R and an L-Lipschitz f: the currents A_t = R⌞{f < t}, B_t = (∂R)⌞{f < t} (integrals over {f < t}), Z_t := ∂A_t − B_t, with Z_t(η) = 0 when tsupport η ∩ {f = t} = ∅, and ∫⁻_{(a,b)} M_G(Z_t) dt ≤ L μ(G ∩ {a < f < b}) and M_G(Z_t) ≤ L liminf_{h↓0} h⁻¹ μ(G ∩ {t − h < f < t}) for open G.
(F8) [closure_and_boundary_rectifiability (BR)] The boundary of an IM current in U with locally finite boundary mass is IM.
For an IMRep, |ξ(x)(α)| ≤ |α| Hᵈ-a.e. on the carrier (sibling im_calculus, conjunct (d)), so (R.measure, orient) is a representation in the sense of (F7), and for Borel B the current of (F7) built from it coincides with the IM restriction of (F5).

Dimension remark. If n > P, every n-covector on ℝ^P vanishes, so every n-current is 0; then the conclusion holds with W as constructed in steps 1–2 below (W := ∅ if K = ∅, W := W₀ otherwise), φ := id and e_j := 0. Otherwise (F6) applies in every codimension (including n = P, where (n+1)-currents vanish).

Proof.
1. (Trivial case.) If K = ∅, take W := ∅ (open, closure ∅ compact and contained in U, K ⊆ ∅ ⊆ thickening), φ := id and e_j := 0; only the zero form has support in ∅, so M_∅(T_j) = 0. Assume K ≠ ∅.
2. (Cut-off; lines 176–186.) Let d₀ := dist(K, ℝ^P ∖ U) ∈ (0, ∞] (d₀ := ∞ if U = ℝ^P) and δ := min(ε, d₀)/2, so 0 < δ < ε and C := {x : dist(x, K) ≤ δ} is a compact subset of U. Choose ψ ∈ C^∞(ℝ^P) with 0 ≤ ψ ≤ 1, ψ = 1 on K and tsupport ψ ⊆ {dist(·, K) < δ} (mollify the indicator of {dist(·, K) < δ/2} at scale δ/4). ψ is Lipschitz with constant L := sup|Dψ| < ∞. For 0 ≤ s < 1 put W_s := {ψ > s}: open, K ⊆ W_s ⊆ {dist(·, K) < δ} ⊆ thickening ε K, closure(W_s) ⊆ tsupport ψ ⊆ C, so W_s ⊂⊂ U. For 0 < s < 1: {ψ ≥ s} is a closed subset of tsupport ψ, hence compact; closure(W_s) ⊆ {ψ ≥ s}; {ψ ≥ s} ⊆ W_γ for 0 ≤ γ < s; ⋂_{0<γ<s} W_γ = {ψ ≥ s}; and {ψ = s} ∩ K = ∅.
3. (Flat convergence; (2), lines 187–191.) By hypothesis every T_j is minimizing, hence IM, T is IM, and the mass bounds and T_j ⇀ T hold; (F6) with G := W₀ gives IM R_j ∈ 𝒟_{n+1}(U), S_j ∈ 𝒟_n(U) with T − T_j − S_j = ∂R_j and M_{W₀}(R_j) + M_{W₀}(S_j) → 0.
4. (Slicing; (3)–(4), lines 192–201.) ∂R_j = T − T_j − S_j is IM (F4), so R_j and ∂R_j have IM representations whose measures μ_{R_j}, μ_{∂R_j} are finite on compact subsets of U (F1). Apply (F7) to R_j with f := −ψ (Lipschitz constant L) and t := −s, so that {f < t} = W_s: the currents A_t = R_j⌞W_s and B_t = (∂R_j)⌞W_s are the IM restrictions (F5), and
 P_{j,s} := ∂(R_j⌞W_s) − (∂R_j)⌞W_s
satisfies P_{j,s}(η) = 0 whenever tsupport η ∩ {ψ = s} = ∅, and, since {t − h < f < t} = {s < ψ < s + h},
 M_{W₀}(P_{j,s}) ≤ L liminf_{h↓0} h⁻¹ μ_{R_j}(W₀ ∩ {s < ψ < s + h}) for every s ∈ (0, 1).
(a) Localization of the mass of P_{j,s}: for s ∈ (0, 1) the closed set {ψ = s} is a compact subset of W₀. Choose χ ∈ C_c^∞(W₀; [0, 1]) with χ = 1 near {ψ = s}. For any open G and any ω admissible for M_G, (1 − χ)ω vanishes near {ψ = s}, so P_{j,s}(ω) = P_{j,s}(χω) ≤ M_{W₀}(P_{j,s}) (χω is admissible for M_{W₀}). Hence M_G(P_{j,s}) ≤ M_{W₀}(P_{j,s}) for every open G, in particular M(P_{j,s}) ≤ M_{W₀}(P_{j,s}).
(b) Integrality: if M_{W₀}(P_{j,s}) < ∞, then ∂(R_j⌞W_s) = (∂R_j)⌞W_s + P_{j,s} has locally finite mass (by (a) and μ_{∂R_j}(G) < ∞ for G ⊂⊂ U), R_j⌞W_s is IM (F5), so ∂(R_j⌞W_s) is IM by (F8) and P_{j,s} is IM by (F4), (F5); and spt P_{j,s} ⊆ {ψ = s} (vanishing property). Thus ∂(R_j⌞W_s) = (∂R_j)⌞W_s + P_{j,s}, Simon's (3).
Remark (not an erratum): Simon's spt P_j ⊆ ∂W_α also holds, but only spt P_j ⊆ {ψ = α} (⊇ ∂W_α) is used. The sign convention is that of Simon 4.6 with f = −ψ, which yields exactly (3).
5. (Choice of α and φ; (3)–(5), lines 192–205.) Let H_j(s) := μ_{R_j}(W₀ ∩ {s < ψ < 1}) for every s ∈ ℝ: a nonincreasing real function (finite, bounded by μ_{R_j}(W₀) = M_{W₀}(R_j) < ∞ since closure W₀ is a compact subset of U; F1). For 0 < h < 1 − s, {s < ψ < s + h} ⊆ {s < ψ < 1} ∖ {s + h < ψ < 1}, so μ_{R_j}(W₀ ∩ {s < ψ < s + h}) ≤ H_j(s) − H_j(s + h). By Lebesgue's theorem (Mathlib Monotone.ae_differentiableAt applied to −H_j) H_j is differentiable a.e., and at such s step 4 gives M_{W₀}(P_{j,s}) ≤ g_j(s) := −L H_j'(s). The functions g_j ≥ 0 are measurable (Mathlib measurable_deriv) and ∫_0^1 g_j ≤ L(H_j(0) − H_j(1)) ≤ L M_{W₀}(R_j) (Mathlib MonotoneOn.intervalIntegrable_deriv and MonotoneOn.intervalIntegral_deriv_mem_uIcc applied to the nondecreasing function −H_j). Since M_{W₀}(R_j) → 0 (step 3), Fatou's lemma gives ∫_0^1 liminf_j g_j ≤ liminf_j ∫_0^1 g_j = 0, so liminf_j g_j(s) = 0 for a.e. s. For each j, the level sets {ψ = s} (0 < s < 1) are pairwise disjoint subsets of the compact set tsupport ψ ⊆ U, on which μ_{T_j} is finite (F1), so μ_{T_j}({ψ = s}) > 0 for at most countably many s. Hence there is α ∈ (0, 1) such that: every H_j is differentiable at α (so M_{W₀}(P_{j,α}) ≤ g_j(α) < ∞ and step 4(b) applies at s = α for every j); liminf_j g_j(α) = 0; and μ_{T_j}({ψ = α}) = 0 for every j. Choose a strictly increasing φ : ℕ → ℕ with g_{φ(j)}(α) → 0; then M(P_{φ(j),α}) ≤ M_{W₀}(P_{φ(j),α}) → 0 by step 4(a). Let W := W_α; by step 2, W is open, K ⊆ W ⊆ thickening ε K, and W ⊂⊂ U.
Correction: Simon's (5) “M(T_j⌞∂W_α) = 0” is used in the form μ_{T_j}({ψ = α}) = 0; the condition on T is not needed.
6. (The decomposition; (6)–(7), lines 206–221.) Fix j and write T' := T_{φ(j)}, R := R_{φ(j)}, S'' := S_{φ(j)}, P := P_{φ(j),α}. Put R̃ := R⌞W and S̃ := S''⌞W − P; both are IM (F4), (F5), and ∂R̃ = (∂R)⌞W + P by step 4, which is IM. If ω ∈ 𝒟ⁿ(U) and tsupport ω ⊆ W, then R̃(dω) = R(dω) (F5, tsupport dω ⊆ W), (S''⌞W)(ω) = S''(ω), and P(ω) = 0 (tsupport ω ⊆ W is disjoint from {ψ = α}). Hence by step 3,
 (★) T(ω) = T'(ω) + ∂R̃(ω) + S̃(ω) for every ω ∈ 𝒟ⁿ(U) with tsupport ω ⊆ W,
which is Simon's (6) tested in W. Moreover M(S̃) ≤ M(S''⌞W) + M(P) = μ_{S''}(W) + M(P) ≤ M_{W₀}(S'') + M(P) (F1, F4, F5). Define e_j := M(S̃) + M(P) ∈ [0, ∞]; it depends only on j, and e_j ≤ M_{W₀}(S_{φ(j)}) + 2M(P_{φ(j),α}) → 0 by steps 3 and 5.
Correction: the printed formula reads S̃_j = S_j⌞W_α + P_j; with (3) the correct expression is S̃_j = S_j⌞W_α − P_j.
7. (The competitor; (9), lines 222–245.) Let S ∈ 𝒟_n(U) be IM with ∂S = ∂T and spt(S − T) ⊆ K. Then X := S − T is IM (F4), ∂X = 0 and spt X ⊆ K. Y := X + ∂R̃ is IM (F4), ∂Y = ∂X + ∂∂R̃ = 0, and spt Y ⊆ spt X ∪ spt R̃ ⊆ K ∪ closure(W) ⊆ {ψ ≥ α} (F3, F5; ψ = 1 on K). Let Z := T' + Y. Z is IM (F4), ∂Z = ∂T', and Z − T' = Y, so spt(Z − T') ⊆ {ψ ≥ α} is compact (F3) and contained in W_γ = U ∩ W_γ for every γ ∈ (0, α). Since W_γ ⊂⊂ U and T' is minimizing in U, M_{W_γ}(T') ≤ M_{W_γ}(Z), i.e. by (F1)
 (9) μ_{T'}(W_γ) ≤ μ_Z(W_γ) for every γ ∈ (0, α).
Correction: the printed text has “(9) … for γ > α” and then “letting γ ↓ 0”; since W_γ decreases as γ increases, the inclusion spt(Z − T') ⊆ W_γ holds for γ < α, and the limit to take is γ ↑ α.
8. (Letting γ ↑ α; (10), lines 246–252.) As γ ↑ α, W_γ decreases to {ψ ≥ α}, and μ_{T'}, μ_Z are finite on W₀ ⊆ C; by continuity from above, (9) gives μ_{T'}({ψ ≥ α}) ≤ μ_Z({ψ ≥ α}). The left side is ≥ μ_{T'}(W) = M_W(T'). Since {ψ ≥ α} is the disjoint union of W and {ψ = α}, the right side equals M_W(Z) + μ_Z({ψ = α}). The set {ψ = α} is a compact subset of U, so by (F4), μ_Z({ψ = α}) ≤ μ_{T'}({ψ = α}) + μ_X({ψ = α}) + μ_{∂R̃}({ψ = α}), where μ_{T'}({ψ = α}) = 0 by the choice of α; μ_X({ψ = α}) = 0 by (F2), since spt X ⊆ K and K ∩ {ψ = α} = ∅; and μ_{∂R̃}({ψ = α}) ≤ μ_{(∂R)⌞W}({ψ = α}) + μ_P({ψ = α}) ≤ 0 + M(P), because μ_{(∂R)⌞W} = μ_{∂R}⌞W vanishes on {ψ = α} ⊆ ℝ^P ∖ W (F5) and μ_P({ψ = α}) ≤ μ_P(ℝ^P) = M(P) (F1). Therefore
 (10) M_W(T') ≤ M_W(Z) + M(P).
9. (Conclusion; (11), lines 253–257.) For ω ∈ 𝒟ⁿ(U) with tsupport ω ⊆ W, (★) gives Z(ω) = T'(ω) + X(ω) + ∂R̃(ω) = (T(ω) − S̃(ω)) + (S(ω) − T(ω)) = S(ω) − S̃(ω). If ω is admissible for M_W (tsupport ω ⊆ W, |ω| ≤ 1), so is −ω, and −S̃(ω) = S̃(−ω) ≤ M_W(S̃) ≤ M(S̃); hence Z(ω) ≤ M_W(S) + M(S̃) and M_W(Z) ≤ M_W(S) + M(S̃). With (10):
 M_W(T_{φ(j)}) ≤ M_W(S) + M(S̃) + M(P) = M_W(S) + e_j.
W, φ and (e_j) were fixed in steps 5–6 before S was chosen, so this holds for every j and every S as in the statement, and e_j → 0. ∎

## Key steps

1. Cut-off ψ with ψ = 1 on K and tsupport ψ ⊆ {dist(·,K) < δ}, δ < min(ε, dist(K, ℝ^P∖U)); W_s := {ψ > s} ⊂⊂ U.
2. Flat convergence (sibling): T − T_j − S_j = ∂R_j with IM R_j, S_j and M_{W₀}(R_j) + M_{W₀}(S_j) → 0.
3. Slicing (sibling) by −ψ with monotone majorants and Fatou: a level α and a subsequence φ with ∂(R_j⌞W_α) = (∂R_j)⌞W_α + P_j, P_j IM by (BR), spt P_j ⊆ {ψ = α}, M(P_j) → 0 and μ_{T_j}({ψ = α}) = 0.
4. For S as in the statement, Z_j := T_j + (S − T) + ∂(R_j⌞W_α) is an IM competitor with spt(Z_j − T_j) ⊆ {ψ ≥ α} ⊂ W_γ (γ < α); minimality and γ ↑ α give M_{W_α}(T_j) ≤ M_{W_α}(Z_j) + M(P_j).
5. On W_α, Z_j = S − S̃_j with S̃_j := S_j⌞W_α − P_j, so M_{W_α}(T_j) ≤ M_{W_α}(S) + e_j with e_j := M(S̃_j) + M(P_j) → 0 independent of S.

## Reference use

### local-project

Queries:
- `cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; cmp GMT/Ch07/Contract.lean .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `rg -n 'cmc_|dtc_vanish_off_support' local-references/123e8435b4a2469b/project (no match); rg -c sorry local-references/123e8435b4a2469b/project/GMT -g '*.lean'`
- `rg -n -i 'federer.?fleming|deformation theorem|flat norm' local-references/123e8435b4a2469b/mathlib/Mathlib -g '*.lean' (no match); rg -n 'theorem eLpNorm_le_eLpNorm_fderiv_one|theorem tendsto_measure_thickening_of_isClosed' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -n -i 'federer|deformation|flat (norm|metric|convergence)|slice|slicing|closure theorem|boundary rectifiab' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06`
- `python3 scan of dag.json: lean_name, lean_statement, status and children of all 451 nodes; collisions of the twelve proposed names; accepted nodes with matching types (dtc_vanish_off_support, dor_ims_massOn_le_measure, dor_ims_measure_le_massOn, regcomp_approx_tangent_locality, regcomp_covector_eval_orthonormal_le, rsdic_unitOrientation_eq_or_eq_neg, dtc_isIntegerMultiplicity_sub); cross-branch reuse edges`
- `grep compactness_of_minimizing cluster-state/logs/gmt-ch07/*.log; comparison of swarm-configs/3cda86c657b24789a5e2370499838a03.json and e19a0116cbcc4eccb5496520b27c492f.json (max_nodes 200 vs 1000); node-directory timestamps at the v3 and v4 audit times`
- `sed -n 1300,1700p and 1801,2000p /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py; grep -n 'def _existing_lean_name_problem' -A 40 runtime.py; grep -n 'def ensure' -A 35 store.py`
- `grep for declarations simon_theorem_4_14_caratheodory, simon_theorem_4_14_positive_envelope, vectorFunctionalEnvelopeMeasure_isRadon, radonCaratheodoryMeasure_apply, integral_radonCaratheodoryMeasure, IsLocallyBoundedCcFunctional, simon_theorem_4_16_compact_metrizable, simon_theorem_3_6, simon_remark_3_7_hausdorff, simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure, simonHausdorffMeasureReal_toOuterMeasure, simon_theorem_3_3, simon_theorem_3_26_i, exists_isClosed_continuousOn_of_measurable, area_image_criticalSet_eq_zero, injective_area_formula_lipschitzOn, weighted_area_formula_lipschitzOn_fiberSum, exteriorDerivativeOn_pullbackFormWithin, countablyRectifiable_of_measure_zero, HasApproximateTangentSpaceAt.unique, WeaklyConvergesOn.boundary, WeaklyConvergesOn.massOn_le_liminf, affinePushforward in lake-packages-25730c7c/simongmt/Poincare`
- `grep for declarations Monotone.ae_differentiableAt, measurable_deriv, MonotoneOn.intervalIntegrable_deriv, MonotoneOn.intervalIntegral_deriv_mem_uIcc, LipschitzWith.ae_differentiableAt, LipschitzOnWith.hausdorffMeasure_image_le, exists_partition_approximatesLinearOn_of_hasFDerivWithinAt, LinearMap.exists_antilipschitzWith, MeasurableSet.image_of_continuousOn_injOn, LipschitzOnWith.extend_real, LipschitzOnWith.extend_pi, Besicovitch.exists_disjoint_closedBall_covering_ae, VitaliFamily.ae_tendsto_average_norm_sub, isMulLeftInvariant_eq_smul, tendstoUniformlyOn_of_ae_tendsto, LipschitzWith.integral_lineDeriv_mul_eq, eLpNorm_le_eLpNorm_fderiv_one, euclideanHausdorffMeasure_zero, hausdorffMeasure_smul₀, tendsto_measure_thickening_of_isClosed, countable_meas_level_set_pos, Integrable.integral_eq_integral_meas_lt, SmoothPartitionOfUnity.exists_isSubordinate, exists_contDiff_tsupport_subset, ContDiffBump.normed, AlternatingMap.map_linearDependent, Vitali.exists_disjoint_subfamily_covering_enlargement, RealRMK.rieszMeasure, ext_of_generate_finite, ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable, hausdorffMeasure_zero_singleton, Besicovitch.tendsto_filterAt in lake-packages-25730c7c/mathlib/Mathlib`
- `lake env lean /tmp/cmc-a5/lean/TypesFinal.lean; lake env lean /tmp/cmc-a5/lean/AssemblyFinal.lean; lake env lean /tmp/cmc-a5/lean/Inst.lean; lake env lean /tmp/cmc-a5/lean/Names.lean; lake env lean /tmp/cmc-a5/lean/Names2.lean`
- `git -C lake-packages-25730c7c/simongmt rev-parse HEAD; git -C lake-packages-25730c7c/mathlib rev-parse HEAD`
- `sed -n 176,260p book/chapter-07.txt`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Metric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1/decomposition-v4.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1/decomposition-audit-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1/decomposition-audit-v4.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1/decomposition-review-receipt-v4.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/swarm-configs/3cda86c657b24789a5e2370499838a03.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/swarm-configs/e19a0116cbcc4eccb5496520b27c492f.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/cluster-state/logs/gmt-ch07/3cda86c657b24789a5e2370499838a03.log`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/cluster-state/logs/gmt-ch07/e19a0116cbcc4eccb5496520b27c492f.log`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/store.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/GeometricPointProduct.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonPolarRepresentation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/VectorFunctionalEnvelope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonCaratheodoryIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/CompactMetrizableCompactness.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/HausdorffDensityBounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLiteral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Measure/Haar/Unique.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/cmc-a5/final.json`
- `/tmp/cmc-a5/scripts/build_final.py`
- `/tmp/cmc-a5/scripts/gen_types_final.py`
- `/tmp/cmc-a5/scripts/gen_assembly.py`
- `/tmp/cmc-a5/scripts/body.lean`
- `/tmp/cmc-a5/lean/TypesFinal.lean`
- `/tmp/cmc-a5/lean/AssemblyFinal.lean`
- `/tmp/cmc-a5/lean/Inst.lean`
- `/tmp/cmc-a5/lean/Names.lean`
- `/tmp/cmc-a5/lean/Names2.lean`

The snapshot contract (manifest: project b4d606db, mathlib 25730c7c) is byte-identical to the workspace Contract.lean and Submission.lean, and each snapshot chapter contract has only its frozen final sorry; the pinned packages are SimonGMT 2b366308 and Mathlib 25730c7c. SimonGMT Chapter06 says Federer–Fleming compactness remains a separate obligation and contains only point slices of products. Neither SimonGMT nor the snapshot Mathlib has a closure, deformation, Lipschitz-slicing or flat-convergence theorem (rg: no match). These results, Riesz representation and absolute continuity of normal currents, and IM calculus therefore remain children with complete parent-written proofs. Reusable library facts: WeaklyConvergesOn.massOn_le_liminf and WeaklyConvergesOn.boundary, the Chapter01 Riesz, compactness, density and Lusin theorems, the Chapter02 area formulas and the Chapter03 rectifiability API. Every SimonGMT and Mathlib declaration cited by name in the child proofs exists in the pinned sources. The 451-node DAG contains no cmc_ name, and the snapshot project has no cmc_ or dtc_ name. dtc_vanish_off_support is a comparator-accepted node whose frozen type equals the vanish_off_support child type, so it is reused verbatim; accepted declarations covering parts of mass_equals_rep_measure and im_calculus are named in remarks. In the workspace build, all 12 exact child types elaborate after import GMT.Ch07.Submission. The conditional assembly of CompactnessOfMinimizingCurrents from the six used child types depends only on propext, Classical.choice and Quot.sound, and current subtraction uses the contract instance. The identical previously accepted split was dropped only by the runtime node bound (max_nodes = 200 with about 200 DAG nodes); the current configuration allows 1000 nodes. Book lines 176–260 confirm the two corrections used in local_comparison.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
