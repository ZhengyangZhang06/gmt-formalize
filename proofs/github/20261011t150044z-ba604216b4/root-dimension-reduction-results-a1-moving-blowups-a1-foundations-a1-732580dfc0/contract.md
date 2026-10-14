<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.moving_blowups-a1.foundations-a1 -->

## Theorem `Submission.dimred_mbl_current_foundations`

Two facts about currents in open subsets of ℝ^P (P, n ∈ ℕ arbitrary in each part), forming one conjunction. (REP) Let P, n ∈ ℕ, U ⊆ ℝ^P open and T ∈ 𝒟_n(U) a current (SimonGMT GeometricCurrentOn U n) with M_W(T) < ∞ for every open W with closure(W) compact and contained in U. Then there are a Borel measure μ on ℝ^P and a map ξ from ℝ^P to n-vectors (continuous linear functionals on n-covectors) such that: μ(ℝ^P ∖ U) = 0; μ(K) < ∞ for every compact K ⊆ U; M_W(T) = μ(W) for every open W ⊆ ℝ^P; ξ is μ-a.e. strongly measurable; |ξ(x)(α)| ≤ |α| for every x and every n-covector α, where |α| is the Euclidean coefficient norm (covectorEuclideanNorm); T(ω) = ∫ ξ(x)(ω(x)) dμ(x) for every ω ∈ 𝒟ⁿ(U); and, if in addition M_W(∂T) < ∞ for every such W (boundaryMassOn, read as 0 when n = 0), then μ(E) = 0 for every set E ⊆ ℝ^P with Hⁿ(E) = 0 (Hⁿ = μHE[n]). (IMC) (a) Let P, n ∈ ℕ, U ⊆ ℝ^P open and M ⊆ M' ⊆ U Borel sets with Hⁿ(M' ∩ K) < ∞ for every compact K ⊆ U (Hⁿ = μHE[n]). Then for Hⁿ-a.e. x ∈ M and every linear subspace Q, M has approximate tangent space Q at x (SimonGMT HasApproximateTangentSpaceAt n M x Q, Simon Ch. 3, 1.4) if and only if M' does. (b) If U ⊆ ℝ^P is open, R = (M, θ, ξ) is an IMRep in U (contract structure) and E is Borel, then (M ∩ E, θ, ξ) is an IMRep in U and it represents some current in 𝒟_n(U). (c) If U is open and A, B ∈ 𝒟_n(U) are integer multiplicity (contract IsIntegerMultiplicity), then so is A − B. (d) For every IMRep R in any U, for Hⁿ-a.e. x ∈ R.carrier, |R.orient(x)(α)| ≤ |α| for every n-covector α (|·| the Euclidean coefficient norm).

Node: `root.dimension_reduction_results-a1.moving_blowups-a1.foundations-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1022

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4196, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4607, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4614, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2392, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1319, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5589, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5601, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5622, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5639, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5651, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5662, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5671

## Lean problem

Declaration: `Submission.dimred_mbl_current_foundations`

```lean
(∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) ∧ ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α))
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
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.foundations-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon 6.2.7–2.8, 2.35–2.37 (REP; BV theorem 2.35 replaced by Lemma TD, step 8); 3.1.5(2), 3.1.6, 6.2.6, 6.2.9, 6.3.2(1) (IMC).
Part (REP).
Notation. 𝒟ⁿ(U):=TestFormOn U n; 𝕀:={increasing I=(i_1<⋯<i_n) in {1,…,P}}, e_I:=(e_{i_1},…,e_{i_n}), H:=EuclideanSpace ℝ 𝕀. For n-covectors α, |α| := covectorEuclideanNorm α = (Σ_Iα(e_I)²)^{1/2} = ‖c(α)‖_H, where c(α):=(α(e_I))_{I∈𝕀} is a linear isomorphism onto H (injective: alternating forms are determined on increasing basis tuples; surjective: the alternating dx^I(v_1,…,v_n):=det((v_j)^{i_k})_{k,j} has dx^I(e_J)=δ_{IJ}); α=Σ_Iα(e_I)dx^I. If n>P, 𝕀=∅ and n-covectors vanish (n>P vectors are dependent). |ω|_∞:=sup_x|ω(x)|. n-vectors (MultiVector P n) are continuous linear functionals ζ on n-covectors, ⟨α,ζ⟩:=ζ(α).
(E1) If ω∈𝒟ⁿ(U), tsupport ω⊆W, W open, W⊂⊂U, then |T(ω)|≤|ω|_∞M_W(T) (ω=0 if |ω|_∞=0, else ±ω/|ω|_∞ are admissible: massAdmissibleOn).
(E2) |β∧γ|≤|β||γ| (β a 1-, γ a k-covector) and |p_α^#γ|=|γ| (p_α : ℝ^P→ℝⁿ, x↦(x^{i_1},…,x^{i_n}), γ a k-covector on ℝⁿ): k!|γ|²=Σ_{i_1,…,i_k}γ(e_{i_1},…,e_{i_k})² (repeated indices vanish; each increasing tuple occurs k! times up to sign) is the basis-independent Hilbert–Schmidt norm of γ, so |·| is invariant under orthogonal coordinate changes; rotating to β=|β|e¹, β∧γ=|β|Σ_{I∌1}γ_Ie¹∧e^I has norm |β|(Σ_{I∌1}γ_I²)^{1/2}≤|β||γ|; p_α^# maps the orthonormal basis e^J of ℝⁿ to the orthonormal e^{α(J)}.
1. If n>P, test forms vanish, T=0, M_W(T)=0, and μ:=0, ξ:=0 satisfy all assertions. Let n≤P.
2. (Extension.) X:=U (open in ℝ^P, so locally compact Hausdorff, second countable). For g∈C_c(X,H) let g̃:=c⁻¹∘g on U, 0 off U (continuous, spt g⊆U compact). Fix compact C⊇spt g in U and open W⊇C, W⊂⊂U (e.g. W:=thickening δ C, 2δ<infDist(C,ℝ^P∖U), δ:=1 if U=ℝ^P; if C=∅, g=0 and L(g):=0). With a standard mollifier φ_σ (C^∞, ≥0, ∫φ_σ=1, support in B̄_σ) and 0<σ<dist(C,ℝ^P∖W), g_σ:=g̃∗φ_σ (componentwise) is C^∞ with tsupport in C+B̄_σ⊆W, so g_σ∈𝒟ⁿ(U); g_σ→g̃ uniformly (uniform continuity), |g_σ|≤|g̃|_∞ (convexity of the norm). By (E1) |T(g_σ)−T(g_τ)|≤|g_σ−g_τ|_∞M_W(T)→0, so L(g):=lim_{σ↓0}T(g_σ) exists; it is independent of the mollifier and of C, W, as h_k, h'_k∈𝒟ⁿ(U) supported in a fixed open W'⊂⊂U with h_k, h'_k→g̃ uniformly have |T(h_k)−T(h'_k)|≤|h_k−h'_k|_∞M_{W'}(T)→0 (E1), and a union of two open sets ⊂⊂U is ⊂⊂U. Hence (a) L is linear; (b) L(ω|_U)=T(ω) for ω∈𝒟ⁿ(U) (constant sequence); (c) |L(g)|≤sup‖g‖_H·M_W(T) if spt g⊆W⊂⊂U, W open. So L is locally bounded (IsLocallyBoundedCcFunctional: for compact C⊆X apply (c) with open W⊇C, W⊂⊂U).
3. (Riesz.) simon_theorem_4_14_caratheodory (H finite-dimensional, so separable; L locally bounded) yields the Radon measure μ₀:=vectorFunctionalEnvelopeMeasure L on X and ν : X→H, measurable for the Carathéodory σ-algebra of μ₀, with ‖ν‖=1 μ₀-a.e. and L(g)=∫⟨g,ν⟩_H dμ₀ for g∈C_c(X,H); simon_theorem_4_14_positive_envelope yields, for f∈C_c(X,ℝ_{≥0}),
 (3a) sup{L(g) : g∈C_c(X,H), ‖g‖≤f} = ∫f dμ₀.
As μ₀ is σ-finite (X σ-compact), Carathéodory-measurable sets are μ₀-null-measurable (radonCaratheodoryMeasure μ₀ has the null sets of μ₀ and equals μ₀ on Borel sets), so ν=ν_B μ₀-a.e. with ν_B Borel, L(g)=∫⟨g,ν_B⟩dμ₀; set ν_B:=0 on the Borel null set {‖ν_B‖≠1}, so ‖ν_B‖≤1 everywhere.
4. μ:=push-forward of μ₀ under U ↪ ℝ^P: Borel, μ(ℝ^P∖U)=0, μ(C)=μ₀(C)<∞ for compact C⊆U. ξ(x)(α):=⟨c(α),ν_B(x)⟩_H for x∈U, ξ:=0 off U, is Borel (finite-dimensional target), so a.e. strongly measurable, and |ξ(x)(α)|≤‖c(α)‖‖ν_B(x)‖≤|α| (Cauchy–Schwarz); so |ξ(x)(ω(x))|≤|ω(x)|. For ω∈𝒟ⁿ(U), by 2(b) and 3, T(ω)=L(ω|_U)=∫_U⟨c(ω),ν_B⟩dμ₀=∫ξ(x)(ω(x))dμ(x), the integrand being bounded by the μ-integrable |ω|_∞1_{tsupport ω}.
5. (M_W(T)=μ(W), W open.) ≤: for ω admissible for M_W(T) (tsupport ω⊆W, |ω|≤1), ξ(ω)≤1_{tsupport ω}, so T(ω)≤μ(tsupport ω)<∞, ofReal T(ω)≤μ(W); take the sup. ≥: μ(W)=μ₀(W∩U)=sup{μ₀(C) : C⊆W∩U compact} (inner regularity). Fix such C, ε>0, f∈C_c(X,[0,1]) with f=1 on C, spt f⊆W∩U (Urysohn), and by (3a) g with ‖g‖≤f, L(g) ≥ ∫f dμ₀ − ε ≥ μ₀(C)−ε. Mollifying as in step 2 with σ<dist(spt f,ℝ^P∖(W∩U)): g_σ∈𝒟ⁿ(U), tsupport g_σ⊆W∩U, |g_σ|≤1, T(g_σ)→L(g); for small σ, g_σ is admissible with T(g_σ)≥μ₀(C)−2ε. So M_W(T)≥μ(W) (both may be ∞).
6. (U1) Finite signed Borel measures κ, κ' on an open G with ∫b dκ=∫b dκ' for all b∈C_c^∞(G) agree on Borel subsets of G: for compact C⊆G, smooth 0≤b_k≤1, b_k ↓ 1_C, supported in a fixed compact subset of G, give κ(C)=κ'(C) (dominated convergence); compact sets form a π-system generating the Borel sets; κ, κ' are finite.
Last assertion. Assume M_W(∂T)<∞ (boundaryMassOn) for open W⊂⊂U. If n=0, μHE[0]=μH[0] is counting measure, so μHE[0](E)=0 forces E=∅. If n>P, μ=0 (step 1). Let 1≤n≤P, Hⁿ:=μHE[n].
7. Let Hⁿ(E)=0; by Borel regularity take Borel E'⊇E, Hⁿ(E')=0, and replace E by E'∩U (μ(ℝ^P∖U)=0). μ is inner regular on Borel sets (locally finite on the σ-compact Polish space U, 0 off U), so it suffices that μ(C)=0 for compact C⊆U with Hⁿ(C)=0. Fix such C and open W⊇C, W⊂⊂U (step 2): μ(W)=M_W(T)<∞, M_W(∂T)<∞.
8. (Lemma TD.) Let n≥1, m a finite signed Borel measure on ℝⁿ with compact support, Λ:=sup{|∫div g dm| : g∈C_c^∞(ℝⁿ;ℝⁿ), |g|≤1}<∞. Then |m|(N)=0 if Lⁿ(N)=0.
Proof. u_σ(y):=∫φ_σ(y−z)dm(z) (φ_σ a mollifier on ℝⁿ) is C^∞, supported in spt m+B̄_σ, with ∂_ju_σ(y)=∫∂_jφ_σ(y−z)dm(z) (differentiation under the integral, m finite). For g∈C_c^∞(ℝⁿ;ℝⁿ), by Fubini ∫∇u_σ·g dy = ∫∫∇φ_σ(y−z)·g(y)dy dm(z) = −∫div(φ̌_σ∗g)dm, where (φ̌_σ∗g)(z):=∫φ_σ(y−z)g(y)dy is C_c^∞ with |φ̌_σ∗g|≤1 if |g|≤1; so |∫∇u_σ·g|≤Λ, whence, ∇u_σ being C_c^∞, ∫|∇u_σ|≤Λ (test g_k:=χ_k∇u_σ/(|∇u_σ|²+1/k)^{1/2}, smooth cut-offs χ_k ↑ 1, |g_k|≤1; monotone convergence). If n≥2, Gagliardo–Nirenberg–Sobolev (Mathlib eLpNorm_le_eLpNorm_fderiv_one, p=n/(n−1) conjugate to finrank ℝⁿ=n, ‖fderiv u_σ‖=|∇u_σ|) gives ‖u_σ‖_{L^{n/(n−1)}}≤C_nΛ; if n=1, u_σ(y)=∫_{−∞}^yu_σ' gives sup|u_σ|≤Λ. For a∈C_c^∞(ℝⁿ), by Fubini ∫u_σa dy = ∫(φ̌_σ∗a)dm → ∫a dm as σ ↓ 0 (φ̌_σ∗a→a uniformly, |m| finite), so by Hölder |∫a dm|≤C_nΛ‖a‖_{L^n}, resp. Λ‖a‖_{L¹} (n=1). For open G, |m|(G)=sup{∫a dm : a∈C_c^∞(G), |a|≤1} (Hahn decomposition S₊∪S₋, inner regularity of |m| on G, smooth approximation of 1_{S₊∩C}−1_{S₋∩C} for compact C, dominated convergence), so |m|(G)≤C_nΛLⁿ(G)^{1/n}, resp. ΛL¹(G). Outer regularity of Lⁿ gives open G⊇N of arbitrarily small measure, so |m|(N)=0.
9. (Projection; Simon 2.36.) For α=(i_1<⋯<i_n)∈𝕀 let p_α be as in (E2), dx^α:=dx^{i_1}∧⋯∧dx^{i_n}. p_α is 1-Lipschitz, so Hⁿ(p_α(C))≤Hⁿ(C)=0, and Hⁿ=Lⁿ on ℝⁿ (μHE[n] on EuclideanSpace ℝ (Fin n) is volume): N_α:=p_α(C) is compact, Lⁿ-null. dλ_α:=⟨dx^α,ξ⟩dμ⌞W is a finite signed Borel measure on W (|⟨dx^α,ξ⟩|≤|dx^α|=1, μ(W)<∞); for b∈C_c^∞(W), m_{α,b}:=(p_α)_*(bλ_α) is finite, supported in the compact p_α(spt b). For g∈C_c^∞(ℝⁿ;ℝⁿ), γ:=Σ_jg_jε_j with ε_j:=(−1)^{j−1}dy¹∧⋯∧dy^{j−1}∧dy^{j+1}∧⋯∧dyⁿ has dγ=(div g)dy, |γ(y)|=|g(y)|, p_α^#((div g)dy)=d(p_α^#γ); so step 4 for the test form b·p_α^#((div g)dy) (support in spt b⊆W) gives
 ∫div g dm_{α,b} = ∫b(x)(div g)(p_αx)⟨dx^α,ξ(x)⟩dμ(x) = T(b·d(p_α^#γ)) = T(d(bp_α^#γ)) − T(db∧p_α^#γ) = ∂T(bp_α^#γ) − T(db∧p_α^#γ),
of absolute value ≤ |b|_∞M_W(∂T)+|db|_∞M_W(T)<∞ if |g|≤1, by (E1), (E2) (|p_α^#γ|=|γ|≤1, |db∧p_α^#γ|≤|db|). By step 8, |m_{α,b}|(N_α)=0, i.e. ∫_{p_α⁻¹(N_α)}b dλ_α = m_{α,b}(N_α) = 0 for all b∈C_c^∞(W). (U1) for 1_{p_α⁻¹(N_α)}λ_α and 0 on W gives λ_α(B∩p_α⁻¹(N_α))=0 for Borel B⊆W; as C⊆p_α⁻¹(N_α), ∫_Ch dλ_α=0 for bounded Borel h on W.
10. For ω admissible for M_W(T), ω=Σ_{α∈𝕀}ω_αdx^α with ω_α∈C_c^∞(W); by steps 4, 9 (h:=ω_α) and |ξ(ω)|≤|ω|≤1,
 T(ω) = Σ_α∫ω_αdλ_α = Σ_α∫_Cω_αdλ_α + ∫_{W∖C}ξ(ω)dμ = ∫_{W∖C}ξ(ω)dμ ≤ μ(W∖C).
Taking the sup, μ(W)=M_W(T)≤μ(W∖C)<∞ gives μ(C)=0, so μ(E)=0 (step 7).
Part (IMC). Hⁿ:=μHE[n]; IMReps are written (carrier, mult, orient)=(M,θ,ξ); η_{x,r}(y):=r⁻¹(y−x) (blowUpMap); 𝒯(N,x,Q):=HasApproximateTangentSpaceAt n N x Q; 𝒰(ζ,Q):=IsUnitOrientationOf ζ Q.
(P0) SimonGMT's density theorems use simonHausdorffOuterMeasureReal n=μHE[n] (n∈ℕ), so null sets, finiteness and densities transfer; Hⁿ is Borel regular.
(P1) Hⁿ(η_{x,r}(A))=r^{−n}Hⁿ(A) for all A (scaling, isometry invariance), so ∫_{η_{x,r}(A)}f dHⁿ=r^{−n}∫_Af∘η_{x,r}dHⁿ for Borel A, bounded Borel f.
(P2) (simon_theorem_3_6 with (P0)) If D is Borel, Hⁿ(D)<∞, then Hⁿ(D∩B̄_r(x))/(ω_nrⁿ)→0 as r ↓ 0 for Hⁿ-a.e. x∉D.
(P3) (Cauchy–Binet) det(ABᵀ)=Σ_{I∈𝕀}det(A_I)det(B_I) for n×P matrices A, B (A_I: columns I of A): expanding det(ABᵀ) multilinearly in its columns Σ_kB_{jk}A_{·k}, terms with a repeated index vanish, and grouping the rest by the increasing rearrangement I (k=I∘σ) gives Σ_Idet(A_I)Σ_σsgn(σ)Π_jB_{j,I_{σ(j)}}=Σ_Idet(A_I)det(B_I). (n>P: 𝕀=∅, rank ABᵀ<n.)
(P4) If τ_1,…,τ_n are orthonormal and ⟨α,ζ⟩=±α(τ) for all n-covectors α, then |⟨α,ζ⟩|≤|α|: with A_{ik}:=⟨τ_i,e_k⟩, α(τ)=Σ_Idet(A_I)α(e_I) (multilinear, alternating), so by Cauchy–Schwarz and (P3) |α(τ)|≤|α|(Σ_Idet(A_I)²)^{1/2}=|α|det(AAᵀ)^{1/2}=|α|, as AAᵀ=(⟨τ_i,τ_j⟩)=id. (n=0: |α(∅)|=|α|.)
(P5) Orthonormal bases τ, τ' of an n-dimensional Q satisfy τ'_i=Σ_jO_{ij}τ_j, O orthogonal, so α(τ')=det(O)α(τ)=±α(τ) for alternating α. Hence 𝒰(ζ,Q)∧𝒰(ζ',Q) ⇒ ζ'=±ζ, and 𝒰(ζ,Q) ⇒ 𝒰(−ζ,Q).
(P6) For an IMRep (M,θ,ξ) in open U and compact K⊆U, Hⁿ(M∩K) ≤ ∫_{M∩K}θ dHⁿ < ∞ (θ≥1 on M).
(d) For Hⁿ-a.e. x∈R.carrier some Q has 𝒰(R.orient x, Q) (orientation field), i.e. ⟨α, R.orient x⟩=±α(τ) for an orthonormal τ and all α; so |R.orient x α|≤|α| by (P4).
(a) Let D:=M'∖M.
1. For R∈ℕ, U_R:={x∈U : |x|<R, infDist(x,ℝ^P∖U)>1/R} ({|x|<R} if U=ℝ^P) is open with compact closure in U, U_R ↑ U. D_R:=D∩U_R is Borel, Hⁿ(D_R)≤Hⁿ(M'∩closure U_R)<∞, so by (P2) some Hⁿ-null Z_R has Hⁿ(D_R∩B̄_r(x))=o(rⁿ) for x∉D_R∪Z_R. Let Z'⊇⋃_RZ_R be Borel, Hⁿ-null (P0). For x∈M∖Z' choose R, r₀>0 with B̄_{r₀}(x)⊆U_R; then x∉D_R (x∈M) and D∩B̄_r(x)=D_R∩B̄_r(x) for r<r₀, so Hⁿ(D∩B̄_r(x))=o(rⁿ).
2. Fix such x, a subspace Q, f∈C_c(ℝ^P) with spt f⊆B_ρ(0). For r<r₀/ρ, η_{x,r}(M), η_{x,r}(M') meet B_ρ(0) in sets of finite Hⁿ-measure (genuine Bochner integrals), η_{x,r}(M')=η_{x,r}(M)⊔η_{x,r}(D) (η_{x,r} injective), and by (P1)
 |∫_{η_{x,r}(M')}f dHⁿ − ∫_{η_{x,r}(M)}f dHⁿ| = |∫_{η_{x,r}(D)}f dHⁿ| ≤ |f|_∞r^{−n}Hⁿ(D∩B_{rρ}(x)) → 0.
So both families have the same limit as r→0⁺ or both have none, and finrank Q=n is common: 𝒯(M,x,Q)↔𝒯(M',x,Q) for x∈M∖Z' and all Q; M∩Z' is Hⁿ⌞M-null.
(b) For R=(M,θ,ξ) let R':=(M∩E,θ,ξ).
1. M∩E is Borel, ⊆U, countably n-rectifiable (subset of M); θ is measurable, >0 on M∩E, ∫_{M∩E∩K}θ dHⁿ ≤ ∫_{M∩K}θ dHⁿ < ∞ for compact K⊆U; ξ is a.e. strongly measurable for Hⁿ⌞(M∩E)≤Hⁿ⌞M.
2. By (P6) and (a) for M∩E⊆M⊆U, 𝒯(M∩E,x,Q)↔𝒯(M,x,Q) for Hⁿ-a.e. x∈M∩E and all Q, so the orientation field of R gives that of R'.
3. A(ω):=∫_{M∩E}θ⟨ω,ξ⟩dHⁿ (ω∈𝒟ⁿ(U)) is linear, the integrand being integrable: |θ⟨ω,ξ⟩|≤|ω|_∞θ1_{tsupport ω} Hⁿ-a.e. on M by (d), tsupport ω⊆U compact. If ω_j→0 in 𝒟ⁿ(U) (TestFormOnConverges: supports in a fixed compact K⊆U, all derivatives converge uniformly; so |ω_j|_∞→0, norms on covectors being equivalent), |A(ω_j)| ≤ |ω_j|_∞∫_{M∩K}θ dHⁿ → 0. So A is a GeometricCurrentOn U n represented by R' (IMRep.Represents).
(c) Let R_A=(M_A,θ_A,ξ_A), R_B=(M_B,θ_B,ξ_B) represent A, B.
1. Take Borel ξ̃_A, ξ̃_B equal to ξ_A, ξ_B Hⁿ-a.e. on M_A, resp. M_B (a.e. strong measurability), and 0 off them. Let G be the set of x∈M_A∪M_B such that: if x∈M_A, ξ̃_A(x)=ξ_A(x) and 𝒯(M_A,x,Q_A(x)), 𝒰(ξ_A x,Q_A(x)) for some Q_A(x); likewise for B; and 𝒯(N,x,·)↔𝒯(N',x,·) if x∈N, (N,N')∈{(M_A∩M_B,M_A), (M_A∩M_B,M_B)}. By the orientation fields, (P6) and (a), (M_A∪M_B)∖G is Hⁿ-null; let N₀ be a Borel Hⁿ-null superset (P0).
2. For x∈(M_A∩M_B)∖N₀, 𝒯(M_A∩M_B,x,Q) for Q=Q_A(x) and Q=Q_B(x) (def. of G), so Q_A(x)=Q_B(x) (HasApproximateTangentSpaceAt.unique) and by (P5) ξ̃_B(x)=ε(x)ξ̃_A(x), where ε(x):=1 if ξ̃_B(x)=ξ̃_A(x), −1 otherwise (Borel).
3. Let O:=(M_A∩M_B)∖N₀, k:=θ_A−εθ_B∈ℤ on O,
 M:=((M_A∖M_B) ∪ (M_B∖M_A) ∪ {x∈O : k(x)≠0})∖N₀,
 θ:=θ_A, θ_B, |k|, 0 and ζ:=ξ̃_A, −ξ̃_B, sign(k)ξ̃_A, 0 on M_A∖M_B, M_B∖M_A, O, elsewhere, respectively (Borel; θ ℕ-valued).
For x∉N₀, θ1_Mζ = θ_A1_{M_A}ξ̃_A − θ_B1_{M_B}ξ̃_B (on O: if k=0 both vanish, else θ_Aξ̃_A − θ_Bεξ̃_A=kξ̃_A=|k|sign(k)ξ̃_A; other cases immediate).
4. For ω∈𝒟ⁿ(U), pairing with ω and integrating (N₀ null; integrable by (d), θ1_M≤θ_A1_{M_A}+θ_B1_{M_B}): ∫_Mθ⟨ω,ζ⟩dHⁿ = ∫_{M_A}θ_A⟨ω,ξ_A⟩dHⁿ − ∫_{M_B}θ_B⟨ω,ξ_B⟩dHⁿ = (A−B)(ω).
5. M is Borel, ⊆M_A∪M_B⊆U, countably n-rectifiable (countable unions, subsets); θ≥1 on M (|k|≥1 where k≠0), ∫_{M∩K}θ ≤ ∫_{M_A∩K}θ_A+∫_{M_B∩K}θ_B < ∞ for compact K⊆U; ζ is Borel, so a.e. strongly measurable.
6. By (P6), Hⁿ(M∩K)≤Hⁿ(M_A∩K)+Hⁿ(M_B∩K)<∞ for compact K⊆U, so (a) applies to M∩M_A⊆M_A, M∩M_A⊆M, M∩M_B⊆M_B, M∩M_B⊆M: for Hⁿ-a.e. x∈M∩M_A, 𝒯(M,x,·)↔𝒯(M∩M_A,x,·)↔𝒯(M_A,x,·), likewise for M_B. For such x∉N₀: if x∈M_A, 𝒯(M,x,Q_A(x)) and ζ(x)=±ξ_A(x) (cases M_A∖M_B, O; ξ̃_A(x)=ξ_A(x)); if x∈M_B∖M_A, 𝒯(M,x,Q_B(x)) and ζ(x)=−ξ_B(x); so 𝒰(ζ(x),Q_A(x)), resp. 𝒰(ζ(x),Q_B(x)), by (P5). So the orientation field holds a.e. on M, and (M,θ,ζ) is an IMRep in U representing A−B, so A−B is integer multiplicity.

## Key steps

1. (REP) Mollify to extend T to a locally bounded L on C_c(U;H); vector Riesz gives μ, ξ, T(ω)=∫ξ(ω)dμ, |ξ(x)(α)|≤|α|.
2. (REP) M_W(T)=μ(W) via (3a), Urysohn, mollification.
3. (REP) Lemma TD (Gagliardo–Nirenberg–Sobolev) and projections p_α give μ(C)=0 for Hⁿ-null compact C.
4. (IMC) (d) by Cauchy–Binet; (a) by density zero of Hⁿ⌞(M'∖M); (b) via (a), (d).
5. (IMC) (c): orientations agree up to sign on the overlap; multiplicity |θ_A−εθ_B|; fields via (a).

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
