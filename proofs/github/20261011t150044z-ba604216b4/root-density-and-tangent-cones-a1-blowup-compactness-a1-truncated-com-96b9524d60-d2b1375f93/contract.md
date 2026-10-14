<!-- theorem-id: gmt-ch07/root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1.deformation-a1.face-a1 -->

## Theorem `Submission.dtc_bc_tc_cl_dfm_face_replacement`

Assume, as hypotheses of the statement, (VO) the frozen type of Submission.dtc_vanish_off_support: for all P, n, U, S ∈ 𝒟_n(U) and ω ∈ 𝒟ⁿ(U) with tsupport ω disjoint from spt S, S(ω) = 0; (MR) the frozen type of Submission.cmc_massOn_eq_imRep_measure: for U open and an IMRep R representing T ∈ 𝒟_n(U), M_W(T) = R.measure(W) for every open W; (IMC) the frozen type of Submission.cmc_imRep_locality_restrict_sub: (a) locality of approximate tangent spaces for Borel M ⊆ M' ⊆ U with Hⁿ(M' ∩ K) < ∞ (K ⊆ U compact); (b) the restriction (M ∩ E, θ, ξ) of an IMRep to a Borel E is an IMRep representing some current; (c) A − B is integer multiplicity for integer multiplicity A, B (U open); (d) |R.orient(x)(α)| ≤ |α| for Hⁿ-a.e. x in the carrier. (These are the exact frozen Lean types of the accepted declarations named above, written as antecedents. The parent node discharges them with its own antecedents (MR), (IMC), (VO), which are exactly these frozen types.) For all P, m ∈ ℕ (n := m + 1) there is c ∈ ℝ≥0 with c ≥ 1 such that for every compact K ⊆ ℝ^P and every Λ ∈ ℝ≥0 there is a finite set 𝒬₀ of currents in 𝒟_n(ℝ^P) (domain univ) with the following property: if Q₀ ∈ 𝒟_n(ℝ^P) is integer multiplicity, spt Q₀ ⊆ K, spt Q₀ ⊆ L_n := {x : there is a set s of coordinate indices with P ≤ n + |s| and x_i ∈ ℤ for i ∈ s}, M(Q₀) ≤ Λ and M(∂Q₀) < ∞, then there is Pc ∈ 𝒬₀ such that Pc and ∂Pc are integer multiplicity, Pc = 0 or M(Pc) ≥ 1, M(Pc) ≤ cM(Q₀), M(∂Pc) ≤ cM(∂Q₀), M(Q₀ − Pc) ≤ cM(∂Q₀), spt Pc ⊆ cthickening(√P, spt Q₀) and spt(Q₀ − Pc) ∪ spt ∂Pc ⊆ cthickening(√P, spt ∂Q₀).

Node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1.deformation-a1.face-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8061

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8157

Decomposition children: None

## Lean problem

Declaration: `Submission.dtc_bc_tc_cl_dfm_face_replacement`

```lean
(∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) → ∀ (P m : ℕ), ∃ c : NNReal, 1 ≤ c ∧ ∀ (K : Set (Euclid P)) (Λ : NNReal), IsCompact K → ∃ 𝒬₀ : Set (GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), 𝒬₀.Finite ∧ ∀ Q₀ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), IsIntegerMultiplicity Q₀ → Q₀.support ⊆ K → Q₀.support ⊆ {x : Euclid P | ∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, x i = z} → Q₀.mass ≤ Λ → Q₀.boundary.mass < ∞ → ∃ Pc ∈ 𝒬₀, IsIntegerMultiplicity Pc ∧ IsIntegerMultiplicity Pc.boundary ∧ (Pc = 0 ∨ 1 ≤ Pc.mass) ∧ Pc.mass ≤ c * Q₀.mass ∧ Pc.boundary.mass ≤ c * Q₀.boundary.mass ∧ (Q₀ - Pc).mass ≤ c * Q₀.boundary.mass ∧ Pc.support ⊆ cthickening (Real.sqrt P) Q₀.support ∧ (Q₀ - Pc).support ∪ Pc.boundary.support ⊆ cthickening (Real.sqrt P) Q₀.boundary.support
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

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1.deformation-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1.deformation-a1.face-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 6, proof of the deformation theorem 5.1, displays (26)–(37) (chapter-06.txt lines 1844–1928, printed pp. 167–168), together with the finite family of polyhedral chains of 7.2 (1)–(3) (lines 2047–2091). The BV facts used by Simon on the faces (2.34–2.35; Ch. 2, 2.7, 2.9) are replaced by the sibling dtc_bc_tc_cl_dfm_cube_bv_median (CB). Simon bounds the variation on a face by μ_{∂Q}(F̆). Here the corresponding number is Var_F := M_{N_F}(∂Q₀) for explicit pairwise disjoint open neighbourhoods N_F, which needs no measure representation of ∂Q₀ (below, V_F denotes the coordinate n-plane of F). The frozen statement is byte-identical to that of cmcdt_face_replacement (compactness_of_minimizing_currents branch, speculative-ready) and of the leaf dtc_bc_lc_fd_dfm_face_replacement (local_comparison branch, in formalization), whose dependency CB has the same frozen type as ours; neither is accepted, so a fresh name is used, and an accepted single-theorem proof of the leaf can be transplanted after renaming CB. The argument below is the one written and reviewed for that statement.

Notation. n := m + 1. (VO), (MR), (IMC) are the three displayed hypotheses (frozen types of Submission.dtc_vanish_off_support, cmc_massOn_eq_imRep_measure, cmc_imRep_locality_restrict_sub). Currents are on univ in ℝ^P; |·| is the Euclidean coefficient norm, ‖ω‖ := sup|ω(x)|, and |X(ω)| ≤ M(X)‖ω‖. Support facts: spt(A − B) ⊆ spt A ∪ spt B, spt ∂A ⊆ spt A, spt 0 = ∅, and a current vanishing on all test forms supported off a closed set E has support in E. Hⁿ := μHE[n], Lⁿ is Lebesgue measure, Q₁ := (0,1)ⁿ.

1. Trivial case n > P. Every n-covector on ℝ^P vanishes (n vectors in ℝ^P are linearly dependent), so every n-current is 0. Take c := 1 and 𝒬₀ := {0}; for Q₀ = 0 take Pc := 0 (0 and ∂0 = 0 are integer multiplicity, all masses are 0, spt 0 = ∅). From now on n ≤ P; let c_B be CB's constant and c := max(2, 1 + c_B).

2. Faces. For I = {i_1 < ⋯ < i_n} ⊆ {1,…,P} and b ∈ ℤ^P, F = F(b, I) := {x : b_i ≤ x_i ≤ b_i + 1 (i ∈ I), x_i = b_i (i ∉ I)} is an n-face; distinct pairs (b|_{all}, I) give distinct faces. Further notation:
 - F̆ := {b_i < x_i < b_i + 1 (i ∈ I), x_i = b_i (i ∉ I)}, Π_F := {x : x_i = b_i (i ∉ I)}, V_F := span{e_i : i ∈ I};
 - e_F is the n-vector α ↦ α(e_{i_1},…,e_{i_n}) (a unit orientation of V_F);
 - φ_F(y) := b + Σ_j y_j e_{i_j} is an affine isometric embedding ℝⁿ → ℝ^P with φ_F(Q₁) = F̆ and φ_F([0,1]ⁿ) = F;
 - p̃_F(x) := (x_{i_j} − b_{i_j})_j and p_F := φ_F ∘ p̃_F (orthogonal projection onto Π_F);
 - δ_F(y) := dist(y, F ∖ F̆) = min_j min(y_{i_j} − b_{i_j}, b_{i_j} + 1 − y_{i_j}) for y ∈ F̆.
 Hⁿ⌞Π_F is the image of Lⁿ under φ_F (Mathlib Isometry.euclideanHausdorffMeasure_image and EuclideanSpace.euclideanHausdorffMeasure_eq_volume), so Hⁿ(F̆) = Hⁿ(F) = 1 and Hⁿ(F ∖ F̆) = 0; diam F = √n. The union of the n-faces is L_n = {x : at least P − n integer coordinates}. L_{n−1} (at least P − n + 1 integer coordinates) is the union of the (n−1)-faces and has Hⁿ(L_{n−1}) = 0 (each (n−1)-face is covered by k^{n−1} sets of diameter √n/k, so its Hⁿ measure is ≤ C k^{n−1}k^{−n} → 0). L_n ∖ L_{n−1} is the disjoint union of the F̆ (for x with exactly P − n integer coordinates, I := the others, b_i := ⌊x_i⌋ (i ∈ I), b_i := x_i (i ∉ I)). Face currents: [[F]](ω) := ∫_F ⟨ω, e_F⟩ dHⁿ = ∫_{[0,1]ⁿ} ω(φ_F y)(e_{i_1},…,e_{i_n}) dy is a current (|[[F]](ω)| ≤ ‖ω‖) with spt [[F]] ⊆ F.
 Lemma 2.1: if y ∈ F̆ and G ≠ F is an n-face, then dist(y, G) ≥ δ_F(y). (The same statement and proof hold verbatim for distinct j-faces of any common dimension j; it is used for j = n − 1 in 8.) Proof: let z ∈ G. Then |y − z| ≥ |y − p_F(z)|. If p_F(z) ∉ F̆ then |y − p_F(z)| ≥ δ_F(y). Otherwise the coordinates z_i (i ∈ I) are non-integers, so they are free coordinates of G. As G has exactly n free coordinates, they are I, and z_i ∈ (b_i, b_i + 1) forces G = F(b', I) with b'_i = b_i (i ∈ I). G ≠ F gives b'_k ≠ b_k for some k ∉ I, and |y − z| ≥ |b_k − b'_k| ≥ 1 ≥ δ_F(y).
 Neighbourhoods: N_F := {x : p_F(x) ∈ F̆, |x − p_F(x)| < δ_F(p_F(x))/2} is open.
 (i) N_F ∩ L_n ⊆ F̆: if x ∈ N_F ∩ G for an n-face G ≠ F, then y := p_F(x) ∈ F̆ satisfies |x − y| < δ_F(y)/2 ≤ dist(y, G)/2 ≤ |x − y|/2, which is impossible. So x ∈ F ⊆ Π_F and p_F(x) = x ∈ F̆.
 (ii) N_F ∩ N_{F'} = ∅ for F ≠ F': with y := p_F(x), y' := p_{F'}(x), Lemma 2.1 gives |y − y'| ≥ max(δ_F(y), δ_{F'}(y')), while |y − y'| < (δ_F(y) + δ_{F'}(y'))/2.
 Finite family. Given K (compact) and Λ, let 𝔉_K be the set of n-faces contained in cthickening(√P, K), a finite set (a bounded set contains finitely many unit faces), and 𝒬₀ := {Σ_{F∈𝔉_K} β_F[[F]] : β : 𝔉_K → ℤ, Σ_F|β_F| ≤ 2Λ}, where Σβ_F[[F]] is the current ω ↦ Σβ_F[[F]](ω). 𝒬₀ is finite (the image of a finite set of coefficient vectors) and does not depend on Q₀.

3. Decomposition on open faces (Simon (33)). Let Q₀ be as in the statement, R = (M, θ, ξ) an IMRep and μ := R.measure. By (MR), μ(W) = M_W(Q₀) for open W, so μ(ℝ^P) = M(Q₀). By (VO), μ(ℝ^P ∖ spt Q₀) = 0, hence μ(ℝ^P ∖ L_n) = 0; and μ(L_{n−1}) = 0 as Hⁿ(L_{n−1}) = 0. Thus Hⁿ(M ∖ ⋃_F F̆) = 0 (θ ≥ 1 on M). Let 𝔉 := {F : F̆ ∩ spt Q₀ ≠ ∅}. Since spt Q₀ ⊆ K is compact, 𝔉 is finite; every F ∈ 𝔉 lies in cthickening(√n, spt Q₀) ⊆ cthickening(√P, K) (so 𝔉 ⊆ 𝔉_K); and μ(F̆) = 0 for F ∉ 𝔉. For F ∈ 𝔉, (IMC)(b) with E := F̆ (Borel) gives a current A_F represented by R_F := (M ∩ F̆, θ, ξ). For every test form ω, the function θξ(ω) is Hⁿ-integrable on M (|ξ(x)(ω(x))| ≤ ‖ω‖ a.e. by (IMC)(d), and ∫_M θ dHⁿ = μ(ℝ^P) = M(Q₀) < ∞). Splitting the representing integral over the disjoint sets M ∩ F̆ (F ∈ 𝔉) and the Hⁿ-null remainder gives Q₀(ω) = Σ_{F∈𝔉} A_F(ω) for all ω, and M(Q₀) = Σ_{F∈𝔉} μ(F̆).

4. Orientation on faces (Simon (26)–(27)). Fix F ∈ 𝔉. For Hⁿ-a.e. x ∈ M ∩ F̆ there is Q_x with HasApproximateTangentSpaceAt n (M ∩ F̆) x Q_x and ξ(x) a unit orientation of Q_x (R_F is an IMRep). Since M ∩ F̆ ⊆ Π_F ∋ x, blowUpMap x r '' (M ∩ F̆) ⊆ V_F for all r > 0. Suppose Q_x ≠ V_F; pick q ∈ Q_x ∖ V_F, ε := dist(q, V_F)/2 and f(y) := max(0, ε − |y − q|). Then ∫_{blowUpMap x r''(M∩F̆)} f dHⁿ = 0 for all r, while ∫_{Q_x} f dHⁿ ≥ (ε/2)Hⁿ(Q_x ∩ B_{ε/2}(q)) > 0, contradicting the definition. So Q_x = V_F and, by the sign rule (two unit orientations of one n-plane differ by a sign: the transition between orthonormal bases has determinant ±1), ξ(x) = ±e_F. Let α_F be the n-covector with α_F(v_1,…,v_n) := det((v_j)_{i_k})_{j,k}, so e_F(α_F) = 1, and s_F(x) := ξ(x)(α_F) (a.e. ±1). Define u_F := s_Fθ on {x ∈ M ∩ F̆ : s_F(x) ∈ {±1}} and u_F := 0 elsewhere (Borel after modification of ξ on a null set; integer-valued). Then A_F(ω) = ∫_{F̆} u_F ⟨ω, e_F⟩ dHⁿ and ∫_{F̆}|u_F| dHⁿ = μ(F̆). With ũ_F := u_F ∘ φ_F (integer-valued on ℝⁿ, integrable on Q₁, ∫_{Q₁}|ũ_F| = μ(F̆)): A_F(ω) = ∫_{Q₁} ũ_F(y) ω(φ_F y)(e_{i_1},…,e_{i_n}) dy.

5. Boundary variation on a face (Simon (27)–(33)). For F ∈ 𝔉 let Var_F := M_{N_F}(∂Q₀) ≤ M(∂Q₀) < ∞ (a number; not to be confused with the plane V_F). Claim: ∫_{Q₁} ũ_F div g ≤ Var_F for every smooth g : ℝⁿ → ℝⁿ with compact support in Q₁ and |g| ≤ 1.
 Let ε_j := (−1)^{j−1} dx^{i_1} ∧ ⋯ ∧ dx^{i_{j−1}} ∧ dx^{i_{j+1}} ∧ ⋯ ∧ dx^{i_n}. Choose χ ∈ C_c^∞(N_F), 0 ≤ χ ≤ 1, with χ = 1 on a neighbourhood of the compact set φ_F(spt g) ⊆ F̆ ⊆ N_F, and put γ(x) := χ(x) Σ_j g_j(p̃_F x) ε_j. Then γ is a test (n−1)-form with tsupport γ ⊆ N_F and |γ(x)| = χ(x)|g(p̃_F x)| ≤ 1. For x ∈ F̆, ⟨dγ(x), e_F⟩ = Σ_j ∂_{i_j}(χ·g_j∘p̃_F)(x) = div g(p̃_F x): where g∘p̃_F ≠ 0 near x, χ = 1 near x; elsewhere both sides vanish; and derivatives in directions k ∉ I do not pair with e_F. For an n-face G ∈ 𝔉, G ≠ F, the integrand of A_G(dγ) vanishes, because tsupport dγ ⊆ N_F and N_F ∩ Ğ ⊆ N_F ∩ L_n ∩ Ğ ⊆ F̆ ∩ Ğ = ∅. Hence ∂Q₀(γ) = Q₀(dγ) = A_F(dγ) = ∫_{Q₁} ũ_F div g. Since γ is admissible for M_{N_F}(∂Q₀), ∫_{Q₁} ũ_F div g ≤ Var_F.
 Moreover Σ_{F∈𝔉} Var_F ≤ M(∂Q₀). For ε > 0 choose admissible γ_F with tsupport γ_F ⊆ N_F and ∂Q₀(γ_F) ≥ Var_F − ε. Since the N_F are pairwise disjoint, Σ_F γ_F is admissible (at each point at most one term is nonzero), so M(∂Q₀) ≥ Σ_F Var_F − |𝔉|ε.

6. Integer medians (Simon (31)–(32); CB). For F ∈ 𝔉 apply CB to ũ_F and the real number V := Var_F (finite, as Var_F ≤ M(∂Q₀) < ∞; CB's hypothesis is the claim of 5). There is β_F ∈ ℤ with (1) ∫_{Q₁}|ũ_F − β_F| ≤ c_B Var_F, (2) |β_F| ≤ 2∫_{Q₁}|ũ_F| = 2μ(F̆), and (3) |∫_{Q₁}(ũ_F − β_F) div G| ≤ c_B Var_F for every smooth G : ℝⁿ → ℝⁿ with |G| ≤ 1. Put β_F := 0 for F ∉ 𝔉.

7. The polyhedral current (Simon (34)–(37)). Pc := Σ_{F∈𝔉} β_F[[F]]. Σ_F|β_F| ≤ 2Σ_F μ(F̆) = 2M(Q₀) ≤ 2Λ and 𝔉 ⊆ 𝔉_K, so Pc ∈ 𝒬₀. Since Hⁿ(F ∖ F̆) = 0,
 (Q₀ − Pc)(ω) = Σ_{F∈𝔉} ∫_{Q₁} (ũ_F − β_F)(y) ω(φ_F y)(e_{i_1},…,e_{i_n}) dy.
 (34a) For admissible ω, |ω(x)(e_{i_1},…,e_{i_n})| ≤ |ω(x)| ≤ 1 (one coefficient), so M(Q₀ − Pc) ≤ Σ_F ∫|ũ_F − β_F| ≤ c_B Σ_F Var_F ≤ c_B M(∂Q₀).
 (34b) For an admissible (n−1)-form γ', let α := φ_F^#γ' and G_F(y)_j := (−1)^{j−1} α(y)(e_1,…,ê_j,…,e_n) = (−1)^{j−1} γ'(φ_F y)(e_{i_1},…,ê_{i_j},…,e_{i_n}). G_F is smooth and |G_F(y)|² ≤ |γ'(φ_F y)|² ≤ 1 (distinct coefficients of γ'). By the coordinate formula for d (SimonGMT exteriorDerivative_apply) and the chain rule, dγ'(φ_F y)(e_{i_1},…,e_{i_n}) = div G_F(y). Hence ∂(Q₀ − Pc)(γ') = (Q₀ − Pc)(dγ') = Σ_F ∫_{Q₁}(ũ_F − β_F) div G_F, which has absolute value ≤ c_B Σ_F Var_F ≤ c_B M(∂Q₀) by (3). So M(∂(Q₀ − Pc)) ≤ c_B M(∂Q₀).
 (36), (37) M(Pc) ≤ Σ_F|β_F| ≤ 2M(Q₀) (indeed M(Pc) = Σ|β_F|, see 8). ∂Pc = ∂Q₀ − ∂(Q₀ − Pc), so M(∂Pc) ≤ (1 + c_B)M(∂Q₀).

8. Integrality and the mass dichotomy. Pc is represented by the IMRep with carrier C_P := ⋃_{β_F≠0} F̆ (Borel, and countably n-rectifiable as a finite union of subsets of the affine images φ_F(ℝⁿ)), multiplicity |β_F| on F̆ (the F̆ are disjoint) and orientation sign(β_F)e_F. Approximate tangent space: for x ∈ F̆ and δ < δ_F(x), Π_F ∩ B_δ(x) ⊆ F̆ (points of Π_F within δ_F(x) of x have their free coordinates strictly inside (b_i, b_i + 1)), and by Lemma 2.1 no other open face meets B_δ(x). So C_P ∩ B_δ(x) = Π_F ∩ B_δ(x), and for f ∈ C_c(ℝ^P) with spt f ⊆ B_ρ(0) and r < δ/ρ, ∫_{blowUpMap x r '' C_P} f dHⁿ = ∫_{V_F} f dHⁿ. That is, V_F is the approximate tangent space, oriented by sign(β_F)e_F. The action is Σ_F ∫_{F̆}|β_F| sign(β_F)⟨ω, e_F⟩ dHⁿ = Pc(ω). By (MR), M(Pc) = Σ_F |β_F| Hⁿ(F̆) = Σ_F |β_F|; hence either all β_F = 0 and Pc = 0, or M(Pc) ≥ 1.
 Boundary: for an (n−1)-form γ, Fubini and the fundamental theorem of calculus on [0,1]ⁿ give [[F]](dγ) = Σ_j (−1)^{j−1}([[G_j^1]](γ) − [[G_j^0]](γ)). Here G_j^ε is the (n−1)-face of F with x_{i_j} = b_{i_j} + ε, and [[G]](γ) := ∫_G ⟨γ, e_G⟩ dH^{n−1} with its coordinate orientation e_G (for n = 1, [[G]](γ) = γ(v) at the vertex G = {v}). So ∂Pc = Σ_G γ_G[[G]], a finite sum over (n−1)-faces with γ_G ∈ ℤ. It is integer multiplicity by the same construction in degree n − 1 (for n − 1 = 0: finite carrier of vertices, multiplicity |γ_v|, orientation sign(γ_v), approximate tangent space {0} at isolated points, H⁰ the counting measure).

9. Supports (Simon (23)).
 - spt Pc ⊆ ⋃_{β_F≠0} F. β_F ≠ 0 gives F ∈ 𝔉 (μ(F̆) ≥ |β_F|/2 > 0 by (2)), so F̆ meets spt Q₀ and F ⊆ cthickening(√n, spt Q₀) ⊆ cthickening(√P, spt Q₀).
 - spt(Q₀ − Pc) ⊆ ⋃{F ∈ 𝔉 : ∫_{Q₁}|ũ_F − β_F| > 0}. For such F, (1) gives Var_F = M_{N_F}(∂Q₀) > 0, so some γ with tsupport γ ⊆ N_F has ∂Q₀(γ) ≠ 0; by (VO), N_F meets spt ∂Q₀. As spt ∂Q₀ ⊆ spt Q₀ ⊆ L_n and N_F ∩ L_n ⊆ F̆, F̆ meets spt ∂Q₀ and F ⊆ cthickening(√n, spt ∂Q₀). Hence spt(Q₀ − Pc) ⊆ cthickening(√P, spt ∂Q₀).
 - spt ∂Pc ⊆ spt ∂Q₀ ∪ spt ∂(Q₀ − Pc) ⊆ spt ∂Q₀ ∪ spt(Q₀ − Pc) ⊆ cthickening(√P, spt ∂Q₀).

10. With c = max(2, 1 + c_B) ≥ 1 and the finite set 𝒬₀ of 2 (fixed before Q₀), Pc satisfies every conclusion: Pc ∈ 𝒬₀ (7), Pc and ∂Pc integer multiplicity (8), Pc = 0 or M(Pc) ≥ 1 (8), the mass bounds (7), and the support inclusions (9). ∎

## Key steps

1. Trivial case n > P; unit grid n-faces, face currents [[F]], the finite family of integer chains on faces in cthickening(√P, K) with Σ|β_F| ≤ 2Λ.
2. Disjoint open neighbourhoods N_F with N_F ∩ L_n ⊆ F̆ (distance lemma for distinct faces).
3. Q₀ = Σ_F Q₀⌞F̆ (MR, VO, Hⁿ(L_{n−1}) = 0, IMC(b)); approximate tangent planes of subsets of Π_F are V_F, so Q₀⌞F̆ = ũ_F[[F̆]] with integer ũ_F.
4. Testing ∂Q₀ with forms built from fields g on the face gives ∫ũ_F div g ≤ Var_F := M_{N_F}(∂Q₀), and Σ_F Var_F ≤ M(∂Q₀).
5. CB yields integer medians β_F; Pc := Σβ_F[[F]] ∈ 𝒬₀ with M(Q₀ − Pc), M(∂(Q₀ − Pc)) ≤ c_B M(∂Q₀), M(Pc) ≤ 2M(Q₀), M(∂Pc) ≤ (1 + c_B)M(∂Q₀).
6. IMReps of Pc and ∂Pc (Stokes on cubes), M(Pc) = Σ|β_F| so Pc = 0 or M(Pc) ≥ 1; supports via spt Q₀ and Var_F > 0 ⇒ F̆ meets spt ∂Q₀.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical); md5sum GMT/Ch07/Submission.lean GMT/Ch07/Contract.lean (identical)`
- `rg -n -l -i 'skeleton_retraction|cmcdt_|dtc_bc_tc_cl_dfm|deformation_theorem|isoperimetric' project -g '*.lean' (only project/GMT/Ch06/Contract.lean and project/GMT/Ch06/Submission.lean); grep -n -i 'DeformationTheorem|IsLatticeChain|LipschitzPushforwardIntegerMultiplicity' project/GMT/Ch06/Contract.lean (defs at lines 177, 223, 274; main_theorem := by sorry at line 362)`
- `grep -n 'theorem mem_thickening_iff_infEDist_lt|theorem mem_cthickening_iff |theorem cthickening_mono|theorem cthickening_subset_of_subset|IsCompact.cthickening|theorem cthickening_cthickening' mathlib/Mathlib/Topology/MetricSpace/Thickening.lean mathlib/Mathlib/Analysis/Normed/Module/Ball/Pointwise.lean; grep -rn 'infEDist_smul₀' mathlib/Mathlib/Analysis/Normed/Module/Ball/ (all found; an unrestricted rg over mathlib/Mathlib timed out after 120 s and was replaced by these targeted greps)`
- `grep -n 'theorem WeaklyConvergesOn.massOn_le_liminf|theorem WeaklyConvergesOn.boundary|theorem GeometricCurrentOn.boundary_affinePushforward|theorem GeometricCurrentOn.le_massOn|theorem GeometricCurrentOn.zero_apply|def GeometricCurrentOn.VanishesOn|def GeometricCurrentOn.support|theorem GeometricCurrentOn.boundary_boundary' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/*.lean (all found); grep -n 'def HasApproximateTangentSpaceAt' -A 8 Chapter03/Rectifiable.lean (includes finrank ℝ P = n)`
- `python3 -I over dag.json: status, candidate_commit and updated_at of the six reuse names and of all nodes with identical lean_statement (twins); replay of Runtime._existing_lean_name_problem for the 11 proposed names with parent root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1.deformation-a1 (no problem)`
- `grep -n '_existing_lean_name_problem|def _accepted_checkpoint|def _overlay_accepted_children|def _leaf_author_task' /runtime/flows/gmt-claude-63aa5a7df725/_recursive_lean/runtime.py; Store.refresh in store.py; github_shared_issue_runtime in scripts/swarm-run-issue.py (HUMANIZE_SWARM_PROTOCOL=shared-theorem-issues-v1, so the DAG store refreshes on every update)`
- `git show <candidate>:GMT/Ch07/Submission.lean for 0c9347ca33 (cmcdt_skeleton_retraction), 42b2a51030, fba5d30a5b, 9b823b5696, 6ae39d3e62, 172c98ff29: declared type byte-identical to the child type, the only sorry is main_theorem, no axiom declarations; grep of the five fresh names in these and in the dependency candidates a1c12d76e1, b23650f455 (no hit)`
- `nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-ske-2b0c475fa4/{parent-child-handoff.json, parent-supplied-natural-proof.md, isolated-comparator-result.json, lean-audit-v1.json} (audited proof and acceptance evidence of cmcdt_skeleton_retraction)`
- `difflib comparison of the bv_median, pushforward, skeleton and face natural proofs with nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-57991f1e6d/decomposition-v4.json (only names and provenance differ); decomposition-audit-v4.json (all 12 children acceptable)`
- `PATH=toolchains/lean-4.35.0-rc3-linux/bin:$PATH lake env lean /tmp/dtc_dfm_v2/Final2.lean (13 sorry warnings for stand-ins; #print axioms Check.assembly and Check.iso: [propext, Classical.choice, Quot.sound]; Check.composed typechecks); validate_lean_statement (copy of verifier/lean_contract.py) on all 11 child types (accepted)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Ball/Pointwise.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-truncated-com-cba2d86b76/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-truncated-com-cba2d86b76/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-ske-2b0c475fa4/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-ske-2b0c475fa4/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-57991f1e6d/decomposition-v4.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-57991f1e6d/decomposition-audit-v4.json`
- `/runtime/flows/gmt-claude-63aa5a7df725/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-63aa5a7df725/_recursive_lean/store.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/dtc_dfm_v2/Final2.lean`

The snapshot (local-project, project b4d606db, Mathlib 25730c7c) has a Ch07 Contract.lean byte-identical to the workspace Contract.lean and Submission.lean. Its only deformation or isoperimetric material is the separate, unsolved Ch06 specification (DeformationTheorem, IsLatticeChain, LipschitzPushforwardIntegerMultiplicity; main_theorem := by sorry). That specification uses incompatible types and cannot be imported into Ch07, so it is not reusable; no cmcdt_ or dtc_bc_tc_cl_dfm_ declaration exists in the snapshot. Mathlib supplies every lemma used by the parent assembly (mem_thickening_iff_infEDist_lt, mem_cthickening_iff, cthickening_mono, cthickening_subset_of_subset, IsCompact.cthickening, cthickening_cthickening, infEDist_smul₀). SimonGMT supplies the cited current lemmas, and HasApproximateTangentSpaceAt includes finrank = n, as the face argument needs. The reuse names are accepted checkpoints with byte-identical types and clean candidates. The replaced name dtc_bc_lc_fd_dfm_skeleton_retraction is not used; its long-accepted twin cmcdt_skeleton_retraction is reused. All child types elaborate, and the parent assembly and the isoperimetric proof compile with only propext, Classical.choice and Quot.sound.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
