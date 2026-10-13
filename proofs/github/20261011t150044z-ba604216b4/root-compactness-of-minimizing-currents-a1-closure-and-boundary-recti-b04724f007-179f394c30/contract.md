<!-- theorem-id: gmt-ch07/root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.im_local-a1.glue-a1.glue_pieces-a1 -->

## Theorem `Submission.cbrg_imRep_glue_disjoint`

Assume (IMC)(a), passed as a hypothesis: the exact first conjunct of the frozen statement of cmc_imRep_locality_restrict_sub, namely: for all P, n ∈ ℕ, every open U ⊆ ℝ^P and all Borel sets M ⊆ M' ⊆ U with Hⁿ(M' ∩ K) < ∞ for every compact K ⊆ U (Hⁿ = μHE[n]), for Hⁿ-a.e. x ∈ M and every linear subspace Q, Q is an approximate tangent space of M at x iff it is one of M' at x (HasApproximateTangentSpaceAt). Let ι be a countable type, P, k ∈ ℕ and U ⊆ ℝ^P open. For each i ∈ ι let W_i ⊆ U be open, R_i an IMRep in W_i (IMRep (W i) k) with carrier M_i, multiplicity θ_i, orientation ξ_i and weight R_i.measure = (Hᵏ⌞M_i).withDensity θ_i (Hᵏ = μHE[k]), and A_i a Borel set, with the A_i pairwise disjoint. Let μ be a measure on ℝ^P and ξ : ℝ^P → Λ_k(ℝ^P) (MultiVector P k) such that: μ(ℝ^P ∖ ⋃_i A_i) = 0; μ⌞A_i = (R_i.measure)⌞A_i for every i; μ(K) < ∞ for every compact K ⊆ U; ξ is a.e. strongly measurable for μ; and, for every i, ξ(y) = ξ_i(y) for Hᵏ-a.e. y ∈ M_i ∩ A_i. Then there is an IMRep R' in U (IMRep U k) with carrier ⋃_i (M_i ∩ A_i), orientation R'.orient = ξ and weight R'.measure = μ.

Node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.im_local-a1.glue-a1.glue_pieces-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5342

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5998

Decomposition children: None

## Lean problem

Declaration: `Submission.cbrg_imRep_glue_disjoint`

```lean
(∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) → ∀ (ι : Type) [Countable ι] (P k : ℕ) (U : Set (Euclid P)) (W A : ι → Set (Euclid P)) (R : (i : ι) → IMRep (W i) k) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P k), IsOpen U → (∀ i, IsOpen (W i)) → (∀ i, W i ⊆ U) → (∀ i, MeasurableSet (A i)) → Pairwise (fun i j => Disjoint (A i) (A j)) → μ (⋃ i, A i)ᶜ = 0 → (∀ i, μ.restrict (A i) = (R i).measure.restrict (A i)) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → AEStronglyMeasurable ξ μ → (∀ i, ∀ᵐ y ∂(μHE[k].restrict ((R i).carrier ∩ A i)), ξ y = (R i).orient y) → ∃ R' : IMRep U k, R'.carrier = ⋃ i, (R i).carrier ∩ A i ∧ R'.orient = ξ ∧ R'.measure = μ
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

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.im_local-a1.glue-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.im_local-a1.glue-a1.glue_pieces-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 4–8 of the selected node's supplied proof: the glued data (M, θ), the measure identity μ = (Hᵏ⌞M).withDensity θ, its consequences 6(a)–(d), the orientation step 7 and the glued IMRep of step 8. They are stated for an arbitrary countable family of pairwise disjoint Borel pieces A_i. The glued orientation is ξ itself, exactly as in the supplied proof. The orientation step is the sibling cbrg_ae_orient_iUnion.

Notation: Hᵏ := μHE[k]. For i ∈ ι write M_i := (R i).carrier, θ_i := (R i).mult and ξ_i := (R i).orient, so that R_i.measure = (Hᵏ⌞M_i).withDensity θ_i (contract IMRep.measure). Put N_i := M_i ∩ A_i and M := ⋃_i N_i. The hypotheses are those of the statement: (IMC)(a); ι countable; U open; W_i open with W_i ⊆ U; A_i Borel and pairwise disjoint; μ((⋃_i A_i)ᶜ) = 0; μ⌞A_i = (R_i.measure)⌞A_i; μ(K) < ∞ for compact K ⊆ U; ξ is a.e. strongly measurable for μ; and ξ = ξ_i holds Hᵏ⌞N_i-a.e.

1. (Glued multiplicity.) Define θ : ℝ^P → ℕ as follows. If x ∈ A_j for some j, pick such a j (classical choice) and set θ(x) := θ_j(x). Otherwise set θ(x) := 0. In Lean: θ x := if h : ∃ i, x ∈ A i then (R h.choose).mult x else 0.

2. (θ = θ_i on A_i.) Let x ∈ A_i, and let j be the index chosen in step 1. Then x ∈ A_j. If j ≠ i, then x ∈ A_j ∩ A_i = ∅ by pairwise disjointness, which is impossible. So j = i and θ(x) = θ_i(x). Also, θ(x) = 0 whenever x lies in no A_i.

3. (The carrier.) Each N_i = M_i ∩ A_i is Borel (field measurableSet_carrier of R_i, and A_i Borel). So M = ⋃_i N_i is Borel as a countable union. Moreover M ⊆ U, because N_i ⊆ M_i ⊆ W_i ⊆ U by the field carrier_subset and the hypothesis W_i ⊆ U.

4. (θ is measurable.) ℕ is countable with the discrete σ-algebra, so it suffices that every fibre θ⁻¹({n}) is Borel (Mathlib measurable_to_countable'). By step 2,
θ⁻¹({n}) = ⋃_i (A_i ∩ θ_i⁻¹({n})) ∪ ((⋃_i A_i)ᶜ ∩ E_n),
where E_n = ℝ^P if n = 0 and E_n = ∅ otherwise. Each θ_i⁻¹({n}) is Borel by the field measurable_mult. So the right side is Borel.

5. (θ ≥ 1 on M.) If x ∈ M, then x ∈ N_i = M_i ∩ A_i for some i. So θ(x) = θ_i(x) > 0 by step 2 and the field mult_pos of R_i.

6. (M is countably k-rectifiable.) Each N_i ⊆ M_i is countably k-rectifiable by the field rectifiable of R_i and CountablyRectifiable.mono.
- If ι is empty, then M = ∅. This set is Hᵏ-null, hence countably k-rectifiable (countablyRectifiable_of_measure_zero).
- Otherwise there is a surjection s : ℕ → ι (exists_surjective_nat). Then M = ⋃_n N_{s(n)} (Function.Surjective.iUnion_comp), which is countably k-rectifiable by SimonGMT countablyRectifiable_iUnion.

7. (μ = Σ_i (R_i.measure)⌞A_i.) Since μ((⋃_i A_i)ᶜ) = 0, μ-a.e. point lies in ⋃_i A_i. So μ⌞(⋃_i A_i) = μ (restrict_eq_self_of_ae_mem). The A_i are pairwise disjoint Borel sets, so μ⌞(⋃_i A_i) = Σ_i μ⌞A_i (Measure.restrict_iUnion). By hypothesis μ⌞A_i = (R_i.measure)⌞A_i.

8. (The measure identity (Hᵏ⌞M).withDensity θ = μ.) The N_i are Borel and pairwise disjoint (N_i ⊆ A_i). So Hᵏ⌞M = Σ_i Hᵏ⌞N_i (Measure.restrict_iUnion), and therefore (Hᵏ⌞M).withDensity θ = Σ_i (Hᵏ⌞N_i).withDensity θ (withDensity_sum). For each i:
- (R_i.measure)⌞A_i = ((Hᵏ⌞M_i).withDensity θ_i)⌞A_i = (Hᵏ⌞(A_i ∩ M_i)).withDensity θ_i = (Hᵏ⌞N_i).withDensity θ_i (restrict_withDensity, Measure.restrict_restrict, commutativity of ∩);
- θ = θ_i holds Hᵏ⌞N_i-a.e., by step 2 and N_i ⊆ A_i, so (Hᵏ⌞N_i).withDensity θ = (Hᵏ⌞N_i).withDensity θ_i (withDensity_congr_ae).
Summing over i and using step 7 gives (Hᵏ⌞M).withDensity θ = Σ_i (R_i.measure)⌞A_i = μ.

9. (Local integrability.) Let K ⊆ U be compact, hence closed, hence Borel. Then ∫_{M∩K} θ dHᵏ = ((Hᵏ⌞M).withDensity θ)(K) (withDensity_apply, Measure.restrict_restrict). By step 8 this equals μ(K), which is < ∞ by hypothesis.

10. (Local finiteness of M.) For compact K ⊆ U, Hᵏ(M ∩ K) = ∫_{M∩K} 1 dHᵏ (setLIntegral_one). This is at most ∫_{M∩K} θ dHᵏ, by step 5 and setLIntegral_mono (θ is measurable by step 4). By step 9 this is < ∞.

11. (ξ is Hᵏ⌞M-measurable.) θ ≠ 0 holds Hᵏ⌞M-a.e., since Hᵏ⌞M-a.e. point lies in the Borel set M and θ > 0 on M (step 5). So Hᵏ⌞M ≪ (Hᵏ⌞M).withDensity θ (withDensity_absolutelyContinuous'), and this measure is μ by step 8. Since ξ is a.e. strongly measurable for μ, it is a.e. strongly measurable for Hᵏ⌞M (AEStronglyMeasurable.mono_ac).

12. (Orientation.) Apply the sibling cbrg_ae_orient_iUnion, with (IMC)(a), ι, P, k, U, the families W, N, R and ξ. Its hypotheses hold:
- U is open and every W_i is open;
- every N_i is Borel, and N_i ⊆ M_i;
- M = ⋃_i N_i ⊆ U (step 3);
- Hᵏ(M ∩ K) ≠ ∞ for compact K ⊆ U (step 10);
- ξ = ξ_i holds Hᵏ⌞N_i-a.e. (hypothesis).
It yields: for Hᵏ⌞M-a.e. x there is a subspace Q with HasApproximateTangentSpaceAt k M x Q and IsUnitOrientationOf (ξ x) Q.

13. (The glued IMRep.) Let R' := (M, θ, ξ). Its fields are justified as follows:
- measurableSet_carrier and carrier_subset: step 3;
- rectifiable: step 6;
- measurable_mult: step 4;
- mult_pos: step 5;
- locallyIntegrable_mult: step 9;
- aestronglyMeasurable_orient: step 11;
- orients: step 12.
So R' is an IMRep in U. By construction R'.carrier = ⋃_i (M_i ∩ A_i) and R'.orient = ξ. By definition R'.measure = (Hᵏ⌞M).withDensity θ, which is μ by step 8. ∎

Remark on step 11. In Lean, measurability of ξ on Hᵏ⌞M cannot be obtained from the pieces with aestronglyMeasurable_iUnion_iff. That lemma needs a PseudoMetrizableSpace instance for MultiVector P k = Covector →L[ℝ] ℝ, and in this environment instance synthesis does not find one: the strong topology ContinuousLinearMap.topologicalSpace is not definitionally the metric topology. This is why the hypothesis AEStronglyMeasurable ξ μ is used, as in the supplied proof's step 6(d).

Appendix (verified Lean realization of the numbered proof above). The declaration below compiles with Lean v4.35.0-rc3 and Mathlib 25730c7c (lake env lean in the gmt-ch07 workspace). It was placed after `import GMT.Ch07.Submission` in the child comparator scope, i.e. inside `namespace GMT.Ch07` with the frozen contract's `open` commands (`open Filter Function Set MeasureTheory Metric`, `open scoped ENNReal Topology`, `open Poincare.SimonGMT.Chapter06`, `open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt)`), after the contract's `noncomputable section ... end`. The only non-library declaration it uses is the sibling `Submission.cbrg_ae_orient_iUnion`, with exactly its frozen type. `#print axioms` reports only propext, Classical.choice and Quot.sound.

```lean
theorem Submission.cbrg_imRep_glue_disjoint : (∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) → ∀ (ι : Type) [Countable ι] (P k : ℕ) (U : Set (Euclid P)) (W A : ι → Set (Euclid P)) (R : (i : ι) → IMRep (W i) k) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P k), IsOpen U → (∀ i, IsOpen (W i)) → (∀ i, W i ⊆ U) → (∀ i, MeasurableSet (A i)) → Pairwise (fun i j => Disjoint (A i) (A j)) → μ (⋃ i, A i)ᶜ = 0 → (∀ i, μ.restrict (A i) = (R i).measure.restrict (A i)) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → AEStronglyMeasurable ξ μ → (∀ i, ∀ᵐ y ∂(μHE[k].restrict ((R i).carrier ∩ A i)), ξ y = (R i).orient y) → ∃ R' : IMRep U k, R'.carrier = ⋃ i, (R i).carrier ∩ A i ∧ R'.orient = ξ ∧ R'.measure = μ := by
  classical
  intro hIMC ι _ P k U W A R μ ξ hU hWo hWU hAm hAd hAc hμA hfin hξm hξ
  -- pieces `Nᵢ = Mᵢ ∩ Aᵢ` and multiplicities `mᵢ = θᵢ`
  let N : ι → Set (Euclid P) := fun i => (R i).carrier ∩ A i
  let m : ι → Euclid P → ℕ := fun i => (R i).mult
  -- glued multiplicity: `θ = θᵢ` on `Aᵢ`, `0` off `⋃ Aᵢ`
  let θ : Euclid P → ℕ := fun x => if h : ∃ i, x ∈ A i then m h.choose x else 0
  have hθA : ∀ i, ∀ x ∈ A i, θ x = (R i).mult x := by
    intro i x hx
    have h : ∃ j, x ∈ A j := ⟨i, hx⟩
    have hj : h.choose = i := by
      by_contra hne
      exact (Set.disjoint_left.1 (hAd hne)) h.choose_spec hx
    show (if h' : ∃ j, x ∈ A j then m h'.choose x else 0) = m i x
    rw [dite_eq_left h, hj]
  have hθ0 : ∀ x, (¬ ∃ i, x ∈ A i) → θ x = 0 := by
    intro x hx
    show (if h' : ∃ j, x ∈ A j then m h'.choose x else 0) = 0
    rw [dite_eq_right hx]
  have hNm : ∀ i, MeasurableSet (N i) := fun i => (R i).measurableSet_carrier.inter (hAm i)
  have hMm : MeasurableSet (⋃ i, N i) := MeasurableSet.iUnion hNm
  have hMU : (⋃ i, N i) ⊆ U :=
    iUnion_subset fun i => inter_subset_left.trans ((R i).carrier_subset.trans (hWU i))
  have hθm : Measurable θ := by
    refine measurable_to_countable' fun n => ?_
    have hpre : θ ⁻¹' {n} = (⋃ i, A i ∩ (R i).mult ⁻¹' {n}) ∪ ((⋃ i, A i)ᶜ ∩ {_x | 0 = n}) := by
      ext x
      simp only [mem_preimage, mem_singleton_iff, mem_union, mem_iUnion, mem_inter_iff,
        mem_compl_iff, mem_ofPred_eq]
      constructor
      · intro hx
        by_cases h : ∃ i, x ∈ A i
        · obtain ⟨i, hi⟩ := h
          exact Or.inl ⟨i, hi, by rw [← hθA i x hi]; exact hx⟩
        · exact Or.inr ⟨h, by rw [← hθ0 x h]; exact hx⟩
      · rintro (⟨i, hi, hx⟩ | ⟨h, hn⟩)
        · rw [hθA i x hi]; exact hx
        · rw [hθ0 x h]; exact hn
    rw [hpre]
    refine (MeasurableSet.iUnion fun i =>
      (hAm i).inter ((R i).measurable_mult (measurableSet_singleton n))).union
      ((MeasurableSet.iUnion hAm).compl.inter ?_)
    by_cases hn : 0 = n
    · simp [hn]
    · simp [hn]
  have hθpos : ∀ x ∈ ⋃ i, N i, 0 < θ x := by
    intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.1 hx
    rw [hθA i x hxi.2]
    exact (R i).mult_pos x hxi.1
  have hMrect : CountablyRectifiable k (⋃ i, N i) := by
    rcases isEmpty_or_nonempty ι with hι | hι
    · rw [iUnion_of_empty]
      exact Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero measure_empty
    · obtain ⟨s, hs⟩ := exists_surjective_nat ι
      rw [← hs.iUnion_comp N]
      exact Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion _
        fun n => (R (s n)).rectifiable.mono inter_subset_left
  -- `μ = Σᵢ μ⌞Aᵢ = Σᵢ (θᵢ Hᵏ⌞Mᵢ)⌞Aᵢ`
  have hμsum : μ = Measure.sum (fun i => ((R i).measure).restrict (A i)) := by
    have h1 : μ.restrict (⋃ i, A i) = μ := by
      refine Measure.restrict_eq_self_of_ae_mem ?_
      rw [ae_iff]
      simpa [compl_def] using hAc
    calc μ = μ.restrict (⋃ i, A i) := h1.symm
      _ = Measure.sum (fun i => μ.restrict (A i)) := Measure.restrict_iUnion hAd hAm
      _ = Measure.sum (fun i => ((R i).measure).restrict (A i)) := by
          congr 1
          funext i
          exact hμA i
  -- the measure identity `θ Hᵏ⌞M = μ`
  have hmeas : (μHE[k].restrict (⋃ i, N i)).withDensity (fun x => (θ x : ℝ≥0∞)) = μ := by
    have hNd : Pairwise (fun i j => Disjoint (N i) (N j)) :=
      fun i j hij => (hAd hij).mono inter_subset_right inter_subset_right
    rw [hμsum, Measure.restrict_iUnion hNd hNm, withDensity_sum]
    congr 1
    funext i
    rw [IMRep.measure, restrict_withDensity (hAm i), Measure.restrict_restrict (hAm i),
      inter_comm (A i)]
    refine withDensity_congr_ae ?_
    filter_upwards [ae_restrict_mem (hNm i)] with x hx
    rw [hθA i x hx.2]
  have hlint : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      ∫⁻ x in (⋃ i, N i) ∩ K, (θ x : ℝ≥0∞) ∂μHE[k] ≠ ∞ := by
    intro K hK hKU
    have h1 : ∫⁻ x in (⋃ i, N i) ∩ K, (θ x : ℝ≥0∞) ∂μHE[k] =
        ((μHE[k].restrict (⋃ i, N i)).withDensity (fun x => (θ x : ℝ≥0∞))) K := by
      rw [withDensity_apply _ hK.measurableSet, Measure.restrict_restrict hK.measurableSet,
        inter_comm]
    rw [h1, hmeas]
    exact (hfin K hK hKU).ne
  have hMfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[k] ((⋃ i, N i) ∩ K) ≠ ∞ := by
    intro K hK hKU
    refine ne_top_of_le_ne_top (hlint K hK hKU) ?_
    calc μHE[k] ((⋃ i, N i) ∩ K) = ∫⁻ _ in (⋃ i, N i) ∩ K, (1 : ℝ≥0∞) ∂μHE[k] := by
          rw [setLIntegral_one]
      _ ≤ ∫⁻ x in (⋃ i, N i) ∩ K, (θ x : ℝ≥0∞) ∂μHE[k] := by
          refine setLIntegral_mono (measurable_from_nat.comp hθm) ?_
          intro x hx
          exact_mod_cast hθpos x hx.1
  -- `Hᵏ⌞M ≪ θ Hᵏ⌞M = μ`, so `ξ` is `Hᵏ⌞M`-measurable
  have hac : μHE[k].restrict (⋃ i, N i) ≪ μ := by
    rw [← hmeas]
    refine withDensity_absolutelyContinuous' (measurable_from_nat.comp hθm).aemeasurable ?_
    filter_upwards [ae_restrict_mem hMm] with x hx
    exact_mod_cast (hθpos x hx).ne'
  have hξM : AEStronglyMeasurable ξ (μHE[k].restrict (⋃ i, N i)) := hξm.mono_ac hac
  -- orientation: sibling `cbrg_ae_orient_iUnion`
  have horient := Submission.cbrg_ae_orient_iUnion hIMC ι P k U W N R ξ hU hWo hNm
    (fun i => inter_subset_left) hMU hMfin hξ
  exact ⟨{ carrier := ⋃ i, N i
           mult := θ
           orient := ξ
           measurableSet_carrier := hMm
           carrier_subset := hMU
           rectifiable := hMrect
           measurable_mult := hθm
           mult_pos := hθpos
           locallyIntegrable_mult := hlint
           aestronglyMeasurable_orient := hξM
           orients := horient }, rfl, rfl, hmeas⟩
```

## Key steps

1. Glue θ := θ_i on A_i (unique index by disjointness), 0 off ⋃ A_i; M := ⋃_i (M_i ∩ A_i) is Borel, ⊆ U, countably k-rectifiable; θ is measurable (fibres) and θ ≥ 1 on M.
2. μ = Σ_i μ⌞A_i = Σ_i (R_i.measure)⌞A_i = Σ_i (Hᵏ⌞(M_i ∩ A_i)).withDensity θ = (Hᵏ⌞M).withDensity θ (restrict_iUnion, withDensity_sum, restrict_withDensity, withDensity_congr_ae).
3. Hence ∫_{M∩K} θ dHᵏ = μ(K) < ∞ and Hᵏ(M ∩ K) < ∞ on compacts K ⊆ U; Hᵏ⌞M ≪ μ gives AEStronglyMeasurable ξ (Hᵏ⌞M).
4. Orientation of M by ξ a.e. is the sibling cbrg_ae_orient_iUnion applied to the pieces N_i = M_i ∩ A_i.
5. R' := (M, θ, ξ) is an IMRep in U with R'.carrier = ⋃_i (M_i ∩ A_i), R'.orient = ξ and R'.measure = μ.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); cmp /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean (identical); diff GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `rg -n in /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib for: theorem isOpen_iUnion_countable; protected theorem MeasurableSet.disjointed; theorem iUnion_disjointed; theorem disjoint_disjointed; theorem disjointed_subset; theorem biUnion_range; theorem Countable.exists_eq_range; theorem exists_surjective_nat; theorem iUnion_comp; theorem ae_restrict_iUnion_iff; theorem ae_restrict_of_ae_restrict_of_subset; theorem ae_restrict_iff'; theorem restrict_iUnion; theorem restrict_eq_self_of_ae_mem; theorem restrict_restrict_of_subset; theorem withDensity_sum; theorem restrict_withDensity; theorem withDensity_congr_ae; lemma withDensity_absolutelyContinuous'; lemma mono_ac; theorem measurable_to_countable'; theorem setLIntegral_mono; theorem setLIntegral_one; aestronglyMeasurable_iUnion_iff; PseudoMetrizableSpace instances (Topology/Metrizable/Basic.lean); ContinuousAlternatingMap instNormedAddCommGroup`
- `grep -n in /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean for def CountablyRectifiable, countablyRectifiable_of_measure_zero, CountablyRectifiable.mono, countablyRectifiable_iUnion (ℕ-indexed only), def HasApproximateTangentSpaceAt; sed of Chapter06/Forms.lean (Covector E n := E [⋀^Fin n]→L[ℝ] ℝ)`
- `lake env lean instance probes: #synth NormedAddCommGroup/MetricSpace (MultiVector P k) succeed; #synth TopologicalSpace.PseudoMetrizableSpace (MultiVector P k) fails (strong topology ContinuousLinearMap.topologicalSpace is not defeq to the metric topology)`
- `python3 -I scans of /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json: lean_statements mentioning carrier ∩ K, IsUnitOrientationOf, ⋃, tangent locality, IMRep; status/candidate_commit of rsd_imrep_compact_measure_ne_top, rsdic_imrep_ae_tangent_orient_of_subset, fvmb_imrep_ae_unitOrientation_approxTangentPlane, regcomp_approx_tangent_locality, rsdic_ae_tangent_iff_of_subset, dtc_approxTangent_of_null_diff; cross-branch dependency count (240 edges); lean_name collision scan for cbrg_exists_countable_disjoint_refinement, cbrg_ae_orient_iUnion, cbrg_imRep_glue_disjoint, rsd_imrep_compact_measure_ne_top (re-run at 981 nodes); exact-type equality of the selected node, cbr_imRep_measure_basic and rsd_imrep_compact_measure_ne_top`
- `git show 702e7082a5a7012f7a8f6efd9d272697e426f50b:GMT/Ch07/Submission.lean (theorem Submission.rsd_imrep_compact_measure_ne_top with the frozen type) and its accepted parent-child-handoff.json`
- `sed of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_existing_lean_name_problem, _accepted_checkpoint, _install_parent_supplied_child_handoff, child id mapping by lean_name) and store.py ensure: accepted same-type declarations are reused by name and left untouched`
- `lake env lean /tmp/glue-decomp/Types.lean, Assembly.lean, Children2.lean, Final.lean, Appendix.lean; python3 -I /tmp/glue-decomp-scripts/lexcheck.py, extract_check.py, final_checks.py (validate_lean_statement from /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py)`
- `sed -n 733,753p and 2305,2320p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt (Simon 6.3.1 Definition; Remark 8.3(1)); web: Simon, Introduction to GMT (public copy https://web.stanford.edu/class/math285/ts-gmt.pdf), Ch. 3 §1 and Ch. 6 §3`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Disjointed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Countable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Lattice/Image.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Lattice/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/Countable/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Metrizable/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-f6cee6c8d7/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1-imrep-local-finiteness-a1/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/store.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/glue-decomp/Types.lean`
- `/tmp/glue-decomp/Assembly.lean`
- `/tmp/glue-decomp/Children2.lean`
- `/tmp/glue-decomp/Final.lean`
- `/tmp/glue-decomp/Appendix.lean`

The snapshot contract is byte-identical to the workspace Contract.lean and Submission.lean. Neither the Mathlib snapshot, SimonGMT nor the DAG contains a countable disjoint refinement of a local cover, an orientation-locality lemma for countable unions of IMRep pieces, or an IMRep gluing lemma (no match); these are the three new children. Local finiteness of IMRep carriers is the accepted rsd_imrep_compact_measure_ne_top (candidate 702e7082), reused with its identical frozen type. Unconditional tangent-locality declarations also exist (regcomp_approx_tangent_locality, rsdic_ae_tangent_iff_of_subset, rsdic_imrep_ae_tangent_orient_of_subset). They are not needed, because the selected node carries (IMC)(a) as a hypothesis and the children pass it on. Every cited Mathlib name exists in the pinned snapshot. SimonGMT countablyRectifiable_iUnion is ℕ-indexed, so glue_pieces reindexes through exists_surjective_nat. aestronglyMeasurable_iUnion_iff is unusable for MultiVector P k: no PseudoMetrizableSpace instance is synthesized, because the strong topology of Covector →L[ℝ] ℝ is not definitionally the metric topology. glue_pieces therefore uses AEStronglyMeasurable ξ μ and Hᵏ⌞M ≪ μ, as in the supplied step 6(d). All child types elaborate and pass the lexical check. A hypothesis-only Lean proof derives the exact frozen parent type from the child types and cbr_imRep_measure_basic's type. Every child is fully proved in Lean from its declared dependencies. All of these checks use only the axioms propext, Classical.choice and Quot.sound.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
