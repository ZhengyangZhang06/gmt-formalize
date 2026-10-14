<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1 -->

## Theorem `Submission.dimred_mbl_deformation_theorem`

For all P, m ∈ ℕ (degree n := m + 1) there is a constant c ∈ ℝ≥0 with c ≥ 1 such that for every ρ > 0, every compact K ⊆ ℝ^P and every Λ ∈ ℝ≥0 there is a finite set 𝒬 of currents in 𝒟_n(ℝ^P) with the following property. If T ∈ 𝒟_n(ℝ^P) is integer multiplicity, spt T ⊆ K, M(T) ≤ Λ and M(∂T) < ∞, then there are Q ∈ 𝒬, R ∈ 𝒟_{n+1}(ℝ^P) and S ∈ 𝒟_n(ℝ^P) such that: Q, ∂Q and R are integer multiplicity; T − Q − S = ∂R; Q = 0 or M(Q) ≥ ρⁿ; M(Q) ≤ c·M(T), M(∂Q) ≤ c·M(∂T), M(R) ≤ c·ρ·M(T) and M(S) ≤ c·ρ·M(∂T); spt Q ∪ spt R ⊆ thickening(3√P·ρ, spt T) and spt ∂Q ∪ spt S ⊆ thickening(3√P·ρ, spt ∂T), where thickening(r, A) := {x : |x − y| < r for some y ∈ A} (Mathlib Metric.thickening; it is empty when A = ∅). Here M := massOn ℝ^P is the total mass (GeometricCurrentOn.mass, with the Euclidean coefficient norm), masses and products are read in [0, ∞], and spt is the support of Simon 6.2.11 (GeometricCurrentOn.support). Nothing beyond these properties is asserted about Q: in particular the statement does not assert that Q is a polyhedral chain (that is only a feature of the construction used in the proof).

Node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1022

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/810, https://github.com/ZhengyangZhang06/gmt-formalize/issues/667, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5014, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5023

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5845, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5864, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5882, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5898, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5912, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5920, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5939, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5955

## Lean problem

Declaration: `Submission.dimred_mbl_deformation_theorem`

```lean
∀ (P m : ℕ), ∃ c : NNReal, 1 ≤ c ∧ ∀ (ρ : ℝ) (K : Set (Euclid P)) (Λ : NNReal), 0 < ρ → IsCompact K → ∃ 𝒬 : Set (GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), 𝒬.Finite ∧ ∀ T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), IsIntegerMultiplicity T → T.support ⊆ K → T.mass ≤ Λ → T.boundary.mass < ∞ → ∃ Q ∈ 𝒬, ∃ (R : GeometricCurrentOn (univ : Set (Euclid P)) (m + 2)) (S : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), IsIntegerMultiplicity Q ∧ IsIntegerMultiplicity Q.boundary ∧ IsIntegerMultiplicity R ∧ T - Q - S = R.boundary ∧ (Q = 0 ∨ ENNReal.ofReal (ρ ^ (m + 1)) ≤ Q.mass) ∧ Q.mass ≤ c * T.mass ∧ Q.boundary.mass ≤ c * T.boundary.mass ∧ R.mass ≤ c * ENNReal.ofReal ρ * T.mass ∧ S.mass ≤ c * ENNReal.ofReal ρ * T.boundary.mass ∧ Q.support ∪ R.support ⊆ thickening (3 * Real.sqrt P * ρ) T.support ∧ Q.boundary.support ∪ S.support ⊆ thickening (3 * Real.sqrt P * ρ) T.boundary.support
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
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 6 §5 (5.1,5.3,5.4 = Lemma D, proof (1)–(38)). Erratum: the printed |y−a|≥3/4 in the proof of 5.4 is corrected to |y−a|≥1/4 (a∈B_{1/4}(q),y∈∂C); only constants change.
Conventions. n:=m+1≥1; IM: integer multiplicity; Lip: Lipschitz; M(X):=X.mass; |α|: Euclidean coefficient norm, |ω|_∞:=sup|ω(x)|,|ζ|:=sup{⟨α,ζ⟩:|α|≤1} for k-vectors; X+Y:=X−(0−Y); U_r(A):=⋃_{y∈A}B̄_r(y) (U_r(∅)=∅). The zero current is IM (IMRep (∅,0,0); ∅ is Borel and null, so countably rectifiable). Siblings: vanish_off_support (VO), mass_and_support (MR), foundations (REP) (μ_X,ξ_X: μ_X(G)=M_G(X),|ξ_X|≤1) and (IMC), slicing (SL). For spt X compact, M(X)<∞: μ_X is finite, μ_X(ℝ^P∖spt X)=0 ((VO),(REP)),|X(ω)|≤∫|ω|dμ_X, and for bounded Borel g (e.g. 1_B) X⌞g(ω):=∫gξ_X(ω)dμ_X is a current (μ_X finite) of mass ≤∫|g|dμ_X; for IM X,X⌞B is the (IMC)(b) restriction (same vector measure on test forms, hence on bounded Borel functions).
(L0) For a k-covector β,k!|β|²=Σ_{i_1,…,i_k}β(e_{i_1},…,e_{i_k})²=:‖β‖²_HS (each increasing tuple occurs k! times up to sign, tuples with repeats vanish); ‖·‖_HS (Hilbert–Schmidt norm), hence |·| and the dual norm on k-vectors, are orthogonally invariant. (L1) |A^#β|≤‖A‖^k|β|, dually |Λ_kAζ|≤‖A‖^k|ζ| (⟨β,Λ_kAζ⟩:=⟨A^#β,ζ⟩), for linear A: by (L0) bound ‖·‖_HS; replacing one slot of a multilinear form γ by A multiplies ‖γ‖_HS by ≤‖A‖ (for fixed other arguments Σ_iγ(Ae_i,…)²=|Aᵀg|²≤‖A‖²|g|², g representing γ(·,…)); do this k times. (L2) |β'∧γ|≤|β'||γ| for a 1-covector β' (by (L0) rotate: β'=|β'|e¹, β'∧γ=|β'|Σ_{I∌1}γ_Ie¹∧e^I); likewise |ι_vβ|≤|v||β| (v=|v|e_1, ι_vβ=|v|Σ_{I∋1}±β_Ie^{I∖{1}}); so |v∧ζ|≤|v||ζ| (⟨β,v∧ζ⟩:=⟨ι_vβ,ζ⟩). (L3) |τ_1∧⋯∧τ_k|=1 for orthonormal τ_i (rotate: τ_i=e_i, and ⟨α,e_1∧⋯∧e_k⟩=α(e_1,…,e_k) is a coefficient of α); for linear A:ℝᵏ→ℝ^P,e:=e_1∧⋯∧e_k: if A is injective, A=OS (S:=(AᵀA)^{1/2},O:=AS⁻¹ isometric) and Λ_kA(e)=Λ_kO(det S·e)=det S·Oe_1∧⋯∧Oe_k, so |Λ_kA(e)|=det S=√det(AᵀA)=:JA and Λ_kA(e)/JA is a unit simple k-vector orienting A(ℝᵏ); else Λ_kA(e)=0=JA; unit simple k-vectors orienting the same plane differ by a sign (orthonormal changes of basis have determinant ±1).
Part A (X: compactly supported k-current).
A1. For C^∞ F:ℝ^P→ℝ^Q,(F^#ω)(x)(v_1,…,v_k):=ω(F(x))(DF(x)v_1,…,DF(x)v_k),F_#X(ω):=X(ζF^#ω),ζ∈C_c^∞,ζ=1 near spt X (ζ irrelevant by (VO)): a current (chain, Leibniz rules), ∂F_#X=F_#∂X (dF^#=F^#d; X(dζ∧F^#ω)=0 by (VO)), spt F_#X⊆F(spt X). If M(X)<∞,F_#X(ω)=∫⟨ω(F(x)),Λ_kDF(x)ξ_X(x)⟩dμ_X, so M(F_#X)≤∫‖DF‖^kdμ_X≤sup_{spt X}‖DF‖^k·M(X) (L1).
A2. On ℝ×ℝ^P (points (t,x),e₀:=∂_t), for a (k+1)-form ω let ω₁(t,x)(v_1,…,v_k):=ω(t,x)(e₀,(0,v_1),…,(0,v_k)),ω₀ the dt-free part; with 𝕀:=[[0,1]],(𝕀×X)(ω):=X(∫_0^1ω₁(t,·)dt),({s}×X)(ω):=X(i_s^#ω), i_s(x):=(s,x), are compactly supported currents. ω=dt∧ω₁+ω₀,d(dt∧ω₁)=−dt∧d_xω₁,dω₀=dt∧∂_tω₀+d_xω₀ ⇒ (dω)₁=∂_tω₀−d_xω₁; integrating in t (d_x commutes with ∫dt): ∂(𝕀×X)={1}×X−{0}×X−𝕀×∂X (no last term if k=0). If M(X)<∞: (𝕀×X)(ω)=∫_0^1∫⟨ω(t,x),e₀∧ξ_X(x)⟩dμ_Xdt,M(𝕀×X)≤M(X).
A3. For C^∞ F,G and H(t,x):=F(x)+t(G(x)−F(x)),A2 (∂H_#=H_#∂,H∘i_1=G,H∘i_0=F) gives G_#X−F_#X=∂H_#(𝕀×X)+H_#(𝕀×∂X) (no last term if k=0). If M(X)<∞: DH(t,x)e₀=(G−F)(x),DH(t,x)(0,v)=((1−t)DF+tDG)(x)v, so Λ_{k+1}DH(e₀∧ζ)=(G−F)(x)∧Λ_k((1−t)DF+tDG)(x)ζ and by (L1),(L2) M(H_#(𝕀×X))≤∫|G−F|(‖DF‖+‖DG‖)^kdμ_X≤sup_{spt X}|G−F|·sup_{spt X}(‖DF‖+‖DG‖)^k·M(X).
A4. Let M(X)+M(∂X)<∞ (k≥1; for k=0 drop ∂X terms), F Λ-Lip,F_σ:=F∗φ_σ (C^∞,‖DF_σ‖≤Λ,F_σ→F uniformly), K(ω):=(2Λ)^kM(X)|dω|_∞+(2Λ)^{k−1}M(∂X)|ω|_∞. By A3,|(F_σ)_#X(ω)−(F_τ)_#X(ω)|≤sup|F_σ−F_τ|K(ω)→0, so F_#X(ω):=lim_{σ↓0}(F_σ)_#X(ω) exists. (a) |F_#X(ω)|≤Λ^kM(X)|ω|_∞: F_#X is a current, M(F_#X)≤Λ^kM(X). (b) ∂F_#X=F_#∂X. (c) For smooth F it is A1's (DF_σ→DF locally uniformly). (d) spt F_#X⊆F(spt X) (A1 for F_σ; F_σ→F uniformly). (e) F,G Λ-Lip,|F−G|≤δ on spt X ⇒ |F_#X(ω)−G_#X(ω)|≤δK(ω) (limit of A3); so F_#X depends only on F|spt X, and for ψ Lip on a closed A⊇spt X,ψ_#X:=ψ̃_#X is well defined for any Lip extension ψ̃ of ψ|A (componentwise McShane, constant ≤√Q·Lip(ψ|A)), linear in X among currents supported in A. (f) For Lip F,G with G−F bounded, A3 holds with H(t,x):=F(x)+t(G−F)(x) (t clamped to [0,1]) and Lip F+Lip G for sup(‖DF‖+‖DG‖) (exponent k−1 for ∂X): apply A3 to F_σ,G_σ with t replaced by a bounded smooth s, s(t)=t on [−1,2] (only [0,1]×spt X matters), and pass to the limit by (e) in ℝ×ℝ^P (uniformly Lip, uniformly convergent) and lower semicontinuity of mass.
Part B. X=τ(M,θ,ξ) IM,k≥1, spt X compact, M(∂X)<∞; by (MR),(IMC) take M⊆spt X, so Hᵏ(M)≤∫_Mθ dHᵏ=M(X)<∞. Lᵏ: Lebesgue measure; Hᵏ=μHE[k].
B1. There are countably many compact A_i⊆ℝᵏ, Lip G_i:ℝᵏ→ℝ^P,κ_i>0 with G_i differentiable, DG_i injective on A_i,|G_i(u)−G_i(v)|≥κ_i|u−v| on A_i,G_i(A_i)⊆M disjoint, Hᵏ(M∖⋃G_i(A_i))=0; given open O with Hᵏ(M∖O)=0 and countably many compacts whose interiors cover O, each G_i(A_i) can lie in one of them (run it on M∩O).
M⊆M₀∪⋃_jF_j(ℝᵏ),Hᵏ(M₀)=0,F_j Lip. Remove the non-differentiability set of F_j and Z_j:={DF_j not injective}, whose images are Hᵏ-null (Rademacher, Lip images of null sets; area formula); let E_j⊆F_j^{-1}(M) be the Borel rest. With r(A):=1/(2K_A),|Au|≥|u|/K_A, for injective A (else 1), exists_partition_approximatesLinearOn_of_hasFDerivWithinAt covers E_j by disjoint Borel E_j∩t_l with |F_j(u)−F_j(v)−A_l(u−v)|≤r(A_l)|u−v|,A_l=DF_j(y_l), y_l∈E_j, so |F_j(u)−F_j(v)|≥(2K_{A_l})⁻¹|u−v| there. Intersect pieces (E_i,G_i,κ_i) with preimages of the given compacts, disjointify, E'_i:=E_i∖G_i^{-1}(⋃_{i'<i}G_{i'}(E'_{i'})) (Borel: Lusin–Souslin), and split each E'_i up to an Lᵏ-null set (Hᵏ-null image) into countably many disjoint compacts (inner regularity).∎
B2. If A⊆ℝᵏ is compact, G:ℝᵏ→ℝ^P Lip, differentiable on A, |G(u)−G(v)|≥κ|u−v| on A (κ>0), then for Lᵏ-a.e. u∈A,V:=DG(u)(ℝᵏ) is k-dimensional and HasApproximateTangentSpaceAt k (G(A)) (G(u)) V.
At a density point u of A that is a Lebesgue point of 1_A·JG (JG:=√det(DGᵀDG)), points v∈A with v−u=rw/|w|+o(r) give |DG(u)w|≥κ|w|, so JG(u)>0; for x:=G(u),f∈C_c(B_ρ(0)), scaling and injective area formula give ∫_{η_{x,r}(G(A))}f dHᵏ=∫1_A(u+rw)f((G(u+rw)−G(u))/r)JG(u+rw)dw (integrand 0 off B_{ρ/κ}) →∫f(DG(u)w)JG(u)dw=∫_Vf dHᵏ (differentiability at u; 1_A(u+r·)→1,1_A(u+r·)JG(u+r·)→JG(u) in L¹; area formula); finrank V=k.∎
Hence ((IMC)(a); G_i bi-Lip on A_i, so null sets correspond) the approximate tangent space T_{G_i(u)}M is DG_i(u)(ℝᵏ) for a.e. u∈A_i, oriented by ξ, so (L3) gives:
(B2′) ξ(G_i(u))=s_i(u)Λ_kDG_i(u)(e)/JG_i(u), s_i(u)∈{±1} Borel.
B3. Let O⊆ℝ^P be open, Hᵏ(M∖O)=0,F:O→ℝ^Q locally Lip; take B1 with each G_i(A_i) in a compact subset of O where F is Lip, so H_i:=F∘G_i is Lip near A_i; for a.e. u∈A_i,d^MF(G_iu):=DH_i(u)∘DG_i(u)^{-1}:T_{G_iu}M→ℝ^Q (Rademacher); J^MF:=|Λ_k(d^MF)ξ|≤‖d^MF‖ᵏ (L1). If I_F:=∫_MJ^MFθ dHᵏ<∞, then Φ_F(ω):=∫_Mθ⟨ω(F(x)),Λ_k(d^MF(x))ξ(x)⟩dHᵏ(x) is an IM current, M(Φ_F)≤I_F.
|Φ_F(ω)|≤|ω|_∞I_F: continuity, mass bound. Area formula, (B2′) and chain rule Λ_k(d^MF)Λ_kDG_i(e)=Λ_kDH_i(e) give, with θ_i:=θ∘G_i,
(★) Φ_F(ω)=Σ_i∫_{A_i}θ_is_i(H_i^#ω)(e), absolutely convergent: Σ_i∫_{A_i}θ_iJH_i=:I'_F≤I_F (JH_i:=|Λ_kDH_i(e)|=J^MF(G_i)JG_i).
Λ_kDH_i(e)=0 where DH_i is not injective; split {u∈A_i: DH_i(u) exists, injective}, up to a null set, as in B1 into compact A_{il} with |H_i(u)−H_i(v)|≥κ_{il}|u−v|; N_{il}:=H_i(A_{il}),g_{il}:=(θ_is_i)∘(H_i|A_{il})^{-1}∈ℤ∖{0},η_{il}:=(Λ_kDH_i(e)/JH_i)∘(H_i|A_{il})^{-1} (unit simple, (L3)). Injective area formula: Φ_F(ω)=Σ_{il}∫_{N_{il}}g_{il}⟨ω,η_{il}⟩dHᵏ,Σ_{il}∫_{N_{il}}|g_{il}|dHᵏ=I'_F, so N:=⋃N_{il} has Hᵏ(N)≤I'_F. By B2,(IMC)(a), for Hᵏ-a.e. y∈N and all (i,l) with y∈N_{il},T_yN=DH_i(u)(ℝᵏ), so η_{il}(y)=±η(y),η(y):=η_{il}(y) for the first such (i,l) (L3); a.e. y lies in finitely many N_{il} (Σ|g_{il}|1_{N_{il}}∈L¹). So Σg_{il}1_{N_{il}}η_{il}=mη,m(y)∈ℤ,Φ_F(ω)=∫_Nm⟨ω,η⟩dHᵏ (dominated convergence). With N':={m≠0} minus a Borel null set off which this holds and m,η are Borel, (N',|m|,sign(m)η) is an IMRep representing Φ_F: N' Borel, countably k-rectifiable (⊆⋃H_i(A_{il}),H_i extended Lip), |m|≥1,∫|m|≤I'_F, Borel orientation orienting T_yN'=T_yN a.e. ((IMC)(a): N'⊆N,Hᵏ(N)<∞).∎
B4. For Λ-Lip F:ℝ^P→ℝ^Q,F_#X=Φ_F (O=ℝ^P), so F_#X is IM and Φ_F is parametrization-independent. Hence (A4(e),B5) for IM Y with compact support, M(∂Y)<∞,ψ Lip on a closed A⊇spt Y and h(t,x):=x+t(ψ(x)−x),ψ_#Y and h_#(𝕀×Y) are IM and equal Φ_ψ(Y),Φ_h(𝕀×Y) (any parametrization).
Lemma (weak continuity of Jacobians): if H_σ,H:ℝᵏ→ℝ^Q are Lip near a compact A, sup_σLip H_σ<∞ and H_σ→H uniformly there, then ∫_Aw(H_σ^#ω)(e)→∫_Aw(H^#ω)(e) (ω∈𝒟ᵏ(ℝ^Q),w∈L¹(A)). As (H^#ω)(e)=Σ_Jω_J(H)det D(H^{j_1},…,H^{j_k}) is uniformly bounded, by density of C_c^∞ in L¹ we may take w∈C_c^∞; as ω_J(H_σ)→ω_J(H) uniformly, it suffices that ∫c det Dv_σ→∫c det Dv for continuous compactly supported c and Lip v_σ→v uniformly with bounded constants. This is the case r=k,β=c of: ∫β∧dv_σ^1∧⋯∧dv_σ^r→∫β∧dv^1∧⋯∧dv^r for every continuous compactly supported (k−r)-form β, shown by induction on r (r=0 trivial). For smooth β, with R_σ:=dv_σ^2∧⋯∧dv_σ^r (R likewise for v), by parts ∫β∧dv_σ^1∧R_σ=±∫v_σ^1dβ∧R_σ (valid for Lip v by mollifying v: the a.e. derivative of a Lip function is its weak derivative, so D(v∗φ_δ)=(Dv)∗φ_δ→Dv a.e. and boundedly), and ∫v_σ^1dβ∧R_σ−∫v^1dβ∧R=∫(v_σ^1−v^1)dβ∧R_σ+∫v^1dβ∧(R_σ−R)→0 by uniform convergence and the induction hypothesis for the continuous form v^1dβ; continuous β by uniform approximation and the uniform bounds.
Now (F_σ)_#X(ω)=∫_Mθ⟨ω(F_σ),Λ_kDF_σξ⟩dHᵏ (A1), i.e. (★) with H_{i,σ}:=F_σ∘G_i for H_i. By the lemma (w=θ_is_i1_{A_i}∈L¹ as JG_i≥κ_iᵏ on A_i) term i tends to that of (★), and it is ≤|ω|_∞Λᵏ∫_{G_i(A_i)}θ dHᵏ (summable), so by dominated convergence (F_σ)_#X(ω)→Φ_F(ω). As F_#X is parametrization-free, so is Φ_F.∎
B5. 𝕀×X=τ((0,1)×M,θ∘pr,e₀∧ξ) is IM in ℝ×ℝ^P (≅Euclid (P+1) by a linear isometry, which transports IM-ness, masses, supports), M(𝕀×X)=M(X),M(∂(𝕀×X))≤2M(X)+M(∂X).
Hᵏ(Z)=0 ⇒ H^{k+1}(I×Z)=0 for bounded intervals I (cover Z by C_j, diam C_j<1,Σ(diam C_j)ᵏ<ε, and I×C_j by ⌈|I|/diam C_j⌉ sets of diameter ≤√2 diam C_j: Σdiam^{k+1}≤c(|I|+1)ε); so null parts of M and M∖⋃G_i(A_i) do not matter. Ĝ_i(t,u):=(t,G_i(u)) is injective, bi-Lip on [0,1]×A_i (constant min(1,κ_i)), differentiable, JĜ_i=JG_i; so H^{k+1}⌞((0,1)×G_i(A_i))=L¹⌞(0,1)⊗Hᵏ⌞G_i(A_i) (area formula), [0,1]×G_i(A_i) has a.e. approximate tangent space ℝe₀⊕DG_i(u)(ℝᵏ) (B2), and by (IMC)(a) so does (0,1)×M, oriented by unit simple e₀∧ξ. Fubini, A2: ∫_{(0,1)×M}θ⟨ω,e₀∧ξ⟩dH^{k+1}=∫_0^1∫_Mθ⟨ω₁(t,·),ξ⟩dHᵏdt=(𝕀×X)(ω). Other fields are immediate; mass bounds: A2.∎
C1. Let Q₁:=(0,1)ⁿ,u∈L¹(Q₁),V:=sup{∫_{Q₁}u div g: g∈C_c^∞(Q₁;ℝⁿ),|g|≤1}<∞. Then (i) ∫_{Q₁}|u−β|≤c_nV for each median β of u (Lⁿ{u≥β},Lⁿ{u≤β}≥1/2); (ii) Y:=u[[Q₁]] (Y(a dy):=∫_{Q₁}ua) has M(∂Y)≤c_n(V+∫_{Q₁}|u|).
For 0<σ<δ<1/8,Q_δ:=(δ,1−δ)ⁿ,u_σ:=u∗φ_σ is smooth near closure Q_δ and ∫_{Q_δ}|∇u_σ|≤V (Fubini: ∫∇u_σ·g=−∫u div(φ̌_σ∗g),φ̌_σ∗g∈C_c^∞(Q₁;ℝⁿ),|φ̌_σ∗g|≤1, for g∈C_c^∞(Q_δ;ℝⁿ),|g|≤1). For v∈C¹ on a closed cube Q' of side s∈[1/2,1]: ∫∫|v(x)−v(y)|≤2^{n+1}√n s^{n+1}∫|∇v| (integrate |v(x)−v(y)|≤∫_0^1|∇v(x+t(y−x))||y−x|dt over Q'×Q', substituting z=x+t(y−x) in x if t≤1/2, in y if t≥1/2, Jacobian ≥2^{−n}), so ∫_{Q'}|v−v_{Q'}|≤2^{n+1}√n∫_{Q'}|∇v|; and ∫_{x₁=δ}|v|≤2∫_{Q_δ}|v|+∫_{Q_δ}|∇v| (average |v(δ,x')|≤|v(x₁,x')|+∫|∂₁v(t,x')|dt over x₁, a length ≥1/2), so ∫_{∂Q_δ}|v|≤2n(2∫_{Q_δ}|v|+∫_{Q_δ}|∇v|). For v=u_σ,σ↓0 (continuity of translations in L¹) then δ↓0 (u_{Q_δ}→u_{Q₁}, monotone convergence) give ∫_{Q₁}|u−u_{Q₁}|≤2^{n+1}√nV; (i): medians minimize c↦∫|u−c|. (ii) For γ=Σg_jε_j,|g|≤1 (ε_j:=(−1)^{j−1}dy¹∧⋯∧dy^{j−1}∧dy^{j+1}∧⋯∧dyⁿ,dγ=(div g)dy), the divergence theorem gives |∂(u_σ[[Q_δ]])(γ)|=|∫_{Q_δ}u_σ div g|≤∫_{Q_δ}|∇u_σ|+∫_{∂Q_δ}|u_σ|≤(2n+1)V+4n∫_{Q_δ}|u_σ|; as δ↓0,σ=σ(δ)↓0,u_σ1_{Q_δ}→u1_{Q₁} in L¹, so u_σ[[Q_δ]]⇀Y and lower semicontinuity of mass gives M(∂Y)≤(2n+1)V+4n∫_{Q₁}|u|.∎
C2. For integer-valued u,β:=min{c∈ℤ: Lⁿ{u≤c}≥1/2} is a median, |β|≤2∫_{Q₁}|u| (β>0 ⇒ Lⁿ{u≥β}≥1/2 ⇒ ∫|u|≥β/2; β<0 likewise), and β=c if u=c a.e.
Part D. Unit grid: ℓ:=P−n≥1 (ℓ=0: E0),C:=[0,1]^P,q:=(1/2,…,1/2),L_j: j-skeleton,S_1,…,S_N (N:=binom(P,n+1)) the (n+1)-dimensional coordinate subspaces, p_j: orthogonal projection onto S_j,F_j:=C∩S_j, x_j:=p_j(q). For a∈B_{1/4}(q): L*(a):=⋃_j⋃_{z∈ℤ^P∩S_j}p_j^{-1}(p_j(a)+z)=a+L_{ℓ−1} (L_{ℓ−1}: points with ≥n+1 integer coordinates), L*(a;ρ):={dist(·,L*(a))<ρ}=⋃_j⋃_zp_j^{-1}(B_ρ(p_j(a)+z)); dist(L*(a),L_n)≥1/4 (points of L_n have ≥ℓ integer coordinates, of L*(a) ≥n+1 in a+ℤ⊆(1/4,3/4)+ℤ; n+1+ℓ>P).
Lemma D. There is ψ:ℝ^P∖L*(a)→L_n with ψ=id on L_n,ψ(z+x)=z+ψ(x) (z∈ℤ^P),ψ(z+C∖L*(a))⊆z+C (so |ψ(x)−x|≤√P),D̄ψ(x):=limsup_{y→x}|ψ(y)−ψ(x)|/|y−x|≤c₁/d(x),d:=dist(·,L*(a)),c₁=c₁(n,P); so ψ is c₂/ρ-Lip on {d≥ρ} for 0<ρ≤1/4,c₂:=2c₁+8√P+1.
For a j-face F of C,j≥n+1, let a_F be the orthogonal projection of a to aff(F) (a_F∈F: its free coordinates are a's, in (1/4,3/4)),ψ_F:F∖{a_F}→∂F the radial retraction from a_F. As translated faces get translated a_F,ψ^{(j)}:=⋃_Fψ_F (j-faces F) is a well defined continuous map ⋃_F(F∖{a_F})→(j−1)-skeleton. (1) L*(a)∩F=⋃_{ℓ'∈J_F}p_{ℓ'}^{-1}(p_{ℓ'}(a))∩F,J_F:={ℓ': S_{ℓ'} spanned by n+1 free coordinates of F}: p_{ℓ'}^{-1}(p_{ℓ'}(a)+z) meets F only if its n+1 prescribed coordinates are free for F (fixed ones are 0 or 1∉a_i+ℤ), and then z=0 there; these planes contain a_F (a_F−a ⊥ free directions). So L*(a)∩F is a cone with vertex a_F,ψ_F(F∖L*(a))⊆∂F∖L*(a),ψ₀:=ψ^{(n+1)}∘⋯∘ψ^{(P)} maps C∖L*(a) to C∩L_n (id on C∩L_n), and ψ(z+x):=z+ψ₀(x) is well defined on ℝ^P∖L*(a). D̄ψ, by induction on ℓ. ℓ=1: L*(a)∩C={a},ψ is the radial projection from a to ∂C,D̄ψ(x)≤c/|x−a|≤c/d(x) (|y−a|≤√P on ∂C). ℓ≥2: for x∈int C∖L*(a) let y:=ψ^{(P)}(x)∈∂C,F a (P−1)-face of C containing y,p_F: orthogonal projection to aff(F) (p_F(a)=a_F),L:=L*(a)∩aff(F), by (1) the dual skeleton of the cube F centred at a_F (codimension ℓ−1); L=L₀∪L₁,L₀ the planes through a_F (those of (1)),L₁ the other (translated) ones, each at distance ≥1/4 from F (a prescribed a_i+z_i, z_i≠0, is ≥1/4 from [0,1]). Now y−a=λ(x−a),λ:=|y−a|/|x−a|, and p_F^{-1}(L₀) is a cone with vertex a inside L*(a) (L₀ plus normal lines of F; the one through a lies in some p_{ℓ'}^{-1}(p_{ℓ'}(a)) as n+1≤P−1), so dist(y,L₀)=dist(y,p_F^{-1}(L₀))=λdist(x,p_F^{-1}(L₀))≥λd(x); as λd(x)≤|y−a|≤√P,dist(y,L)≥min(λd(x),1/4)≥λd(x)/(4√P). Induction for ψ̃:=ψ^{(n+1)}∘⋯∘ψ^{(P−1)} on F: D̄ψ̃(y)≤c/dist(y,L)≤4√Pc|x−a|/(|y−a|d(x))≤16√Pc|x−a|/d(x) (|y−a|≥1/4); with D̄ψ^{(P)}(x)≤c'/|x−a| and chain rule for upper Lip constants, D̄ψ(x)≤D̄ψ̃(y)D̄ψ^{(P)}(x)≤c₁/d(x). ∂C, other cubes: periodicity (same estimate per closed cube). Finally, for x,y∈{d≥ρ}: if |x−y|<ρ/2,[x,y]⊆{d≥ρ/2} where D̄ψ≤2c₁/ρ, so |ψ(x)−ψ(y)|≤(2c₁/ρ)|x−y|; else |ψ(x)−ψ(y)|≤2√P+|x−y|≤(4√P/ρ+1)|x−y|≤(c₂/ρ)|x−y|.∎
E0. If n>P, all n- and (n+1)-currents vanish (no nonzero covectors): T=0; Q=R=S=0,𝒬:={0} work. If T=0: Q=R=S=0. μ_T:=IMRep.measure of an IMRep of T, which is the (REP) measure (by (MR),(REP) both are locally finite Borel measures with μ(G)=M_G(T) for open G). Let n≤P. It suffices to prove (U): for some c=c(n,P), each IM T with compact support and M(∂T)<∞ has T−P=∂R+S,P=Σ_Fβ_F[[F]] (n-faces F of the unit grid, β_F∈ℤ, finitely many ≠0),P,∂P,R IM,M(P),M(R)≤cM(T),M(∂P),M(S)≤cM(∂T), spt P∪spt R⊆U_{2√P}(spt T), spt ∂P∪spt S⊆U_{2√P}(spt ∂T). Indeed, for δ_ρ(x):=ρ⁻¹x,δ_{ρ#} (affinePushforward) preserves IM (carrier δ_ρ(M), same θ,ξ; approximate tangent spaces commute with dilations), scales k-masses by ρ^{−k} and supports by ρ⁻¹, commutes with ∂; (U) for δ_{ρ#}T, pushed back by δ_{1/ρ}, gives M(Q)=ρⁿM(P)≤cM(T),M(R)=ρ^{n+1}M(R')≤cρM(T),M(S)=ρⁿM(S')≤ρⁿcρ^{1−n}M(∂T)=cρM(∂T),M(∂Q)≤cM(∂T), supports within 2√Pρ<3√Pρ. By construction (not asserted) Q=δ_{1/ρ#}P=Σ_Fβ_F[[ρF]] ([[G]](ω):=∫_G⟨ω,e_G⟩dHⁿ,e_G as in E7(d); δ_{1/ρ#}[[F]]=[[ρF]]: δ_{1/ρ}(F)=ρF,(δ_{1/ρ}^#ω)(x)=ρⁿω(ρx),Hⁿ(ρA)=ρⁿHⁿ(A)), so Q≠0 ⇒ M(Q)=ρⁿΣ|β_F|≥ρⁿ (E7(e)). For K':=U_{3√Pρ}(K) (compact),𝒬:={0}∪{Σβ_G[[G]]: G among finitely many n-faces of the ρ-grid in K',β_G∈ℤ,ρⁿΣ|β_G|≤cΛ} is finite (finitely many faces, finitely many integer vectors of bounded ℓ¹-norm), independent of T, and contains Q when spt T⊆K,M(T)≤Λ (T=0 ⇒ Q=0; else each ρF with β_F≠0 lies within (√P+√n)ρ≤2√Pρ of spt T (E7(e)), so in K', and ρⁿΣ|β_F|=M(Q)≤cΛ); c:=max(1, constants of E1–E8) depends only on n,P. For n=P (ℓ=0),Q₀:=T,R₁:=S₁:=0 satisfy (21),(24),(25) (c=1), spt Q₀=spt T, spt ∂Q₀=spt ∂T and E6 (L_n=ℝ^P; the Hⁿ-null L_{n−1} carries no μ_{Q₀}-mass); go to E7–E8. Else ℓ≥1: E1–E8.
E1. Fix β=β(n,P)>0 with 2N·5^{n+1}ω_{n+1}β⁻¹·ω_{ℓ−1}4^{1−ℓ}<ω_P4^{−P} (ω_d:=Lᵈ(B_1),ω₀:=1); let M(T)>0 (else T=0). For j≤N let G_j be the set of g∈F_j∩B_{1/4}(x_j) with μ_T(⋃_{z∈ℤ^P∩S_j}p_j^{-1}(B_ρ(g+z)))≤βρ^{n+1}M(T) ∀ρ∈(0,1/4],B_j:=(F_j∩B_{1/4}(x_j))∖G_j (relatively open: l.s.c. in g). Each b∈B_j has a violating ρ_b∈(0,1/4]; the 5r-covering lemma gives disjoint B_{ρ_l}(b_l) with B_j⊆⋃B_{5ρ_l}(b_l); the ⋃_zp_j^{-1}(B_{ρ_l}(b_l+z)) are disjoint (balls in B_{1/2}(x_j),|z|≥1 for z≠0), so βΣρ_l^{n+1}M(T)≤M(T),L^{n+1}(B_j)≤5^{n+1}ω_{n+1}β⁻¹; likewise for ∂T (B'_j). For a∈B_{1/4}(q), p_j(a)∈B_{1/4}(x_j)⊆F_j and L^P{a∈B_{1/4}(q): p_j(a)∈B_j∪B'_j}≤L^{n+1}(B_j∪B'_j)ω_{ℓ−1}4^{1−ℓ} (Fubini on S_j×S_j^⊥; fibres: (ℓ−1)-balls of radius ≤1/4); by the choice of β fix a∈B_{1/4}(q) with p_j(a)∈G_j∩G'_j ∀j. By Part D's formula for L*(a;ρ), for ρ∈(0,1/4]:
(6) μ_T(L*(a;ρ))≤Nβρ^{n+1}M(T),(7) μ_{∂T}(L*(a;ρ))≤Nβρ^{n+1}M(∂T); so μ_T(L*(a))=μ_{∂T}(L*(a))=0.
E2. Let d:=dist(·,L*(a)) (1-Lip),ρ_ν:=2^{−ν−2} (ν≥0). (SL) with f:=d for T (IM representation, |ξ|≤1 a.e. by (IMC)(d)) and ∂T ((REP) representation) gives T_t:=T⌞{d<t},(∂T)_t:=(∂T)⌞{d<t},Z_t:=∂T_t−(∂T)_t,M(Z_t)≤liminf_{h↓0}h⁻¹μ_T({t−h<d<t})≤F'(t) wherever F(t):=μ_T({d<t}) (nondecreasing) is differentiable (a.e. t). F'=deriv F is integrable with ∫_{ρ_ν/2}^{ρ_ν}F'≤F(ρ_ν)−F(ρ_ν/2)≤μ_T(L*(a;ρ_ν))≤Nβρ_ν^{n+1}M(T) (Lebesgue, F monotone; (6)), so F'≤(4/ρ_ν)Nβρ_ν^{n+1}M(T) on a positive-measure subset of (ρ_ν/2,ρ_ν). If n≥2,(SL) for ∂T (boundary 0; representations (μ_{∂T},ξ_{∂T}),(0,0)) and the same argument with F_∂(t):=μ_{∂T}({d<t}) give M(∂((∂T)_t))<∞ for a.e. t. So for each ν there is ρ*_ν∈(ρ_ν/2,ρ_ν) with
(10) M(Z_{ρ*_ν})≤(4/ρ_ν)Nβρ_ν^{n+1}M(T)=4Nβρ_νⁿM(T),
M(∂((∂T)_{ρ*_ν}))<∞ (n≥2),μ_T({d=ρ*_ν})=μ_{∂T}({d=ρ*_ν})=0 (all but countably many radii). With shell_i:={ρ*_{i+1}≤d<ρ*_i}, (∂T)⌞shell_i,(∂T)⌞{d≥ρ*_ν} and Z_{ρ*_ν} (∂Z_{ρ*_ν}=−∂((∂T)_{ρ*_ν})) have finite mass and boundary mass (A4 applies); T_{ρ*_ν}=T⌞{d≤ρ*_ν}; X_ν:=T−T_{ρ*_ν}=T⌞{d≥ρ*_ν} is IM ((IMC)(b)), compactly supported in {d≥ρ*_ν}, where ψ (Lemma D) is c₂/ρ*_ν-Lip, and ∂X_ν=(∂T)⌞{d≥ρ*_ν}−Z_{ρ*_ν} has finite mass.
E3. Let ψ_ν be a Lip extension of ψ|{d≥ρ*_ν} (A4(e)),h_ν(t,x):=x+t(ψ_ν(x)−x). By A4(e),(f),B4: ψ_#X_ν:=ψ_{ν#}X_ν,H_ν:=h_{ν#}(𝕀×X_ν) are IM,J_ν:=h_{ν#}(𝕀×∂X_ν) is a current, all independent of the extension and additive over decompositions of X_ν into currents supported in {d≥ρ*_ν}, and
(20) X_ν−ψ_#X_ν=∂(−H_ν)+(−J_ν).
X_ν=X_0+Σ_{i<ν}Y_i with Y_i:=T⌞shell_i IM, normal (∂Y_i=(∂T)⌞shell_i+Z_{ρ*_i}−Z_{ρ*_{i+1}}), supported in {d≥ρ*_{i+1}}, where Lip ψ≤c₂/ρ*_{i+1}≤c₂2^{i+4} (extensions: factor ≤√P, absorbed in c),μ_T(shell_i)≤μ_T(L*(a;ρ_i))≤Nβρ_i^{n+1}M(T) (6). By A4(a),(f),|ψ−id|≤√P,(6),(7),(10):
M(ψ_#Y_i)≤(c₂2^{i+4})ⁿNβρ_i^{n+1}M(T)≤c2^{−i}M(T),M(h_#(𝕀×Y_i))≤√P(1+c₂2^{i+4})ⁿNβρ_i^{n+1}M(T)≤c2^{−i}M(T); M(ψ_#((∂T)⌞shell_i)),M(h_#(𝕀×(∂T)⌞shell_i))≤c2^{−2i}M(∂T); M(ψ_#Z_{ρ*_i})≤(c₂/ρ*_i)^{n−1}4Nβρ_iⁿM(T)≤cρ_iM(T),M(h_#(𝕀×Z_{ρ*_i}))≤√P(1+c₂/ρ*_i)^{n−1}4Nβρ_iⁿM(T)≤cρ_iM(T);
on {d≥ρ*_0} (Lip ψ≤8c₂): M(ψ_#X_0)≤(8c₂)ⁿM(T),M(H_0)≤√P(1+8c₂)ⁿM(T), likewise for (∂T)⌞{d≥ρ*_0} with exponent n−1 (0 for slice terms if n=1). So ψ_#X_ν,H_ν,J_ν+h_{ν#}(𝕀×Z_{ρ*_ν}) are Cauchy in mass, and the Z_{ρ*_ν}-terms →0 in mass.
E4. Let Q₀:=lim ψ_#X_ν,R₁:=−lim H_ν,S₁:=−lim(J_ν+h_{ν#}(𝕀×Z_{ρ*_ν})) (mass, hence weak, limits). By (20),M(T_{ρ*_ν})→μ_T(L*(a))=0 and the vanishing Z-terms,
(21) T−Q₀=∂R₁+S₁,
and by E3,(24) M(Q₀),M(R₁)≤cM(T),M(S₁)≤cM(∂T),(25) M(∂Q₀)≤liminf M(ψ_#∂X_ν)≤cM(∂T) (lower semicontinuity; ∂ψ_#X_ν=ψ_#∂X_ν,ψ_#Z_{ρ*_ν}→0). Integrality: on the open O:=ℝ^P∖L*(a)⊇M∖L*(a) (μ_T(L*(a))=0),ψ is locally Lip, ‖d^Mψ‖ is at most its pointwise Lip constant, ≤c₂2^{ν+4} on shell_ν and ≤8c₂ on {d≥ρ*_0}, so I_ψ≤∫‖d^Mψ‖ⁿθ dHⁿ≤Σ_ν(c₂2^{ν+4})ⁿμ_T(shell_ν)+(8c₂)ⁿM(T)<∞ (6). By B3 Φ_ψ(T) is IM; by countable additivity of its integral over the disjoint {d≥ρ*_0}, shell_i, and B4,Φ_ψ(T)=ψ_#X_0+Σ_iψ_#Y_i=Q₀ (B4 for the extension ψ̃_i used for Y_i: ψ̃_i=ψ on the open {d>ρ*_{i+1}} and μ_T({d=ρ*_{i+1}})=0 (E2), so d^Mψ̃_i=d^Mψ Hⁿ-a.e. on M∩shell_i). So Q₀ is IM; likewise R₁=−Φ_h(𝕀×T) is IM (B5; B3 in ℝ×ℝ^P on ℝ×O, where h(t,x)=x+t(ψ(x)−x) is locally Lip and, along (0,1)×M,Jh(t,x)=|(ψ(x)−x)∧Λ_n((1−t)I+t d^Mψ(x))ξ(x)|≤√P(1+c₁/d(x))ⁿ by (L1),(L2), so I_h≤√PΣ_ν(1+c₂2^{ν+4})ⁿμ_T(shell_ν)+√P(1+8c₂)ⁿM(T)<∞).
E5. ψ maps O into L_n, moving points ≤√P within their cube; by A4(d) spt ψ_#X_ν⊆ψ(spt X_ν)⊆L_n, so spt Q₀⊆L_n (closed); spt Q₀∪spt R₁⊆U_{√P}(spt T); spt S₁⊆U_{√P}(spt ∂T) (only the terms h_#(𝕀×(∂T)⌞{d≥ρ*_ν}) survive); spt ∂Q₀⊆U_{√P}(spt ∂T) (∂Q₀=lim ψ_#((∂T)⌞{d≥ρ*_ν})).
E6. Q₀ is IM, so μ_{Q₀}=θ_{Q₀}Hⁿ⌞M_{Q₀} vanishes on the Hⁿ-null L_{n−1}, and μ_{Q₀}(ℝ^P∖L_n)=0 (VO); so Q₀=Σ_FQ₀⌞F̆,F over the n-faces of the unit grid, F̆ the relative interior (finitely many ≠0: spt Q₀ is compact).
E7. Fix an n-face F=b_F+[0,1]^I (|I|=n,b_F∈ℤ^P), affine hull Π_F,e_F:=e_{i_1}∧⋯∧e_{i_n}. (a) Q₀⌞F̆ is IM, carried by F̆⊆Π_F ((IMC)(b)); a.e. its approximate tangent space lies in, so equals, the coordinate plane V_F of Π_F (blow-ups of subsets of Π_F lie in V_F), so its orientation is ±e_F a.e. and Q₀⌞F̆(ω)=∫_{F̆}u_F⟨ω,e_F⟩dLⁿ,u_F:=±θ_{Q₀}1_{M_{Q₀}}∈L¹(F̆) integer-valued (F̆≅Q₁ via translation and coordinate projection p_F to ℝ^I; Hⁿ=Lⁿ on Π_F). (b) For g∈C_c^∞(F̆;ℝ^I),|g|≤1, let γ:=χΣ_j(g_j∘p_F)ε_j(I) (d(Σg_jε_j(I))=(div g)dx^I),χ∈C_c^∞,0≤χ≤1,χ=1 near spt g, spt χ in a neighbourhood N of spt g with N∩L_n⊆F̆ (spt g⊆F̆ compact; other n-faces meet F only in ∂F). Then |γ|≤1 and ∫u_F div g=Q₀(dγ)=∂Q₀(γ) (only Q₀⌞F̆ sees N; dχ=0 near spt g∩Π_F), so |∫u_F div g|≤μ_{∂Q₀}(N∩L_n)≤μ_{∂Q₀}(F̆) (spt ∂Q₀⊆spt Q₀⊆L_n): V_F:=sup_g∫u_F div g≤μ_{∂Q₀}(F̆),Σ_FV_F≤M(∂Q₀) (the F̆ are disjoint). (c) Let β_F be the integer median of C2. By C1(i),∫_{F̆}|u_F−β_F|≤c_nV_F; by C1(ii) for u_F−β_F (same V_F), pushed to ℝ^P by the affine isometric embedding ℝⁿ→Π_F (A1; mass not increased by (L1)),M(∂((u_F−β_F)[[F̆]]))≤c_n(V_F+c_nV_F); by C2,|β_F|≤2∫_{F̆}|u_F|, and β_F=0 unless ∫_{F̆}|u_F|≥1/2, so finitely many β_F≠0; V_F=0 ⇒ u_F a.e. constant (C1(i)) ⇒ u_F=β_F. (d) P:=Σ_Fβ_F[[F]],[[F]](ω):=∫_F⟨ω,e_F⟩dHⁿ. As Hⁿ(∂F)=0,Q₀−P=Σ_F(u_F−β_F)[[F̆]], so
(34) M(Q₀−P)≤c_nM(∂Q₀),M(∂Q₀−∂P)≤Σ_FM(∂((u_F−β_F)[[F̆]]))≤c'_nM(∂Q₀),(36) M(P)=Σ_F|β_F|≤2M(Q₀),(37) M(∂P)≤(1+c'_n)M(∂Q₀).
(e) P is IM (carrier ⋃_{β_F≠0}F̆, multiplicity |β_F|, orientation sign(β_F)e_F; approximate tangent space V_F on F̆; ∂F is null), M(P)=Σ|β_F| (MR); ∂[[F]] is the sum of the (n−1)-faces of F with Stokes orientations, so ∂P=Σ_Gγ_G[[G]] (γ_G∈ℤ, (n−1)-faces G) is IM likewise (n=1: integer combination of points). Supports: β_F≠0 only if F̆ meets spt Q₀ (u_F=0 a.e. ⇒ β_F=0), so spt P⊆U_{√n}(spt Q₀)⊆U_{2√P}(spt T); u_F≠β_F only if V_F>0, i.e. F̆ meets spt ∂Q₀, so spt(Q₀−P), spt ∂P⊆U_{√n}(spt ∂Q₀)⊆U_{2√P}(spt ∂T).
E8. By (21),T−P=∂R₁+(S₁+(Q₀−P)); R:=R₁,S:=S₁+(Q₀−P) (ℓ=0: R=0,S=T−P). Then P,∂P,R are IM,M(P)≤2M(Q₀)≤cM(T),M(∂P)≤(1+c'_n)M(∂Q₀)≤cM(∂T),M(R)≤cM(T),M(S)≤M(S₁)+c_nM(∂Q₀)≤cM(∂T), supports as in (U) (E5,E7(e)): (U) holds, and E0 gives the theorem.∎

## Key steps

1. A1–A4: smooth/Lipschitz push-forwards, 𝕀×X, homotopy formula and mass bounds.
2. B1–B5: bi-Lipschitz pieces, tangent planes, integral current Φ_F is IM, F_#X=Φ_F, 𝕀×X IM.
3. C1–C2: Poincaré/trace bounds, integer medians; Lemma D: retraction ψ onto L_n, D̄ψ≤c₁/d.
4. E1–E5: good centre a and radii, shell estimates, mass limits: T−Q₀=∂R₁+S₁, Q₀ and R₁ IM.
5. E6–E8, E0: Q₀ ↦ P=Σβ_F[[F]] by face medians, (U), rescale by ρ, finite net 𝒬.

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
