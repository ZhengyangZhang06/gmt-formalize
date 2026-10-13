<!-- theorem-id: gmt-ch07/root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.retraction_comparison-a1.ambient_restriction-a1 -->

## Theorem `Submission.dtc_bc_lc_rc_ambient_restriction`

Let P, n ∈ ℕ, U ⊆ ℝ^P open and W ⊆ ℝ^P open with W ⊂⊂ U (CompactlyContained W U: closure W is compact and closure W ⊆ U). Let S ∈ 𝒟_n(U) (GeometricCurrentOn U n) and let R = (M, θ, ξ) be an integer multiplicity representation of S in U (IMRep U n with R.Represents S). Then there are a current Q ∈ 𝒟_n(ℝ^P) (GeometricCurrentOn univ n) and an integer multiplicity representation R_Q of Q in ℝ^P (IMRep univ n with R_Q.Represents Q) with carrier M ∩ W, multiplicity θ and orientation ξ, such that: (Q1) Q(ιω) = S(ω) for every ω ∈ 𝒟ⁿ(U) with tsupport ω ⊆ W, where ιω = testFormOnInclusion (U ⊆ ℝ^P) n ω is ω regarded as a test form on ℝ^P; and (Q2) spt Q ⊆ closure(W) ∩ spt S and spt Q is compact. (Q is S⌞W regarded as a current in ℝ^P; its weight is θHⁿ⌞(M ∩ W) = μ_S⌞W.)

Node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.retraction_comparison-a1.ambient_restriction-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5396

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4196, https://github.com/ZhengyangZhang06/gmt-formalize/issues/808, https://github.com/ZhengyangZhang06/gmt-formalize/issues/810, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1174

Decomposition children: None

## Lean problem

Declaration: `Submission.dtc_bc_lc_rc_ambient_restriction`

```lean
∀ (P n : ℕ) (U W : Set (Euclid P)) (S : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → IsOpen W → CompactlyContained W U → R.Represents S → ∃ (Q : GeometricCurrentOn (univ : Set (Euclid P)) n) (RQ : IMRep (univ : Set (Euclid P)) n), RQ.Represents Q ∧ RQ.carrier = R.carrier ∩ W ∧ RQ.mult = R.mult ∧ RQ.orient = R.orient ∧ (∀ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Euclid P) n) ⊆ W → Q (testFormOnInclusion (subset_univ U) n ω) = S ω) ∧ Q.support ⊆ closure W ∩ S.support ∧ IsCompact Q.support
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

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.retraction_comparison-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.retraction_comparison-a1.ambient_restriction-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 of the parent proof (Q := S⌞B_G as a current in ℝ^P, with (Q1) and (Q2)), stated for an arbitrary open W ⊂⊂ U. The parent applies it with W = B_G(0), whose closure closedBall(0, G) is compact and contained in U. It is the supplied proof's own device for applying the push-forward, which is defined for currents in ℝ^P, to the part of S inside B_G. Simon states 7.2.4 and Remark 7.2.5(2) at chapter-07.txt lines 157–175 and leaves the modification of the proof of 2.4 to minimizers in submanifolds N_j to the reader; this restriction step is not printed there.

Siblings used:
- im_calculus (b) [IMC-b]: if U' is open, R' is an IMRep of U' and E is Borel, there are a current A ∈ 𝒟_n(U') and an IMRep of U' representing A with carrier R'.carrier ∩ E and the same multiplicity and orientation.
- mass_eq_measure [M]: if U' and O are open, O ⊆ U' and R' represents T in U', then M_O(T) = R'.measure(O).
- vanish_off_support [V]: T(ω) = 0 whenever tsupport ω is disjoint from spt T.
- support_of_vanishing [SV]: if U' is open, K ⊆ U' is compact and F ∈ 𝒟_n(U') satisfies F(ω) = 0 for every ω whose tsupport is disjoint from K, then spt F ⊆ K and spt F is compact.

Notation. Hⁿ := μHE[n]. For an IMRep R' = (M', θ', ξ') and a form ω, R'.action ω = ∫_{M'} θ'(x)·ξ'(x)(ω(x)) dHⁿ(x), and R'.Represents T means T(ω) = R'.action ω for every test form ω of the domain of T. R'.measure = θ'Hⁿ⌞M' (withDensity), so R'.measure(E) = ∫_{M'∩E} θ' dHⁿ for Borel E. spt T = U' ∖ Z_T, where the zero region Z_T is open (isOpen_zeroRegion).

1. (The triple (M ∩ W, θ, ξ) in U.) W is open, hence Borel. IMC-b with (U, R, E := W) gives an IMRep R' of U with carrier M ∩ W, multiplicity θ and orientation ξ. Its fields give: M ∩ W is countably n-rectifiable; ξ is Hⁿ⌞(M ∩ W)-a.e. strongly measurable; for Hⁿ⌞(M ∩ W)-a.e. x there is a subspace Q_x with HasApproximateTangentSpaceAt n (M ∩ W) x Q_x and IsUnitOrientationOf (ξ x) Q_x.

2. (The same triple in ℝ^P.) Define R₀ : IMRep univ n with carrier M ∩ W, multiplicity θ and orientation ξ. Its fields hold:
 (a) M ∩ W is Borel (M is Borel and W is open), and M ∩ W ⊆ ℝ^P.
 (b) Rectifiability, a.e. strong measurability of ξ and the orientation property hold by step 1. These fields refer only to the carrier M ∩ W and to θ, ξ, not to the domain.
 (c) θ is measurable, and θ(x) > 0 for x ∈ M ∩ W, since x ∈ M.
 (d) Local integrability in ℝ^P. Let K ⊆ ℝ^P be compact. Since (M ∩ W) ∩ K ⊆ M ∩ closure(W), ∫_{(M∩W)∩K} θ dHⁿ ≤ ∫_{M∩closure(W)} θ dHⁿ < ∞. The last bound is the local integrability of R in U, applied to the compact set closure(W) ⊆ U (lintegral_mono_set).

3. (The current Q.) IMC-b with (ℝ^P, R₀, E := ℝ^P) gives Q ∈ 𝒟_n(ℝ^P) and an IMRep R_Q of ℝ^P with R_Q.Represents Q, carrier (M ∩ W) ∩ ℝ^P = M ∩ W, multiplicity θ and orientation ξ. Thus Q(η) = ∫_{M∩W} θ ξ(η) dHⁿ for every η ∈ 𝒟ⁿ(ℝ^P).

4. (Q1) Let ω ∈ 𝒟ⁿ(U) with tsupport ω ⊆ W. The form ιω has the same underlying form as ω (testFormOnInclusion_coe), so Q(ιω) = ∫_{M∩W} θ ξ(ω) dHⁿ. Also S(ω) = ∫_M θ ξ(ω) dHⁿ, because R represents S. For x ∈ M ∖ (M ∩ W) we have x ∉ W ⊇ tsupport ω, so ω(x) = 0 (image_eq_zero_of_notMem_tsupport) and the integrand θ(x)·ξ(x)(0) = 0. As M is measurable and M ∩ W ⊆ M, the integral over M equals the integral over M ∩ W (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero). Hence Q(ιω) = S(ω).

5. (Hⁿ(M ∖ spt S) = 0.)
 (a) O := U ∖ spt S equals U ∩ Z_S, because spt S = U ∖ Z_S. So O is open, and O ⊆ U.
 (b) M_O(S) = 0. Every admissible form ω for M_O has tsupport ω ⊆ O, and O is disjoint from spt S, so S(ω) = 0 by V. Every element ofReal(S(ω)) of the set whose supremum is M_O(S) is therefore 0.
 (c) By M (U and O open, O ⊆ U, R represents S): R.measure(O) = M_O(S) = 0, that is, ∫_{O∩M} θ dHⁿ = 0 (withDensity_apply, Measure.restrict_restrict).
 (d) θ ≥ 1 on M, so Hⁿ(O ∩ M) = ∫_{O∩M} 1 dHⁿ ≤ ∫_{O∩M} θ dHⁿ = 0.
 (e) M ⊆ U, so M ∖ spt S ⊆ O ∩ M. Hence Hⁿ(M ∖ spt S) = 0.

6. (Q2) Put K := closure(W) ∩ spt S.
 (a) K is compact. Since closure(W) ⊆ U, K = closure(W) ∩ (ℝ^P ∖ Z_S), the intersection of the compact set closure(W) with a closed set.
 (b) Q vanishes off K. Let η ∈ 𝒟ⁿ(ℝ^P) with tsupport η disjoint from K. By step 5, (M ∩ W) ∖ spt S ⊆ M ∖ spt S is Hⁿ-null, so Hⁿ-a.e. x ∈ M ∩ W lies in spt S. For such x, x ∈ W ⊆ closure(W), so x ∈ K. Then x ∉ tsupport η, so η(x) = 0 and θ(x)·ξ(x)(η(x)) = 0. Thus the integrand of Q(η) = ∫_{M∩W} θ ξ(η) dHⁿ vanishes Hⁿ⌞(M ∩ W)-a.e., and Q(η) = 0 (integral_eq_zero_of_ae).
 (c) SV with (ℝ^P, K, Q) (ℝ^P is open, K is compact, K ⊆ ℝ^P) gives spt Q ⊆ K = closure(W) ∩ spt S and spt Q compact.

7. Steps 3, 4 and 6 give Q and R_Q with all the stated properties. ∎

Checked Lean realization (not part of the mathematical argument). The following single declaration was compiled in a scratch copy (Lean v4.35.0-rc3, Mathlib 25730c7c, simongmt 2b36630, import GMT.Ch07.Submission at b4d606d, scope of the frozen contract), with the four siblings declared as Submission.* axioms of their exact frozen types; #print axioms lists only propext, Classical.choice, Quot.sound and those four siblings.

theorem Submission.dtc_bc_lc_rc_ambient_restriction : ∀ (P n : ℕ) (U W : Set (Euclid P)) (S : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → IsOpen W → CompactlyContained W U → R.Represents S → ∃ (Q : GeometricCurrentOn (univ : Set (Euclid P)) n) (RQ : IMRep (univ : Set (Euclid P)) n), RQ.Represents Q ∧ RQ.carrier = R.carrier ∩ W ∧ RQ.mult = R.mult ∧ RQ.orient = R.orient ∧ (∀ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Euclid P) n) ⊆ W → Q (testFormOnInclusion (subset_univ U) n ω) = S ω) ∧ Q.support ⊆ closure W ∩ S.support ∧ IsCompact Q.support := by
  have hIM := Submission.cmc_imRep_locality_restrict_sub
  have hM := Submission.dtc_mass_eq_measure
  have hV := Submission.dtc_vanish_off_support
  have hSV := Submission.rsd_cmr_support_subset_of_vanish
  intro P n U W S R hU hW hWU hR
  obtain ⟨A₀, R', -, hR'c, hR'm, hR'o⟩ := hIM.2.1 P n U R W hU hW.measurableSet
  have hrect : CountablyRectifiable n (R.carrier ∩ W) := hR'c ▸ R'.rectifiable
  have hasm : AEStronglyMeasurable R.orient (μHE[n].restrict (R.carrier ∩ W)) := by
    rw [← hR'c, ← hR'o]; exact R'.aestronglyMeasurable_orient
  have hor : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ W)), ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n (R.carrier ∩ W) x Q ∧ IsUnitOrientationOf (R.orient x) Q := by
    rw [← hR'c, ← hR'o]; exact R'.orients
  let R₀ : IMRep (univ : Set (Euclid P)) n :=
    { carrier := R.carrier ∩ W
      mult := R.mult
      orient := R.orient
      measurableSet_carrier := R.measurableSet_carrier.inter hW.measurableSet
      carrier_subset := subset_univ _
      rectifiable := hrect
      measurable_mult := R.measurable_mult
      mult_pos := fun x hx => R.mult_pos x hx.1
      locallyIntegrable_mult := fun K _ _ => by
        apply ne_top_of_le_ne_top (R.locallyIntegrable_mult (closure W) hWU.1 hWU.2)
        apply lintegral_mono_set
        intro x hx
        exact ⟨hx.1.1, subset_closure hx.1.2⟩
      aestronglyMeasurable_orient := hasm
      orients := hor }
  obtain ⟨Q, RQ, hRQ, hRQc, hRQm, hRQo⟩ := hIM.2.1 P n univ R₀ univ isOpen_univ MeasurableSet.univ
  have hRQc' : RQ.carrier = R.carrier ∩ W := by rw [hRQc]; exact inter_univ _
  -- the null set M \ spt S
  have hnull : μHE[n] (R.carrier \ S.support) = 0 := by
    have hopen : IsOpen (U \ S.support) := by
      have : U \ S.support = U ∩ S.zeroRegion := by
        ext x
        simp only [GeometricCurrentOn.support, Set.mem_sdiff, mem_inter_iff, not_and, not_not]
        constructor
        · intro h; exact ⟨h.1, h.2 h.1⟩
        · intro h; exact ⟨h.1, fun _ => h.2⟩
      rw [this]
      exact hU.inter S.isOpen_zeroRegion
    have hmass : S.massOn (U \ S.support) = 0 := by
      apply le_zero_iff.mp
      apply sSup_le
      rintro r ⟨ω, hω, rfl⟩
      show ENNReal.ofReal (S ω) ≤ 0
      rw [hV P n U S ω (by
        rw [← Set.subset_compl_iff_disjoint_right]
        exact hω.1.trans (fun x hx => hx.2)), ENNReal.ofReal_zero]
    have hmeas : R.measure (U \ S.support) = 0 := by
      rw [← hM P n U (U \ S.support) S R hU hopen sdiff_subset hR, hmass]
    unfold IMRep.measure at hmeas
    rw [withDensity_apply _ hopen.measurableSet, Measure.restrict_restrict hopen.measurableSet] at hmeas
    have hle : μHE[n] ((U \ S.support) ∩ R.carrier) ≤
        ∫⁻ x in (U \ S.support) ∩ R.carrier, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
      calc μHE[n] ((U \ S.support) ∩ R.carrier)
          = ∫⁻ x in (U \ S.support) ∩ R.carrier, (1 : ℝ≥0∞) ∂μHE[n] := by
            rw [setLIntegral_const, one_mul]
        _ ≤ ∫⁻ x in (U \ S.support) ∩ R.carrier, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
            apply setLIntegral_mono' (hopen.measurableSet.inter R.measurableSet_carrier)
            intro x hx
            have := R.mult_pos x hx.2
            exact_mod_cast this
    have h0 : μHE[n] ((U \ S.support) ∩ R.carrier) = 0 := le_zero_iff.mp (hmeas ▸ hle)
    apply measure_mono_null _ h0
    intro x hx
    exact ⟨⟨R.carrier_subset hx.1, hx.2⟩, hx.1⟩
  refine ⟨Q, RQ, hRQ, hRQc', hRQm, hRQo, ?_, ?_⟩
  · -- (Q1)
    intro ω hω
    rw [hRQ, hR ω]
    unfold IMRep.action
    rw [hRQc', hRQm, hRQo, testFormOnInclusion_coe]
    symm
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero R.measurableSet_carrier inter_subset_left
    intro x hx
    have : (ω : DifferentialForm (Euclid P) n) x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hx.2 ⟨hx.1, hω h⟩)
    simp [this]
  · -- (Q2)
    have hKcpt : IsCompact (closure W ∩ S.support) := by
      have : closure W ∩ S.support = closure W ∩ (S.zeroRegion)ᶜ := by
        ext x
        simp only [GeometricCurrentOn.support, mem_inter_iff, Set.mem_sdiff, mem_compl_iff]
        constructor
        · intro h; exact ⟨h.1, h.2.2⟩
        · intro h; exact ⟨h.1, hWU.2 h.1, h.2⟩
      rw [this]
      exact hWU.1.inter_right S.isOpen_zeroRegion.isClosed_compl
    exact hSV P n univ (closure W ∩ S.support) Q isOpen_univ hKcpt (subset_univ _) (fun ω hω => by
      rw [hRQ ω]
      unfold IMRep.action
      rw [hRQc', hRQm, hRQo]
      apply integral_eq_zero_of_ae
      have hn' : μHE[n] ((R.carrier ∩ W) \ S.support) = 0 :=
        measure_mono_null (sdiff_subset_sdiff_left inter_subset_left) hnull
      have hae : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ W)), x ∈ S.support := by
        rw [ae_restrict_iff' (R.measurableSet_carrier.inter hW.measurableSet)]
        rw [ae_iff]
        apply measure_mono_null _ hn'
        intro x hx
        simp only [Set.mem_ofPred_eq, not_imp] at hx
        exact ⟨hx.1, hx.2⟩
      filter_upwards [hae, ae_restrict_mem (R.measurableSet_carrier.inter hW.measurableSet)]
        with x hx hxM
      have : (ω : DifferentialForm (Euclid P) n) x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h =>
          hω.ne_of_mem h ⟨subset_closure hxM.2, hx⟩ rfl)
      simp [this])

## Key steps

1. im_calculus (b) in U with E = W makes (M ∩ W, θ, ξ) an integer multiplicity triple. It is locally integrable in all of ℝ^P because M ∩ W lies in the compact set closure(W) ⊆ U, so im_calculus (b) in ℝ^P with E = ℝ^P gives Q with representation (M ∩ W, θ, ξ).
2. (Q1): a form supported in W vanishes on M ∖ W, so the integrals over M and over M ∩ W agree.
3. Hⁿ(M ∖ spt S) = 0, by vanish_off_support, mass_eq_measure and θ ≥ 1.
4. (Q2): Q vanishes on forms supported off the compact set closure(W) ∩ spt S, and support_of_vanishing gives the support inclusion and compactness.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606d, mathlib 25730c7c); ls local-references/123e8435b4a2469b/project/GMT (contracts and README of Ch01–Ch08 only); grep -rn 'pushforward' project/GMT (only the Ch08 varifold pushforwardMeasure)`
- `read simongmt Chapter06/Mass.lean (covectorEuclideanNorm, massAdmissibleOn, GeometricCurrentOn.massOn, mass := massOn U, massOn_mono, le_massOn), Chapter06/Currents.lean (GeometricCurrentOn, ext, Zero instance and zero_apply, exteriorDerivativeTestOn, boundary, boundary_apply), Chapter06/CurrentLocalEquality.lean (testFormOnInclusion, testFormOnInclusion_coe, restrictDomain, restrictDomain_apply, VanishesOn, zeroRegion, support, isOpen_zeroRegion)`
- `python3 -I scans of runs/20261011T150044Z-ba604216b4/dag.json: parent decomposition nodes/…-local-comparison-a1/decomposition-v1.json (sibling types and the five re-listed accepted children); accepted statements mentioning massOn/restrictDomain/support/IsMinimizingIn (found dtc_massOn_eq_of_agreeOn, dtc_extend_by_zero, lcmp_massOn_le_add_of_eval_eq, cmc_fcl_massOn_le_add, lcmp_massOn_le_of_vanish_off_compact, cmc_massOn_le_of_le_near_support); search for nodes stating the two new lemmas (none besides this node); dependency-inheritance pattern of testform_extension-a1 (decomposition-v1.json rationale)`
- `git show <candidate commit>:GMT/Ch07/Submission.lean for dtc_massOn_eq_of_agreeOn (0c79e2a), dtc_mass_eq_measure (bff81d3), dtc_vanish_off_support (44ef61f), cmc_imRep_locality_restrict_sub (2af75d6), dtc_restrictDomain_isIntegerMultiplicity (8f3bacb), rsd_cmr_support_subset_of_vanish (02c6122): whitespace-normalised type comparison, all IDENTICAL; accepted natural proofs copied from each node's parent-supplied-natural-proof.md`
- `contract_scope(Contract.lean, 'GMT.Ch07.main_theorem') and child_modules(…, 'contract') from verifier/gmt-compare.py; lean_contract.validate_lean_statement on all eight child types; lake env lean /tmp/rcsplit/challenges/Challenge_<key>.lean (8 modules, only the expected sorry warning)`
- `lake env lean /tmp/rcsplit/lean/{Types,Children,Assembly,SubmissionForm}.lean with #print axioms (restr_proof, comp_proof, ret_assembly; leaf-form Submission.dtc_bc_lc_rc_ambient_restriction, Submission.dtc_bc_lc_rc_cycle_competitor, Submission.dtc_bc_lc_retraction_comparison)`
- `Mathlib names used at the pin: norm_fderiv_le_of_lipschitzOn, LipschitzOnWith.of_dist_le_mul, closure_ball, closedBall_subset_ball, ContDiffOn.differentiableOn, integral_congr_ae, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero, image_eq_zero_of_notMem_tsupport, withDensity_apply, withDensity_absolutelyContinuous, Measure.restrict_restrict, setLIntegral_const, setLIntegral_mono', lintegral_mono_set, ae_restrict_iff', integral_eq_zero_of_ae, measure_add_measure_compl, Measure.le_iff', IsCompact.image_of_continuousOn, Set.subset_compl_iff_disjoint_right`
- `grep for dtc_bc_lc_rc_ambient_restriction, dtc_bc_lc_rc_cycle_competitor and the prefix dtc_bc_lc_rc_ in dag.json (1223 nodes at the final check), nodes/, GMT/ and .lake/packages/simongmt (no match); dag.json lookup of dimred_mbl_lc_retraction_comparison (analogous node, not accepted) and dtc_approxTangent_of_null_diff (accepted)`
- `sed book/chapter-07.txt lines 157–262 (Simon 7.2.4 statement, Remark 7.2.5(2), proof steps (8)–(12); inequality (9) at lines 237–243)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-6950e06fcd/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-comparison-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-tes-dd42d587af/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-localize-a1-mass-agree-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/rcsplit/lean/Types.lean`
- `/tmp/rcsplit/lean/Children.lean`
- `/tmp/rcsplit/lean/Assembly.lean`
- `/tmp/rcsplit/lean/SubmissionForm.lean`

The pinned snapshot holds only chapter contracts; the SimonGMT library supplies currents, boundary, massOn/mass, support/zeroRegion, restrictDomain and testFormOnInclusion, but no restriction of a current to a subset, no extension to ℝ^P with an explicit representation and no competitor lemma. No accepted or active DAG node states the two new lemmas, so they are new children with unique names. Six accepted declarations are reused with identical types: dtc_massOn_eq_of_agreeOn (new for this node, used in steps 6(a) and 6(d)) and the five already re-listed by the parent. In Lean, the two children are proved from their declared siblings, and the exact frozen type of this node follows from the two children plus its declared dependencies (pushforward, orientation_fixed, measure_subadditive, mass_eq_measure, vanish_off_support, im_calculus, support_of_vanishing) and mass_agree, using only propext, Classical.choice and Quot.sound.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
