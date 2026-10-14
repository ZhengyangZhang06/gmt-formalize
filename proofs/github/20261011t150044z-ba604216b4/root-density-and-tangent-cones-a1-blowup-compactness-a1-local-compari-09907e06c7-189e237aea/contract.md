<!-- theorem-id: gmt-ch07/root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1 -->

## Theorem `Submission.dtc_bc_lc_slice`

Let P, m ∈ ℕ with m + 1 < P. Let T ∈ 𝒟_{m+2}(ℝ^P) be represented by an integer multiplicity triple R_T = (M, θ, ξ) (IMRep univ (m + 2), R_T.Represents T), and let ∂T ∈ 𝒟_{m+1}(ℝ^P) be represented by an integer multiplicity triple R_∂ = (M', θ', ξ') (IMRep univ (m + 1)). Let f : ℝ^P → ℝ be Lipschitz with constant L ∈ [0, ∞) (LipschitzWith L f). Then there are currents P_t ∈ 𝒟_{m+1}(ℝ^P) (t ∈ ℝ) such that: (1) for every open W ⊆ ℝ^P the function t ↦ M_W(P_t) ∈ [0, ∞] is a.e.-measurable for Lebesgue measure and ∫_ℝ M_W(P_t) dt ≤ L·M_W(T); (2) for L¹-a.e. t ∈ ℝ: P_t is integer multiplicity; P_t(ω) = 0 for every ω ∈ 𝒟^{m+1}(ℝ^P) whose topological support is disjoint from f⁻¹(t); and P_t(ω) = ∫_{M∩{f<t}} θ⟨dω, ξ⟩ dH^{m+2} − ∫_{M'∩{f<t}} θ'⟨ω, ξ'⟩ dH^{m+1} for every ω ∈ 𝒟^{m+1}(ℝ^P) (Hᵏ = μHE[k]). The last identity says P_t = ∂(T⌞{f < t}) − (∂T)⌞{f < t}, Simon's formula 4.5(2) for the slice ⟨T, f, t⟩.

Node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4757

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4196, https://github.com/ZhengyangZhang06/gmt-formalize/issues/808

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6023, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6031, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6044, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4196, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5119, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4635, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6068, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6075, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6085, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6092, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6099, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6105

## Lean problem

Declaration: `Submission.dtc_bc_lc_slice`

```lean
∀ (P m : ℕ) (T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 2)) (RT : IMRep (univ : Set (Euclid P)) (m + 2)) (RB : IMRep (univ : Set (Euclid P)) (m + 1)) (f : Euclid P → ℝ) (L : NNReal), m + 1 < P → RT.Represents T → RB.Represents T.boundary → LipschitzWith L f → ∃ Ps : ℝ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), (∀ W : Set (Euclid P), IsOpen W → AEMeasurable (fun t => (Ps t).massOn W) ∧ ∫⁻ t, (Ps t).massOn W ≤ (L : ℝ≥0∞) * T.massOn W) ∧ ∀ᵐ t, IsIntegerMultiplicity (Ps t) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 1))) (f ⁻¹' {t}) → Ps t ω = 0) ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), Ps t ω = (∫ x in RT.carrier ∩ {x | f x < t}, (RT.mult x : ℝ) * RT.orient x (exteriorDerivative (ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 2]) - ∫ x in RB.carrier ∩ {x | f x < t}, (RB.mult x : ℝ) * RB.orient x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 1]
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

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 6, Lemma 4.1, Remark 4.2, 4.3, Definition 4.4, Lemma 4.5 and 4.8 (chapter-06.txt lines 1151–1360, printed pp. 153–158). They are applied to the integer multiplicity (m+2)-current T = τ(M, θ, ξ) in U = ℝ^P; Simon's n is m + 2 here and the slices are (m+1)-currents. This is the result cited as (C2) in step 5 of the parent proof. The printed proofs are copied. Two points the source leaves implicit are made explicit: the family P_t is defined for every t, by the right side of 4.5(2) (step 1), and t ↦ M_W(P_t) is measurable (step 6). The hypothesis m + 1 < P only ensures that the currents considered are not trivially zero; it is not otherwise used.

Notation.
 • N := m + 2 and Hᵏ := μHE[k].
 • For x ∈ M, ∇^M f(x) is the gradient of f along M (Simon Ch. 3, 2.1). It is defined Hᴺ-a.e. on M through a decomposition M = ⋃_j M_j with Hᴺ(M₀) = 0 and M_j ⊆ N_j, N_j embedded C¹ submanifolds, and |∇^M f| ≤ L Hᴺ-a.e. on M.
 • M₊ := {x ∈ M : ∇^M f(x) ≠ 0}, and M_t := M₊ ∩ f⁻¹(t) for t ∈ ℝ.
 Borel versions of ∇^M f and of M₊ are fixed; this changes nothing up to Hᴺ-null sets.

1. (The currents P_t.) For every t, E_t := {f < t} is open, since f is continuous.
 (a) By the sibling im_calculus (b) (restriction of a representation to a Borel set, U = ℝ^P) there are currents A_t ∈ 𝒟_N(ℝ^P) and B_t ∈ 𝒟_{N−1}(ℝ^P) represented by (M ∩ E_t, θ, ξ) and (M' ∩ E_t, θ', ξ'). These are Simon's T⌞{f < t} and (∂T)⌞{f < t}.
 (b) Put P_t := ∂A_t − B_t. For every ω ∈ 𝒟^{N−1}(ℝ^P), P_t(ω) = A_t(dω) − B_t(ω) = ∫_{M∩{f<t}} θ⟨dω, ξ⟩ dHᴺ − ∫_{M'∩{f<t}} θ'⟨ω, ξ'⟩ dH^{N−1}. This is the identity in (2), and it holds for every t.

2. (Lemma 4.1: coarea on M.) For L¹-a.e. t the following hold.
 (a) M_t is countably (N−1)-rectifiable (Simon Ch. 3, Remark 2.10(2)).
 (b) For H^{N−1}-a.e. x ∈ M_t, the approximate tangent spaces T_xM_t and T_xM exist, T_xM_t is an (N−1)-dimensional subspace of T_xM, and T_xM = {y + λ∇^M f(x) : y ∈ T_xM_t, λ ∈ ℝ}. This follows from Simon Ch. 3, 1.6 applied to M_t and to M, together with ∇^M f(x) ∈ T_xM and ⟨∇^M f(x), τ⟩ = 0 for τ ∈ T_xM_t (Ch. 3, 2.1).
 (c) For every non-negative Hᴺ-measurable g on M, ∫_ℝ ∫_{M_t} g dH^{N−1} dt = ∫_M |∇^M f| g dHᴺ, and t ↦ ∫_{M_t} g dH^{N−1} is L¹-measurable. This is the co-area formula, Simon Ch. 3, 2.8–2.9 with m = 1.
 Replacing g by g·1_{f<t} gives Remark 4.2: t ↦ ∫_{M∩{f<t}} |∇^M f| g dHᴺ = ∫_{−∞}^t ∫_{M_s} g dH^{N−1} ds is absolutely continuous, with derivative ∫_{M_t} g dH^{N−1} for a.e. t.

3. (4.3–4.4: the slice as an integer multiplicity current.) Take t as in step 2.
 (a) For H^{N−1}-a.e. x ∈ M_t, ξ_t(x) := ξ(x) ⌞ (∇^M f(x)/|∇^M f(x)|) (with ⟨ξ⌞w, a⟩ := ⟨ξ, w ∧ a⟩) is a unit simple (N−1)-vector orienting T_xM_t. Indeed (4.3), ξ(x) = ±τ₁ ∧ ⋯ ∧ τ_N with τ₁ = ∇^M f/|∇^M f| and τ₂, …, τ_N an orthonormal basis of T_xM_t.
 (b) Let θ_t := θ|M_t. By step 2(c) with g = θ1_K, ∫_ℝ ∫_{M_t∩K} θ dH^{N−1} dt ≤ L∫_{M∩K} θ dHᴺ < ∞ for each compact K. Applying this to K = closedBall(0, k), k ∈ ℕ, θ_t is locally H^{N−1}-integrable on M_t for a.e. t.
 (c) Fix a Borel version ξ̃ of ξ; ξ is Hᴺ⌞M-a.e. strongly measurable. Let Z ⊆ M be an Hᴺ-null Borel set containing the points where ξ̃ ≠ ξ, where ξ does not orient T_xM, or where ∇^M f or T_xM does not exist. By step 2(c) with g = 1_Z, ∫_ℝ H^{N−1}(Z ∩ M_t) dt = ∫_Z |∇^M f| dHᴺ = 0, so H^{N−1}(Z ∩ M_t) = 0 for a.e. t. Hence for a.e. t, (a) holds at H^{N−1}-a.e. x ∈ M_t, and ξ_t agrees H^{N−1}-a.e. on M_t with the Borel field ξ̃ ⌞ (∇^M f/|∇^M f|).
 (d) Hence for a.e. t, (M_t, θ_t, ξ_t) is an integer multiplicity triple (an IMRep univ (N−1)): Borel carrier, countably (N−1)-rectifiable, θ_t ≥ 1 integer valued and locally integrable, ξ_t measurable and orienting the approximate tangent spaces a.e.
 (e) ⟨T, f, t⟩ := τ(M_t, θ_t, ξ_t) ∈ 𝒟_{N−1}(ℝ^P) is then an integer multiplicity current: im_calculus (b) with E = ℝ^P provides the current, the functional being sequentially continuous by local integrability.

4. (4.5(2): ⟨T, f, t⟩ = P_t for a.e. t.)
 (a) Fix ω ∈ 𝒟^{N−1}(ℝ^P), t ∈ ℝ and ε > 0. Let γ_ε : ℝ → [0, 1] equal 1 on (−∞, t − ε], 0 on [t, ∞), and be linear on [t − ε, t]. Then h := γ_ε ∘ f is Lipschitz, and its mollification h^{(σ)} := h ∗ φ_σ (Simon Ch. 2, §2) is smooth.
 (b) (∂T)(h^{(σ)}ω) = T(d(h^{(σ)}ω)) = T(dh^{(σ)} ∧ ω) + T(h^{(σ)} dω).
 (c) Since ξ(x) orients T_xM, ⟨ξ(x), dh^{(σ)}(x) ∧ ω(x)⟩ = ⟨ξ(x) ⌞ ∇^M h^{(σ)}(x), ω(x)⟩. As σ ↓ 0, ∇^M h^{(σ)} → ∇^M h weakly in L²(μ_T) on M. This is Simon's (1), checked on each C¹ piece N_j using the uniform convergence of h^{(σ)} to h. Hence lim_{σ↓0} T(dh^{(σ)} ∧ ω) = ∫_M θ⟨ξ ⌞ ∇^M h, ω⟩ dHᴺ.
 (d) By the chain rule (Simon's (4)), ∇^M h = γ_ε'(f)∇^M f Hᴺ-a.e. on M, since ∇^M f = 0 a.e. on level sets of f. Also h^{(σ)}ω → hω and h^{(σ)}dω → h dω uniformly, with supports in a fixed compact set. Using the representations of T and ∂T, (b) and (c) give
 ∫_{M'} θ' h⟨ω, ξ'⟩ dH^{N−1} = −ε^{−1}∫_{M∩{t−ε<f<t}} θ⟨ξ ⌞ ∇^M f, ω⟩ dHᴺ + ∫_M θ h⟨dω, ξ⟩ dHᴺ.
 (e) Let ε ↓ 0. By dominated convergence (h → 1_{f<t}), the left side tends to B_t(ω) and the last term to A_t(dω). Apply Remark 4.2 (step 2) with g := θ⟨ξ ⌞ (∇^M f/|∇^M f|), ω⟩, split into positive and negative parts: the middle term tends to −∫_{M_t} θ⟨ξ_t, ω⟩ dH^{N−1} = −⟨T, f, t⟩(ω) for every t outside an L¹-null set F_ω. Hence ⟨T, f, t⟩(ω) = A_t(dω) − B_t(ω) = P_t(ω) for t ∉ F_ω.
 (f) Take a countable set Ω ⊆ 𝒟^{N−1}(ℝ^P) such that every ω is the limit of some ω_k ∈ Ω with supports in a fixed compact set and ω_k → ω, dω_k → dω uniformly (Simon: "by considering a countable dense set of ω"). Put F := ⋃_{ω ∈ Ω} F_ω, an L¹-null set. Both sides are continuous in ω for this convergence: |P_t(ω)| ≤ sup|dω| μ_T(K) + sup|ω| μ_{∂T}(K), and |⟨T, f, t⟩(ω)| ≤ sup|ω| ∫_{M_t∩K} θ dH^{N−1} < ∞ for a.e. t. So ⟨T, f, t⟩ = P_t for a.e. t.

5. (4.8: support.) For t as in steps 2–4, ⟨T, f, t⟩ = τ(M_t, θ_t, ξ_t) with M_t ⊆ f⁻¹(t). If tsupport ω ∩ f⁻¹(t) = ∅, then ω = 0 on M_t, so P_t(ω) = ⟨T, f, t⟩(ω) = 0. Together with step 3, P_t is integer multiplicity and vanishes on such ω for a.e. t; with the identity of step 1, which holds for every t, this proves (2).

6. (4.5(1) and measurability.) Let W be open.
 (a) For a.e. t, P_t = ⟨T, f, t⟩ is integer multiplicity with representation (M_t, θ_t, ξ_t). By the sibling mass_eq_measure (with U = ℝ^P), M_W(P_t) = ∫_{M_t∩W} θ dH^{N−1}.
 (b) By step 2(c) with g = θ1_W, the right side is an L¹-measurable function of t. So t ↦ M_W(P_t) is a.e.-measurable.
 (c) Using |∇^M f| ≤ L Hᴺ-a.e. (f is L-Lipschitz) and mass_eq_measure for T: ∫_ℝ M_W(P_t) dt = ∫_ℝ ∫_{M_t∩W} θ dH^{N−1} dt = ∫_{M∩W} |∇^M f| θ dHᴺ ≤ L ∫_{M∩W} θ dHᴺ = L·μ_T(W) = L·M_W(T). This proves (1). ∎

## Key steps

1. Define P_t := ∂A_t − B_t for every t, with A_t, B_t the restrictions of T and ∂T to {f < t} (im_calculus (b)). This is the stated integral formula.
2. Coarea on M (Lemma 4.1): for a.e. t, M_t = M₊ ∩ f⁻¹(t) is countably (m+1)-rectifiable with T_xM = T_xM_t ⊕ ℝ∇^M f, and ∫_ℝ ∫_{M_t} g = ∫_M |∇^M f| g.
3. For a.e. t, ⟨T, f, t⟩ = τ(M_t, θ, ξ⌞∇^M f/|∇^M f|) is integer multiplicity (4.3–4.4).
4. Mollification and Remark 4.2 give ⟨T, f, t⟩ = P_t for a.e. t (4.5(2)); a countable dense family of forms makes the null set independent of ω.
5. P_t is carried by f⁻¹(t) (4.8). M_W(P_t) = ∫_{M_t∩W} θ is measurable in t, with integral ∫_{M∩W} |∇^M f| θ ≤ L·M_W(T) (4.5(1), mass_eq_measure).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; read workspace GMT/Ch07/Contract.lean, GMT/Ch07/README.md (contract unchanged; Submission.lean byte copy)`
- `rg/grep 'def GeometricCurrentOn.massOn|massAdmissibleOn|covectorEuclideanNorm_neg|le_massOn|massOn_mono|massOn_le_liminf' simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `grep 'structure GeometricCurrentOn|instance .*Zero|def GeometricCurrentOn.boundary|boundary_boundary|exteriorDerivativeTestOn|tsupport_exteriorDerivative_subset|WeaklyConvergesOn' simongmt/Poincare/SimonGMT/Chapter06/Currents.lean; grep 'abbrev Covector|abbrev DifferentialForm|abbrev exteriorDerivative' Chapter06/Forms.lean`
- `grep 'restrictDomain|testFormOnInclusion|VanishesOn|zeroRegion|def GeometricCurrentOn.support|isOpen_zeroRegion' simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `grep 'def CountablyRectifiable|def HasApproximateTangentSpaceAt|blowUpMap|HasApproximateTangentSpaceAt.unique|support_euclideanHausdorffMeasure_restrict_submodule' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (no slicing, flat-norm, deformation theorem or non-affine push-forward in Chapter06)`
- `python3 -I scans of dag.json (673 nodes at the first scan, 783 at the final re-check): related nodes cmc_flat_convergence, cmc_slice_mass_bounds, dimred_mbl_pushforward, dimred_mbl_local_comparison, imrep_c1_diffeo_pushforward_im (not accepted, not reusable); accepted candidates dtc_mass_eq_measure, dtc_vanish_off_support, cmc_imRep_locality_restrict_sub, dtc_restrictDomain_isIntegerMultiplicity, rsd_cmr_support_subset_of_vanish, dtc_approxTangent_of_null_diff, lcmp_massOn_le_add_of_eval_eq, dpf_pushforward_formula_current_exists, dpf_pushforward_formula_boundaryVanishes; collision check of the seven new dtc_bc_lc_ names (none)`
- `git grep 'theorem Submission.<name> ' <accepted commit> -- GMT for the five reused declarations; whitespace-normalised type comparison (all IDENTICAL); git show e34a71c (dispatch commit contains only the contract)`
- `#check of Mathlib names at the pin: Filter.extraction_forall_of_eventually, ENNReal.tendsto_atTop_zero_of_tsum_ne_top, Metric.mem_thickening_iff_infDist_lt, IsCompact.cthickening, Measure.countable_meas_level_set_pos, norm_fderiv_le_of_lipschitzOn, ENNReal.tsum_geometric, restrict_withDensity, Measure.le_iff, image_eq_zero_of_notMem_tsupport`
- `lake env lean /tmp/dtcbclc/check/Types.lean; challenge modules /tmp/dtcbclc/check/challenges/Challenge_<key>.lean (12, generated by verifier gmt-compare.py child_modules, contract mode); lake env lean /tmp/dtcbclc/out/Assembly.lean with #print axioms for assembly and ret_assembly`
- `sed book/chapter-07.txt lines 150-300 (Simon 7.2.4 proof (1)-(14), Remark 7.2.5); book/chapter-06.txt lines 395-540, 700-1000, 1140-1500, 1990-2120 (2.23-2.29, 3.1-3.14, 4.1-4.11, 5.1-5.4, 6.3, 7.1-7.2); book/chapter-03.txt lines 100-160, 327-445 (1.6, 2.1-2.10)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-comparison-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-local-comparison-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/dtcbclc/out/Assembly.lean`
- `/tmp/dtcbclc/check/Types.lean`
- `/tmp/dtcbclc/stmts/children.py`

The pinned SimonGMT library provides currents, boundary, massOn with the Euclidean coefficient norm, support/zeroRegion, restrictDomain, testFormOnInclusion, lower semicontinuity of mass, CountablyRectifiable and HasApproximateTangentSpaceAt. It has no flat-norm theorem, deformation theorem, slicing, C¹ push-forward of currents or area/coarea formula on rectifiable sets. These are the three Simon Ch. 6 results (C1)–(C3) cited by the supplied proof, so they become the children flat_decomposition, slicing and pushforward. Related DAG nodes in other branches (cmc_flat_convergence, cmc_slice_mass_bounds, dimred_mbl_pushforward) are not accepted, so they cannot be reused and the new names are unique. Five accepted declarations are reused with identical types: dtc_mass_eq_measure, dtc_vanish_off_support, cmc_imRep_locality_restrict_sub, dtc_restrictDomain_isIntegerMultiplicity and rsd_cmr_support_subset_of_vanish. All Mathlib lemmas used in the Lean assembly exist at the pin. All 12 child types elaborate in the comparator scope. The Lean assembly proves the exact frozen type of dtc_bc_local_comparison from the 12 child types and the sibling measure_locality type, and proves retraction_comparison from its declared siblings, using only propext, Classical.choice and Quot.sound.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
