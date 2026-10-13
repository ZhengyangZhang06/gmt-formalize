<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.density_one_local_rep-a1.rep_support-a1 -->

## Theorem `Submission.codim1_dolr_rep_support_inter`

Support of a locally represented current. Data: P, m ∈ ℕ; U ⊆ ℝ^P; T ∈ 𝒟_m(U) (GeometricCurrentOn U m); W, M ⊆ ℝ^P; k ∈ ℤ; ξ : ℝ^P → Λ_m(ℝ^P) (MultiVector P m). Hypotheses: W is open and W ⊆ U; k ≠ 0; M is an embedded C¹ m-dimensional submanifold (IsEmbeddedSubmanifold 1 m M); ξ is an orientation of M (IsOrientation m M ξ); M is relatively closed in W (closure(M) ∩ W ⊆ M); H^m(M ∩ K) < ∞ for every compact K ⊆ W; and T(ω) = k ∫_M ⟨ω(x), ξ(x)⟩ dH^m(x) for every ω ∈ 𝒟^m(U) with tsupport ω ⊆ W. Conclusion: spt T ∩ W = M ∩ W, where spt T = T.support = U ∖ T.zeroRegion and T.zeroRegion is the union of the open O with closure(O) compact and contained in U such that T(ω) = 0 whenever tsupport ω ⊆ O. Here H^m = μHE[m].

Node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.density_one_local_rep-a1.rep_support-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5209

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4182, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4210, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4192

Decomposition children: None

## Lean problem

Declaration: `Submission.codim1_dolr_rep_support_inter`

```lean
∀ (P m : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U m) (W M : Set (Euclid P)) (k : ℤ) (ξ : Euclid P → MultiVector P m), IsOpen W → W ⊆ U → k ≠ 0 → IsEmbeddedSubmanifold 1 m M → IsOrientation m M ξ → closure M ∩ W ⊆ M → (∀ K : Set (Euclid P), IsCompact K → K ⊆ W → μHE[m] (M ∩ K) ≠ ∞) → (∀ ω : TestFormOn U m, tsupport (ω : DifferentialForm (Euclid P) m) ⊆ W → T ω = k * ∫ x in M, ξ x ((ω : DifferentialForm (Euclid P) m) x) ∂μHE[m]) → T.support ∩ W = M ∩ W
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

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.density_one_local_rep-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.density_one_local_rep-a1.rep_support-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Parent step 6 ("Support", parts 6a and 6b) of the supplied proof of codim1_density_one_regular_local_rep, written for an arbitrary open W ⊆ U and an arbitrary integer k ≠ 0. Book: Simon Ch. 6, 2.11 (spt T, chapter-06.txt lines 296–301), 2.5 (M_W(T), line 231); Simon 7.4.1 (T = m[[M]] near a regular point, chapter-07.txt lines 590–600).
Departure from the parent text, stated explicitly. Part 1 below is the parent's step 6a. In step 6b the parent tested T with a bump form φ·L(ξ(w)) and used the positivity fact (F3), proved from a chart through bilipschitz_measure. Here part 2 uses the accepted mass_identity (the exact local mass |k|·H^m(M ∩ B), which the parent's handoff explicitly allowed child sessions to reuse once accepted) and derives positivity from the accepted density_one.

Dependencies used (sibling subproblems; accepted declarations reused with their identical frozen types):
- locally_closed (Submission.dimred_rpd_embedded_locally_closed): if IsEmbeddedSubmanifold r d M, then M is measurable and every y ∈ M has some ε > 0 with M ∩ closedBall(y, ε) compact.
- density_one (Submission.dimred_rpd_submanifold_density_one): if IsEmbeddedSubmanifold 1 n M and z ∈ M, then H^n(M ∩ B_s(z))/(ω_n·ofReal(s^n)) → 1 in [0, ∞] as s → 0 within (0, ∞).
- mass_identity (Submission.dimred_rpd_massOn_eq_mult_measure): let W be open with W ⊆ U, M measurable, ξ continuous on M with ξ(x) a unit orientation of some linear subspace for every x ∈ M (IsUnitOrientationOf), H^n(M ∩ W) < ∞, and T(ω) = m₀ ∫_M ⟨ω(x), ξ(x)⟩ dH^n(x) for every ω ∈ 𝒟^n(U) with tsupport ω ⊆ W (m₀ ∈ ℤ). Then M_W(T) = T.massOn W = |m₀|·H^n(M ∩ W) in [0, ∞], |m₀| = m₀.natAbs.

Notation. H^m := μHE[m]; B_s(x) := ball x s (open ball); ω_m := unitBallVolume m; ⟨ω(x), ξ(x)⟩ := ξ(x)(ω(x)); 𝒟^m(U) := TestFormOn U m (smooth compactly supported m-forms ω with tsupport ω ⊆ U). M_W(T) := T.massOn W = sup{ofReal(T(ω)) : ω ∈ 𝒟^m(U), tsupport ω ⊆ W, covectorEuclideanNorm(ω(x)) ≤ 1 for all x} (supremum in [0, ∞]). T vanishes on O (T.VanishesOn O) if T(ω) = 0 for every ω ∈ 𝒟^m(U) with tsupport ω ⊆ O; T.zeroRegion is the union of all open O with closure(O) compact, closure(O) ⊆ U and T vanishing on O; spt T := T.support = U ∖ T.zeroRegion. IsOrientation m M ξ means: ξ is continuous on M, and for every x ∈ M there is a linear subspace Q with (Q : Set) = tangentSpace(M, x) and IsUnitOrientationOf (ξ(x)) Q.

Proof. Fix the data and hypotheses of the statement: W open, W ⊆ U, k ≠ 0, IsEmbeddedSubmanifold 1 m M, IsOrientation m M ξ, closure(M) ∩ W ⊆ M, H^m(M ∩ K) < ∞ for compact K ⊆ W, and (R) T(ω) = k ∫_M ⟨ω(x), ξ(x)⟩ dH^m(x) for every ω ∈ 𝒟^m(U) with tsupport ω ⊆ W.
0. (Preliminaries.) By locally_closed (r = 1, d = m), M is measurable. By IsOrientation m M ξ, ξ is continuous on M and each ξ(x), x ∈ M, satisfies IsUnitOrientationOf (ξ(x)) Q for some subspace Q.
1. (Inclusion spt T ∩ W ⊆ M ∩ W.) Let x ∈ spt T ∩ W, and suppose x ∉ M.
 (1a) As x ∈ W and closure(M) ∩ W ⊆ M, we get x ∉ closure(M). The complement of closure(M) is open, so there is r₁ > 0 with B_{r₁}(x) ∩ closure(M) = ∅; in particular no point of M lies in B_{r₁}(x). As W is open and x ∈ W, there is r₂ > 0 with B_{r₂}(x) ⊆ W. Put r₀ := min(r₁, r₂), r := r₀/2 > 0 and O := B_r(x).
 (1b) O is open. Its closure is closedBall(x, r) (closure of an open ball of positive radius in a normed space), which is compact because ℝ^P is proper, and closedBall(x, r) ⊆ B_{r₀}(x) ⊆ B_{r₂}(x) ⊆ W ⊆ U.
 (1c) T vanishes on O. Let ω ∈ 𝒟^m(U) with tsupport ω ⊆ O. Then tsupport ω ⊆ closedBall(x, r) ⊆ B_{r₀}(x) ⊆ W, so (R) gives T(ω) = k ∫_M ⟨ω(z), ξ(z)⟩ dH^m(z). For every z ∈ M we have z ∉ B_{r₁}(x) ⊇ B_{r₀}(x) ⊇ tsupport ω, hence ω(z) = 0 and ⟨ω(z), ξ(z)⟩ = ξ(z)(0) = 0 because ξ(z) is linear. The integrand vanishes at every point of M, so the integral over M is 0 (setIntegral_eq_zero_of_forall_eq_zero), and T(ω) = k·0 = 0.
 (1d) By (1b) and (1c), O is one of the sets whose union is T.zeroRegion, and x ∈ O. So x ∈ T.zeroRegion, contradicting x ∈ spt T = U ∖ T.zeroRegion. Hence x ∈ M, and x ∈ M ∩ W.
2. (Inclusion M ∩ W ⊆ spt T ∩ W.) Let w ∈ M ∩ W. Then w ∈ U since W ⊆ U. Suppose, for a contradiction, that w ∈ T.zeroRegion: there is an open O with w ∈ O (and closure(O) compact, closure(O) ⊆ U) such that T(ω) = 0 for every ω ∈ 𝒟^m(U) with tsupport ω ⊆ O.
 (2a) O ∩ W is open and contains w, so there is r₁ > 0 with B_{r₁}(w) ⊆ O ∩ W. Put r := r₁/2 > 0 and B := B_r(w). Then closedBall(w, r) ⊆ B_{r₁}(w) ⊆ O ∩ W, and B ⊆ closedBall(w, r) ⊆ W.
 (2b) (The mass of T on B vanishes.) M_B(T) is the supremum of ofReal(T(ω)) over ω ∈ 𝒟^m(U) with tsupport ω ⊆ B and covectorEuclideanNorm(ω(x)) ≤ 1 for all x. Each such ω has tsupport ω ⊆ B ⊆ O, so T(ω) = 0 and ofReal(T(ω)) = 0. A supremum of values all equal to 0 is ≤ 0, hence M_B(T) = 0.
 (2c) (Mass identity on B.) Apply mass_identity with W := B, n := m, m₀ := k: B is open; B ⊆ W ⊆ U; M is measurable and ξ is continuous on M with unit orientations (step 0); H^m(M ∩ B) ≤ H^m(M ∩ closedBall(w, r)) < ∞ because closedBall(w, r) is compact and contained in W; and if ω ∈ 𝒟^m(U) with tsupport ω ⊆ B, then tsupport ω ⊆ W and (R) gives T(ω) = k ∫_M ⟨ω, ξ⟩ dH^m. Hence M_B(T) = |k|·H^m(M ∩ B).
 (2d) (Positivity.) By density_one (n := m, z := w ∈ M), f(s) := H^m(M ∩ B_s(w))/(ω_m·ofReal(s^m)) → 1 as s → 0 within (0, ∞). Since 0 < 1, f(s) > 0 for all s in some member of that filter; also (0, r) belongs to it. The filter is non-trivial, so there is s ∈ (0, r) with f(s) > 0. If H^m(M ∩ B_s(w)) were 0, then f(s) = 0/(ω_m·ofReal(s^m)) = 0, a contradiction; so H^m(M ∩ B_s(w)) ≠ 0. As B_s(w) ⊆ B_r(w) = B, monotonicity gives H^m(M ∩ B) ≠ 0.
 (2e) Since k ≠ 0, k.natAbs ≠ 0, so |k| ≠ 0 in [0, ∞]. With (2d), |k|·H^m(M ∩ B) ≠ 0 ([0, ∞] has no zero divisors). This contradicts (2b)–(2c). Therefore w ∉ T.zeroRegion, so w ∈ U ∖ T.zeroRegion = spt T, and w ∈ spt T ∩ W.
3. (Conclusion.) Parts 1 and 2 give spt T ∩ W = M ∩ W. ∎

Lean reference proof (verified). The declaration below was compiled with Lean v4.35.0-rc3 (Mathlib 25730c7c) against the workspace build of GMT.Ch07.Submission at b4d606db, after `import GMT.Ch07.Submission` with the contract's namespace GMT.Ch07 and `open`s; the dependencies locally_closed, density_one and mass_identity were stated as axioms with their exact frozen types (in the child worktree they are the accepted theorems). It exits 0 with no `sorry`, and `#print axioms` lists propext, Classical.choice, Quot.sound, Submission.dimred_rpd_embedded_locally_closed, Submission.dimred_rpd_massOn_eq_mult_measure and Submission.dimred_rpd_submanifold_density_one. It follows the numbered proof above.

```lean
theorem Submission.codim1_dolr_rep_support_inter : ∀ (P m : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U m) (W M : Set (Euclid P)) (k : ℤ) (ξ : Euclid P → MultiVector P m), IsOpen W → W ⊆ U → k ≠ 0 → IsEmbeddedSubmanifold 1 m M → IsOrientation m M ξ → closure M ∩ W ⊆ M → (∀ K : Set (Euclid P), IsCompact K → K ⊆ W → μHE[m] (M ∩ K) ≠ ∞) → (∀ ω : TestFormOn U m, tsupport (ω : DifferentialForm (Euclid P) m) ⊆ W → T ω = k * ∫ x in M, ξ x ((ω : DifferentialForm (Euclid P) m) x) ∂μHE[m]) → T.support ∩ W = M ∩ W := by
  intro P m U T W M k ξ hW hWU hk hMemb hξ hcl hfin hrep
  obtain ⟨hMmeas, -⟩ := Submission.dimred_rpd_embedded_locally_closed P 1 m M hMemb
  have hunit : ∀ x ∈ M, ∃ Q : Submodule ℝ (Euclid P), IsUnitOrientationOf (ξ x) Q := by
    intro x hx
    obtain ⟨Q, -, hQ⟩ := hξ.2 x hx
    exact ⟨Q, hQ⟩
  ext x
  constructor
  · rintro ⟨hxS, hxW⟩
    refine ⟨?_, hxW⟩
    by_contra hxM
    have hxcl : x ∉ closure M := fun h => hxM (hcl ⟨h, hxW⟩)
    obtain ⟨r₁, hr₁, hr₁s⟩ := Metric.isOpen_iff.mp isClosed_closure.isOpen_compl x hxcl
    obtain ⟨r₂, hr₂, hr₂s⟩ := Metric.isOpen_iff.mp hW x hxW
    have hr : 0 < min r₁ r₂ / 2 := half_pos (lt_min hr₁ hr₂)
    have hcb : closedBall x (min r₁ r₂ / 2) ⊆ ball x (min r₁ r₂) :=
      closedBall_subset_ball (half_lt_self (lt_min hr₁ hr₂))
    have hb1 : ball x (min r₁ r₂) ⊆ ball x r₁ := ball_subset_ball (min_le_left _ _)
    have hb2 : ball x (min r₁ r₂) ⊆ ball x r₂ := ball_subset_ball (min_le_right _ _)
    apply hxS.2
    refine Set.mem_sUnion.mpr ⟨ball x (min r₁ r₂ / 2), ⟨isOpen_ball, ?_, ?_, ?_⟩, mem_ball_self hr⟩
    · rw [closure_ball x hr.ne']
      exact isCompact_closedBall x _
    · rw [closure_ball x hr.ne']
      exact hcb.trans (hb2.trans (hr₂s.trans hWU))
    · intro ω hω
      have hωb : tsupport (ω : DifferentialForm (Euclid P) m) ⊆ ball x (min r₁ r₂) :=
        hω.trans (ball_subset_closedBall.trans hcb)
      rw [hrep ω (hωb.trans (hb2.trans hr₂s)), setIntegral_eq_zero_of_forall_eq_zero, mul_zero]
      intro z hz
      have hz' : z ∉ tsupport (ω : DifferentialForm (Euclid P) m) := by
        intro h
        exact hr₁s (hb1 (hωb h)) (subset_closure hz)
      rw [image_eq_zero_of_notMem_tsupport hz']
      simp
  · rintro ⟨hxM, hxW⟩
    refine ⟨⟨hWU hxW, ?_⟩, hxW⟩
    intro hz
    obtain ⟨O, ⟨hO, -, -, hvan⟩, hxO⟩ := Set.mem_sUnion.mp hz
    obtain ⟨r₁, hr₁, hr₁s⟩ := Metric.isOpen_iff.mp (hO.inter hW) x ⟨hxO, hxW⟩
    have hr : 0 < r₁ / 2 := half_pos hr₁
    have hcb : closedBall x (r₁ / 2) ⊆ O ∩ W :=
      (closedBall_subset_ball (half_lt_self hr₁)).trans hr₁s
    have hballW : ball x (r₁ / 2) ⊆ W := ball_subset_closedBall.trans (hcb.trans inter_subset_right)
    have hzero : T.massOn (ball x (r₁ / 2)) = 0 := by
      refine nonpos_iff_eq_zero.mp ?_
      unfold GeometricCurrentOn.massOn
      refine sSup_le ?_
      rintro _ ⟨ω, hω, rfl⟩
      dsimp only
      rw [hvan ω (hω.1.trans (ball_subset_closedBall.trans (hcb.trans inter_subset_left)))]
      simp
    have hmass := Submission.dimred_rpd_massOn_eq_mult_measure P m U T M (ball x (r₁ / 2)) k ξ
      isOpen_ball (hballW.trans hWU) hMmeas hξ.1 hunit
      (ne_top_of_le_ne_top (hfin _ (isCompact_closedBall x _) (hcb.trans inter_subset_right))
        (measure_mono (inter_subset_inter_right _ ball_subset_closedBall)))
      (fun ω hω => hrep ω (hω.trans hballW))
    have hpos : μHE[m] (M ∩ ball x (r₁ / 2)) ≠ 0 := by
      have hlim := Submission.dimred_rpd_submanifold_density_one P m M x hMemb hxM
      obtain ⟨s, hs1, hs2⟩ :=
        ((hlim.eventually (lt_mem_nhds zero_lt_one)).and (Ioo_mem_nhdsGT hr)).exists
      intro h0
      have : μHE[m] (M ∩ ball x s) = 0 :=
        measure_mono_null (inter_subset_inter_right _ (ball_subset_ball hs2.2.le)) h0
      rw [this, ENNReal.zero_div] at hs1
      exact lt_irrefl _ hs1
    have hk' : (k.natAbs : ℝ≥0∞) ≠ 0 := by simpa using hk
    rw [hmass] at hzero
    exact mul_ne_zero hk' hpos hzero
```

## Key steps

1. Points of W off M: relative closedness gives a ball B_r(x) whose closure is compact, lies in W ⊆ U and misses M; by the representation T vanishes on B_r(x), so x ∈ T.zeroRegion and x ∉ spt T.
2. Points w of M ∩ W lie in U; if w ∈ T.zeroRegion, a small ball B with closure in O ∩ W has M_B(T) = 0 because every admissible form gives T(ω) = 0.
3. mass_identity on B gives M_B(T) = |k|·H^m(M ∩ B) (finiteness from the compact closedBall(w, r) ⊆ W).
4. density_one at w gives H^m(M ∩ B) > 0, and |k| ≥ 1, contradicting M_B(T) = 0; so w ∈ spt T.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; sha256sum local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `sed -n 1,457p GMT/Ch07/Contract.lean (IsEmbeddedSubmanifold, tangentSpace, IsOrientation, IsUnitOrientationOf, regularSet, HasMassDensity, unitBallVolume, MultiVector)`
- `grep -n 'def support|def zeroRegion|isOpen_zeroRegion|VanishesOn|def massOn|massAdmissibleOn|structure GeometricCurrentOn|testFormOnSubmodule|abbrev Covector|def covectorEuclideanNorm' simongmt/Poincare/SimonGMT/Chapter06/{Currents,CurrentLocalEquality,Mass,Forms}.lean`
- `python3 scans of dag.json: lean_statement mentions IsEmbeddedSubmanifold, IsOrientation, regularSet, tangentSpace, support, massOn; children of regular_point_density-a1, simons_regular_cone-a1, imrep_mass_and_support-a1, cone_constant_density_planar-a1; status and candidate_commit of dimred_rpd_submanifold_density_one, dimred_rpd_massOn_eq_mult_measure, dimred_rpd_embedded_locally_closed, dimred_rpd_near_isometric_chart, dor_ims_unitOrientation_dual, chart_tangentSpace_eq_range_fderiv, dimred_rpd_bilipschitz_image_measure, dor_ims_support_of_massOn_eq, dimred_regular_point_density, idtp_ccd_regular_point_support, codim1_massOn_eq_lintegral_of_oriented_rep`
- `grep -rln IsEmbeddedSubmanifold local-references/123e8435b4a2469b/project; grep -rn 'theorem.*inter_open|theorem.*tangentSpace_inter|theorem.*support_inter' local-references/123e8435b4a2469b/project; grep -rn 'theorem .*support.*rep|theorem .*mem_support' simongmt/Poincare/SimonGMT/Chapter06/*.lean`
- `grep -rn 'setIntegral_eq_of_subset_of_forall_sdiff_eq_zero|setIntegral_eq_zero_of_forall_eq_zero|image_eq_zero_of_notMem_tsupport|IsOpen.closure_inter|ContinuousOn.isOpen_inter_preimage|HasDerivAt.scomp|ContDiffOn.comp|closure_ball|tendsto_nhds_unique|integral_const_mul' Mathlib`
- `runtime.py _existing_lean_name_problem, _accepted_checkpoint, _solve_children, _install_parent_supplied_child_handoff, _overlay_accepted_children, _wait_for_accepted_dependencies; store.py ensure; models.py Subproblem/Decomposition; lean_contract.py validate_lean_statement`
- `git for-each-ref --format='%(objectname)' | sort -u | xargs -n 100 sh -c 'git grep -l -E "codim1_dolr_(embedded_inter_open|rep_hasMassDensity|rep_support_inter)" "$@" -- GMT' _ (positive control: Submission.dimred_rpd_submanifold_density_one)`
- `lean -DautoImplicit=false /tmp/dolr-split/check/Types2.lean, Children2.lean, Assembly2.lean (LEAN_PATH = .lake/build/lib/lean plus every package's .lake/build/lib/lean)`
- `book: chapter-02.txt 850-871; chapter-03.txt 290-316; chapter-06.txt 225-233 and 290-305; chapter-07.txt 588-600`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Neighborhoods.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/RCLike/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Topology/Separation/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-b47a776447/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-7577af74dd/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-regular-point-density-a1-density-one-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-regular-point-density-a1-mass-identity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-regular-point-density-a1-locally-closed-a1/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/store.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/models.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/dolr-split/check/Types2.lean`
- `/tmp/dolr-split/check/Children2.lean`
- `/tmp/dolr-split/check/Assembly2.lean`

Pins match. The snapshot manifest records project b4d606db and Mathlib 25730c7c, equal to workspace HEAD and the pinned Mathlib. The snapshot Contract.lean, the workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…). So the selected frozen type and the definitions it uses (regularSet, IsEmbeddedSubmanifold, tangentSpace, IsOrientation, HasMassDensity) are unchanged.
Library.
- SimonGMT Chapter06 defines T.support = U \ T.zeroRegion, where zeroRegion is the union of the open W with compact closure inside U on which T vanishes (CurrentLocalEquality.lean). It defines T.massOn W as a supremum of ofReal T(ω) over massAdmissibleOn (Mass.lean), and TestFormOn as the smooth compactly supported forms with tsupport in U (Currents.lean).
- SimonGMT has no lemma relating the support or the mass to a local representation m[[M]]. The snapshot project has no embedded-submanifold lemmas beyond the contract definitions (no match).
- The pinned Mathlib supplies every tool the child and glue proofs use (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero, setIntegral_eq_zero_of_forall_eq_zero, image_eq_zero_of_notMem_tsupport, IsOpen.closure_inter, ContinuousOn.isOpen_inter_preimage, HasDerivAt.scomp, ContDiffOn.comp, closure_ball, tendsto_nhds_unique, ENNReal.Tendsto.const_mul).
DAG.
- The parent handoff listed dimred_rpd_submanifold_density_one and dimred_rpd_massOn_eq_mult_measure as unaccepted, reusable by child sessions once accepted. Both are now accepted (candidate commits e8842d90b78f and 5fcaddaa05c1), as is dimred_rpd_embedded_locally_closed (6da66b1edf6f). Their frozen types are copied byte-for-byte, so they are reused with no new DAG node (runtime _existing_lean_name_problem / _accepted_checkpoint).
- idtp_ccd_regular_point_support and codim1_massOn_eq_lintegral_of_oriented_rep remain unaccepted in other branches and are not used.
- The 3 new codim1_dolr_ names are free in dag.json (974 nodes), GMT/, SimonGMT and all 1734 ref tips (corrected git grep, positive control 6 hits).
Lean.
- Types2.lean elaborates all 6 child types (exit 0).
- Assembly2.lean proves the selected frozen type from open_piece, rep_density, rep_support and locally_closed as axioms (exit 0; #print axioms: propext, Classical.choice, Quot.sound and those 4).
- Children2.lean proves the 3 new children from the 3 accepted declarations, with no sorry (exit 0).


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
