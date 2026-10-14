<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1.slice_decomposition-a1.level_decomposition-a1 -->

## Theorem `Submission.dimred_mbl_lc_sd_level_decomposition`

Let P, m ∈ ℕ and n := m + 1; all currents are currents in ℝ^P (SimonGMT GeometricCurrentOn univ, ℝ^P = Euclid P). Let R, A ∈ 𝒟_{n+1}(ℝ^P) and B, S′ ∈ 𝒟_n(ℝ^P). Let ρ be an integer multiplicity representation in ℝ^P of degree n + 1 (contract IMRep univ (n + 1)) with ρ.Represents R, i.e. R(ω) = ρ.action(ω) for every ω ∈ 𝒟^{n+1}(ℝ^P), and let β be any IMRep in ℝ^P of degree n; write μ_ρ := ρ.measure, ξ_ρ := ρ.orient, μ_β := β.measure, ξ_β := β.orient. Let f : ℝ^P → ℝ be continuous, t ∈ ℝ, W₀ ⊆ ℝ^P open and c ∈ [0, ∞] with c ≠ ∞, and put W := {x : f(x) < t}, F := {x : f(x) ≤ t}, Σ := {x : f(x) = t}. Assume: (i) S′ is integer multiplicity (contract IsIntegerMultiplicity); (ii) F is compact and F ⊆ W₀; (iii) A(ω) = ∫_W ξ_ρ(x)(ω(x)) dμ_ρ(x) for every ω ∈ 𝒟^{n+1}(ℝ^P) (TestFormOn univ (n + 1)); (iv) B(η) = ∫_W ξ_β(x)(η(x)) dμ_β(x) for every η ∈ 𝒟ⁿ(ℝ^P); (v) ∂A(η) = B(η) for every η ∈ 𝒟ⁿ(ℝ^P) whose topological support tsupport η is disjoint from Σ; (vi) M_{W₀}(∂A − B) ≤ c, where M_G is the SimonGMT local mass massOn G (Euclidean coefficient norm) and ∂A − B is the difference current; (vii) (BR′) every integer multiplicity T ∈ 𝒟_{n+1}(ℝ^P) such that M_G(∂T) < ∞ for every open G ⊆ ℝ^P with compact closure (contract CompactlyContained G univ) has an integer multiplicity boundary ∂T. Then there are Y, Sr ∈ 𝒟_n(ℝ^P) such that: Y is integer multiplicity, ∂Y = 0 and spt Y ⊆ F (GeometricCurrentOn.support); M(Sr) ≤ M_{W₀}(S′) + c, where M = mass = M_{ℝ^P}; Q.measure(Σ) ≤ c for every IMRep Q in ℝ^P (degree n) with Q.Represents Y; and Y(ω) = ∂R(ω) and Sr(ω) = S′(ω) for every ω ∈ 𝒟ⁿ(ℝ^P) with tsupport ω ⊆ W.

Node: `root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1.slice_decomposition-a1.level_decomposition-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6173

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/667, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4196, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4695, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4704, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4728, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4710, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1174, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5327

Decomposition children: None

## Lean problem

Declaration: `Submission.dimred_mbl_lc_sd_level_decomposition`

```lean
∀ (P m : ℕ) (R A : GeometricCurrentOn (univ : Set (Euclid P)) (m + 2)) (B S' : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (ρ : IMRep (univ : Set (Euclid P)) (m + 2)) (β : IMRep (univ : Set (Euclid P)) (m + 1)) (f : Euclid P → ℝ) (t : ℝ) (W₀ : Set (Euclid P)) (c : ℝ≥0∞), ρ.Represents R → IsIntegerMultiplicity S' → Continuous f → IsOpen W₀ → IsCompact {x | f x ≤ t} → {x | f x ≤ t} ⊆ W₀ → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 2), A ω = ∫ x in {x | f x < t}, ρ.orient x ((ω : DifferentialForm (Euclid P) (m + 2)) x) ∂ρ.measure) → (∀ η : TestFormOn (univ : Set (Euclid P)) (m + 1), B η = ∫ x in {x | f x < t}, β.orient x ((η : DifferentialForm (Euclid P) (m + 1)) x) ∂β.measure) → (∀ η : TestFormOn (univ : Set (Euclid P)) (m + 1), Disjoint (tsupport (η : DifferentialForm (Euclid P) (m + 1))) {x | f x = t} → A.boundary η = B η) → (A.boundary - B).massOn W₀ ≤ c → c ≠ ∞ → (∀ T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 2), IsIntegerMultiplicity T → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W univ → T.boundary.massOn W < ∞) → IsIntegerMultiplicity T.boundary) → ∃ Y Sr : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), IsIntegerMultiplicity Y ∧ Y.boundary = 0 ∧ Y.support ⊆ {x | f x ≤ t} ∧ Sr.mass ≤ S'.massOn W₀ + c ∧ (∀ Q : IMRep (univ : Set (Euclid P)) (m + 1), Q.Represents Y → Q.measure {x | f x = t} ≤ c) ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), tsupport (ω : DifferentialForm (Euclid P) (m + 1)) ⊆ {x | f x < t} → Y ω = R.boundary ω ∧ Sr ω = S' ω
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

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1.slice_decomposition-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.local_comparison-a1.slice_decomposition-a1.level_decomposition-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the parent proof (selected node slice_decomposition), steps 6–12, i.e. Simon 7.2.4 (3), (6), (7) (chapter-07.txt lines 193–221) for one index j and the chosen level, with the corrected sign S̃ = S′⌞W − P. The slice data of the parent (A = A_{j,t}, B = B_{j,t} obtained from (SL′)) and the bound L·D_j of the parent's step 7 are turned into the hypotheses (iii)–(vi), with c in place of L·D_j; the parent's (MR), (IMC), (IR), (MT), (COB), (ML) are the siblings below, and the parent's step 0 and its (IR)(c) with E := ℝ^P are packaged in the sibling imrep_measure_basic.
Siblings: (MR) mass_and_support, first conjunct: if the IMRep Q in the open set U represents X ∈ 𝒟_k(U), then M_G(X) = μ_Q(G) for every open G. (IMC) im_calculus (b): for an IMRep Q in an open U and a Borel set E there are a current X and an IMRep Q′ in U with Q′.Represents X, carrier Q′ = carrier Q ∩ E, Q′.mult = Q.mult, Q′.orient = Q.orient. (IR) imrep_restriction (c): for such Q, E, Q′: μ_{Q′} = μ_Q⌞E and Q′.action(ω) = ∫_E ξ_Q(ω) dμ_Q for every form ω. (MT) mass_triangle: if Z(ω) = X(ω) + γ·Y(ω) for every test form ω with tsupport ω ⊆ G and |γ| ≤ 1, then M_G(Z) ≤ M_G(X) + M_G(Y). (COB) compact_outer_bound: for U open, E ⊆ U compact, measures μ, ν with ν finite on compact subsets of U and c′ ∈ [0, ∞]: if μ(G) ≤ ν(G) + c′ for every open G ⊇ E with closure(G) compact and contained in U, then μ(E) ≤ ν(E) + c′. (ML) mass_localization: if X(ω) = 0 for every test form ω with tsupport ω disjoint from a compact set C contained in an open set V, then M_G(X) ≤ M_V(X) for every set G. (SV) support_of_vanishing: for U open, K ⊆ U compact and X ∈ 𝒟_k(U) with X(ω) = 0 whenever tsupport ω ∩ K = ∅, spt X ⊆ K. (IB) imrep_measure_basic: for every IMRep Q in ℝ^P (degree k), (e) μ_Q(K) < ∞ for every compact K, and (g) Q.action(ω) = ∫ ξ_Q(ω) dμ_Q for every k-form ω.
Conventions. ℝ^P is open, so (MR), (IMC), (SV) apply with U := ℝ^P. For currents X, Y of the same degree, (X − Y)(ω) = X(ω) − Y(ω). For a test form ω, dω is its exterior derivative, ∂T(ω) = T(dω), and tsupport dω ⊆ tsupport ω (SimonGMT tsupport_exteriorDerivative_subset); a function vanishes at every point outside its tsupport.
0. (The sets.) W is open and F, Σ are closed, because f is continuous. W ⊆ F, Σ ⊆ F and Σ ∩ W = ∅ (f(x) = t and f(x) < t exclude each other). Σ is compact, as a closed subset of the compact set F. By (ii), Σ ⊆ F ⊆ W₀ and W ⊆ F ⊆ W₀. W is Borel, being open.
1. (Restrictions to W; parent step 6.) (a) (IMC)(b) for ρ and E := W gives an IMRep ρ′ in ℝ^P with carrier ρ.carrier ∩ W, multiplicity ρ.mult and orientation ρ.orient. By (IR)(c) for ρ, E := W and ρ′, ρ′.action(ω) = ∫_W ξ_ρ(ω) dμ_ρ for every form ω. Comparing with (iii), A(ω) = ρ′.action(ω) for every ω ∈ 𝒟^{n+1}(ℝ^P): ρ′ represents A, so A is integer multiplicity. (b) In the same way (IMC)(b) and (IR)(c) for β and W give an IMRep β′ with μ_{β′} = μ_β⌞W and β′.action(η) = ∫_W ξ_β(η) dμ_β = B(η) by (iv); so β′ represents B. (c) By (i) choose an IMRep σ representing S′. (IMC)(b) for σ and W gives a current S′_W ∈ 𝒟_n(ℝ^P) and an IMRep σ′ representing S′_W with carrier σ.carrier ∩ W and the multiplicity and orientation of σ; by (IR)(c), μ_{σ′} = μ_σ⌞W and S′_W(ω) = σ′.action(ω) = ∫_W ξ_σ(ω) dμ_σ for every ω ∈ 𝒟ⁿ(ℝ^P).
2. (The error current P; parent step 7.) Put P := ∂A − B ∈ 𝒟_n(ℝ^P). If η ∈ 𝒟ⁿ(ℝ^P) and tsupport η is disjoint from Σ, then P(η) = ∂A(η) − B(η) = 0 by (v). Σ is compact and contained in the open set W₀ (step 0), so (ML) (C := Σ, V := W₀) and (vi) give M_G(P) ≤ M_{W₀}(P) ≤ c for every set G ⊆ ℝ^P.
3. (Triangle inequality.) For every η, ∂A(η) = B(η) + 1·P(η). By (MT) with γ := 1, M_G(∂A) ≤ M_G(B) + M_G(P) ≤ M_G(B) + c for every set G (step 2).
4. (Y := ∂A is an integer multiplicity cycle; parent step 8.) Let G be open with closure(G) compact. By (MR) for β′, which represents B (step 1(b)), M_G(B) = μ_{β′}(G) ≤ μ_{β′}(closure G) < ∞ by (IB)(e). With step 3 and c ≠ ∞, M_G(∂A) ≤ M_G(B) + c < ∞. A is integer multiplicity (step 1(a)), so (vii) shows that ∂A is integer multiplicity. Put Y := ∂A. Then ∂Y = ∂∂A = 0 (∂∂ = 0, SimonGMT GeometricCurrentOn.boundary_boundary; A has degree n + 1 = m + 2).
5. (spt Y ⊆ F; parent step 9.) Let η ∈ 𝒟ⁿ(ℝ^P) with tsupport η ∩ F = ∅. For x ∈ W we have x ∈ F, hence x ∉ tsupport η ⊇ tsupport dη, so dη(x) = 0 and ξ_ρ(x)(dη(x)) = 0. Therefore Y(η) = A(dη) = ∫_W ξ_ρ(dη) dμ_ρ = 0 by (iii). By (SV) with U := ℝ^P and the compact set K := F, spt Y ⊆ F.
6. (The remainder Sr; parent step 10.) Put Sr := S′_W − P. For every ω, Sr(ω) = S′_W(ω) + (−1)·P(ω), so (MT) with G := ℝ^P and γ := −1 gives M(Sr) ≤ M(S′_W) + M(P). By (MR) for σ′ and G := ℝ^P, then step 1(c), then (MR) for σ and the open set G := W: M(S′_W) = μ_{σ′}(ℝ^P) = (μ_σ⌞W)(ℝ^P) = μ_σ(W) = M_W(S′) ≤ M_{W₀}(S′), the last inequality because M_G(S′) is monotone in G (SimonGMT GeometricCurrentOn.massOn_mono) and W ⊆ W₀. By step 2 with G := ℝ^P, M(P) ≤ c. Hence M(Sr) ≤ M_{W₀}(S′) + c.
7. (The measure of Σ for every representation of Y; parent step 11.) Let Q be an IMRep in ℝ^P representing Y. Let G ⊇ Σ be open with closure(G) compact. By (MR) for Q and for β′, and by step 3, μ_Q(G) = M_G(Y) ≤ M_G(B) + c = μ_{β′}(G) + c. The measure μ_{β′} is finite on compact sets by (IB)(e). So (COB) with U := ℝ^P, E := Σ (compact, step 0), μ := μ_Q, ν := μ_{β′} and c′ := c gives μ_Q(Σ) ≤ μ_{β′}(Σ) + c. Σ is closed, hence Borel, so μ_{β′}(Σ) = (μ_β⌞W)(Σ) = μ_β(Σ ∩ W) = μ_β(∅) = 0 (steps 1(b), 0). Hence Q.measure(Σ) ≤ c.
8. (Identities on W; parent step 12.) Let ω ∈ 𝒟ⁿ(ℝ^P) with tsupport ω ⊆ W. For x ∉ W we have x ∉ tsupport ω ⊇ tsupport dω, so ω(x) = 0 and dω(x) = 0. (a) Y(ω) = A(dω) = ∫_W ξ_ρ(dω) dμ_ρ by (iii); the integrand ξ_ρ(x)(dω(x)) vanishes for x ∉ W, so the integral over W equals the integral over ℝ^P (Mathlib setIntegral_eq_integral_of_forall_compl_eq_zero), which is ρ.action(dω) by (IB)(g); since ρ represents R and dω ∈ 𝒟^{n+1}(ℝ^P), ρ.action(dω) = R(dω) = ∂R(ω). So Y(ω) = ∂R(ω). (b) tsupport ω ⊆ W is disjoint from Σ (step 0), so P(ω) = 0 by step 2, and Sr(ω) = S′_W(ω) = ∫_W ξ_σ(ω) dμ_σ (step 1(c)). Since ω vanishes off W, this equals ∫ ξ_σ(ω) dμ_σ = σ.action(ω) (IB)(g) = S′(ω), σ representing S′. So Sr(ω) = S′(ω).
Steps 4–8 give all conclusions: Y is integer multiplicity with ∂Y = 0 (step 4) and spt Y ⊆ F (step 5); M(Sr) ≤ M_{W₀}(S′) + c (step 6); Q.measure(Σ) ≤ c for every IMRep Q representing Y (step 7); and Y(ω) = ∂R(ω), Sr(ω) = S′(ω) whenever tsupport ω ⊆ W (step 8). ∎

## Key steps

1. Restrict the representations ρ, β and a representation σ of S′ to the Borel set W = {f < t} (im_calculus (b), imrep_restriction (c)): ρ′ represents A, β′ represents B with μ_{β′} = μ_β⌞W, and σ′ represents S′⌞W with μ_{σ′} = μ_σ⌞W.
2. P := ∂A − B vanishes on forms supported off the compact level set Σ ⊆ W₀, so mass_localization and (vi) give M_G(P) ≤ c for every G; mass_triangle gives M_G(∂A) ≤ M_G(B) + c.
3. M_G(B) = μ_{β′}(G) < ∞ for G with compact closure, so (BR′) makes Y := ∂A integer multiplicity; ∂Y = 0, and Y vanishes on forms supported off F, so spt Y ⊆ F by support_of_vanishing.
4. Sr := S′⌞W − P: mass_triangle and mass_and_support give M(Sr) ≤ M_W(S′) + c ≤ M_{W₀}(S′) + c.
5. For a representation Q of Y, μ_Q(G) ≤ μ_{β′}(G) + c on open G ⊇ Σ, so compact_outer_bound gives μ_Q(Σ) ≤ μ_β(Σ ∩ W) + c = c; for tsupport ω ⊆ W, Y(ω) = ∂R(ω) and Sr(ω) = S′(ω) because ω and dω vanish off W.

## Reference use

### local-project

Queries:
- `cat RUN/local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; cmp SNAP/project/GMT/Ch07/Contract.lean and SNAP/project/GMT/Ch07/Submission.lean against the workspace copies`
- `rg -n 'structure IMRep|def IMRep.measure|def IsIntegerMultiplicity|def CompactlyContained|def IMRep.Represents' SNAP/project/GMT/Ch07/Contract.lean`
- `rg -n 'dimred_mbl_lc_sd|level_decomposition|slice_decomposition' SNAP/project SNAP/mathlib/Mathlib (no match)`
- `rg -n 'theorem setIntegral_eq_integral_of_forall_compl_eq_zero|theorem setIntegral_eq_zero_of_forall_eq_zero|theorem restrict_apply_univ|protected theorem Tendsto.const_mul|exists_forall_of_atTop|theorem tendsto_add_atTop_nat|IsBounded.subset_ball|theorem image_eq_one_of_notMem_mulTSupport|theorem limsup_le_limsup' SNAP/mathlib/Mathlib`
- `python3 scans of RUN/dag.json: lean_statement regex 'measure K < ∞|measure K ≠ ∞'; children of the three local_comparison nodes; lean_name lookups (status, candidate_commit, byte-identical lean_statement) of the 10 reused declarations; collision check for dimred_mbl_lc_sd_level_decomposition (none)`
- `git show d39c95fa2 -- GMT/Ch07/Submission.lean (speculative Lean draft of cmc_local_comparison_inequality, the analogous Simon 7.2.4 argument)`
- `grep -n 'def GeometricCurrentOn.massOn|def GeometricCurrentOn.mass|theorem GeometricCurrentOn.massOn_mono|def GeometricCurrentOn.support|boundary_apply|boundary_boundary|tsupport_exteriorDerivative_subset' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/*.lean`
- `sed -n 150,280p book/chapter-07.txt; grep -n '(3)|(6)|(7)' book/chapter-07.txt (Simon 7.2.4 (3) line 196, (6) line 208, (7) line 220)`
- `contract_scope(Contract.lean, 'GMT.Ch07.main_theorem') from verifier/gmt-compare.py (replayed child comparator scope); _existing_lean_name_problem and _accepted_checkpoint in runtime.py (reuse rules)`
- `lake env lean /tmp/sd_split/Types.lean; lake env lean /tmp/sd_split/N1.lean; lake env lean /tmp/sd_split/Assembly.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-local-compariso-cc4a50e6b1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-local-comparison-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-local-comparison-a1-lipsch-80245fc994/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-constant-multiplicity-reduction-a1-support-a67ad69f81/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-6249c06eba/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/tmp/sd_split/Types.lean`
- `/tmp/sd_split/N1.lean`
- `/tmp/sd_split/Assembly.lean`

Pins match the manifest (project b4d606d = HEAD, Mathlib 25730c7c) and the snapshot's Contract.lean and Submission.lean are byte-identical to the workspace copies (IMRep line 61, IMRep.Represents 83, IMRep.measure 88, IsIntegerMultiplicity 92, CompactlyContained 127). The snapshot's Mathlib supplies the lemmas used by the new child's proof and the assembly: setIntegral_eq_integral_of_forall_compl_eq_zero and setIntegral_eq_zero_of_forall_eq_zero (Integral/Bochner/Set.lean 486, 357), Measure.restrict_apply_univ (Measure/Restrict.lean 168), ENNReal.Tendsto.const_mul (Instances/ENNReal/Lemmas.lean 354), Eventually.exists_forall_of_atTop (AtTopBot/Basic.lean 86), tendsto_add_atTop_nat (AtTopBot/Basic.lean 331), Bornology.IsBounded.subset_ball (MetricSpace/Bounded.lean 111), image_eq_zero_of_notMem_tsupport (to_additive of Algebra/Support.lean 111), liminf_le_liminf (to_dual of LiminfLimsup.lean 159); SimonGMT supplies GeometricCurrentOn.boundary_apply/boundary_boundary (Currents.lean 333/365), tsupport_exteriorDerivative_subset (Currents.lean 182) and GeometricCurrentOn.massOn_mono (Mass.lean 81). Neither the snapshot nor the DAG contains the per-index slice decomposition (no match), so level_decomposition is new and its name is unused. Ten comparator-accepted declarations (status accepted, candidate commits set) are reused with byte-identical types: lcmp_exists_lipschitz_cutoff, cbr_imRep_measure_basic, rsd_cmr_support_subset_of_vanish, dor_imrep_massOn_eq_measure_and_support, cmc_imRep_locality_restrict_sub, lcmp_imRep_measure_restrict, lcmp_massOn_le_add_of_eval_eq, lcmp_measure_le_add_of_open_nhds, lcmp_massOn_le_of_vanish_off_compact, lcmp_exists_good_slice_level. Lean: all 12 types elaborate in the comparator scope; the conditional proof of the new child from its 8 dependencies and the conditional proof of the exact parent type from level_decomposition and five reused types compile with axioms propext, Classical.choice, Quot.sound.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
