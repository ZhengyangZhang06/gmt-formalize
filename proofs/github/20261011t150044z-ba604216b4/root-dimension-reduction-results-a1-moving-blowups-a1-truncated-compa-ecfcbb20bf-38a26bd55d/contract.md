<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.moving_blowups-a1.truncated_compactness-a1.truncation-a1 -->

## Theorem `Submission.dimred_mbl_tc_truncate_at_good_radius`

Let P, m ∈ ℕ, n := m + 1, U ⊆ ℝ^P open, S, A ∈ 𝒟_n(U) (GeometricCurrentOn U n) and R = (M, θ, ξ) an integer multiplicity representation in U (contract IMRep U n) of S (R.Represents S), with weight μ := R.measure = θHⁿ⌞M (Hⁿ = μHE[n]). Let ρ, s ∈ ℝ with 0 < ρ < s and B_s := ball(0, s) ⊆ U, and assume: (i) ∂S(β) = 0 for every β ∈ 𝒟^m(U) with tsupport β ⊆ B_s; (ii) A(ω) = ∫_{ball(0,ρ)} ξ(x)(ω(x)) dμ(x) (Bochner integral) for every ω ∈ 𝒟ⁿ(U); (iii) M_{B_s}(∂A) < ∞ (SimonGMT massOn, Euclidean coefficient norm). Then there are Ŝ ∈ 𝒟_n(ℝ^P) (GeometricCurrentOn univ n) and an IMRep R′ in ℝ^P such that R′ represents Ŝ (so Ŝ is integer multiplicity), R′.measure = μ⌞ball(0, ρ), Ŝ(ω) = currentEval(S, ω) for every ω ∈ 𝒟ⁿ(ℝ^P) with tsupport ω ⊆ ball(0, ρ), ∂Ŝ(β) = 0 for every β ∈ 𝒟^m(ℝ^P) with tsupport β ⊆ ball(0, ρ), and M_{ℝ^P}(∂Ŝ) ≤ M_{B_s}(∂A).

Node: `root.dimension_reduction_results-a1.moving_blowups-a1.truncated_compactness-a1.truncation-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5065

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4607, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4196, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4695

Decomposition children: None

## Lean problem

Declaration: `Submission.dimred_mbl_tc_truncate_at_good_radius`

```lean
∀ (P m : ℕ) (U : Set (Euclid P)) (S A : GeometricCurrentOn U (m + 1)) (R : IMRep U (m + 1)) (ρ s : ℝ), IsOpen U → R.Represents S → (∀ β : TestFormOn U m, tsupport (β : DifferentialForm (Euclid P) m) ⊆ ball 0 s → S.boundary β = 0) → 0 < ρ → ρ < s → ball (0 : Euclid P) s ⊆ U → (∀ ω : TestFormOn U (m + 1), A ω = ∫ x in ball (0 : Euclid P) ρ, R.orient x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂R.measure) → A.boundary.massOn (ball 0 s) ≠ ∞ → ∃ (Ŝ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (R' : IMRep (univ : Set (Euclid P)) (m + 1)), R'.Represents Ŝ ∧ R'.measure = R.measure.restrict (ball 0 ρ) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), tsupport (ω : DifferentialForm (Euclid P) (m + 1)) ⊆ ball 0 ρ → Ŝ ω = currentEval S (ω : DifferentialForm (Euclid P) (m + 1))) ∧ (∀ β : TestFormOn (univ : Set (Euclid P)) m, tsupport (β : DifferentialForm (Euclid P) m) ⊆ ball 0 ρ → Ŝ.boundary β = 0) ∧ Ŝ.boundary.massOn univ ≤ A.boundary.massOn (ball 0 s)
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

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.truncated_compactness-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.truncated_compactness-a1.truncation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 3 (Simon Ch. 6, 2.9 and 3.2: the restriction T⌞B of T = τ(M, θ, ξ) to a ball is τ(M ∩ B, θ, ξ), chapter-06.txt lines 284–288 and 755–767; the bound on its boundary is the slice estimate 4.6–4.10, lines 1335–1376, which the parent supplies through hypotheses (ii)–(iii)).
Siblings: im_calculus (IMC), part (b); imrep_restriction (RS), part (c); eval_mass_bound (E1).
Notation: n := m + 1; Hⁿ := μHE[n]; M := R.carrier, θ := R.mult, ξ := R.orient, μ := R.measure; B_r := ball(0, r); ⟨α, ξ(x)⟩ := ξ(x)(α); |α| := covectorEuclideanNorm α; 𝒟^k(V) := TestFormOn V k (a form α belongs to 𝒟^k(V) iff it is smooth, compactly supported and tsupport α ⊆ V).

0. Preliminary facts.
 (F1) closedBall(0, ρ) ⊆ B_s ⊆ U since ρ < s; so B_ρ ⊆ U, and closedBall(0, ρ) is a compact subset of U.
 (F2) |tα| = |t|·|α| for t ∈ ℝ and every covector α: (tα)(e_I) = t·α(e_I), so Σ_I [I strictly increasing](tα)(e_I)² = t²·Σ_I [I strictly increasing]α(e_I)², and √(t²X) = |t|√X for X ≥ 0.
 (F3) If x ∉ tsupport α then α(x) = 0 (image_eq_zero_of_notMem_tsupport), hence ⟨α(x), ξ(x)⟩ = 0 by linearity of ξ(x).

1. (Restriction in U.) Apply (IMC)(b) to R and the Borel set E := B_ρ (U is open): there is an IMRep R₁ in U with carrier M ∩ B_ρ, multiplicity θ and orientation ξ (the current it represents is not needed). By (RS)(c) applied to R, E = B_ρ and R′ := R₁: R₁.measure = μ⌞B_ρ, and R₁.action(α) = ∫_{B_ρ} ⟨α, ξ⟩ dμ for every n-form α (no regularity required).

2. (The same data as a representation in ℝ^P.) Let R₂ be the IMRep in ℝ^P with carrier M ∩ B_ρ, multiplicity θ and orientation ξ. Its fields measurableSet_carrier, rectifiable, measurable_mult, mult_pos, aestronglyMeasurable_orient and orients only involve carrier, multiplicity, orientation and Hⁿ, so they are those of R₁; carrier ⊆ ℝ^P is trivial. Local integrability: for every compact K, (M ∩ B_ρ) ∩ K ⊆ M ∩ closedBall(0, ρ), so ∫_{(M∩B_ρ)∩K} θ dHⁿ ≤ ∫_{M∩closedBall(0,ρ)} θ dHⁿ < ∞, by monotonicity of the lower integral in the domain (lintegral_mono_set) and R.locallyIntegrable_mult for the compact set closedBall(0, ρ) ⊆ U (F1).

3. (The current Ŝ.) Apply (IMC)(b) to R₂ (domain ℝ^P, open) and E := ℝ^P: there are Ŝ ∈ 𝒟_n(ℝ^P) and an IMRep R′ in ℝ^P representing Ŝ, with carrier (M ∩ B_ρ) ∩ ℝ^P = M ∩ B_ρ, multiplicity θ and orientation ξ. IMRep.measure and IMRep.action depend only on carrier, multiplicity and orientation, so R′.measure = R₁.measure = μ⌞B_ρ (the second claim), and for every ω ∈ 𝒟ⁿ(ℝ^P):
 Ŝ(ω) = R′.action(ω) = R₁.action(ω) = ∫_{B_ρ} ⟨ω, ξ⟩ dμ.   (∗)

4. (Agreement.) Let ω ∈ 𝒟ⁿ(ℝ^P) with tsupport ω ⊆ B_ρ. Then ω is smooth with compact support and tsupport ω ⊆ U (F1), so ω ∈ 𝒟ⁿ(U) and currentEval(S, ω) = S(ω) (definition of currentEval, positive branch). As R represents S, S(ω) = R.action(ω); by (RS)(c) applied to R, E = ℝ^P and R′ := R (R.carrier = R.carrier ∩ ℝ^P), R.action(ω) = ∫_{ℝ^P} ⟨ω, ξ⟩ dμ. For x ∉ B_ρ we have x ∉ tsupport ω, so the integrand vanishes (F3), and ∫_{ℝ^P} ⟨ω, ξ⟩ dμ = ∫_{B_ρ} ⟨ω, ξ⟩ dμ (setIntegral_eq_integral_of_forall_compl_eq_zero). By (∗) this is Ŝ(ω).

5. (No boundary inside B_ρ.) Let β ∈ 𝒟^m(ℝ^P) with tsupport β ⊆ B_ρ. Then ∂Ŝ(β) = Ŝ(dβ) (GeometricCurrentOn.boundary_apply; dβ = exteriorDerivative β is a test form, exteriorDerivative_isTestForm), and tsupport dβ ⊆ tsupport β ⊆ B_ρ (tsupport_exteriorDerivative_subset). By step 4, Ŝ(dβ) = currentEval(S, dβ) = S(dβ), with dβ ∈ 𝒟ⁿ(U). Also β ∈ 𝒟^m(U) (tsupport β ⊆ B_ρ ⊆ U), and S(dβ) = ∂S(β) because the exterior derivative of β ∈ 𝒟^m(U) is the same form dβ (boundary_apply). Since tsupport β ⊆ B_ρ ⊆ B_s, hypothesis (i) gives ∂S(β) = 0. Hence ∂Ŝ(β) = 0.

6. (Cut-off.) Put s′ := (ρ + s)/2, so ρ < s′ < s, and let χ : ℝ^P → ℝ be the smooth bump function centred at 0 with inner radius ρ and outer radius s′ (Mathlib ContDiffBump): χ is C^∞, 0 ≤ χ ≤ 1, χ = 1 on closedBall(0, ρ), tsupport χ = closedBall(0, s′) ⊆ B_s, χ has compact support, and for every x ∈ B_ρ, χ = 1 on a neighbourhood of x (ContDiffBump.eventuallyEq_one_of_mem_ball). Let β ∈ 𝒟^m(ℝ^P) with |β(x)| ≤ 1 for all x, and γ(x) := χ(x)·β(x).
 (a) γ is smooth (product of smooth maps) with compact support (HasCompactSupport.smul_right), and tsupport γ ⊆ tsupport χ ⊆ B_s ⊆ U (tsupport_smul_subset_left). Thus γ ∈ 𝒟^m(U) and tsupport γ ⊆ B_s.
 (b) |γ(x)| = χ(x)·|β(x)| ≤ 1 for every x, by (F2) and 0 ≤ χ ≤ 1.
 (c) For x ∈ B_ρ, γ = β on a neighbourhood of x, so dγ(x) = dβ(x): the exterior derivative at x depends only on the germ at x (Filter.EventuallyEq.extDeriv_eq).

7. (Boundary mass.) With β, γ as in step 6:
 ∂Ŝ(β) = Ŝ(dβ) = ∫_{B_ρ} ⟨dβ, ξ⟩ dμ   by (∗)
  = ∫_{B_ρ} ⟨dγ, ξ⟩ dμ   (the integrands agree on B_ρ by 6(c); setIntegral_congr_fun)
  = A(dγ)   (hypothesis (ii) for the test form dγ ∈ 𝒟ⁿ(U))
  = ∂A(γ)   (boundary_apply).
 By (E1) applied in U to the current ∂A ∈ 𝒟_m(U), the set W := B_s, the form γ and r := 1 — legitimate by (iii), 6(a) and 6(b) — |∂A(γ)| ≤ (M_{B_s}(∂A)).toReal. Hence ofReal(∂Ŝ(β)) ≤ ofReal((M_{B_s}(∂A)).toReal) = M_{B_s}(∂A), the last equality by (iii). The forms admissible for M_{ℝ^P}(∂Ŝ) are exactly such β (the support condition tsupport β ⊆ ℝ^P is vacuous), so taking the supremum (sSup_le) gives M_{ℝ^P}(∂Ŝ) ≤ M_{B_s}(∂A).

8. (Conclusion.) Ŝ and R′ satisfy all five claims: representation and weight (step 3), agreement (step 4), vanishing boundary inside B_ρ (step 5) and the boundary mass bound (step 7). ∎

Appendix (verified Lean realization of the numbered proof above; not part of the proof). Compiled in this decomposition session with Lean v4.35.0-rc3, Mathlib 25730c7c and SimonGMT 2b366308 after `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the frozen contract's `open` commands (after its `noncomputable section ... end`). No extra import is needed. The sibling declarations are used through their accepted names `Submission.<lean_name>`; with them as hypotheses `#print axioms` reports only propext, Classical.choice and Quot.sound.

```lean
theorem Submission.dimred_mbl_tc_truncate_at_good_radius : ∀ (P m : ℕ) (U : Set (Euclid P)) (S A : GeometricCurrentOn U (m + 1)) (R : IMRep U (m + 1)) (ρ s : ℝ), IsOpen U → R.Represents S → (∀ β : TestFormOn U m, tsupport (β : DifferentialForm (Euclid P) m) ⊆ ball 0 s → S.boundary β = 0) → 0 < ρ → ρ < s → ball (0 : Euclid P) s ⊆ U → (∀ ω : TestFormOn U (m + 1), A ω = ∫ x in ball (0 : Euclid P) ρ, R.orient x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂R.measure) → A.boundary.massOn (ball 0 s) ≠ ∞ → ∃ (Ŝ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (R' : IMRep (univ : Set (Euclid P)) (m + 1)), R'.Represents Ŝ ∧ R'.measure = R.measure.restrict (ball 0 ρ) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), tsupport (ω : DifferentialForm (Euclid P) (m + 1)) ⊆ ball 0 ρ → Ŝ ω = currentEval S (ω : DifferentialForm (Euclid P) (m + 1))) ∧ (∀ β : TestFormOn (univ : Set (Euclid P)) m, tsupport (β : DifferentialForm (Euclid P) m) ⊆ ball 0 ρ → Ŝ.boundary β = 0) ∧ Ŝ.boundary.massOn univ ≤ A.boundary.massOn (ball 0 s) := by
  have hE1 := Submission.cmr_abs_apply_le_massOn
  have hIMC := Submission.cmc_imRep_locality_restrict_sub
  have hRS := Submission.lcmp_imRep_measure_restrict
  intro P m U S A R ρ s hU hSR hSb hρ hρs hsU hA hAfin
  have hcb : closedBall (0 : Euclid P) ρ ⊆ U := (closedBall_subset_ball hρs).trans hsU
  -- Step 1: restriction of R to ball 0 ρ, in U
  obtain ⟨-, R₁, -, hR₁c, hR₁m, hR₁o⟩ := hIMC.2.1 P (m + 1) U R (ball 0 ρ) hU measurableSet_ball
  -- Step 2: the same data as an IMRep in ℝ^P
  let R₂ : IMRep (univ : Set (Euclid P)) (m + 1) :=
    { carrier := R₁.carrier
      mult := R₁.mult
      orient := R₁.orient
      measurableSet_carrier := R₁.measurableSet_carrier
      carrier_subset := subset_univ _
      rectifiable := R₁.rectifiable
      measurable_mult := R₁.measurable_mult
      mult_pos := R₁.mult_pos
      locallyIntegrable_mult := fun K _ _ => by
        refine ne_top_of_le_ne_top
          (R.locallyIntegrable_mult _ (isCompact_closedBall 0 ρ) hcb) ?_
        rw [hR₁c, hR₁m]
        exact lintegral_mono_set (fun x hx => ⟨hx.1.1, ball_subset_closedBall hx.1.2⟩)
      aestronglyMeasurable_orient := R₁.aestronglyMeasurable_orient
      orients := R₁.orients }
  -- Step 3: the current represented in ℝ^P
  obtain ⟨Ŝ, R', hR'rep, hR'c, hR'm, hR'o⟩ :=
    hIMC.2.1 P (m + 1) univ R₂ univ isOpen_univ MeasurableSet.univ
  -- Step 4: weight and action
  obtain ⟨-, -, hrestr⟩ := hRS P (m + 1) U R
  obtain ⟨hmeas₁, hact₁⟩ := hrestr (ball 0 ρ) R₁ measurableSet_ball hR₁c hR₁m hR₁o
  have hR'meas : R'.measure = R.measure.restrict (ball 0 ρ) := by
    rw [← hmeas₁]
    unfold IMRep.measure
    rw [hR'c, hR'm, inter_univ]
  have hact : ∀ ω : DifferentialForm (Euclid P) (m + 1),
      R'.action ω = ∫ x in ball (0 : Euclid P) ρ, R.orient x (ω x) ∂R.measure := by
    intro ω
    rw [← hact₁ ω]
    unfold IMRep.action
    rw [hR'c, hR'm, hR'o, inter_univ]
  have hŜ : ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1),
      Ŝ ω = ∫ x in ball (0 : Euclid P) ρ,
        R.orient x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂R.measure := fun ω => by
    rw [hR'rep ω, hact]
  -- Step 5: agreement
  have hagree : ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1),
      tsupport (ω : DifferentialForm (Euclid P) (m + 1)) ⊆ ball 0 ρ →
        Ŝ ω = currentEval S (ω : DifferentialForm (Euclid P) (m + 1)) := by
    intro ω hω
    have hωU : IsTestForm (ω : DifferentialForm (Euclid P) (m + 1)) ∧
        tsupport (ω : DifferentialForm (Euclid P) (m + 1)) ⊆ U :=
      ⟨ω.property.1, hω.trans (ball_subset_closedBall.trans hcb)⟩
    rw [currentEval, dif_pos hωU, hSR, hŜ,
      (hrestr univ R MeasurableSet.univ (by simp) rfl rfl).2, Measure.restrict_univ]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)
    show R.orient x ((ω : DifferentialForm (Euclid P) (m + 1)) x) = 0
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hω h)), map_zero]
  -- Step 6: vanishing boundary inside
  have hbdry : ∀ β : TestFormOn (univ : Set (Euclid P)) m,
      tsupport (β : DifferentialForm (Euclid P) m) ⊆ ball 0 ρ → Ŝ.boundary β = 0 := by
    intro β hβ
    have hdβ : tsupport (exteriorDerivative (β : DifferentialForm (Euclid P) m)) ⊆ ball 0 ρ :=
      (tsupport_exteriorDerivative_subset _).trans hβ
    have hβU : (β : DifferentialForm (Euclid P) m) ∈ TestFormOn U m :=
      ⟨β.property.1, hβ.trans (ball_subset_closedBall.trans hcb)⟩
    rw [GeometricCurrentOn.boundary_apply, hagree _ hdβ]
    have hdU : IsTestForm (exteriorDerivative (β : DifferentialForm (Euclid P) m)) ∧
        tsupport (exteriorDerivative (β : DifferentialForm (Euclid P) m)) ⊆ U :=
      ⟨exteriorDerivative_isTestForm β.property.1,
        hdβ.trans (ball_subset_closedBall.trans hcb)⟩
    have := hSb ⟨_, hβU⟩ (hβ.trans (ball_subset_ball hρs.le))
    rw [GeometricCurrentOn.boundary_apply] at this
    show currentEval S (exteriorDerivative (β : DifferentialForm (Euclid P) m)) = 0
    rw [currentEval, dif_pos hdU]
    exact this
  -- Step 7: cutoff
  have hmid : ρ < (ρ + s) / 2 := by linarith
  let χ : ContDiffBump (0 : Euclid P) := ⟨ρ, (ρ + s) / 2, hρ, hmid⟩
  have hχsupp : tsupport (χ : Euclid P → ℝ) ⊆ ball 0 s := by
    rw [χ.tsupport_eq]
    exact closedBall_subset_ball (by show (ρ + s) / 2 < s; linarith)
  have hsmul : ∀ (c : ℝ) (α : Covector (Euclid P) m),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro c α
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg c), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun I _ => ?_)
    split_ifs <;> simp [ContinuousAlternatingMap.smul_apply, mul_pow]
  -- Step 8: boundary mass
  have hmass : Ŝ.boundary.massOn univ ≤ A.boundary.massOn (ball 0 s) := by
    unfold GeometricCurrentOn.massOn
    apply sSup_le
    rintro _ ⟨β, hβ, rfl⟩
    show ENNReal.ofReal (Ŝ.boundary β) ≤ _
    set b : DifferentialForm (Euclid P) m := (β : DifferentialForm (Euclid P) m) with hb
    let γ : DifferentialForm (Euclid P) m := fun x => (χ x) • b x
    have hγtest : IsTestForm γ := by
      refine ⟨?_, ?_⟩
      · exact (χ.contDiff).smul β.property.1.1
      · exact χ.hasCompactSupport.smul_right
    have hγsupp : tsupport γ ⊆ ball 0 s :=
      (tsupport_smul_subset_left (fun x => χ x) b).trans hχsupp
    have hγU : γ ∈ TestFormOn U m := ⟨hγtest, hγsupp.trans hsU⟩
    have hγnorm : ∀ x, covectorEuclideanNorm (γ x) ≤ 1 := by
      intro x
      show covectorEuclideanNorm (χ x • b x) ≤ 1
      rw [hsmul, abs_of_nonneg (χ.nonneg)]
      calc χ x * covectorEuclideanNorm (b x) ≤ 1 * 1 :=
            mul_le_mul χ.le_one (hβ.2 x) (covectorEuclideanNorm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    have hloc : ∀ x ∈ ball (0 : Euclid P) ρ, exteriorDerivative b x = exteriorDerivative γ x := by
      intro x hx
      have h1 : (χ : Euclid P → ℝ) =ᶠ[𝓝 x] 1 := χ.eventuallyEq_one_of_mem_ball hx
      have h2 : b =ᶠ[𝓝 x] γ := by
        filter_upwards [h1] with y hy
        show b y = χ y • b y
        rw [hy]; simp
      exact h2.extDeriv_eq
    have hkey : Ŝ.boundary β = A.boundary ⟨γ, hγU⟩ := by
      rw [GeometricCurrentOn.boundary_apply, GeometricCurrentOn.boundary_apply, hŜ, hA]
      refine setIntegral_congr_fun measurableSet_ball (fun x hx => ?_)
      show R.orient x (exteriorDerivative b x) = R.orient x (exteriorDerivative γ x)
      rw [hloc x hx]
    have hle := hE1 P m U (ball 0 s) A.boundary ⟨γ, hγU⟩ 1 hAfin hγsupp hγnorm
    rw [hkey, one_mul] at *
    calc ENNReal.ofReal (A.boundary ⟨γ, hγU⟩)
        ≤ ENNReal.ofReal (A.boundary.massOn (ball 0 s)).toReal :=
          ENNReal.ofReal_le_ofReal ((le_abs_self _).trans hle)
      _ = A.boundary.massOn (ball 0 s) := ENNReal.ofReal_toReal hAfin
  exact ⟨Ŝ, R', hR'rep, hR'meas, hagree, hbdry, hmass⟩
```

## Key steps

1. (IMC)(b) restricts R to M ∩ B_ρ in U; the same data form an IMRep in ℝ^P (local integrability from the compact closedBall(0, ρ) ⊆ U), and (IMC)(b) in ℝ^P gives the represented current Ŝ.
2. (RS)(c): R′.measure = μ⌞B_ρ and Ŝ(ω) = ∫_{B_ρ} ⟨ω, ξ⟩ dμ for every test form ω.
3. Forms supported in B_ρ vanish off B_ρ, so Ŝ(ω) = ∫ ⟨ω, ξ⟩ dμ = S(ω) = currentEval(S, ω); with tsupport dβ ⊆ tsupport β this gives ∂Ŝ(β) = ∂S(β) = 0 inside B_ρ.
4. For |β| ≤ 1 and a smooth bump χ (χ = 1 near closedBall(0, ρ), tsupport χ ⊆ B_s): ∂Ŝ(β) = ∫_{B_ρ} ⟨d(χβ), ξ⟩ dμ = ∂A(χβ), and (E1) bounds it by M_{B_s}(∂A); take the supremum.

## Reference use

### local-project

Queries:
- `cat RUN/local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `python3 scans of RUN/dag.json: selected node, parent root.dimension_reduction_results-a1.moving_blowups-a1 and its children, dependency types (dor_imrep_massOn_eq_measure_and_support, dimred_mbl_current_foundations, dimred_mbl_slice_mass_bounds, dimred_mbl_closure_and_boundary_rectifiability), accepted declarations mentioning massOn/IMRep/compact/diagonal/separab, collisions for dimred_mbl_tc_*`
- `rg -n 'Banach|Alaoglu|SecondCountableTopology|IsSeparable|diagonal|extraction' lake-packages/simongmt/Poincare/SimonGMT/Chapter06 (no match); rg -n 'WeaklyConvergesOn|Banach' SNAPSHOT/project --glob '*.lean'`
- `rg -n 'instSecondCountableTopology|theorem extraction_forall_of_eventually|IsSeparable.exists_countable_dense_subset|Filter.EventuallyEq.extDeriv_eq' SNAPSHOT/mathlib/Mathlib; grep of setLIntegral_congr_fun, lipschitzWith_one_norm, ContDiffBump API, tsupport_sub, norm_iteratedFDeriv_zero`
- `sed -n on book/chapter-06.txt lines 284–333 (2.9, 2.13–2.15), 755–767 (3.2), 875–895 (3.11), 1330–1380 (4.6–4.10)`
- `grep -n _existing_lean_name_problem _overlay_accepted_children _accepted_checkpoint ensure in /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py and store.py; contract_scope in verifier/gmt-compare.py`
- `lake env lean on Types/Final.lean (7 child types), Assembly.lean (conditional parent), LT.lean, TR.lean, WC.lean (child proofs from sibling types), SubForm.lean and SubParent.lean (Submission-form compile), all with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-truncated-compactness-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-eva-463e096c91/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-cov-64249b6f60/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-im-calculus-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-local-comparison-a1-imrep-1bd5f15878/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/ContinuousMap/SecondCountableSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Metrizable/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/tmp/tc-decomp-x7k2/lean/Assembly.lean`
- `/tmp/tc-decomp-x7k2/lean/TR.lean`
- `/tmp/tc-decomp-x7k2/lean/WC.lean`
- `/tmp/tc-decomp-x7k2/lean/LT.lean`

Pins match: HEAD b4d606d, Mathlib 25730c7c, SimonGMT 2b366308, and Submission.lean is byte-identical to Contract.lean. Neither the pinned libraries nor any accepted DAG node proves weak compactness of currents. SimonGMT Chapter06 has no match. The project snapshot states Simon 2.15 only as the unproved Ch06 contract conjunct CompactnessUnderMassBounds (GMT/Ch06/Contract.lean:194–205), a different problem. So weak_compactness is a new child. Its Lean route exists in Mathlib: ContinuousMap.instSecondCountableTopology (separate import), IsSeparable.exists_countable_dense_subset, IsCompact.tendsto_subseq on a countable product, and norm_iteratedFDeriv_zero. The cut-off uses ContDiffBump and Filter.EventuallyEq.extDeriv_eq. Step 1 uses Filter.extraction_forall_of_eventually. Four accepted declarations are reused with identical frozen types: cmr_abs_apply_le_massOn, cmr_covector_euclidean_equiv, cmc_imRep_locality_restrict_sub and lcmp_imRep_measure_restrict. The new names dimred_mbl_tc_* collide with nothing. All child types elaborate. The conditional assembly proves the exact parent type, and each new child is proved in Lean from its sibling types. All of these depend only on propext, Classical.choice and Quot.sound.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
