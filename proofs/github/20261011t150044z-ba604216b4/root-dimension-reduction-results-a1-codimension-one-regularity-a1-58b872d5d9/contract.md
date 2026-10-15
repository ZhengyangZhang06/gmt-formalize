<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.codimension_one_regularity-a1 -->

## Theorem `Submission.dimred_codimension_one_regularity`

CodimensionOneRegularity of the frozen contract (Simon 7.5.8, with README erratum 7). For all n, k ∈ ℕ, all sets U, N, E ⊆ ℝ^{n+k}, every map ξ_N : ℝ^{n+k} → Λ_{n+1}(ℝ^{n+k}) (MultiVector (n+k) (n+1)) and every T ∈ 𝒟_n(U): if U is open, InClassO n U N ξ_N (N an embedded C² (n+1)-dimensional submanifold, ξ_N a continuous orientation of N, (closure N ∖ N) ∩ U = ∅, N ∩ U ≠ ∅), E is a measurable set with E ⊆ N ∩ U, T(ω) = ∫_E ξ_N(x)(dω(x)) dH^{n+1}(x) for every ω ∈ 𝒟^n(U) (IsBoundaryOfRegion T E ξ_N), and T is minimizing in N ∩ U, then: (a) singularSet T = ∅ if n ≤ 6; (b) singularSet T ∩ K is finite for every compact K ⊆ U if n = 7; (c) μH[n − 7 + α](singularSet T) = 0 for every real α > 0 if n > 7.

Node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/374

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1016, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1017, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1018, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1020, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1024, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1026, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1028, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1030

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/810, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1211, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1238, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1285, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1081, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4336, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4339, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4345, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4348, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4352, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4368

## Lean problem

Declaration: `Submission.dimred_codimension_one_regularity`

```lean
CodimensionOneRegularity
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

- Parent DAG node: `root.dimension_reduction_results-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent steps 0 and C0–C6 (Simon 7.5.8 and its proof, chapter-07.txt lines 919–974 with footnote 5; 5.2(‡) and 5.3–5.4(3), lines 757–860; Appendix B, B.1, B.2 and its printed proof, chapter-07-source.txt lines 1256–1539), with departures [D3] (gap lemma and density_one_implies_regular instead of Allard along sequences), [D4] (zero-scale limits with moving centres lie in affine planes T_xN − a; the offset plane is treated with the cutoff radius R + |a| + 2, and the projected-current identity and the uniform perimeter bound are proved before BV compactness), [D5] (δ below every gap constant used; the factor S₀ is handled through densities; the hypotheses of B.2 are verified). P := n + k; μ_A is the measure of any representation of an integer multiplicity A (sibling child im_mass_measure: all representations have the same measure (c), M_W(A) = μ_A(W) for open W (a), spt A = spt μ_A (b)); Θ_A := Θ^n(μ_A, ·); H^m := μHE[m]; ω_n := unitBallVolume n; η_{y,λ}(w) := λ^{−1}(w − y).
0. (C0: setting; n = 0.) T is integer multiplicity (first conjunct of IsMinimizingIn). If ω ∈ 𝒟^n(U) vanishes near closure(E), then dω = 0 on E and T(ω) = 0; hence spt T ⊆ closure(E) ∩ U ⊆ closure(N) ∩ U ⊆ N (as (closure N ∖ N) ∩ U = ∅). If n = 0, the sibling child zero_dim_vanishing (A := N ∩ U, spt T ⊆ N ∩ U) gives T = 0, so singularSet T = ∅ ⊆ spt T = ∅; (a) holds and (b), (c) are vacuous. Assume n ≥ 1. Then k ≥ 1 (N ∩ U ≠ ∅ and an embedded (n+1)-dimensional submanifold of ℝ^{n+k} requires n + 1 ≤ n + k); N is an embedded C² (n + ℓ)-submanifold with ℓ := 1 ≤ k; spt T ⊆ U ∩ N; T is minimizing in U ∩ N = N ∩ U; ∂T = 0 since T(dω) = ∫_E ξ_N(d(dω)) dH^{n+1} = 0. So T satisfies the hypotheses of the sibling children monotonicity (d := n + 1) and threshold_reduction (ℓ := 1), and of the siblings density_and_tangent_cones and density_one_implies_regular. Let Θ be the upper semicontinuous density of T on U given by monotonicity (iii); Θ ≥ 1 on spt T.
1. (C1: multiplicity one; Simon 5.2(‡).) Θ = 1 μ_T-a.e. Proof: let y ∈ N ∩ U and Φ a C² diffeomorphism from an open W ∋ y (W ⊆ U) onto an open subset of ℝ^P with Φ(W ∩ N) = G × {0}, G ⊆ ℝ^{n+1} open, orientation preserving from ξ_N to the standard orientation. Then Φ_#(T⌞W) = ∂[[Φ(E ∩ W)]] in Φ(W) (change of variables in the defining integral), and since T has locally finite mass, Φ(E ∩ W) has locally finite perimeter in G (Simon Ch. 6, 2.35). By De Giorgi's structure theorem (Ch. 3, 4.3), ∂[[Φ(E ∩ W)]] is the integer multiplicity current carried by the reduced boundary with multiplicity 1; pushing back by Φ^{−1} (multiplicity is preserved by C¹ diffeomorphisms, Ch. 6, 3.3–3.9), T has multiplicity 1 H^n-a.e. on its carrier in W, and Θ = multiplicity = 1 μ_T-a.e. (Ch. 3, Theorem 1.9; Ch. 4, Remark 1.8(2)). Cover N ∩ U by countably many such W.
2. (C4: sing T is the superlevel set {Θ ≥ 1 + δ}.) For 1 ≤ j ≤ n let δ_j > 0 be given by the sibling child density_gap for (P, j), and put δ := min_{1≤j≤n} δ_j > 0. For x ∈ spt T: x ∈ reg T ⟺ Θ(x) < 1 + δ. (⇐) If Θ(x) < 1 + δ, a tangent cone C of T at x (sibling density_and_tangent_cones (2); C minimizing in ℝ^P, a cone, ∂C = 0 as a weak limit of cycles, HasMassDensity C 0 Θ(x)) has vertex density < 1 + δ_n, so density_gap gives Θ(x) ≤ 1, hence Θ(x) = 1, and the sibling density_one_implies_regular with constant sequences (Ts :≡ T, ys :≡ x, y := x) gives x ∈ reg T. (⇒) If x ∈ reg T, the sibling child regular_point_density gives m ≥ 1 and ρ > 0 with Θ = m on spt T ∩ B_ρ(x); since μ_T(B_ρ(x)) > 0 (x ∈ spt T), μ_T(B_ρ(x) ∖ spt T) = 0 and Θ = 1 μ_T-a.e. (step 1), m = 1, so Θ(x) = 1 < 1 + δ. As points with Θ ≥ 1 + δ > 0 lie in spt T, sing T = {x ∈ U : Θ(x) ≥ 1 + δ}.
3. (C2(ii): zero-scale limits lie in offset planes and have multiplicity one; [D4].) Claim: let x_i ∈ U converge to x ∈ U, λ_i > 0, λ_i → 0, S_i := blowUp T x_i λ_i, and S ∈ 𝒟_n(ℝ^P) with S_i ⇀ S (ConvergesWeakly), S ≠ 0. Then x ∈ N, and there are a ∈ (T_xN)^⊥ and an H^{n+1}-measurable F ⊆ A := T_xN − a of locally finite perimeter in A with S = ∂[[F]] in ℝ^P, where [[F]](β) := ∫_F ξ_A(β) dH^{n+1} and ξ_A := ξ_N(x) orients A; in particular spt S ⊆ A and Θ_S = 1 μ_S-a.e. Proof. (α) Put N_i := η_{x_i,λ_i}(N), E_i := η_{x_i,λ_i}(E), ξ_i(w) := ξ_N(x_i + λ_iw). By the change of variables w = x_i + λ_iv in the defining integral (η_{x_i,λ_i}^#(dω) = λ_i^{−(n+1)}dω∘η_{x_i,λ_i}, dH^{n+1}(w) = λ_i^{n+1}dH^{n+1}(v)), S_i(ω) = ∫_{E_i} ξ_i(dω) dH^{n+1} for ω ∈ 𝒟^n(η_{x_i,λ_i}(U)), and spt S_i ⊆ N_i. Choose δ₀ > 0 with closedBall x (2δ₀) ⊆ U and Λ for K := closedBall x (2δ₀) (monotonicity (i)); for |x_i − x| < δ₀ and λ_iρ ≤ δ₀/2, μ_{S_i}(B_ρ(0)) = λ_i^{−n}μ_T(B_{λ_iρ}(x_i)) ≤ c_*ρ^n with c_* := e^{Λδ₀}(2/δ₀)^nμ_T(K). If dist(x_i, N)/λ_i were unbounded, then along a subsequence every ball B_R(0) would eventually miss N_i ⊇ spt S_i and S = 0. Hence dist(x_i, N) ≤ C₀λ_i for some C₀ ≥ 1 and all i, and x ∈ closure(N) ∩ U ⊆ N. (β) Let Π₀ := T_xN, p the orthogonal projection onto Π₀ and p^⊥ := I − p. As N is an embedded C² submanifold, relatively closed in U, there are δ₁, δ₂ > 0 and u ∈ C²(Π₀ ∩ B_{δ₁}(0); Π₀^⊥) with u(0) = 0, Du(0) = 0, |Du| ≤ 1, |u| < δ₂, such that the open cylinder Z := {x + v + h : v ∈ Π₀, |v| < δ₁, h ∈ Π₀^⊥, |h| < δ₂} lies in U and N ∩ Z = {x + v + u(v) : v ∈ Π₀, |v| < δ₁}; moreover ξ_N(x + v + u(v)) = Λ_{n+1}(I + Du(v))ξ_A/|Λ_{n+1}(I + Du(v))ξ_A| (two continuous unit orientations of the tangent planes of a connected graph that agree at v = 0). Write x_i − x = s_i + t_i (s_i ∈ Π₀, t_i ∈ Π₀^⊥) and, for w ∈ Π₀ with |s_i + λ_iw| < δ₁, G_i(w) := w + g_i(w), g_i(w) := λ_i^{−1}(u(s_i + λ_iw) − t_i). Then η_{x_i,λ_i}(x + v + u(v)) = G_i(λ_i^{−1}(v − s_i)), so η_{x_i,λ_i}(N ∩ Z) = G_i(dom G_i); p∘G_i = id, p^⊥∘G_i = g_i, DG_i(w) = I + Du(s_i + λ_iw) on Π₀, and ξ_i(G_i(w)) = Λ_{n+1}DG_i(w)ξ_A/J_i(w) with J_i(w) := |Λ_{n+1}DG_i(w)ξ_A| the Jacobian of G_i. (γ) Choose p_i ∈ N with |p_i − x_i| ≤ 2C₀λ_i; for large i, p_i = x + v_i + u(v_i) ∈ Z and w_i := λ_i^{−1}(v_i − s_i) satisfies G_i(w_i) = η_{x_i,λ_i}(p_i), so |w_i| ≤ 2C₀ and |g_i(w_i)| ≤ 2C₀; since |Dg_i| ≤ 1, |g_i(0)| ≤ 4C₀. Pass to a subsequence with g_i(0) → −a; then a ∈ Π₀^⊥, and because Dg_i(w) = Du(s_i + λ_iw) → 0 uniformly on bounded sets, G_i → G, G(w) := w − a, in C¹ on Π₀ ∩ closedBall 0 R' for every R'. Put A := G(Π₀) = Π₀ − a, oriented by ξ_A. (δ) Fix R ≥ 1, R₁ := R + |a| + 2 and C_R := {y : |p(y)| < R, |p^⊥(y)| < |a| + 1} ⊆ B_{R₁}(0). For all large i: B_{λ_iR₁}(x_i) ⊆ Z, B_{R₁}(0) ⊆ η_{x_i,λ_i}(U), λ_iR₁ ≤ δ₀/2, Π₀ ∩ closedBall 0 R₁ ⊆ dom G_i, and |g_i(w) + a| < 1/4 for |w| ≤ R₁. For these i: (δ1) N_i ∩ B_{R₁}(0) = η_{x_i,λ_i}(N ∩ B_{λ_iR₁}(x_i)) ⊆ G_i(dom G_i); (δ2) N_i ∩ C_R = G_i(Π₀ ∩ B_R(0)) (a point y of the left side lies in B_{R₁}(0), so y = G_i(w) with |w| = |p(y)| < R; conversely, for |w| < R, |p^⊥(G_i(w))| = |g_i(w)| < |a| + 1/4); (δ3) N_i ∩ B_R(0) ⊆ G_i(Π₀ ∩ B_R(0)) ⊆ {y : |p^⊥(y)| < |a| + 1/4}. (ε) Let F_i' := {w ∈ dom G_i : G_i(w) ∈ E_i} and F_i := G(F_i') ⊆ A. For ω ∈ 𝒟^n(ℝ^P) with tsupport ω ⊆ C_R and large i, (α), (δ2), the area formula for the injective C¹ map G_i on Π₀ ∩ B_R(0) and (β) give S_i(ω) = ∫_{E_i∩C_R} ξ_i(dω) dH^{n+1} = ∫_{F_i'∩B_R(0)} ξ_i(G_i(w))(dω(G_i(w)))J_i(w) dH^{n+1}(w) = ∫_{F_i'∩B_R(0)} ξ_A((G_i^#dω)(w)) dH^{n+1}(w). Let π_A := G∘p = p − a and ζ(y) := χ(|p^⊥(y)|) with χ ∈ C^∞(ℝ; [0, 1]), χ = 1 on (−∞, |a| + 3/4], χ = 0 on [|a| + 7/8, ∞) (ζ is smooth because χ is constant near 0). For every n-form α̃ ∈ 𝒟^n(A ∩ B_R(−a)) (A ∩ B_R(−a) = G(Π₀ ∩ B_R(0)) = A ∩ C_R), ω := ζ·π_A^#α̃ belongs to 𝒟^n(ℝ^P) with tsupport ω ⊆ C_R, and G_i^#ω = χ(|g_i|)(π_A∘G_i)^#α̃ = G^#α̃ on Π₀ ∩ B_R(0) (π_A∘G_i = G and |g_i| < |a| + 1/4 there); hence S_i(ζ·π_A^#α̃) = ∫_{F_i'∩B_R(0)} ξ_A(G^#dα̃) dH^{n+1} = ∫_{F_i} ξ_A(dα̃) dH^{n+1} = ∂[[F_i]](α̃) (G is a translation): ∂[[F_i]] = π_{A#}(ζS_i) on A ∩ B_R(−a). (ζ) If moreover |α̃| ≤ 1 pointwise, then |ζπ_A^#α̃| ≤ 1 (π_A is an orthogonal projection followed by a translation, 0 ≤ ζ ≤ 1), so |∂[[F_i]](α̃)| ≤ M_{C_R}(S_i) ≤ μ_{S_i}(B_{R₁}(0)) ≤ c_*R₁^n. Identifying A with ℝ^{n+1} (oriented by ξ_A), n-forms α̃ with |α̃| ≤ 1 correspond to vector fields φ with |φ| ≤ 1 and ξ_A(dα̃) = div φ, so the perimeter of F_i in A ∩ B_R(−a) (Ch. 2, 2.1; smooth fields suffice by mollification) is at most c_*(R + |a| + 2)^n for all large i ≥ i_R, and H^{n+1}(F_i ∩ B_R(−a)) ≤ ω_{n+1}R^{n+1}. (η) For R = 1, 2, … apply the BV compactness theorem (Ch. 2, 2.6) on A ∩ B_{R+1}(−a) to the tail i ≥ i_{R+1} of the current subsequence; a diagonal subsequence gives an H^{n+1}-measurable F ⊆ A with 1_{F_i} → 1_F in L¹(A ∩ B_R(−a)) for every R, and F has locally finite perimeter in A by lower semicontinuity of the variation (Ch. 2, §2; SimonGMT Chapter02.bvVariationOn_le_liminf_of_locallyL1). (θ) Let ω ∈ 𝒟^n(ℝ^P) with tsupport ω ⊆ B_R(0) (R ∈ ℕ) and write ω = ζω + (1 − ζ)ω. (1 − ζ)ω vanishes on the open set {|p^⊥| < |a| + 3/4}, which contains N_i ∩ B_R(0) for large i (δ3) and contains A (|p^⊥| = |a| on A); hence S_i((1 − ζ)ω) = 0 and ∂[[F]]((1 − ζ)ω) = [[F]](d((1 − ζ)ω)) = 0. Since tsupport(ζω) ⊆ C_R, (ε) gives S_i(ζω) = ∫_{F_i'∩B_R(0)} ξ_A(G_i^#d(ζω)) dH^{n+1}; as 1_{F_i'} = 1_{F_i}∘G → 1_F∘G in L¹(Π₀ ∩ B_R(0)) and G_i^#d(ζω) → G^#d(ζω) uniformly on Π₀ ∩ closedBall 0 R, S_i(ζω) → ∫_{G^{−1}(F)∩B_R(0)} ξ_A(G^#d(ζω)) dH^{n+1} = [[F]](d(ζω)) = ∂[[F]](ζω). As S_i ⇀ S, S(ω) = ∂[[F]](ω). Thus S = ∂[[F]], spt S ⊆ closure(F) ⊆ A, and De Giorgi's structure theorem in the plane A (Ch. 3, 4.3; as in step 1 with N replaced by A) gives μ_S = H^n⌞∂*F, so Θ_S = 1 μ_S-a.e.
4. (C2(iii): cones lie in linear planes.) If in step 3 S is moreover a cone, then spt S is a nonempty closed cone, so 0 ∈ spt S ⊆ A = Π₀ − a, i.e. a ∈ Π₀ ∩ Π₀^⊥ = {0}: spt S ⊆ T_xN, a linear (n+1)-dimensional subspace.
5. (C5: hypotheses of threshold_reduction.) Fix z, r with closedBall z (2r) ⊆ U and apply the sibling child threshold_reduction (ℓ := 1) with c := 1 + δ and d₀ := n − 6 (natural subtraction). Let S be an admissible zero-scale limit: S = lim blowUp T x_i λ_i (ConvergesWeakly) with x_i ∈ B_r(z), λ_i → 0⁺, S minimizing in ℝ^P with ∂S = 0. Passing to a subsequence, x_i → x ∈ closedBall z r ⊆ U, so steps 3 and 4 apply to S whenever S ≠ 0. Hypothesis (H1): if Θ_S = c'·1_Q with Q an n-dimensional subspace and c' ≥ 1 + δ, then Q ⊆ spt S (c' > 0), so S ≠ 0, and by step 3 Θ_S = 1 μ_S-a.e.; since μ_S ≠ 0 there is y with Θ_S(y) = 1 ∈ {0, c'}, so c' = 1 < 1 + δ: impossible. Hypothesis (H2): suppose L is a subspace with d₀ ≤ d := dim L < n, Θ_S invariant under w ↦ y + λw (y ∈ L, λ > 0), and {Θ_S ≥ 1 + δ} = L. As 0 ∈ L, Θ_S(0) ≥ 1 + δ > 0, so S ≠ 0. By the sibling child cone_splitting, S is a cone and there is S₀ ∈ 𝒟_{n'}(ℝ^P), n' := n − d, minimizing in ℝ^P, ∂S₀ = 0, a cone, spt S₀ ⊆ L^⊥, with t + y ∈ spt S ⟺ y ∈ spt S₀ and Θ_S(t + y) = Θ_{S₀}(y) for t ∈ L, y ∈ L^⊥. By step 4, spt S ⊆ A₀' := T_xN, a linear (n+1)-dimensional subspace; L ⊆ spt S (Θ_S ≥ 1 + δ > 0 on L), so L ⊆ A₀', and spt S₀ ⊆ A₀ := A₀' ∩ L^⊥ (y ∈ spt S₀ ⟹ y = 0 + y ∈ spt S), a linear subspace of dimension n' + 1. Moreover Θ_{S₀}(0) = Θ_S(0) ≥ 1 + δ, and for y ∈ L^⊥ ∖ {0} we have y ∉ L, so Θ_{S₀}(y) = Θ_S(y) < 1 + δ. Since d₀ ≤ d ≤ n − 1, 1 ≤ n' ≤ 6. Case n' = 1: the sibling child one_dim_cones (S₀ transported to degree 1) gives e, m' with spt S₀ ⊆ span{e} and HasMassDensity S₀ y m' for y ∈ span{e}; then m' = Θ_{S₀}(0) ≥ 1 + δ > 0, so |e| = 1, e ∈ spt S₀ ⊆ L^⊥ (positive density), e ≠ 0, and m' = Θ_{S₀}(e) < 1 + δ: impossible. Case 2 ≤ n' ≤ 6: (α) every y ∈ spt S₀ ∖ {0} is a regular point: by the sibling density_and_tangent_cones (2) applied to S₀ (dimension n', U = N = ℝ^P, after transporting along Euclid P = Euclid (n' + (P − n'))), S₀ has at y a minimizing tangent cone C_y with ∂C_y = 0 and HasMassDensity C_y 0 Θ_{S₀}(y); as Θ_{S₀}(y) < 1 + δ ≤ 1 + δ_{n'}, density_gap gives Θ_{S₀}(y) ≤ 1, so Θ_{S₀}(y) = 1 (monotonicity (iv)), and the sibling density_one_implies_regular with constant sequences (dimension n', U = N = ℝ^P) gives y ∈ reg S₀ (and the sibling child regular_point_density then gives Θ_{S₀} ≡ 1 on spt S₀ near y). (β) Let M := spt S₀ ∖ {0} ⊆ A₀, and identify A₀ with ℝ^{n'+1} by a linear isometry. M ≠ ∅ (otherwise μ_{S₀} would be carried by {0}, so S₀ = 0 as n' ≥ 1, contradicting Θ_{S₀}(0) > 0), M is a cone, and closure(M) ∖ M = {0}. The hypotheses of Simon's Theorem B.2 hold for M in A₀ ≅ ℝ^{n'+1}: (i) M is an embedded C¹ hypersurface of A₀: by (α), for each y ∈ M there are ρ_y > 0, m_y ∈ ℤ ∖ {0} and an embedded C¹ n'-submanifold M_y ∋ y with S₀ = m_y[[M_y]] in B_{ρ_y}(y); by properness and injectivity of the chart of M_y at y (as in step 2 of the proof of regular_point_density), M_y is relatively closed in a small ball B_{ρ'}(y), 0 < ρ' ≤ min(ρ_y, |y|)/2 (so 0 ∉ B_{ρ'}(y)); re-proved here exactly as in steps 3–4 of that proof (the mass identity M_{B_s(w)}(S₀) = |m_y|·H^{n'}(M_y ∩ B_s(w)) for balls B_s(w) ⊆ B_{ρ_y}(y), and the H^{n'}-density 1 of a C¹ submanifold at each of its points), Θ_{S₀}(w) = |m_y| for every w ∈ M_y ∩ B_{ρ'}(y), so |m_y| = Θ_{S₀}(y) = 1 by (α); S₀ vanishes on the open set B_{ρ'}(y) ∖ M_y, so spt S₀ ∩ B_{ρ'}(y) ⊆ M_y ∩ B_{ρ'}(y), and conversely every point of M_y ∩ B_{ρ'}(y) has density 1 > 0 and lies in spt S₀; hence M ∩ B_{ρ'}(y) = M_y ∩ B_{ρ'}(y) ⊆ A₀ (spt S₀ ⊆ A₀), so M is an embedded C¹ hypersurface of A₀ ∖ {0}; (ii) M is smooth with zero mean curvature (Simon Ch. 5, 7.1, last part, with N = ℝ^P: the varifold of S₀ is stationary in ℝ^P by the sibling minimizing_implies_stationary, integer multiplicity, with density 1 at each y ∈ M, so near each y ∈ M the set M is a C^{q+2,α} graph for every q, and the first variation formula then gives mean curvature 0); (iii) M is a cone; (iv) closure(M) ∖ M = {0}; (v) M is stable in the sense of B.1: M is oriented by the orientation of S₀ (the local orientations m_yξ_{M_y} agree a.e., hence everywhere by continuity); for ζ ∈ C^∞_c(M) let Z be a compactly supported smooth extension of ζν (ν the unit normal of M in A₀) to A₀ ∖ {0}, tangent to A₀, and Φ_t := id + tZ; for small |t|, Φ_{t#}S₀ is an integer multiplicity competitor for S₀ (same boundary, spt(Φ_{t#}S₀ − S₀) ⊆ spt Z compact), so H^{n'}(M ∩ W) ≤ H^{n'}(Φ_t(M ∩ W)) for an open W ⊂⊂ ℝ^P ∖ {0} containing spt Z, and the second variation formula (Simon Ch. 2, 5.12, with H = 0) gives ∫_M(|∇^Mζ|² − |A|²ζ²) dH^{n'} ≥ 0, extended by mollification in charts to compactly supported locally Lipschitz ζ (|A| is continuous on M and supports stay in a fixed compact subset of M), the form used in the printed proof of B.2. (γ) By Simon's Theorem B.2 (Simons [Sim68]) closure(M) is a hyperplane H₀ of A₀. Its printed proof: Simons' identity B.8 and Lemma B.11 (cf. SimonGMT AppendixB/ConeDefect.lean cone_simonsDefect_lower_bound) give, for the minimal cone M, (1/2)Δ_M|A|² + |A|⁴ ≥ 2r^{−2}|A|² + |∇_M|A||²; inserting ζ := |A|ψ into the stability inequality B.1 and integrating by parts yields 2∫_M r^{−2}ψ²|A|² ≤ ∫_M |A|²|∇_Mψ|² for every locally Lipschitz ψ with ∫_M r^{−2}ψ²|A|² < ∞ (first for compactly supported ψ, then by the cut-off functions γ_ε of the printed proof); the choice ψ := r^{1+ε}r₁^{1−n'/2−2ε}, r₁ := max{1, r}, with ε > 0 such that (n'/2 − 2 + ε)² < 2 and (1 + ε)² < 2 (possible exactly because 2 ≤ n' ≤ 6), together with the homogeneity |A(x)|² = r^{−2}|A(x/|x|)|² and the cone formula ∫_M f dH^{n'} = ∫_0^∞ r^{n'−1}∫_{M∩S^{n'}} f(rω) dH^{n'−1}(ω) dr, forces |A| ≡ 0 on M. Then every component of M is an open subset of a hyperplane through 0; since M is relatively closed in A₀ ∖ {0}, embedded, and H ∖ {0} is connected for every hyperplane H of A₀ (n' ≥ 2), M = H₀ ∖ {0} for a single hyperplane H₀. Then spt S₀ = H₀, and by the constancy theorem (Ch. 6, 2.34) S₀ = c₀[[H₀]] with |c₀| = Θ_{S₀}(y) = 1 for y ∈ H₀ ∖ {0}; hence Θ_{S₀}(0) = 1 < 1 + δ: impossible. So (H2) holds.
6. (C6: conclusions.) For every (z, r) with closedBall z (2r) ⊆ U, step 2 shows that {x ∈ B_r(z) : ∃ θ ≥ 1 + δ, HasMassDensity T x θ} = singularSet T ∩ B_r(z), and step 5 verifies (H1), (H2). Hence threshold_reduction gives: if n ≤ 6 (d₀ = 0), singularSet T ∩ B_r(z) = ∅; if n = 7 (d₀ = 1), singularSet T ∩ B_{r/2}(z) is finite; if n > 7 (d₀ = n − 6 ≥ 2), μH[(n − 6) − 1 + α](singularSet T ∩ B_r(z)) = μH[n − 7 + α](singularSet T ∩ B_r(z)) = 0 for every α > 0. (a) n ≤ 6: the balls B_r(z) cover U and singularSet T ⊆ spt T ⊆ U, so singularSet T = ∅. (b) n = 7: a compact K ⊆ U is covered by finitely many balls B_{r_x/2}(x), x ∈ K, with closedBall x (2r_x) ⊆ U, so singularSet T ∩ K is finite. (c) n > 7: the countably many balls B_r(z) with z ∈ ℚ^P, r ∈ ℚ_{>0} and closedBall z (2r) ⊆ U cover U, so μH[n − 7 + α](singularSet T) = 0 for every α > 0 by countable subadditivity.

## Key steps

1. n = 0: T = 0; for n ≥ 1, T = ∂[[E]] is a minimizing cycle in N with ℓ = 1, and has multiplicity one a.e. by De Giorgi's structure theorem.
2. With δ below the gap constants δ_G(j), 1 ≤ j ≤ n: x ∈ reg T ⇔ Θ(x) < 1 + δ, so sing T = {Θ ≥ 1 + δ}.
3. Zero-scale limits of blow-ups with moving centres are ∂[[F]] in offset planes T_xN − a with multiplicity one (graph description, projected-current identity, uniform perimeter bound, BV compactness); cones lie in linear (n+1)-planes.
4. threshold_reduction with c = 1 + δ, d₀ = n − 6: (H1) fails by multiplicity one; for (H2), cone_splitting gives a codimension-one cone S₀ of dimension n' ∈ [1, 6] with an isolated singularity at 0, excluded by one_dim_cones (n' = 1) and by Simons' theorem B.2 after verifying smoothness and stability (2 ≤ n' ≤ 6).
5. Hence sing T = ∅ (n ≤ 6), locally finite (n = 7), and μH[n−7+α](sing T) = 0 (n > 7).

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD (compared with manifest.json)`
- `grep -n 'μHE\|euclideanHausdorffMeasure' local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean; rg -n addHaarScalarFactor_volume_hausdorffMeasure_ne_zero (same file)`
- `grep -rn 'theorem massOn_le_liminf\|theorem boundary_affinePushforward\|exp_normalizedBallMass_monotoneOn\|theorem bvVariationOn_le_liminf_of_locallyL1\|theorem cone_simonsDefect_lower_bound' simongmt/Poincare`
- `grep -n 'def support\|zeroRegion\|def massOn' simongmt/Poincare/SimonGMT/Chapter06/*.lean`
- `grep -rn dimred --include=*.lean GMT .lake/packages/simongmt/Poincare; grep -c dimred dag.json; grep -rln dimred_ .swarm-worktrees/*/gmt-ch07/GMT (no match anywhere)`
- `python3 inspection of dag.json: sibling lean_statements (abstract_dimension_reduction, density_and_tangent_cones, density_one_implies_regular, compactness_of_minimizing_currents, minimizing_implies_stationary) and similar lemma nodes in other branches (dtc_mass_eq_measure, dor_imrep_massOn_eq_measure_and_support, dtc_dim_zero_eq_zero, imrep_measure_eq_of_represents_same_current, rsd_massOn_eq_measure)`
- `lean -R /tmp/dr-v2-check/src /tmp/dr-v2-check/src/CheckV2Types.lean (private olean of GMT.Ch07.Submission; 12 child types declared as Submission.X in namespace GMT.Ch07 with the contract opens; assembly ⟨A, B, C⟩; #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/MeanCurvature.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/AppendixB/ConeDefect.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1/decomposition-review-receipt-v1.json`
- `/tmp/dr-v2-check/src/CheckV2Types.lean`

Pins match. The snapshot has project b4d606d (equal to workspace HEAD), mathlib 25730c7c and simongmt 2b36630. The snapshot contract is byte-identical to the workspace Contract.lean and Submission.lean; its only sorry is the frozen main_theorem.

Normalization (decides correction R1). Mathlib defines μHE[d] = addHaarScalarFactor(volume, μH[d]) • μH[d] (Measure.lean, lines 68–101). The scalar is in ℝ≥0 and nonzero (addHaarScalarFactor_volume_hausdorffMeasure_ne_zero), so μ_A = ϑ_A·μHE[n] gives ∫_K ϑ_A dμH[n] = c_n⁻¹·μ_A(K).

SimonGMT definitions used:
- massOn is the sSup over admissible forms with Euclidean coefficient norm ≤ 1 (Mass.lean).
- support = U \ zeroRegion (CurrentLocalEquality.lean, lines 108–117).
- WeaklyConvergesOn.massOn_le_liminf (Mass.lean:100) gives the lower semicontinuity used for the new mass bounds.

Other cited library facts exist:
- GeometricCurrentOn.boundary_affinePushforward (AffineCurrentPushforward.lean:188);
- HasGeneralizedMeanCurvatureIn.exp_normalizedBallMass_monotoneOn (Chapter04/MeanCurvature.lean:361);
- bvVariationOn_le_liminf_of_locallyL1 (Chapter02/BV.lean:225);
- cone_simonsDefect_lower_bound (AppendixB/ConeDefect.lean:228).

The library provides none of the following for the contract's IMRep currents: the mass–measure identity, product currents, Federer–Fleming compactness, or Appendix A.4. These are children or sibling prerequisites.

Lean check. All twelve child types elaborate after import GMT.Ch07.Submission, in namespace GMT.Ch07 with the contract opens, with only the stub sorry warnings. The assembly ⟨A, B, C⟩ proves IntegerDensityAndTangentPlanes ∧ SingularSetSmallWhereDensityBelowTwo ∧ CodimensionOneRegularity, and the conditional assembly depends only on propext, Classical.choice and Quot.sound.

Names. No dimred_ identifier occurs in the workspace, SimonGMT, any speculative worktree or dag.json. Similar lemmas in other branches have different types and names, so there is neither reuse nor collision.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
