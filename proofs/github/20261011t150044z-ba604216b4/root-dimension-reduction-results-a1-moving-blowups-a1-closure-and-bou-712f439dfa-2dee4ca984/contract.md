<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.closure_succ-a1.cutoff_extension-a1 -->

## Theorem `Submission.dmcbrcs_cutoff_extension`

Let P, m ∈ ℕ, U ⊆ ℝ^P open and K ⊆ U compact. Then there is a map E : 𝒟_{m+1}(U) → 𝒟_{m+1}(ℝ^P) (GeometricCurrentOn U (m+1) → GeometricCurrentOn univ (m+1)) such that: (i) for every X ∈ 𝒟_{m+1}(U) and every ω ∈ 𝒟^{m+1}(U) with tsupport ω ⊆ K, (E X)(ω) = X(ω), where ω is regarded as a test form on ℝ^P (testFormOnInclusion); (ii) if X_j ⇀ X in U then E X_j ⇀ E X in ℝ^P; (iii) M(E X) ≤ M(X) for every X (total masses: massOn ℝ^P and massOn U, Simon 6.2.4–6.2.5); (iv) if X(ω) = 0 for every ω ∈ 𝒟^{m+1}(U) whose topological support is disjoint from K, then spt(E X) ⊆ K and M(∂(E X)) ≤ M(∂X); (v) if some IMRep R in U represents X and R.carrier ⊆ K, then E X is integer multiplicity in ℝ^P. (In the proof E X(ω) = X(ζω) for one fixed smooth cutoff ζ.)

Node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.closure_succ-a1.cutoff_extension-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5902

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/7128

Decomposition children: None

## Lean problem

Declaration: `Submission.dmcbrcs_cutoff_extension`

```lean
∀ (P m : ℕ) (U K : Set (Euclid P)), IsOpen U → IsCompact K → K ⊆ U → ∃ E : GeometricCurrentOn U (m + 1) → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), (∀ (X : GeometricCurrentOn U (m + 1)) (ω : TestFormOn U (m + 1)), tsupport (ω : DifferentialForm (Euclid P) (m + 1)) ⊆ K → E X (testFormOnInclusion (subset_univ U) (m + 1) ω) = X ω) ∧ (∀ (Xs : ℕ → GeometricCurrentOn U (m + 1)) (X : GeometricCurrentOn U (m + 1)), WeaklyConvergesOn Xs X → WeaklyConvergesOn (fun j => E (Xs j)) (E X)) ∧ (∀ X : GeometricCurrentOn U (m + 1), (E X).mass ≤ X.mass) ∧ (∀ X : GeometricCurrentOn U (m + 1), (∀ ω : TestFormOn U (m + 1), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 1))) K → X ω = 0) → (E X).support ⊆ K ∧ (E X).boundary.mass ≤ X.boundary.mass) ∧ (∀ (X : GeometricCurrentOn U (m + 1)) (R : IMRep U (m + 1)), R.Represents X → R.carrier ⊆ K → IsIntegerMultiplicity (E X))
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

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.closure_succ-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.closure_succ-a1.cutoff_extension-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the parent-supplied proof of dmcbr_closure_succ, step 8 (extension to ℝ^P: X̂(ω) := X(ζω) with a cutoff ζ ∈ C^∞_c(U) equal to 1 near K), together with the facts about the extension used in its steps 9–11 (integer multiplicity, support, mass and boundary-mass bounds, weak convergence, agreement with the original current on forms supported in K). This is the transfer to U = ℝ^P in Simon Ch. 6, Remark 8.3(1) (book/chapter-06.txt lines 2311–2318, printed p. 176). The vanishing hypothesis in (iv) replaces the appeal to (VO) in step 8: it is exactly what (VO) yields from spt X ⊆ K, and the sibling localize supplies it directly. Sibling dependency: SMC = dmcbrcs_testFormOnConverges_smul (key smul_continuity): if ζ : ℝ^P → ℝ is C^∞ with compact support and tsupport ζ ⊆ U, ω_j → 0 in 𝒟^k(ℝ^P) and η_j ∈ 𝒟^k(U) satisfy η_j(x) = ζ(x)•ω_j(x), then η_j → 0 in 𝒟^k(U). Notation: for a covector α, |α| is the Euclidean coefficient norm covectorEuclideanNorm α; 𝒟^k(V) = TestFormOn V k (C^∞ k-forms on ℝ^P with compact support and tsupport ⊆ V); ι := testFormOnInclusion (subset_univ U) (m+1) : 𝒟^{m+1}(U) → 𝒟^{m+1}(ℝ^P), which does not change the underlying form.
1. (Cutoff.) ℝ^P is locally compact and regular, so (Mathlib exists_open_between_and_isCompact_closure) there is an open V₁ with K ⊆ V₁, closure V₁ ⊆ U and closure V₁ compact; applying the same lemma to the compact set closure V₁ ⊆ U gives an open V₂ with closure V₁ ⊆ V₂, closure V₂ ⊆ U and closure V₂ compact. By the smooth Urysohn lemma for finite-dimensional real normed spaces (Mathlib exists_contDiff_support_eq_eq_one_iff, Mathlib/Geometry/Manifold/PartitionOfUnity.lean, available after `import GMT.Ch07.Submission`; smoothness order ⊤ : ℕ∞, s := V₂ open, t := closure V₁ closed, t ⊆ s) there is ζ : ℝ^P → ℝ with ContDiff ℝ ⊤ ζ, range ζ ⊆ [0, 1], support ζ = V₂, and ζ(x) = 1 for every x ∈ closure V₁. Put K₂ := tsupport ζ = closure (support ζ) = closure V₂, a compact subset of U (so ζ has compact support), and N := V₁, an open set with K ⊆ N on which ζ = 1.
2. (Multiplication by ζ.) For a k-form ω on ℝ^P let ζω be x ↦ ζ(x)•ω(x). If ω ∈ 𝒟^k(ℝ^P), then ζω is C^∞ (ContDiff.smul), tsupport(ζω) ⊆ tsupport ω (tsupport_smul_subset_right), which is compact, so ζω has compact support (a closed subset of a compact set), and tsupport(ζω) ⊆ tsupport ζ = K₂ ⊆ U (tsupport_smul_subset_left). So ζω ∈ 𝒟^k(U). The map M_k : 𝒟^k(ℝ^P) → 𝒟^k(U), ω ↦ ζω, is ℝ-linear, because pointwise ζ(x)•(ω + η)(x) = ζ(x)•ω(x) + ζ(x)•η(x) and ζ(x)•(cω(x)) = c(ζ(x)•ω(x)).
3. (Norm homogeneity.) For c ∈ ℝ and a k-covector α, |cα| = |c|·|α|: each coefficient α(e_{I_1}, …, e_{I_k}) with I strictly increasing is multiplied by c, so the sum of squares is multiplied by c², and √(c²s) = |c|√s (Real.sqrt_mul, Real.sqrt_sq_eq_abs). Hence, as 0 ≤ ζ ≤ 1, |ω(x)| ≤ 1 for all x implies |(ζω)(x)| = ζ(x)|ω(x)| ≤ 1 for all x.
4. (Sequential continuity of M_k.) If ω_j → 0 in 𝒟^k(ℝ^P) (TestFormOnConverges), then M_k ω_j → 0 in 𝒟^k(U): this is SMC applied to ζ (C^∞, compact support, tsupport ζ = K₂ ⊆ U), the sequence (ω_j) and η_j := M_k ω_j, for which η_j(x) = ζ(x)•ω_j(x) holds by definition.
5. (Definition of E.) For X ∈ 𝒟_{m+1}(U) let E X have underlying linear map X ∘ M_{m+1}, i.e. (E X)(ω) := X(ζω) for ω ∈ 𝒟^{m+1}(ℝ^P). If ω_j → 0 in 𝒟^{m+1}(ℝ^P), then M_{m+1}ω_j → 0 in 𝒟^{m+1}(U) by step 4, so (E X)(ω_j) = X(M_{m+1}ω_j) → 0 by the continuity field of X. Thus E X ∈ 𝒟_{m+1}(ℝ^P) (a GeometricCurrentOn univ (m+1)).
6. (Proof of (i).) Let ω ∈ 𝒟^{m+1}(U) with tsupport ω ⊆ K. For x ∈ K ⊆ N, ζ(x) = 1 and ζ(x)•ω(x) = ω(x); for x ∉ K, x ∉ tsupport ω, so ω(x) = 0 = ζ(x)•ω(x). Hence ζ·(ιω) = ω pointwise, so M_{m+1}(ιω) = ω in 𝒟^{m+1}(U) (Subtype.ext and funext), and (E X)(ιω) = X(ω).
7. (Proof of (ii).) If X_j ⇀ X in U then, for every ω ∈ 𝒟^{m+1}(ℝ^P), (E X_j)(ω) = X_j(M_{m+1}ω) → X(M_{m+1}ω) = (E X)(ω), since M_{m+1}ω is one fixed element of 𝒟^{m+1}(U). So E X_j ⇀ E X in ℝ^P.
8. (Proof of (iii).) M(E X) = M_{ℝ^P}(E X) is the supremum of ofReal((E X)(ω)) over ω ∈ 𝒟^{m+1}(ℝ^P) with |ω(x)| ≤ 1 for all x (tsupport ω ⊆ ℝ^P holds trivially). For such ω, M_{m+1}ω ∈ 𝒟^{m+1}(U) has tsupport ⊆ U and |ζω| ≤ 1 (step 3), so it is admissible for M_U(X), and ofReal((E X)(ω)) = ofReal(X(M_{m+1}ω)) ≤ M_U(X) = M(X) (GeometricCurrentOn.le_massOn). Taking the supremum (sSup_le) gives M(E X) ≤ M(X).
9. (Proof of (iv), support.) Assume X(ω) = 0 for every ω ∈ 𝒟^{m+1}(U) whose topological support is disjoint from K. Let x ∈ ℝ^P ∖ K. K is compact, hence closed, so (Metric.isOpen_iff for the open set ℝ^P ∖ K) there is ε > 0 with ball(x, ε) ∩ K = ∅; let W := ball(x, ε/2). W is open, x ∈ W, closure W ⊆ closedBall(x, ε/2) (closure_ball_subset_closedBall), so closure W is compact, and closure W ⊆ ℝ^P. For ω ∈ 𝒟^{m+1}(ℝ^P) with tsupport ω ⊆ W: tsupport(ζω) ⊆ tsupport ω ⊆ W ⊆ ball(x, ε) (step 2), which is disjoint from K, so (E X)(ω) = X(M_{m+1}ω) = 0. Thus E X vanishes on W, W belongs to the family whose union is the zero region of E X, x lies in that zero region, and x ∉ spt(E X) = ℝ^P ∖ zeroRegion(E X). Therefore spt(E X) ⊆ K.
10. (Proof of (iv), boundary mass.) Under the same assumption let η ∈ 𝒟^m(ℝ^P) with |η(x)| ≤ 1 for all x. By the definition of the boundary (∂Y(η) = Y(dη), through exteriorDerivativeTestOn), ∂(E X)(η) = (E X)(dη) = X(ζ·dη) and ∂X(ζη) = X(d(ζη)); here d is SimonGMT's exteriorDerivative, an abbreviation of Mathlib's extDeriv (Chapter06/Forms.lean). Let δ := d(ζη) − ζ·dη, the difference of the two elements exteriorDerivativeTestOn U m (M_m η) and M_{m+1}(exteriorDerivativeTestOn univ m η) of 𝒟^{m+1}(U). For y ∈ N the forms ζη and η agree on the open neighbourhood N of y (ζ = 1 on N), i.e. ζη =ᶠ[𝓝 y] η, so d(ζη)(y) = dη(y) (Mathlib Filter.EventuallyEq.extDeriv_eq), and ζ(y)·dη(y) = dη(y). Hence δ = 0 on N, so support δ ⊆ ℝ^P ∖ N; this set is closed, so tsupport δ ⊆ ℝ^P ∖ N (closure_minimal), which is disjoint from K ⊆ N. The hypothesis gives X(δ) = 0, and by linearity X(δ) = X(d(ζη)) − X(ζ·dη), so ∂(E X)(η) = X(ζ·dη) = X(d(ζη)) = ∂X(ζη). Since ζη ∈ 𝒟^m(U) satisfies |ζη| ≤ 1 (step 3) and tsupport(ζη) ⊆ U, it is admissible for M_U(∂X), so ofReal(∂(E X)(η)) ≤ M_U(∂X) = M(∂X). Taking the supremum over η gives M(∂(E X)) ≤ M(∂X).
11. (Proof of (v).) Let R = (M, θ, ξ) be an IMRep in U representing X with M ⊆ K. Let R̂ have the same carrier, multiplicity and orientation, regarded in ℝ^P. The fields measurableSet_carrier, rectifiable, measurable_mult, mult_pos, aestronglyMeasurable_orient and orients do not mention the domain and are inherited (HasApproximateTangentSpaceAt n M x Q depends only on M, x and Q), and carrier_subset holds because M ⊆ ℝ^P. For locallyIntegrable_mult let K′ ⊆ ℝ^P be compact: as M ⊆ K, M ∩ K′ ⊆ M ∩ K, so ∫_{M∩K′} θ dH^{m+1} ≤ ∫_{M∩K} θ dH^{m+1} (lintegral_mono_set) < ∞ by R's own locallyIntegrable_mult field applied to the compact set K ⊆ U. So R̂ is an IMRep in ℝ^P. For ω ∈ 𝒟^{m+1}(ℝ^P), (E X)(ω) = X(ζω) = R.action(ζω) = ∫_M θ(x)·ξ(x)(ζ(x)•ω(x)) dH^{m+1}(x); for x ∈ M ⊆ K ⊆ N we have ζ(x) = 1, so the integrand equals θ(x)·ξ(x)(ω(x)) on M (setIntegral_congr_fun on the measurable set M), and (E X)(ω) = ∫_M θ(x)·ξ(x)(ω(x)) dH^{m+1}(x) = R̂.action(ω). Hence R̂ represents E X, and E X is integer multiplicity.
12. (Conclusion.) The map E of step 5 satisfies (i) (step 6), (ii) (step 7), (iii) (step 8), (iv) (steps 9–10) and (v) (step 11). ∎

Appendix (verified Lean realization of the numbered proof above; not part of the proof). The declaration below was compiled in the decomposition session of dmcbr_closure_succ with Lean v4.35.0-rc3, Mathlib 25730c7c and SimonGMT 2b366308 inside a copy of GMT/Ch07/Contract.lean (namespace GMT.Ch07, after the `noncomputable section ... end` block, before `main_theorem`), i.e. under the frozen imports only, with default options (no `set_option`), as one theorem with local `have`s and no helper declaration. Its only dependency, Submission.dmcbrcs_testFormOnConverges_smul, was present with the proof of the sibling smul_continuity (itself proved from smul_leibniz). `#print axioms` reports propext, Classical.choice and Quot.sound. The runtime's leaf source-delta checker (_recursive_lean/leaf_verification.check_source_delta) accepts the insertion.

```lean
theorem Submission.dmcbrcs_cutoff_extension : ∀ (P m : ℕ) (U K : Set (Euclid P)), IsOpen U → IsCompact K → K ⊆ U → ∃ E : GeometricCurrentOn U (m + 1) → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), (∀ (X : GeometricCurrentOn U (m + 1)) (ω : TestFormOn U (m + 1)), tsupport (ω : DifferentialForm (Euclid P) (m + 1)) ⊆ K → E X (testFormOnInclusion (subset_univ U) (m + 1) ω) = X ω) ∧ (∀ (Xs : ℕ → GeometricCurrentOn U (m + 1)) (X : GeometricCurrentOn U (m + 1)), WeaklyConvergesOn Xs X → WeaklyConvergesOn (fun j => E (Xs j)) (E X)) ∧ (∀ X : GeometricCurrentOn U (m + 1), (E X).mass ≤ X.mass) ∧ (∀ X : GeometricCurrentOn U (m + 1), (∀ ω : TestFormOn U (m + 1), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 1))) K → X ω = 0) → (E X).support ⊆ K ∧ (E X).boundary.mass ≤ X.boundary.mass) ∧ (∀ (X : GeometricCurrentOn U (m + 1)) (R : IMRep U (m + 1)), R.Represents X → R.carrier ⊆ K → IsIntegerMultiplicity (E X)) := by
  have hC := Submission.dmcbrcs_testFormOnConverges_smul
  intro P m U K hU hK hKU
  -- Step 1: the cutoff ζ
  obtain ⟨V₁, hV₁o, hKV₁, hV₁U, hV₁c⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨V₂, hV₂o, hV₁V₂, hV₂U, hV₂c⟩ := exists_open_between_and_isCompact_closure hV₁c hU hV₁U
  obtain ⟨ζ, hζs, hζr, hζsupp, hζone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hV₂o isClosed_closure hV₁V₂
  have htsζ : tsupport ζ = closure V₂ := by rw [tsupport, hζsupp]
  have hζc : HasCompactSupport ζ := by
    rw [HasCompactSupport, htsζ]; exact hV₂c
  have hζU : tsupport ζ ⊆ U := htsζ ▸ hV₂U
  have hζ1 : ∀ x ∈ V₁, ζ x = 1 := fun x hx => (hζone x).1 (subset_closure hx)
  have hζ01 : ∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1 := fun x => hζr (mem_range_self x)
  -- Step 3: absolute homogeneity of the Euclidean coefficient norm
  have hnorm : ∀ (k : ℕ) (c : ℝ) (α : Covector (Euclid P) k),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro k c α
    unfold covectorEuclideanNorm
    have hsum : (∑ I : Fin k → Fin P, if StrictMono I then
          ((c • α) (fun i ↦ EuclideanSpace.basisFun (Fin P) ℝ (I i))) ^ 2 else 0)
        = c ^ 2 * ∑ I : Fin k → Fin P, if StrictMono I then
          (α (fun i ↦ EuclideanSpace.basisFun (Fin P) ℝ (I i))) ^ 2 else 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun I _ => ?_
      split_ifs
      · rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_pow]
      · rw [mul_zero]
    rw [hsum, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]
  have hadm : ∀ (k : ℕ) (ω : DifferentialForm (Euclid P) k), (∀ x, covectorEuclideanNorm (ω x) ≤ 1) →
      ∀ x, covectorEuclideanNorm (ζ x • ω x) ≤ 1 := by
    intro k ω hω x
    rw [hnorm, abs_of_nonneg (hζ01 x).1]
    exact (mul_le_mul (hζ01 x).2 (hω x) (covectorEuclideanNorm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  -- Step 2: multiplication by ζ
  have hmem : ∀ (k : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) k),
      (fun x => ζ x • (ω : DifferentialForm (Euclid P) k) x) ∈ TestFormOn U k := by
    intro k ω
    have hω : IsTestForm (ω : DifferentialForm (Euclid P) k) ∧
        tsupport (ω : DifferentialForm (Euclid P) k) ⊆ univ := ω.property
    have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (ω : DifferentialForm (Euclid P) k) := hω.1.1
    have hcompact : IsCompact (tsupport (ω : DifferentialForm (Euclid P) k)) := hω.1.2
    have hsub : tsupport (fun x => ζ x • (ω : DifferentialForm (Euclid P) k) x) ⊆
        tsupport (ω : DifferentialForm (Euclid P) k) :=
      tsupport_smul_subset_right (fun x => ζ x) _
    have hsubζ : tsupport (fun x => ζ x • (ω : DifferentialForm (Euclid P) k) x) ⊆ tsupport ζ :=
      tsupport_smul_subset_left (fun x => ζ x) _
    have hcpt : IsCompact (tsupport fun x => ζ x • (ω : DifferentialForm (Euclid P) k) x) :=
      hcompact.of_isClosed_subset (isClosed_tsupport _) hsub
    exact ⟨⟨hζs.smul hsmooth, hcpt⟩, hsubζ.trans hζU⟩
  let Mk : (k : ℕ) → TestFormOn (univ : Set (Euclid P)) k →ₗ[ℝ] TestFormOn U k := fun k =>
    { toFun := fun ω => ⟨fun x => ζ x • (ω : DifferentialForm (Euclid P) k) x, hmem k ω⟩
      map_add' := fun ω η => by
        apply Subtype.ext; funext x
        change ζ x • ((ω : DifferentialForm (Euclid P) k) x + (η : DifferentialForm (Euclid P) k) x) =
          ζ x • (ω : DifferentialForm (Euclid P) k) x + ζ x • (η : DifferentialForm (Euclid P) k) x
        rw [smul_add]
      map_smul' := fun c ω => by
        apply Subtype.ext; funext x
        change ζ x • (c • (ω : DifferentialForm (Euclid P) k) x) =
          c • (ζ x • (ω : DifferentialForm (Euclid P) k) x)
        rw [smul_comm] }
  have hMk : ∀ (k : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) k) (x : Euclid P),
      ((Mk k ω : TestFormOn U k) : DifferentialForm (Euclid P) k) x =
        ζ x • (ω : DifferentialForm (Euclid P) k) x := fun _ _ _ => rfl
  -- Step 5: the extension
  let E : GeometricCurrentOn U (m + 1) → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1) :=
    fun X =>
      { toCurrent := X.toCurrent.comp (Mk (m + 1))
        continuous' := fun ωs hω => by
          have h1 := hC P (m + 1) U ζ ωs (fun j => Mk (m + 1) (ωs j)) hζs hζc hζU hω
            (fun j x => rfl)
          have h2 := X.continuous' _ h1
          have h3 : (fun j => X.toCurrent ((fun j => Mk (m + 1) (ωs j)) j)) =
              (fun j => (X.toCurrent.comp (Mk (m + 1))) (ωs j)) := rfl
          rw [h3] at h2
          exact h2 }
  have hE : ∀ (X : GeometricCurrentOn U (m + 1)) (ω : TestFormOn (univ : Set (Euclid P)) (m + 1)),
      E X ω = X (Mk (m + 1) ω) := fun _ _ => rfl
  refine ⟨E, ?_, ?_, ?_, ?_, ?_⟩
  · -- (i) agreement on forms supported in K
    intro X ω hω
    rw [hE]
    congr 1
    apply Subtype.ext; funext x
    change ζ x • (ω : DifferentialForm (Euclid P) (m + 1)) x = (ω : DifferentialForm (Euclid P) (m + 1)) x
    by_cases hx : x ∈ K
    · rw [hζ1 x (hKV₁ hx), one_smul]
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hω h)), smul_zero]
  · -- (ii) weak convergence
    intro Xs X hX ω
    exact hX (Mk (m + 1) ω)
  · -- (iii) mass
    intro X
    apply sSup_le
    rintro _ ⟨ω, ⟨-, hω⟩, rfl⟩
    exact X.le_massOn ⟨(Mk (m + 1) ω).property.2, hadm (m + 1) _ hω⟩
  · -- (iv) support and boundary mass
    intro X hvan
    constructor
    · intro x hx
      by_contra hxK
      obtain ⟨ε, hε, hεK⟩ := Metric.isOpen_iff.1 hK.isClosed.isOpen_compl x hxK
      apply hx.2
      refine ⟨ball x (ε / 2), ⟨isOpen_ball, ?_, subset_univ _, ?_⟩, mem_ball_self (half_pos hε)⟩
      · exact (isCompact_closedBall x (ε / 2)).of_isClosed_subset isClosed_closure
          closure_ball_subset_closedBall
      · intro ω hω
        rw [hE]
        apply hvan
        rw [Set.disjoint_left]
        intro y hy hyK
        have hy' : y ∈ tsupport (ω : DifferentialForm (Euclid P) (m + 1)) :=
          tsupport_smul_subset_right _ _ hy
        exact hεK (ball_subset_ball (half_le_self hε.le) (hω hy')) hyK
    · apply sSup_le
      rintro _ ⟨η, ⟨-, hη⟩, rfl⟩
      have hδ : X (exteriorDerivativeTestOn U m (Mk m η) -
          Mk (m + 1) (exteriorDerivativeTestOn univ m η)) = 0 := by
        apply hvan
        have hzero : ∀ y ∈ V₁, ((exteriorDerivativeTestOn U m (Mk m η) -
            Mk (m + 1) (exteriorDerivativeTestOn univ m η) : TestFormOn U (m + 1)) :
              DifferentialForm (Euclid P) (m + 1)) y = 0 := by
          intro y hy
          change extDeriv (fun x => ζ x • (η : DifferentialForm (Euclid P) m) x) y -
            ζ y • extDeriv (η : DifferentialForm (Euclid P) m) y = 0
          have hev : (fun x => ζ x • (η : DifferentialForm (Euclid P) m) x) =ᶠ[𝓝 y]
              (η : DifferentialForm (Euclid P) m) := by
            filter_upwards [hV₁o.mem_nhds hy] with z hz
            rw [hζ1 z hz, one_smul]
          rw [hev.extDeriv_eq, hζ1 y hy, one_smul, sub_self]
        have hts : tsupport ((exteriorDerivativeTestOn U m (Mk m η) -
            Mk (m + 1) (exteriorDerivativeTestOn univ m η) : TestFormOn U (m + 1)) :
              DifferentialForm (Euclid P) (m + 1)) ⊆ V₁ᶜ := by
          apply closure_minimal _ hV₁o.isClosed_compl
          intro y hy hyV
          exact hy (hzero y hyV)
        exact Set.disjoint_of_subset_left hts (Set.disjoint_compl_left_iff_subset.2 hKV₁)
      have heq : (E X).boundary η = X.boundary (Mk m η) := by
        rw [GeometricCurrentOn.boundary_apply, GeometricCurrentOn.boundary_apply, hE]
        have hsub := X.toCurrent.map_sub (exteriorDerivativeTestOn U m (Mk m η))
          (Mk (m + 1) (exteriorDerivativeTestOn univ m η))
        change X.toCurrent (exteriorDerivativeTestOn U m (Mk m η) -
          Mk (m + 1) (exteriorDerivativeTestOn univ m η)) = 0 at hδ
        rw [hsub, sub_eq_zero] at hδ
        exact hδ.symm
      change ENNReal.ofReal ((E X).boundary η) ≤ X.boundary.mass
      rw [heq]
      exact X.boundary.le_massOn ⟨(Mk m η).property.2, hadm m _ hη⟩
  · -- (v) integer multiplicity
    intro X R hR hRK
    refine ⟨{ carrier := R.carrier
              mult := R.mult
              orient := R.orient
              measurableSet_carrier := R.measurableSet_carrier
              carrier_subset := subset_univ _
              rectifiable := R.rectifiable
              measurable_mult := R.measurable_mult
              mult_pos := R.mult_pos
              locallyIntegrable_mult := fun K' _ _ => ?_
              aestronglyMeasurable_orient := R.aestronglyMeasurable_orient
              orients := R.orients }, ?_⟩
    · refine ne_top_of_le_ne_top (R.locallyIntegrable_mult K hK hKU) (lintegral_mono_set ?_)
      exact fun x hx => ⟨hx.1, hRK hx.1⟩
    · intro ω
      rw [hE, hR (Mk (m + 1) ω)]
      unfold IMRep.action
      apply setIntegral_congr_fun R.measurableSet_carrier
      intro x hx
      change (R.mult x : ℝ) * R.orient x (ζ x • (ω : DifferentialForm (Euclid P) (m + 1)) x) =
        (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) (m + 1)) x)
      rw [hζ1 x (hKV₁ (hRK hx)), one_smul]
```

## Key steps

1. Smooth cutoff ζ: ℝ^P → [0, 1] with compact tsupport ζ ⊆ U and ζ = 1 on an open N ⊇ K (exists_open_between_and_isCompact_closure twice, then exists_contDiff_support_eq_eq_one_iff).
2. ω ↦ ζω maps 𝒟^k(ℝ^P) linearly into 𝒟^k(U), shrinks tsupport, and keeps |ω| ≤ 1 (the Euclidean coefficient norm is absolutely homogeneous).
3. ω ↦ ζω is sequentially continuous (sibling smul_continuity), so E X := X(ζ·) is a current in ℝ^P; weak convergence passes through E.
4. ζω = ω when tsupport ω ⊆ K, so E X agrees with X there; admissible forms map to admissible forms, so M(E X) ≤ M(X).
5. If X vanishes on forms supported off K: E X vanishes on small balls missing K, so spt E X ⊆ K; d(ζη) − ζdη vanishes on N (EventuallyEq.extDeriv_eq), so ∂(E X)(η) = ∂X(ζη) and M(∂E X) ≤ M(∂X).
6. An IMRep in U with carrier in K, regarded in ℝ^P, is an IMRep there (compact local integrability) and represents E X because ζ = 1 on the carrier.

## Reference use

### local-project

Queries:
- `python3 over RUN/dag.json: selected node, siblings convergence_tools/im_local/closure_compact (types byte-identical to the twin cbr_* nodes), twin node root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_succ-a1 (type byte-identical), its decomposition-v2/audit-v2, status and candidate commits of the six reused declarations, and absence of the names dmcbrcs_norm_iteratedFDeriv_smul_le, dmcbrcs_testFormOnConverges_smul, dmcbrcs_cutoff_extension, dmcbrcs_localize_at_point`
- `rg -c dmcbrcs SNAPSHOT (no match, exit 1); grep -c dmcbrcs GMT/Ch07/Submission.lean (0); cmp SNAPSHOT/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Submission.lean GMT/Ch07/Contract.lean; git rev-parse HEAD (b4d606d), mathlib 25730c7c, simongmt 2b366308`
- `rg -n -F in SNAPSHOT/mathlib/Mathlib: exists_contDiff_support_eq_eq_one_iff, norm_iteratedFDeriv_smul_le, Filter.EventuallyEq.extDeriv_eq, exists_open_between_and_isCompact_closure, support_iteratedFDeriv_subset, tsupport_iteratedFDeriv_subset, HasCompactSupport.iteratedFDeriv, iteratedFDeriv_fun_zero, bounded_above_of_compact_support, eventually_all_finset, tendstoUniformlyOn_iff, setIntegral_congr_fun, lintegral_mono_set, tsupport_smul_subset_left/right, ContDiff.smul, extraction_of_frequently_atTop, frequently_lt_of_liminf_lt, limsup_comp, setIntegral_eq_integral_of_forall_compl_eq_zero, enorm_integral_le_lintegral_enorm, LipschitzWith.dist_left; sed of Mathlib/Analysis/Calculus/ContDiff/Bounds.lean lines 36-260 (Leibniz proofs and imports)`
- `lake env lean availability probe after `import GMT.Ch07.Submission`: #check norm_iteratedFDeriv_smul_le and ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear (unknown), exists_contDiff_support_eq_eq_one_iff, EventuallyEq.extDeriv_eq, ContinuousLinearMap.precompR/precompL, norm_precompR_le, fderivWithin_of_bilinear, norm_iteratedFDerivWithin_fderivWithin, Finset.sum_choose_succ_mul (available); Norm instance on three-level CLM spaces needs maxSynthPendingDepth 3 when written explicitly`
- `git log --all -G '^import ' -- GMT/Ch07/Submission.lean and -S 'set_option maxHeartbeats' (import additions and set_option reverted by the leaf gate: fa0865963, d5ba41d68, fe5f15468, 410955ec1); grep set_option in _recursive_lean/*.py (leaf_verification.check_source_delta forbidden-token rule)`
- `sed of SimonGMT Chapter06 Currents.lean (TestFormOnConverges, GeometricCurrentOn, WeaklyConvergesOn, boundary), Mass.lean (covectorEuclideanNorm, massAdmissibleOn, massOn, le_massOn, massOn_le_liminf), CurrentLocalEquality.lean (testFormOnInclusion, restrictDomain, zeroRegion, support), Forms.lean (exteriorDerivative = extDeriv); book/chapter-06.txt lines 2280-2345 (Simon 8.2, Remark 8.3(1), printed p. 176)`
- `lake env lean on /tmp/dmcbr-succ-dec/lean/{Types,Assembly,Localize,LocalizeHyp,LocalizeFinal,Challenges}.lean, /tmp/dmcbr-succ-dec/proto/{Leibniz3,Cont3,Cutoff}.lean and /tmp/dmcbr-succ-dec/final/FromJSON.lean; leaf_verification.check_source_delta on each appendix insertion; lean_contract.validate_lean_statement on all child types`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Bounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Separation/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-79c745d596/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-932152a15b/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-932152a15b/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-f9e8023a0d/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/tmp/dmcbr-succ-dec/lean/Assembly.lean`
- `/tmp/dmcbr-succ-dec/lean/LocalizeHyp.lean`
- `/tmp/dmcbr-succ-dec/final/FromJSON.lean`

Pins match: HEAD b4d606d is the snapshot project commit, with Mathlib 25730c7c and SimonGMT 2b366308, and Submission.lean is byte-identical to the frozen contract. The snapshot has no dmcbrcs declaration and no closure or extension theorem; its Chapter 6 matches are definitions only. Every Mathlib name cited by the child proofs exists in the pinned sources. One cited name, norm_iteratedFDeriv_smul_le from Mathlib.Analysis.Calculus.ContDiff.Bounds, is outside the frozen import closure, so the Leibniz bound becomes the child smul_leibniz, transcribed from that file and verified. The six reused declarations are accepted, with byte-identical declarations in their candidate commits. All child types elaborate, and the hypothesis-only assembly proves the exact parent type with propext, Classical.choice and Quot.sound. Every new child's appendix compiles under default options and passes the leaf source-delta gate.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
