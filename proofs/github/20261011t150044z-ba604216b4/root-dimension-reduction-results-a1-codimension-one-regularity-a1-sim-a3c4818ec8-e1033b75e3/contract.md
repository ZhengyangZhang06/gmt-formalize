<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.simons_cone-a1 -->

## Theorem `Submission.codim1_hcp_stable_minimal_cone_flat`

Simons' theorem (Simon B.2) for smooth cones. Data: P, m ∈ ℕ; a linear subspace A₀ ⊆ ℝ^P; M ⊆ ℝ^P; ν : ℝ^P → ℝ^P. Hypotheses: 2 ≤ m ≤ 6; dim A₀ = m + 1; M ⊆ A₀; 0 ∉ M; M is an embedded C^r m-dimensional submanifold of ℝ^P for every r ∈ ℕ; closure(M) ⊆ M ∪ {0}; tx ∈ M for every x ∈ M and t > 0; H^m(M ∩ K) < ∞ for every compact K ⊆ ℝ^P; M is stationary away from 0: ∫_M div_M X dH^m = 0 for every C¹ X : ℝ^P → ℝ^P with compact support and 0 ∉ tsupport X (div_M X(x) := trace(P_x∘DX(x)), P_x the orthogonal projection onto span(tangentSpace M x)); ν is C^∞ on some open set O ⊇ M, and for every x ∈ M, ν(x) ∈ A₀, |ν(x)| = 1, ν(x)·v = 0 for all v ∈ tangentSpace M x, and trace(P_x∘Dν(x)) = 0; and the stability inequality B.1 holds: ∫_M |A|²ζ² dH^m ≤ ∫_M |∇^Mζ|² dH^m for every ζ : ℝ^P → ℝ that is locally Lipschitz on M and vanishes on M outside some compact subset of M, where |A|²(x) := Σ_{j=1}^P |Dν(x)(P_xe_j)|², |∇^Mζ|²(x) := Σ_{j=1}^P (fderivWithin ℝ ζ M x (P_xe_j))², e_j = EuclideanSpace.single j 1, H^m = μHE[m] (Bochner integrals). Conclusion: Dν(x)v = 0 (fderiv ℝ ν x v = 0) for every x ∈ M and every v ∈ tangentSpace M x.

Node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.simons_cone-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5240

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5997, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6001, https://github.com/ZhengyangZhang06/gmt-formalize/issues/984, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4210, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4182

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/984, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6797, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6803, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6808, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6813, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6818, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6821, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6827, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6830, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6835, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6841, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6848

## Lean problem

Declaration: `Submission.codim1_hcp_stable_minimal_cone_flat`

```lean
∀ (P m : ℕ) (A₀ : Submodule ℝ (Euclid P)) (M : Set (Euclid P)) (ν : Euclid P → Euclid P), 2 ≤ m → m ≤ 6 → Module.finrank ℝ A₀ = m + 1 → M ⊆ (A₀ : Set (Euclid P)) → (0 : Euclid P) ∉ M → (∀ r : ℕ, IsEmbeddedSubmanifold r m M) → closure M ⊆ insert 0 M → (∀ t : ℝ, 0 < t → ∀ x ∈ M, t • x ∈ M) → (∀ K : Set (Euclid P), IsCompact K → μHE[m] (M ∩ K) ≠ ∞) → (∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → (0 : Euclid P) ∉ tsupport X → ∫ x in M, LinearMap.trace ℝ (Euclid P) ((Submodule.span ℝ (tangentSpace M x)).starProjection.toLinearMap ∘ₗ (fderiv ℝ X x).toLinearMap) ∂μHE[m] = 0) → (∃ O : Set (Euclid P), IsOpen O ∧ M ⊆ O ∧ ContDiffOn ℝ (⊤ : ℕ∞) ν O) → (∀ x ∈ M, ν x ∈ A₀ ∧ ‖ν x‖ = 1 ∧ ∀ v ∈ tangentSpace M x, inner ℝ (ν x) v = 0) → (∀ x ∈ M, LinearMap.trace ℝ (Euclid P) ((Submodule.span ℝ (tangentSpace M x)).starProjection.toLinearMap ∘ₗ (fderiv ℝ ν x).toLinearMap) = 0) → (∀ ζ : Euclid P → ℝ, LocallyLipschitzOn M ζ → (∃ C : Set (Euclid P), IsCompact C ∧ C ⊆ M ∧ ∀ x ∈ M, x ∉ C → ζ x = 0) → ∫ x in M, (∑ j : Fin P, ‖fderiv ℝ ν x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))‖ ^ 2) * ζ x ^ 2 ∂μHE[m] ≤ ∫ x in M, ∑ j : Fin P, (fderivWithin ℝ ζ M x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))) ^ 2 ∂μHE[m]) → ∀ x ∈ M, ∀ v ∈ tangentSpace M x, fderiv ℝ ν x v = 0
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

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.simons_cone-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Simon Appendix B: B.4–B.11 and the printed proof of B.2 (chapter-B.txt lines 88–282 = chapter-07-source.txt lines 1340–1539), as organized in steps 3 (homogeneity of ν), 5, 6, 7, 8 and 9 of the supplied proof of the parent. The finite-dimensional algebra of B.10–B.11 is kernel-checked in SimonGMT: Poincare.SimonGMT.AppendixB.simonsDefect_eq_sum_skew, four_mul_radialSkewSum_le, radial_derivative_of_codazzi, cone_simonsDefect_lower_bound; the exponent is AppendixB.exists_final_exponent (ε = 1/10). Departures, stated explicitly: (i) the printed proof obtains the finiteness of the integrals in (4) and (6) from the polar formula (5) ∫_M f dH^m = ∫_0^∞ r^{m−1}∫_Σ f(rω) dH^{m−1}(ω) dr; only these finiteness statements and the H^m-nullity of M ∩ {r = 1} are used, and they are proved below by dyadic scaling of H^m, which avoids the (m−1)-dimensional area formula on Σ; (ii) as printed, the second line of B.7 carries the opposite sign on the two curvature terms relative to its first line and B.6; Simons' identity is derived below with one fixed convention, and it coincides with the printed B.8 (whose printed proof uses the correct signs); (iii) the cut-off parameter of the printed text, also called ε there, is called κ. Sibling lemmas: smooth_charts (Submission.codim1_hcp_smooth_charts), lipschitz_approx (Submission.codim1_hcp_lipschitz_smooth_approx), chart_tangent_space, density_one (Submission.dimred_rpd_submanifold_density_one), locally_closed (Submission.dimred_rpd_embedded_locally_closed).

Notation. H^m := μHE[m]; r(x) := |x|; U₀ := ℝ^P ∖ {0}; T_x := tangentSpace M x, P_x its orthogonal projection; D_τν := Dν(x)τ; for a linear functional ℓ, |ℓ|²_{T_x} := Σ_jℓ(P_xe_j)² (= Σ_iℓ(τ_i)² for an orthonormal basis τ of T_x). If M = ∅ there is nothing to prove; assume M ≠ ∅.

0. (Preliminaries.)
 (0a) Cone and closure. Applying the cone property with t and 1/t gives tM = M for t > 0. Since 0 ∉ M and closure(M) ⊆ M ∪ {0}, M is closed in U₀, and for 0 < a ≤ b the set M ∩ {a ≤ r ≤ b} = closure(M) ∩ {a ≤ r ≤ b} is compact. So a function vanishing on M outside M ∩ {a ≤ r ≤ b} vanishes outside a compact subset of M.
 (0b) Tangent spaces. For x ∈ M, T_x is an m-dimensional linear subspace (chart_tangent_space), T_x ⊆ A₀ (velocities of curves in M ⊆ A₀), A₀ = T_x ⊕ ℝν(x) orthogonally, x ∈ T_x (s ↦ e^sx is a C¹ curve in M through x with velocity x), and T_{tx} = T_x for t > 0 (if γ is a C¹ curve in M through x then tγ is one through tx, so tT_x ⊆ T_{tx}, and symmetrically). Hence P_x(x/|x|) = x/|x|, and for f(z) = g(|z|) with g C¹ near |x|, |Df(x)|_{T_x} = |g'(|x|)|.
 (0c) Second fundamental form. For x ∈ M and τ, η ∈ T_x: D_τν ∈ T_x (differentiate ν(γ(s)) ∈ A₀ and |ν(γ(s))|² = 1 along a C¹ curve γ in M with γ'(0) = τ, and use (0b)); and η·D_τν = τ·D_ην (in a C^∞ chart ψ of M (smooth_charts), differentiate ν(ψ(v))·∂_iψ(v) = 0 in v_j; the term ν·∂_j∂_iψ is symmetric). With an orthonormal basis τ_1, …, τ_m of T_x and h_ij := −τ_j·D_{τ_i}ν = h_ji: D_{τ_i}ν = −Σ_jh_ijτ_j; |A|²(x) = Σ_j|Dν(x)(P_xe_j)|² = Σ_i|D_{τ_i}ν|² = Σ_{i,j}h_ij² (Hilbert–Schmidt identity Σ_j|LP_xe_j|² = Σ_i|Lτ_i|²); and H := Σ_ih_ii = −trace(P_xDν(x)) = 0.
 (0d) Homogeneity (parent step 3). For x ∈ M and t > 0, ν(tx) = ν(x): ν(tx) is a unit vector of A₀ ∩ T_{tx}^⊥ = A₀ ∩ T_x^⊥ = ℝν(x), so ν(tx) = ±ν(x), and t ↦ ν(tx)·ν(x) is continuous on (0, ∞) with values in {±1} and value 1 at t = 1. Differentiating ν(tγ(s)) = ν(γ(s)) at s = 0 along C¹ curves γ in M through x gives t·Dν(tx)τ = Dν(x)τ for τ ∈ T_x. Hence, computed in the same orthonormal basis of T_{tx} = T_x, h_ij(tx) = t^{-1}h_ij(x) and |A|²(tx) = t^{-2}|A|²(x); and D_xν = d/dt ν(tx)|_{t=1} = 0.
 (0e) Measure facts. (i) H^m(tE) = t^mH^m(E) for E ⊆ ℝ^P and t > 0 (scaling of Hausdorff measure). (ii) a₀ := H^m(M ∩ {1 ≤ r < 2}) < ∞ (the closed annulus is compact), and H^m(M ∩ {2^k ≤ r < 2^{k+1}}) = 2^{km}a₀ for every k ∈ ℤ, by (i) and 2^kM = M. (iii) H^m(M ∩ {r = c}) = 0 for every c > 0: the sets M ∩ {r = c}, 1 ≤ c ≤ 2, are pairwise disjoint subsets of a set of finite measure, so at most countably many have positive measure, while H^m(M ∩ {r = c}) = c^mH^m(M ∩ {r = 1}) by (i). (iv) Every nonempty relatively open subset of M has positive H^m-measure: for x ∈ M, H^m(M ∩ B_s(x))/(ω_ms^m) → 1 as s ↓ 0 (density_one).
 (0f) Regularity of |A|. For y ∈ M, smooth_charts and the inverse function theorem (Simon 2, 4.4, applied to the orthogonal projection onto T_y of a C^∞ chart) give a C^∞ graph chart G : D → M ∩ W (D ⊆ ℝ^m an open ball, W ∋ y open, M ∩ W = G(D)) whose inverse is the restriction to M ∩ W of an affine 1-Lipschitz map. In it, P_{G(a)} = DG(a)(DG(a)*DG(a))^{-1}DG(a)* and a ↦ Dν(G(a))∘P_{G(a)} are C^∞, |A|²(G(a)) = ‖Dν(G(a))∘P_{G(a)}‖²_HS is C^∞, and |A|(G(a)) = ‖Dν(G(a))∘P_{G(a)}‖_HS is locally Lipschitz in a (the Hilbert–Schmidt norm is 1-Lipschitz). Hence |A|² is smooth along M, |A| is locally Lipschitz on M, and |A| is smooth along M on the relatively open set {|A| > 0}. c_Σ := sup{|A|²(x) : x ∈ M, |x| = 1} < ∞ (a continuous function on the compact set M ∩ {r = 1}, (0a)), and |A|²(x) ≤ c_Σ|x|^{-2} on M by (0d).
 (0g) Calculus on M. For f smooth along M, d^M_xf is its derivative along M (unique on T_x), ∇^Mf(x) ∈ T_x represents it, the divergence of a smooth tangent field Y along M is div_MY(x) := Σ_iτ_i·D_{τ_i}Y (derivatives along curves in M), and Δ_Mf := div_M∇^Mf (the Laplace–Beltrami operator, = Σ_kf_{;kk} in an orthonormal frame). A locally Lipschitz function on M is differentiable within M at H^m-a.e. point of M (Rademacher's theorem in the coordinates of the graph charts, Simon 2, 4.8–4.9: G is locally Lipschitz, so it maps L^m-null sets to H^m-null sets); at such points fderivWithin ℝ f M x is a derivative within M, unique on T_x, and the product and chain rules hold. If f ≥ 0 is locally Lipschitz on M, f(x) = 0 and f is differentiable within M at x, then d^M_xf = 0 on T_x (x is a minimum and every τ ∈ T_x is the velocity of a C¹ curve in M through x). Measurability: for every f locally Lipschitz on M and every j, x ↦ fderivWithin ℝ f M x (P_xe_j) is H^m-a.e. strongly measurable on M (lipschitz_approx, part (i)); hence every integrand below that is built from |A|, r, ψ and tangential derivatives of locally Lipschitz functions is a.e.-measurable on M, and the bounded ones with support in a compact subset of M are integrable.

1. (Simons' identity B.8; Simon B.4–B.9.) Near x₀ ∈ M take a smooth orthonormal frame τ_1, …, τ_m of tangent fields along M (Gram–Schmidt applied to ∂_jG). Let ∇_XY := P(D_XY) be the Levi-Civita connection of M, R(X, Y)Z := ∇_X∇_YZ − ∇_Y∇_XZ − ∇_{[X,Y]}Z its curvature, S the shape operator SX := −D_Xν (tangent by (0c)), so h(X, Y) = SX·Y. Write h_{ij;k} := (∇_{τ_k}h)(τ_i, τ_j) and h_{ij;kl} := (∇²_{τ_l,τ_k}h)(τ_i, τ_j), where ∇²_{X,Y} := ∇_X∇_Y − ∇_{∇_XY} (so k is differentiated first); repeated indices are summed. All fields are A₀-valued and A₀ = T_x ⊕ ℝν(x), so for tangent fields Y, Z: D_YZ = ∇_YZ + h(Y, Z)ν (differentiate ν·Z = 0 along Y).
 B.4 h_ij = h_ji ((0c)); hence h_{ij;k} and h_{ij;kl} are symmetric in i, j.
 B.5/B.6 (Codazzi and Gauss). Flatness of ℝ^P gives D_XD_YZ − D_YD_XZ − D_{[X,Y]}Z = 0. Expanding with D_YZ = ∇_YZ + h(Y, Z)ν and D_Xν = −SX, the normal component gives (∇_Xh)(Y, Z) = (∇_Yh)(X, Z) (Codazzi; with B.4, h_{ij;k} is totally symmetric), and the tangential component gives R(X, Y)Z = h(Y, Z)SX − h(X, Z)SY (Gauss; in components R(τ_i, τ_j)τ_k·τ_l = h_jkh_il − h_ikh_jl, so the sectional curvatures are h_iih_jj − h_ij², as in B.6).
 B.7 (Ricci identity, the definition of R on tensors): h_{ij;kl} − h_{ij;lk} = −h(R(τ_l, τ_k)τ_i, τ_j) − h(τ_i, R(τ_l, τ_k)τ_j).
 Commutation. By B.7 and Gauss, with Sτ_a = h_abτ_b: Σ_k(h_{ki;jk} − h_{ki;kj}) = −h(R(τ_k, τ_j)τ_k, τ_i) − h(τ_k, R(τ_k, τ_j)τ_i) = −[(h³)_ji − H(h²)_ji] − [|A|²h_ji − (h³)_ij] = H(h²)_ij − |A|²h_ij.
 Simons' identity. h_{ij;kk} = h_{ik;jk} (Codazzi, differentiated) = h_{ki;jk} (B.4) = h_{ki;kj} + H(h²)_ij − |A|²h_ij (commutation) = H_{;ij} + H(h²)_ij − |A|²h_ij (Codazzi: Σ_kh_{ki;k} = Σ_kh_{kk;i} = H_{;i}). Multiplying by h_ij and using ½Δ_M|A|² = ½(h_ij²)_{;kk} = h_ijh_{ij;kk} + Σh²_{ij;k}:
 (B.8) ½Δ_M|A|² = Σ_{i,j,k}h²_{ij;k} − |A|⁴ + h_ijH_{;ij} + H·h_mih_mjh_ij.
 Since H ≡ 0 on M ((0c)), ½Δ_M|A|² = Σh²_{ij;k} − |A|⁴. (Check: for the unit sphere, h = δ gives Δh = 0, consistent with the formula h_{ij;kk} = H_{;ij} + H(h²)_ij − |A|²h_ij.)

2. (Lemma B.11.) Let x ∈ M with |A|(x) > 0 and put D := Σ_{i,j,k}h²_{ij;k} − |A|^{-2}Σ_k(Σ_{i,j}h_ijh_{ij;k})². Then D ≥ 2r^{-2}|A|² at x. Proof as printed:
 - Choose the frame near x so that τ_m(z) = z/|z| and τ_1, …, τ_{m−1} are constant along rays (possible by (0b): T_{tz} = T_z ∋ z; take a smooth orthonormal tangent frame e_1, …, e_m near x/|x|, project e_i(z/|z|) onto z^⊥, select m − 1 of these that are independent at x and apply Gram–Schmidt; all operations depend on z/|z| only).
 - (1) h_mj = h_jm = 0 on the ray ℓ_x, because D_{τ_m}ν = |z|^{-1}D_zν = 0 by (0d).
 - (2) h_{ij;m} = −r^{-1}h_ij on ℓ_x: along ℓ_x the frame is constant, so ∇_{τ_m}τ_i = P(D_{τ_m}τ_i) = 0 and h_{ij;m} = τ_m(h_ij) = d/ds h_ij(x + sx/|x|)|_{s=0} = −|x|^{-1}h_ij(x), by h_ij(tx) = t^{-1}h_ij(x) in this frame ((0d)).
 - The algebra: D = ½|A|^{-2}Σ_kΣ_{i,j,r,s}(h_rsh_{ij;k} − h_ijh_{rs;k})² ≥ 2|A|^{-2}Σ_kΣ_{i,j,r<m}(h_ijh_{rm;k})² (the four placements of one radial index; terms containing h_rm vanish by (1)), and Codazzi with (2) gives h_rm;k = h_rk;m = −r^{-1}h_rk, so D ≥ 2r^{-2}|A|^{-2}Σ_{i,j}h_ij²Σ_{r,k}h_rk² = 2r^{-2}|A|² by (1). In SimonGMT terms (index set Fin m = Fin (n + 1), n := m − 1, last index radial, h := (h_ij(x)), dh := (h_{ij;k}(x)), ρ := r(x)): the hypotheses h_last_left, h_last_right are (1), h_flip and dh_flip are B.4, dh_radial is radial_derivative_of_codazzi applied to Codazzi and (2), and cone_simonsDefect_lower_bound gives 2ρ^{-2}·secondFundamentalNormSq h ≤ simonsDefect h dh = D.

3. (Inequality (1) of the printed proof.) H^m-a.e. on M,
 (1) ½Δ_M|A|² + |A|⁴ ≥ 2r^{-2}|A|² + |∇^M|A||².
 Where |A| > 0 (relatively open), |A| is smooth and ∇_k|A| = |A|^{-1}Σ_{ij}h_ijh_{ij;k}, so |∇^M|A||² = |A|^{-2}Σ_k(Σ_{ij}h_ijh_{ij;k})² and (1) is B.8 (with H = 0) combined with Lemma B.11. At points with |A| = 0 at which |A| is differentiable within M (H^m-a.e. such point, by (0f), (0g)), ∇^M|A| = 0 by the minimum principle of (0g), and ½Δ_M|A|² = Σh²_{ij;k} ≥ 0 = 2r^{-2}|A|² + |∇^M|A||² − |A|⁴.

4. (Inequality (3) of the printed proof.) Let ψ be locally Lipschitz on M and vanish on M outside a compact subset of M. Then
 (3) 2∫_M r^{-2}ψ²|A|² dH^m ≤ ∫_M |A|²|∇^Mψ|² dH^m.
 (4a) ζ := |A|ψ (with |A|(x) := (Σ_j|Dν(x)(P_xe_j)|²)^{1/2}) is locally Lipschitz on M ((0f)) and vanishes on M outside a compact subset of M, so B.1 gives
 (2) ∫_M |A|⁴ψ² ≤ ∫_M |∇^M(|A|ψ)|² = ∫_M (|∇^Mψ|²|A|² + ψ²|∇^M|A||² + 2ψ|A|∇^Mψ·∇^M|A|),
 using the product rule at the H^m-a.e. points where |A| and ψ are both differentiable within M ((0g)). All integrands are bounded with support in a compact subset of M (finite measure); r^{-2} is bounded there.
 (4b) H^m-a.e. on M, |A|∇^M|A| = ∇^M(½|A|²): where |A| > 0 by the chain rule; where |A| = 0 (and |A| is differentiable within M) both sides vanish ((0g); ½|A|² is smooth along M with a minimum there). Hence 2ψ|A|∇^Mψ·∇^M|A| = ∇^M(ψ²)·∇^M(½|A|²) a.e.
 (4c) Integration by parts: with f := ½|A|², ∫_M (∇^M(ψ²)·∇^Mf + ψ²Δ_Mf) dH^m = 0. Indeed, ψ² is locally Lipschitz on M and vanishes on M outside a compact set, so lipschitz_approx gives a compact C'' ⊆ M and C^∞ functions χ_k with χ_k = 0 on M ∖ C'', χ_k → ψ² uniformly on M and ∫⁻_M |Dχ_k − d^M(ψ²)|²_{T_x} dH^m → 0. Cover the compact set C'' by finitely many chart cylinders O_l := {z ∈ W_l : π_l(z − p_l) ∈ D_l} ⊆ O ∩ U₀ of C^∞ graph charts G_l : D_l → M ∩ W_l (as in (0f), with inverse π_l(· − p_l)), choose β_l ∈ C^∞_c(O_l) with Σ_lβ_l = 1 on a neighbourhood of C'', and let V_l(z) := ∇^Mf(G_l(π_l(z − p_l))) for z ∈ O_l (C^∞ on O_l, equal to ∇^Mf on M ∩ O_l). Then X_k := χ_k·Σ_lβ_lV_l (each term 0 off O_l) is C^∞ with compact support, 0 ∉ tsupport X_k, and X_k = χ_k∇^Mf on M (near C'' because Σ_lβ_l = 1, and both sides vanish on M ∖ C''). Along M, DX_k(x)τ_i = (Dχ_k(x)τ_i)∇^Mf(x) + χ_k(x)D_{τ_i}(∇^Mf), so div_M X_k = Dχ_k(x)(∇^Mf(x)) + χ_kΔ_Mf. Stationarity gives ∫_M (Dχ_k(∇^Mf) + χ_kΔ_Mf) dH^m = 0. As k → ∞, Dχ_k(x)(∇^Mf(x)) → d^M_x(ψ²)(∇^Mf(x)) in L¹(H^m⌞M) (|Dχ_k(∇^Mf) − d^M(ψ²)(∇^Mf)| ≤ |Dχ_k − d^M(ψ²)|_{T_x}|∇^Mf|, ∇^Mf is bounded on C'' ∪ spt ψ, and these sets have finite measure), and χ_kΔ_Mf → ψ²Δ_Mf uniformly with supports in a fixed compact set. Hence the claim.
 (4d) By (4b), (4c) and (1) (multiplied by ψ² ≥ 0 and integrated),
 2∫_M ψ|A|∇^Mψ·∇^M|A| = ∫_M ∇^M(ψ²)·∇^M(½|A|²) = −∫_M ψ²Δ_M(½|A|²) ≤ ∫_M ψ²(|A|⁴ − 2r^{-2}|A|² − |∇^M|A||²).
 Inserting this into (2) and cancelling the finite quantities ∫ψ²|A|⁴ and ∫ψ²|∇^M|A||² gives (3).

5. (Extension of (3); printed text after (3).) (3) holds for every ψ locally Lipschitz on M such that r^{-2}ψ²|A|² and |A|²|∇^Mψ|² are integrable on M (with respect to H^m), in particular
 (4) ∫_M r^{-2}ψ²|A|² dH^m < ∞.
 (The printed text assumes only (4); if ∫_M |A|²|∇^Mψ|² dH^m = ∞ the inequality is trivial for integrals in [0, ∞], and step 6 checks both integrability conditions for the ψ used.) For 0 < κ < 1 let γ_κ(x) := g_κ(|x|), where g_κ is continuous and piecewise linear: 0 on [0, κ/2], 1 on [κ, κ^{-1}], 0 on [2κ^{-1}, ∞), linear on [κ/2, κ] and on [κ^{-1}, 2κ^{-1}]. Then 0 ≤ γ_κ ≤ 1, and at every x ∈ M with |x| ∉ {κ/2, κ, κ^{-1}, 2κ^{-1}} (an H^m-null exceptional set by (0e)(iii)), γ_κ is smooth near x and |∇^Mγ_κ(x)| ≤ |g_κ'(|x|)| ≤ 3|x|^{-1}·1_{E_κ}(x), where E_κ := {κ/2 < r < κ} ∪ {κ^{-1} < r < 2κ^{-1}} (|g_κ'| = 2/κ < 2/r on the inner annulus and κ < 2/r on the outer one). ψγ_κ is locally Lipschitz on M and vanishes on M outside the compact set M ∩ {κ/2 ≤ r ≤ 2κ^{-1}} ((0a)). Apply (3) to ψγ_κ and use |∇^M(ψγ_κ)|² ≤ (1 + η)|∇^Mψ|²γ_κ² + (1 + η^{-1})ψ²|∇^Mγ_κ|² (a.e., η > 0):
 2∫_M r^{-2}ψ²γ_κ²|A|² ≤ (1 + η)∫_M |A|²|∇^Mψ|² + 9(1 + η^{-1})∫_{M∩E_κ} r^{-2}ψ²|A|².
 Let κ = κ_j ↓ 0. On M, γ_{κ_j} → 1 and 1_{E_{κ_j}} → 0 pointwise (0 < |x| < ∞), and r^{-2}ψ²|A|² is integrable by (4); dominated convergence gives 2∫_M r^{-2}ψ²|A|² ≤ (1 + η)∫_M |A|²|∇^Mψ|². Let η ↓ 0.

6. (Choice of ψ; printed (6).) Let ε := 1/10 (the witness used in SimonGMT AppendixB.exists_final_exponent); for 2 ≤ m ≤ 6, m/2 − 2 + ε ∈ {−0.9, −0.4, 0.1, 0.6, 1.1}, so (m/2 − 2 + ε)² ≤ 1.21 < 2, and (1 + ε)² = 1.21 < 2. Put ψ := r^{1+ε}r₁^{1−m/2−2ε} with r₁ := max{1, r}; so ψ = r^{1+ε} on {r ≤ 1} and ψ = r^{2−m/2−ε} on {r ≥ 1}. ψ is continuous on U₀, smooth on U₀ ∩ {r ≠ 1}, and locally Lipschitz on U₀ (bounded one-sided derivatives near r = 1), hence locally Lipschitz on M. On M, r^{-2}ψ² = r^{2ε} on {r < 1} and r^{2−m−2ε} on {r > 1}; by (0b), at x ∈ M with |x| ≠ 1, |∇^Mψ(x)| = (1 + ε)r^ε on {r < 1} and |m/2 − 2 + ε|r^{1−m/2−ε} on {r > 1}; M ∩ {r = 1} is H^m-null ((0e)(iii)).
 Finiteness (replacing the use of (5)). Put I₁ := ∫_{M∩{r<1}} |A|²r^{2ε} dH^m and I₂ := ∫_{M∩{r>1}} |A|²r^{2−m−2ε} dH^m. By (0f), |A|² ≤ c_Σr^{-2} on M; with (0e)(ii):
 I₁ ≤ Σ_{k≥1} c_Σ·2^{k(2−2ε)}·H^m(M ∩ {2^{-k} ≤ r < 2^{1−k}}) = c_Σa₀Σ_{k≥1}2^{−k(m−2+2ε)} < ∞ (m − 2 + 2ε > 0),
 I₂ ≤ Σ_{k≥0} c_Σ·2^{−k(m+2ε)}·H^m(M ∩ {2^k ≤ r < 2^{k+1}}) = c_Σa₀Σ_{k≥0}2^{−2kε} < ∞,
 using r^{2ε−2} ≤ 2^{k(2−2ε)} on {r ≥ 2^{-k}} and r^{−m−2ε} ≤ 2^{−k(m+2ε)} on {r ≥ 2^k}. So ∫_M r^{-2}ψ²|A|² = I₁ + I₂ < ∞, i.e. (4) holds, and ∫_M |A|²|∇^Mψ|² = (1 + ε)²I₁ + (m/2 − 2 + ε)²I₂ < ∞.
 By step 5, (6): 2I₁ + 2I₂ ≤ (1 + ε)²I₁ + (m/2 − 2 + ε)²I₂, i.e. (2 − (1 + ε)²)I₁ + (2 − (m/2 − 2 + ε)²)I₂ ≤ 0. Both coefficients are positive and I₁, I₂ ∈ [0, ∞), so I₁ = I₂ = 0.

7. (Conclusion.) I₁ = I₂ = 0 gives |A|² = 0 H^m-a.e. on M ∩ {r ≠ 1}, hence H^m-a.e. on M ((0e)(iii)). |A|² is continuous on M; if |A|²(x₀) > 0 for some x₀ ∈ M, then |A|² > 0 on a nonempty relatively open subset of M, which has positive H^m-measure ((0e)(iv)) — a contradiction. So |A|² ≡ 0 on M, i.e. Σ_i|D_{τ_i}ν|² = 0 at every x ∈ M ((0c)), and Dν(x)v = 0 for every v ∈ T_x = tangentSpace M x. ∎

## Key steps

1. Cone/closure/tangent facts; ν(tx) = ν(x), hence h_ij(tx) = t^{-1}h_ij(x), D_xν = 0 and |A|² ≤ c_Σ r^{-2}; dyadic scaling of H^m and H^m(M ∩ {r = c}) = 0.
2. Simons' identity B.8 from Codazzi, Gauss and the Ricci identity; with H = 0, ½Δ_M|A|² = Σh²_{ij;k} − |A|⁴.
3. Lemma B.11 in a radial frame (SimonGMT cone_simonsDefect_lower_bound) gives (1): ½Δ_M|A|² + |A|⁴ ≥ 2r^{-2}|A|² + |∇^M|A||² H^m-a.e.
4. B.1 with ζ = |A|ψ and integration by parts (lipschitz_approx and stationarity) give (3): 2∫r^{-2}ψ²|A|² ≤ ∫|A|²|∇^Mψ|² for compactly supported ψ.
5. Cut-offs γ_κ extend (3) to locally Lipschitz ψ with ∫r^{-2}ψ²|A|² < ∞.
6. ψ = r^{1+ε}r₁^{1−m/2−2ε}, ε = 1/10: the integrals are finite by dyadic scaling, and (1+ε)² < 2, (m/2−2+ε)² < 2 force |A| = 0 a.e., hence everywhere by continuity and positivity of H^m on open pieces.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; sha256sum local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `sed -n 1,457p GMT/Ch07/Contract.lean (IsEmbeddedSubmanifold, tangentSpace, IsOrientation, IsUnitOrientationOf, MultiVector, tangentialDivergence, unitBallVolume)`
- `python3 scans of dag.json: selected node, parent simons_regular_cone and its decomposition-v1.json; nodes whose types mention IsEmbeddedSubmanifold or tangentSpace with statuses and candidate commits; keyword scan Allard|Schauder|second fundamental|Simons|stability|first variation|area formula`
- `grep -n 'theorem|def' simongmt/Poincare/SimonGMT/AppendixB/{SimonsInequalities,ConeDefect,LagrangeIdentity}.lean and Chapter02/{SecondFundamentalForm,SecondFundamentalFormCalculus,SubmanifoldCalculus,AreaFormula,Area}.lean`
- `grep -rn 'measurable_fderiv|LipschitzWith.ae_differentiableAt|ae_differentiableWithinAt_of_mem|hausdorffMeasure_image_le|image_of_continuousOn_injOn|hasDerivAt_integral_of_dominated_loc_of_deriv_le|exists_isSubordinate|contDiffOn_infty|HasFDerivWithinAt.unique_on|normDet' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `runtime.py of flow gmt-claude-252c8df06c56: _existing_lean_name_problem, _solve_children, _install_parent_supplied_child_handoff, _accepted_checkpoint; store.py ensure`
- `git for-each-ref (1709 distinct objects) | xargs git grep -l codim1_hcp -- 'GMT/*.lean' (no match); grep -c codim1_hcp dag.json (0); grep -rn codim1_hcp simongmt (no match)`
- `lean -DautoImplicit=false /tmp/hcp-split/check/{Types,TypesAll,Assembly,Inst}.lean (LEAN_PATH = .lake/build/lib/lean plus every package's .lake/build/lib/lean)`
- `book: chapter-B.txt 1-282; chapter-02.txt 854-1410; chapter-05.txt 1280-1397; chapter-03.txt 290-330; grep 'B.2 Theorem|B.8 Lemma|B.11 Lemma|Proof of B.2' sources/chapter-07-source.txt`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-b5d5990773/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-7577af74dd/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-chart-tangent-space-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-regular-point-density-a1-density-one-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-regular-point-density-a1-locally-closed-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/AppendixB/SimonsInequalities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/AppendixB/ConeDefect.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/AppendixB/LagrangeIdentity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaFormula.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SecondFundamentalForm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/runtime/flows/gmt-claude-252c8df06c56/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-252c8df06c56/_recursive_lean/store.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-B.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/hcp-split/check/TypesAll.lean`
- `/tmp/hcp-split/check/Assembly.lean`
- `/tmp/hcp-split/check/Inst.lean`

Pins match. The snapshot manifest records project b4d606db and Mathlib 25730c7c, equal to workspace HEAD and .lake/packages/mathlib (simongmt 2b366308). The snapshot Contract.lean, workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).
Library. SimonGMT supplies injective_area_formula_of_injective_derivative (Chapter02/AreaFormula.lean:145), the Appendix B algebra simonsDefect_eq_sum_skew (LagrangeIdentity.lean:122), four_mul_radialSkewSum_le, radial_derivative_of_codazzi, cone_simonsDefect_lower_bound (ConeDefect.lean:136–228) and exists_final_exponent (witness 1/10). It has no submanifold curvature calculus, Simons identity or Allard theorem; these remain book citations inside unit_normal, stability, simons_cone and smooth_regularity. The snapshot Mathlib has measurable_fderiv (FDeriv/Measurable.lean:378), LipschitzWith.ae_differentiableAt and LipschitzOnWith.ae_differentiableWithinAt_of_mem (Calculus/Rademacher.lean), LipschitzOnWith.hausdorffMeasure_image_le (Hausdorff.lean:733), MeasurableSet.image_of_continuousOn_injOn, hasDerivAt_integral_of_dominated_loc_of_deriv_le, SmoothPartitionOfUnity.exists_isSubordinate, contDiffOn_infty and HasFDerivWithinAt.unique_on. LinearMap.normDet exists (InnerProductSpace/NormDet.lean) but is outside Submission's import closure, so Jacobians are stated as √det(L*∘L).
DAG. chart_tangentSpace_eq_range_fderiv, dimred_rpd_submanifold_density_one and dimred_rpd_embedded_locally_closed are accepted with candidate commits (d626082a69a0, e8842d90b78f, 6da66b1edf6f) and are reused with byte-identical types; the runtime reuses accepted nodes by identical name and type and leaves their handoffs untouched. The Allard nodes dor_allard_bounded_curvature_graph and codim1_ldr_allard_bounded_curvature_graph are unaccepted and cannot be reused. The stationarity integrand has the same form as idtp_ccd_sheet_first_variation. The 9 new codim1_hcp_ names are free in dag.json, GMT/, SimonGMT and all ref trees.
Lean. All 12 child types elaborate after import GMT.Ch07.Submission in the contract namespace and opens (TypesAll.lean, exit 0). The selected frozen type is kernel-checked from the child types as axioms (Assembly.lean, exit 0; axioms: propext, Classical.choice, Quot.sound and six children). Inline instances verified by rfl (Inst.lean): the inner product on span(tangentSpace M x) is Submodule.innerProductSpace and starProjection = subtypeL ∘ orthogonalProjection; ContDiff ℝ (⊤ : ℕ∞) elaborates to ↑⊤ (C^∞, not analytic).


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
