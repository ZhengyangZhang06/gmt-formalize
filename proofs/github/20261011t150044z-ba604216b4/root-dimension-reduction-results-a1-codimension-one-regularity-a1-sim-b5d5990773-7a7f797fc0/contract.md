<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1 -->

## Theorem `Submission.codim1_deformation_minimal_hypercone_is_plane`

Simons' theorem for deformation-minimal C¹ hypercones. Data: P, m ∈ ℕ with 2 ≤ m ≤ 6; a linear subspace A₀ ⊆ ℝ^P with dim A₀ = m + 1; M ⊆ ℝ^P. Hypotheses: M ≠ ∅, M ⊆ A₀ and 0 ∉ M; M is an embedded C¹ m-submanifold of ℝ^P; closure(M) ⊆ M ∪ {0}; tx ∈ M for every x ∈ M and t > 0; M has an orientation ξ (IsOrientation m M ξ for some ξ); H^m(M ∩ K) < ∞ for every compact K; and for every C^∞ map Z : ℝ^P → ℝ^P with compact support and 0 ∉ tsupport Z there is t₀ > 0 with H^m(M ∩ tsupport Z) ≤ H^m({x + tZ(x) : x ∈ M ∩ tsupport Z}) for every t with |t| < t₀. Conclusion: there is a linear subspace H₀ ⊆ ℝ^P with dim H₀ = m and M = H₀ ∖ {0}. H^m = μHE[m].

Node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4352

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/984, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4203

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/984, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4210, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4182, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5987, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5989, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5993, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5997, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6001, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6004, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6008, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6016, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6025

## Lean problem

Declaration: `Submission.codim1_deformation_minimal_hypercone_is_plane`

```lean
∀ (P m : ℕ) (A₀ : Submodule ℝ (Euclid P)) (M : Set (Euclid P)), 2 ≤ m → m ≤ 6 → Module.finrank ℝ A₀ = m + 1 → M.Nonempty → M ⊆ (A₀ : Set (Euclid P)) → (0 : Euclid P) ∉ M → IsEmbeddedSubmanifold 1 m M → closure M ⊆ insert 0 M → (∀ t : ℝ, 0 < t → ∀ x ∈ M, t • x ∈ M) → (∃ ξ : Euclid P → MultiVector P m, IsOrientation m M ξ) → (∀ K : Set (Euclid P), IsCompact K → μHE[m] (M ∩ K) ≠ ∞) → (∀ Z : Euclid P → Euclid P, ContDiff ℝ (⊤ : ℕ∞) Z → HasCompactSupport Z → (0 : Euclid P) ∉ tsupport Z → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, |t| < t₀ → μHE[m] (M ∩ tsupport Z) ≤ μHE[m] ((fun x => x + t • Z x) '' (M ∩ tsupport Z))) → ∃ H₀ : Submodule ℝ (Euclid P), Module.finrank ℝ H₀ = m ∧ M = (H₀ : Set (Euclid P)) \ {0}
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

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Parent steps B5e (first variation), B6 (smoothness), B7 (stability B.1), B8 (Simons' theorem B.2, printed proof) and B9 (hyperplane) of the supplied proof of codim1_simons_regular_cone_density. Book:
- Simon Appendix B: B.1, B.2 and its printed proof, B.4–B.11 (chapter-B.txt lines 13–282 = chapter-07-source.txt lines 1256–1539);
- Ch. 2, §4: 4.1, 4.23–4.30 (chapter-02.txt lines 854–1160);
- Ch. 2, §5: 5.1–5.12 (chapter-02.txt lines 1162–1405);
- Ch. 5, Theorem 7.1 (chapter-05.txt lines 1306–1360);
- Ch. 3, 1.8(2) (chapter-03.txt lines 298–316).
Departures from the parent text, stated explicitly.
(i) The hypothesis (AC) below is the conclusion of the parent's B5d with the compact set K_Z := tsupport Z in place of the open set W ⊇ K_Z. This is equivalent, because Φ_t = id off K_Z.
(ii) The parent identified A₀ with ℝ^{m+1}; here everything is done inside A₀ ⊆ ℝ^P. The unit normal of M in A₀ is built from the given orientation ξ (step 3), which is exactly how B7a uses "the orientation induced from C".
(iii) The printed proof uses ε both for the cut-off parameter and for the exponent; the cut-off parameter is called κ here (as in the parent).

Sibling subproblems used.
- chart_tangent_space (Submission.chart_tangentSpace_eq_range_fderiv): for a chart (V, W, ψ) of an embedded C^r submanifold N (r ≥ 1), tangentSpace N (ψ v) = range Dψ(v).
- bilipschitz_measure (Submission.dimred_rpd_bilipschitz_image_measure): if c₁|a − b| ≤ |χ(a) − χ(b)| ≤ c₂|a − b| on E ⊆ ℝ^n (c₁ > 0, c₂ ≥ 0), then c₁ⁿLⁿ(E) ≤ Hⁿ(χ(E)) ≤ c₂ⁿLⁿ(E).

Hypotheses and notation.
- P, m with 2 ≤ m ≤ 6; A₀ ⊆ ℝ^P a linear subspace with dim A₀ = m + 1; M ⊆ A₀ nonempty with 0 ∉ M.
- M is an embedded C¹ m-submanifold, closure(M) ⊆ M ∪ {0}, and tx ∈ M for x ∈ M, t > 0.
- ξ is an orientation of M.
- (LF) H^m(M ∩ K) < ∞ for every compact K.
- (AC) For every C^∞ map Z : ℝ^P → ℝ^P with compact support and 0 ∉ K_Z := tsupport Z there is t₀(Z) > 0 with H^m(M ∩ K_Z) ≤ H^m(Φ_t^Z(M ∩ K_Z)) for |t| < t₀(Z), where Φ_t^Z(x) := x + tZ(x).
- H^m := μHE[m], ω_m := unitBallVolume m, r(x) := |x|, U₀ := ℝ^P ∖ {0}, B_s(x) := ball x s.

Facts on embedded C¹ m-submanifolds N (proofs as indicated).
(F1) For a chart (V, W, ψ) of N, W ∩ N is closed in W and ψ⁻¹ : W ∩ N → V is continuous. If ψ(v_j) → z ∈ W, the compact set {z} ∪ {ψ(v_j)} ⊆ W has compact preimage in V; a subsequence v_j → v with ψ(v) = z, and injectivity gives continuity of ψ⁻¹. Consequently N is Borel: countably many such W cover N.
(F2) For x ∈ N, T_xN := tangentSpace(N, x) = range Dψ(ψ⁻¹(x)) for any chart (chart_tangent_space). It is an m-dimensional linear subspace, and the same holds for N ∩ O, O open, with the same tangent spaces (restrict the chart to V ∩ ψ⁻¹(O)).
(F3) H^m(N ∩ B_s(x)) > 0 for x ∈ N, s > 0. Near v₀ := ψ⁻¹(x), ψ is bi-Lipschitz on a small ball mapped into B_s(x) (mean value inequality and injectivity of Dψ(v₀)); apply bilipschitz_measure.
(F4) H^m(N ∩ B_s(x))/(ω_m s^m) → 1 as s ↓ 0 (Simon Ch. 3, 1.8(2)). Near x, N is the graph {x + a + u(a)} over T_xN (identified isometrically with ℝ^m) of a C¹ map u with u(0) = 0, Du(0) = 0. This follows from the inverse function theorem applied to the projection onto T_xN of ψ − x, and (F1). With L(s) := sup_{|a|≤s}‖Du(a)‖ → 0, the graph map g is bi-Lipschitz on B_s(0) with constants 1 and 1 + L(s). Also N ∩ B_s(x) = g(E_s) with B_{s/√(1+L(s)²)}(0) ⊆ E_s ⊆ B_s(0). bilipschitz_measure gives (1 + L(s)²)^{−m/2} ≤ H^m(N ∩ B_s(x))/(ω_m s^m) ≤ (1 + L(s))^m.

Proof.
0. (Preliminaries.)
 (0a) Cone and closure. Applying the cone hypothesis with t and t⁻¹ gives tM = M for t > 0. For x ∈ M, tx → 0 as t ↓ 0, so 0 ∈ closure(M); with closure(M) ⊆ M ∪ {0} and 0 ∉ M, closure(M) ∖ M = {0}. Hence M is relatively closed in U₀ and Borel (F1).
 (0b) Tangent spaces. For x ∈ M, T_xM is m-dimensional (F2), and T_xM ⊆ A₀: a C¹ curve in M ⊆ A₀ has its derivative in the closed subspace A₀. Also x ∈ T_xM: s ↦ e^s x is a C¹ curve in M with derivative x at 0. Hence the radial unit vector x/|x| is tangent and |∇^M r| = 1 on M.
 (0c) Area formula for the variations (Simon Ch. 2, 5.1–5.2). Let Z be as in (AC) and Λ := sup‖DZ‖. For |t| < 1/(1 + Λ), Φ_t := Φ_t^Z is a C^∞ diffeomorphism of ℝ^P: DΦ_t = I + tDZ is invertible, |Φ_t(a) − Φ_t(b)| ≥ (1 − |t|Λ)|a − b|, and Φ_t is onto by the contraction argument. Φ_t = id off K_Z and Φ_t(K_Z) = K_Z. By the area formula for the injective C¹ map Φ_t on M,
 f_Z(t) := H^m(Φ_t(M ∩ K_Z)) = ∫_{M∩K_Z} J_t dH^m,
 where J_t(x) := √det G_t(x), G_t(x)_{ij} := (τ_i + tDZ(x)τ_i)·(τ_j + tDZ(x)τ_j), and τ is an orthonormal basis of T_xM.
1. (First variation and stationarity; parent B5e.) Let Z be as in (AC).
 - det G_t(x) is a polynomial in t whose coefficients are bounded on M ∩ K_Z by constants depending only on m and Λ, and G_0 = I. So there is t₁ ∈ (0, 1/(1 + Λ)) with det G_t ≥ 1/2 for |t| ≤ t₁. For such t, Φ_t is a diffeomorphism and the area-formula expression (0c) for f_Z(t) is valid.
 - Hence J_t is C^∞ in t, with |∂_t^k J_t(x)| ≤ C_k for x ∈ M ∩ K_Z and |t| ≤ t₁.
 - Since H^m(M ∩ K_Z) < ∞ by (LF), f_Z is C^∞ on (−t₁, t₁) and may be differentiated under the integral. ∂_tJ_t|_{t=0} = Σ_i τ_i·DZ(x)τ_i = div_M Z(x) (Simon 5.2–5.3).
 - By (AC), f_Z(t) ≥ f_Z(0) for |t| < min{t₀(Z), t₁}, so f_Z has a local minimum at 0: f_Z'(0) = 0 and f_Z''(0) ≥ 0.
 - DZ = 0 on the open set ℝ^P ∖ K_Z, so div_M Z = 0 on M ∖ K_Z. Therefore
 (1.1) ∫_M div_M Z dH^m = 0.
 Now let X ∈ C¹_c(U₀; ℝ^P) and X_k := X * ϕ_{1/k} (standard mollifier). For large k, X_k is C^∞ with support in a fixed compact K' ⊆ U₀, and DX_k → DX uniformly. As H^m(M ∩ K') < ∞ and |div_M Y| ≤ m‖DY‖, (1.1) passes to the limit:
 (1.2) ∫_M div_M X dH^m = 0 for every X ∈ C¹_c(U₀; ℝ^P).
 So V := v(M, 1) is stationary in U₀ (Simon Ch. 2, 5.3 and the definition after 5.4; Ch. 4, 2.6).
2. (Smoothness and zero mean curvature; parent B6.) V = v(M, 1) is a rectifiable m-varifold in U₀ with multiplicity θ ≡ 1, stationary in U₀ by (1.2), so its generalized mean curvature is 0 ∈ L^p for every p. Θ^m(V, y) = 1 at every y ∈ M by (F4). Moreover spt V ∩ U₀ = M: points of M have positive density, and M is relatively closed in U₀.
 By Simon Ch. 5, Theorem 7.1, last part (with N := ℝ^P, which is C^∞, so q is arbitrary), for every y ∈ M and every q there are σ > 0 and a rigid motion after which M ∩ B_σ(y) is the graph of a C^{q+2,α} function. Hence M is a C^∞ embedded submanifold of U₀.
 For C² submanifolds the first variation formula ∫_M div_M X dH^m = −∫_M X·H_M dH^m holds for X ∈ C¹_c(U₀; ℝ^P) (Simon Ch. 2, 4.29–4.30, 5.5(2)). With (1.2) and continuity of H_M, the mean curvature vector H_M vanishes identically.
3. (Unit normal and second fundamental form; parent B7a.)
 - Let a_0, …, a_m be an orthonormal basis of A₀ and Ω(v_0, …, v_m) := det(a_i·v_j)_{i,j=0..m}, an alternating (m+1)-form on ℝ^P. For v ∈ ℝ^P let ι_vΩ be the m-covector (w_1, …, w_m) ↦ Ω(w_1, …, w_m, v).
 - For x ∈ M write ξ(x)(β) = ε_x·β(τ_1, …, τ_m) with τ an orthonormal basis of T_xM and ε_x = ±1. The functional ℓ_x(v) := ξ(x)(ι_vΩ) = ε_x·Ω(τ_1, …, τ_m, v) is linear in v and depends only on ξ(x).
 - ℓ_x vanishes on T_xM, since the m + 1 arguments are then dependent. For a unit vector n ∈ N_x := A₀ ∩ (T_xM)^⊥ (a line, by (0b)), (τ_1, …, τ_m, n) is an orthonormal basis of A₀, so ℓ_x(n) = ±1.
 - Let ν(x) ∈ A₀ be the vector with ν(x)·v = ℓ_x(v) for v ∈ A₀. Then ν(x) ∈ N_x and |ν(x)| = 1.
 - ν is continuous on M, because ξ is continuous and v ↦ ι_vΩ is linear.
 - ν is C^∞: on a smooth chart ψ of M (step 2), n_ψ := the A₀-Riesz representative of v ↦ Ω(∂_1ψ, …, ∂_mψ, v) is smooth and nonzero, ν = ±n_ψ/|n_ψ|, and the sign is locally constant by continuity.
 - For x ∈ M, τ ∈ T_xM: D_τν ⊥ ν (|ν| ≡ 1) and D_τν ∈ A₀, so D_τν ∈ T_xM.
 - The second fundamental form of M (Simon 4.23–4.24) is B_x(τ_i, τ_j) = h_{ij}ν(x) with h_{ij} := −(D_{τ_i}ν)·τ_j = h_{ji}. The normal directions (A₀)^⊥ are constant along M ⊆ A₀ and contribute nothing. Put |A|² := Σ_{i,j} h_{ij}² = Σ_i |D_{τ_i}ν|².
 - |A| is smooth where positive and locally Lipschitz on M.
 - Homogeneity: ν(λx) = ν(x) for λ > 0 (the tangent spaces of the cone are dilation invariant and ν is continuous along rays), so h_{ij}(λx) = λ⁻¹h_{ij}(x) and |A(x)|² = r^{−2}|A(x/|x|)|².
4. (Stability inequality B.1; parent B7b–B7e; Simon 5.4, 5.11, 5.12.) Let ζ ∈ C^∞_c(M) with support K_ζ ⊆ M compact.
 (4a) The variation field. There is a C^∞ map Z : ℝ^P → ℝ^P with compact support, Z(w) ∈ A₀ for all w, 0 ∉ tsupport Z, and Z = ζν on M.
 - Each p ∈ K_ζ has an open O_p ⊆ U₀ such that M ∩ O_p is a single smooth graph sheet. On O_p there is a smooth Y_p with Y_p = ζν on M ∩ O_p (extend ζν constantly along the normal coordinates of the graph).
 - Finitely many O_{p_k} cover K_ζ. Let φ_k be smooth, compactly supported in O_{p_k}, with Σ_kφ_k = 1 near K_ζ.
 - Put Z := P_{A₀}(Σ_kφ_kY_{p_k}), with P_{A₀} the orthogonal projection onto A₀.
 - On M ∩ O_{p_k}, Y_{p_k} = ζν, so on M, Z = (Σ_kφ_k)·ζν. This equals ζν near K_ζ, and 0 = ζν on M away from K_ζ. Also P_{A₀}ν = ν.
 (4b) Second variation. Let f(t) := H^m(Φ_t^Z(M ∩ K_Z)). By step 1 (applied to this Z), f is C^∞ on (−t₁, t₁), and f(t) ≥ f(0) for |t| < min{t₀(Z), t₁}, so f''(0) ≥ 0. The variation Φ_t^Z = id + tZ has initial velocity Z and acceleration 0. M is C² and stationary in U₀, (closure(M) ∖ M) ∩ U₀ = ∅, and Z|_M = ζν is normal to M. So Lemma 5.11 (from the second variation formula 5.4) gives
 f''(0) = ∫_M (Σ_i |(D_{τ_i}Z)^⊥|² − Σ_{i,j}(Z·B(τ_i, τ_j))²) dH^m.
 - (D_{τ_i}(ζν))^⊥ = (∇_{τ_i}ζ)ν, because D_{τ_i}ν ∈ T_xM (step 3).
 - Z·B(τ_i, τ_j) = ζh_{ij}.
 Hence (Simon 5.12 (‡)) f''(0) = ∫_M (|∇^Mζ|² − |A|²ζ²) dH^m ≥ 0.
 (4c) B.1 holds for every locally Lipschitz ζ with compact support in M. Mollify in finitely many charts (partition of unity) to get ζ_k ∈ C^∞_c(M) with supports in a fixed compact K' ⊆ M, ζ_k → ζ uniformly and ∇^Mζ_k → ∇^Mζ in L²(H^m⌞K'). Here H^m(K') < ∞ and |A| is bounded on K'.
5. (Simons' inequality; Simon B.4–B.11 and (1) of the proof of B.2.) Work in a local orthonormal frame τ_1, …, τ_m of TM, with covariant derivatives h_{ij;k}.
 (5a) Simons' identity B.8 holds:
 ½Δ_M|A|² = Σ_{i,j,k} h²_{ij;k} − |A|⁴ + h_{ij}H_{;ij} + H h_{mi}h_{mj}h_{ij}, with H = h_{kk}.
 Ingredients: h_{ij} = h_{ji} (B.4); Codazzi h_{ij;k} = h_{ik;j} (B.5, the ambient curvature is 0); Gauss R_{ijkl} = h_{il}h_{jk} − h_{ik}h_{jl} (B.6); the commutation formula B.7. Printed proof:
 - h_{ij;kk} = h_{ik;jk} = h_{ki;jk} = h_{ki;kj} + h_{km}(h_{mj}h_{ik} − h_{mk}h_{ij}) − h_{mi}(h_{kj}h_{mk} − h_{kk}h_{mj}) = h_{kk;ij} − Σ_{m,k}h_{mk}²·h_{ij} + h_{kk}h_{mi}h_{mj};
 - multiply by h_{ij} and use ½Δ Σ h_{ij}² = Σ h_{ij}h_{ij;kk} + Σ h_{ij;k}².
 With H ≡ 0 (step 2): ½Δ_M|A|² = Σ h²_{ij;k} − |A|⁴.
 (5b) Lemma B.11 (cone): where |A| > 0, D := Σ_{i,j,k} h²_{ij;k} − Σ_k |A|^{−2}(Σ_{i,j}h_{ij}h_{ij;k})² ≥ 2r^{−2}|A|². Printed proof:
 - At x ∈ M choose the frame with τ_m = x/|x| radial and τ_1, …, τ_{m−1} constant along the ray ℓ_x (possible by (0b) and homogeneity).
 - Then (1) h_{mj} = h_{jm} = 0 on ℓ_x, since ν is constant along rays, and (2) h_{ij;m} = −r^{−1}h_{ij} on ℓ_x, by h_{ij}(λx) = λ⁻¹h_{ij}(x).
 - The algebra: D = ½Σ_k |A|^{−2}Σ_{i,j,r,s}(h_{rs}h_{ij;k} − h_{ij}h_{rs;k})² ≥ 2|A|^{−2}Σ_kΣ_{i,j,r<m}(h_{ij}h_{rm;k})², by the four placements of one radial index. Codazzi and (2) give h_{rm;k} = h_{rk;m} = −r^{−1}h_{rk}. Hence D ≥ 2r^{−2}|A|^{−2}Σ_{i,j,r,k}h_{ij}²h_{rk}² = 2r^{−2}|A|² by (1).
 - This finite-dimensional algebra is kernel-checked in SimonGMT: AppendixB.simonsDefect_eq_sum_skew, four_mul_radialSkewSum_le, cone_simonsDefect_lower_bound.
 Since |∇^M|A||² = Σ_k |A|^{−2}(Σ_{ij}h_{ij}h_{ij;k})² where |A| > 0, (5a) and (5b) give there
 (1) ½Δ_M|A|² + |A|⁴ ≥ 2r^{−2}|A|² + |∇_M|A||².
 Where |A| = 0: ∇_M|A| = 0 H^m-a.e. (|A| is locally Lipschitz, and its gradient vanishes a.e. on a level set), and ½Δ_M|A|² = Σh²_{ij;k} ≥ 0. So (1) holds H^m-a.e. on M.
6. (Inequality (3); printed proof of B.2.) Let ψ be locally Lipschitz with compact support in M. Apply B.1 (step 4c) to ζ := |A|ψ:
 (2) ∫_M |A|⁴ψ² ≤ ∫_M |∇(|A|ψ)|² = ∫_M (|∇ψ|²|A|² + ψ²|∇|A||² + 2ψ|A|∇ψ·∇|A|).
 Integration by parts on M is valid: ψ² is compactly supported Lipschitz, |A|² is smooth, and ∫_M div_M Y dH^m = 0 for compactly supported Lipschitz tangential Y, by (1.2) and approximation. With (1) it gives
 2∫ψ|A|∇ψ·∇|A| = ∫∇(ψ²)·∇(½|A|²) = −∫ψ²Δ_M(½|A|²) ≤ ∫ψ²(|A|⁴ − 2r^{−2}|A|² − |∇|A||²).
 Inserting this into (2):
 (3) 2∫_M r^{−2}ψ²|A|² dH^m ≤ ∫_M |A|²|∇_Mψ|² dH^m.
7. (Extension of (3); printed text after (3).) (3) holds for every locally Lipschitz ψ on M with
 (4) ∫_M r^{−2}ψ²|A|² dH^m < ∞.
 If the right side of (3) is infinite there is nothing to prove; assume it is finite.
 - For 0 < κ < 1 let γ_κ be Lipschitz on ℝ^P with 0 ≤ γ_κ ≤ 1, γ_κ = 1 on {κ ≤ r ≤ κ⁻¹}, γ_κ = 0 on {r ≤ κ/2} ∪ {r ≥ 2κ⁻¹}, linear in r on the two transition annuli, so |∇γ_κ| ≤ 3/r.
 - ψγ_κ has compact support in M: its support lies in M ∩ {κ/2 ≤ r ≤ 2κ⁻¹}, which is compact because closure(M) ∖ M = {0}.
 - Apply (3) to ψγ_κ, with |∇(ψγ_κ)|² ≤ (1 + η)|∇ψ|²γ_κ² + (1 + η⁻¹)ψ²|∇γ_κ|² (η > 0) and |∇γ_κ|² ≤ 9r^{−2}1_{E_κ}, E_κ := {κ/2 < r < κ} ∪ {κ⁻¹ < r < 2κ⁻¹}:
 2∫ r^{−2}ψ²γ_κ²|A|² ≤ (1 + η)∫|A|²|∇ψ|² + 9(1 + η⁻¹)∫_{E_κ} r^{−2}ψ²|A|².
 - As κ ↓ 0, the left side tends to 2∫r^{−2}ψ²|A|² by dominated convergence (dominant r^{−2}ψ²|A|², integrable by (4)). The last term tends to 0 by dominated convergence, since 1_{E_κ} → 0 pointwise on M.
 - Then let η ↓ 0.
8. (Cone integrals; printed (5).) Σ := M ∩ ∂B_1(0) is a compact C^∞ (m−1)-dimensional submanifold:
 - closure(M) ∩ ∂B_1 = M ∩ ∂B_1, so Σ is closed and bounded;
 - ∂B_1 meets M transversally, since x ∈ T_xM is not tangent to the sphere at x.
 Ψ : (0, ∞) × Σ → M, Ψ(r, σ) := rσ, is a diffeomorphism (cone property; inverse x ↦ (|x|, x/|x|)) with Jacobian r^{m−1} with respect to dr ⊗ H^{m−1}⌞Σ. By the area formula,
 (5) ∫_M f dH^m = ∫_0^∞ r^{m−1}∫_Σ f(rσ) dH^{m−1}(σ) dr for every Borel f ≥ 0 on M.
 Put c_Σ := ∫_Σ |A|² dH^{m−1} < ∞ (|A| is continuous on the compact Σ). Recall |A(x)|² = r^{−2}|A(x/|x|)|² (step 3).
9. (Choice of ψ; printed (6).) Choose ε > 0 with (m/2 − 2 + ε)² < 2 and (1 + ε)² < 2. This is possible exactly because 2 ≤ m ≤ 6; ε := 1/10 works (SimonGMT AppendixB.exists_final_exponent).
 - Let ψ := r^{1+ε}r₁^{1−m/2−2ε}, r₁ := max{1, r}. It is locally Lipschitz on M (r > 0 on M), with r^{−2}ψ² = r^{2ε} on {r < 1} and r^{2−m−2ε} on {r > 1}.
 - By (5) and step 8, ∫_M r^{−2}ψ²|A|² = c_Σ(∫_0^1 r^{m−3+2ε} dr + ∫_1^∞ r^{−1−2ε} dr) < ∞, since m − 3 + 2ε > −1. So (4) holds.
 - |∇_M r| = 1 on M (0b), so |∇_Mψ| = (1 + ε)r^ε on {r < 1} and |m/2 − 2 + ε|·r^{1−m/2−ε} on {r > 1}. The set {r = 1} ∩ M = Σ is H^m-null.
 Hence (3) becomes
 (6) 2∫_{M∩{r<1}} |A|²r^{2ε} + 2∫_{M∩{r>1}} |A|²r^{2−m−2ε} ≤ (1 + ε)²∫_{M∩{r<1}} |A|²r^{2ε} + (m/2 − 2 + ε)²∫_{M∩{r>1}} |A|²r^{2−m−2ε},
 with all integrals finite (each is bounded by c_Σ times the convergent integrals above). Since 2 − (1 + ε)² > 0 and 2 − (m/2 − 2 + ε)² > 0, both integrals vanish. |A| is continuous and every nonempty relatively open subset of M has positive H^m-measure (F3), so |A| ≡ 0 on M.
10. (Hyperplane; parent B9.)
 - |A| ≡ 0 gives D_τν = 0 for every tangent τ (step 3: |A|² = Σ_i|D_{τ_i}ν|²), so ν is locally constant on M. Let M_c be a connected component of M (open in M, M being a manifold) and ν_c the constant value of ν on M_c.
 - For a C¹ curve γ in M_c, (ν_c·γ)' = ν_c·γ' = 0, so ν_c·x = const_c on M_c (connected manifolds are path connected).
 - For x ∈ M_c the ray {tx : t > 0} lies in M (0a), is connected and meets M_c, so it lies in M_c. Letting t ↓ 0 gives const_c = 0. Hence M_c ⊆ H_c := A₀ ∩ ν_c^⊥, an m-dimensional linear subspace.
 - M_c is open in H_c: it is an m-submanifold of the m-dimensional H_c, and a chart into H_c with injective derivative is a local diffeomorphism.
 - M_c is closed in H_c ∖ {0}: it is closed in M (components are closed), and M is closed in U₀ (0a).
 - H_c ∖ {0} is connected because m ≥ 2, and M_c ≠ ∅, so M_c = H_c ∖ {0}.
 - Suppose two components have H_c ≠ H_{c'}. Then dim(H_c ∩ H_{c'}) = m − 1 ≥ 1 (two distinct hyperplanes of the (m+1)-dimensional A₀), so some w ≠ 0 lies in M_c ∩ M_{c'}. Then M_c = M_{c'}, a contradiction.
 - M ≠ ∅, so all components share one plane H₀ := H_c with dim H₀ = m, and M = ⋃_c M_c = H₀ ∖ {0}.
 This is the conclusion: Module.finrank ℝ H₀ = m and M = H₀ ∖ {0}. ∎

## Key steps

1. Area formula: f_Z(t) = H^m(Φ_t(M ∩ K_Z)) = ∫J_t is smooth with a local minimum at 0. So f_Z′(0) = ∫_M div_M Z = 0, and v(M, 1) is stationary in ℝ^P ∖ {0}.
2. Allard–Schauder (Simon Ch. 5, 7.1, last part), with density one everywhere, makes M smooth. The first variation formula gives H_M ≡ 0.
3. ξ and a volume form of A₀ give a smooth unit normal ν ∈ A₀. Extending ζν to an A₀-valued Z and taking the second variation (Simon 5.11–5.12) gives the stability inequality B.1.
4. Simons' identity B.8 and the cone lemma B.11 give ½Δ|A|² + |A|⁴ ≥ 2r^{−2}|A|² + |∇|A||². Inserting ζ = |A|ψ in B.1 gives 2∫r^{−2}ψ²|A|² ≤ ∫|A|²|∇ψ|², which the cut-offs γ_κ extend to ψ with ∫r^{−2}ψ²|A|² < ∞.
5. With ψ = r^{1+ε}r₁^{1−m/2−2ε} and ε = 1/10 (2 ≤ m ≤ 6), (1+ε)² < 2 and (m/2−2+ε)² < 2 force |A| ≡ 0.
6. |A| ≡ 0 makes ν locally constant, so each component is a punctured hyperplane H_c ∖ {0} through 0. Since m ≥ 2 all H_c coincide, so M = H₀ ∖ {0}.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; sha256sum local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `sed -n 1,457p GMT/Ch07/Contract.lean (IMRep, IsIntegerMultiplicity, IsMinimizingIn, HasMassDensity, IsConeCurrent, IsEmbeddedSubmanifold, tangentSpace, IsOrientation, IsUnitOrientationOf, regularSet, unitBallVolume)`
- `grep -n 'def support|def zeroRegion|isOpen_zeroRegion|def massOn|structure GeometricCurrentOn|abbrev Covector' simongmt/Poincare/SimonGMT/Chapter06/{Currents,CurrentLocalEquality,Mass,Forms}.lean`
- `grep -n 'theorem|def' simongmt/Poincare/SimonGMT/AppendixB/{SimonsInequalities,ConeDefect,LagrangeIdentity}.lean and Chapter02/{SecondFundamentalForm,SecondFundamentalFormCalculus,SubmanifoldCalculus,AreaFormula}.lean`
- `sed -n 1,200p mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean; grep -n 'theorem addHaar_ball_of_pos|theorem ContinuousOn.aestronglyMeasurable|theorem setLIntegral_one|measure_sdiff_null' Mathlib`
- `python3 scans of dag.json: 518 nodes by status; children of codimension_one_regularity; accepted nodes whose statements mention IsConeCurrent, regularSet or HasMassDensity; statuses, frozen types and candidate commits of the 6 reused names; status of codim1_massOn_eq_lintegral_of_oriented_rep (decomposing)`
- `runtime.py of flow gmt-claude-b888e19cffb1: _solve_children, _existing_lean_name_problem, _wait_for_accepted_dependencies, _overlay_accepted_children`
- `git grep over all 2770 refs for the 5 new names (no match); git grep 'PseudoMetrizableSpace (MultiVector' in accepted branches`
- `lean -DautoImplicit=false /tmp/simons-split/check/Types2.lean; lean -DautoImplicit=false /tmp/simons-split/check/Assembly2.lean (LEAN_PATH = .lake/build/lib/lean plus every package's .lake/build/lib/lean)`
- `book: chapter-B.txt 1-282; chapter-02.txt 1162-1440; chapter-05.txt 1290-1380; chapter-06.txt 400-440 and 770-870; chapter-03.txt 290-330; chapter-07-source.txt 900-1010 and 1256-1300`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/AppendixB/SimonsInequalities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/AppendixB/ConeDefect.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SecondFundamentalForm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaFormula.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-7577af74dd/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1/decomposition-v6.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-ori-0059e6635e/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-chart-tangent-space-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-regular-point-density-a1-bilipsch-1804d7035f/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-B.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/simons-split/check/Types2.lean`
- `/tmp/simons-split/check/Assembly2.lean`

Pins match. The snapshot manifest records project b4d606db and Mathlib 25730c7c, equal to workspace HEAD and .lake/packages/mathlib. The snapshot Contract.lean, the workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…), so the selected frozen type and the 6 reused types are unchanged.
Library.
- SimonGMT supplies GeometricCurrentOn, support = U \ zeroRegion with zeroRegion open, and massOn (Chapter06).
- SimonGMT supplies the Appendix B algebra: simonsDefect_eq_sum_skew, four_mul_radialSkewSum_le, cone_simonsDefect_lower_bound (AppendixB/ConeDefect.lean) and exists_final_exponent (SimonsInequalities.lean).
- It has only pointwise second-fundamental-form algebra (Chapter02/SecondFundamentalForm.lean): no submanifold curvature field, no Simons identity, no Allard theorem, no nonlinear push-forward. These remain book citations inside hypercone_plane and area_comparison.
- The snapshot Mathlib has μHE isometry invariance and μHE = volume on Euclid d (Geometry/Euclidean/Volume/Measure.lean), Measure.euclideanHausdorffMeasure_smul₀, and addHaar_ball_of_pos (MeasureTheory/Measure/Lebesgue/EqHaar.lean:445), used by subspace_ball_measure and offvertex_rep.
DAG.
- codim1_massOn_eq_lintegral_of_oriented_rep is decomposing (unaccepted) under another parent. It cannot be a child or a child dependency here, so only this node's glue uses it.
- The six reused names are accepted with byte-identical types. Candidate commits: dor_ims_unitOrientation_dual 9c8432cb0101, dtc_vanish_off_support 44ef61f79e21, cone_current_apply_dilation_pullback 52115c22ec2d, rsdic_unitOrientation_eq_or_eq_neg fe95347baaed, chart_tangentSpace_eq_range_fderiv d626082a69a0, dimred_rpd_bilipschitz_image_measure 0501e07ced47.
- Overlapping unaccepted nodes cannot be reused: dimred_rpd_submanifold_density_one, dimred_rpd_massOn_eq_mult_measure and imrep_c1_diffeo_pushforward_im. Child sessions may reuse them once accepted.
- The 5 new codim1_ names are free in dag.json, GMT/, SimonGMT and all 2770 refs.
Lean.
- Types2.lean elaborates all 11 child types (exit 0).
- Assembly2.lean proves the selected frozen type from 4 child types plus oriented_piece_mass as axioms (exit 0). Its axioms are propext, Classical.choice, Quot.sound and those 5.
- A MultiVector PseudoMetrizableSpace instance workaround from accepted branches was needed and works.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
