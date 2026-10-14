<!-- theorem-id: gmt-ch07/root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1 -->

## Theorem `Submission.dtc_bc_tc_closure`

Let P, m ∈ ℕ with n := m + 1 < P, and let T_j (j ∈ ℕ) and T be currents in 𝒟_n(ℝ^P) (GeometricCurrentOn univ n) such that every T_j is integer multiplicity, sup_j (M_W(T_j) + M_W(∂T_j)) < ∞ for every bounded open W ⊆ ℝ^P (masses in [0, ∞]), and T_j ⇀ T (WeaklyConvergesOn). Then T is integer multiplicity.

Node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4749

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4168, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4196, https://github.com/ZhengyangZhang06/gmt-formalize/issues/810

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4200, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4763, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8057, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8061, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8063, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8065, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8066, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8067, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8068, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8070, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8077, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8081

## Lean problem

Declaration: `Submission.dtc_bc_tc_closure`

```lean
∀ (P m : ℕ) (Ts : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), m + 1 < P → (∀ j, IsIntegerMultiplicity (Ts j)) → (∀ W : Set (Euclid P), IsOpen W → Bornology.IsBounded W → ⨆ j, ((Ts j).massOn W + (Ts j).boundary.massOn W) < ∞) → WeaklyConvergesOn Ts T → IsIntegerMultiplicity T
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

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 of the parent proof cites Simon Ch. 6, Theorem 3.11 (Federer–Fleming compactness, chapter-06.txt lines 880–891), whose only non-elementary part is the present claim: "the existence of a T ∈ 𝒟_n(U) and a subsequence {T_j'} with T_j' ⇀ T is a consequence of the elementary 2.15; only the fact that T is an integer multiplicity current is non-trivial" (lines 888–891). Simon proves it in §8: Theorem 8.2 with Remarks 8.3(1),(2) (chapter-06.txt lines 2297–2473, printed pp. 176–179), Theorem 6.3 with 6.2 and 6.4 (boundary rectifiability; lines 1962–2003), the isoperimetric theorem 6.1 (lines 1939–1961), and Ch. 3, Theorem 1.6 "⇐" (chapter-03.txt lines 107–300). Parts I–V below follow, with the citation labels adapted as explained in "Cited results", the closure/boundary-rectifiability argument written in this run for DAG node root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1 (not reused by name: that node is unaccepted, reserved by another parent, and its statement also claims top-dimensional cases). Range correction (relative to that argument and to the first version of this proof): Simon's deformation theorem is stated only for n-currents in ℝ^{n+k} with n, k ∈ {1, 2, …} (§5 notation, chapter-06.txt line 1411), i.e. for positive degree and positive codimension, and it is cited below only in that range. Accordingly the closure statement CL(d) is asserted and proved only in ambient dimensions P' > d, and the boundary statement BR(d) only in ambient dimensions P' > d + 1 (Simon treats top-dimensional boundary rectifiability separately, by 3.14; that case is not needed here). Part II checks that the induction closes within these ranges, every application below states its range, and Part VI uses the hypothesis m + 1 < P exactly to place the stated case in the range of CL(m + 1). Departure (inherited from that reviewed proof): Simon's proof of 8.2 obtains rectifiability from the Rectifiability Theorem 8.1, which rests on the Besicovitch–Federer structure theorem (Ch. 3, 3.6), quoted in the book without proof ("For the proof of this theorem see [Fed69] or [Ros84]"). Here 8.1 is replaced by the tangent-plane argument of B. White (Comment. Math. Helv. 64 (1989) 207–220, cf. Simon's own remark in §8 that the structure theorem can be avoided), which uses only the slices, the lower density bound proved in Simon's 8.2 and BV-type estimates proved below; integrality of the multiplicity is then read off from slices (Step V14) instead of Simon's BV compactness argument. Errata: in Simon's 8.2 proof "Θ^{*n}(μ_T, ξ) < η" may be replaced by the lower density (only a sequence of radii is needed), and the support of the isoperimetric filling must be controlled (supplied by the deformation theorem); in Ch. 3, 1.6 the constant ε = 1/16ⁿ must be taken smaller (ε := 2^{−1}16^{−n}) for the contradiction in (10).

Notation. IM := integer multiplicity. Hᵏ := μHE[k]; Lᵏ is Lebesgue measure; ω_k := Lᵏ(B_1). For a measure μ, Θ^k_*(μ, x) := liminf_{r↓0} μ(B_r(x))/(ω_k r^k) (open balls). M(X) := X.mass for currents in ℝ^P; |α| is the Euclidean coefficient norm of covectors, and for k-vectors the dual norm. For currents X, Y in the same space, X + Y := X − (0 − Y). W ⊂⊂ U means: W open, closure(W) compact and contained in U (contract CompactlyContained). For d ∈ ℕ we use the two statements
CL(d): for every P' ∈ ℕ with d < P', every open U ⊆ ℝ^{P'} and all currents T_j (j ∈ ℕ), T ∈ 𝒟_d(U): if every T_j is IM, sup_j (M_W(T_j) + M_W(∂T_j)) < ∞ for every W ⊂⊂ U (the boundary term read as 0 when d = 0, contract boundaryMassOn), and T_j ⇀ T in U (WeaklyConvergesOn), then T is IM;
BR(d): for every P' ∈ ℕ with d + 1 < P', every open U ⊆ ℝ^{P'} and every IM R ∈ 𝒟_{d+1}(U) with M_W(∂R) < ∞ for every W ⊂⊂ U, the boundary ∂R is IM.
Cited results. Three are siblings of this decomposition (comparator-accepted declarations reused verbatim); three are theorems of the source text, exactly as the parent proof cites Simon's slicing and compactness theorems.
(MR) sibling mass_equals_rep_measure (accepted declaration cmc_massOn_eq_imRep_measure): for IM X with IMRep R in open U, M_G(X) = R.measure(G) for every open G; in particular a nonzero IM 0-current has mass ≥ 1.
(IMC) sibling im_calculus (accepted declaration cmc_imRep_locality_restrict_sub): locality of approximate tangent spaces (a), IM restrictions (b), differences and integer combinations (c), and (d) for every IMRep the orientation satisfies |orient x α| ≤ |α| for a.e. x of the carrier, so that (R.measure, R.orient) is an admissible representation for (SL) and the integrals below are absolutely convergent.
(VO) sibling vanish_off_support (accepted declaration dtc_vanish_off_support): if tsupport ω is disjoint from spt S then S(ω) = 0.
(REP) Simon Ch. 6, 2.7–2.8 (Riesz representation of currents of locally finite mass, chapter-06.txt lines 265–282) with Remark 2.37(1) (absolute continuity, lines 644–652; for currents of top degree on an open subset of ℝⁿ, as in V11(c), absolute continuity is Remark 2.35, lines 606–638, which writes such a current with locally finite boundary mass as integration of a BV_loc density against Lⁿ, and Lemma 2.36 reduces the general case to it), valid in every ambient space and every degree (it is applied in ℝ^P and, in V11(c), in ℝⁿ): a current X ∈ 𝒟_k(U) (U open) with M_W(X) < ∞ for every W ⊂⊂ U has a Borel measure μ_X on ℝ^P and a μ_X-a.e. strongly measurable field ξ_X of k-vectors with μ_X(ℝ^P ∖ U) = 0, μ_X(K) < ∞ for compact K ⊆ U, μ_X(G) = M_G(X) for every open G, |ξ_X(x)(α)| ≤ |α|, X(ω) = ∫ ξ_X(ω) dμ_X for ω ∈ 𝒟ᵏ(U); and if also M_W(∂X) < ∞ for every W ⊂⊂ U, then μ_X(E) = 0 whenever Hᵏ(E) = 0. Consequences: |ξ_X| = 1 μ_X-a.e. (for open G, μ_X(G) = M_G(X) ≤ ∫_G |ξ_X| dμ_X); for a Borel B, X⌞B(ω) := ∫_B ξ_X(ω) dμ_X is a current (linear; sequentially continuous because |X⌞B(ω)| ≤ |ω|_∞ μ_X(tsupport ω)), and for IM X with IMRep (M, θ, ξ) this is the IM restriction: by (MR) and REP, μ_X(G) = M_G(X) = (θHᵏ⌞M)(G) for open G, so the two locally finite Borel measures agree on Borel sets; both (μ_X, ξ_X) and (θHᵏ⌞M, ξ) represent X, so ∫⟨ω, ξ_X − ξ⟩ dμ_X = 0 for all test forms ω, whence ξ_X = ξ μ_X-a.e. (coordinatewise, a finite signed Radon measure on an open set annihilating C_c^∞ is zero).
(SL) Simon Ch. 6, 4.6–4.11 (slices by Lipschitz functions, chapter-06.txt lines 1335–1403): let U be open, X ∈ 𝒟_{k+1}(U) and ∂X represented by Borel measures μ, μ' (finite on compact subsets of U) and fields ξ, ξ' with |ξ(x)(α)| ≤ |α| μ-a.e. and |ξ'(x)(α)| ≤ |α| μ'-a.e., and let f be L-Lipschitz. Then X⌞{f < t}(ω) := ∫_{f<t} ξ(ω) dμ and (∂X)⌞{f < t}(η) := ∫_{f<t} ξ'(η) dμ' are currents, the slice Z_t := ∂(X⌞{f<t}) − (∂X)⌞{f<t} satisfies Z_t(η) = 0 whenever tsupport η ∩ {f = t} = ∅, M_G(Z_t) ≤ L liminf_{h↓0} h⁻¹μ(G ∩ {t − h < f < t}) for every open G and t, and ∫⁻_{(a,b)} M_G(Z_t) dt ≤ L μ(G ∩ {a < f < b}).
(DT) Simon Ch. 6, 5.1–5.3 (deformation theorem, chapter-06.txt lines 1405–1930, statements lines 1428–1476, stated for n-currents in ℝ^{n+k} with n, k ∈ {1, 2, …}, line 1411; used here only in that range of positive degree and positive codimension; the dichotomy below is (1) in the proof of 6.1, lines 1948–1956, each k-dimensional face of the cubical grid of side ρ having k-dimensional measure ρ^k): for every P ∈ ℕ and every e ∈ ℕ with e + 1 < P (currents of degree k := e + 1, so 1 ≤ k ≤ P − 1) there is c = c(P, e) ≥ 1 such that for every ρ > 0 and every IM T ∈ 𝒟_k(ℝ^P) with compact support and M(T) + M(∂T) < ∞ there are Q ∈ 𝒟_k(ℝ^P), R ∈ 𝒟_{k+1}(ℝ^P), S ∈ 𝒟_k(ℝ^P) with Q, ∂Q, R IM (Q = Σ_F β_F[[F]] with integers β_F over the oriented k-faces F of the grid of side ρ, so ∂Q is an integer combination of oriented (k−1)-faces), T − Q − S = ∂R, Q = 0 or M(Q) ≥ ρ^k, M(Q) ≤ cM(T), M(∂Q) ≤ cM(∂T), M(R) ≤ cρM(T), M(S) ≤ cρM(∂T), spt Q ∪ spt R ⊆ {dist(·, spt T) < 3√P ρ} and spt ∂Q ∪ spt S ⊆ {dist(·, spt ∂T) < 3√P ρ} (Simon's bound is 2√P ρ). (Parts I–V write "(DT) with m := e" for this choice of e, i.e. for currents T of degree e + 1, and verify 1 ≤ e + 1 < P at each use; (DT) is never applied to currents of degree P in ℝ^P.)
Measurable majorant (MM). In the situation of (SL) with G open and F(t) := μ_X(G ∩ {a < f < t}) (nondecreasing, finite if μ_X(G ∩ {a < f < b}) < ∞), M_G(Z_t) ≤ L F'(t) at every t ∈ (a, b) where F is differentiable (a.e., Mathlib Monotone.ae_differentiableAt), F' is measurable (Mathlib measurable_deriv) and integrable on [a, b] (Mathlib MonotoneOn.intervalIntegrable_deriv), and ∫_a^b F' ≤ μ_X(G ∩ {a < f < b}) (Mathlib MonotoneOn.intervalIntegral_deriv_mem_uIcc). For a sequence X_j with sup_j μ_{X_j}(G ∩ {a < f < b}) ≤ Λ, Fatou gives ∫_a^b liminf_j F_j' ≤ Λ, so for a.e. t: every F_j is differentiable at t and liminf_j M_G(Z_{j,t}) ≤ L liminf_j F_j'(t) < ∞.

Part I. Tools.
T0 (Zero current.) For every P, k and every U ⊆ ℝ^P, the zero current in 𝒟_k(U) is IM: the IMRep with empty carrier, multiplicity 0 and orientation 0 represents it (∅ is Borel and countably rectifiable by SimonGMT countablyRectifiable_of_measure_zero; the positivity, integrability, measurability and orientation fields hold vacuously because μHE restricted to ∅ is the zero measure; and the representing integral over ∅ is 0).
T1 (Compactness of Radon measures.) If U ⊆ ℝ^P is open and μ_j are Borel measures with sup_j μ_j(K) < ∞ for compact K ⊆ U, then a subsequence converges to a Borel measure μ on U, finite on compact subsets of U, in the sense ∫ f dμ_j → ∫ f dμ for f ∈ C_c(U); then limsup_j μ_j(C) ≤ μ(C) for compact C ⊆ U and μ(G) ≤ liminf_j μ_j(G) for open G ⊆ U. Proof: take compact K_k ↑ U with K_k ⊆ int K_{k+1}; by SimonGMT Chapter01 simon_theorem_4_16_compact_metrizable applied to μ_j⌞K_k on the compact metrizable space K_k and a diagonal argument, Λ(f) := lim ∫ f dμ_j exists for every f ∈ C_c(U); Λ is a positive linear functional, so Riesz–Markov–Kakutani (Mathlib RealRMK.rieszMeasure) gives μ. The two inequalities follow by approximating 1_C from above and 1_G from below by functions in C_c(U) (Urysohn).
T2 (Restrictions converge.) Let X_j ⇀ X in 𝒟_k(U) (U open), all with locally finite mass (representations from REP), μ_{X_j} → μ as in T1, and f : ℝ^P → ℝ continuous with μ({f = t}) = 0. Then X_j⌞{f < t} ⇀ X⌞{f < t}. Proof: let ω ∈ 𝒟ᵏ(U) with compact support C ⊆ U and ε > 0. The compact sets C ∩ {f ≤ t − ε} and C ∩ {f ≥ t} are disjoint; choose χ_ε ∈ C_c^∞(U; [0, 1]) equal to 1 on the first and 0 on the second. Then 1_{f<t} − χ_ε vanishes on C outside {t − ε < f < t} and has absolute value ≤ 1, so |X_j⌞{f<t}(ω) − X_j(χ_εω)| ≤ |ω|_∞ μ_{X_j}(C ∩ {t − ε ≤ f ≤ t}), whose limsup is ≤ |ω|_∞ μ(C ∩ {t − ε ≤ f ≤ t}) (T1, compact set), and this tends to |ω|_∞ μ(C ∩ {f = t}) = 0 as ε ↓ 0. Likewise |X⌞{f<t}(ω) − X(χ_εω)| ≤ |ω|_∞ μ_X(C ∩ {t − ε < f < t}) → 0. Finally X_j(χ_εω) → X(χ_εω).
T3 (Cone inequality.) If X ∈ 𝒟_k(ℝ^P), k ≥ 1, has finite mass, ∂X = 0 and spt X ⊆ B̄_r(x₀), then |X(ω)| ≤ r M(X)|dω|_∞ for ω ∈ 𝒟ᵏ(ℝ^P). Proof: let (Kγ)(x) := ∫_0^1 t^{j−1} ι_{x−x₀}γ(x₀ + t(x − x₀)) dt for a smooth j-form γ (the homotopy operator of the contraction h_t(x) = x₀ + t(x − x₀)); differentiation under the integral and Cartan's formula d ι_v + ι_v d = L_v for the radial field v(x) = x − x₀ give dKγ + Kdγ = γ − h₀^#γ = γ for j ≥ 1 (h₀ is constant), and |Kγ(x)| ≤ |x − x₀| |γ|_∞/j (|ι_vγ| ≤ |v||γ|). With ζ ∈ C_c^∞ equal to 1 near spt X: X(ω) = X(ζω) = X(ζ dKω) + X(ζ Kdω), and X(ζ dKω) = X(d(ζKω)) − X(dζ ∧ Kω) = ∂X(ζKω) − 0 = 0 by (VO). Hence |X(ω)| ≤ ∫|Kdω| dμ_X ≤ r|dω|_∞ M(X) (μ_X is carried by spt X, REP and VO).
T4 (IM is local.) Let U be open and X ∈ 𝒟_k(U) with locally finite mass. If every point of U has an open ball B ⊆ U and an IM current X_B ∈ 𝒟_k(U) with X(ω) = X_B(ω) whenever tsupport ω ⊆ B, then X is IM. Proof: let (μ_X, ξ_X) be the REP representation and (M_B, θ_B, ξ_B) an IMRep of X_B. For open G ⊆ B, the admissible forms for M_G(X) and M_G(X_B) coincide and give the same values, so by REP and (MR) μ_X(G) = M_G(X) = M_G(X_B) = (θ_BHᵏ⌞M_B)(G); two locally finite Borel measures agreeing on the open subsets of B agree on its Borel subsets, so μ_X⌞B = θ_BHᵏ⌞(M_B ∩ B). Both (μ_X, ξ_X) and (μ_X⌞B, ξ_B) represent X on forms supported in B, so ∫⟨ω, ξ_X − ξ_B⟩ dμ_X = 0 for every test form ω supported in B; coordinatewise (a finite signed Radon measure on an open set annihilating C_c^∞ is zero: approximate indicators of compact sets by smooth functions and use dominated convergence and inner regularity) ξ_X = ξ_B μ_X-a.e. on B. Cover U by countably many such balls B_i, put A_i := B_i ∖ ⋃_{l<i} B_l and M := ⋃_i (M_{B_i} ∩ A_i), θ := θ_{B_i}, ξ := ξ_{B_i} on M_{B_i} ∩ A_i. Then X(ω) = Σ_i ∫_{A_i} ξ_X(ω) dμ_X = ∫_M θ⟨ω, ξ⟩ dHᵏ; the IMRep fields hold (countable unions of rectifiable sets are rectifiable; θ ≥ 1 integer-valued; ∫_{M∩K}θ dHᵏ = μ_X(K) < ∞ for compact K ⊆ U; by IMC(a), for a.e. x ∈ M ∩ A_i the approximate tangent spaces of M, of M ∩ A_i = M_{B_i} ∩ A_i and of M_{B_i} coincide, and ξ_{B_i}(x) orients them).
T5 (Dilations.) For a ∈ ℝ^P and λ > 0 let η(y) := λ⁻¹(y − a) and η_#X := the push-forward by this proper affine map (SimonGMT affinePushforward): η_#X(ω) = X(η^#ω), (η^#ω)(y) = λ^{−k}ω(η(y)) (as k-covectors). Then ∂η_# = η_#∂, M_{η(W)}(η_#X) = λ^{−k}M_W(X), spt η_#X = η(spt X); if X = τ(M, θ, ξ) is IM then η_#X = τ(η(M), θ ∘ η⁻¹, ξ ∘ η⁻¹) is IM (Hᵏ(η(A)) = λ^{−k}Hᵏ(A), and the approximate tangent space of η(M) at η(x) is that of M at x because blow-ups commute: η_{η(x),r}(η(M)) = η_{x,λr}(M)); restrictions commute: η_#(X⌞{f ∘ η < t}) = (η_#X)⌞{f < t} (by the change of variables η_#X(ω) = ∫⟨λ^{−k}ω(η(x)), ξ_X(x)⟩ dμ_X(x), the pair (λ^{−k}η_*μ_X, ξ_X ∘ η⁻¹) represents η_#X, and restrictions do not depend on the representation by (o) of V4).

Part II. Structure of the induction. CL(d) and BR(d) are as defined in the Notation paragraph, each with its range of ambient dimensions; the ambient space of Parts III–V is denoted ℝ^P. We prove CL(0) in every ambient dimension P ≥ 1 (Part III). For every d ≥ 0 we prove BR(d) in every ambient dimension P ≥ d + 2 from CL(d) (Part IV), and CL(d+1) in every ambient dimension P ≥ d + 2 from CL(d) and BR(d) (Part V). The ranges close up. Part IV works in ℝ^P with d + 1 < P and uses CL(d) only in ℝ^P (d < P) and (DT) only in degree d + 1 ∈ [1, P − 1]. Part V proves CL(n), n := d + 1, in ℝ^P with n < P. It uses BR(d) only for n-currents in open subsets of ℝ^P (d + 1 = n < P), CL(d) only for (n−1)-currents in open subsets of ℝ^P (d < P), and (DT) only through (Iso), in degree d = n − 1 ∈ [1, P − 1] when n ≥ 2. By induction on d, for every d ∈ ℕ, CL(d) holds in every ambient dimension P > d and BR(d) in every ambient dimension P > d + 1. No top-dimensional case (currents of degree P in ℝ^P) of CL, BR or (DT) is used. The only top-dimensional objects are the n-currents Y_k on an open subset of ℝⁿ in V11, and only (REP) is applied to them (Simon 2.35 covers that case).

Part III. CL(0) (in every ambient dimension P ≥ 1; the argument does not use the range). Let U ⊆ ℝ^P be open and T_j ∈ 𝒟_0(U) be IM with sup_j M_W(T_j) < ∞ for W ⊂⊂ U (the boundary term is 0 in degree 0) and T_j ⇀ T. In degree 0, H⁰ is counting measure and an IMRep is a set M_j with θ_j ≥ 1 and orientations ±1 (the approximate tangent space at each point of a locally finite set is {0}); local integrability makes M_j ∩ K finite for compact K ⊆ U, so T_j(a) = Σ_{x∈M_j} m_j(x) a(x) with m_j(x) ∈ ℤ ∖ {0} (a ∈ C_c^∞(U) a 0-form). T has locally finite mass (lower semicontinuity). Fix x₀ ∈ U and r > 0 with B̄_{2r}(x₀) ⊆ U, and c := sup_j M_{B_{2r}(x₀)}(T_j) < ∞; by (MR), Σ_{x∈M_j∩B_{2r}(x₀)}|m_j(x)| ≤ c, so on B_{2r}(x₀), T_j = Σ_{i=1}^{N_j} ε_{j,i}δ_{x_{j,i}} with N_j ≤ c, ε_{j,i} = ±1, x_{j,i} ∈ B_{2r}(x₀) (points repeated by multiplicity). Pass to a subsequence with N_j = N, ε_{j,i} = ε_i and x_{j,i} → y_i ∈ B̄_{2r}(x₀). For a ∈ C_c^∞(B_r(x₀)), T(a) = lim_j Σ_i ε_i a(x_{j,i}) = Σ_i ε_i a(y_i). So on B_r(x₀), T agrees with the IM current Σ_{y} m(y)δ_y, m(y) := Σ_{y_i = y}ε_i (points with m(y) = 0 omitted; finite carrier in U). By T4, T is IM.

Part IV. BR(d) from CL(d). Let P ≥ d + 2 (i.e. d + 1 < P), U ⊆ ℝ^P open, and R ∈ 𝒟_{d+1}(U) IM with M_W(∂R) < ∞ for W ⊂⊂ U. CL(d) is available in ℝ^P because d < P.
1. (Localization.) Fix x₀ ∈ U and r₀ > 0 with B̄_{2r₀}(x₀) ⊆ U; f := |· − x₀|. Apply (SL) to R (IM representation) and ∂R (REP representation); by (MM), for a.e. r ∈ (0, r₀) the slice Z_r := ∂(R⌞B_r(x₀)) − (∂R)⌞B_r(x₀) has finite mass. Fix such r. (The total mass of Z_r is controlled by its mass in G := B_{r₀}(x₀): Z_r vanishes on forms supported off ∂B_r(x₀) ⊆ G, so splitting an admissible form ω = χω + (1 − χ)ω with χ ∈ C_c^∞(G; [0,1]) equal to 1 near ∂B_r(x₀) gives Z_r(ω) = Z_r(χω) ≤ M_G(Z_r).) R' := R⌞B_r(x₀) is IM (IMC(b)) with carrier contained in B_r(x₀), supported in B̄_r(x₀), M(R') < ∞ (MR), and ∂R' = (∂R)⌞B_r(x₀) + Z_r has finite mass. Extend R' to ℝ^P: R̂'(ω) := R'(ζω) with ζ ∈ C_c^∞(U) equal to 1 near B̄_r(x₀) (independent of ζ by VO); R̂' is IM with the same IMRep, M(R̂') = M(R'), ∂R̂' = (∂R')^ (VO).
2. (Approximation by the deformation theorem; Simon 6.2.) R̂' is an IM current of degree d + 1 with 1 ≤ d + 1 < P, compact support in B̄_r(x₀) and M(R̂') + M(∂R̂') < ∞, so (DT) applies in its range. By (DT) with m := d and ρ := ρ_k := 2^{−k}, applied to R̂': R̂' − Q_k − S_k = ∂R_k with Q_k and ∂Q_k IM, M(R_k) ≤ cρ_kM(R̂') → 0, M(S_k) ≤ cρ_kM(∂R̂') → 0, M(∂Q_k) ≤ cM(∂R̂'), and spt Q_k ⊆ {dist(·, B̄_r(x₀)) < 3√P ρ_k}. For ω ∈ 𝒟^{d+1}(ℝ^P), |Q_k(ω) − R̂'(ω)| ≤ M(S_k)|ω|_∞ + M(R_k)|dω|_∞ → 0, so Q_k ⇀ R̂' and ∂Q_k ⇀ ∂R̂'. The ∂Q_k are IM d-currents in ℝ^P with ∂∂Q_k = 0 and bounded masses, so by CL(d) (in U := ℝ^P, within its range since d < P; the boundary term is M(∂∂Q_k) = 0, or 0 in degree 0), ∂R̂' is IM.
3. (Back to ∂R.) If tsupport η ⊆ B_r(x₀), then ∂R̂'(η) = (∂R)⌞B_r(x₀)(η) + Z_r(η) = ∂R(η) + 0 (η vanishes off B_r(x₀); Z_r(η) = 0 by SL since tsupport η misses {f = r}). The restriction of ∂R̂' to test forms in U is IM: by (MR) and (VO) its IMRep measure vanishes off spt ∂R̂' ⊆ B̄_r(x₀) ⊆ U, so the carrier can be intersected with B̄_r(x₀) without changing the current (IMC(b)), and the resulting data form an IMRep in U. By T4 (∂R has locally finite mass by hypothesis), ∂R is IM. ∎

Part V. CL(n) for n = d + 1 ≥ 1, assuming CL(d) (in every ambient dimension > d) and BR(d) (in every ambient dimension > d + 1).
Let P > n (i.e. d + 1 < P), U ⊆ ℝ^P open, T_j ∈ 𝒟_n(U) IM, Λ_W := sup_j (M_W(T_j) + M_W(∂T_j)) < ∞ for W ⊂⊂ U, T_j ⇀ T. Throughout Part V the ambient space is this ℝ^P with n < P. So every application of BR(d) below (to n-currents in open subsets of ℝ^P) is in its range d + 1 = n < P. Every application of CL(d) (to (n−1)-currents in open subsets of ℝ^P) is in its range d < P. (DT) enters only through (Iso), in degree n − 1 with 1 ≤ n − 1 < P.
V1 (Boundaries.) Each ∂T_j is IM by BR(d) (in U ⊆ ℝ^P; range d + 1 = n < P). T and ∂T have locally finite mass (lower semicontinuity), hence representations (REP).
V2 (Localization; Simon 8.3(1).) Fix x₀ ∈ U, r₀ > 0 with B̄_{2r₀}(x₀) ⊆ U. Pass to a subsequence with μ_{T_j} → μ on U (T1). By (SL) with f := |· − x₀| (representations from IMReps of T_j and ∂T_j, with |orient| ≤ 1 a.e. by IMC(d)) and (MM) (with Λ_{B_{r₀}(x₀)}; total masses of the slices are controlled by their masses in B_{r₀}(x₀) as in IV.1), for a.e. r ∈ (0, r₀), liminf_j M(Z_{j,r}) < ∞, where Z_{j,r} := ∂(T_j⌞B_r(x₀)) − (∂T_j)⌞B_r(x₀); also μ(∂B_r(x₀)) = 0 for all but countably many r. Fix such r and pass to a subsequence with sup_j M(Z_{j,r}) < ∞. Then T'_j := T_j⌞B_r(x₀) are IM (IMC(b)), supported in K := B̄_r(x₀), with sup_j (M(T'_j) + M(∂T'_j)) < ∞, and T'_j ⇀ T⌞B_r(x₀) (T2). Extending to ℝ^P as in IV.1 (carriers inside B_r(x₀)), the extensions T̂'_j are IM with M(∂T̂'_j) = M(∂T'_j) < ∞, so ∂T̂'_j is IM by BR(d) applied in ℝ^P (range n < P); and T̂'_j ⇀ (T⌞B_r(x₀))^. Then the claim (CL*) below shows that (T⌞B_r(x₀))^ is IM; its restriction to U is IM and agrees with T on forms supported in B_r(x₀). By T4, T is IM. It remains to prove:
(CL*) (Here n < P.) If T_j ∈ 𝒟_n(ℝ^P) are IM, ∂T_j are IM, spt T_j ⊆ K (a fixed compact set), sup_j (M(T_j) + M(∂T_j)) < ∞ and T_j ⇀ T, then T is IM.
V3 (Reduction to cycles; Simon 8.2 and White.) In (CL*), ∂T_j are IM (n−1)-cycles supported in K with bounded masses and ∂T_j ⇀ ∂T, so ∂T is IM by CL(d) (in ℝ^P; range d < P), with spt ∂T ⊆ K, M(∂T) < ∞ and ∂∂T = 0 (if n − 1 ≥ 1). We find an IM Y ∈ 𝒟_n(ℝ^P) with compact support and ∂Y = ∂T:
(Iso) If n − 1 = d ≥ 1 (so 1 ≤ d < n < P) and Z ∈ 𝒟_d(ℝ^P) is an IM cycle with compact support, then there is IM Y with ∂Y = Z, M(Y) ≤ c_I M(Z)^{(d+1)/d} and spt Y ⊆ {dist(·, spt Z) < 3√P(2c M(Z))^{1/d}}, where c = c(P, d − 1) is the constant of (DT) and c_I := c(2c)^{1/d}. Proof (Simon 6.1, stated for (n−1)-cycles in ℝ^{n+k} with n ≥ 2 and k ≥ 1, i.e. here d + 1 ≥ 2 and d + 1 < P; its proof uses (DT) only in degree d, and 1 ≤ d < P): if Z = 0 take Y = 0 (IM by T0). Otherwise apply (DT) with m := d − 1 (degree d, within its range 1 ≤ d < P) and ρ := (2cM(Z))^{1/d} to Z (IM, compact support, M(Z) + M(∂Z) = M(Z) < ∞): Z − Q − S = ∂Y with M(S) ≤ cρM(∂Z) = 0, so S = 0; M(Q) ≤ cM(Z) = ρ^d/2 < ρ^d, so Q = 0 by the dichotomy Q = 0 ∨ M(Q) ≥ ρ^d; hence Z = ∂Y with Y IM, M(Y) ≤ cρM(Z) = c_IM(Z)^{(d+1)/d} and the support bound of (DT).
If n = 1: ∂T is an IM 0-current with compact support, so ∂T = Σ_{i=1}^N m_iδ_{x_i}; with ζ ∈ C_c^∞ equal to 1 near K, ∂T(ζ) = lim_j T_j(dζ) = 0 (VO), i.e. Σm_i = 0; let Y := Σ_i m_i[[x₀, x_i]] (oriented segments from a fixed point x₀ ∉ {x_1, …, x_N}; each is IM — carrier the open segment, multiplicity 1, unit tangent orientation, approximate tangent line at every interior point — and integer combinations are IM by IMC(c)); then ∂Y = Σ m_i(δ_{x_i} − δ_{x₀}) = ∂T.
Put Γ := T − Y. Then Γ is a cycle (∂Γ = ∂T − ∂Y = 0) with compact support (⊆ K ∪ spt Y) and finite mass, and it suffices to show that Γ is IM, because then T = Γ − (0 − Y) is IM (IMC(c)). (Note that the currents T_j − Y are not cycles; the argument below only uses properties of the limit.)
V4 (IM slice property.) For a current X ∈ 𝒟_n(ℝ^P) such that X and ∂X have locally finite mass (if n = 1, ∂X is a 0-current and terms involving ∂∂X are absent), with REP representations of X and ∂X, a Lipschitz f and t ∈ ℝ, let ⟨X, f, t⟩ := ∂(X⌞{f < t}) − (∂X)⌞{f < t} (the current Z_t of SL). Say that X has (ISP) if for every Lipschitz f : ℝ^P → ℝ and L¹-a.e. t, ⟨X, f, t⟩ is IM. For a cycle, ⟨X, f, t⟩ = ∂(X⌞{f < t}).
(o) Linearity. For such X, X' and Borel B, (X − X')⌞B = X⌞B − X'⌞B: the finite-dimensional-vector-valued Radon measures ξ_{X−X'}μ_{X−X'} and ξ_Xμ_X − ξ_{X'}μ_{X'} integrate every smooth compactly supported covector field in the same way, hence (coordinatewise, a finite signed Radon measure on an open set annihilating C_c^∞ is zero: approximate indicators of compact sets by smooth functions and use dominated convergence and inner regularity) agree on bounded Borel sets. Consequently ⟨X − X', f, t⟩ = ⟨X, f, t⟩ − ⟨X', f, t⟩.
(i) If X is IM, ∂X is IM and both have locally finite mass, then X has (ISP): by (SL) and (MM), for a.e. t the slice ⟨X, f, t⟩ has locally finite mass; X⌞{f < t} is IM (IMC(b)) and its boundary (∂X)⌞{f<t} + ⟨X, f, t⟩ has locally finite mass, so it is IM by BR(d); and ⟨X, f, t⟩ = ∂(X⌞{f<t}) − (∂X)⌞{f<t} is IM (IMC(b),(c)). (BR(d) is applied to the n-current X⌞{f < t} in ℝ^P, within its range since d + 1 = n < P.)
(ii) (ISP) passes to weak limits: let X_i have (ISP), sup_i (μ_{X_i}(B_k(0)) + μ_{∂X_i}(B_k(0))) < ∞ for every k, and X_i ⇀ X. By lower semicontinuity of mass, X and ∂X have locally finite mass, so ⟨X, f, t⟩ is defined. Fix f (L-Lipschitz) and k ∈ ℕ. Pass to a subsequence with μ_{X_i} → μ and μ_{∂X_i} → μ' (T1). Applying (MM) to the sum of the majorants for X_i (slices ⟨X_i, f, t⟩) and, if n ≥ 2, for ∂X_i (slices ⟨∂X_i, f, t⟩ = ∂((∂X_i)⌞{f<t}), as ∂∂X_i = 0), on each interval (−m, m) (and then for all m simultaneously, countably many conditions) we get for a.e. t: μ({f = t}) = μ'({f = t}) = 0; liminf_i (M_{B_{k+1}(0)}(⟨X_i, f, t⟩) + M_{B_{k+1}(0)}(⟨∂X_i, f, t⟩)) < ∞; and ⟨X_i, f, t⟩ is IM for every i. Fix such t and a further subsequence along which these masses are bounded. By T2 applied to X_i and to ∂X_i, ⟨X_i, f, t⟩ ⇀ ⟨X, f, t⟩; and ∂⟨X_i, f, t⟩ = −∂((∂X_i)⌞{f<t}) = −⟨∂X_i, f, t⟩ has bounded mass in B_{k+1}(0) (for n = 1 the slices are 0-currents and there is no boundary term). The domain restrictions to U' := B_{k+1}(0) of the IM currents ⟨X_i, f, t⟩ are IM (intersect their carriers with U', IMC(b) in ℝ^P), with bounded mass and boundary mass in U', and converge weakly in U'; by CL(d) in U' (an open subset of ℝ^P; range d < P), the domain restriction of ⟨X, f, t⟩ to U' is IM. Intersecting its carrier with B_k(0) (IMC(b) in U') and extending by A ↦ (ω ↦ A(ζω)), ζ ∈ C_c^∞(U') equal to 1 near B̄_k(0) (as in IV.1; an IMRep with carrier in B_k(0) is an IMRep in ℝ^P), gives an IM current in ℝ^P agreeing with ⟨X, f, t⟩ on forms supported in B_k(0). ⟨X, f, t⟩ has locally finite mass (lower semicontinuity of mass under the above weak convergence). For a.e. t this holds for all k, and T4 shows that ⟨X, f, t⟩ is IM. So X has (ISP).
(iii) (ISP) is invariant under the dilations of T5 (slices of η_#X by f are η_# of slices of X by f ∘ η, and η_# preserves IM).
Application: the T_j have (ISP) by (i) (T_j, ∂T_j IM, bounded masses); by (ii), T has (ISP); Y has (ISP) by (i) (Y IM with compact support, ∂Y = ∂T IM, finite masses); by (o) and IMC(c), Γ = T − Y has (ISP), i.e. ∂(Γ⌞{f < t}) is IM for every Lipschitz f and a.e. t.
V5 (Lower density lemma; Simon 8.2 (2)–(6).) There is η₀ = η₀(n, P) > 0 such that every n-cycle C in ℝ^P (n < P) with locally finite mass and (ISP) satisfies Θⁿ_*(μ_C, x) ≥ η₀ for μ_C-a.e. x.
Proof. Θⁿ_*(μ_C, ·) is Borel (x ↦ μ_C(B_r(x)) is lower semicontinuous and r ↦ μ_C(B_r(x)) is left continuous, so the liminf may be taken over rational r). Let 0 < η < 1/4 and A_η := {x : Θⁿ_*(μ_C, x) < η}. By inner regularity it suffices to show μ_C(K') = 0 for compact K' ⊆ A_η, when η is small. Fix K', ε₀ ∈ (0, 1) and W := {dist(·, K') < ε₀} (bounded open, μ_C(W) < ∞).
(a) Good radii. Let x₁ ∈ K' and 0 < δ < ε₀/(2 + 3√P). Since Θⁿ_*(μ_C, x₁) < η there is s ∈ (0, δ) with F(s) < ηω_nsⁿ, F(ρ) := μ_C(B_ρ(x₁)). F^{1/n} is nondecreasing, so ∫_0^s (F^{1/n})' ≤ F^{1/n}(s) < (ηω_n)^{1/n}s, and the set of ρ ∈ (0, s) with (F^{1/n})'(ρ) ≤ 2(ηω_n)^{1/n} has positive measure. Choose ρ in it such that also F is differentiable at ρ, ∂(C⌞B_ρ(x₁)) is IM (ISP with f = |· − x₁|), μ_C(∂B_ρ(x₁)) = 0, and (SL) gives M(∂(C⌞B_ρ(x₁))) ≤ F'(ρ) (the slice equals ∂(C⌞B_ρ(x₁)) because ∂C = 0, and liminf_h h⁻¹μ_C({ρ − h < |· − x₁| < ρ}) ≤ F'(ρ)). Then Z := ∂(C⌞B_ρ(x₁)) is an IM (n−1)-cycle with spt Z ⊆ ∂B_ρ(x₁) and M(Z) ≤ F'(ρ) = nF(ρ)^{(n−1)/n}(F^{1/n})'(ρ) ≤ 2n(ηω_n)^{1/n}F(ρ)^{(n−1)/n} ≤ 2nηω_n s^{n−1}. If n ≥ 2, (Iso) gives IM S with ∂S = Z, M(S) ≤ c_I(2n)^{n/(n−1)}(ηω_n)^{1/(n−1)} μ_C(B_ρ(x₁)) =: κ(η) μ_C(B_ρ(x₁)) and spt S ⊆ B̄_{ρ + 3√P(4cnηω_n)^{1/(n−1)}s}(x₁) ⊆ B̄_{(1+3√P)δ}(x₁) as soon as 4cnηω_n ≤ 1. If n = 1, M(Z) ≤ 4η < 1, so Z = 0 by (MR) and we take S := 0, κ := 0.
(b) Covering. The closed balls B̄_ρ(x₁) of (a) (x₁ ∈ K', ρ arbitrarily small) form a fine cover of K'; by the Besicovitch–Vitali theorem for the finite measure μ_C⌞W (Mathlib Besicovitch.exists_disjoint_closedBall_covering_ae) there are disjoint B_i = B̄_{ρ_i}(x_i) from (a) covering μ_C-almost all of K', with B_i ⊆ W. Let S_i be the corresponding fillings and X_i := S_i − C⌞B_i, an n-cycle (∂S_i = ∂(C⌞B_i), μ_C(∂B_i) = 0) supported in B̄_{(1+3√P)δ}(x_i). By T3, |X_i(ω)| ≤ (1 + 3√P)δ(1 + κ)μ_C(B_i)|dω|_∞; as Σ_iμ_C(B_i) ≤ μ_C(W), Σ_i S_i and Σ_i C⌞B_i converge absolutely in mass, and |Σ_iX_i(ω)| ≤ (1 + 3√P)δ(1 + κ)μ_C(W)|dω|_∞ → 0 as δ ↓ 0. Hence C⌞(ℝ^P ∖ ⋃B_i) + Σ_iS_i = C + Σ_iX_i ⇀ C as δ ↓ 0 (countable additivity of the representing integral).
(c) By lower semicontinuity of M_W, μ_C(W) = M_W(C) ≤ liminf_{δ↓0}(μ_C(W ∖ ⋃B_i) + Σ_iM(S_i)) ≤ μ_C(W ∖ K') + κ μ_C(W), using μ_C(K' ∖ ⋃B_i) = 0 and Σ_iμ_C(B_i) ≤ μ_C(W). Choose η₀ < 1/4 with κ(η₀) ≤ 1/2 and (if n ≥ 2) 4cnη₀ω_n ≤ 1; for η = η₀, μ_C(W) ≤ 2μ_C(W ∖ K'). Letting ε₀ ↓ 0 gives μ_C(K') = 0. ∎
V6 (Representation of the cycle Γ.) Γ is an n-cycle with finite mass, compact support and (ISP) (V3, V4). Let M₀ := {x ∈ spt Γ : Θⁿ_*(μ_Γ, x) ≥ η₀} (Borel); μ_Γ(ℝ^P ∖ M₀) = 0 by V5 and VO. Since the upper density with closed balls is ≥ η₀ on M₀, SimonGMT Chapter01 simon_theorem_3_3 gives η₀Hⁿ(M₀) ≤ μ_Γ(ℝ^P) < ∞. By REP (absolute continuity; ∂Γ = 0), μ_Γ ≪ Hⁿ⌞M₀, so by Radon–Nikodym μ_Γ = θHⁿ⌞M₀ with θ Borel, integrable; let M' := M₀ ∩ {θ > 0} (μ_Γ(M₀ ∖ M') = 0). With ξ_Γ from REP (|ξ_Γ| = 1 μ_Γ-a.e.) put τ := θξ_Γ: Γ(ω) = ∫_{M'}⟨ω, τ⟩ dHⁿ, |τ| = θ Hⁿ-a.e. on M'.
V7 (Good points.) For Hⁿ-a.e. a ∈ M': (i) Θ^{*n}(Hⁿ⌞M', a) ≤ 1 (SimonGMT simon_theorem_3_26_i); (ii) a is a Lebesgue point of τ for Hⁿ⌞M': H^n(M' ∩ B̄_r(a))⁻¹∫_{M'∩B̄_r(a)}|τ − τ(a)| dHⁿ → 0 (Mathlib VitaliFamily.ae_tendsto_average_norm_sub for the Besicovitch Vitali family of the finite measure Hⁿ⌞M', Besicovitch.tendsto_filterAt); (iii) Θⁿ_*(μ_Γ, a) ≥ η₀ and 0 < θ(a) = |τ(a)| < ∞. Fix such a, τ₀ := τ(a), θ₀ := θ(a). Since |θ − θ₀| ≤ |τ − τ₀|, μ_Γ(B_r(a)) ≤ θ₀Hⁿ(M' ∩ B_r(a)) + ∫_{M'∩B̄_r(a)}|τ − τ₀| = θ₀Hⁿ(M' ∩ B_r(a)) + o(rⁿ) (by (i), (ii)), and μ_Γ(B_r(a)) ≥ (η₀/2)ω_nrⁿ for small r by (iii), so Hⁿ(M' ∩ B_r(a)) ≥ (η₀/(4θ₀))ω_nrⁿ for small r.
V8 (Blow-ups.) Let λ_i ↓ 0 be any sequence, η_i := η_{a,λ_i}, Γ_i := η_{i#}Γ (T5) and μ_i := Hⁿ⌞η_i(M'). By T5 and the scaling of Hⁿ, Γ_i(ω) = ∫_{η_i(M')}⟨ω(y), τ(a + λ_iy)⟩ dHⁿ(y), and for every R > 0 and large i, (η₀/(4θ₀))ω_nRⁿ ≤ μ_i(B_R(0)) ≤ 2ω_nRⁿ. For ω with spt ω ⊆ B_R(0), |Γ_i(ω) − ∫⟨ω, τ₀⟩ dμ_i| ≤ |ω|_∞ λ_i^{−n}∫_{M'∩B_{λ_iR}(a)}|τ − τ₀| dHⁿ → 0 by V7(i),(ii). By T1 (on ℝ^P) a subsequence has μ_i → ν; then Γ_i ⇀ C, C(ω) := ∫⟨ω, τ₀⟩ dν. Properties: ν(B_R(0)) ≤ liminf μ_i(B_R(0)) ≤ ω_nRⁿΘ^{*n}(Hⁿ⌞M', a) ≤ ω_nRⁿ for every R > 0; ν(B̄_R(0)) ≥ limsup μ_i(B̄_R(0)) ≥ (η₀/(4θ₀))ω_nRⁿ > 0, so 0 ∈ spt ν; ∂C = lim ∂Γ_i = 0; a current Ξ = ζ₀ν' with constant n-vector ζ₀ has M_G(Ξ) = |ζ₀|ν'(G) (≤ is clear; for ≥ test with φβ₀, β₀ a unit covector with ⟨β₀, ζ₀⟩ = |ζ₀|, φ ∈ C_c^∞(G; [0,1]) ↑ 1_G), so μ_C = θ₀ν and |μ_{Γ_i}(G) − θ₀μ_i(G)| ≤ M_G(Γ_i − τ₀μ_i) → 0 for bounded open G; hence μ_{Γ_i} → θ₀ν in the sense of T1, and sup_i μ_{Γ_i}(B_R(0)) < ∞. By V4(iii) the Γ_i have (ISP), so by V4(ii) C has (ISP).
V9 (Invariance and simplicity.) For an (n−1)-covector α define v_α ∈ ℝ^P by ⟨v_α, w⟩ := ⟨w^♭ ∧ α, τ₀⟩ (w^♭ := ⟨w, ·⟩). For φ ∈ C_c^∞(ℝ^P), ∂C(φα) = C(dφ ∧ α) = ∫ Dφ·v_α dν = 0, so d/ds ∫φ(y + sv_α) dν(y) = 0 and ν is invariant under translations by multiples of v_α, hence by V₀ := span{v_α}. Linear algebra: τ₀ ∈ Λ_n(V₀): in an orthonormal basis e'_1, …, e'_P with V₀ = span(e'_1, …, e'_r), for an increasing multi-index I containing some i > r, ⟨e'^I, τ₀⟩ = ±⟨e'^i ∧ e'^{I∖i}, τ₀⟩ = ±⟨v_{e'^{I∖i}}, e'_i⟩ = 0; so τ₀ = Σ_{I⊆{1..r}}⟨e'^I, τ₀⟩e'_I and, τ₀ ≠ 0, r ≥ n. Growth: pick y₀ ∈ spt ν, m₀ := ν(B_1(y₀)) > 0; for large R the balls B_1(y₀ + v), v ∈ 2ℤ^r (coordinates in e'_1..e'_r) with |v| ≤ R/2, are disjoint, contained in B_R(0), at least c_rR^r in number and each of ν-measure m₀; so c_rm₀R^r ≤ ν(B_R(0)) ≤ ω_nRⁿ for all large R, forcing r ≤ n. Hence dim V₀ = n, Λ_n(V₀) is one-dimensional, and τ₀ = θ₀ v_1 ∧ ⋯ ∧ v_n for a suitably oriented orthonormal basis (v_i) of V₀ (|τ₀| = θ₀).
V10 (Structure of ν.) Write ℝ^P = V₀ ⊕ V₀^⊥. For bounded Borel B ⊆ V₀^⊥, A ↦ ν(A + B) (A ⊆ V₀ Borel) is a translation invariant, locally finite Borel measure on V₀ ≅ ℝⁿ, hence σ(B)·Lⁿ_{V₀} (Mathlib MeasureTheory.Measure.isAddLeftInvariant_eq_smul); σ is a locally finite measure on V₀^⊥ and ν = Lⁿ_{V₀} ⊗ σ (agreement on products, π-λ). By V5 applied to C (μ_C = θ₀ν), Θⁿ_*(ν, y) ≥ η₀/θ₀ for ν-a.e. y; for y = v + w, ν(B_r(y)) ≤ ω_nrⁿσ(B_r(w)), so σ({w}) = lim_r σ(B_r(w)) ≥ η₀/θ₀ for σ-a.e. w (the exceptional w form a σ-null set, since ν(B_1(0)∩V₀ + G) = ω_nσ(G)). Hence σ = Σ_i α_iδ_{w_i} with α_i ≥ η₀/θ₀ and {w_i} locally finite. ν(B_R(0)) = Σ_iα_iω_n(R² − |w_i|²)_+^{n/2} ≤ ω_nRⁿ; dividing by ω_nRⁿ and letting R → ∞ over finite subfamilies gives Σ_iα_i ≤ 1, so there are finitely many w_1, …, w_N, and some w_i = 0 because 0 ∈ spt ν = ⋃_i(V₀ + w_i).
V11 (Each α_i ≥ 1.) Fix a plane index i₀ and write α := α_{i₀}, w := w_{i₀}; the blow-up index is now k (Γ_k, μ_k, λ_k from V8); choose orthonormal coordinates with V₀ = ℝⁿ × {0} and τ₀ = θ₀e_1 ∧ ⋯ ∧ e_n; p : ℝ^P → ℝⁿ the projection; δ' := min_{j≠i₀}|w_j − w|/3 (δ' := 1 if N = 1); g := dist(·, V₀ + w) (1-Lipschitz); fix R > 0, Ω := p^{-1}(B_{3R}).
(a) The compact set A'' := Ω̄ ∩ {δ' ≤ g ≤ 2δ'} has ν(A'') = 0 (no plane V₀ + w_j meets it), so μ_{Γ_k}(A'') → 0 (V8, T1). By (SL) for Γ_k (∂Γ_k = 0) with f = g, G = Ω, and (MM) applied to F_k(t) := μ_{Γ_k}(Ω ∩ {δ' < g < t}) with ∫F_k' ≤ μ_{Γ_k}(A'') → 0, Fatou gives liminf_kF_k'(t) = 0 for a.e. t ∈ (δ', 2δ'); fix such t (with all F_k differentiable at t) and a subsequence with M_Ω(∂Z_k) → 0, Z_k := Γ_k⌞{g < t}. By T2 (ν({g = t}) = 0), Z_k ⇀ C⌞{g < t} = τ₀αHⁿ⌞(V₀ + w). (This also covers N = 1, with δ' := 1. Since n < P, V₀^⊥ ≠ {0}.)
(b) Projection. For b ∈ C_c^∞(B_{2R}) let Y_k(b dy) := ∫ b(p(x))⟨dy¹ ∧ ⋯ ∧ dyⁿ, ξ_{Z_k}(x)⟩ dμ_{Z_k}(x) (absolutely convergent: μ_{Z_k}(p^{-1}(spt b)) ≤ μ_{Γ_k}({g ≤ t} ∩ Ω) < ∞). Y_k ∈ 𝒟_n(B_{2R}) is a current with M(Y_k) ≤ μ_{Γ_k}({g ≤ t} ∩ Ω) (bounded in k) and, for an (n−1)-form γ on B_{2R}, ∂Y_k(γ) = Z_k(χ p^#dγ) = ∂Z_k(χp^#γ) (χ ∈ C_c^∞(Ω) equal to 1 near {g ≤ t} ∩ p^{-1}(spt γ), VO), so M_{B_{2R}}(∂Y_k) ≤ M_Ω(∂Z_k) → 0 (|p^#γ| = |γ ∘ p|). Moreover Y_k(b dy) → θ₀α∫ b dy (from Z_k ⇀ τ₀αHⁿ⌞(V₀ + w), testing with χ(b ∘ p)dy, where χ ∈ C_c^∞(Ω) is a fixed function equal to 1 on the compact set {g ≤ t} ∩ p^{-1}(B̄_{2R})).
(c) Density. By REP applied to Y_k in the open set B_{2R} ⊆ ℝⁿ (degree n, locally finite mass and boundary mass; this top-degree case is Simon 2.35), μ_{Y_k} ≪ Lⁿ, so Y_k(b dy) = ∫ b u_k dLⁿ with u_k ∈ L¹(B_{2R}) (Radon–Nikodym). The signed measure b ↦ Y_k(b dy) is the push-forward under p of ⟨dy, τ(a + λ_k·)⟩Hⁿ⌞(N_k ∩ Ω), N_k := η_k(M') ∩ {g < t} (V8), so u_k = 0 Lⁿ-a.e. outside E_k := toMeasurable(Lⁿ, p(N_k ∩ Ω)) (a measurable hull with Lⁿ(B ∩ E_k) = Lⁿ(B ∩ p(N_k ∩ Ω)) for Borel B; no measurability of p(N_k ∩ Ω) is needed, since |u_k|Lⁿ is the push-forward of a measure carried by N_k ∩ Ω and therefore vanishes on every Borel set disjoint from p(N_k ∩ Ω)).
(d) L¹ convergence. For 0 < s₀ < R and a mollifier φ_{s₀} on ℝⁿ: (u_k ∗ φ_{s₀})(x) = Y_k(φ_{s₀}(x − ·)dy) → θ₀α for each x ∈ B̄_R, uniformly in x (equicontinuity: |Y_k(φ_{s₀}(x − ·)dy) − Y_k(φ_{s₀}(x' − ·)dy)| ≤ |x − x'| Lip(φ_{s₀}) M(Y_k)). Further ∫_{B_R}|u_k − u_k ∗ φ_{s₀}| ≤ s₀ M_{B_{2R}}(∂Y_k): for the smooth function v := u_k ∗ φ_ϑ (0 < ϑ small), ∫_{B_R}|v(x) − v(x − z)| dx ≤ |z|∫_{B_{R+|z|}}|∇v| (fundamental theorem of calculus along segments), and ∫_{B_{R+s₀}}|∇v| ≤ M_{B_{2R}}(∂Y_k) because for every smooth compactly supported vector field G on B_{R+s₀} with |G| ≤ 1, ∫∇v·G = −∫u_k div(φ̌_ϑ ∗ G) = −Y_k(div(φ̌_ϑ ∗ G)dy) = −∂Y_k(Σ_j(φ̌_ϑ ∗ G)_jε_j) with |Σ_j(φ̌_ϑ ∗ G)_jε_j| ≤ 1 (ε_j := (−1)^{j−1}dy¹∧⋯∧dy^{j−1}∧dy^{j+1}∧⋯∧dyⁿ); average against φ_{s₀}(z) and let ϑ ↓ 0 (v → u_k in L¹_loc by continuity of translations). Hence ∫_{B_R}|u_k − θ₀α| ≤ s₀ M_{B_{2R}}(∂Y_k) + ω_nRⁿ sup_{B_R}|u_k ∗ φ_{s₀} − θ₀α| → 0 as k → ∞.
(e) Conclusion. Lⁿ(B_R ∖ E_k) ≤ (θ₀α)⁻¹∫_{B_R}|u_k − θ₀α| → 0. And Lⁿ(B_R ∩ E_k) = Lⁿ(B_R ∩ p(N_k ∩ Ω)) ≤ Hⁿ(N_k ∩ p^{-1}(B_R)) (p is 1-Lipschitz, Hⁿ = Lⁿ on ℝⁿ) ≤ μ_k(A'), A' := {g ≤ t} ∩ p^{-1}(B̄_R) compact, and limsup_k μ_k(A') ≤ ν(A') = αω_nRⁿ (only the plane V₀ + w meets A' since t < 2δ' < 3δ'). Therefore ω_nRⁿ ≤ αω_nRⁿ, i.e. α_{i₀} ≥ 1.
V12 (Approximate tangent plane.) By V10–V11, 1 ≥ Σα_i ≥ N, so N = 1, α_1 = 1, w_1 = 0 and ν = Hⁿ⌞V₀. V₀ is determined by τ₀ alone, so every sequence λ_i ↓ 0 has a subsequence with Hⁿ⌞η_{a,λ_i}(M') → Hⁿ⌞V₀; hence ∫_{η_{a,λ}(M')} f dHⁿ → ∫_{V₀} f dHⁿ as λ → 0⁺ for every f ∈ C_c(ℝ^P), i.e. HasApproximateTangentSpaceAt n M' a V₀, and τ₀/θ₀ = v_1 ∧ ⋯ ∧ v_n is a unit orientation of V₀ (IsUnitOrientationOf). This holds for Hⁿ-a.e. a ∈ M'. The map a ↦ V₀(a) is Borel (the projection onto the plane of the unit simple n-vector τ(a)/θ(a) is a polynomial in its coordinates).
V13 (Rectifiability; Simon Ch. 3, 1.6 “⇐”.) Let A ⊆ M' be Borel; then μ := Hⁿ⌞A is finite and, by IMC(a), A has approximate tangent space P_x := V₀(x) at μ-a.e. x. Claim: there are finitely many Lipschitz F_k : ℝⁿ → ℝ^P with μ(ℝ^P ∖ ⋃F_k(ℝⁿ)) ≤ μ(ℝ^P)/2. Iterating with A ∖ ⋃F_k(ℝⁿ) (Borel, as the F_k(ℝⁿ) are σ-compact) shows that M' is covered by countably many Lipschitz images up to an Hⁿ-null set, i.e. M' is countably n-rectifiable.
Proof of the claim (Simon, with the corrected ε). For x with P_x: with π_x := P_x^⊥ and X_α(π, x) := {y : dist(y − x, π) < α|y − x|}, the definition of P_x (testing with continuous functions approximating 1_{B_1} and 1_{X̄_{1/2}(π_x,0) ∩ B̄_1}, whose boundaries are Hⁿ⌞P_x-null, and X̄_{1/2}(π_x, 0) ∩ P_x = {0}) gives (5) μ(B_ρ(x))/(ω_nρⁿ) → 1 and (6) μ(X_{1/2}(π_x, x) ∩ B_ρ(x))/(ω_nρⁿ) → 0. By Lusin's theorem (SimonGMT Chapter01 exists_isClosed_continuousOn_of_measurable, applied to the finitely many coordinates of the projection matrix of P_x, a Borel function of x by V12, and intersecting the closed sets obtained; μ finite) take a closed F ⊆ A with μ(ℝ^P ∖ F) ≤ μ(ℝ^P)/4 on which x ↦ P_x is continuous and (5), (6) hold; the functions f_k(x) := inf_{ρ<1/k} μ(B_ρ(x))/(ω_nρⁿ) and q_k(x) := sup_{ρ<1/k} μ(X_{1/2}(π_x, x) ∩ B_ρ(x))/(ω_nρⁿ) are Borel on F (countable inf/sup over rational ρ of semicontinuous functions, by left continuity in ρ and continuity of x ↦ π_x on F), f_k → 1 and q_k → 0 on F; by Egorov (Mathlib MeasureTheory.tendstoUniformlyOn_of_ae_tendsto) choose a closed E ⊆ F with μ(F ∖ E) ≤ μ(ℝ^P)/4 and uniform convergence on E. With ε := 2^{−1}16^{−n} there is δ > 0 such that μ(B_ρ(x)) ≥ (1 − ε)ω_nρⁿ and μ(X_{1/2}(π_x, x) ∩ B_ρ(x)) ≤ εω_nρⁿ for x ∈ E, ρ < δ. Choose ℓ-dimensional subspaces π_1, …, π_N (ℓ := P − n) such that every ℓ-subspace π has ‖p_π − p_{π_j}‖ < 1/16 for some j, and E_j := {x ∈ E : ‖p_{π_j} − p_{π_x}‖ < 1/16}. Then (10): X_{1/4}(π_j, x) ∩ E_j ∩ B_{δ/2}(x) = ∅ for x ∈ E_j (x itself never lies in X_{1/4}(π_j, x), the defining inequality being strict). Otherwise there is y ∈ X_{1/4}(π_j, x) ∩ E_j with σ := |y − x| ∈ (0, δ/2); for z ∈ B_{σ/8}(y), dist(z − x, π_x) ≤ dist(y − x, π_j) + σ/16 + σ/8 < 7σ/16 ≤ |z − x|/2, so B_{σ/8}(y) ⊆ X_{1/2}(π_x, x) ∩ B_{2σ}(x), whence (1 − ε)ω_n(σ/8)ⁿ ≤ μ(B_{σ/8}(y)) ≤ εω_n(2σ)ⁿ, i.e. (1 − ε)8^{−n} ≤ ε2ⁿ = 8^{−n}/2, a contradiction. By (10), for any x₀ ∈ ℝ^P the orthogonal projection p_j onto π_j^⊥ ≅ ℝⁿ satisfies |p_j(y) − p_j(x)| ≥ |y − x|/4 for x, y ∈ E_j ∩ B_{δ/4}(x₀) (then |x − y| < δ/2); so E_j ∩ B_{δ/4}(x₀) is the graph over p_j(E_j ∩ B_{δ/4}(x₀)) of a Lipschitz map into π_j, which extends to a Lipschitz map on π_j^⊥ (Mathlib LipschitzOnWith.extend_pi componentwise in an orthonormal basis of π_j; the constant changes by a factor √ℓ), i.e. E_j ∩ B_{δ/4}(x₀) ⊆ F(ℝⁿ) for a Lipschitz F. E is compact (closed and bounded), so finitely many balls B_{δ/4}(x₀) cover E, and the finitely many pieces E_j ∩ B_{δ/4}(x₀) cover E, and μ(ℝ^P ∖ ⋃F_k(ℝⁿ)) ≤ μ(ℝ^P ∖ E) ≤ μ(ℝ^P)/2. ∎
V14 (Integrality; replaces Simon (7)–(10).) At a as in V12, C = τ₀Hⁿ⌞V₀ = θ₀[[V₀]] with [[V₀]] oriented by v_1 ∧ ⋯ ∧ v_n, and C has (ISP) (V8). For f(y) := ⟨y, v_1⟩ (1-Lipschitz) and every t, the divergence theorem in V₀ ≅ ℝⁿ on the half-space {f < t} gives ∂(C⌞{f < t}) = θ₀[[V₀ ∩ {f = t}]] with orientation ±v_2 ∧ ⋯ ∧ v_n (for n = 1: ±θ₀δ_{tv_1}). For a.e. t this current is IM; by (MR) its mass measure is θ₀H^{n−1}⌞(V₀ ∩ {f = t}) and also θ'H^{n−1}⌞M_t for an IMRep (M_t, θ', ·) with θ' ≥ 1 integer; uniqueness of Radon–Nikodym densities on the plane gives θ₀ = θ' a.e. on a set of positive measure, so θ₀ ∈ ℤ (for n = 1, θ₀ = θ'(tv_1)). Hence θ(a) is a positive integer for Hⁿ-a.e. a ∈ M'.
V15 (Conclusion of CL*.) Let M'' ⊆ M' be a Borel set with Hⁿ(M' ∖ M'') = 0 such that at every point of M'' V12 and V14 hold and θ is a positive integer (Borel regularity; the sets where these fail are null); put mult := the ℕ-valued Borel function equal to θ on M'' and 0 elsewhere (so mult ≥ 1 at every point of the carrier), orient := ξ_Γ = τ/θ. Then (M'', θ, ξ_Γ) is an IMRep in ℝ^P: M'' Borel and countably n-rectifiable (V13), θ ≥ 1, ∫θ dHⁿ = M(Γ) < ∞, ξ_Γ a.e. strongly measurable for Hⁿ⌞M'' (it is for μ_Γ = θHⁿ⌞M', and θ > 0 on M'' makes the two measures mutually absolutely continuous on M''), and for a.e. a ∈ M'' the approximate tangent space of M'' at a is V₀(a) (V12 and IMC(a)), oriented by ξ_Γ(a). It represents Γ by V6. So Γ is IM, hence T = Γ − (0 − Y) is IM (IMC(c)), which proves (CL*) and hence, by V2, CL(n). ∎

This completes the induction (Parts II–V): for every d ∈ ℕ, CL(d) holds in every ambient dimension P' > d and BR(d) holds in every ambient dimension P' > d + 1.

Part VI. The stated case. Let P, m ∈ ℕ with m + 1 < P, and let T_j, T ∈ 𝒟_{m+1}(ℝ^P) be as in the statement. Take U := ℝ^P (open) and d := m + 1. If W ⊂⊂ ℝ^P then closure(W) is compact, hence W is bounded, so the hypothesis gives sup_j (M_W(T_j) + M_W(∂T_j)) < ∞; since d = m + 1 ≥ 1, M_W(∂T_j) is exactly the boundary term boundaryMassOn T_j W of CL(d). Every T_j is IM and T_j ⇀ T in ℝ^P. The hypothesis m + 1 < P is exactly the range condition d < P' of CL(d) for d := m + 1 and P' := P. Hence CL(m + 1), applied with P' := P and U := ℝ^P, shows that T is integer multiplicity. ∎

Remark (reuse; not a proof step). The DAG declaration cmc_closure_and_boundary_rectifiability (node root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1; unaccepted and reserved by another parent at the time of this decomposition, hence not a dependency here) has as first conjunct (CL) the closure theorem in every open U ⊆ ℝ^P and every degree. With d := m + 1 and U := ℝ^P it implies the present statement directly: an open W with W ⊂⊂ ℝ^P (CompactlyContained) has compact, hence bounded, closure, so the hypothesis of the present statement gives the required bound, and boundaryMassOn of an (m+1)-current is the mass of its boundary. This three-line derivation was checked with lake env lean (axioms propext, Classical.choice, Quot.sound). If that declaration has been comparator-accepted when this node is decomposed, a decomposition may reuse it verbatim with its identical frozen type instead of re-proving Parts I–VI.

## Key steps

1. Joint induction in positive codimension: CL(d) in ambient dimensions P > d and BR(d) in ambient dimensions P > d + 1. CL(0) holds directly (finite point masses). BR(d) follows from CL(d) by localization by slicing and approximation by the deformation theorem in degree d + 1 < P. CL(d+1) follows from CL(d) and BR(d). The deformation theorem is used only in positive degree and positive codimension.
2. Localization (Simon 8.3(1)) by slicing and restriction convergence; IM is a local property; reduction to compact supports in ℝ^P.
3. Reduction to the cycle Γ = T − Y, with ∂Y = ∂T filled by the isoperimetric inequality (deformation theorem in degree n − 1 < P) or by segments; the IM slice property passes to weak limits, so Γ has it.
4. Simon 8.2 lower density bound Θⁿ_* ≥ η₀ via isoperimetric fillings, the cone inequality and Besicovitch covering.
5. White-type blow-up at Lebesgue points: limits are τ₀ν with ν invariant along an n-plane V₀, τ₀ simple, ν a finite sum of parallel planes, each of multiplicity ≥ 1 by a projection/mollification argument; so the tangent measure is Hⁿ⌞V₀.
6. Approximate tangent planes a.e. give rectifiability (Simon Ch. 3, 1.6 ⇐, corrected constant); slices give integer multiplicity; assemble the IMRep.
7. Specialization: m + 1 < P is exactly the range condition of CL(m + 1) in ℝ^P. Every W ⊂⊂ ℝ^P is bounded, so the hypothesis of the statement is that of CL(m + 1), which yields that T is integer multiplicity.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (mode local-project, project b4d606db, mathlib 25730c7c); cmp workspace GMT/Ch07/Contract.lean local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean; diff GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `rg -n -i 'federer|fleming|deformation|closure theorem|weak.*compact' local-references/123e8435b4a2469b/project/GMT`
- `sed -n 225,300p local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `rg -n 'theorem extraction_forall_of_eventually|theorem setIntegral_eq_of_subset_of_forall_sdiff_eq_zero|lemma isMulLeftInvariant_eq_smul|instance instSeparableSpace|theorem lintegral_liminf_le|theorem lintegral_lintegral_swap|theorem exists_disjoint_closedBall_covering_ae|theorem ae_tendsto_average_norm_sub|theorem LipschitzOnWith.extend_pi|theorem tendstoUniformlyOn_of_ae_tendsto' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `grep -n 'def massAdmissibleOn|def GeometricCurrentOn.massOn|def GeometricCurrentOn.mass|massOn_mono|le_massOn' simongmt/Poincare/SimonGMT/Chapter06/Mass.lean; grep -n 'structure GeometricCurrentOn|TestFormOnConverges|WeaklyConvergesOn|GeometricCurrentOn.ext|GeometricCurrentOn.zero_apply|exteriorDerivativeTestOn|GeometricCurrentOn.boundary_apply' simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `grep -rn 'theorem simon_theorem_4_16_compact_metrizable|theorem simon_theorem_3_3|theorem simon_theorem_3_26_i|theorem exists_isClosed_continuousOn_of_measurable|theorem countablyRectifiable_of_measure_zero' simongmt/Poincare`
- `python3 -I over dag.json: lean_name, lean_statement, status and candidate_commit of rsd_cmr_imrep_restrict, dtc_imrep_current, cmc_massOn_eq_imRep_measure, covectorEuclideanNorm_gram_bounds, cmc_imRep_locality_restrict_sub, dtc_vanish_off_support, cmc_closure_and_boundary_rectifiability and the accepted cmcs_/lcmp_/cmr_ helpers; prefix search dtc_bc_tc_ (902 nodes)`
- `git cat-file -t <candidate>; git show <candidate>:GMT/Ch07/Submission.lean | grep 'theorem Submission.<name>'; git log --all -S dtc_bc_tc_`
- `python3 -I: verifier/gmt-compare.py contract_scope + child_modules (contract mode) and verifier/lean_contract.py validate_lean_statement on the 11 types`
- `lake env lean /tmp/tc3/challenges/Challenge_<key>.lean (11 files) and /tmp/tc3/check/{Types,Parse,Assembly,TruncAssembly,ClosureFromCmc}.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/Unique.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/ContinuousMap/SecondCountableSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Egorov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/CompactMetrizableCompactness.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/HausdorffDensityBounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-truncated-compactness-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-truncated-compactness-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-truncated-compactness-a1/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-truncated-compactness-a1/decomposition-review-receipt-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/cluster-state/logs/gmt-ch07/03a1fcac808347a1bd64e0507e57e08b.log`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/tc3/check/Assembly.lean`
- `/tmp/tc3/check/TruncAssembly.lean`
- `/tmp/tc3/check/ClosureFromCmc.lean`
- `/tmp/tc3/check/Types.lean`
- `/tmp/tc3/check/Parse.lean`

The snapshot (mode local-project; project b4d606db, Mathlib 25730c7c) has a Ch07 Contract.lean that is byte-identical to the workspace Contract.lean and Submission.lean. Its Ch06 contract states FedererFlemingCompactness, SlicingTheorem and DeformationTheorem (1 ≤ ℓ, i.e. positive codimension) only as Props under a sorry main_theorem, so no proved Federer–Fleming, slicing or deformation theorem can be reused. The DAG node cmc_closure_and_boundary_rectifiability is unaccepted, which is why the closure child remains a new obligation. Every Mathlib lemma named in the children's proofs exists in the snapshot Mathlib (isAddLeftInvariant_eq_smul is the to_additive form of isMulLeftInvariant_eq_smul), and every cited SimonGMT theorem exists in the pinned library. The six reused declarations are accepted with identical frozen types and are present in their candidate commits. All eleven types elaborate in comparator contract scope. The parent assembly, the truncation assembly and the closure-from-cmc derivation compile using only propext, Classical.choice and Quot.sound. No dtc_bc_tc_ name occurs anywhere else.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
