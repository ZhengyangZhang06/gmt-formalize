<!-- theorem-id: gmt-ch07/root.compactness_of_minimizing_currents-a1.local_comparison-a1.good_slice_level-a1 -->

## Theorem `Submission.lcmp_exists_good_slice_level`

Let P ∈ ℕ, let (ν_j)_{j∈ℕ} and (κ_j)_{j∈ℕ} be measures on ℝ^P, f : ℝ^P → ℝ Borel measurable, a < b real and A := {x : a < f(x) < b}. Assume ν_j(A) < ∞ for every j, ν_j(A) → 0 as j → ∞, and κ_j(A) < ∞ for every j. Then there are t ∈ (a, b) and a strictly increasing φ : ℕ → ℕ such that (i) κ_j({f = t}) = 0 for every j; (ii) D_j(t) < ∞ for every j; (iii) D_{φ(j)}(t) → 0 as j → ∞; where D_j(t) := liminf_{h → 0, h > 0} ofReal(h⁻¹)·ν_j({x : t − h < f(x) < t}) ∈ [0, ∞] (liminf along the filter 𝓝[>] 0).

Node: `root.compactness_of_minimizing_currents-a1.local_comparison-a1.good_slice_level-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4282

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.lcmp_exists_good_slice_level`

```lean
∀ (P : ℕ) (ν κ : ℕ → Measure (Euclid P)) (f : Euclid P → ℝ) (a b : ℝ), Measurable f → a < b → (∀ j, ν j {x | a < f x ∧ f x < b} < ∞) → Tendsto (fun j => ν j {x | a < f x ∧ f x < b}) atTop (𝓝 0) → (∀ j, κ j {x | a < f x ∧ f x < b} < ∞) → ∃ t ∈ Ioo a b, ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ j, κ j {x | f x = t} = 0) ∧ (∀ j, liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ν j {x | t - h < f x ∧ f x < t}) (𝓝[>] 0) < ∞) ∧ Tendsto (fun j => liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ν (φ j) {x | t - h < f x ∧ f x < t}) (𝓝[>] 0)) atTop (𝓝 0)
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

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.local_comparison-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.local_comparison-a1.good_slice_level-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 5 (choice of α and φ; Simon 7.2.4 (3)–(5), chapter-07.txt lines 192–205: “By the slicing theory (and in particular by 4.5 of Ch. 6) we can choose 0 < α < 1 and a subsequence ... We can also of course choose α to be such that (5) ...”). The parent applies this lemma with ν_j := μ_{R_j}, κ_j := μ_{T_j}, f := −ψ and (a, b) := (−1, 0), so that A = {0 < ψ < 1}, {t − h < f < t} = {α < ψ < α + h} and {f = t} = {ψ = α} for α := −t ∈ (0, 1); the slicing sibling bounds M_{W₀}(P_{j,α}) by L·D_j(t).
Detail (departure in the choice of the majorant). The parent majorizes the difference quotients by −L H_j′ with H_j(s) = μ_{R_j}(W₀ ∩ {s < ψ < 1}) and bounds ∫ −H_j′ by Mathlib MonotoneOn.intervalIntegral_deriv_mem_uIcc; that lemma is not in the import closure of the frozen contract. We use instead the sequential lower difference quotient G_j below, whose integral bound follows from Tonelli's theorem; the remainder of the argument (Fatou's lemma, countably many atoms, choice of the level and of the subsequence) is the parent's.

All quantities lie in [0, ∞] (0·∞ = 0); λ is Lebesgue measure on ℝ and “a.e.” refers to λ.

1. Measurability. Since f is Borel, A, the level sets {f = s} and the sets {t − h < f < t} are Borel.
2. Pushforward. Let ρ_j be the image of ν_j⌞A under f: ρ_j(B) = ν_j(f⁻¹(B) ∩ A) for Borel B ⊆ ℝ. Then ρ_j(ℝ) = ν_j(A) < ∞, so ρ_j is a finite Borel measure on ℝ.
3. Tonelli. For c ∈ ℝ let S_c := {(s, y) ∈ ℝ² : s − c < y < s}, a Borel set. Its sections are {y : (s, y) ∈ S_c} = (s − c, s) and {s : (s, y) ∈ S_c} = (y, y + c). Hence s ↦ ρ_j((s − c, s)) is Borel (measurability of sections of a product set, Mathlib measurable_measure_prodMk_left), and computing (λ × ρ_j)(S_c) in both orders (Measure.prod_apply, Measure.prod_apply_symm) gives ∫ ρ_j((s − c, s)) dλ(s) = ∫ λ((y, y + c)) dρ_j(y) = ofReal(c)·ρ_j(ℝ) = ofReal(c)·ν_j(A).
4. Majorants. For k ∈ ℕ let h_k := 1/(k + 1) and F_{j,k}(s) := (k + 1)·ρ_j((s − h_k, s)). By step 3, F_{j,k} is Borel and ∫ F_{j,k} dλ = (k + 1)·ofReal(h_k)·ν_j(A) = ν_j(A). Let G_j(s) := liminf_{k→∞} F_{j,k}(s), a Borel function. Fatou's lemma gives ∫ G_j dλ ≤ liminf_k ∫ F_{j,k} dλ = ν_j(A) < ∞; hence G_j < ∞ a.e., and, intersecting countably many full-measure sets, a.e. s satisfies G_j(s) < ∞ for every j.
5. Fatou in j. H(s) := liminf_{j→∞} G_j(s) is Borel and ∫ H dλ ≤ liminf_j ∫ G_j dλ ≤ liminf_j ν_j(A) = 0, because ν_j(A) → 0. Hence H = 0 a.e.
6. Atoms. For each j the measure κ_j⌞A is finite. The level sets {f = s}, s ∈ ℝ, are pairwise disjoint, so (κ_j⌞A)({f = s}) > 0 for at most countably many s (Mathlib Measure.countable_meas_level_set_pos). Countable sets are λ-null, so for a.e. s: (κ_j⌞A)({f = s}) = 0 for every j.
7. The level. λ((a, b)) = b − a > 0. By steps 4–6, a.e. s ∈ (a, b) satisfies H(s) = 0, G_j(s) < ∞ for every j, and (κ_j⌞A)({f = s}) = 0 for every j. A full-measure subset of a set of positive measure is nonempty, so there is t ∈ (a, b) with these three properties.
8. (i). Since t ∈ (a, b), {f = t} ⊆ A, so κ_j({f = t}) = κ_j({f = t} ∩ A) = (κ_j⌞A)({f = t}) = 0.
9. D_j(t) ≤ G_j(t). Put u_j(h) := ofReal(h⁻¹)·ν_j({t − h < f < t}). The sequence h_k tends to 0 through positive values, i.e. along atTop it tends to 0 within (0, ∞); a liminf along the finer filter (the image of atTop under k ↦ h_k) is at least the liminf along 𝓝[>] 0, so D_j(t) ≤ liminf_k u_j(h_k). For all k with h_k < t − a (all large k, since h_k → 0 < t − a): a < t − h_k and t < b give {t − h_k < f < t} ⊆ A, so ν_j({t − h_k < f < t}) = ν_j(f⁻¹((t − h_k, t)) ∩ A) = ρ_j((t − h_k, t)); and ofReal(h_k⁻¹) = k + 1. Hence u_j(h_k) = F_{j,k}(t) for all large k, and liminf_k u_j(h_k) = G_j(t). Therefore D_j(t) ≤ G_j(t).
10. (ii). D_j(t) ≤ G_j(t) < ∞ by steps 7 and 9.
11. (iii). liminf_j G_j(t) = H(t) = 0, so for every n ∈ ℕ there are infinitely many j with G_j(t) < 1/(n + 1). Choose φ(0) < φ(1) < ⋯ inductively with G_{φ(n)}(t) < 1/(n + 1) (Mathlib extraction_forall_of_frequently). Then 0 ≤ D_{φ(n)}(t) ≤ G_{φ(n)}(t) < 1/(n + 1) → 0. ∎

Appendix (verified Lean realization of the numbered proof above; not part of the proof). The declaration below was compiled in this decomposition session with Lean v4.35.0-rc3, Mathlib 25730c7c and SimonGMT 2b366308, placed after `import GMT.Ch07.Submission` in the child comparator scope (inside `namespace GMT.Ch07` with the frozen contract's `open` commands, after its `noncomputable section ... end`). `exact Submission.lcmp_exists_good_slice_level` closes the frozen type, and `#print axioms` reports only propext, Classical.choice and Quot.sound. In the code, `ρ j` is the pushforward measure ρ_j of step 2 and `D j` is the majorant G_j of steps 4–11.

```lean
theorem Submission.lcmp_exists_good_slice_level : ∀ (P : ℕ) (ν κ : ℕ → Measure (Euclid P)) (f : Euclid P → ℝ) (a b : ℝ), Measurable f → a < b → (∀ j, ν j {x | a < f x ∧ f x < b} < ∞) → Tendsto (fun j => ν j {x | a < f x ∧ f x < b}) atTop (𝓝 0) → (∀ j, κ j {x | a < f x ∧ f x < b} < ∞) → ∃ t ∈ Ioo a b, ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ j, κ j {x | f x = t} = 0) ∧ (∀ j, liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ν j {x | t - h < f x ∧ f x < t}) (𝓝[>] 0) < ∞) ∧ Tendsto (fun j => liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ν (φ j) {x | t - h < f x ∧ f x < t}) (𝓝[>] 0)) atTop (𝓝 0) := by
  intro P ν κ f a b hf hab hνfin hνlim hκfin
  obtain ⟨A, hA⟩ : ∃ A : Set (Euclid P), A = {x | a < f x ∧ f x < b} := ⟨_, rfl⟩
  rw [← hA] at hνfin hνlim hκfin
  have hAm : MeasurableSet A := by
    rw [hA]
    exact (measurableSet_lt measurable_const hf).inter (measurableSet_lt hf measurable_const)
  -- Step 1: push the restricted measures forward to the line
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℕ → Measure ℝ, ρ = fun j => ((ν j).restrict A).map f := ⟨_, rfl⟩
  have hρapp : ∀ j (s : Set ℝ), MeasurableSet s → ρ j s = ν j (f ⁻¹' s ∩ A) := by
    intro j s hs
    rw [hρ, Measure.map_apply hf hs, Measure.restrict_apply (hf hs)]
  have hρuniv : ∀ j, ρ j univ = ν j A := by
    intro j
    rw [hρapp j univ MeasurableSet.univ, preimage_univ, univ_inter]
  have hρfin : ∀ j, IsFiniteMeasure (ρ j) := fun j => ⟨by rw [hρuniv]; exact hνfin j⟩
  -- Step 2: Tonelli for the strips
  have hSm : ∀ c : ℝ, MeasurableSet {p : ℝ × ℝ | p.1 - c < p.2 ∧ p.2 < p.1} := fun c =>
    (measurableSet_lt (measurable_fst.sub_const c) measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_fst)
  have hsec : ∀ c t : ℝ, Prod.mk t ⁻¹' {p : ℝ × ℝ | p.1 - c < p.2 ∧ p.2 < p.1} = Ioo (t - c) t := by
    intro c t
    ext y
    simp [mem_Ioo]
  have hsec' : ∀ c y : ℝ,
      (fun t => (t, y)) ⁻¹' {p : ℝ × ℝ | p.1 - c < p.2 ∧ p.2 < p.1} = Ioo y (y + c) := by
    intro c y
    ext t
    simp only [mem_preimage, mem_ofPred_eq, mem_Ioo]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have hmeasF : ∀ j (c : ℝ), Measurable fun t : ℝ => ρ j (Ioo (t - c) t) := by
    intro j c
    have := hρfin j
    have := measurable_measure_prodMk_left (ν := ρ j) (hSm c)
    simpa only [hsec] using this
  have hTon : ∀ j (c : ℝ), ∫⁻ t, ρ j (Ioo (t - c) t) = ENNReal.ofReal c * ν j A := by
    intro j c
    have := hρfin j
    have h1 := Measure.prod_apply (μ := (volume : Measure ℝ)) (ν := ρ j) (hSm c)
    have h2 := Measure.prod_apply_symm (μ := (volume : Measure ℝ)) (ν := ρ j) (hSm c)
    simp only [hsec, hsec', Real.volume_Ioo, add_sub_cancel_left] at h1 h2
    rw [← h1, h2, lintegral_const, hρuniv]
  -- Step 3: the sequential majorants D_j and their integrals
  have hFm : ∀ j (k : ℕ),
      Measurable fun t : ℝ => ((k : ℝ≥0∞) + 1) * ρ j (Ioo (t - 1 / ((k : ℝ) + 1)) t) :=
    fun j k => (hmeasF j _).const_mul _
  have hcancel : ∀ k : ℕ, ((k : ℝ≥0∞) + 1) * ENNReal.ofReal (1 / ((k : ℝ) + 1)) = 1 := by
    intro k
    have hk : ENNReal.ofReal ((k : ℝ) + 1) = (k : ℝ≥0∞) + 1 := by
      rw [ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_natCast,
        ENNReal.ofReal_one]
    rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity), hk,
      ENNReal.mul_inv_cancel (by simp) (by simp)]
  have hFint : ∀ j (k : ℕ),
      ∫⁻ t, ((k : ℝ≥0∞) + 1) * ρ j (Ioo (t - 1 / ((k : ℝ) + 1)) t) = ν j A := by
    intro j k
    rw [lintegral_const_mul _ (hmeasF j _), hTon j, ← mul_assoc, hcancel, one_mul]
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℝ → ℝ≥0∞, D = fun j t =>
      liminf (fun k : ℕ => ((k : ℝ≥0∞) + 1) * ρ j (Ioo (t - 1 / ((k : ℝ) + 1)) t)) atTop :=
    ⟨_, rfl⟩
  have hDm : ∀ j, Measurable (D j) := fun j => by
    rw [hD]
    exact Measurable.liminf (hFm j)
  have hDint : ∀ j, ∫⁻ t, D j t ≤ ν j A := by
    intro j
    rw [hD]
    calc ∫⁻ t, liminf (fun k : ℕ => ((k : ℝ≥0∞) + 1) * ρ j (Ioo (t - 1 / ((k : ℝ) + 1)) t)) atTop
        ≤ liminf (fun k : ℕ => ∫⁻ t, ((k : ℝ≥0∞) + 1) * ρ j (Ioo (t - 1 / ((k : ℝ) + 1)) t))
          atTop := lintegral_liminf_le (hFm j)
      _ = ν j A := by simp only [hFint, liminf_const]
  -- Step 4: Fatou in j
  have hHm : Measurable fun t => liminf (fun j => D j t) atTop := Measurable.liminf hDm
  have hHint : ∫⁻ t, liminf (fun j => D j t) atTop = 0 := by
    refine le_antisymm ?_ zero_le
    calc ∫⁻ t, liminf (fun j => D j t) atTop ≤ liminf (fun j => ∫⁻ t, D j t) atTop :=
          lintegral_liminf_le hDm
      _ ≤ liminf (fun j => ν j A) atTop := liminf_le_liminf (Eventually.of_forall hDint)
      _ = 0 := hνlim.liminf_eq
  have hH0 : ∀ᵐ t, liminf (fun j => D j t) atTop = 0 :=
    ((lintegral_eq_zero_iff hHm).1 hHint).mono fun t ht => ht
  have hDfin : ∀ᵐ t, ∀ j, D j t < ∞ :=
    ae_all_iff.2 fun j => ae_lt_top (hDm j) ((hDint j).trans_lt (hνfin j)).ne
  -- Step 5: atoms of κ_j on the level sets
  have hatomsAE : ∀ᵐ s : ℝ, ∀ j, (κ j).restrict A {x | f x = s} = 0 := by
    rw [ae_all_iff]
    intro j
    have : IsFiniteMeasure ((κ j).restrict A) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hκfin j⟩
    have hc := Measure.countable_meas_level_set_pos (μ := (κ j).restrict A) hf
    filter_upwards [hc.ae_notMem (volume : Measure ℝ)] with s hs
    simp only [not_lt, nonpos_iff_eq_zero] at hs
    exact hs
  -- Step 6: the good level
  have hIoo : volume (Ioo a b) ≠ 0 := by
    rw [Real.volume_Ioo]
    simpa using hab
  have : (ae (volume.restrict (Ioo a b))).NeBot :=
    ae_neBot.2 (by rw [Ne, Measure.restrict_eq_zero]; exact hIoo)
  have hgood : ∀ᵐ s ∂(volume.restrict (Ioo a b)), s ∈ Ioo a b ∧
      liminf (fun j => D j s) atTop = 0 ∧ (∀ j, D j s < ∞) ∧
      ∀ j, (κ j).restrict A {x | f x = s} = 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hH0,
      ae_restrict_of_ae hDfin, ae_restrict_of_ae hatomsAE] with s h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨t, ht, hHt, hDt, hκt⟩ := hgood.exists
  -- Step 7: the one-sided difference quotients are dominated by D_j(t)
  have hlink : ∀ j, liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ν j {x | t - h < f x ∧ f x < t})
      (𝓝[>] 0) ≤ D j t := by
    intro j
    have hseq : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall fun k => ?_⟩
      show (0 : ℝ) < 1 / ((k : ℝ) + 1)
      positivity
    have hle := liminf_le_liminf_of_le
      (u := fun h : ℝ => ENNReal.ofReal h⁻¹ * ν j {x | t - h < f x ∧ f x < t}) hseq
    refine hle.trans (le_of_eq ?_)
    rw [hD]
    show liminf ((fun h : ℝ => ENNReal.ofReal h⁻¹ * ν j {x | t - h < f x ∧ f x < t}) ∘
      fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop = _
    apply liminf_congr
    have hsmall : ∀ᶠ k : ℕ in atTop, 1 / ((k : ℝ) + 1) < t - a :=
      tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds (sub_pos.2 ht.1))
    filter_upwards [hsmall] with k hk
    simp only [Function.comp_apply]
    have h1 : ENNReal.ofReal (1 / ((k : ℝ) + 1))⁻¹ = (k : ℝ≥0∞) + 1 := by
      rw [one_div, inv_inv, ENNReal.ofReal_add (by positivity) zero_le_one,
        ENNReal.ofReal_natCast, ENNReal.ofReal_one]
    have h2 : ν j {x | t - 1 / ((k : ℝ) + 1) < f x ∧ f x < t} =
        ρ j (Ioo (t - 1 / ((k : ℝ) + 1)) t) := by
      rw [hρapp j _ measurableSet_Ioo]
      congr 1
      ext x
      simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Ioo, hA]
      constructor
      · rintro ⟨h3, h4⟩
        refine ⟨⟨h3, h4⟩, ?_, ?_⟩ <;> linarith [ht.2]
      · rintro ⟨⟨h3, h4⟩, -⟩
        exact ⟨h3, h4⟩
    rw [h1, h2]
  -- Step 8: the subsequence
  have hfreq : ∀ n : ℕ, ∃ᶠ j in atTop, D j t < ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro n
    refine frequently_lt_of_liminf_lt (by isBoundedDefault) ?_
    rw [hHt]
    exact ENNReal.inv_pos.2 (by simp)
  obtain ⟨φ, hφ, hφlt⟩ := extraction_forall_of_frequently hfreq
  refine ⟨t, ht, φ, hφ, fun j => ?_, fun j => (hlink j).trans_lt (hDt j), ?_⟩
  · have hsubA : {x | f x = t} ⊆ A := by
      intro x hx
      rw [hA]
      simp only [mem_ofPred_eq] at hx ⊢
      rw [hx]
      exact ht
    have h := hκt j
    rwa [Measure.restrict_apply (measurableSet_eq_fun hf measurable_const),
      inter_eq_left.2 hsubA] at h
  · have hinv : Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
      have := ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
      refine this.congr fun n => ?_
      simp [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hinv (fun _ => zero_le)
      (fun n => (hlink (φ n)).trans (hφlt n).le)
```

## Key steps

1. Push ν_j⌞A forward by f to a finite measure ρ_j on ℝ; Tonelli on S_c = {s − c < y < s} gives ∫ ρ_j((s − c, s)) ds = c·ν_j(A).
2. G_j(s) := liminf_k (k + 1)·ρ_j((s − 1/(k + 1), s)) is Borel with ∫ G_j ≤ ν_j(A) (Fatou), so G_j < ∞ a.e.
3. Fatou in j: liminf_j G_j = 0 a.e.; for each j only countably many levels are atoms of κ_j⌞A.
4. Pick a good t ∈ (a, b): κ_j({f = t}) = 0, and D_j(t) ≤ G_j(t) < ∞ via h_k = 1/(k + 1) and {t − h_k < f < t} ⊆ A.
5. Extract φ with G_{φ(n)}(t) < 1/(n + 1), so D_{φ(n)}(t) → 0.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical); cat local-references/123e8435b4a2469b/manifest.json`
- `rg -n 'lcmp_|good_slice|lipschitz_cutoff' local-references/123e8435b4a2469b/project (no match)`
- `rg -n 'theorem MonotoneOn.intervalIntegral_deriv_mem_uIcc|theorem countable_meas_level_set_pos|theorem IsOpen.exists_contDiff_support_eq|theorem prod_apply_symm|theorem measurable_measure_prodMk_left|theorem lintegral_liminf_le|theorem extraction_forall_of_frequently|theorem integral_withDensity_eq_integral_smul|theorem tendsto_measure_iInter_atTop|theorem closure_eq_iInter_thickening' local-references/123e8435b4a2469b/mathlib/Mathlib -g '*.lean'; rg -n 'theorem (one_of_one_le|zero_of_nonpos|le_one|nonneg)|protected theorem contDiff' .../Analysis/SpecialFunctions/SmoothTransition.lean`
- `lake env lean /tmp/lcmp/Names.lean, Names2.lean, Names3.lean, N4.lean (#check of every cited Mathlib/SimonGMT declaration after import GMT.Ch07.Submission; MonotoneOn.intervalIntegral_deriv_mem_uIcc and MonotoneOn.intervalIntegrable_deriv are not in the import closure)`
- `sed SimonGMT Chapter06/{Mass,Currents,CurrentLocalEquality,Forms}.lean (massOn, massAdmissibleOn, covectorEuclideanNorm_neg, le_massOn, massOn_mono, boundary_apply, boundary_boundary, zeroRegion/support, TestFormOn); rg -n -i 'slice by|lipschitz slic|flat norm|deformation theorem' Chapter06 (no match)`
- `python3 -I scans of dag.json: lean_statement/status/children/depends_on of all 514 nodes; sibling frozen types of the selected node; accepted nodes mentioning support/massOn/IMRep/withDensity (155); smooth cut-off and mass-triangle candidates; collision check of the 8 proposed names`
- `grep -c of the six lcmp_ names in dag.json, issue-workers.json, DAG.md, GMT/, .lake/packages/simongmt; git grep -l lcmp_ over all 1117 distinct ref commits -- GMT (no match)`
- `git show 02c6122c94d0280a6288d299659b2dab7b59e109:GMT/Ch07/Submission.lean and 702e7082a5a7012f7a8f6efd9d272697e426f50b:GMT/Ch07/Submission.lean (accepted proofs of the two reused declarations)`
- `sed -n 3160,3230p and 6557,6600p runtime.py (_overlay_accepted_children: prerequisites = children + depends_on; _existing_lean_name_problem: reuse only for accepted identical types); sed -n 480,620p verifier/gmt-compare.py (contract_scope, child_modules)`
- `lake env lean /tmp/lcmp/Types1.lean; /tmp/lcmp/AsmFinal.lean; /tmp/lcmp/Validate.lean; /tmp/lcmp/FinalCheck.lean (#print axioms)`
- `sed -n 150,262p book/chapter-07.txt (Simon 7.2.4 proof, (1)–(12))`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-local-comparison-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1/decomposition-v5.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-constant-multiplicity-reduction-a1-support-a67ad69f81/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1-imrep-local-finiteness-a1/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/lcmp/Types1.lean`
- `/tmp/lcmp/AsmFinal.lean`
- `/tmp/lcmp/Validate.lean`
- `/tmp/lcmp/FinalCheck.lean`
- `/tmp/lcmp/out/subproblems.json`

The snapshot contract is byte-identical to the workspace Contract.lean and Submission.lean (manifest: project b4d606db, mathlib 25730c7c), and the snapshot project contains no lcmp_ declaration. Neither the snapshot Mathlib nor the pinned SimonGMT states any of the six new child facts: Lipschitz cut-off, good slicing level, mass localization, mass triangle inequality, IMRep restriction calculus, compact outer bound. SimonGMT Chapter06 has only massOn/le_massOn/massOn_mono and covectorEuclideanNorm_neg. Every Mathlib declaration cited in the child proofs is located in the snapshot and checked importable after import GMT.Ch07.Submission. The exception is MonotoneOn.intervalIntegral_deriv_mem_uIcc (DerivIntegrable.lean): it is cited by the parent's step 5 but is not imported, so child good_slice_level uses a Tonelli-based majorant instead. Two accepted DAG declarations with byte-identical frozen types are reused: rsd_cmr_support_subset_of_vanish and rsd_imrep_compact_measure_ne_top. In Lean: all eight child types elaborate in the comparator scope, and all eight child proofs compile with only propext, Classical.choice and Quot.sound. A conditional assembly from the six exact sibling types plus the eight child types proves the exact frozen parent type, with the same axioms. Simon's text (chapter-07.txt lines 176–258) confirms the parent's corrections S̃_j = S_j⌞W_α − P_j and γ ↑ α.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
