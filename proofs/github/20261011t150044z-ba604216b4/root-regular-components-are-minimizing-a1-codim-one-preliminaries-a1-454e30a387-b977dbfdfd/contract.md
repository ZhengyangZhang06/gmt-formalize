<!-- theorem-id: gmt-ch07/root.regular_components_are_minimizing-a1.codim_one_preliminaries-a1.zero_dim_regular_empty-a1 -->

## Theorem `Submission.regcomp_cop_zero_dim_regularSet_empty`

Let P ∈ ℕ, let U ⊆ ℝ^P be open, let A ⊆ ℝ^P, and let T ∈ 𝒟_0(U) be minimizing in A in the sense of the contract (IsMinimizingIn T A, Simon 7.1.1: T is integer multiplicity, and M_W(T) ≤ M_W(S) for every open W with closure W compact and ⊆ U and every integer multiplicity S ∈ 𝒟_0(U) with spt(S − T) a compact subset of A ∩ W; the condition ∂S = ∂T is vacuous in degree 0). If spt T ⊆ A, then reg T = ∅ (regularSet T = ∅, Simon 7.4.1 as frozen in the contract).

Node: `root.regular_components_are_minimizing-a1.codim_one_preliminaries-a1.zero_dim_regular_empty-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/912

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4406, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4416, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4419, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1204, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1207, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1206, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4423, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4426

## Lean problem

Declaration: `Submission.regcomp_cop_zero_dim_regularSet_empty`

```lean
∀ (P : ℕ) (U A : Set (Euclid P)) (T : GeometricCurrentOn U 0), IsOpen U → IsMinimizingIn T A → T.support ⊆ A → regularSet T = ∅
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

- Parent DAG node: `root.regular_components_are_minimizing-a1.codim_one_preliminaries-a1`
- Child DAG node: `root.regular_components_are_minimizing-a1.codim_one_preliminaries-a1.zero_dim_regular_empty-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 4 (4.1–4.8: for n = 0 a regular point is an isolated atom of T, and deleting it gives a cheaper admissible competitor), with the parent's set N ∩ U replaced by an arbitrary A satisfying spt T ⊆ A. The parent applies this lemma with P := 0 + k and A := N ∩ U, using spt T ⊆ N (its step 2) and spt T ⊆ U. Notation: H^0 = μHE[0]; tsupport ω is the closed support of a form; Z(S) (zeroRegion) is the union of all open W with closure W compact, closure W ⊆ U, on which S vanishes, and spt S = U ∖ Z(S); M_W(S) (massOn) is the supremum of ofReal(S(ω)) over ω ∈ 𝒟^0(U) with tsupport ω ⊆ W and Euclidean coefficient norm ≤ 1 at every point.

0. Facts in dimension 0.
 (F1) H^0 = μHE[0] = μH[0] (Mathlib euclideanHausdorffMeasure_zero) and H^0({x}) = 1 for every x (hausdorffMeasure_zero_singleton). Hence H^0(F) = #F for finite F (additivity over the measurable singletons), and every set S with H^0(S) < ∞ is finite (otherwise it contains finite subsets of every cardinality). Moreover, for any set C and any x ∈ C, (H^0⌞C)({x}) = H^0({x} ∩ C) = 1 ({x} is measurable), so by monotonicity no (H^0⌞C)-null set contains a point of C.
 (F2) Fin 0 → ℝ^P has exactly one element, the empty family, written (); for a 0-covector α write α() for its value at (). Let ε₀ be the 0-covector with ε₀() = 1 (the constant alternating map, constOfIsEmpty).
 (F3) The Euclidean coefficient norm of a 0-covector α is |α()|: the only index map Fin 0 → Fin P is the empty one, which is strictly monotone, so the defining sum has the single term α()².
 (F4) If ξ' ∈ Λ_0(ℝ^P) satisfies IsUnitOrientationOf ξ' Q for some subspace Q, its frame τ : Fin 0 → ℝ^P is the empty family, so either ξ'(α) = α() for all α or ξ'(α) = −α() for all α; write ξ'(α) = s·α() with s ∈ {1, −1}.
 (F5) For z ∈ ℝ^P and a > 0 there is a smooth g : ℝ^P → [0, 1] with g(z) = 1 and g = 0 outside ball(z, a), so tsupport g ⊆ closedBall(z, a) (a ContDiffBump centred at z with outer radius a). For c ∈ ℝ the 0-form ω := c g ε₀ (x ↦ c g(x) ε₀) is smooth with compact support, tsupport ω ⊆ closedBall(z, a), ω(x)() = c g(x), and its coefficient norm at x is |c| g(x) by (F3); if closedBall(z, a) ⊆ U then ω ∈ 𝒟^0(U).

1. (Set-up.) Suppose, for a contradiction, that y ∈ reg T. By the first conjunct of IsMinimizingIn, T is integer multiplicity; fix R ∈ IMRep U 0 with R.Represents T, with carrier C (Borel, C ⊆ U, countably 0-rectifiable), multiplicity θ (measurable, ℕ-valued, θ ≥ 1 on C, ∫_{C∩K} θ dH^0 < ∞ for every compact K ⊆ U) and orientation ξ_R. Thus T(ω) = ∫_C θ(x) ξ_R(x)(ω(x)) dH^0(x) for every ω ∈ 𝒟^0(U).

2. (Local form of T near y; parent 4.1.) By the definition of regularSet there are ρ > 0 with ball(y, ρ) ⊆ U, m ∈ ℤ ∖ {0}, a set M with y ∈ M and ξ : ℝ^P → Λ_0(ℝ^P) such that IsEmbeddedSubmanifold 1 0 M, IsOrientation 0 M ξ, and T(ω) = m ∫_M ξ(x)(ω(x)) dH^0(x) for every ω ∈ 𝒟^0(U) with tsupport ω ⊆ ball(y, ρ).
 2a. The chart of M at y gives V ⊆ ℝ^0, an open W_M ⊆ ℝ^P with y ∈ W_M, and ψ : ℝ^0 → ℝ^P with ψ(V) = W_M ∩ M. As ℝ^0 = {0}, ψ(V) ⊆ {ψ(0)}; since y ∈ W_M ∩ M = ψ(V), y = ψ(0) and W_M ∩ M = {y}.
 2b. Choose r with 0 < r < ρ and ball(y, r) ⊆ W_M (W_M is open). Then M ∩ ball(y, r) = {y}.
 2c. By IsOrientation 0 M ξ at y ∈ M and (F4), ξ(y)(α) = s·α() for all α, for some s ∈ {1, −1}.
 2d. Claim (*): every ω ∈ 𝒟^0(U) with tsupport ω ⊆ ball(y, r) satisfies T(ω) = m s ω(y)(). Proof: K := tsupport ω is closed and K ⊆ ball(y, r) ⊆ ball(y, ρ), so T(ω) = m ∫_M f dH^0 with f(x) := ξ(x)(ω(x)). The function f vanishes outside K (there ω(x) = 0 and ξ(x) is linear), so ∫_M f dH^0 = ∫_{M∩K} f dH^0 (restriction to the closed, hence measurable, set K; no measurability of M is used). Since M ∩ K ⊆ M ∩ ball(y, r) = {y}: if y ∈ K then M ∩ K = {y} and ∫_{{y}} f dH^0 = f(y) H^0({y}) = f(y) = s ω(y)(); if y ∉ K then M ∩ K = ∅, the integral is 0, and s ω(y)() = 0 as well because ω(y) = 0. In both cases T(ω) = m s ω(y)().

3. (Structure of C; parent 4.2.)
 3a. (Local finiteness.) For compact K ⊆ U, H^0(C ∩ K) = ∫_{C∩K} 1 dH^0 ≤ ∫_{C∩K} θ dH^0 < ∞ (θ ≥ 1 on C), so C ∩ K is finite by (F1).
 3b. (Orientation at every point.) By R.orients, the set of points x at which there is no Q with HasApproximateTangentSpaceAt 0 C x Q and IsUnitOrientationOf (ξ_R(x)) Q is (H^0⌞C)-null, hence contains no point of C by (F1). So for every x ∈ C there is a subspace Q_x with HasApproximateTangentSpaceAt 0 C x Q_x and IsUnitOrientationOf (ξ_R(x)) Q_x, and by (F4) ξ_R(x)(α) = s_x α() for all α, with s_x ∈ {1, −1}.
 3c. (Isolated atoms.) If x ∈ C, a > 0, C ∩ closedBall(x, a) = {x}, and ω ∈ 𝒟^0(U) has tsupport ω ⊆ closedBall(x, a), then T(ω) = θ(x) s_x ω(x)(). Indeed the integrand F(z) := θ(z) ξ_R(z)(ω(z)) vanishes outside closedBall(x, a), so ∫_C F dH^0 = ∫_{C ∩ closedBall(x, a)} F dH^0 = ∫_{{x}} F dH^0 = F(x) H^0({x}) = θ(x) s_x ω(x)().

4. (C ∩ ball(y, r) ⊆ {y}; parent 4.3.) Let x ∈ C ∩ ball(y, r) with x ≠ y, and put δ := |x − y| > 0. With a₀ := min(r − δ, δ)/2 > 0 we have closedBall(x, a₀) ⊆ ball(y, r) ⊆ U and y ∉ closedBall(x, a₀). By 3a, C ∩ closedBall(x, a₀) is finite, so there is a with 0 < a ≤ a₀ and C ∩ closedBall(x, a) = {x} (take a smaller than the distance from x to each of the finitely many points of (C ∩ closedBall(x, a₀)) ∖ {x}). Let g be as in (F5) for (x, a) and ω := g ε₀ ∈ 𝒟^0(U). Then tsupport ω ⊆ closedBall(x, a) ⊆ ball(y, r) and g(y) = 0, so (*) gives T(ω) = m s g(y) = 0. On the other hand 3c gives T(ω) = θ(x) s_x g(x) = ±θ(x) ≠ 0, since θ(x) ≥ 1. Contradiction.

5. (y ∈ C; parent 4.4.) Suppose y ∉ C; then C ∩ ball(y, r) = ∅ by 4. Let g be as in (F5) for (y, r/2) and ω := g ε₀ ∈ 𝒟^0(U) (closedBall(y, r/2) ⊆ ball(y, r) ⊆ U). Every z ∈ C lies outside ball(y, r) ⊇ tsupport ω, so ω(z) = 0, the integrand of the representation vanishes on C, and T(ω) = 0. But (*) gives T(ω) = m s g(y) = m s ≠ 0. Contradiction. Hence y ∈ C and, by 4, C ∩ ball(y, r) = {y}.

6. (The competitor; parent 4.5.)
 6a. Define D : 𝒟^0(U) → ℝ by D(ω) := θ(y) ξ_R(y)(ω(y)). D is linear. It is sequentially continuous: if ω_j → 0 in 𝒟^0(U) (all tsupport ω_j in one compact K ⊆ U and all derivatives of ω_j → 0 uniformly on K), then ω_j(y) → 0 (if y ∈ K by uniform convergence of the 0-th derivatives on K; if y ∉ K because ω_j(y) = 0 for all j), so D(ω_j) → 0 by continuity of the linear functional ξ_R(y) on the finite-dimensional space of 0-covectors. Thus D ∈ 𝒟_0(U).
 6b. Let S := T − D ∈ 𝒟_0(U), the contract's difference of currents: S(ω) = T(ω) − D(ω).
 6c. R_S := (C ∖ {y}, θ, ξ_R) is an IMRep in U. C ∖ {y} is Borel and ⊆ U; it is countably 0-rectifiable as a subset of C (CountablyRectifiable.mono); θ is measurable and θ > 0 on C ∖ {y}; for compact K ⊆ U, ∫_{(C∖{y})∩K} θ dH^0 ≤ ∫_{C∩K} θ dH^0 < ∞; ξ_R is a.e. strongly measurable for H^0⌞(C ∖ {y}) because this measure is ≤ H^0⌞C. Orientation condition: let x ∈ C ∖ {y} and Q_x be as in 3b. Then C ∖ {y} also has approximate tangent space Q_x at x: for f ∈ C_c(ℝ^P) with f = 0 outside B_R(0) and 0 < λ < |x − y|/R, the images η_{x,λ}(C) and η_{x,λ}(C ∖ {y}) under the injective map η_{x,λ}(z) = λ^{−1}(z − x) differ only by the point (y − x)/λ, whose norm |y − x|/λ exceeds R, so f vanishes there and ∫_{η_{x,λ}(C)} f dH^0 = ∫_{η_{x,λ}(C∖{y})} f dH^0. Hence the two functions of λ in Definition 1.4 of Ch. 3 (HasApproximateTangentSpaceAt) agree for all small λ > 0 and have the same limit ∫_{Q_x} f dH^0, while the dimension condition finrank Q_x = 0 is unchanged. Thus every point of C ∖ {y} satisfies the orientation condition for R_S, which therefore holds (H^0⌞(C ∖ {y}))-a.e.
 6d. (R_S represents S.) Let ω ∈ 𝒟^0(U) and F(z) := θ(z) ξ_R(z)(ω(z)). F vanishes outside the compact set tsupport ω ⊆ U, and C ∩ tsupport ω is finite by 3a, so on C the function F is supported in a finite set and F is integrable for H^0⌞C and for H^0⌞(C ∖ {y}). Since C is the disjoint union of the measurable sets C ∖ {y} and {y} (y ∈ C by 5) and H^0({y}) = 1, ∫_C F dH^0 = ∫_{C∖{y}} F dH^0 + θ(y) ξ_R(y)(ω(y)). Hence S(ω) = T(ω) − D(ω) = ∫_{C∖{y}} θ ξ_R(ω) dH^0 = R_S.action(ω) for every ω, so R_S represents S and S is integer multiplicity.

7. (Minimality applies; parent 4.6.) Let W := ball(y, r/2). W is open, and closure W = closedBall(y, r/2) is compact and contained in ball(y, r) ⊆ U, so CompactlyContained W U. SameBoundary S T holds because the degree is 0. For every ω, (S − T)(ω) = (T(ω) − D(ω)) − T(ω) = −D(ω). If x ∈ U ∖ {y}, choose b > 0 with closedBall(x, 2b) ⊆ U ∖ {y} (an open set containing x); then ball(x, b) is open, its closure closedBall(x, b) is compact and ⊆ U, and every ω with tsupport ω ⊆ ball(x, b) has ω(y) = 0, so (S − T)(ω) = −θ(y) ξ_R(y)(0) = 0; thus x ∈ Z(S − T). Hence spt(S − T) ⊆ {y}; as a subset of a singleton it is finite, hence compact; and {y} ⊆ A ∩ W because y ∈ reg T ⊆ spt T ⊆ A and y ∈ W. By minimality of T in A (second conjunct of IsMinimizingIn): M_W(T) ≤ M_W(S).

8. (M_W(S) = 0; parent 4.7.) Let ω be admissible for M_W(S), so tsupport ω ⊆ W ⊆ ball(y, r). For z ∈ C ∖ {y}, z ∉ ball(y, r) by 5, so ω(z) = 0 and θ(z) ξ_R(z)(ω(z)) = 0; hence S(ω) = R_S.action(ω) = ∫_{C∖{y}} θ ξ_R(ω) dH^0 = 0 by 6d. Every element ofReal(S(ω)) of the set whose supremum defines M_W(S) is ofReal(0) = 0, so M_W(S) = 0.

9. (M_W(T) ≥ 1; parent 4.8.) Let σ := sign(m s) ∈ {1, −1} (m s ≠ 0), g as in (F5) for (y, r/4) and ω := σ g ε₀ ∈ 𝒟^0(U). Then tsupport ω ⊆ closedBall(y, r/4) ⊆ W, and the coefficient norm of ω(x) is |σ| g(x) = g(x) ≤ 1 for every x (F3), so ω is admissible for M_W(T). By (*), T(ω) = m s σ g(y) = |m s| = |m| ≥ 1. Hence M_W(T) ≥ ofReal(T(ω)) ≥ 1 > 0 = M_W(S) by 8, contradicting 7. Therefore reg T has no point: reg T = ∅.

Remark (formalization aids, not part of the argument): comparator-accepted declarations proved in other branches of this run treat several of these steps for arbitrary 0-dimensional IMReps and may be consulted when formalizing: Submission.dor_zdm_imrep_zero_structure (3a, 3b), Submission.dtc_point_current (6a), Submission.dtc_approxTangent_sdiff_singleton and Submission.dtc_dim_zero_erase_point (6c, 6d), Submission.regcomp_rim_action_integrable (integrability in 6d), Submission.rsd_cmr_support_subset_of_vanish (the support bound in 7) and Submission.dor_ims_massOn_le_measure (an alternative route to 8). A complete kernel-checked Lean development of exactly this argument (those helpers copied verbatim, plus local lemmas for (F3), (F4), the isolated-atom integrals of 2d and 3c, the bump 0-forms of (F5) and the local form of step 2; axioms propext, Classical.choice, Quot.sound) is kept in the gitignored scratch file GMT/Scratch/regcomp_cop_decomposition/Full.lean of the run workspace. Since a leaf may append only its own theorem, a formalization should split along those helpers or inline them.

## Key steps

1. Assume y ∈ reg T and fix an integer multiplicity representation (C, θ, ξ_R) of T.
2. The 0-dimensional chart gives M ∩ ball(y, r) = {y}, so T(ω) = m s ω(y)() whenever tsupport ω ⊆ ball(y, r).
3. C is locally finite, and every point of C carries a unit orientation ξ_R(x) = s_x·eval (H^0-null sets are empty).
4. Bump test forms show C ∩ ball(y, r) = {y}.
5. S := T − θ(y)ξ_R(y)δ_y is represented by (C ∖ {y}, θ, ξ_R), hence integer multiplicity, and spt(S − T) ⊆ {y} ⊆ A ∩ W with W = ball(y, r/2).
6. M_W(S) = 0 while M_W(T) ≥ |m| ≥ 1, contradicting minimality.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `rg -n 'theorem setIntegral_eq_zero_of_forall_eq_zero|theorem hausdorffMeasure_zero_singleton|def constOfIsEmpty|hasContDiffBump_of_innerProductSpace|theorem closure_ball|image_eq_zero_of_notMem_tsupport' mathlib/Mathlib`
- `rg -n 'finrank_le_finrank_of_injective' mathlib/Mathlib`
- `rg -n 'regcomp_cop_|IsBoundaryOfRegion|InClassO' project/GMT/Ch07`
- `rg -n 'IsEmbeddedSubmanifold.*finrank|finrank_le_of_.*embedded' project mathlib/Mathlib (no match)`
- `grep -n 'tsupport_exteriorDerivative_subset|exteriorDerivative_sq|GeometricCurrentOn.boundary_apply|GeometricCurrentOn.ext' simongmt Chapter06/Currents.lean, Chapter06/Forms.lean`
- `grep -n 'VanishesOn|zeroRegion|support_subset_domain' simongmt Chapter06/CurrentLocalEquality.lean; grep -n 'covectorEuclideanNorm|massAdmissibleOn|massOn|le_massOn' Chapter06/Mass.lean`
- `grep -n 'blowUpMap|HasApproximateTangentSpaceAt|CountablyRectifiable.mono' simongmt Chapter03/Rectifiable.lean`
- `grep -n 'euclideanHausdorffMeasure_zero|setIntegral_eq_zero_of_ae_eq_zero' mathlib Geometry/Euclidean/Volume/Measure.lean, MeasureTheory/Integral/Bochner/Set.lean`
- `python3 scan of dag.json lean_name fields (no regcomp_cop_ collision; related dimension-0 nodes and their statuses); git grep regcomp_cop_ over all 1897 refs (no match)`
- `git show <theorems/solutions branch>:GMT/Ch07/Submission.lean for accepted dor_zdm_imrep_zero_structure, dtc_point_current, dtc_dim_zero_carrier_finite, dtc_approxTangent_sdiff_singleton, dtc_dim_zero_erase_point, rsd_cmr_support_subset_of_vanish, dor_ims_massOn_le_measure; verification.json machine_comparator_passed`
- `lake env lean /tmp/cop-decomp/gen/Assembly.lean (four child stubs + parent assembly, #print axioms)`
- `lake env lean /tmp/cop-decomp/Small.lean and in-situ leaf candidates; simulated _recursive_lean.leaf_verification.check_source_delta`
- `source env.sh && lean GMT/Scratch/regcomp_cop_decomposition/Full.lean (#print axioms: propext, Classical.choice, Quot.sound)`
- `sed -n 740,790p book/chapter-07.txt (Simon 7.5: 5.1 T = ∂[[E]], class 𝒪)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-codim-one-preliminaries-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/StrongRankCondition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/EuclideanDist.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/InnerProduct.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/parent_verification.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/regcomp_cop_decomposition/Assembly.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/regcomp_cop_decomposition/Small.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/regcomp_cop_decomposition/Full.lean`

Snapshot and toolchain:
- The snapshot contract (project b4d606d, mathlib 25730c7c) is byte-identical to the workspace Submission.lean.
- SimonGMT supplies tsupport_exteriorDerivative_subset, exteriorDerivative_sq, GeometricCurrentOn.boundary_apply and ext, the definitions of zeroRegion, support and massOn, and covectorEuclideanNorm, blowUpMap and CountablyRectifiable.mono. These close C2 and C3 and the degree-0 steps of C4.
- Mathlib supplies:
  - setIntegral_eq_zero_of_forall_eq_zero, which needs no measurability of the integration set;
  - euclideanHausdorffMeasure_zero (μHE[0] = μH[0]) and hausdorffMeasure_zero_singleton;
  - LinearMap.finrank_le_finrank_of_injective and closure_ball;
  - ContinuousAlternatingMap.constOfIsEmpty and ContDiffBump.
- No library theorem states the dimension bound for IsEmbeddedSubmanifold (no match), so C1 is proved directly.

Accepted helpers in other branches:
- Comparator-accepted declarations exist in solution branches of other DAG branches: dor_zdm_imrep_zero_structure, dtc_point_current, dtc_dim_zero_carrier_finite, dtc_approxTangent_sdiff_singleton, dtc_dim_zero_erase_point, rsd_cmr_support_subset_of_vanish, dor_ims_massOn_le_measure and regcomp_rim_action_integrable.
- They are not present in the workspace Submission.lean. Copied verbatim, they compile against the frozen contract and cover several of C4's steps.

Verification:
- The four child types elaborate after `import GMT.Ch07.Submission`. The parent assembles from them; only the stubs contribute sorryAx.
- C1–C3 have proofs that pass the simulated leaf source-delta check and compile in place inside Submission.lean.
- A full end-to-end development of the node compiles with only propext, Classical.choice and Quot.sound. It is kept in the gitignored GMT/Scratch/regcomp_cop_decomposition/.
- No regcomp_cop_ name collides with anything in dag.json or any git ref.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
