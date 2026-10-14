<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1 -->

## Theorem `Submission.codim1_simons_regular_cone_density`

Simons' theorem for minimizing hypercones that are regular with multiplicity one off the vertex (Simon B.2).
Data: P, m ∈ ℕ with 2 ≤ m ≤ 6; C ∈ 𝒟_m(ℝ^P); A₀ ⊆ ℝ^P a linear subspace with dim A₀ = m + 1.
Hypotheses:
- C is minimizing in ℝ^P and ∂C = 0;
- C is a cone: η_{0,λ#}C = C for every λ > 0 (IsConeCurrent C);
- spt C ⊆ A₀;
- every y ∈ spt C ∖ {0} is a regular point of C (y ∈ regularSet C) with Θ^m(μ_C, y) = 1.
Conclusion: every θ with Θ^m(μ_C, 0) = θ satisfies θ ≤ 1.

Node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1038

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/810, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1211, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4336, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1285, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1081

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5209, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5217, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5228, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5240, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5249, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1285, https://github.com/ZhengyangZhang06/gmt-formalize/issues/810, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1211, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1081, https://github.com/ZhengyangZhang06/gmt-formalize/issues/984, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4203

## Lean problem

Declaration: `Submission.codim1_simons_regular_cone_density`

```lean
∀ (P m : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) m) (A₀ : Submodule ℝ (Euclid P)), 2 ≤ m → m ≤ 6 → Module.finrank ℝ A₀ = m + 1 → IsMinimizingIn C univ → BoundaryVanishes C → IsConeCurrent C → C.support ⊆ (A₀ : Set (Euclid P)) → (∀ y ∈ C.support, y ≠ 0 → y ∈ regularSet C ∧ HasMassDensity C y 1) → ∀ θ : ℝ, HasMassDensity C 0 θ → θ ≤ 1
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

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Parent step 5 (β)–(γ) of the supplied proof of CodimensionOneRegularity for the cone factor S₀: Simon Appendix B, B.1, B.2 and the printed proof of B.2 (Simons [Sim68], in the form of Schoen–Simon–Yau; chapter-07-source.txt lines 1256–1539 = chapter-B.txt lines 1–233), together with the verification of the hypotheses of B.2. Supporting book results: Ch. 2, 5.1–5.12, first and second variation (chapter-02.txt lines 1290–1405); Ch. 5, 7.1 (chapter-05.txt lines 1312–1366); Ch. 3, 1.8–1.9, densities (chapter-03.txt lines 298–323); Ch. 6, 3.3–3.9, push-forward of integer multiplicity currents. This is part B of the previously reviewed analytic core of this node, stated as its own theorem.
Explicit departures from the parent text:
(i) The hypothesis “y ∈ reg C and Θ^m(μ_C, y) = 1 for every y ∈ spt C ∖ {0}” is supplied by the parent in step 5(α) (from the sibling children low_density_regular and, at the parent level, regular_point_density).
(ii) Stationarity of M is proved directly from minimality, by the same first-variation competitors that give stability, instead of citing MinimizingImpliesStationary; the vertex density is computed from the multiplicity-one representation instead of the constancy theorem.
(iii) The mass facts are cited from the sibling child oriented_piece_mass instead of the parent's sibling im_mass_measure.

Sibling children used.
- vanish_off_support (Submission.dtc_vanish_off_support): S(ω) = 0 whenever tsupport ω ∩ spt S = ∅.
- cone_pullback_identity (Submission.cone_current_apply_dilation_pullback): for a cone C, λ > 0 and ω ∈ 𝒟^m(ℝ^P) there is ω' ∈ 𝒟^m(ℝ^P) with ω'(y) = λ^{−m}ω(λ^{−1}y) for all y and C(ω') = C(ω).
- oriented_piece_mass (Submission.codim1_massOn_eq_lintegral_of_oriented_rep): if V ⊆ U is open, M' ⊆ V Borel, θ' ≥ 0 measurable, ξ' a.e. strongly measurable on M' and H^m-a.e. on M' a unit orientation of some subspace, and T(ω) = ∫_{M'} θ'·ξ'(ω) dH^m whenever tsupport ω ⊆ V, then for every open W ⊆ V: M_W(T) ≤ ∫_{M'∩W} θ' dH^m (first conclusion), with equality when the right side is finite (second conclusion).
- orientation_sign (Submission.rsdic_unitOrientation_eq_or_eq_neg): two unit orientations of the same subspace satisfy w = v or w = −v.
- unit_orientation_dual (Submission.dor_ims_unitOrientation_dual): a continuous linear L : Λ_m → Λ^m such that every unit orientation ξ of a subspace satisfies (a) |ξ(α)| ≤ |α| for all α, (b) |L(ξ)| ≤ 1 and (c) ξ(L(ξ)) = 1.

Notation.
- H^d := μHE[d]; on a d-dimensional affine plane it is d-dimensional Lebesgue measure. ω_d := unitBallVolume d is H^d of a unit d-disc. B_ρ(y) := ball y ρ; r(x) := |x|.
- For a k-covector α, |α| is the Euclidean coefficient norm (covectorEuclideanNorm). M_W(T) := T.massOn W is the supremum of ofReal T(ω) over ω ∈ 𝒟^m(ℝ^P) with tsupport ω ⊆ W and |ω| ≤ 1 pointwise.
- “T vanishes on W” means T(ω) = 0 whenever tsupport ω ⊆ W; Z(T) is the union of the open W with compact closure on which T vanishes, and spt T := ℝ^P ∖ Z(T).
- “Θ^m(μ_T, y) = θ” means HasMassDensity T y θ: θ ≥ 0 and M_{B_ρ(y)}(T)/(ω_mρ^m) → θ as ρ ↓ 0.
- For an IMRep R = (M_R, θ_R, ξ_R), μ_R(A) := ∫_{M_R∩A} θ_R dH^m.
- M := spt C ∖ {0}.

General facts (for a current T ∈ 𝒟_m(U), U open).
(G1) Uniqueness of densities. If Θ^m(μ_T, y) = θ₁ and Θ^m(μ_T, y) = θ₂, then θ₁ = θ₂, because limits in [0, ∞] are unique and ofReal is injective on [0, ∞).
(G2) Positive density forces support. If T vanishes on an open W, then M_{W'}(T) = 0 for every W' ⊆ W. Hence if y ∈ U has Θ^m(μ_T, y) = θ > 0, then y ∈ spt T: otherwise y lies in an open W on which T vanishes, M_{B_t(y)}(T) = 0 for small t, and the density is 0 ≠ θ.
(G7) Density of C¹ submanifolds (Simon Ch. 3, 1.8–1.9). If M' ∩ B_r(w) is a relatively closed embedded C¹ m-submanifold of B_r(w) containing w, then H^m(M' ∩ B_s(w))/(ω_ms^m) → 1 as s ↓ 0: near w, M' is the graph over T_wM' of a C¹ map whose Lipschitz constant on B_s(w) tends to 0 as s ↓ 0, and the area formula gives H^m(M' ∩ B_s(w)) = ω_ms^m(1 + o(1)).

Proof. Fix P, m, C, A₀ satisfying the hypotheses, and let θ satisfy Θ^m(μ_C, 0) = θ.

B0. (Set-up.)
- dim A₀ = m + 1 ≤ P.
- C is integer multiplicity (first conjunct of IsMinimizingIn). Fix an IMRep R = (M_R, θ_R, ξ_R) of C and put μ := μ_R; then μ(K) < ∞ for compact K (IMRep.locallyIntegrable_mult).
- The general facts (G1), (G2), (G7) above hold with U := ℝ^P.
(B0.1) Vertex negligibility. Let χ_ε ∈ C^∞_c(B_{2ε}(0)) with 0 ≤ χ_ε ≤ 1 and χ_ε = 1 on B_ε(0). For every ω ∈ 𝒟^m(ℝ^P), C(χ_εω) → 0 as ε ↓ 0.
- C(χ_εω) = ∫_{M_R} θ_Rχ_ε⟨ω, ξ_R⟩ dH^m.
- For ε ≤ 1/2 the integrand is dominated by θ_R·max|ω|·1_{B_1(0)}, because ξ_R(x) is a unit orientation of a plane for H^m-a.e. x ∈ M_R (IMRep.orients) and then |ξ_R(x)(α)| ≤ |α| by unit_orientation_dual (a); the dominant is integrable since μ(closedBall(0, 1)) < ∞.
- It tends pointwise to θ_R1_{{0}}⟨ω, ξ_R⟩, and H^m({0}) = 0 because m ≥ 1. Dominated convergence gives the limit 0.
- Since (1 − χ_ε)ω ∈ 𝒟^m(ℝ^P) with tsupport ⊆ tsupport ω ∖ B_ε(0), it follows that C(ω) = lim_{ε↓0} C((1 − χ_ε)ω).

B1. (Trivial case M = ∅.) Then spt C ⊆ {0}.
- For every ω, tsupport((1 − χ_ε)ω) is disjoint from {0} ⊇ spt C, so C((1 − χ_ε)ω) = 0 by vanish_off_support.
- By (B0.1), C(ω) = 0 for every ω. Thus C = 0, M_{B_ρ(0)}(C) = 0 for every ρ, and Θ^m(μ_C, 0) = 0.
- By (G1), θ = 0 ≤ 1. From now on assume M ≠ ∅.

B2. (Local structure of M; parent 5(β)(i).) Let y ∈ M. By hypothesis y ∈ regularSet C and Θ^m(μ_C, y) = 1. The definition of regularSet gives:
- ρ_y > 0, m_y ∈ ℤ ∖ {0}, and an embedded C¹ m-dimensional submanifold M_y ∋ y;
- an orientation ξ_y of M_y: continuous on M_y, with ξ_y(w) a unit orientation of tangentSpace(M_y, w);
- H^m(M_y ∩ K) < ∞ for compact K ⊆ B_{ρ_y}(y);
- C(ω) = m_y ∫_{M_y} ⟨ω, ξ_y⟩ dH^m whenever tsupport ω ⊆ B_{ρ_y}(y).
(B2a) Relative closedness.
- Take a chart (V, W_ψ, ψ) of M_y at y. Since ψ(V) = W_ψ ∩ M_y and ψ is proper, W_ψ ∩ M_y is closed in W_ψ.
- Choose ρ' with 0 < ρ' ≤ min(ρ_y, |y|)/2 and B_{2ρ'}(y) ⊆ W_ψ.
- Then M_y ∩ B_{ρ'}(y) is relatively closed in B_{ρ'}(y), and 0 ∉ closedBall(y, ρ').
(B2b) If tsupport ω ⊆ B_{ρ'}(y) ∖ M_y, an open set, then ω = 0 on M_y and C(ω) = 0. So spt C ∩ B_{ρ'}(y) ⊆ M_y.
(B2c) Mass identity. Apply oriented_piece_mass (second conclusion) with θ' :≡ |m_y|, V := B_{ρ'}(y), M' := M_y ∩ B_{ρ'}(y) and ξ' := sign(m_y)ξ_y (extended by 0 off M'). Its hypotheses hold:
- M' is Borel, being relatively closed in the open ball;
- ξ' is continuous on the Borel set M', hence measurable, and sign(m_y)ξ_y(w) is a unit orientation of tangentSpace(M_y, w) for every w ∈ M';
- C(ω) = m_y∫_{M_y}⟨ω, ξ_y⟩ dH^m = |m_y|∫_{M'}⟨ω, sign(m_y)ξ_y⟩ dH^m whenever tsupport ω ⊆ B_{ρ'}(y);
- for open W ⊆ B_{ρ'}(y), ∫_{M'∩W} |m_y| dH^m = |m_y|·H^m(M_y ∩ W) ≤ |m_y|·H^m(M_y ∩ closedBall(y, ρ')) < ∞, since closedBall(y, ρ') is a compact subset of B_{ρ_y}(y).
This gives M_W(C) = |m_y|·H^m(M_y ∩ W) for every open W ⊆ B_{ρ'}(y).
(B2d) Densities.
- By (B2c) and (G7) (C¹ case), Θ^m(μ_C, w) = |m_y| for every w ∈ M_y ∩ B_{ρ'}(y).
- In particular |m_y| = Θ^m(μ_C, y) = 1 by (G1).
- Every such w has density 1 > 0, so w ∈ spt C by (G2).
(B2e) Consequences.
- M ∩ B_{ρ'}(y) = M_y ∩ B_{ρ'}(y), and this set lies in A₀ since spt C ⊆ A₀.
- C(ω) = ∫_M ⟨ω, ξ'_y⟩ dH^m for tsupport ω ⊆ B_{ρ'}(y), where ξ'_y := m_yξ_y is a continuous unit orientation.
- M_W(C) = H^m(M ∩ W) for open W ⊆ B_{ρ'}(y).
- Hence M is an embedded C¹ m-submanifold of ℝ^P contained in the (m+1)-dimensional subspace A₀, i.e. a C¹ hypersurface of A₀ ∖ {0}. It is relatively closed in ℝ^P ∖ {0}, because spt C is closed.

B3. (Global orientation and representation off the vertex.)
(B3a) Agreement on overlaps. If B_{ρ'}(y) ∩ B_{ρ'}(y') ≠ ∅, then ∫_M ⟨ω, ξ'_y − ξ'_{y'}⟩ dH^m = 0 for every ω supported in the overlap. Test with ω = φβ, where φ ranges over C^∞_c and β over a countable dense set of constant covectors. This gives ξ'_y = ξ'_{y'} H^m-a.e. on M in the overlap.
(B3b) A continuous global orientation. The set where ξ'_y ≠ ξ'_{y'} is relatively open in M and H^m-null. A nonempty relatively open subset of a C¹ m-submanifold has positive H^m-measure, so the two orientations agree everywhere on the overlap. This defines a continuous unit orientation ξ_M of M.
(B3c) Representation off the vertex. Let ω have tsupport ω ⊆ ℝ^P ∖ {0}.
- Cover the compact set tsupport ω by finitely many balls B_{ρ'}(y_j), y_j ∈ M, together with the open set ℝ^P ∖ spt C.
- Take a smooth partition of unity subordinate to this cover. On pieces supported in ℝ^P ∖ spt C both sides vanish, by vanish_off_support and because M ∩ (ℝ^P ∖ spt C) = ∅.
- Hence (†) C(ω) = ∫_M ⟨ω, ξ_M⟩ dH^m for every ω ∈ 𝒟^m(ℝ^P) with tsupport ω ⊆ ℝ^P ∖ {0}.
(B3d) Finiteness and mass off the vertex.
- For W open with compact closure in ℝ^P ∖ {0}, H^m(M ∩ W) < ∞, since finitely many balls B_{ρ'}(y_j) cover M ∩ closure(W).
- M is relatively closed in the open set ℝ^P ∖ {0}, hence Borel, and ξ_M (extended by 0 off M) is measurable. By oriented_piece_mass (second conclusion) with θ' :≡ 1, V := ℝ^P ∖ {0}, M' := M and ξ' := ξ_M, using (†): M_W(C) = H^m(M ∩ W) for such W.
- For 0 < ε < ρ, W_ε := B_ρ(0) ∖ closedBall(0, ε) is such a W, and oriented_piece_mass (first conclusion) applied to the representation R gives M_{W_ε}(C) ≤ ∫_{M_R∩W_ε} θ_R dH^m ≤ μ(closedBall(0, ρ)) < ∞. So H^m(M ∩ W_ε) ≤ μ(closedBall(0, ρ)); letting ε ↓ 0 (monotone convergence, 0 ∉ M) gives H^m(M ∩ B_ρ(0)) < ∞ for every ρ.

B4. (Cone structure; parent 5(β)(iii)–(iv).)
- Let t > 0 and let W be an open set with compact closure on which C vanishes. Then C vanishes on tW. Indeed, let tsupport ω ⊆ tW. The sibling child cone_pullback_identity with λ := t^{−1} gives ω' ∈ 𝒟^m(ℝ^P) with ω'(z) = t^{m}ω(tz) and C(ω') = C(ω). Since tsupport ω' = t^{−1}tsupport ω ⊆ W, we get C(ω) = C(ω') = 0.
- closure(tW) = t·closure(W) is compact. Hence Z(C) is invariant under all dilations, and so is spt C = ℝ^P ∖ Z(C). Thus M = tM for all t > 0: M is a cone.
- 0 ∈ closure(M), because ty → 0 as t ↓ 0 for y ∈ M. Also closure(M) ⊆ spt C = M ∪ {0} and 0 ∉ M. Hence closure(M) ∖ M = {0}.

B5. (Competitors and first variation; stationarity.)
(B5a) Deformation. Let Z ∈ C^∞_c(ℝ^P ∖ {0}; ℝ^P), put K_Z := spt Z, and choose an open W with compact closure in ℝ^P ∖ {0} and K_Z ⊆ W.
- For |t| < t₀ := 1/(1 + 2 sup|DZ|), the map Φ_t := id + tZ is a C^∞ diffeomorphism of ℝ^P equal to the identity off K_Z.
- Hence Φ_t(K_Z) = K_Z and Φ_t(W) = W. If Z(w) ∈ A₀ for all w, then also Φ_t(A₀) = A₀.
(B5b) The push-forward is a current. S_t(ω) := C(Φ_t^#ω), the push-forward Φ_{t#}C (Simon 6.2.23).
- Φ_t is proper, so Φ_t^# maps 𝒟^m(ℝ^P) into itself.
- Φ_t^# is sequentially continuous in the test-form topology: supports stay in Φ_t^{−1}(K), and derivatives converge uniformly by the chain rule. So S_t ∈ 𝒟_m(ℝ^P).
(B5c) S_t is an admissible competitor.
- Integer multiplicity. By the area formula on the rectifiable set M_R (Simon Ch. 6, 3.3–3.9), S_t is represented by (Φ_t(M_R), θ_R∘Φ_t^{−1}, ξ_t) with ξ_t(Φ_t x) := Λ_mDΦ_t(x)ξ_R(x)/|Λ_mDΦ_t(x)ξ_R(x)|. Here Φ_t(M_R) is Borel and countably m-rectifiable, its approximate tangent space at Φ_t(x) is DΦ_t(x)(T_xM_R), and the multiplicity is locally integrable since the Jacobians are bounded.
- Same boundary. m ≥ 2, so S_t(dφ) = C(Φ_t^#dφ) = C(d(Φ_t^#φ)) = 0 = C(dφ), using ∂C = 0.
- Compact support of the difference. If tsupport ω ∩ K_Z = ∅, then Φ_t^#ω = ω: at points off K_Z the map Φ_t is the identity nearby, and at points of K_Z both sides vanish because Φ_t(K_Z) = K_Z. So spt(S_t − C) ⊆ K_Z, a compact subset of W.
- Minimality of C in ℝ^P therefore gives M_W(C) ≤ M_W(S_t).
(B5d) Both masses are areas.
- For tsupport ω ⊆ W: S_t(ω) = C(Φ_t^#ω), with tsupport Φ_t^#ω ⊆ W ⊆ ℝ^P ∖ {0}.
- By (†) and the area formula for the injective smooth map Φ_t, S_t(ω) = ∫_{Φ_t(M)} ⟨ω, ξ_{M,t}⟩ dH^m, with ξ_{M,t} the transported unit orientation.
- Φ_t(M) ∩ W = Φ_t(M ∩ W) is Borel with finite H^m-measure (Φ_t is a diffeomorphism with Φ_t(W) = W, and H^m(M ∩ W) < ∞ by (B3d)), and ξ_{M,t} is measurable. By oriented_piece_mass (second conclusion) with θ' :≡ 1, V := W, M' := Φ_t(M) ∩ W and ξ' := ξ_{M,t}, M_W(S_t) = H^m(Φ_t(M) ∩ W) = H^m(Φ_t(M ∩ W)); by (B3d), M_W(C) = H^m(M ∩ W).
- So f_Z(t) := H^m(Φ_t(M ∩ W)) satisfies f_Z(t) ≥ f_Z(0) for |t| < t₀.
(B5e) First variation.
- By the area formula, f_Z(t) = ∫_{M∩W} J_t dH^m with J_t(x) := |(τ_1 + tDZ(x)τ_1)∧⋯∧(τ_m + tDZ(x)τ_m)|, for τ an orthonormal basis of T_xM.
- J_t(x) is smooth in t with derivatives bounded uniformly in x ∈ K_Z, J_t = 1 off K_Z, and ∂_tJ_t|_{t=0} = Σ_i τ_i·DZ(x)τ_i = div_M Z(x) (Simon Ch. 2, 5.1–5.3).
- So f_Z is differentiable at 0 with f_Z'(0) = ∫_M div_M Z dH^m. Since 0 is an interior minimum, ∫_M div_M Z dH^m = 0.
- For X ∈ C¹_c(ℝ^P ∖ {0}; ℝ^P), mollification gives such Z → X in C¹ with supports in a fixed compact set. Since H^m(M ∩ K) < ∞ (B3d), ∫_M div_M X dH^m = 0.
- Hence the varifold V := v(M, 1) is stationary in ℝ^P ∖ {0} (Simon Ch. 2, 5.7–5.8).

B6. (Smoothness and zero mean curvature; parent 5(β)(ii).)
- Apply Simon Ch. 5, Theorem 7.1, last part, in the open set ℝ^P ∖ {0} with N := ℝ^P (C^∞). Its hypotheses hold: V is stationary, θ ≡ 1, and Θ^m(V, y) = 1 at every y ∈ M by (G7).
- So for each y ∈ M and each q there is σ_q > 0 such that, after a rigid motion, spt V ∩ B_{σ_q}(y) = M ∩ B_{σ_q}(y) is the graph of a C^{q+2,α} function. This holds at every y ∈ M and for every q, so M is a C^∞ submanifold.
- Since V is stationary and M is smooth, the first variation formula (Simon Ch. 2, 4.29 and 5.10) gives ∫_M X·H_M dH^m = 0 for all X ∈ C¹_c(ℝ^P ∖ {0}; ℝ^P). So the mean curvature H_M ≡ 0.
- As M ⊆ A₀, M is a smooth minimal hypersurface of A₀ ∖ {0}, with closure(M) ∖ M = {0} (B4).

B7. (Stability B.1; parent 5(β)(v); Simon Ch. 2, 5.11–5.12.)
(B7a) Unit normal. Fix an orientation of A₀ and let ν be the unit normal of M in A₀ determined by ξ_M; ν is smooth on M.
(B7b) The variation field. Let ζ ∈ C^∞_c(M), with support K ⊆ M compact. Let Z ∈ C^∞_c(ℝ^P ∖ {0}; ℝ^P) satisfy Z(w) ∈ A₀ for all w and Z = ζν on M. It exists:
- extend ζν to a smooth A₀-valued map near K, by local extensions and a partition of unity;
- compose with the orthogonal projection onto A₀;
- multiply by a cutoff equal to 1 near K with compact support in ℝ^P ∖ {0}.
(B7c) Minimality at t = 0. With W and Φ_t as in (B5a), Φ_t(A₀) = A₀. By (B5d), f(t) := H^m(Φ_t(M ∩ W)) has a minimum at t = 0. f is C^∞ near 0:
- J_t² is a polynomial in t whose coefficients are bounded on M ∩ K_Z, and J_t² ≥ 1/2 for |t| small.
- So J_t is C^∞ in t with t-derivatives bounded uniformly on M ∩ K_Z, and J_t = 1 off K_Z.
- Since H^m(M ∩ W) < ∞, f may be differentiated under the integral.
Hence f'(0) = 0 and f''(0) ≥ 0.
(B7d) Second variation. Apply the second variation formula (Simon Ch. 2, 5.4 and 5.11) to the smooth stationary M:
- The acceleration ∂²Φ_t/∂t² vanishes. The variation field Z|_M = ζν is normal to M.
- (D_{τ_i}(ζν))^⊥ = (∇_{τ_i}ζ)ν. Indeed D_{τ_i}ν ∈ A₀ is orthogonal to ν, hence tangent to M.
- B(τ_i, τ_j) = h_{ij}ν, where A = (h_{ij}) is the second fundamental form of M in A₀.
- So f''(0) = ∫_M (|∇^Mζ|² − |A|²ζ²) dH^m (Simon 5.12 (‡)).
(B7e) Conclusion. B.1 holds: ∫_M (|∇^Mζ|² − |A|²ζ²) dH^m ≥ 0 for every ζ ∈ C^∞_c(M). By mollification in charts it extends to locally Lipschitz ζ with compact support in M: |A| is continuous on M, and the supports stay in a fixed compact subset of M.

B8. (Simons' theorem B.2: the printed proof.) Identify A₀ with ℝ^{m+1} by a linear isometry. Then M is a smooth m-dimensional cone in ℝ^{m+1} with zero mean curvature, closure(M) ∖ M = {0}, stable in the sense of B.1, and 2 ≤ m ≤ 6. We show |A| ≡ 0 on M.
(B8a) Simons' identity and inequality.
- In a local orthonormal frame, Simons' identity B.8 reads ½Δ_M|A|² = Σ_{i,j,k} h²_{ij;k} − |A|⁴ + h_{ij}H_{;ij} + H h_{mi}h_{mj}h_{ij}. It follows from the symmetry B.4, the Codazzi equations B.5, the Gauss equations B.6 and the commutation formula B.7.
- With H = 0 this is ½Δ_M|A|² = Σ h²_{ij;k} − |A|⁴.
- For a cone, Lemma B.11 gives Σ_{i,j,k} h²_{ij;k} − |∇_M|A||² ≥ 2r^{−2}|A|² wherever |A| > 0. Choose τ_m radial along the ray through x; then h_{mj} = 0 and h_{ij;m} = −r^{−1}h_{ij} by homogeneity. The algebra is SimonGMT AppendixB.simonsDefect_eq_sum_skew, four_mul_radialSkewSum_le and cone_simonsDefect_lower_bound.
- Where |A| = 0, ∇|A| = 0 H^m-a.e. (|A| is locally Lipschitz) and ½Δ|A|² = Σ h²_{ij;k} ≥ 0.
- Hence, H^m-a.e. on M, (1) ½Δ_M|A|² + |A|⁴ ≥ 2r^{−2}|A|² + |∇_M|A||².
(B8b) Basic inequality. Let ψ be locally Lipschitz with compact support in M, and insert ζ := |A|ψ in B.1:
 (2) ∫|A|⁴ψ² ≤ ∫|∇(|A|ψ)|² = ∫(|∇ψ|²|A|² + ψ²|∇|A||² + 2ψ|A|∇ψ·∇|A|).
Integration by parts and (1) give
 2∫ψ|A|∇ψ·∇|A| = ∫∇(ψ²)·∇(½|A|²) = −∫ψ²Δ_M(½|A|²) ≤ ∫ψ²(|A|⁴ − 2r^{−2}|A|² − |∇|A||²).
Combining: (3) 2∫_M r^{−2}ψ²|A|² dH^m ≤ ∫_M |A|²|∇_Mψ|² dH^m.
(B8c) Extension. (3) holds for every locally Lipschitz ψ on M with (4) ∫_M r^{−2}ψ²|A|² < ∞.
- For 0 < κ < 1 let γ_κ be Lipschitz with 0 ≤ γ_κ ≤ 1, γ_κ = 1 for |x| ∈ (κ, κ^{−1}), γ_κ = 0 for |x| < κ/2 or |x| > 2κ^{−1}, and |∇γ_κ| ≤ 3/|x|.
- ψγ_κ has compact support in M, since closure(M) ∖ M = {0}. Apply (3) to it.
- Use |∇(ψγ_κ)|² ≤ (1 + η)|∇ψ|²γ_κ² + (1 + η^{−1})ψ²|∇γ_κ|². By (4), ∫|A|²ψ²|∇γ_κ|² ≤ 9∫_{{κ/2<r<κ}∪{κ^{−1}<r<2κ^{−1}}} r^{−2}ψ²|A|² → 0.
- Let κ ↓ 0:
  - the left side converges by dominated convergence, with dominant r^{−2}ψ²|A|², which is integrable by (4);
  - the first term on the right is at most (1 + η)∫|A|²|∇ψ|², because γ_κ ≤ 1;
  - the second term on the right tends to 0.
  Then let η ↓ 0.
(B8d) Cone integrals.
- Σ := M ∩ ∂B_1(0) is a compact smooth (m−1)-dimensional submanifold. It is closed because closure(M) ∩ ∂B_1(0) = M ∩ ∂B_1(0), and the sphere is transversal to the cone M.
- (5) ∫_M f dH^m = ∫_0^∞ r^{m−1}∫_Σ f(rσ) dH^{m−1}(σ) dr for continuous f ≥ 0 on M.
- |A(x)|² = r^{−2}|A(x/|x|)|² by homogeneity. Put c_Σ := ∫_Σ |A|² dH^{m−1} < ∞.
(B8e) Choice of ψ.
- Choose ε > 0 with (m/2 − 2 + ε)² < 2 and (1 + ε)² < 2. This is possible exactly because 2 ≤ m ≤ 6, e.g. ε = 1/10 (SimonGMT AppendixB.exists_final_exponent).
- Put ψ := r^{1+ε}r₁^{1−m/2−2ε} with r₁ := max{1, r}. Then r^{−2}ψ² = r^{2ε} on {r < 1} and r^{2−m−2ε} on {r > 1}.
- By (5), ∫_M r^{−2}ψ²|A|² = c_Σ(∫_0^1 r^{m−3+2ε} dr + ∫_1^∞ r^{−1−2ε} dr) < ∞. So (4) holds.
- |∇_Mψ| = (1+ε)r^{ε} on {r < 1} and |m/2 − 2 + ε|r^{1−m/2−ε} on {r > 1}, since |∇_Mr| = 1 on a cone.
- So (3) becomes (6): 2∫_{M∩{r<1}} |A|²r^{2ε} + 2∫_{M∩{r>1}} |A|²r^{2−m−2ε} ≤ (1+ε)²∫_{M∩{r<1}} |A|²r^{2ε} + (m/2 − 2 + ε)²∫_{M∩{r>1}} |A|²r^{2−m−2ε}, with all integrals finite.
- Since 2 − (1+ε)² > 0 and 2 − (m/2 − 2 + ε)² > 0, both integrals vanish. As |A| is continuous, |A| ≡ 0 on M.

B9. (Hyperplane.)
- |A| ≡ 0 means ν is locally constant on M. So each connected component M_c of M lies in an affine hyperplane of A₀.
- That hyperplane passes through 0. The ray through a point of M_c is connected, lies in M (B4) and meets M_c, so it lies in M_c. Hence M_c ⊆ H_c for an m-dimensional linear subspace H_c ⊆ A₀.
- M_c is open in H_c, being an m-submanifold of the m-plane H_c. It is closed in H_c ∖ {0}, since M is relatively closed in ℝ^P ∖ {0} and M_c is closed in M. H_c ∖ {0} is connected (m ≥ 2), so M_c = H_c ∖ {0}.
- Suppose two components had H_c ≠ H_{c'}. Then H_c ∩ H_{c'} has dimension m − 1 ≥ 1 and contains some w ≠ 0 lying in both M_c and M_{c'}, which is impossible.
- Hence M = H₀ ∖ {0} for a single m-dimensional linear subspace H₀ ⊆ A₀.

B10. (Density at the vertex.)
(B10a) Constant orientation. H₀ ∖ {0} is connected (m ≥ 2). For y ∈ M, ξ_M(y) is a unit orientation of tangentSpace(M, y) = H₀; fixing one unit orientation ξ_{H₀} of H₀, orientation_sign gives ξ_M(y) ∈ {ξ_{H₀}, −ξ_{H₀}}. A continuous map from a connected set into this two-point set is constant; so ξ_M is constant, say ξ.
(B10b) Global representation. For every ω ∈ 𝒟^m(ℝ^P), (B0.1) and (†) give
 C(ω) = lim_{ε↓0} C((1 − χ_ε)ω) = lim_{ε↓0} ∫_{H₀} (1 − χ_ε)⟨ω, ξ⟩ dH^m = ∫_{H₀} ⟨ω, ξ⟩ dH^m,
by dominated convergence (H^m(H₀ ∩ {0}) = 0).
(B10c) Mass of balls. By oriented_piece_mass (second conclusion) with θ' :≡ 1, V := ℝ^P, M' := H₀ (closed, hence Borel) and the constant ξ' := ξ, and (B10b): M_{B_ρ(0)}(C) = H^m(H₀ ∩ B_ρ(0)) = ω_mρ^m < ∞, because H^m on the m-plane H₀ is m-dimensional Lebesgue measure.
(B10d) Conclusion. (ω_mρ^m)^{−1}M_{B_ρ(0)}(C) ≡ 1, so Θ^m(μ_C, 0) = 1, and by (G1) θ = 1 ≤ 1.
This proves the statement. ∎

## Key steps

1. The vertex is negligible for C; if spt C ⊆ {0} then C = 0 and θ = 0. Otherwise, regularity with density one off the vertex makes C = [[M]] near each point of M = spt C ∖ {0}, with a continuous global orientation; oriented_piece_mass gives M_W(C) = H^m(M ∩ W) away from 0.
2. spt C is a cone (cone_pullback_identity), so M is a C¹ hypersurface cone of A₀ ∖ {0} with closure(M) ∖ M = {0}.
3. The competitors (id + tZ)_#C are admissible; minimality gives first variation zero, Ch. 5, 7.1 makes M smooth and minimal, and the second variation for Z = ζν tangent to A₀ gives stability B.1.
4. Simons' identity B.8 and Lemma B.11 inserted in B.1 with the cut-offs γ_κ and ψ = r^{1+ε}r₁^{1−m/2−2ε} (2 ≤ m ≤ 6) force |A| ≡ 0; so M = H₀ ∖ {0}, C = [[H₀]] (orientation_sign), and θ = Θ^m(μ_C, 0) = 1 ≤ 1.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; grep -n simongmt -A4 local-references/123e8435b4a2469b/project/lake-manifest.json`
- `sha256sum local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `grep -n 'theorem finrank_add_inf_finrank_orthogonal|theorem IsCompact.tendsto_subseq|theorem isOpen_iUnion_countable' local-references/123e8435b4a2469b/mathlib/Mathlib/{Analysis/InnerProductSpace/Projection/FiniteDimensional,Topology/Sequences,Topology/Bases}.lean`
- `grep -n 'def massOn|massOn_mono|def zeroRegion|def support|Zero (GeometricCurrentOn' simongmt/Poincare/SimonGMT/Chapter06/{Mass,CurrentLocalEquality,Currents}.lean`
- `grep -rn 'theorem <name>' simongmt/Poincare/SimonGMT for bvVariationOn_le_liminf_of_locallyL1, cone_simonsDefect_lower_bound, exists_final_exponent, injective_area_formula_of_injective_derivative, exteriorDerivative_affinePullbackForm, tsupport_exteriorDerivative_subset, exteriorDerivative_sq, simonsDefect_eq_sum_skew, four_mul_radialSkewSum_le, WeakDerivativesZero.ae_eq_const`
- `header of simongmt Chapter03/FinitePerimeter.lean and Chapter05/Basic.lean; grep -rln 'Allard|DeGiorgi|BVCompact' simongmt/Poincare/SimonGMT`
- `python3 scan of dag.json: statuses and frozen types of the 8 siblings, the 5 reused names, the 6 new codim1_ names, the root theorems DensityAndTangentCones, DensityOneImpliesRegular, MinimizingImpliesStationary and dor_stationary_cycle_epsilon_regularity; keyword scan for overlapping nodes (regcomp_codim_one_preliminaries, regcomp_cop_region_support_subset, regcomp_cop_region_boundary_vanishes)`
- `for r in $(git for-each-ref refs/heads refs/remotes): git grep -l codim1_ $r -- 'GMT/*.lean' (2056 refs, no match)`
- `lean -DautoImplicit=false /tmp/codim1-v6/check/Types.lean; lean -DautoImplicit=false /tmp/codim1-v6/check/Assembly.lean (LEAN_PATH taken from .lake/build/lib/lean/GMT/Ch07/Submission.trace)`
- `ps -eo pid,lstart,args; max_nodes timeline over .humanize/swarm-configs; /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py _decompose, _solve_children, _existing_lean_name_problem, _install_parent_supplied_child_handoff; store.py ensure`
- `sed -n 560,1000p book/sources/chapter-07-source.txt (7.4–7.5.8); sed -n 1286,1330p book/sources/chapter-02-source.txt (5.6–5.8); sed -n 1300,1370p book/sources/chapter-05-source.txt (Theorem 7.1)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/FinitePerimeter.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter05/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/AppendixB/ConeDefect.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/AppendixB/SimonsInequalities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1/decomposition-v5.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1/decomposition-audit-v5.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-07-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-02-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-05-source.txt`
- `/tmp/codim1-v6/check/Types.lean`
- `/tmp/codim1-v6/check/Assembly.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/swarm-configs/33c6cc03ee394bfbb35f84931b68580c.json`

Pins match. The snapshot manifest records project b4d606db and Mathlib 25730c7c, equal to workspace HEAD and .lake/packages/mathlib; the snapshot lake-manifest pins simongmt 2b366308, equal to .lake/packages/simongmt. The snapshot Contract.lean, the workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…), so the frozen types of this node and of the 8 siblings are unchanged since v5.
Library.
- The snapshot Mathlib has finrank_add_inf_finrank_orthogonal (FiniteDimensional.lean:89), IsCompact.tendsto_subseq (Sequences.lean:298) and isOpen_iUnion_countable (Bases.lean:932); the glue uses all three.
- SimonGMT supplies massOn and massOn_mono, support = U \ zeroRegion and the zero current (Chapter06). It also supplies BV lower semicontinuity (Chapter02/BV.lean:225), the Simons algebra (AppendixB/ConeDefect.lean:228, SimonsInequalities.lean:88), and the area-formula, exterior-derivative and affine-pullback lemmas cited by the children.
- Its headers state that De Giorgi's theorem (Chapter03/FinitePerimeter.lean) and Allard's theorem (Chapter05/Basic.lean) are not provided, and no BV compactness theorem exists. These remain book citations inside the children.
DAG.
- The 5 reused declarations are accepted with byte-identical types.
- DensityAndTangentCones, DensityOneImpliesRegular, MinimizingImpliesStationary and dor_stationary_cycle_epsilon_regularity are not accepted, so they cannot be reused.
- regcomp_codim_one_preliminaries and its children overlap region_support_cycle, but they are unaccepted and have other types.
- The 6 new codim1_ names are free in dag.json, GMT/, SimonGMT and all 2056 refs.
Lean.
- Types.lean elaborates all 11 child types (exit 0, only sorry warnings).
- Assembly.lean proves CodimensionOneRegularity from the 8 sibling and 11 child types taken as axioms (exit 0). Its axioms are propext, Classical.choice, Quot.sound, 5 new children and 7 siblings; no root proposition occurs.
Infrastructure. The current controller (pid 23222) runs with max_nodes = 1000 and dag.json has 457 nodes, so the 6 new nodes can be activated. The accepted v5 was dropped by the old controller, which had max_nodes = 200 loaded.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
