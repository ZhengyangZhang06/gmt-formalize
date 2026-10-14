<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1 -->

## Theorem `Submission.codim1_region_density_one_dense`

Let P, n ∈ ℕ with n ≥ 1, U, N, E ⊆ ℝ^P, ξ_N : ℝ^P → Λ_{n+1}(ℝ^P) and T ∈ 𝒟_n(U). Assume U is open, InClassO n U N ξ_N, E is measurable with E ⊆ N ∩ U, T(ω) = ∫_E ξ_N(x)(dω(x)) dH^{n+1}(x) for every ω ∈ 𝒟^n(U) (IsBoundaryOfRegion T E ξ_N), and T is integer multiplicity (IsIntegerMultiplicity T). Then for every x ∈ spt T and every ρ > 0 there is y ∈ spt T ∩ B_ρ(x) with Θ^n(μ_T, y) = 1 (HasMassDensity T y 1).

Node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1038

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4339, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4336, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1285, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1081

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4713, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4721, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4725, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1285, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1081, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1287, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4739, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4748, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4755

## Lean problem

Declaration: `Submission.codim1_region_density_one_dense`

```lean
∀ (P n : ℕ) (U N E : Set (Euclid P)) (ξN : Euclid P → MultiVector P (n + 1)) (T : GeometricCurrentOn U n), 1 ≤ n → IsOpen U → InClassO n U N ξN → MeasurableSet E → E ⊆ N ∩ U → IsBoundaryOfRegion T E ξN → IsIntegerMultiplicity T → ∀ x ∈ T.support, ∀ ρ : ℝ, 0 < ρ → ∃ y ∈ T.support ∩ ball x ρ, HasMassDensity T y 1
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
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Parent step 1 (C1) of the supplied proof of CodimensionOneRegularity: Simon 7.5.2 and its consequence (‡) “Θ^n(μ_T, x) = 1 for μ_T-a.e. x” (chapter-07.txt lines 757–770), which rests on Ch. 6, 2.35 (chapter-06.txt lines 606ff.) and De Giorgi's structure theorem, Ch. 3, 4.3 (chapter-03.txt lines 588–606); densities of rectifiable sets are Ch. 3, 1.8(2)–1.9 (chapter-03.txt lines 298–323). This is part A1 of the previously reviewed analytic core of this node, stated as its own theorem. Departures from that text: the hypothesis is only that T is integer multiplicity (all that its proof used of minimality); the mass facts (G5c), (G6) are cited from the sibling child oriented_piece_mass; the Riesz map is replaced by the dual map of unit_orientation_dual. The conclusion is the form of 5.2(‡) used by the parent: density-one points are dense in spt T.

Sibling children used.
- region_support_cycle (Submission.codim1_region_support_cycle): under the hypotheses below, n + 1 ≤ P, spt T ⊆ U ∩ N and ∂T = 0.
- oriented_piece_mass (Submission.codim1_massOn_eq_lintegral_of_oriented_rep): if V ⊆ U is open, M' ⊆ V Borel, θ' ≥ 0 measurable, ξ' a.e. strongly measurable on M' and H^k-a.e. on M' a unit orientation of some subspace, and T(ω) = ∫_{M'} θ'·ξ'(ω) dH^k whenever tsupport ω ⊆ V, then for every open W ⊆ V: M_W(T) ≤ ∫_{M'∩W} θ' dH^k, with equality when the right side is finite.
- unit_orientation_dual (Submission.dor_ims_unitOrientation_dual): a continuous linear L : Λ_k → Λ^k with |ξ(α)| ≤ |α|, |L(ξ)| ≤ 1 and ξ(L(ξ)) = 1 for every unit orientation ξ of a subspace.
- orientation_sign (Submission.rsdic_unitOrientation_eq_or_eq_neg): two unit orientations of the same subspace Q satisfy w = v or w = −v.

Notation.
- H^d := μHE[d]. On a d-dimensional affine plane it is d-dimensional Lebesgue measure (Hausdorff measure is isometry invariant and μHE[d] = volume on ℝ^d). ω_d := unitBallVolume d is H^d of a unit d-disc. B_ρ(y) := ball y ρ.
- For a k-covector α, |α| is the Euclidean coefficient norm (covectorEuclideanNorm). M_W(T) := T.massOn W = sup{ofReal T(ω) : ω ∈ 𝒟^k(U), tsupport ω ⊆ W, |ω| ≤ 1 pointwise}; such ω are admissible for M_W(T).
- “T vanishes on W” means T(ω) = 0 whenever tsupport ω ⊆ W. Z(T) is the union of the open W with compact closure in U on which T vanishes, and spt T := U ∖ Z(T).
- “Θ^n(μ_T, y) = θ” means HasMassDensity T y θ: θ ≥ 0 and M_{B_ρ(y)}(T)/(ω_nρ^n) → θ as ρ ↓ 0.
- For an IMRep R = (M_R, θ_R, ξ_R) of T, μ_R(A) := ∫_{M_R∩A} θ_R dH^n; μ_R(K) < ∞ for compact K ⊆ U (IMRep.locallyIntegrable_mult).

General facts (T ∈ 𝒟_n(U), U open).
(G2) Positive density forces support. If T vanishes on an open W, then M_{W'}(T) = 0 for every W' ⊆ W, since every admissible form gives the value 0. Hence if y ∈ U has Θ^n(μ_T, y) = θ > 0 and y ∉ spt T, then y lies in an open W on which T vanishes, M_{B_t(y)}(T) = 0 for small t, and the density is 0 ≠ θ. So such y lies in spt T.
(G3) Mass near support points. Let x ∈ spt T and let W ∋ x be open with compact closure in U. Then T does not vanish on W (otherwise W ⊆ Z(T) ∋ x), so T(ω) ≠ 0 for some ω ∈ 𝒟^n(U) with tsupport ω ⊆ W. With s := max|ω| > 0, one of ±ω/s is admissible for M_W(T) and has positive value; so M_W(T) > 0.
(G7) Density of rectifiable sets (Simon Ch. 3, 1.8(2), 1.9). If M' ⊆ ℝ^P is countably n-rectifiable and H^n-measurable with H^n(M') < ∞, then lim_{t↓0} H^n(M' ∩ B_t(w))/(ω_nt^n) = 1 for H^n-a.e. w ∈ M'.

Proof. Fix P, n ≥ 1, U, N, E, ξ_N, T satisfying the hypotheses, x ∈ spt T and ρ > 0. Fix an IMRep R = (M_R, θ_R, ξ_R) of T (T is integer multiplicity). By region_support_cycle, x ∈ spt T ⊆ U ∩ N.
1. (Graph chart of N at x.)
(1a) Tangent plane. IsOrientation (n+1) N ξ_N at x gives a subspace Π with Π = tangentSpace(N, x) (as sets) and IsUnitOrientationOf(ξ_N(x), Π). The orthonormal family in that definition has n + 1 vectors and spans Π, so dim Π = n + 1. Put ξ_Π := ξ_N(x), p := orthogonal projection onto Π and p^⊥ := I − p.
(1b) The chart is a homeomorphism. Take a chart (V, W, ψ) of N at x (IsEmbeddedSubmanifold 2 (n+1) N) and z₀ ∈ V with ψ(z₀) = x. ψ : V → W ∩ N is a continuous bijection, and V ∩ ψ^{−1}(K) is compact for every compact K ⊆ W. A continuous map from V into the locally compact Hausdorff space W with this property is a closed map into W. Hence ψ maps relatively closed subsets of V onto relatively closed subsets of W ∩ N (in particular W ∩ N = ψ(V) is closed in W), and the continuous bijection ψ : V → W ∩ N is a homeomorphism.
(1c) The derivative has range Π. For v ∈ ℝ^{n+1} and small ε > 0, t ↦ ψ(z₀ + εtv) (t ∈ (−1, 1)) is a C¹ curve in N through x with derivative εDψ(z₀)v at t = 0; so range Dψ(z₀) ⊆ tangentSpace(N, x) = Π. Dψ(z₀) is injective and dim Π = n + 1, so range Dψ(z₀) = Π.
(1d) The graph map u. p∘(ψ − x) has invertible derivative p∘Dψ(z₀) : ℝ^{n+1} → Π at z₀. By the inverse function theorem it is a C² diffeomorphism of an open V₀ ∋ z₀ onto an open neighbourhood O of 0 in Π. ψ(V₀) is relatively open in W ∩ N by (1b), so ψ(V₀) ⊇ N ∩ B_s(x) for some s > 0. Put u := p^⊥∘(ψ − x)∘(p∘(ψ − x)|_{V₀})^{−1} : O → Π^⊥; it is C², u(0) = 0, and Du(0) = 0 because range Dψ(z₀) = Π. Choose r₁ > 0 with closedBall(x, 2r₁) ⊆ U ∩ W ∩ B_s(x), put δ₂ := r₁, and choose δ₁ ∈ (0, r₁) such that D := Π ∩ B_{δ₁}(0) ⊆ O, |Du| ≤ 1 on D and |u| < δ₂/2 on D. The open cylinder Z := {x + v + h : v ∈ Π, |v| < δ₁, h ∈ Π^⊥, |h| < δ₂} has closure in closedBall(x, √2·r₁); so closure Z is compact and contained in U ∩ W ∩ B_s(x).
(1e) The parametrization G. Put G(v) := x + v + u(v) for v ∈ D. Then N ∩ Z = G(D): a point q ∈ N ∩ Z lies in N ∩ B_s(x) ⊆ ψ(V₀), so v := p(q − x) ∈ O with |v| < δ₁ and p^⊥(q − x) = u(v), i.e. q = G(v) with v ∈ D; conversely G(v) = ψ((p∘(ψ − x)|_{V₀})^{−1}(v)) ∈ N and |u(v)| < δ₂, so G(D) ⊆ N ∩ Z. G is an injective C² map with p(G(v) − x) = v and DG(v) = I + Du(v) on Π. In particular N ∩ Z is relatively closed in Z, being the graph of a continuous map over D intersected with Z. Applying (1c) to the parametrization G at v (for t ↦ G(v + εtw) and, conversely, writing a C¹ curve γ in N through G(v) as γ = G∘(p∘(γ − x)) near t = 0) gives tangentSpace(N, G(v)) = DG(v)Π.
(1f) Orientation. Put J(v) := det(DG(v)τ_i · DG(v)τ_j)^{1/2} > 0 for an orthonormal basis τ of Π with ξ_Π(β) = ±β(τ), and η(v) := Λ_{n+1}DG(v)ξ_Π/J(v), i.e. η(v)(α) := ξ_Π(α(DG(v)·, …, DG(v)·))/J(v). Then ξ_N(G(v)) = η(v) for every v ∈ D:
- η(v) is a unit orientation of DG(v)Π: Gram–Schmidt writes (DG(v)τ_1, …, DG(v)τ_{n+1}) = σU with σ an orthonormal basis of DG(v)Π and U upper triangular with positive diagonal; by multilinearity and alternation α(DG(v)τ) = det(U)·α(σ), and J(v) = det(UᵀU)^{1/2} = det U. So η(v)(α) = ±α(σ).
- ξ_N(G(v)) is a unit orientation of tangentSpace(N, G(v)) = DG(v)Π (IsOrientation). By orientation_sign, ξ_N(G(v)) = s(v)·η(v) with s(v) ∈ {1, −1}.
- With L from unit_orientation_dual, s(v) = ξ_N(G(v))(L(η(v))), because η(v)(L(η(v))) = 1. The right side is continuous in v ∈ D: ξ_N is continuous on N, G and DG are continuous (u ∈ C²), J > 0 is continuous, L is continuous linear, and evaluation is continuous. D is connected, so s is constant, and s(0) = 1 because G(0) = x, DG(0) = I on Π and η(0) = ξ_Π = ξ_N(x).
2. (Local formula.) Let F := {v ∈ D : G(v) ∈ E}; F is Borel (E is measurable and G continuous) and E ∩ Z = G(F), because E ⊆ N. Let ω ∈ 𝒟^n(U) with tsupport ω ⊆ Z.
- dω vanishes off tsupport ω ⊆ Z. The area formula for the injective C¹ map G (SimonGMT injective_area_formula_of_injective_derivative), with Jacobian J, and (1f) give
 T(ω) = ∫_{E∩Z} ξ_N(dω) dH^{n+1} = ∫_F ξ_N(G(v))(dω(G(v)))J(v) dv = ∫_F ξ_Π((G^#dω)(v)) dv.
- G^{−1}(tsupport ω) = p((tsupport ω ∩ N) − x) is compact (tsupport ω ∩ N is closed in the compact tsupport ω, because N ∩ Z is relatively closed in Z), so G^#ω is a compactly supported C¹ n-form on D, and G^#dω = d(G^#ω) (G is C²).
- Identify Π with ℝ^{n+1} by a linear isometry carrying ξ_Π to e_1∧⋯∧e_{n+1}. A compactly supported C¹ n-form β on D is β = Σ_j(−1)^{j−1}φ_j dv^1∧⋯∧\widehat{dv^j}∧⋯∧dv^{n+1} for a vector field φ_β = (φ_1, …, φ_{n+1}), with |β| = |φ_β| and ξ_Π(dβ) = div φ_β.
- Hence (*) T(ω) = ∫_F div φ_{G^#ω} dv.
3. (Locally finite perimeter; Simon Ch. 6, 2.35.) For 0 < s' < δ₁ put D_{s'} := Π ∩ B_{s'}(0) and Z_{s'} := {w ∈ Z : |p(w − x)| < s'}.
- Fix χ ∈ C^∞(ℝ; [0, 1]) with χ = 1 on (−∞, δ₂/2] and χ = 0 on [3δ₂/4, ∞). Put ζ(w) := χ(|p^⊥(w − x)|), smooth because χ is constant near 0, and π(w) := p(w − x).
- Let φ be a smooth vector field with compact support in D_{s'} and |φ| ≤ 1, with corresponding n-form β, and put ω_φ := ζ·π^#β. Then ω_φ is smooth, tsupport ω_φ ⊆ {w : π(w) ∈ spt φ, |p^⊥(w − x)| ≤ 3δ₂/4} is a compact subset of Z_{s'}, so ω_φ ∈ 𝒟^n(U), and G^#ω_φ = β (π∘G = id and ζ∘G = 1 on D, as |u| < δ₂/2).
- |ω_φ| ≤ 1. Choose an orthonormal basis f_1, …, f_P of ℝ^P whose first n + 1 vectors are those of the isometry Π ≅ ℝ^{n+1}. In the basis of increasing wedges of the f's, the coefficients of ω_φ(w) = ζ(w)·β(π(w))∘p are ζ(w) times those of β(π(w)) for index sets inside {1, …, n+1} and 0 otherwise; so their square sum is ζ(w)²|φ(π(w))|² ≤ 1. The Euclidean coefficient norm does not depend on the orthonormal basis: coefficients transform by the n-th compound matrix C_n(O) of the orthogonal change-of-basis matrix O, and C_n(O)C_n(O)ᵀ = C_n(OOᵀ) = I by the Cauchy–Binet formula. (Only a bound |ω_φ| ≤ c₀ with c₀ independent of φ is needed below, and such a bound is immediate since the coefficients of ω_φ depend linearly on φ.)
- So ω_φ is admissible for M_{Z_{s'}}(T). By (*) and oriented_piece_mass (first conclusion) applied to the representation R (V := U, M' := M_R, θ' := θ_R, ξ' := ξ_R, W := Z_{s'}):
 ∫_F div φ = T(ω_φ) ≤ M_{Z_{s'}}(T) ≤ ∫_{M_R∩Z_{s'}} θ_R dH^n ≤ μ_R(closure Z) < ∞;
 the same holds for −φ.
- Smooth fields suffice in the definition of the variation (mollify a C¹ field; supports stay in D_{s'} and |φ| ≤ 1 is preserved). So |D1_F|(D_{s'}) ≤ μ_R(closure Z) < ∞ for every s' < δ₁, and F has locally finite perimeter in D.
4. (De Giorgi; Simon Ch. 3, 4.3.) The reduced boundary ∂*F is countably n-rectifiable, |D1_F| = H^n⌞∂*F on D, and with the measure-theoretic inner normal ν_F, ∫_F div φ = −∫_{∂*F} φ·ν_F dH^n for compactly supported C¹ fields φ on D. Since H^n is Borel regular and H^n(∂*F ∩ D_{s'}) < ∞, fix a Borel set B ⊆ D with ∂*F ∩ D ⊆ B and H^n(B ∖ ∂*F) = 0; all integrals over ∂*F below are integrals over B. For v ∈ ∂*F let ξ_F(v) be the unit simple n-vector of the plane ν_F(v)^⊥ ⊆ Π with ξ_F(v)(β) = −φ_β(v)·ν_F(v) for n-covectors β on Π. Then ∫_F ξ_Π(dβ) = ∫_{∂*F} ξ_F(β) dH^n.
5. (Multiplicity-one representation.) Put D' := D_{δ₁/2}, Z₀ := Z_{δ₁/2} (an open set containing x) and M' := G(B ∩ D') = {w ∈ N ∩ Z : p(w − x) ∈ B ∩ D'}, a Borel set (N ∩ Z is relatively closed in Z) with M' ⊆ Z₀.
- Let ω ∈ 𝒟^n(U) with tsupport ω ⊆ Z₀; then G^#ω has support in D'. By (*), step 4 with β = G^#ω, and the area formula for G on the rectifiable set B ∩ D' (Simon Ch. 3, 2.4–2.7, with Jacobian J'(v) := |Λ_nDG(v)ξ_F(v)| > 0),
 T(ω) = ∫_{M'} ξ'(w)(ω(w)) dH^n(w), where ξ'(G(v)) := Λ_nDG(v)ξ_F(v)/J'(v).
- M' is countably n-rectifiable (a Lipschitz image of a rectifiable set), and ξ' is a measurable field of unit simple n-vectors, i.e. ξ'(w) is a unit orientation of an n-plane (Gram–Schmidt as in (1f)).
- H^n(M') = ∫_{B∩D'} J' dH^n ≤ 2^{n/2}·|D1_F|(D') < ∞, because |Du| ≤ 1 gives ‖DG‖ ≤ √2, hence J' ≤ ‖DG‖^n ≤ 2^{n/2}.
- By oriented_piece_mass (second conclusion) with V := Z₀, θ' :≡ 1 and this M', ξ': M_W(T) = H^n(M' ∩ W) for every open W ⊆ Z₀.
6. (Density one a.e. on M'.) By (G7), for H^n-a.e. w ∈ M', H^n(M' ∩ B_t(w))/(ω_nt^n) → 1 as t ↓ 0. For such w, B_t(w) ⊆ Z₀ for small t (w ∈ M' ⊆ Z₀, Z₀ open), so step 5 gives M_{B_t(w)}(T) = H^n(M' ∩ B_t(w)); hence Θ^n(μ_T, w) = 1.
7. (Conclusion.)
- W' := Z₀ ∩ B_ρ(x) is open, contains x, and has compact closure in U.
- By (G3), M_{W'}(T) > 0, so H^n(M' ∩ W') > 0 by step 5.
- The exceptional set of step 6 is H^n-null, so some w ∈ M' ∩ W' has Θ^n(μ_T, w) = 1.
- By (G2), w ∈ spt T. So y := w ∈ spt T ∩ B_ρ(x) and HasMassDensity T y 1. ∎

## Key steps

1. spt T ⊆ N (region_support_cycle); near x ∈ spt T, N is a C² graph G(v) = x + v + u(v) over T_xN with ξ_N(G(v)) = Λ_{n+1}DG(v)ξ_N(x)/J(v) (orientation_sign, and continuity of the sign via unit_orientation_dual).
2. In the chart, T(ω) = ∫_F div φ_{G^#ω} with F = G^{−1}(E); testing with ζ·π^#β and the mass bound of oriented_piece_mass for an IMRep of T gives finite perimeter of F (Simon 6.2.35).
3. De Giorgi's structure theorem writes T = [[G(∂*F)]] with multiplicity one near x; oriented_piece_mass gives M_W(T) = H^n(G(∂*F) ∩ W).
4. Rectifiable sets have density one a.e., and positive mass near x forces a density-one point of spt T in every ball about x.

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
