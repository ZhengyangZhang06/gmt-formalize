<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.density_gap-a1.origin_regularity-a1 -->

## Theorem `Submission.dimred_cdg_minimizing_origin_regular`

Let P, j ∈ ℕ with 1 ≤ j ≤ P. Then there is a real δ > 0 with the following property. Let C ∈ 𝒟_j(ℝ^P) (GeometricCurrentOn (univ : Set (Euclid P)) j) be minimizing in ℝ^P (IsMinimizingIn C univ, Simon 7.1.1; in particular C is integer multiplicity), with ∂C = 0 (BoundaryVanishes C) and 0 ∈ spt C (C.support), and suppose M_{B_ρ(0)}(C) ≤ (1 + δ)·ω_j·ρ^j in [0, ∞] for every real ρ with 0 < ρ ≤ 1, i.e. C.massOn (ball 0 ρ) ≤ ofReal(1 + δ)·unitBallVolume j·ofReal(ρ^j); here B_ρ(0) is the open ball, M_W = massOn (Simon 6.2.5) and ω_j = unitBallVolume j is the Lebesgue measure of the unit ball of ℝ^j. Then 0 ∈ reg C (regularSet C, Simon 7.4.1 as in the contract: 0 ∈ spt C and there are ρ' > 0, m ∈ ℤ ∖ {0} and an embedded oriented C¹ j-submanifold M ∋ 0 of locally finite Hʲ-measure in B_{ρ'}(0) with C = m[[M]] in B_{ρ'}(0)).

Node: `root.dimension_reduction_results-a1.density_gap-a1.origin_regularity-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1028

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/667, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6030, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6046, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6098, https://github.com/ZhengyangZhang06/gmt-formalize/issues/974

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6938, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6952

## Lean problem

Declaration: `Submission.dimred_cdg_minimizing_origin_regular`

```lean
∀ (P j : ℕ), 1 ≤ j → j ≤ P → ∃ δ : ℝ, 0 < δ ∧ ∀ C : GeometricCurrentOn (univ : Set (Euclid P)) j, IsMinimizingIn C univ → BoundaryVanishes C → (0 : Euclid P) ∈ C.support → (∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → C.massOn (ball 0 ρ) ≤ ENNReal.ofReal (1 + δ) * unitBallVolume j * ENNReal.ofReal (ρ ^ j)) → (0 : Euclid P) ∈ regularSet C
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

- Parent DAG node: `root.dimension_reduction_results-a1.density_gap-a1`
- Child DAG node: `root.dimension_reduction_results-a1.density_gap-a1.origin_regularity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 7, Lemma 1.2 (minimizing currents are stationary; chapter-07.txt lines 29–60), here in the flat case N = ℝ^P, followed by Allard's Regularity Theorem (Ch. 5, 5.2; chapter-05.txt lines 1008–1032) applied at the origin. This is how the book itself uses them in 7.4.3 (chapter-07.txt lines 626–631: "by Allard's Theorem 5.2 of Ch. 5 we have y ∈ reg T … (1.2 justifies the use of 5.2 of Ch. 5)") and in the proof of 7.4.4(8) (lines 673–675).
Every analytic input is a sibling of this decomposition. E and K are comparator-accepted declarations, reused by exact name and type; F, G and J are siblings declared under fresh names; no unaccepted declaration of another DAG branch is used:
- E = imrep_mass_support (Submission.dor_imrep_massOn_eq_measure_and_support, comparator-accepted);
- F = c1_pushforward (Submission.dimred_cdg_c1_diffeo_pushforward_im);
- G = first_variation_bound (Submission.dimred_cdg_pushforward_massOn_le_first_variation);
- J = allard_graph (Submission.dimred_cdg_allard_bounded_curvature_graph);
- K = graph_cycle_regular (Submission.dor_graph_supported_cycle_regular, comparator-accepted).
Notation: for R = (M, θ, ξ) ∈ IMRep, μ := R.measure = θH^j⌞M and δV(X) := R.firstVariation X = ∫_M θ div_M X dH^j. B_r(x) is the open ball (Lean ball) and B̄_r(x) the closed ball; spt X := tsupport X; ω_j := unitBallVolume j; M_W := massOn; spt C := C.support.
1. (Dimensions and constants.) Since j ≤ P, write P = j + k with k := P − j (in Lean: obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le), so ℝ^P is literally Euclid (j + k). Apply J with n := j ≥ 1, this k and ε := 1/4. It yields δ₀ > 0 and γ ∈ (0, 1], depending only on j and k, i.e. only on P and j. Put δ := δ₀ > 0. This δ is fixed before C is chosen, as the statement requires.
2. (Representation, mass and support.) Let C satisfy the hypotheses for this δ. IsMinimizingIn C univ contains IsIntegerMultiplicity C, so there is R = (M, θ, ξ) ∈ IMRep univ j with R.Represents C. Apply E with U := ℝ^P (open), T := C and R:
- (E1) M_W(C) = μ(W) for every open W ⊆ ℝ^P;
- (E2) spt C = ℝ^P ∩ spt μ = spt μ.
Since 0 ∈ spt C by hypothesis, 0 ∈ spt μ.
3. (Stationarity: δV(X) = 0 for every C¹ vector field X : ℝ^P → ℝ^P with compact support.) This is Simon 7.1.2 for N = ℝ^P. Fix such an X and put K := spt X, a compact set.
 3.1 DX is continuous with compact support, so A := sup_x ‖DX(x)‖ is finite, and A ≥ 0. By the mean value inequality on the convex set ℝ^P, |X(x) − X(y)| ≤ A|x − y| for all x, y.
 3.2 For t ∈ ℝ let φ_t(y) := y + tX(y). Each φ_t is C¹. φ_t = id outside K, since X = 0 there. Dφ_t(x) = I + tDX(x), so ‖Dφ_t(x) − I − tDX(x)‖ = 0 ≤ ε|t| for all ε > 0, t and x.
 3.3 Let |t|A < 1.
 (a) φ_t is injective: φ_t(x) = φ_t(y) gives x − y = t(X(y) − X(x)), so |x − y| ≤ |t|A|x − y|, whence x = y.
 (b) φ_t is surjective: |(φ_t(x) − φ_t(y)) − (x − y)| = |t||X(x) − X(y)| ≤ |t|A|x − y|. So φ_t approximates the identity isomorphism of ℝ^P on all of ℝ^P with constant |t|A < 1 = ‖id⁻¹‖⁻¹, and φ_t is onto by Mathlib's ApproximatesLinearOn.surjective with f' = ContinuousLinearEquiv.refl. For P = 0 the space is a single point. Equivalently, for each y the map x ↦ y − tX(x) is a contraction of the complete space ℝ^P, and its fixed point x satisfies φ_t(x) = y.
 (c) Dφ_t(x) is injective for every x: (I + tDX(x))v = 0 gives |v| = |t||DX(x)v| ≤ |t|A|v|, so v = 0.
 (d) φ_t(K) ⊆ K: if x ∈ K and φ_t(x) ∉ K, then φ_t(φ_t(x)) = φ_t(x) because φ_t = id off K. By (a), φ_t(x) = x, which contradicts x ∈ K.
 3.4 (The open set W.) Let K' := K ∪ {0}, a compact set, and W := {y : dist(y, K') < 1}, an open set.
- K ⊆ W and B_1(0) ⊆ W.
- closure(W) ⊆ {y : dist(y, K') ≤ 1}, which is compact because ℝ^P is proper. Hence W ⊂⊂ ℝ^P (CompactlyContained W univ).
- μ is finite on compact sets: for compact Q, μ(Q) = ∫_{M∩Q} θ dH^j < ∞ by IMRep.locallyIntegrable_mult (via withDensity_apply and Measure.restrict_restrict). So μ(W) ≤ μ({dist(·, K') ≤ 1}) < ∞.
- μ(W) ≥ μ(B_1(0)) > 0, because 0 ∈ spt μ (step 2).
Put m := μ(W) ∈ (0, ∞).
 3.5 (First-variation bound.) G applies with U := ℝ^P, this W, R, X and the family φ. Its hypotheses hold: W is open; μ(W) ≠ ∞; X is C¹ with compact support; spt X = K ⊆ W; every φ_t is C¹ and equals the identity off spt X; and the derivative condition holds by 3.2. Hence for every ε > 0 there is δ_G > 0 with the following property. For every |t| < δ_G and every S ∈ 𝒟_j(ℝ^P) with S(ω) = ∫_M θ(x)ξ(x)(ω(φ_t x)∘Dφ_t(x)) dH^j(x) for all ω ∈ 𝒟^j(ℝ^P), we have M_W(S) ≤ ofReal(m + t·δV(X) + ε|t|).
 3.6 (Choice of t.) Suppose a := δV(X) ≠ 0. Take ε := |a|/2 and δ_G from 3.5. Put s := min{δ_G/2, 1/(2(A + 1)), m/|a|} > 0, and t := −s if a > 0, t := s if a < 0. Then:
- |t| = s < δ_G and |t|A < 1;
- ta = −s|a|;
- 0 < s|a| ≤ m.
 3.7 (The competitor.) F applies with U := ℝ^P (open), K, T := C, R and φ := φ_t. Its hypotheses hold: R represents C; K is compact; and φ_t is C¹, bijective, has injective derivative everywhere and equals the identity off K (3.2–3.3). It gives an integer multiplicity S ∈ 𝒟_j(ℝ^P) with ∂S = 0 (because ∂C = 0) and S(ω) = ∫_M θ ξ(ω(φ_t x)∘Dφ_t(x)) dH^j for all ω.
 3.8 (spt(S − C) ⊆ K.) Let y ∉ K and choose r > 0 with B_r(y) ∩ K = ∅ (K is closed). Let ω ∈ 𝒟^j(ℝ^P) with spt ω ⊆ B_r(y). Using C(ω) = R.action(ω), (S − C)(ω) = S(ω) − C(ω) = ∫_M θ(x)[ξ(x)(ω(φ_t x)∘Dφ_t(x)) − ξ(x)(ω(x))] dH^j(x). The two integrands coincide at every x:
- if x ∈ K, then φ_t(x) ∈ K by 3.3(d), so ω(φ_t x) = 0 = ω(x), since ω vanishes off B_r(y) and B_r(y) misses K;
- if x ∉ K, then φ_t = id on the open neighbourhood ℝ^P ∖ K of x, so φ_t(x) = x and Dφ_t(x) = I.
Hence S − C vanishes on B_r(y), an open set with compact closure in ℝ^P. So y lies in the zero region of S − C, and y ∉ spt(S − C). Thus spt(S − C) ⊆ K. Since spt(S − C) is closed (the complement of the open zero region) and K is compact, spt(S − C) is compact. Also spt(S − C) ⊆ K ⊆ ℝ^P ∩ W.
 3.9 (Minimality.) The competitor S is admissible in Simon 7.1.1:
- ∂S = ∂C, both being 0 (j ≥ 1);
- S is integer multiplicity;
- W is open with W ⊂⊂ ℝ^P;
- spt(S − C) is a compact subset of ℝ^P ∩ W.
So IsMinimizingIn C univ gives M_W(C) ≤ M_W(S). By (E1), M_W(C) = μ(W) = ofReal(m). By 3.5–3.6, M_W(S) ≤ ofReal(m + ta + (|a|/2)|t|) = ofReal(m − s|a|/2). Since 0 < m − s|a|/2 < m, we get ofReal(m − s|a|/2) < ofReal(m), a contradiction. Hence δV(X) = 0.
4. (Closed-ball mass bound.) For ρ ∈ (1/2, 1], B̄_{1/2}(0) ⊆ B_ρ(0). By (E1) and the hypothesis of the statement, μ(B̄_{1/2}(0)) ≤ μ(B_ρ(0)) = M_{B_ρ(0)}(C) ≤ (1 + δ₀)ω_jρ^j. The right side is continuous in ρ, with a finite value at ρ = 1/2 because ω_j < ∞. Letting ρ ↓ 1/2 gives μ(B̄_{1/2}(0)) ≤ (1 + δ₀)ω_j(1/2)^j.
5. (Allard at the origin.) Apply J, with the δ₀ and γ of step 1, to U := W := ℝ^P, R, H :≡ 0, κ := 0, ρ := 1/2 and z := 0. Its hypotheses hold:
- W is open and W ⊆ U;
- B̄_{1/2}(0) ⊆ W;
- H is measurable with |H| ≤ κ = 0;
- for every C¹ compactly supported X, δV(X) = 0 = −∫⟨X, H⟩ dμ (step 3);
- 0 ∈ spt μ (step 2);
- μ(B̄_{1/2}(0)) ≤ (1 + δ₀)ω_j(1/2)^j (step 4);
- κρ = 0 ≤ δ₀.
Put r := γ/2 > 0. J gives:
- linear isometries ι : ℝ^j → ℝ^P and ι' : ℝ^k → ℝ^P with ⟨ιv, ι'w⟩ = 0 for all v, w;
- u : ℝ^j → ℝ^k with u(0) = 0, u of class C¹ on B_r(0) ⊆ ℝ^j and ‖Du(v)‖ ≤ 1/4 there;
- spt μ ∩ B_r(0) = Φ(B_r(0)) ∩ B_r(0), where Φ(v) := 0 + ιv + ι'u(v).
6. (The graph over a cylinder.) Put σ := r/4 > 0 and Cyl := {0 + ιv + ι'w : |v| < σ, |w| < σ}.
 6.1 For v ∈ B_r(0), |u(v)| ≤ |v|/4. Indeed u is differentiable at every point of the open convex ball B_r(0), being C¹ there, with ‖Du‖ ≤ 1/4. So the mean value inequality gives |u(v) − u(0)| ≤ |v − 0|/4, and u(0) = 0.
 6.2 |ιv + ι'w| ≤ |ιv| + |ι'w| = |v| + |w|. Hence Cyl ⊆ B_{2σ}(0) ⊆ B_r(0).
 6.3 If ιv + ι'w = ιv' + ι'w', then v = v' and w = w'. Indeed ι(v − v') = ι'(w' − w), so |ι(v − v')|² = ⟨ι(v − v'), ι'(w' − w)⟩ = 0. Hence |v − v'| = |ι(v − v')| = 0. Then ι'w = ι'w', and ι' is injective.
 6.4 spt μ ∩ Cyl = Φ(B_σ(0)).
- (⊆) Let x = ιv + ι'w ∈ spt μ with |v|, |w| < σ. By 6.2, x ∈ B_r(0), so by step 5, x = Φ(v') for some v' ∈ B_r(0). By 6.3, v' = v and w = u(v). So x = Φ(v) with v ∈ B_σ(0).
- (⊇) Let |v| < σ. By 6.1, |u(v)| ≤ |v|/4 < σ, so Φ(v) ∈ Cyl ⊆ B_r(0). Also v ∈ B_r(0). So Φ(v) ∈ Φ(B_r(0)) ∩ B_r(0) = spt μ ∩ B_r(0) by step 5.
7. (Regularity.) Apply K with n := j ≥ 1, k, U := ℝ^P (open), T := C, R, ι, ι', u, z := 0 and s := h := σ. Its hypotheses hold:
- R represents C, and ∂C = 0;
- ⟨ιv, ι'w⟩ = 0 for all v, w, and σ > 0;
- u is C¹ on B_σ(0) ⊆ B_r(0), and u(0) = 0;
- Cyl ⊆ ℝ^P, and spt μ ∩ Cyl = Φ(B_σ(0)) (6.4);
- 0 ∈ spt C.
Hence 0 ∈ reg C (regularSet C). ∎
Formalization note. This proof was re-checked for this revision in the scratch file /tmp/dg8/lean/OriginRegular.lean, theorems dg8_stationary (step 3) and dg8_origin_regular (steps 1–7):
- Build: lake env lean against the frozen GMT.Ch07.Submission (project b4d606d, Mathlib 25730c7c, simongmt 2b36630).
- Hypotheses: exactly the frozen types of E, F, G, J, K, matched character for character; no other hypothesis and no sorry.
- #print axioms: propext, Classical.choice, Quot.sound.
- /tmp/dg8/lean/Linked.lean applies the same proof to the declarations Submission.dor_imrep_massOn_eq_measure_and_support, Submission.dimred_cdg_c1_diffeo_pushforward_im, Submission.dimred_cdg_pushforward_massOn_le_first_variation, Submission.dimred_cdg_allard_bounded_curvature_graph and Submission.dor_graph_supported_cycle_regular. These are declared there with their frozen types, and the application proves Submission.dimred_cdg_minimizing_origin_regular.
- Two inessential simplifications in the scratch build: 3.1 takes A := max(sup‖DX‖, 0), and 3.6 takes s := min{δ_G/2, 1/(2(A + 1))} without the cap m/|a|. The cap is not needed: ENNReal.ofReal_lt_ofReal_iff needs only 0 < m, so ofReal(m − s|a|/2) < ofReal(m) holds either way.
Lemmas used, by step:
- 3.1: Continuous.bounded_above_of_compact_support with hX.continuous_fderiv one_ne_zero and HasCompactSupport.fderiv; Convex.norm_image_sub_le_of_norm_fderiv_le.
- 3.2: (hasFDerivAt_id x).add ((hX.differentiable one_ne_zero x).hasFDerivAt.const_smul t); image_eq_zero_of_notMem_tsupport for φ_t = id off K.
- 3.3: ApproximatesLinearOn.surjective with ContinuousLinearEquiv.refl and ContinuousLinearMap.nnnorm_id; the Subsingleton case covers P = 0.
- 3.4: W := Metric.thickening 1 (insert 0 (tsupport X)), with closure_thickening_subset_cthickening and IsCompact.cthickening. Finiteness by IMRep.measure, withDensity_apply, Measure.restrict_restrict and R.locallyIntegrable_mult; positivity by Measure.mem_support_iff_forall.
- 3.8: the zero region is witnessed by ball y r with isCompact_closedBall and closure_ball_subset_closedBall; fderiv_of_notMem_tsupport gives DX = 0, hence Dφ_t = I, off K.
- 3.9: ENNReal.ofReal_lt_ofReal_iff.
- 4: ge_of_tendsto, Ioo_mem_nhdsGT and ENNReal.Tendsto.const_mul.
- 6: LinearIsometry.norm_map, real_inner_self_eq_norm_sq, sub_eq_sub_iff_add_eq_add, add_left_cancel and LinearIsometry.injective.

## Key steps

1. Write P = j + k and take δ := δ₀ from the sibling allard_graph with n = j and ε = 1/4; δ₀ and γ depend only on (P, j).
2. A minimizing C has an integer multiplicity representation R; the sibling imrep_mass_support gives M_W(C) = μ_R(W) for open W and spt C = spt μ_R, so 0 ∈ spt μ_R.
3. Flat Simon 7.1.2: for X ∈ C¹_c, φ_t = id + tX is a C¹ bijection with injective derivative for |t|·sup‖DX‖ < 1. The sibling c1_pushforward gives integer multiplicity competitors S_t with spt(S_t − C) ⊆ spt X. Minimality on W ⊃ spt X ∪ B_1(0), with M_W(C) = μ(W) > 0, combined with the sibling first_variation_bound, forces δV(X) = 0.
4. The open-ball mass hypothesis on (1/2, 1] gives μ(B̄_{1/2}(0)) ≤ (1 + δ₀)ω_j(1/2)^j in the limit.
5. The sibling allard_graph, applied with H ≡ 0, κ = 0, ρ = 1/2 and z = 0, makes spt μ near 0 the graph of a C¹ map u with u(0) = 0 and |Du| ≤ 1/4.
6. Orthogonality of ι and ι' and |u(v)| ≤ |v|/4 identify spt μ in the cylinder of radius γ/8 with the graph; the sibling graph_cycle_regular then gives 0 ∈ reg C.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; git -C local-references/123e8435b4a2469b/mathlib rev-parse HEAD`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `rg -l -e 'dimred_cdg_(eq_zero_of_lt_degree|im_cone_ball_mass|c1_diffeo_pushforward_im|pushforward_massOn_le_first_variation|harmonic_affine_approximation|allard_bounded_curvature_graph|minimizing_origin_regular)' -g '*.lean' local-references/123e8435b4a2469b lake-packages-25730c7c/simongmt/Poincare lake-packages-25730c7c/mathlib/Mathlib workspaces/gmt-ch07/GMT (exit 1: no match)`
- `grep -c -E '<same pattern>' dag.json (0); grep -l -E '<same pattern>' over the 780 workspaces/.swarm-worktrees/*/gmt-ch07/GMT/Ch07/Submission.lean (no match); git log --all --oneline -S dimred_cdg_ (only bbbfd3b8, which mentions dimred_cdg_weak_limit_cone, not a proposed name)`
- `python3 -I /tmp/dg8scripts/check_candidates.py dag.json (git show <candidate>:GMT/Ch07/Submission.lean for e183b985, d49dda91, 36b2d372, 2fd8f6ff, 8a6855aa, 4d9f2899, 01ae2c59, 428db72e: each declares theorem Submission.<lean_name> : <frozen type> := verbatim)`
- `python3 -I /tmp/dg8scripts/name_check.py <run> <decomposition> for v6, v7 and v8 (replay of Runtime._existing_lean_name_problem on dag.json) and replay of Runtime._topological`
- `python3 inspection of dag.json: statuses, candidate commits and frozen types of every node whose lean_statement equals a child type (including the fvmb_* children of first_variation_mass_bound-a1 and the codim1_ldr_ duplicates); this node's record (decomposing, attempt 8, children [])`
- `sed -n '1440,1560p;2355,2385p;6585,6660p' /runtime/flows/gmt-claude-b731e326000c/_recursive_lean/runtime.py; sed -n '60,260p' /runtime/flows/gmt-claude-b731e326000c/_recursive_lean/store.py (_decompose, _accepted_checkpoint, _existing_lean_name_problem, _reference_use_problem, Store.refresh, Store.update)`
- `cat cluster-state/logs/gmt-ch07/e39b4162870940da8110ef2d3c8bdbfa.log; ls nodes/root-minimizing-implies-stationary-a1-first-variation-mass-bound-a1/ (accepted-candidate.json at 07:57Z)`
- `python3 diff of nodes/root-dimension-reduction-results-a1-density-gap-a1/decomposition-v6.json and decomposition-v7.json; cat decomposition-audit-v1..v6.json`
- `sed -n '620,635p;25,62p' book/chapter-07.txt (Simon 7.1.2 and the use of Allard 5.2 in 7.4.3)`
- `PATH=<toolchain lean-4.35.0-rc3>/bin:$PATH lake env lean /tmp/dg8/lean/{Types,Linked,Assembly,HighDegreeZero,ConeBallMass,OriginRegular,HarmonicConclusion}.lean (each with #print axioms); python3 -I /tmp/dg8scripts/check_frozen.py dag.json`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-density-gap-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-density-gap-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-density-gap-a1/decomposition-v6.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-density-gap-a1/decomposition-v7.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-density-gap-a1/decomposition-audit-v6.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-density-gap-a1/decomposition-review-receipt-v5.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-first-variation-mass-bound-a1/accepted-candidate.json`
- `/runtime/flows/gmt-claude-b731e326000c/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b731e326000c/_recursive_lean/store.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/cluster-state/logs/gmt-ch07/e39b4162870940da8110ef2d3c8bdbfa.log`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/dg8/lean/Types.lean`
- `/tmp/dg8/lean/Linked.lean`
- `/tmp/dg8/lean/Assembly.lean`
- `/tmp/dg8/lean/HighDegreeZero.lean`
- `/tmp/dg8/lean/ConeBallMass.lean`
- `/tmp/dg8/lean/OriginRegular.lean`
- `/tmp/dg8/lean/HarmonicConclusion.lean`
- `/tmp/dg8scripts/check_frozen.py`
- `/tmp/dg8scripts/check_candidates.py`
- `/tmp/dg8scripts/name_check.py`

Pins match: the manifest records project b4d606d and Mathlib 25730c7c, which equal the workspace HEAD and the snapshot and package Mathlib; simongmt is at 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.
- Reuse: cone_current_imrep_measure_smul_image (e183b985), dor_imrep_massOn_eq_measure_and_support (d49dda91), imrep_approxTangent_starProjection_aesm (36b2d372), covectorEuclideanNorm_gram_bounds (2fd8f6ff) and dor_graph_supported_cycle_regular (8a6855aa) are accepted. Each has a character-identical frozen type and is declared verbatim in its candidate commit. The resolved dependencies dimred_im_mass_measure (01ae2c59) and dimred_regular_point_density (428db72e) are also accepted and declared verbatim.
- pushforward_action_massOn_le_first_variation (4d9f2899) is accepted with the identical type, but the runtime refused it for this parent. The child therefore uses the fresh name dimred_cdg_pushforward_massOn_le_first_variation, and its six fvmb_* helpers are cited only as a formalization aid.
- Names: the seven fresh dimred_cdg_ names occur nowhere in the snapshot, SimonGMT, Mathlib, the workspace GMT sources, dag.json, the 780 swarm-worktree Submission files or git history. Replaying the runtime name check and the topological sort on v8 reports no problem.
- Lean: all fifteen types elaborate. Linked.lean proves Submission.dimred_cone_density_gap from the actual child declarations, with sorry only in the eleven leaf stubs. The conditional checks (assembly, high_degree_zero, cone_ball_mass, origin_regularity and harmonic_affine's Conclusion) depend only on propext, Classical.choice and Quot.sound. They do not discharge the seven new children.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
