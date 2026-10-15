<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1 -->

## Theorem `Submission.dimred_mbl_closure_and_boundary_rectifiability`

(CL) For all P, d ∈ ℕ, every open U ⊆ ℝ^P and currents T_j, T ∈ 𝒟_d(U): if every T_j is integer multiplicity, sup_j (M_W(T_j) + M_W(∂T_j)) < ∞ for every open W with closure(W) compact and contained in U (∂-mass read as 0 when d = 0, contract boundaryMassOn), and T_j ⇀ T in U, then T is integer multiplicity. (BR) For all P, d ∈ ℕ, every open U ⊆ ℝ^P and every integer multiplicity R ∈ 𝒟_{d+1}(U) with M_W(∂R) < ∞ for every such W, the boundary ∂R is integer multiplicity.

Node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1022

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/810, https://github.com/ZhengyangZhang06/gmt-formalize/issues/667, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5014, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5023, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5033

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5723, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5733, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5749, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5758, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5771, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5785, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5794, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5802, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5819, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5833, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5888, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5902

## Lean problem

Declaration: `Submission.dimred_mbl_closure_and_boundary_rectifiability`

```lean
(∀ (P d : ℕ) (U : Set (Euclid P)) (Ts : ℕ → GeometricCurrentOn U d) (T : GeometricCurrentOn U d), IsOpen U → (∀ j, IsIntegerMultiplicity (Ts j)) → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → ⨆ j, ((Ts j).massOn W + boundaryMassOn (Ts j) W) < ∞) → WeaklyConvergesOn Ts T → IsIntegerMultiplicity T) ∧ (∀ (P d : ℕ) (U : Set (Euclid P)) (R : GeometricCurrentOn U (d + 1)), IsOpen U → IsIntegerMultiplicity R → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → R.boundary.massOn W < ∞) → IsIntegerMultiplicity R.boundary)
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

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 6, 6.1–6.4, 8.2–8.3 (8.1 replaced by White's tangent planes), Ch. 3, 1.6 ⇐. Errata: 8.2 needs the lower density, not Θ^{*n}<η, and filling support control (DT); Ch. 3, 1.6 needs ε:=2^{−1}16^{−n}.
Notation: IM integer multiplicity; lfm locally finite mass; ATS approximate tangent space; lsc lower semicontinuity of mass; ONB orthonormal basis; Lip Lipschitz; Hᵏ:=μHE[k]; Lᵏ Lebesgue; ω_k:=Lᵏ(B_1); B_r:=B_r(0); Θ^k_*(μ,x):=liminf_{r↓0}μ(B_r(x))/(ω_kr^k); M(X):=X.mass; |·| Euclidean (dual) norm; X+Y:=X−(0−Y); W⊂⊂U: W open, W̄⊆U compact.
Siblings: mass_and_support (MR: M_G(X)=R.measure(G) for IM X, IMRep R, G open), foundations (REP: X of lfm in open U has (μ_X,ξ_X), μ_X(G)=M_G(X), |ξ_X|≤1, X(ω)=∫ξ_X(ω)dμ_X, μ_X≪Hᵏ if ∂X has lfm) and (IMC)(a)–(d) ((d): (R.measure,R.orient) is admissible in SL), slicing (SL: slices Z_t:=∂(X⌞{f<t})−(∂X)⌞{f<t}), deformation_theorem (DT), vanish_off_support (VO).
(Z) Coordinatewise, a finite signed Radon measure on an open set annihilating C_c^∞ is 0 (approximate indicators of compact sets by smooth functions; dominated convergence, inner regularity).
(R) For X of lfm in U: |ξ_X|=1 μ_X-a.e. (μ_X(G)=M_G(X)≤∫_G|ξ_X|dμ_X); X⌞B(ω):=∫_Bξ_X(ω)dμ_X (B Borel) is a current (linear, |X⌞B(ω)|≤|ω|_∞μ_X(tsupport ω)). If X equals IM X' (IMRep (M',θ',ξ')) on forms with tsupport in open B⊆U, then μ_X⌞B=θ'Hᵏ⌞(M'∩B) (locally finite, they agree on open G⊆B: μ_X(G)=M_G(X)=M_G(X')=θ'Hᵏ(M'∩G), REP, MR) and ξ_X=ξ' μ_X-a.e. on B (∫⟨ω,ξ_X−ξ'⟩dμ_X=0 for ω supported in B; (Z)). Taking X'=X: for IM X, X⌞B is the IM restriction.
(MM) For L-Lip f and open G, SL gives M_G(Z_t)≤L liminf_{h↓0}h⁻¹μ_X(G∩{t−h<f<t}), so for F(t):=μ_X(G∩{a<f<t}) (nondecreasing; F(b)<∞), M_G(Z_t)≤LF'(t) at t∈(a,b) where F'(t) exists (a.e., Lebesgue); F' is measurable and integrable, ∫_a^bF'≤F(b). If all F_j(b)≤Λ, Fatou gives ∫_a^b liminf_jF_j'≤Λ: for a.e. t all F_j'(t) exist and liminf_jM_G(Z_{j,t})≤L liminf_jF_j'(t)<∞.
T1. For open U and Borel μ_j with sup_jμ_j(K)<∞ (K⊆U compact), a subseq. converges to a Borel μ finite on compacts (∫f dμ_j→∫f dμ, f∈C_c(U)), with limsup_jμ_j(C)≤μ(C), μ(G)≤liminf_jμ_j(G) (C⊆U compact, G⊆U open): weak-* compactness (simon_theorem_4_16_compact_metrizable) of μ_j⌞K_k on compact metrizable K_k↑U (K_k⊆int K_{k+1}) and a diagonal argument give a positive linear Λ(f):=lim∫f dμ_j, =∫f dμ (Riesz–Markov–Kakutani); Urysohn approximation of 1_C from above, 1_G from below.
T2. X_j⇀X in 𝒟_k(U), all of lfm, μ_{X_j}→μ (T1), f continuous, μ({f=t})=0 ⇒ X_j⌞{f<t}⇀X⌞{f<t}. For spt ω⊆C compact ⊆U, ε>0, take χ_ε∈C_c^∞(U;[0,1]), =1 on C∩{f≤t−ε}, =0 on C∩{f≥t}; as |1_{f<t}−χ_ε|≤1 vanishes on C off {t−ε<f<t}, |X_j⌞{f<t}(ω)−X_j(χ_εω)|≤|ω|_∞μ_{X_j}(E_ε), E_ε:=C∩{t−ε≤f≤t}, limsup ≤|ω|_∞μ(E_ε) (T1) →|ω|_∞μ(C∩{f=t})=0 (ε↓0); likewise |X⌞{f<t}(ω)−X(χ_εω)|≤|ω|_∞μ_X(C∩{t−ε<f<t})→0; and X_j(χ_εω)→X(χ_εω).
T3. X∈𝒟_k(ℝ^P), k≥1, M(X)<∞, ∂X=0, spt X⊆B̄_r(x₀) ⇒ |X(ω)|≤rM(X)|dω|_∞. The homotopy operator (Kγ)(x):=∫_0^1t^{j−1}ι_{x−x₀}γ(x₀+t(x−x₀))dt of h_t(x):=x₀+t(x−x₀) on j-forms, j≥1, has dKγ+Kdγ=γ−h₀^#γ=γ (differentiation under ∫, Cartan dι_v+ι_vd=L_v, v(x):=x−x₀; h₀ constant), |Kγ(x)|≤|x−x₀||γ|_∞/j (|ι_vγ|≤|v||γ|). For ζ∈C_c^∞ =1 near spt X: X(ω)=X(ζω)=X(ζdKω)+X(ζKdω), X(ζdKω)=∂X(ζKω)−X(dζ∧Kω)=0 (VO), so |X(ω)|≤∫|Kdω|dμ_X≤r|dω|_∞M(X) (μ_X carried by spt X: REP, VO).
T4. If X∈𝒟_k(U) has lfm and each x∈U lies in an open ball B⊆U on which (tsupport ω⊆B) X equals an IM current, X is IM: take countably many such B_i covering U, X equal to an IM X_i with IMRep (M_i,θ_i,ξ_i) on B_i; by (R), μ_X⌞B_i=θ_iHᵏ⌞(M_i∩B_i), ξ_X=ξ_i μ_X-a.e. on B_i; A_i:=B_i∖⋃_{l<i}B_l, M:=⋃_i(M_i∩A_i), (θ,ξ):=(θ_i,ξ_i) on M_i∩A_i give X(ω)=Σ_i∫_{A_i}ξ_X(ω)dμ_X=∫_Mθ⟨ω,ξ⟩dHᵏ and an IMRep (M countably rectifiable, as a countable union; θ≥1 integer; ∫_{M∩K}θdHᵏ=μ_X(K)<∞, K⊆U compact; by IMC(a), a.e. on M∩A_i, M, M_i∩A_i, M_i share the ATS, oriented by ξ_i).
T5. For a∈ℝ^P, λ>0, η(y):=λ⁻¹(y−a), η_#X(ω):=X(η^#ω) (affinePushforward), (η^#ω)(y)=λ^{−k}ω(η(y)): ∂η_#=η_#∂, M_{η(W)}(η_#X)=λ^{−k}M_W(X), spt η_#X=η(spt X); η_# maps IM τ(M,θ,ξ) to IM τ(η(M),θ∘η⁻¹,ξ∘η⁻¹) (Hᵏ(η(A))=λ^{−k}Hᵏ(A); η_{η(x),r}(η(M))=η_{x,λr}(M), so ATS correspond); η_#(X⌞{f∘η<t})=(η_#X)⌞{f<t}, as (λ^{−k}η_*μ_X,ξ_X∘η⁻¹) represents η_#X (change of variables) and restrictions do not depend on the representation (V4(o)).
Part II. CL(d), BR(d): the conjuncts in degree d, d+1 (of R); induction: CL(0) (III), CL(d)⇒BR(d) (IV), CL(d)∧BR(d)⇒CL(d+1) (V).
Part III. CL(0) (∂-term 0). As H⁰ is counting measure and points have ATS {0}, an IMRep of T_j is a set M_j, θ_j≥1, orientations ±1, M_j∩K finite (K⊆U compact; local integrability): T_j(a)=Σ_{x∈M_j}m_j(x)a(x), m_j∈ℤ∖{0}. T has lfm (lsc). For B:=B_{2r}(x₀), B̄⊆U, (MR) gives Σ_{M_j∩B}|m_j|≤c:=sup_jM_B(T_j)<∞, so on B, T_j=Σ_{i≤N_j}ε_{j,i}δ_{x_{j,i}}, N_j≤c, ε_{j,i}=±1 (with multiplicity). For a subseq. N_j=N, ε_{j,i}=ε_i, x_{j,i}→y_i∈B̄: T(a)=lim_jΣ_iε_ia(x_{j,i})=Σ_iε_ia(y_i) for a∈C_c^∞(B_r(x₀)), so there T equals the IM Σ_ym(y)δ_y, m(y):=Σ_{y_i=y}ε_i≠0 (finite carrier in U). By T4, T is IM.
Part IV. CL(d)⇒BR(d). If d+1>P, R=0 (no nonzero (d+1)-forms) and ∂R=0 is IM via the empty IMRep (carrier ∅, multiplicity 0, orientation 0; ∅ is countably rectifiable by countablyRectifiable_of_measure_zero; the other fields hold vacuously as μHE⌞∅=0; the integral over ∅ is 0). Let d+1≤P.
1. Fix B̄_{2r₀}(x₀)⊆U, f:=|·−x₀|, B'_ρ:=B_ρ(x₀). By SL (IMRep of R, IMC(d); REP for ∂R) and MM, for a.e. r<r₀, Z_r:=∂(R⌞B'_r)−(∂R)⌞B'_r has finite mass (M(Z_r)≤M_G(Z_r), G:=B'_{r₀}, as Z_r(ω)=Z_r(χω) for χ∈C_c^∞(G;[0,1]) =1 near ∂B'_r, SL); fix such r. R':=R⌞B'_r is IM (IMC(b)), carrier in B'_r, spt R'⊆B̄'_r, M(R')<∞ (MR), ∂R'=(∂R)⌞B'_r+Z_r of finite mass. R̂'(ω):=R'(ζω), ζ∈C_c^∞(U) =1 near B̄'_r (ζ-independent by VO), is IM in ℝ^P with the same IMRep, M(R̂')=M(R'), ∂R̂'=(∂R')^ (VO).
2. DT with m:=d, K:=B̄'_r, Λ:=M(R̂'), ρ_k:=2^{−k}: R̂'−Q_k−S_k=∂R_k, Q_k, ∂Q_k IM, M(R_k)≤cρ_kM(R̂')→0, M(S_k)≤cρ_kM(∂R̂')→0, M(∂Q_k)≤cM(∂R̂'), spt Q_k⊆{dist(·,K)<3√Pρ_k}. As |Q_k(ω)−R̂'(ω)|≤M(S_k)|ω|_∞+M(R_k)|dω|_∞→0, Q_k⇀R̂', ∂Q_k⇀∂R̂', and CL(d) in ℝ^P (∂Q_k IM of bounded mass, ∂∂Q_k=0 or d=0) makes ∂R̂' IM.
3. For tsupport η⊆B'_r: ∂R̂'(η)=(∂R)⌞B'_r(η)+Z_r(η)=∂R(η) (η=0 off B'_r; Z_r(η)=0 by SL as tsupport η∩{f=r}=∅). ∂R̂' restricted to forms in U is IM (its IMRep measure vanishes off spt ∂R̂'⊆B̄'_r⊆U by MR, VO; intersect the carrier with B̄'_r, IMC(b)). As ∂R has lfm, T4 gives ∂R IM. ∎
Part V. CL(d)∧BR(d)⇒CL(n), n=d+1; Λ_W:=sup_j(M_W(T_j)+M_W(∂T_j)). If n>P, T=0 is IM (empty IMRep); let n≤P.
V1. ∂T_j is IM (BR(d)); T, ∂T have lfm (lsc), so REP applies.
V2. Take x₀, r₀, f, B'_ρ as in IV.1 and a subseq. with μ_{T_j}→μ on U (T1). By SL, MM (IMReps, IMC(d); Λ_{B'_{r₀}}; slice masses as in IV.1), for a.e. r<r₀ liminf_jM(Z_{j,r})<∞, Z_{j,r}:=∂(T_j⌞B'_r)−(∂T_j)⌞B'_r; and μ(∂B'_r)=0 off a countable set. Fix such r, a subseq. with sup_jM(Z_{j,r})<∞. T'_j:=T_j⌞B'_r are IM (IMC(b)), spt T'_j⊆K:=B̄'_r, sup_j(M(T'_j)+M(∂T'_j))<∞, T'_j⇀T⌞B'_r (T2); their extensions T̂'_j to ℝ^P (IV.1) are IM, ∂T̂'_j IM (BR(d) in ℝ^P; M(∂T̂'_j)<∞), and T̂'_j⇀(T⌞B'_r)^, IM by (CL*); restricted to U it is IM and equals T on forms supported in B'_r: T is IM (T4). It remains to prove
(CL*) T_j∈𝒟_n(ℝ^P), T_j, ∂T_j IM, spt T_j⊆K compact, sup_j(M(T_j)+M(∂T_j))<∞, T_j⇀T ⇒ T IM.
V3. The ∂T_j are IM (n−1)-cycles in K of bounded mass, ⇀∂T, so ∂T is IM (CL(d)), spt ∂T⊆K, M(∂T)<∞, ∂∂T=0 (n≥2). Need IM Y, compact support, ∂Y=∂T.
(Iso) d≥1, Z∈𝒟_d(ℝ^P) an IM cycle of compact support ⇒ ∃ IM Y, ∂Y=Z, M(Y)≤c_IM(Z)^{(d+1)/d}, spt Y⊆{dist(·,spt Z)<3√P(2cM(Z))^{1/d}}, c=c(P,d−1) from DT, c_I:=c(2c)^{1/d}: Y:=0 (IM, empty IMRep) if Z=0; else DT with m:=d−1, ρ:=(2cM(Z))^{1/d}, K:=spt Z, Λ:=M(Z): Z−Q−S=∂Y, M(S)≤cρM(∂Z)=0, so S=0, M(Q)≤cM(Z)=ρ^d/2<ρ^d, so Q=0 (dichotomy Q=0 ∨ M(Q)≥ρ^d); hence Z=∂Y, Y IM, M(Y)≤cρM(Z)=c_IM(Z)^{(d+1)/d}, support by DT.
n≥2: Iso with Z:=∂T. n=1: ∂T, an IM 0-current of compact support, is Σ_{i≤N}m_iδ_{x_i} (III); for ζ∈C_c^∞ =1 near K, ∂T(ζ)=lim_jT_j(dζ)=0 (VO), so Σm_i=0; Y:=Σ_im_i[[x₀,x_i]] (segments from fixed x₀∉{x_i}, IM: carrier the open segment, multiplicity 1, unit tangent orientation, ATS its line; IMC(c)), ∂Y=Σm_i(δ_{x_i}−δ_{x₀})=∂T.
Γ:=T−Y is a cycle of finite mass, compact support (⊆K∪spt Y); it suffices that Γ is IM (T=Γ−(0−Y), IMC(c)).
V4. For X∈𝒟_n(ℝ^P), X, ∂X of lfm (REP; n=1: no ∂∂X terms), Lip f, t∈ℝ: ⟨X,f,t⟩:=∂(X⌞{f<t})−(∂X)⌞{f<t} (Z_t of SL; ∂(X⌞{f<t}) for cycles). (ISP): ∀ Lip f, ⟨X,f,t⟩ is IM for a.e. t.
(o) (X−X')⌞B=X⌞B−X'⌞B (B Borel): ξ_{X−X'}μ_{X−X'} and ξ_Xμ_X−ξ_{X'}μ_{X'} integrate C_c^∞ covector fields alike, so agree on bounded Borel sets (Z). So ⟨X−X',f,t⟩=⟨X,f,t⟩−⟨X',f,t⟩.
(i) X, ∂X IM of lfm ⇒ (ISP): by SL, MM, for a.e. t ⟨X,f,t⟩ has lfm; X⌞{f<t} is IM (IMC(b)), its boundary (∂X)⌞{f<t}+⟨X,f,t⟩ has lfm, so is IM (BR(d)); so is ⟨X,f,t⟩ (IMC(b),(c)).
(ii) X_i with (ISP), sup_i(μ_{X_i}+μ_{∂X_i})(B_k)<∞ ∀k, X_i⇀X ⇒ X has (ISP). X, ∂X have lfm (lsc). Fix f (L-Lip), k, U':=B_{k+1}, a subseq. with μ_{X_i}→μ, μ_{∂X_i}→μ' (T1); S_i:=⟨X_i,f,t⟩, S'_i:=⟨∂X_i,f,t⟩ (n≥2), S:=⟨X,f,t⟩. MM (summed majorants of S_i, S'_i; each (−m,m), all m) gives for a.e. t: μ({f=t})=μ'({f=t})=0, liminf_i(M_{U'}(S_i)+M_{U'}(S'_i))<∞, all S_i IM. Fix such t and a subseq. bounding these masses. By T2 (X_i, ∂X_i) S_i⇀S, and ∂S_i=−∂((∂X_i)⌞{f<t})=−S'_i (none if n=1). CL(d) in U' for the domain restrictions to U' of the S_i (IM: carriers ∩U', IMC(b)) makes that of S IM; cut to B_k (IMC(b)) and extended to ℝ^P as in IV.1 (A↦(ω↦A(ζω)), ζ∈C_c^∞(U') =1 near B̄_k), it is IM and equals S on forms supported in B_k. S has lfm (lsc); as this holds ∀k for a.e. t, S is IM (T4).
(iii) (ISP) is invariant under T5 (slices of η_#X by f are η_# of slices of X by f∘η).
So T_j ((i)), T ((ii)), Y ((i): IM, compact support, ∂Y=∂T IM) and Γ=T−Y ((o), IMC(c)) have (ISP): ∂(Γ⌞{f<t}) is IM ∀ Lip f, a.e. t.
V5. ∃η₀=η₀(n,P)>0: every n-cycle C in ℝ^P of lfm with (ISP) has Θⁿ_*(μ,·)≥η₀ μ-a.e., μ:=μ_C. Θⁿ_*(μ,·) is Borel (x↦μ(B_r(x)) lower semicontinuous, r↦μ(B_r(x)) left continuous: rational r suffice). For 0<η<1/4 and A_η:={Θⁿ_*(μ,·)<η}, by inner regularity it suffices: μ(K')=0 for compact K'⊆A_η, η small. Fix K', ε₀∈(0,1), W:={dist(·,K')<ε₀} (μ(W)<∞).
(a) Let x₁∈K', 0<δ<ε₀/(2+3√P), F(ρ):=μ(B_ρ(x₁)); some s∈(0,δ) has F(s)<ηω_nsⁿ (x₁∈A_η). F^{1/n} is nondecreasing, so ∫_0^s(F^{1/n})'≤F^{1/n}(s)<(ηω_n)^{1/n}s and {ρ<s: (F^{1/n})'(ρ)≤2(ηω_n)^{1/n}} has positive measure; pick ρ in it with F'(ρ) existing, Z:=∂(C⌞B_ρ(x₁)) IM ((ISP), f=|·−x₁|), μ(∂B_ρ(x₁))=0, M(Z)≤F'(ρ) (MM; Z is the slice as ∂C=0). So Z is an IM (n−1)-cycle in ∂B_ρ(x₁), M(Z)≤F'(ρ)=nF(ρ)^{(n−1)/n}(F^{1/n})'(ρ)≤2n(ηω_n)^{1/n}F(ρ)^{(n−1)/n}≤2nηω_ns^{n−1}. If n≥2, Iso gives IM S, ∂S=Z, M(S)≤c_I(2n)^{n/(n−1)}(ηω_n)^{1/(n−1)}F(ρ)=:κ(η)F(ρ), spt S⊆B̄_{ρ+3√P(4cnηω_n)^{1/(n−1)}s}(x₁)⊆B̄_{δ₁}(x₁), δ₁:=(1+3√P)δ, if 4cnηω_n≤1. If n=1, M(Z)≤4η<1, so Z=0 (MR: nonzero IM 0-currents have mass ≥1); S:=0, κ:=0.
(b) These B̄_ρ(x₁) (x₁∈K', ρ arbitrarily small) finely cover K'; Besicovitch–Vitali for finite μ⌞W yields disjoint B_i=B̄_{ρ_i}(x_i)⊆W from (a) covering μ-a.a. of K'. With fillings S_i, X_i:=S_i−C⌞B_i is an n-cycle (∂S_i=∂(C⌞B_i), μ(∂B_i)=0) in B̄_{δ₁}(x_i), so |X_i(ω)|≤δ₁(1+κ)μ(B_i)|dω|_∞ (T3). As Σ_iμ(B_i)≤μ(W), Σ_iS_i, Σ_iC⌞B_i converge absolutely in mass and |Σ_iX_i(ω)|≤δ₁(1+κ)μ(W)|dω|_∞→0: C⌞(ℝ^P∖⋃B_i)+Σ_iS_i=C+Σ_iX_i⇀C as δ↓0 (countable additivity).
(c) By lsc, μ(W)=M_W(C)≤liminf_{δ↓0}(μ(W∖⋃B_i)+Σ_iM(S_i))≤μ(W∖K')+κμ(W) (μ(K'∖⋃B_i)=0). Take η₀<1/4 with κ(η₀)≤1/2 and (n≥2) 4cnη₀ω_n≤1: for η=η₀, μ(W)≤2μ(W∖K'), and ε₀↓0 gives μ(K')=0. ∎
V6. M₀:={x∈spt Γ: Θⁿ_*(μ_Γ,x)≥η₀} is Borel, μ_Γ(ℝ^P∖M₀)=0 (V5 for Γ by V3, V4; VO), η₀Hⁿ(M₀)≤μ_Γ(ℝ^P)<∞ (closed-ball upper density ≥η₀ on M₀; simon_theorem_3_3). μ_Γ≪Hⁿ⌞M₀ (REP, ∂Γ=0), so μ_Γ=θHⁿ⌞M₀, θ Borel integrable (Radon–Nikodym); M':=M₀∩{θ>0}; τ:=θξ_Γ: Γ(ω)=∫_{M'}⟨ω,τ⟩dHⁿ, |τ|=θ Hⁿ-a.e. on M' ((R)).
V7. For Hⁿ-a.e. a∈M': (i) Θ^{*n}(Hⁿ⌞M',a)≤1 (simon_theorem_3_26_i); (ii) Hⁿ(M'∩B̄_r(a))⁻¹∫_{M'∩B̄_r(a)}|τ−τ(a)|dHⁿ→0 (Besicovitch differentiation); (iii) Θⁿ_*(μ_Γ,a)≥η₀, 0<θ(a)=|τ(a)|<∞. Fix such a, τ₀:=τ(a), θ₀:=θ(a), c₀:=η₀ω_n/(4θ₀). As |θ−θ₀|≤|τ−τ₀|, μ_Γ(B_r(a))≤θ₀h(r)+∫_{M'∩B̄_r(a)}|τ−τ₀|=θ₀h(r)+o(rⁿ) ((i),(ii)), h(r):=Hⁿ(M'∩B_r(a)), and for small r, μ_Γ(B_r(a))≥(η₀/2)ω_nrⁿ (iii), so h(r)≥c₀rⁿ.
V8. For λ_i↓0 let η_i:=η_{a,λ_i}, Γ_i:=η_{i#}Γ, μ_i:=Hⁿ⌞η_i(M'). By T5, Γ_i(ω)=∫_{η_i(M')}⟨ω(y),τ(a+λ_iy)⟩dHⁿ(y), c₀Rⁿ≤μ_i(B_R)≤2ω_nRⁿ (R>0, i large), and for spt ω⊆B_R, |Γ_i(ω)−∫⟨ω,τ₀⟩dμ_i|≤|ω|_∞λ_i^{−n}∫_{M'∩B_{λ_iR}(a)}|τ−τ₀|dHⁿ→0 (V7). By T1, for a subseq. μ_i→ν, Γ_i⇀C, C(ω):=∫⟨ω,τ₀⟩dν; ν(B_R)≤liminf μ_i(B_R)≤ω_nRⁿΘ^{*n}(Hⁿ⌞M',a)≤ω_nRⁿ; ν(B̄_R)≥limsup μ_i(B̄_R)≥c₀Rⁿ>0, so 0∈spt ν; ∂C=0 (∂Γ_i=0). As M_G(ζ₀ν')=|ζ₀|ν'(G) for constant n-vectors ζ₀ (≥: test φβ₀, |β₀|=1, ⟨β₀,ζ₀⟩=|ζ₀|, φ∈C_c^∞(G;[0,1])↑1_G), μ_C=θ₀ν and |μ_{Γ_i}(G)−θ₀μ_i(G)|≤M_G(Γ_i−τ₀μ_i)→0 (G bounded open): μ_{Γ_i}→θ₀ν, sup_iμ_{Γ_i}(B_R)<∞. By V4(iii),(ii), C has (ISP).
V9. For (n−1)-covectors α let ⟨v_α,w⟩:=⟨w^♭∧α,τ₀⟩ (w^♭:=⟨w,·⟩). For φ∈C_c^∞(ℝ^P), 0=∂C(φα)=C(dφ∧α)=∫Dφ·v_αdν, so d/ds∫φ(y+sv_α)dν(y)=0: ν is V₀-invariant, V₀:=span{v_α}. τ₀∈Λ_n(V₀): for an ONB (e'_i) with V₀=span(e'_1..e'_r) and increasing I∋i>r, ⟨e'^I,τ₀⟩=±⟨e'^i∧e'^{I∖i},τ₀⟩=±⟨v_{e'^{I∖i}},e'_i⟩=0; as τ₀≠0, r≥n. For y₀∈spt ν, m₀:=ν(B_1(y₀))>0 and large R, balls B_1(y₀+v), v∈2ℤ^r (coordinates in e'_1..e'_r), |v|≤R/2, are disjoint, in B_R, ≥c_rR^r many, of ν-measure m₀: c_rm₀R^r≤ν(B_R)≤ω_nRⁿ, so r≤n. So dim V₀=n, Λ_n(V₀) is a line and τ₀=θ₀v_1∧⋯∧v_n, (v_i) an oriented ONB of V₀ (|τ₀|=θ₀).
V10. ℝ^P=V₀⊕V₀^⊥. For bounded Borel B⊆V₀^⊥, A↦ν(A+B) (A⊆V₀ Borel) is translation invariant, locally finite on V₀≅ℝⁿ, so =σ(B)Lⁿ_{V₀} (Haar uniqueness); σ is locally finite on V₀^⊥, ν=Lⁿ_{V₀}⊗σ (products, π-λ). V5 for C (μ_C=θ₀ν): Θⁿ_*(ν,·)≥η₀/θ₀ ν-a.e.; for y=v+w, ν(B_r(y))≤ω_nrⁿσ(B_r(w)), so σ({w})=lim_rσ(B_r(w))≥η₀/θ₀ σ-a.e. (exceptional w: σ-null, as ν(B_1∩V₀+G)=ω_nσ(G)). So σ=Σ_iα_iδ_{w_i}, α_i≥η₀/θ₀, {w_i} locally finite; ν(B_R)=Σ_iα_iω_n(R²−|w_i|²)_+^{n/2}≤ω_nRⁿ gives (finite subfamilies, R→∞) Σ_iα_i≤1: finitely many w_1..w_N, some w_i=0 (0∈spt ν=⋃_i(V₀+w_i)).
V11. Fix i₀, α:=α_{i₀}, w:=w_{i₀}, blow-up index k (V8), orthonormal coordinates with V₀=ℝⁿ×{0}, τ₀=θ₀e_1∧⋯∧e_n, projection p:ℝ^P→ℝⁿ, δ':=min_{j≠i₀}|w_j−w|/3 (1 if N=1), g:=dist(·,V₀+w) (1-Lip), R>0, Ω:=p⁻¹(B_{3R}).
(a) A'':=Ω̄∩{δ'≤g≤2δ'} is compact, ν(A'')=0 (no V₀+w_j meets it), so μ_{Γ_k}(A'')→0 (V8, T1). SL for Γ_k (∂Γ_k=0), f=g, G=Ω, and MM for F_k(t):=μ_{Γ_k}(Ω∩{δ'<g<t}), ∫F_k'≤μ_{Γ_k}(A'')→0, give (Fatou) liminf_kF_k'(t)=0 for a.e. t∈(δ',2δ'); fix such t and a subseq. with M_Ω(∂Z_k)→0, Z_k:=Γ_k⌞{g<t}. By T2 (ν({g=t})=0) Z_k⇀C⌞{g<t}=τ₀αHⁿ⌞(V₀+w). (Also N=1, n=P: g≡0, A''=∅.)
(b) For b∈C_c^∞(B_{2R}), Y_k(b dy):=∫b∘p⟨dy¹∧⋯∧dyⁿ,ξ_{Z_k}⟩dμ_{Z_k} converges absolutely (μ_{Z_k}(p⁻¹(spt b))≤μ_{Γ_k}({g≤t}∩Ω)<∞); Y_k∈𝒟_n(B_{2R}), M(Y_k)≤μ_{Γ_k}({g≤t}∩Ω) (bounded in k), ∂Y_k(γ)=Z_k(χp^#dγ)=∂Z_k(χp^#γ) (χ∈C_c^∞(Ω) =1 near {g≤t}∩p⁻¹(spt γ); VO), so m_k:=M_{B_{2R}}(∂Y_k)≤M_Ω(∂Z_k)→0 (|p^#γ|=|γ∘p|). Y_k(b dy)→θ₀α∫b dy (test Z_k⇀τ₀αHⁿ⌞(V₀+w) on χ(b∘p)dy, fixed χ∈C_c^∞(Ω) =1 on compact {g≤t}∩p⁻¹(B̄_{2R})).
(c) By REP (Y_k, ∂Y_k of lfm in B_{2R}), μ_{Y_k}≪Lⁿ: Y_k(b dy)=∫bu_kdLⁿ, u_k∈L¹(B_{2R}) (Radon–Nikodym). As b↦Y_k(b dy) is the push-forward by p of ⟨dy,τ(a+λ_k·)⟩Hⁿ⌞(N_k∩Ω), N_k:=η_k(M')∩{g<t}, u_k=0 Lⁿ-a.e. off E_k:=toMeasurable(Lⁿ,p(N_k∩Ω)) (measurable hull; p(N_k∩Ω) need not be measurable: |u_k|Lⁿ, push-forward of a measure on N_k∩Ω, vanishes on Borel sets missing it).
(d) For 0<s₀<R and a mollifier φ_{s₀}, (u_k∗φ_{s₀})(x)=Y_k(φ_{s₀}(x−·)dy)→θ₀α uniformly on B̄_R (by (b); equi-Lip: constant Lip(φ_{s₀})M(Y_k)). And ∫_{B_R}|u_k−u_k∗φ_{s₀}|≤s₀m_k: for v:=u_k∗φ_ϑ (small ϑ>0), ∫_{B_R}|v(x)−v(x−z)|dx≤|z|∫_{B_{R+|z|}}|∇v| (FTC on segments) and ∫_{B_{R+s₀}}|∇v|≤m_k, as for G∈C_c^∞(B_{R+s₀};ℝⁿ), |G|≤1: ∫∇v·G=−∫u_k div G̃=−Y_k(div G̃ dy)=−∂Y_k(Σ_jG̃_jε_j), G̃:=φ̌_ϑ∗G, |Σ_jG̃_jε_j|≤1, ε_j:=(−1)^{j−1}dy¹∧⋯d̂y^j⋯∧dyⁿ; average against φ_{s₀}(z), let ϑ↓0 (v→u_k in L¹_loc). So ∫_{B_R}|u_k−θ₀α|≤s₀m_k+ω_nRⁿsup_{B_R}|u_k∗φ_{s₀}−θ₀α|→0.
(e) Lⁿ(B_R∖E_k)≤(θ₀α)⁻¹∫_{B_R}|u_k−θ₀α|→0, and Lⁿ(B_R∩E_k)=Lⁿ(B_R∩p(N_k∩Ω))≤Hⁿ(N_k∩p⁻¹(B_R))≤μ_k(A') (p 1-Lip, Hⁿ=Lⁿ on ℝⁿ), A':={g≤t}∩p⁻¹(B̄_R) compact, limsup_kμ_k(A')≤ν(A')=αω_nRⁿ (only V₀+w meets A': t<2δ'). So ω_nRⁿ≤αω_nRⁿ: α_{i₀}≥1.
V12. By V10–V11, 1≥Σα_i≥N: N=1, α_1=1, w_1=0, ν=Hⁿ⌞V₀. As V₀ depends only on τ₀, every λ_i↓0 has a subseq. with Hⁿ⌞η_{a,λ_i}(M')→Hⁿ⌞V₀, so ∫_{η_{a,λ}(M')}f dHⁿ→∫_{V₀}f dHⁿ (λ↓0, f∈C_c): HasApproximateTangentSpaceAt n M' a V₀, and τ₀/θ₀=v_1∧⋯∧v_n is a unit orientation of V₀ (IsUnitOrientationOf), for Hⁿ-a.e. a∈M'. a↦V₀(a) is Borel (projection matrix polynomial in τ(a)/θ(a)).
V13. For Borel A⊆M', μ:=Hⁿ⌞A is finite with ATS P_x:=V₀(x) μ-a.e. (IMC(a)). Claim: finitely many Lip F_k:ℝⁿ→ℝ^P have μ(ℝ^P∖⋃F_k(ℝⁿ))≤μ(ℝ^P)/2. Iterating with A∖⋃F_k(ℝⁿ) (Borel: F_k(ℝⁿ) σ-compact) covers Hⁿ-a.a. of M' by countably many Lip images: M' is countably n-rectifiable.
Proof. For x with P_x let π_x:=P_x^⊥, X_α(π,x):={y: dist(y−x,π)<α|y−x|}, X_x:=X_{1/2}(π_x,x), D_ρ(x):=μ(B_ρ(x))/(ω_nρⁿ), D'_ρ(x):=μ(X_x∩B_ρ(x))/(ω_nρⁿ). Testing P_x on continuous approximants of 1_{B_1}, 1_{X̄_{1/2}(π_x,0)∩B̄_1} (Hⁿ⌞P_x-null boundaries; X̄_{1/2}(π_x,0)∩P_x={0}) gives (5) D_ρ(x)→1, (6) D'_ρ(x)→0 (ρ↓0). Lusin (exists_isClosed_continuousOn_of_measurable, for the coordinates of the projection matrix of P_x, Borel by V12; intersect the closed sets) gives closed F⊆A, μ(ℝ^P∖F)≤μ(ℝ^P)/4, with x↦P_x continuous and (5), (6) on F; f_k:=inf_{ρ<1/k}D_ρ→1, q_k:=sup_{ρ<1/k}D'_ρ→0 are Borel on F (rational ρ suffice by left continuity; semicontinuous via continuity of π_x on F); Egorov gives closed E⊆F, μ(F∖E)≤μ(ℝ^P)/4, with uniform convergence on E. So for ε:=2^{−1}16^{−n} some δ>0 has D_ρ≥1−ε, D'_ρ≤ε on E (ρ<δ). Take ℓ-subspaces π_1..π_N (ℓ:=P−n) with min_j‖p_π−p_{π_j}‖<1/16 for every ℓ-subspace π; E_j:={x∈E: ‖p_{π_j}−p_{π_x}‖<1/16}. (10) X_{1/4}(π_j,x)∩E_j∩B_{δ/2}(x)=∅ for x∈E_j (x∉X_{1/4}(π_j,x) by strictness): else for y in it, σ:=|y−x|∈(0,δ/2), z∈B_{σ/8}(y): dist(z−x,π_x)≤dist(y−x,π_j)+σ/16+σ/8<7σ/16≤|z−x|/2, so B_{σ/8}(y)⊆X_x∩B_{2σ}(x), (1−ε)ω_n(σ/8)ⁿ≤μ(B_{σ/8}(y))≤εω_n(2σ)ⁿ, i.e. (1−ε)8^{−n}≤ε2ⁿ=8^{−n}/2, absurd. By (10), for x₀∈ℝ^P and G_j:=E_j∩B_{δ/4}(x₀) (|x−y|<δ/2 on G_j), the projection p_j onto π_j^⊥≅ℝⁿ has |p_j(y)−p_j(x)|≥|y−x|/4 on G_j: G_j is a Lip graph over p_j(G_j)⊆π_j^⊥, the map extending to π_j^⊥ (McShane componentwise in an ONB of π_j, constant ×√ℓ): G_j⊆F(ℝⁿ), F Lip. Finitely many G_j cover the compact E, so μ(ℝ^P∖⋃F_k(ℝⁿ))≤μ(ℝ^P∖E)≤μ(ℝ^P)/2. ∎
V14. At a as in V12, C=τ₀Hⁿ⌞V₀=θ₀[[V₀]] ([[V₀]] oriented by v_1∧⋯∧v_n) has (ISP) (V8). For f:=⟨·,v_1⟩ and every t, the divergence theorem in V₀ gives ∂(C⌞{f<t})=θ₀[[V₀∩{f=t}]] oriented by ±v_2∧⋯∧v_n (n=1: ±θ₀δ_{tv_1}); for a.e. t it is IM, so by MR its mass measure θ₀H^{n−1}⌞(V₀∩{f=t}) is θ'H^{n−1}⌞M_t for an IMRep (M_t,θ',·), θ'≥1 integer, and uniqueness of Radon–Nikodym densities gives θ₀=θ' on a set of positive measure: θ₀∈ℤ (n=1: θ₀=θ'(tv_1)). So θ(a)∈ℤ_{≥1} for Hⁿ-a.e. a∈M'.
V15. Take Borel M''⊆M', Hⁿ(M'∖M'')=0, with V12, V14 at each point of M'' (Borel regularity; failure sets are null); mult:=θ on M'', 0 elsewhere (ℕ-valued Borel, ≥1 on the carrier); orient:=ξ_Γ=τ/θ. (M'',θ,ξ_Γ) is an IMRep in ℝ^P: M'' Borel, countably n-rectifiable (V13); ∫θdHⁿ=M(Γ)<∞; ξ_Γ is a.e. strongly measurable for Hⁿ⌞M'' (as for μ_Γ=θHⁿ⌞M', equivalent to Hⁿ⌞M'' as θ>0 there); for a.e. a∈M'' the ATS of M'' is V₀(a) (V12, IMC(a)), oriented by ξ_Γ(a); it represents Γ (V6). So Γ, hence T=Γ−(0−Y) (IMC(c)), is IM, proving (CL*), CL(n) (V2) and the induction. ∎

## Key steps

1. Induction: CL(0) via point masses; BR(d) from CL(d) by slicing and deformation-theorem approximation; CL(d+1) from CL(d), BR(d).
2. Localize by slicing to compact supports (CL*); subtract an IM filling Y to get a cycle Γ with the IM slice property.
3. Lower density bound η₀ (fillings, cone inequality); blow-ups at good points are θ₀Hⁿ⌞V₀, so tangent planes exist a.e.
4. Tangent planes give rectifiability, slices give integer θ; assemble the IMRep.

## Reference use

### local-project

Queries:
- `cat RUN/local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; cmp GMT/Ch07/Submission.lean GMT/Ch07/Contract.lean`
- `python3 scans of RUN/dag.json: selected node, prerequisite types, accepted reusable declarations and their lean_statement, status of the children of root.compactness_of_minimizing_currents-a1, lean_name collisions (dimred_mbl_: no match)`
- `grep -n _existing_lean_name_problem _accepted_checkpoint contract in /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py and speculation.py`
- `grep -rn of every cited Mathlib/SimonGMT lemma name in the pinned lake packages`
- `lean (v4.35.0-rc3) on AllTypes.lean, AssemblyCond.lean (#print axioms) and 12 Challenge_<key>.lean modules; lean_contract.validate_lean_statement on all child types`
- `sed -n on book/chapter-06.txt (2.15, 2.23–2.33, 3.3–3.10, 4.6–4.11) and book/chapter-07.txt (7.2.4–7.2.5)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1/decomposition-v5.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/mb2/lean/src/AssemblyCond.lean`

Pins match (HEAD b4d606d, Mathlib 25730c7c, SimonGMT 2b366308) and Submission.lean is byte-identical to the frozen contract. The pinned libraries lack Federer–Fleming compactness, the deformation theorem, flat convergence, Lipschitz slicing and integral push-forward by nonlinear maps; SimonGMT supplies currents, mass, support, weak convergence, affine push-forward, the Lipschitz area formula and approximate tangent spaces, and every cited library name exists. Accepted declarations with exact types: dtc_vanish_off_support and dor_imrep_massOn_eq_measure_and_support (reused). The children of root.compactness_of_minimizing_currents-a1 are decomposing, not accepted, so they cannot be shared; identical types with unique dimred_mbl_* names are used. A child's prerequisites are its children plus depends_on, so monotonicity enters as a hypothesis. All 12 child types elaborate and the conditional assembly proves the parent type (axioms propext, Classical.choice, Quot.sound).


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
