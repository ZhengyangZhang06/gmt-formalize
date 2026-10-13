<!-- theorem-id: gmt-ch07/root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.skeleton_retraction-a1 -->

## Theorem `Submission.cmcdt_skeleton_retraction`

Let P, m ∈ ℕ with m + 1 < P and put n := m + 1. There is a constant c > 0, depending only on P and m, such that for every a ∈ ℝ^P (Euclid P) with |a_i − 1/2| < 1/4 for all i the following holds. Let L*(a) := {y ∈ ℝ^P : there is a finite set s of coordinate indices with |s| ≥ m + 2 and y_i − a_i ∈ ℤ for all i ∈ s} (the dual skeleton) and d(x) := dist(x, L*(a)) (Metric.infDist). Then there is a map ψ : ℝ^P → ℝ^P such that (i) for every x with d(x) > 0, ψ(x) lies in the n-skeleton of the unit cubical grid, i.e. there is a set s of coordinate indices with P ≤ n + |s| and ψ(x)_i ∈ ℤ for all i ∈ s, and |ψ(x) − x| ≤ √P; (ii) for every r with 0 < r ≤ 1/4 and all x, y with d(x) ≥ r and d(y) ≥ r, |ψ(x) − ψ(y)| ≤ (c/r)|x − y|.

Node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.skeleton_retraction-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4206

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5957, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5963, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5968, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5973, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5978, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5983

## Lean problem

Declaration: `Submission.cmcdt_skeleton_retraction`

```lean
∀ (P m : ℕ), m + 1 < P → ∃ c : ℝ, 0 < c ∧ ∀ a : Euclid P, (∀ i, |a i - 1 / 2| < 1 / 4) → ∃ ψ : Euclid P → Euclid P, (∀ x : Euclid P, 0 < infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} → (∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, ψ x i = z) ∧ dist (ψ x) x ≤ Real.sqrt P) ∧ ∀ r : ℝ, 0 < r → r ≤ 1 / 4 → ∀ x y : Euclid P, r ≤ infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} → r ≤ infDist y {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} → dist (ψ x) (ψ y) ≤ c / r * dist x y
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

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.skeleton_retraction-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 6, Lemma 5.4 (chapter-06.txt, proof of 5.4 inside lines 1405–1928), as written out in Part D of the parent proof. It applies the documented correction |y − a| ≥ 1/4 (Simon prints 3/4) and states the cone property with the periodically translated planes split off.

Notation. n := m + 1, ℓ := P − n ≥ 1. For J ⊆ {1,…,P} with |J| = j and b ∈ ℤ^P, the closed j-face is F = F(b, J) := {x : b_i ≤ x_i ≤ b_i + 1 (i ∈ J), x_i = b_i (i ∉ J)}. J are its free coordinates, aff F := {x : x_i = b_i (i ∉ J)}, F̆ is its relative interior and ∂F := F ∖ F̆ is the union of its (j − 1)-faces. L_j := union of all closed j-faces. A point x lies in L_j iff at least P − j of its coordinates are integers: a point of F(b, J) has the P − j integer coordinates x_i = b_i (i ∉ J); conversely, if x_i ∈ ℤ for i in a set of P − j indices, let J be the complementary j indices and put b_i := ⌊x_i⌋ (i ∈ J), b_i := x_i (i ∉ J). In particular a point of L_n satisfies the statement's condition “∃ s, P ≤ n + |s|, x_i ∈ ℤ (i ∈ s)”. C := [0,1]^P. The coordinates of a satisfy a_i ∈ (1/4, 3/4). L*(a) is the set of y with at least n + 1 coordinates in a_i + ℤ, and d(x) := dist(x, L*(a)). d is 1-Lipschitz, and d(x) > 0 implies x ∉ L*(a). For a map f and a point x of its domain, D̄f(x) := limsup_{y→x} |f(y) − f(x)|/|y − x| (pointwise upper Lipschitz constant, y in the domain).

1. Centres of faces. For a face F = F(b, J) with |J| = j ≥ n + 1 put a_F ∈ aff F, (a_F)_i := b_i + a_i (i ∈ J), (a_F)_i := b_i (i ∉ J). Since a_i ∈ (1/4, 3/4), a_F ∈ F̆ and every point of ∂F (some free coordinate equal to b_i or b_i + 1) has distance > 1/4 from a_F. F − a_F contains the ball of radius 1/4 of the plane V_J := span{e_i : i ∈ J} and is contained in the ball of radius √j. A face shared by two cubes gets the same centre, because a_F is defined from F alone.

2. The dual skeleton meets a face in a cone. Let F = F(b, J), |J| = j ≥ n + 1. Then L*(a) ∩ F = U_F ∩ F, where U_F := ⋃ {Π_{J'} : J' ⊆ J, |J'| = n + 1} and Π_{J'} := {x ∈ aff F : x_i = (a_F)_i (i ∈ J')}. Proof: if x ∈ F ∩ L*(a), take s with |s| ≥ n + 1 and x_i − a_i ∈ ℤ for i ∈ s. For i ∉ J, x_i = b_i ∈ ℤ while a_i ∉ ℤ, so s ⊆ J. For i ∈ s, x_i − b_i ∈ [0, 1] and x_i − b_i ≡ a_i (mod 1) with a_i ∈ (1/4, 3/4), so x_i = b_i + a_i = (a_F)_i; any J' ⊆ s with |J'| = n + 1 gives x ∈ Π_{J'}. Conversely, if x ∈ F ∩ Π_{J'} then x_i − a_i = b_i ∈ ℤ for the n + 1 indices i ∈ J', so x ∈ L*(a). Each Π_{J'} is an affine subspace of aff F through a_F. So U_F is invariant under every homothety of aff F centred at a_F with nonzero ratio, and a_F ∈ L*(a).

3. Radial retractions. For F as in 2, let N_F be the gauge of the convex body F − a_F in V_J (N_F(v) = max_{i∈J} max(v_i/(1 − a_i), −v_i/a_i)), and put ψ_F(x) := a_F + (x − a_F)/N_F(x − a_F) for x ∈ F ∖ {a_F}. ψ_F(x) is the point of ∂F on the ray from a_F through x, and ψ_F = id on ∂F. By 1, N_F is 4-Lipschitz and N_F(v) ≥ |v|/√j. If x ∈ F ∖ L*(a) then x ∉ U_F, hence ψ_F(x) = a_F + λ(x − a_F) (λ > 0) ∉ U_F by the homothety invariance of U_F, hence ψ_F(x) ∈ ∂F ∖ L*(a) by 2. If x lies in two j-faces F ≠ F', then x lies in their intersection, a face of dimension < j, so x ∈ ∂F ∩ ∂F' and ψ_F(x) = x = ψ_{F'}(x). Hence ψ^{(j)} := ⋃_{|J|=j} ψ_F is a well-defined map L_j ∖ L*(a) → L_{j−1} ∖ L*(a). It is continuous because the j-faces form a locally finite closed cover of L_j and each ψ_F is continuous on F ∖ {a_F}. Radial estimate: for x, y ∈ F ∖ {a_F}, with v := x − a_F, w := y − a_F,
 |ψ_F(x) − ψ_F(y)| = |v/N_F(v) − w/N_F(w)| ≤ |v − w|/N_F(v) + |w| |N_F(w) − N_F(v)|/(N_F(v)N_F(w)) ≤ (1 + 4√j)√j |v − w|/|v|,
so D̄(ψ_F|F)(x) ≤ (1 + 4√j)√j/|x − a_F|.

4. Definition of ψ. On ℝ^P ∖ L*(a) put ψ := ψ^{(n+1)} ∘ ψ^{(n+2)} ∘ ⋯ ∘ ψ^{(P)} (L_P = ℝ^P). By 3 it is well defined and continuous, and it takes values in L_n ∖ L*(a). On L*(a) put ψ := id (never used). This proves the first half of (i) for every x with d(x) > 0. Same cube: if x ∈ z + C (z ∈ ℤ^P) and x ∉ L*(a), then ψ^{(P)}(x) = ψ_{z+C}(x) ∈ z + C. Inductively, if y ∈ (z + C) ∩ L_j ∖ L*(a), then y lies in a j-face G ⊆ z + C (its integer coordinates are z_i or z_i + 1; fix those), and ψ^{(j)}(y) = ψ_G(y) ∈ ∂G ⊆ z + C (any j-face containing y gives the same value by 3). Hence ψ(x) ∈ z + C and |ψ(x) − x| ≤ diam(z + C) = √P, which is the second half of (i). Also ψ(z + x) = z + ψ(x) for z ∈ ℤ^P, since L*(a) + z = L*(a) and the faces, centres and retractions are translated accordingly.

5. Pointwise bound D̄ψ(x) ≤ c₁(P, n)/d(x) for every x with d(x) > 0. The proof is by induction on ℓ = P − n ≥ 1, simultaneously for all P, n with that codimension and all admissible a. Points y near x lie in one of the finitely many closed unit cubes containing x, and the bound is proved on each of them; by periodicity we may take the cube to be C.
 (5a) ℓ = 1, i.e. P = n + 1. By 2 with F = C (j = P = n + 1, only J' = J), L*(a) ∩ C = {a}, and ψ = ψ^{(P)} = ψ_C on C. By 3, D̄(ψ|C)(x) ≤ (1 + 4√P)√P/|x − a| ≤ (1 + 4√P)√P/d(x), because a ∈ L*(a). So c₁(n + 1, n) := (1 + 4√(n+1))√(n+1).
 (5b) ℓ ≥ 2. On C ∖ L*(a), ψ = ψ̃ ∘ ψ_C, with ψ_C = ψ^{(P)} and ψ̃ := ψ^{(n+1)} ∘ ⋯ ∘ ψ^{(P−1)} on ∂C ∖ L*(a). Let y₀ := ψ_C(x) ∈ ∂C and let F be any (P − 1)-face of C containing y₀; for y ∈ C near x, ψ_C(y) is near y₀ and lies in one of the finitely many (P − 1)-faces of C containing y₀. Fix such an F = F(b, J), J = {1,…,P} ∖ {i₀}, b_{i₀} ∈ {0, 1}, b_i = 0 (i ∈ J). Identify aff F with ℝ^{P−1} by deleting the coordinate i₀. Under this identification:
 - the grid faces lying in aff F are the grid faces of ℝ^{P−1};
 - the centre of a face G ⊆ aff F is the centre of G for a' := (a_i)_{i ≠ i₀} (coordinates in (1/4, 3/4));
 - L := L*(a) ∩ aff F is the dual skeleton of ℝ^{P−1} for a' and the same n (the coordinate b_{i₀} ∈ ℤ is never in a_{i₀} + ℤ);
 - ψ̃ restricted to aff F ∖ L is the map of this construction for (P − 1, n, a'), whose codimension is ℓ − 1 ≥ 1. Indeed, a point y ∈ aff F ∩ L_j has at least (P − 1) − j integer coordinates besides y_{i₀}, so it lies in a j-face G ⊆ aff F, and by the consistency in 3 the value ψ^{(j)}(y) may be computed with such a G.
 By the induction hypothesis, D̄(ψ̃|F)(y₀) ≤ c₁(P − 1, n)/dist(y₀, L).
 Distance estimate. L is the union, over J' ⊆ J with |J'| = n + 1 and integers z_i (i ∈ J'), of the planes {u ∈ aff F : u_i = a_i + z_i (i ∈ J')}. Let L₀ be the union of those with all z_i = 0 and L₁ the union of the others. If some z_i ≠ 0 then a_i + z_i lies at distance > 1/4 from [0, 1], so dist(y₀, L₁) ≥ 1/4 for y₀ ∈ F. Let K₀ := ⋃_{J'} {u ∈ ℝ^P : u_i = a_i (i ∈ J')} (J' ⊆ J, |J'| = n + 1). Then K₀ ⊆ L*(a); K₀ is a union of affine subspaces through a, hence invariant under homotheties centred at a; and for u ∈ aff F, dist(u, K₀) = dist(u, L₀) (the coordinate i₀ is unconstrained in each plane of K₀). Since x ∈ C, y₀ = a + λ(x − a) with λ := 1/N_C(x − a) ≥ 1. Therefore dist(y₀, L₀) = dist(y₀, K₀) = λ dist(x, K₀) ≥ λ d(x). As d(x) ≤ |x − a|, λ d(x) ≤ |y₀ − a| ≤ √P, so dist(y₀, L) ≥ min(λ d(x), 1/4) ≥ λ d(x)/(4√P).
 Chain rule. Choose δ > 0 such that every (P − 1)-face of C meeting B_δ(y₀) contains y₀ (the finitely many faces not containing y₀ are at positive distance), and such that the induction bound holds up to ε on B_δ(y₀) for each of the finitely many faces containing y₀. By continuity of ψ_C, ψ_C(y) ∈ B_δ(y₀) for y ∈ C close to x. For such y, with F_y a (P − 1)-face containing ψ_C(y) and y₀,
 |ψ(y) − ψ(x)| ≤ (D̄(ψ̃|F_y)(y₀) + ε)|ψ_C(y) − y₀| ≤ (max_F D̄(ψ̃|F)(y₀) + ε)(D̄(ψ_C|C)(x) + ε)|y − x|.
 Using 3 for ψ_C and |y₀ − a| > 1/4,
 D̄(ψ|C)(x) ≤ 4√P c₁(P − 1, n)/(λ d(x)) · (1 + 4√P)√P/|x − a| = 4P(1 + 4√P)c₁(P − 1, n)/(|y₀ − a| d(x)) ≤ 16P(1 + 4√P)c₁(P − 1, n)/d(x).
 So c₁(P, n) := 16P(1 + 4√P)c₁(P − 1, n) works; it depends only on P and n. Taking the maximum over the finitely many closed cubes containing x (each handled by translation, with its own centre a + z ∈ L*(a)) gives D̄ψ(x) ≤ c₁/d(x), c₁ := c₁(P, n).

6. Lipschitz bound on {d ≥ r}. Let 0 < r ≤ 1/4 and d(x), d(y) ≥ r.
 (6a) Case |x − y| < r/2. Every point w of the segment [x, y] satisfies d(w) ≥ d(x) − |w − x| > r/2, so D̄ψ(w) < 2c₁/r by 5. The function f(t) := ψ(x + t(y − x)) is continuous on [0, 1] with limsup_{s→t}|f(s) − f(t)|/|s − t| ≤ (2c₁/r)|y − x| for every t. Then |f(1) − f(0)| ≤ (2c₁/r)|y − x|. To see this, for ε > 0 let t* := sup{t ∈ [0,1] : |f(s) − f(0)| ≤ ((2c₁/r)|y − x| + ε)s for all s ≤ t}. By continuity the inequality holds at t*; if t* < 1, the bound at t* extends it to [t*, t* + δ] for some δ > 0, a contradiction. Let ε ↓ 0.
 (6b) Case |x − y| ≥ r/2. By (i), |ψ(x) − ψ(y)| ≤ |ψ(x) − x| + |x − y| + |y − ψ(y)| ≤ 2√P + |x − y| ≤ (4√P/r)|x − y| + (1/(4r))|x − y|, using r ≤ 1/4.
 Hence (ii) holds with c := 2c₁ + 4√P + 1 > 0, which depends only on P and m. ∎

## Key steps

1. Faces F(b, J), centres a_F (free coordinates b_i + a_i), distance > 1/4 from a_F to ∂F.
2. L*(a) ∩ F is the union of affine planes of aff F through a_F (prescribed coordinates must be free and equal b_i + a_i), so it is a cone with vertex a_F.
3. Radial retractions ψ_F : F ∖ {a_F} → ∂F map F ∖ L*(a) into ∂F ∖ L*(a), agree on common faces, and satisfy D̄ψ_F ≤ (1 + 4√j)√j/|x − a_F|.
4. ψ := ψ^{(n+1)} ∘ ⋯ ∘ ψ^{(P)} maps {d > 0} into L_n, keeps each point in its closed unit cube (|ψ(x) − x| ≤ √P) and is ℤ^P-periodic.
5. Induction on ℓ = P − n: D̄ψ ≤ c₁/d, using the (P − 1)-face induction hypothesis, the split L = L₀ ∪ L₁ (periodic planes at distance ≥ 1/4), homogeneity of the cone K₀ ⊆ L*(a) about a, and |ψ_C(x) − a| ≥ 1/4 (corrected from Simon's 3/4).
6. Segment argument for |x − y| < r/2 and the bound 2√P + |x − y| otherwise give the Lipschitz constant (2c₁ + 4√P + 1)/r on {d ≥ r}.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean workspaces/gmt-ch07/GMT/Ch07/Contract.lean (identical); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); git -C local-references/123e8435b4a2469b/mathlib rev-parse HEAD (25730c7c759d108ef87ab70af2342a196760f79d, matches manifest)`
- `rg -n -i 'deformation theorem|federer|polyhedral|cubical|skeleton' project/GMT -g '*.lean'`
- `rg -n -i 'homotopy|lipschitz.*push|pushforward' project/GMT -g '*.lean'`
- `rg -n 'cmcdt_' project mathlib/Mathlib -g '*.lean' (no match)`
- `rg -n -i 'federer.?fleming|deformation theorem|flat norm|polyhedral chain' mathlib/Mathlib -g '*.lean' (no match)`
- `rg -n 'theorem (cthickening_smul|smul_cthickening|thickening_smul|infEDist_smul₀|infDist_smul₀)' mathlib/Mathlib`
- `rg -n 'theorem (exists_disjoint_subfamily_covering_enlargement|ae_differentiableAt|integral_divergence_of_hasFDerivAt_off_countable)' mathlib/Mathlib`
- `grep in lake-packages-25730c7c for the declarations cited by the child proofs: countablyRectifiable_iUnion, HasApproximateTangentSpaceAt.unique, countablyRectifiable_of_measure_zero, CountablyRectifiable.mono, area_image_criticalSet_eq_zero, injective_area_formula_lipschitzOn, weighted_area_formula_lipschitzOn_fiberSum, exteriorDerivativeOn_pullbackFormWithin, GeometricCurrentOn.boundary_affinePushforward, exteriorDerivative_affinePullbackForm, WeaklyConvergesOn.massOn_le_liminf, WeaklyConvergesOn.boundary, exteriorDerivative_apply, GeometricCurrentOn.boundary_boundary, euclideanHausdorffMeasure_smul₀, LipschitzOnWith.extend_real, exists_partition_approximatesLinearOn_of_hasFDerivWithinAt, LinearMap.exists_antilipschitzWith, MeasurableSet.image_of_continuousOn_injOn, MonotoneOn.intervalIntegrable_deriv, MonotoneOn.intervalIntegral_deriv_mem_uIcc, Monotone.ae_differentiableAt, LipschitzWith.ae_differentiableAt, LipschitzOnWith.hausdorffMeasure_image_le, LipschitzWith.integral_lineDeriv_mul_eq, ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable, cthickening_cthickening_subset, cthickening_subset_thickening', IsCompact.cthickening, Isometry.euclideanHausdorffMeasure_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, measurable_deriv (all found)`
- `python3 scan of runs/20261011T150044Z-ba604216b4/dag.json (681 nodes): lean_name collisions for the eight proposed names (none), frozen types of the five resolved dependencies, statuses; verbatim antecedent check of the child types`
- `lake env lean /tmp/cmcdt2/lean/V1Types.lean (eight child types elaborate); lake env lean /tmp/cmcdt2/lean/AssemblySkeleton.lean; lake env lean /tmp/cmcdt2/lean/Assembly.lean (assembly proof, #print axioms: propext, Classical.choice, Quot.sound); lake env lean /tmp/cmcdt2/lean/InstCheck.lean (ContDiff ℝ (⊤ : ℕ∞) = C^∞ ≠ ω; pointwise Sub by rfl; trace coercion)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Ball/Pointwise.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1/decomposition-v1.json`
- `/tmp/cmcdt2/lean/V1Types.lean`
- `/tmp/cmcdt2/lean/Assembly.lean`
- `/tmp/cmcdt2/lean/InstCheck.lean`

The snapshot (project b4d606d, Mathlib 25730c7c) has the same contract as the workspace Contract.lean and Submission.lean. The project holds only a separate, unsolved Ch06 specification of the deformation theorem and Lipschitz push-forward (project/GMT/Ch06/Contract.lean: DeformationTheorem, LipschitzPushforwardIntegerMultiplicity, IsLatticeChain; main_theorem := by sorry). It uses incompatible types (Eucl, IsLatticeChain) and cannot be imported into Ch07, so it is not reusable. Mathlib has no deformation, flat-norm or polyhedral-chain results (no match). It does provide every tool cited by the child proofs: Vitali covering, Rademacher, the divergence theorem, integrability of monotone derivatives, infEDist_smul₀, cthickening lemmas, and Hausdorff measure scaling and isometry. Every cited SimonGMT declaration exists. No declaration or DAG node uses the cmcdt_ prefix. All eight child types elaborate. The assembly from the five dependency types and three child types to the selected frozen type compiles with only propext, Classical.choice and Quot.sound.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
