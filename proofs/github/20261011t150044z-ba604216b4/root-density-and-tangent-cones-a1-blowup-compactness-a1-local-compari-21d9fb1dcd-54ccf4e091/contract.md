<!-- theorem-id: gmt-ch07/root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1 -->

## Theorem `Submission.dtc_bc_lc_flat_decomposition`

Let P, m ∈ ℕ with n := m + 1 < P. Let T_j (j ∈ ℕ) and T be integer multiplicity currents in 𝒟_n(ℝ^P) (GeometricCurrentOn univ n with IsIntegerMultiplicity) such that sup_j (M_W(T_j) + M_W(∂T_j)) < ∞ for every bounded open W ⊆ ℝ^P, and T_j ⇀ T in ℝ^P (WeaklyConvergesOn: T_j(ω) → T(ω) for every ω ∈ 𝒟ⁿ(ℝ^P)). Then for every bounded open W ⊆ ℝ^P there are integer multiplicity currents R_j ∈ 𝒟_{n+1}(ℝ^P) and S_j ∈ 𝒟_n(ℝ^P) (j ∈ ℕ) with T − T_j − S_j = ∂R_j for every j (Simon: T − T_j = ∂R_j + S_j) and M_W(R_j) + M_W(S_j) → 0. Here M_W is the SimonGMT mass massOn W (Euclidean coefficient norm).

Node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4757

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4196, https://github.com/ZhengyangZhang06/gmt-formalize/issues/808

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6345, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6346, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6348, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6356, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6358, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6361, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4196, https://github.com/ZhengyangZhang06/gmt-formalize/issues/808, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4928, https://github.com/ZhengyangZhang06/gmt-formalize/issues/810, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1174, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4664

## Lean problem

Declaration: `Submission.dtc_bc_lc_flat_decomposition`

```lean
∀ (P m : ℕ) (Ts : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), m + 1 < P → (∀ j, IsIntegerMultiplicity (Ts j)) → IsIntegerMultiplicity T → (∀ W : Set (Euclid P), IsOpen W → Bornology.IsBounded W → ⨆ j, ((Ts j).massOn W + (Ts j).boundary.massOn W) < ∞) → WeaklyConvergesOn Ts T → ∀ W : Set (Euclid P), IsOpen W → Bornology.IsBounded W → ∃ (R : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 2)) (S : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), (∀ j, IsIntegerMultiplicity (R j) ∧ IsIntegerMultiplicity (S j) ∧ T - Ts j - S j = (R j).boundary) ∧ Tendsto (fun j => (R j).massOn W + (S j).massOn W) atTop (𝓝 0)
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

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 6, Definition 7.1 and the proof of the "only if" part of Theorem 7.2 (chapter-06.txt lines 2004–2120, printed pp. 170–172). Here U = ℝ^P, so "W ⊂⊂ U" means "W bounded", and the ambient dimension is n + ℓ = P with ℓ = P − n ≥ 1, the range n, ℓ ∈ {1, 2, …} of Simon §5. This is the result cited as (C1) in step 4 of the parent proof. The printed proof is copied. The details it leaves to the reader are written out in steps 3, 6 and 7: the localisation to a ball, the identification of the limit after localisation, and the passage from d_W(T_j, T) → 0 to explicit decompositions. In steps 4–6 the error currents S only need small mass; they need not be integer multiplicity. Integer multiplicity of the final error current is recovered in step 7 by applying boundary rectifiability to the (n+1)-current R^{(q)}. So every citation stays inside Simon's range (dimensions ≥ 1, codimension ℓ ≥ 1), also when m = 0.

Cited results of the source text, each used in its stated range:
(D) Simon 6.5.3, Deformation Theorem, scaled version (lines 1462–1480), for n-currents in ℝ^{n+ℓ}, n, ℓ ≥ 1. Let T ∈ 𝒟_n(ℝ^P) with M(T) + M(∂T) < ∞ and let σ > 0. Then T − P = ∂R + S, where:
 • P = Σ_F β_F[[F]], the sum over the n-faces F of the cubical grid of side σ;
 • M(P) ≤ cM(T), M(R) ≤ cσM(T) and M(S) ≤ cσM(∂T), with c = c(n, ℓ);
 • spt P ∪ spt R ⊆ {x : dist(x, spt T) < 2√P σ} and spt S ⊆ {x : dist(x, spt ∂T) < 2√P σ}.
 If T is integer multiplicity, then P and R are integer multiplicity (β_F ∈ ℤ). Only these properties are used; S is just a current.
(BR) Simon 6.6.3, Boundary Rectifiability Theorem (lines 1993–1996). If T ∈ 𝒟_k(U) is integer multiplicity and M_V(∂T) < ∞ for all V ⊂⊂ U, then ∂T is integer multiplicity. It is used only for k = n + 1 ≥ 2.
(SL) Simon 6.4.6–4.10 (lines 1305–1385). Suppose M_V(T) + M_V(∂T) < ∞ for all V ⊂⊂ U and f is Lipschitz, and set ⟨T, f, t−⟩ := ∂(T⌞{f < t}) − (∂T)⌞{f < t}. Here T⌞E is the restriction of T to the Borel set E, defined through the measure representation of T (2.7).
 • (4.8) ⟨T, f, t−⟩ vanishes on every form whose support is disjoint from f⁻¹(t).
 • (4.9) For bounded open W: M_W(⟨T, f, t−⟩) ≤ ess sup_W|Df|·liminf_{h↓0} h⁻¹ M_W(T⌞{t − h < f < t}).
 • The lower Dini derivative D(t) := liminf_{h↓0} h⁻¹ μ_T(W ∩ {t − h < f < t}) of the nondecreasing function t ↦ μ_T(W ∩ {f < t}) is measurable, with ∫_a^b D dt ≤ μ_T(W ∩ {a < f < b}). This is Lebesgue's theorem for monotone functions, which is how 4.10 is derived.
(ML) Elementary mass localisation. Let X be a current that vanishes on every form whose support is disjoint from a compact set C, and let V ⊇ C be open. Then M(X) ≤ M_V(X). Proof: choose χ ∈ C_c^∞(V) with 0 ≤ χ ≤ 1 and χ = 1 on a neighbourhood of C. For every admissible ω, tsupport((1 − χ)ω) is disjoint from C and χω is admissible for M_V, so X(ω) = X(χω) + X((1 − χ)ω) = X(χω) ≤ M_V(X).
(CO) Simon 6.3.13 (lines 905–960). Integer multiplicity currents are complete for the seminorms M_V, V ⊂⊂ U. In particular, an M-absolutely convergent series of integer multiplicity currents with supports in a fixed compact set converges in mass to an integer multiplicity current.
(R) Integer combinations of integer multiplicity currents are integer multiplicity (Simon 6.3.2(1); sibling im_calculus (c)). The restriction (M ∩ E, θ, ξ) of a representation to a Borel set E represents an integer multiplicity current (sibling im_calculus (b)).
(MM) M_V(A) = μ_A(V) for integer multiplicity A and open V (sibling mass_eq_measure), and μ_A is finite on compact sets.
(LSC) Lower semicontinuity of mass under weak convergence (Simon 6.2.14; SimonGMT WeaklyConvergesOn.massOn_le_liminf).

Throughout, n := m + 1, ℓ := P − n ≥ 1, B_r := ball(0, r), and "IM" means integer multiplicity. For currents A, B in one domain and any V: M_V(0 − A) = M_V(A), since ω ↦ −ω preserves admissible forms, and M_V(A ± B) ≤ M_V(A) + M_V(B).

1. (The class I and the pseudometrics.) Let I be the set of IM currents A ∈ 𝒟_n(ℝ^P) with M_V(∂A) < ∞ for every bounded open V.
 (a) Each T_j ∈ I by hypothesis.
 (b) T ∈ I: ∂T_j ⇀ ∂T, because ∂T_j(ω) = T_j(dω) → T(dω). So by (LSC), M_V(∂T) ≤ liminf_j M_V(∂T_j) ≤ sup_j (M_V(T_j) + M_V(∂T_j)) < ∞.
 (c) For A₁, A₂ ∈ I and bounded open V put (Simon 7.1) d_V(A₁, A₂) := inf{M_V(S) + M_V(R) : A₁ − A₂ = ∂R + S, with R ∈ 𝒟_{n+1}(ℝ^P) and S ∈ 𝒟_n(ℝ^P) IM}. The set is nonempty: R = 0 and S = A₁ − A₂, which is IM by (R).

2. (Reduction.) Fix a bounded open W. It suffices to show d_W(T_j, T) → 0.
 (a) Suppose d_W(T_j, T) → 0. For each j choose IM R'_j, S'_j with T_j − T = ∂R'_j + S'_j and M_W(R'_j) + M_W(S'_j) ≤ d_W(T_j, T) + 2^{−j}. Put R_j := 0 − R'_j and S_j := 0 − S'_j, which are IM by (R).
 (b) Then T − T_j − S_j = −(T_j − T) + S'_j = −∂R'_j = ∂R_j, and M_W(R_j) + M_W(S_j) = M_W(R'_j) + M_W(S'_j) → 0.
 (c) Since (d_W(T_j, T))_j is a sequence in [0, ∞], it tends to 0 as soon as every subsequence has a further subsequence along which it tends to 0. This is Simon's last paragraph: "since we can thus extract a subsequence converging relative to d_W̃ from any given subsequence …". So fix an arbitrary subsequence; we keep calling it (T_j) and pass to further subsequences below.

3. (Localisation.) Simon: "by 4.5(1),(2) and an argument as in 6.7(2) of Ch. 2 we can find a subsequence … with sup_j' M(∂(T_j'⌞W_i)) < ∞ … thus we can assume … spt T_j ⊆ W̄".
 (a) Choose r₀ ≥ 1 with W ⊆ B_{r₀} and let f(x) := |x|, a 1-Lipschitz function. Put V := B_{r₀+2} and Λ := sup_j (M_V(T_j) + M_V(∂T_j)) < ∞.
 (b) Fix j and t ∈ (r₀, r₀ + 1). By 4.8 the slice ⟨T_j, f, t−⟩ vanishes on forms whose support misses the compact set f⁻¹(t) = ∂B_t ⊆ V, so M(⟨T_j, f, t−⟩) ≤ M_V(⟨T_j, f, t−⟩) by (ML). By 4.9 with W = V and |Df| ≤ 1, this is at most liminf_{h↓0} h⁻¹ M_V(T_j⌞{t − h < f < t}). Since {t − h < f < t} ⊆ V for 0 < h < t, the restriction T_j⌞{t − h < f < t} is IM by (R) with weight μ_{T_j}⌞{t − h < f < t}, and by (MM) its mass in V is μ_{T_j}({t − h < f < t}). Hence M(⟨T_j, f, t−⟩) ≤ D_j(t) := liminf_{h↓0} h⁻¹ μ_{T_j}(V ∩ {t − h < f < t}). D_j is measurable, and ∫_{r₀}^{r₀+1} D_j dt ≤ μ_{T_j}(V) = M_V(T_j) ≤ Λ by (MM).
 (c) By Fatou's lemma, ∫_{r₀}^{r₀+1} liminf_j D_j dt ≤ Λ. So there is t₀ ∈ (r₀, r₀ + 1) with liminf_j D_j(t₀) < ∞. Pass to a subsequence along which Λ' := sup_j M(⟨T_j, f, t₀−⟩) < ∞.
 (d) Put W₁ := B_{t₀} and T'_j := T_j⌞W₁. T'_j is IM by (R), being represented by (M_j ∩ W₁, θ_j, ξ_j). Moreover spt T'_j ⊆ closure(W₁) and ∂T'_j = (∂T_j)⌞W₁ + ⟨T_j, f, t₀−⟩. By (MM) with V = ℝ^P, M(T'_j) = μ_{T_j}(W₁) ≤ M_V(T_j). Also M((∂T_j)⌞W₁) ≤ μ_{∂T_j}(W₁) ≤ M_V(∂T_j), where μ_{∂T_j} is the Radon measure representing ∂T_j (2.7). Hence M(T'_j) + M(∂T'_j) ≤ Λ + Λ' =: M₀ for all j.
 (e) T'_j(ω) = T_j(ω) for every ω ∈ 𝒟ⁿ(ℝ^P) with tsupport ω ⊆ W₁.
 (f) closure(W) ⊆ closedBall(0, r₀) ⊆ W₁.
 Let 𝒞 be the set of IM A ∈ 𝒟_n(ℝ^P) with spt A ⊆ closure(W₁) and M(A) + M(∂A) ≤ M₀. All T'_j lie in 𝒞.

4. (Total boundedness; Simon (1)–(3).) Let W̃ := B_{t₀+1}.
 Claim: for every ε > 0 there are finitely many IM currents P₁, …, P_N ∈ 𝒟_n(ℝ^P) such that every A ∈ 𝒞 admits some k ≤ N, an IM R ∈ 𝒟_{n+1}(ℝ^P) and a current S ∈ 𝒟_n(ℝ^P) with A − P_k = ∂R + S, spt R ∪ spt S ⊆ W̃ and M(R) + M(S) < ε.
 (a) Choose σ ∈ (0, 1) with 2√P σ < 1 and cσM₀ < ε.
 (b) Let A ∈ 𝒞. A is IM with M(A) + M(∂A) ≤ M₀ < ∞, so (D) gives IM P, R and a current S with A − P = ∂R + S and M(R) + M(S) ≤ cσ(M(A) + M(∂A)) < ε. The supports of P, R and S lie within 2√P σ of spt A ∪ spt ∂A ⊆ closure(W₁), hence in W̃.
 (c) P = Σ_F β_F[[F]] with β_F ∈ ℤ and M(P) = Σ_F |β_F|σⁿ ≤ cM₀. Since spt P ⊆ W̃, only the finitely many n-faces F of the σ-grid meeting the bounded set W̃ occur, and |β_F| ≤ cM₀σ^{−n}.
 (d) So P belongs to a finite set {P₁, …, P_N} that depends only on ε, M₀, W₁, n and ℓ.

5. (A Cauchy subsequence; Simon (5).)
 (a) Apply step 4 with ε = 2^{−r−2} for r = 1, 2, …. By the pigeonhole principle and a diagonal argument there are indices j₁ < j₂ < … and, for each r, a single P^{(r)} among the finitely many currents of step 4 (for ε = 2^{−r−2}) such that T'_{j_s} − P^{(r)} = ∂R_{s,r} + S_{s,r} for all s ≥ r. Here R_{s,r} is IM, S_{s,r} is a current, both are supported in W̃, and M(R_{s,r}) + M(S_{s,r}) < 2^{−r−2}.
 (b) Subtract the decompositions for s = r + 1 and s = r: T'_{j_{r+1}} − T'_{j_r} = ∂R_r + S_r, where R_r := R_{r+1,r} − R_{r,r} is IM by (R) and S_r := S_{r+1,r} − S_{r,r}. Both are supported in closure(W̃), and M(R_r) + M(S_r) < 2^{−r−1}.

6. (Series; Simon: "by 3.13 we can define integer multiplicity R^{(ℓ)}, S^{(ℓ)} by the M-absolutely convergent series".)
 (a) For q ≥ 1 the series R^{(q)} := Σ_{r ≥ q} R_r converges absolutely in mass; by (CO) its limit is IM and the partial sums converge to it in mass, hence weakly.
 (b) For each ω, Σ_{r≥q} |S_r(ω)| ≤ sup|ω|·Σ_r M(S_r) < ∞. So S^{(q)}(ω) := Σ_{r ≥ q} S_r(ω) is a linear functional with |S^{(q)}(ω)| ≤ 2^{−q} sup|ω|, hence a current; it is the mass limit of the partial sums.
 (c) M(R^{(q)}) + M(S^{(q)}) ≤ Σ_{r≥q} 2^{−r−1} = 2^{−q}.
 (d) Summing step 5 for r = q, …, L − 1 gives T'_{j_L} − T'_{j_q} = ∂(Σ_{r=q}^{L−1} R_r) + Σ_{r=q}^{L−1} S_r.
 (e) Evaluate at ω ∈ 𝒟ⁿ(ℝ^P) with tsupport ω ⊆ W₁ and let L → ∞. We have T'_{j_L}(ω) = T_{j_L}(ω) → T(ω), (Σ_{r=q}^{L−1} R_r)(dω) → R^{(q)}(dω) and (Σ_{r=q}^{L−1} S_r)(ω) → S^{(q)}(ω). Hence
 (★) T(ω) − T_{j_q}(ω) = ∂R^{(q)}(ω) + S^{(q)}(ω) whenever tsupport ω ⊆ W₁.

7. (A global integer multiplicity decomposition.)
 (a) ∂R^{(q)} is IM. By 6(d), ∂(Σ_{r=q}^{L−1} R_r) = T'_{j_L} − T'_{j_q} − Σ_{r=q}^{L−1} S_r has mass ≤ 2M₀ + 1, and it converges weakly to ∂R^{(q)} as L → ∞. By (LSC), M(∂R^{(q)}) ≤ 2M₀ + 1 < ∞. Since R^{(q)} is an IM (n+1)-current, (BR) applies.
 (b) Put S^♯_q := (T − T_{j_q}) − ∂R^{(q)}, which is IM by (R). Then T − T_{j_q} = ∂R^{(q)} + S^♯_q.
 (c) By (★), S^♯_q(ω) = S^{(q)}(ω) for every ω with tsupport ω ⊆ W₁ ⊇ W. So M_W(S^♯_q) = M_W(S^{(q)}) ≤ M(S^{(q)}).
 (d) Changing signs (R ↦ 0 − R^{(q)}, S ↦ 0 − S^♯_q) gives an IM decomposition of T_{j_q} − T. Hence d_W(T_{j_q}, T) ≤ M_W(R^{(q)}) + M_W(S^♯_q) ≤ 2^{−q} → 0 as q → ∞.

8. (Conclusion.) By steps 3–7, every subsequence of (T_j) has a further subsequence along which d_W(T_j, T) → 0. Hence d_W(T_j, T) → 0, and step 2 produces the required IM R_j ∈ 𝒟_{n+1}(ℝ^P), S_j ∈ 𝒟_n(ℝ^P) with T − T_j − S_j = ∂R_j and M_W(R_j) + M_W(S_j) → 0. ∎

## Key steps

1. C and the T_j lie in Simon's class I (M_V(∂T) < ∞ by lower semicontinuity). It suffices to prove d_W(T_j, T) → 0 for the pseudometric of 7.1, and for that it suffices that every subsequence has a further subsequence along which it holds.
2. Localise: the slicing bound 4.9 (with its integrated form 4.10) and Fatou give t₀ ∈ (r₀, r₀ + 1) and a subsequence with M(T_j⌞B_{t₀}) + M(∂(T_j⌞B_{t₀})) ≤ M₀.
3. Total boundedness: the deformation theorem 5.3 writes each such current as one of finitely many integer polyhedral currents plus ∂R + S, with R integer multiplicity, supports in B_{t₀+1} and M(R) + M(S) < ε.
4. Pigeonhole gives T'_{j_{r+1}} − T'_{j_r} = ∂R_r + S_r with masses < 2^{−r−1}. R^{(q)} = Σ_{r≥q} R_r is integer multiplicity by 3.13, S^{(q)} = Σ_{r≥q} S_r is a current, and T − T_{j_q} = ∂R^{(q)} + S^{(q)} on forms supported in B_{t₀}.
5. Globalise: ∂R^{(q)} is integer multiplicity by 6.3 for the (n+1)-current R^{(q)}, so S^♯_q := T − T_{j_q} − ∂R^{(q)} is integer multiplicity and d_W(T_{j_q}, T) ≤ 2^{−q}. Conclude d_W(T_j, T) → 0 and pick near-optimal decompositions with signs changed.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; read workspace GMT/Ch07/Contract.lean, GMT/Ch07/README.md (contract unchanged; Submission.lean byte copy)`
- `rg/grep 'def GeometricCurrentOn.massOn|massAdmissibleOn|covectorEuclideanNorm_neg|le_massOn|massOn_mono|massOn_le_liminf' simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `grep 'structure GeometricCurrentOn|instance .*Zero|def GeometricCurrentOn.boundary|boundary_boundary|exteriorDerivativeTestOn|tsupport_exteriorDerivative_subset|WeaklyConvergesOn' simongmt/Poincare/SimonGMT/Chapter06/Currents.lean; grep 'abbrev Covector|abbrev DifferentialForm|abbrev exteriorDerivative' Chapter06/Forms.lean`
- `grep 'restrictDomain|testFormOnInclusion|VanishesOn|zeroRegion|def GeometricCurrentOn.support|isOpen_zeroRegion' simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `grep 'def CountablyRectifiable|def HasApproximateTangentSpaceAt|blowUpMap|HasApproximateTangentSpaceAt.unique|support_euclideanHausdorffMeasure_restrict_submodule' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (no slicing, flat-norm, deformation theorem or non-affine push-forward in Chapter06)`
- `python3 -I scans of dag.json (673 nodes at the first scan, 783 at the final re-check): related nodes cmc_flat_convergence, cmc_slice_mass_bounds, dimred_mbl_pushforward, dimred_mbl_local_comparison, imrep_c1_diffeo_pushforward_im (not accepted, not reusable); accepted candidates dtc_mass_eq_measure, dtc_vanish_off_support, cmc_imRep_locality_restrict_sub, dtc_restrictDomain_isIntegerMultiplicity, rsd_cmr_support_subset_of_vanish, dtc_approxTangent_of_null_diff, lcmp_massOn_le_add_of_eval_eq, dpf_pushforward_formula_current_exists, dpf_pushforward_formula_boundaryVanishes; collision check of the seven new dtc_bc_lc_ names (none)`
- `git grep 'theorem Submission.<name> ' <accepted commit> -- GMT for the five reused declarations; whitespace-normalised type comparison (all IDENTICAL); git show e34a71c (dispatch commit contains only the contract)`
- `#check of Mathlib names at the pin: Filter.extraction_forall_of_eventually, ENNReal.tendsto_atTop_zero_of_tsum_ne_top, Metric.mem_thickening_iff_infDist_lt, IsCompact.cthickening, Measure.countable_meas_level_set_pos, norm_fderiv_le_of_lipschitzOn, ENNReal.tsum_geometric, restrict_withDensity, Measure.le_iff, image_eq_zero_of_notMem_tsupport`
- `lake env lean /tmp/dtcbclc/check/Types.lean; challenge modules /tmp/dtcbclc/check/challenges/Challenge_<key>.lean (12, generated by verifier gmt-compare.py child_modules, contract mode); lake env lean /tmp/dtcbclc/out/Assembly.lean with #print axioms for assembly and ret_assembly`
- `sed book/chapter-07.txt lines 150-300 (Simon 7.2.4 proof (1)-(14), Remark 7.2.5); book/chapter-06.txt lines 395-540, 700-1000, 1140-1500, 1990-2120 (2.23-2.29, 3.1-3.14, 4.1-4.11, 5.1-5.4, 6.3, 7.1-7.2); book/chapter-03.txt lines 100-160, 327-445 (1.6, 2.1-2.10)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-comparison-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-local-comparison-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/dtcbclc/out/Assembly.lean`
- `/tmp/dtcbclc/check/Types.lean`
- `/tmp/dtcbclc/stmts/children.py`

The pinned SimonGMT library provides currents, boundary, massOn with the Euclidean coefficient norm, support/zeroRegion, restrictDomain, testFormOnInclusion, lower semicontinuity of mass, CountablyRectifiable and HasApproximateTangentSpaceAt. It has no flat-norm theorem, deformation theorem, slicing, C¹ push-forward of currents or area/coarea formula on rectifiable sets. These are the three Simon Ch. 6 results (C1)–(C3) cited by the supplied proof, so they become the children flat_decomposition, slicing and pushforward. Related DAG nodes in other branches (cmc_flat_convergence, cmc_slice_mass_bounds, dimred_mbl_pushforward) are not accepted, so they cannot be reused and the new names are unique. Five accepted declarations are reused with identical types: dtc_mass_eq_measure, dtc_vanish_off_support, cmc_imRep_locality_restrict_sub, dtc_restrictDomain_isIntegerMultiplicity and rsd_cmr_support_subset_of_vanish. All Mathlib lemmas used in the Lean assembly exist at the pin. All 12 child types elaborate in the comparator scope. The Lean assembly proves the exact frozen type of dtc_bc_local_comparison from the 12 child types and the sibling measure_locality type, and proves retraction_comparison from its declared siblings, using only propext, Classical.choice and Quot.sound.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
