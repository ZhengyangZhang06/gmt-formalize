<!-- theorem-id: gmt-ch07/root.density_one_implies_regular-a1.limsup_mass_bound-a1.projected_comparison-a1.pf_integer-a1 -->

## Theorem `Submission.dor_lmb_pc_pushforward_isIntegerMultiplicity`

Assume (TL), the frozen statement of the sibling-of-parent node dor_lmb_approx_tangent_locality: for all P, n ∈ ℕ, every open U ⊆ ℝ^P and Borel sets A ⊆ B ⊆ U with Hⁿ(B ∩ K) < ∞ for every compact K ⊆ U, for Hⁿ-a.e. x ∈ A and every linear subspace Q, B has approximate tangent space Q at x (Simon Ch. 3, 1.4; HasApproximateTangentSpaceAt) if and only if A does. Let P, n ∈ ℕ with n ≥ 1, U ⊆ ℝ^P open, R = (M, θ, ξ) an integer multiplicity triple in U (IMRep U n), K ⊆ U compact with Hⁿ(M ∖ K) = 0, O ⊆ ℝ^P open with K ⊆ O, f : ℝ^P → ℝ^P of class C¹ on O with f(K) ⊆ U, and Q ∈ 𝒟_n(U) with Q(ω) = ∫_M θ(x)·ξ(x)(ω(f(x))∘Df(x)) dHⁿ(x) for every ω ∈ 𝒟ⁿ(U) (Df(x) = fderiv ℝ f x, α∘L = α.compContinuousLinearMap L). Then Q is integer multiplicity: Q = τ(C, N', ζ') for some integer multiplicity triple (C, N', ζ') in U (IsIntegerMultiplicity Q).

Node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.projected_comparison-a1.pf_integer-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4756

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4140, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4147, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5835, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5591, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7119, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7121, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7122, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7126, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7127, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7132, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7137, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7143

## Lean problem

Declaration: `Submission.dor_lmb_pc_pushforward_isIntegerMultiplicity`

```lean
(∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q) → ∀ (P n : ℕ) (U K O : Set (Euclid P)) (R : IMRep U n) (f : Euclid P → Euclid P) (Q : GeometricCurrentOn U n), IsOpen U → 0 < n → IsCompact K → K ⊆ U → μHE[n] (R.carrier \ K) = 0 → IsOpen O → K ⊆ O → ContDiffOn ℝ 1 f O → f '' K ⊆ U → (∀ ω : TestFormOn U n, Q ω = ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (((ω : DifferentialForm (Euclid P) n) (f x)).compContinuousLinearMap (fderiv ℝ f x)) ∂μHE[n]) → IsIntegerMultiplicity Q
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

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.projected_comparison-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.projected_comparison-a1.pf_integer-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5(c) of the parent proof, i.e. Simon Ch. 6, 3.3–3.9 (chapter-06.txt lines 770–860), with the correction stated in the parent: Simon's multiplicity N in 3.8 is only a non-negative integer (oppositely oriented sheets with the same image cancel; e.g. an oriented rectangle boundary projected onto a line has zero push-forward), so the carrier is restricted to {N ≥ 1}. Also used: Simon Ch. 3, 1.1–1.6 and 2.6 (chapter-03.txt lines 1–143 and 330–410) and the tangent-locality statement (TL) assumed in the hypothesis. Here K, O and f play the roles of F = B̄_t(y), B_r(y) and π, and Hⁿ(M ∖ K) = 0 replaces the parent's step 2(a).
Deviation from the parent, for formalizability (the mathematics is the same): the parent's step 5(c2) obtains the injectivity pieces from C¹ submanifolds N_j covering M, i.e. from the "only if" half of Simon Ch. 3, Lemma 1.2, which the pinned SimonGMT library does not contain (Chapter03/SubmanifoldCover.lean proves only the converse). Step 2 below obtains the pieces instead from Lipschitz parametrizations, SimonGMT's regular-set lemmas and Mathlib's partition lemma exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (the same construction proves the accepted DAG declaration dpf_rectifiable_bilipschitz_pieces, which a decomposition of this node may reuse). The approximate tangent planes of the image pieces, which the parent reads off from the C¹ image submanifolds Σ_k, are supplied by Lemma T below. Steps 3–9 are the parent's (c3)–(c9).
Notation. Hⁿ := μHE[n]; on ℝⁿ it equals Lebesgue measure Lⁿ (EuclideanSpace.euclideanHausdorffMeasure_eq_volume). M_R := R.carrier, θ := R.mult, ξ := R.orient. Λⁿ denotes the n-covectors and Λ_n := MultiVector P n the n-vectors of ℝ^P. For increasing I = (i₁ < ⋯ < iₙ) let dx^I(v₁, …, vₙ) := det[(v_j)_{i_k}]_{k,j} and e_I := (e_{i₁}, …, e_{iₙ}); every n-covector satisfies α = Σ_I α(e_I)dx^I (multilinearity and the alternating property), so the coordinates ζ(dx^I) determine ζ ∈ Λ_n. Put |α|_E := (Σ_I α(e_I)²)^{1/2} and |ζ| := (Σ_I ζ(dx^I)²)^{1/2}. For a linear L : ℝ^P → ℝ^P and ζ ∈ Λ_n let L_#ζ ∈ Λ_n, (L_#ζ)(α) := ζ(α∘L); then (L₁L₂)_# = (L₁)_#(L₂)_#. For a linear A : ℝⁿ → ℝ^P let A_#e ∈ Λ_n, (A_#e)(α) := α(Ae₁, …, Aeₙ) (e the standard basis of ℝⁿ), and J_A := det(⟨Ae_i, Ae_j⟩)^{1/2} (= normDet A). For g : ℝⁿ → ℝ^P differentiable at a, J_g(a) := J_{Dg(a)} (SimonGMT areaJacobianAt).
Multilinear facts (the parent's (L1)–(L4), with proofs).
 (L1) For v₁, …, vₙ ∈ ℝ^P: α(v) = Σ_I α(e_I)·det[(v_j)_I] (expand α = Σ_I α(e_I)dx^I), and Σ_I det[(v_j)_I]² = det(⟨v_i, v_j⟩) (Cauchy–Binet). By Cauchy–Schwarz, |α(v)| ≤ |α|_E·det(⟨v_i, v_j⟩)^{1/2}. Hadamard's inequality det(⟨v_i, v_j⟩) ≤ Π_j|v_j|² (Gram–Schmidt: for independent v, v_j = Σ_{i≤j} R_{ij}σ_i with σ orthonormal, det(⟨v_i, v_j⟩) = Π_j R_{jj}² and |R_{jj}| ≤ |v_j|; for dependent v the determinant is 0) gives |α(v)| ≤ |α|_E·Π_j|v_j|. Also |α(v)| ≤ ‖α‖·Π_j|v_j| (operator norm).
 (L2) For every ζ ∈ Λ_n and α: ζ(α) = Σ_I α(e_I)ζ(dx^I), so |ζ(α)| ≤ |ζ|·|α|_E (Cauchy–Schwarz). If ζ(α) = ±α(τ) with τ orthonormal, then |ζ|² = Σ_I det[(τ_j)_I]² = det(⟨τ_i, τ_j⟩) = 1 (Cauchy–Binet), so |ζ| = 1.
 (L3) Let ζ(α) = ±α(τ) and ζ'(α) = ±α(σ) for orthonormal bases τ, σ of the same n-plane. Then τ_j = Σ_i O_{ij}σ_i with O := (⟨σ_i, τ_j⟩) orthogonal, so α(τ) = det(O)·α(σ) with det O = ±1 (multilinear alternating expansion), and ζ' = ±ζ.
 (L4) Let ζ(α) = s·α(τ) (s = ±1) for an orthonormal basis τ of an n-plane P₀, and L linear. Then (L_#ζ)(α) = s·α(Lτ₁, …, Lτₙ), and by (L2)'s computation |L_#ζ| = det(⟨Lτ_i, Lτ_j⟩)^{1/2} ≤ Π_i|Lτ_i| ≤ ‖L‖ⁿ (Hadamard). If |L_#ζ| = 0 then (Lτ_i) is dependent and L_#ζ = 0 (alternating). If |L_#ζ| > 0 then L is injective on P₀, L(P₀) is an n-plane with orthonormal basis σ, Lτ_j = Σ_l B_{lj}σ_l, (L_#ζ)(α) = s·det(B)·α(σ) by (L3)'s expansion, and |det B| = |L_#ζ|; so L_#ζ/|L_#ζ| is a unit orientation of L(P₀). The same computation with τ replaced by the standard basis e of ℝⁿ shows: for injective A : ℝⁿ → ℝ^P, |A_#e| = J_A > 0 and A_#e/J_A is a unit orientation of range A.
0. Set-up and cutoff.
 (a) M := M_R ∩ K is Borel (K is compact, hence closed). It is countably n-rectifiable (subset of M_R; SimonGMT CountablyRectifiable.mono). As θ ≥ 1 on M_R, Hⁿ(M) ≤ ∫_M θ dHⁿ < ∞ (R.locallyIntegrable_mult with K). Since Hⁿ(M_R ∖ K) = 0, Q(ω) = ∫_M θ(x)ξ(x)(ω(f(x))∘Df(x)) dHⁿ(x) for ω ∈ 𝒟ⁿ(U).
 (b) Choose an open V with K ⊆ V and closure V compact and contained in O, and χ ∈ C^∞(ℝ^P), 0 ≤ χ ≤ 1, with tsupport χ ⊆ V and χ = 1 on an open set W₀ ⊇ K. Put f̂ := χ·f (0 off tsupport χ). Then f̂ is C¹ on ℝ^P (C¹ on O, identically 0 near each point of the open set ℝ^P ∖ tsupport χ, and these two open sets cover ℝ^P); its derivative is continuous with compact support, so f̂ is L̂-Lipschitz on ℝ^P for some L̂ (mean value inequality). On W₀, f̂ = f; hence f̂(x) = f(x) and Df̂(x) = Df(x) for x ∈ K. So Q(ω) = ∫_M θξ(ω(f̂(x))∘Df̂(x)) dHⁿ, f̂(K) = f(K) ⊆ U, and Λ := max(1, sup_{x∈K}‖Df(x)‖) < ∞ bounds ‖Df̂‖ on K. From now on we write f for f̂.
1. Orientation and Jacobian.
 (a) Fix a Borel map ξ̃ : ℝ^P → Λ_n with ξ̃ = ξ Hⁿ-a.e. on M_R (ξ is a.e.-strongly measurable for Hⁿ⌞M_R and Λ_n is finite-dimensional).
 (b) Call x ∈ M oriented if M has an approximate tangent space T_xM at x (unique, SimonGMT HasApproximateTangentSpaceAt.unique) and ξ̃(x) is a unit orientation of T_xM. Hⁿ-a.e. x ∈ M is oriented: by R.orients, for Hⁿ-a.e. x ∈ M_R there is Q_x with HasApproximateTangentSpaceAt n M_R x Q_x and IsUnitOrientationOf (ξ x) Q_x, and ξ(x) = ξ̃(x); by (TL) with (U, A, B) := (U, M, M_R) (M ⊆ M_R ⊆ U Borel; Hⁿ(M_R ∩ K₀) < ∞ for compact K₀ ⊆ U since θ ≥ 1), for Hⁿ-a.e. x ∈ M the sets M and M_R have the same approximate tangent spaces at x.
 (c) J(x) := |(Df(x))_#ξ̃(x)| is Borel (Df continuous, ξ̃ Borel, (L, ζ) ↦ L_#ζ continuous). At an oriented x ∈ M, by (L4): J(x) ≤ ‖Df(x)‖ⁿ ≤ Λⁿ; J(x) > 0 iff Df(x) is injective on T_xM; and J(x) = 0 implies (Df(x))_#ξ̃(x) = 0. Put M₊ := {x ∈ M : J(x) > 0}, a Borel set.
Lemma T (approximate tangent planes along bi-Lipschitz pieces; Simon Ch. 3, 1.5–1.6 for a Lipschitz parametrization). Let g : ℝⁿ → ℝ^P be Lipschitz, D ⊆ ℝⁿ Borel, c > 0 with |g(a) − g(a')| ≥ c|a − a'| for a, a' ∈ D, and g differentiable at every a ∈ D with Dg(a) injective. Let Y ⊆ ℝ^P be Borel with g(D) ⊆ Y and Hⁿ(Y ∩ K₀) < ∞ for every compact K₀. Then for Lⁿ-a.e. a ∈ D, Y has approximate tangent space Π_a := range Dg(a) at g(a).
 Proof. (i) g is injective on D, so g(D) is Borel (Lusin–Souslin, Mathlib MeasurableSet.image_of_continuousOn_injOn) and Hⁿ(g(D) ∩ K₀) < ∞. (ii) Lⁿ-a.e. a ∈ D is a Lebesgue density point of D and a Lebesgue point of the bounded Borel function 1_D·J_g (Lebesgue differentiation theorem). Fix such an a, put x := g(a), and let f₀ ∈ C_c(ℝ^P) with spt f₀ ⊆ B_ρ(0). For λ > 0, with η_{x,λ}(z) := λ⁻¹(z − x), the scaling of Hⁿ under similarities, the area formula for the injective Lipschitz map g on D (SimonGMT weighted_area_formula_lipschitz_injOn) and the substitution b = a + λu give
  ∫_{η_{x,λ}(g(D))} f₀ dHⁿ = λ⁻ⁿ∫_{g(D)} f₀(λ⁻¹(z − x)) dHⁿ(z) = ∫_{(D−a)/λ} f₀(λ⁻¹(g(a + λu) − g(a)))·J_g(a + λu) du.
 If a + λu ∈ D and the integrand is non-zero, then cλ|u| ≤ |g(a + λu) − g(a)| < λρ, so |u| < ρ/c. As λ ↓ 0, λ⁻¹(g(a + λu) − g(a)) → Dg(a)u uniformly for |u| ≤ ρ/c (differentiability at a), so the f₀-factor converges uniformly there (f₀ is uniformly continuous), while ∫_{B_{ρ/c}(0)} |1_{(D−a)/λ}(u)J_g(a + λu) − J_g(a)| du → 0 (Lebesgue point). Hence the integral tends to J_g(a)∫_{B_{ρ/c}(0)} f₀(Dg(a)u) du = J_g(a)∫_{ℝⁿ} f₀(Dg(a)u) du = ∫_{Π_a} f₀ dHⁿ (area formula for the injective linear map Dg(a), whose Jacobian is J_g(a)); here f₀(Dg(a)u) = 0 for |u| ≥ ρ/c because |Dg(a)u| ≥ c|u|, which follows from the lower bound at the density point a. Thus g(D) has approximate tangent space Π_a at g(a) for Lⁿ-a.e. a ∈ D. (iii) By (TL) with (U, A, B) := (ℝ^P, g(D), Y), for Hⁿ-a.e. z ∈ g(D) the sets g(D) and Y have the same approximate tangent spaces at z. The inverse of g on g(D) is (1/c)-Lipschitz, so the set of a ∈ D with g(a) in this Hⁿ-null exceptional set is Lⁿ-null. Combining with (ii) proves the lemma. ∎
Partition step (P). Let g : ℝⁿ → ℝ^P and let G ⊆ ℝⁿ be a Borel set such that g is differentiable at every a ∈ G with Dg(a) injective. For injective linear A put m(A) := min_{|h|=1}|Ah| > 0 (n ≥ 1, so the unit sphere is compact and non-empty) and r(A) := m(A)/2; put r(A) := 1 for non-injective A. Mathlib exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (applied with f' := Dg, which is a derivative within G at points of G) gives pairwise disjoint Borel sets t_l (l ∈ ℕ) with G ⊆ ⋃_l t_l and linear maps A_l with |g(a) − g(a') − A_l(a − a')| ≤ r(A_l)|a − a'| for a, a' ∈ G ∩ t_l, where A_l = Dg(y_l) for some y_l ∈ G when G ≠ ∅ (so A_l is injective). Hence |g(a) − g(a')| ≥ |A_l(a − a')| − (m(A_l)/2)|a − a'| ≥ (m(A_l)/2)|a − a'| on G ∩ t_l: g is injective on G ∩ t_l with a (2/m(A_l))-Lipschitz inverse.
2. Injective pieces.
 (a) Lipschitz parametrizations of M. By CountablyRectifiable n M there are an Hⁿ-null M₀ and Lipschitz F'_j : ℝⁿ → ℝ^P (j ∈ ℕ) with M ⊆ M₀ ∪ ⋃_j F'_j(ℝⁿ). Let G'_j := {a : F'_j differentiable at a, DF'_j(a) injective} (SimonGMT areaRegularSet F'_j, Borel by measurableSet_areaRegularSet); Hⁿ(F'_j(ℝⁿ ∖ G'_j)) = 0 (SimonGMT area_image_compl_regularSet_eq_zero). Apply (P) to F'_j on G'_j and enumerate the resulting pieces over all j as (F_i, B_i)_{i∈ℕ}, intersecting with F_i⁻¹(M): F_i is one of the Lipschitz F'_j, B_i ⊆ G'_j ∩ F_i⁻¹(M) is Borel, F_i is differentiable with injective DF_i(a) at every a ∈ B_i, |F_i(a) − F_i(a')| ≥ m_i|a − a'| on B_i for some m_i > 0, F_i(B_i) ⊆ M, and M ∖ ⋃_i F_i(B_i) ⊆ M₀ ∪ ⋃_j F'_j(ℝⁿ ∖ G'_j) is Hⁿ-null.
 (b) By Lemma T with (g, D, Y) := (F_i, B_i, M): for Lⁿ-a.e. a ∈ B_i, T_{F_i(a)}M = range DF_i(a).
 (c) g_i := f∘F_i is Lipschitz; for a ∈ B_i it is differentiable at a with Dg_i(a) = Df(F_i(a))∘DF_i(a) (chain rule). G_i := {a ∈ B_i : Dg_i(a) injective} is Borel (a ↦ Dg_i(a) is Borel, Mathlib measurable_fderiv, and injectivity means det(⟨Dg_i(a)e_p, Dg_i(a)e_q⟩) ≠ 0).
 (d) Apply (P) to g_i on G_i: Borel pieces D_{i,l} ⊆ G_i (disjoint in l, covering G_i) on which g_i is injective with Lipschitz inverse.
 (e) Enumerate the pairs (i, l) as k ∈ ℕ and write F_k, m_k for the parametrization F_i and constant m_i of the pair, and g_k := f∘F_k. Put D'_k := D_{i,l} ∩ F_k⁻¹(M₊) (Borel), A'_k := F_k(D'_k) ⊆ M₊ (Borel by Lusin–Souslin, F_k being continuous and injective on B_i ⊇ D'_k), and disjointify: A_k := A'_k ∖ ⋃_{k'<k} A'_{k'} (Borel, pairwise disjoint, ⋃_k A_k = ⋃_k A'_k), D''_k := D'_k ∩ F_k⁻¹(A_k) (Borel), so A_k = F_k(D''_k). f is injective on A_k: f(F_k(a)) = f(F_k(a')) with a, a' ∈ D''_k means g_k(a) = g_k(a'), so a = a'. Moreover g_k has a Lipschitz inverse on D''_k, and Σ_k := f(A_k) = g_k(D''_k) is Borel (Lusin–Souslin) with Hⁿ(Σ_k) ≤ L̂ⁿHⁿ(A_k) < ∞.
 (f) Hⁿ(M₊ ∖ ⋃_k A_k) = 0. Indeed, let x ∈ M₊ be oriented with x = F_i(a), a ∈ B_i and T_xM = range DF_i(a). Then J(x) > 0, so Df(x) is injective on T_xM = range DF_i(a) (1(c)), hence Dg_i(a) = Df(x)DF_i(a) is injective, a ∈ G_i ⊆ ⋃_l D_{i,l}, and x ∈ A'_k ⊆ ⋃_k A_k for some k. The remaining points of M₊ lie in M ∖ ⋃_i F_i(B_i), in the non-oriented null set, or in F_i(N_i) with N_i ⊆ B_i Lⁿ-null from (b); F_i(N_i) is Hⁿ-null because F_i is Lipschitz (Mathlib LipschitzWith.hausdorffMeasure_image_le).
 (g) By Lemma T with (g, D, Y) := (g_k, D''_k, Σ_k): for Lⁿ-a.e. a ∈ D''_k, Σ_k has approximate tangent space range Dg_k(a) = Df(F_k(a))(range DF_k(a)) at f(F_k(a)).
3. Compact pieces and the image set.
 (a) Hⁿ⌞M is a finite Borel measure on ℝ^P, hence inner regular. For each k choose pairwise disjoint compact K_{k,1}, K_{k,2}, … ⊆ A_k with Hⁿ(A_k ∖ ⋃_l K_{k,l}) = 0. Enumerate all K_{k,l} as K₁, K₂, … with K_m ⊆ A_{k(m)}; they are pairwise disjoint. M' := ⋃_m K_m ⊆ M₊ is Borel and Hⁿ(M₊ ∖ M') = 0.
 (b) E := f(M') = ⋃_m f(K_m) is σ-compact, hence Borel; E ⊆ f(K) ⊆ U and Hⁿ(E) ≤ L̂ⁿHⁿ(M) < ∞. As f|K_m is a continuous injection of a compact set, x_m := (f|K_m)⁻¹ : f(K_m) → K_m is continuous.
 (c) Countable rectifiability: by 2(a), E ⊆ f(M) ⊆ f(M₀) ∪ ⋃_j (f∘F'_j)(ℝⁿ), where Hⁿ(f(M₀)) ≤ L̂ⁿ·0 = 0 and every f∘F'_j is Lipschitz. Hence every subset of E is countably n-rectifiable.
 (d) Good points. Call x ∈ M' good if x is oriented and, with m such that x ∈ K_m, k := k(m) and a ∈ D''_k with F_k(a) = x: T_xM = range DF_k(a) and Σ_k has approximate tangent space Df(x)(T_xM) at f(x). By 1(b), 2(b), 2(g), and since F_k maps Lⁿ-null sets to Hⁿ-null sets, Hⁿ(M' ∖ good) = 0. Conversely, the set of a ∈ D''_k with F_k(a) ∈ M' ∖ good is Lⁿ-null (F_k has a (1/m_k)-Lipschitz inverse on F_k(D''_k)).
4. Area formula. Fix m, k := k(m), D_m := D''_k ∩ F_k⁻¹(K_m) (Borel), so F_k(D_m) = K_m and g_k(D_m) = f(K_m). For a ∈ D_m with x := F_k(a) good: σ := (DF_k(a))_#e/J_{DF_k(a)} is a unit orientation of range DF_k(a) = T_xM (L4), so σ = ±ξ̃(x) (L3), and J_{g_k}(a) = |(Df(x)DF_k(a))_#e| = |(Df(x))_#((DF_k(a))_#e)| = J_{F_k}(a)·|(Df(x))_#σ| = J_{F_k}(a)·J(x), using (L∘A)_#e = L_#(A_#e) (both send α to α(LAe₁, …, LAeₙ)) and (L4). For Borel h ≥ 0, the area formula for the injective Lipschitz maps F_k and g_k on D_m (SimonGMT weighted_area_formula_lipschitz_injOn) gives
  ∫_{K_m} h·J dHⁿ = ∫_{D_m} J_{F_k}(a)·h(F_k(a))·J(F_k(a)) da = ∫_{D_m} J_{g_k}(a)·h(F_k(a)) da = ∫_{f(K_m)} h(x_m(w)) dHⁿ(w),
 using x_m(g_k(a)) = F_k(a) and 3(d) for the a.e. identity of Jacobians. Summing over m (monotone convergence; the K_m are disjoint and f is injective on each):
 (A) ∫_{M'} h·J dHⁿ = ∫ Σ_m 1_{f(K_m)}(w)·h(x_m(w)) dHⁿ(w) = ∫ Σ_{x∈f⁻¹(w)∩M'} h(x) dHⁿ(w).
 Each point of f⁻¹(w) ∩ M' lies in exactly one K_m and equals x_m(w), which gives the last equality; the integrand is Borel. With h := θ: ∫ Σ_{x∈f⁻¹(w)∩M'} θ(x) dHⁿ(w) = ∫_{M'} θJ dHⁿ ≤ Λⁿ∫_M θ dHⁿ < ∞. So the Borel set E₁ := {w : Σ_{x∈f⁻¹(w)∩M'} θ(x) < ∞} has Hⁿ(ℝ^P ∖ E₁) = 0, and for w ∈ E₁ the fibre f⁻¹(w) ∩ M' is finite (θ ≥ 1).
5. The image integral.
 (a) ζ̂(x) := J(x)⁻¹·(Df(x))_#ξ̃(x) for x ∈ M' and ζ̂(x) := 0 otherwise. ζ̂ is Borel, |ζ̂| = 1 on M', and at good x, ζ̂(x) is a unit orientation of Df(x)(T_xM) (L4).
 (b) V(w) := Σ_m 1_{f(K_m)}(w)·θ(x_m(w))·ζ̂(x_m(w)) = Σ_{x∈f⁻¹(w)∩M'} θ(x)ζ̂(x) for w ∈ E₁, and V(w) := 0 for w ∉ E₁. The series converges absolutely on E₁ because |ζ̂(x)(dx^I)| ≤ |ζ̂(x)| = 1; each coordinate V(·)(dx^I) is Borel, so V is Borel.
 (c) Let ω ∈ 𝒟ⁿ(U). For Hⁿ-a.e. x ∈ M (oriented, ξ(x) = ξ̃(x)): θ(x)ξ(x)(ω(f(x))∘Df(x)) = θ(x)((Df(x))_#ξ̃(x))(ω(f(x))), which is 0 for x ∈ M ∖ M₊ (1(c)) and equals θ(x)J(x)ζ̂(x)(ω(f(x))) for x ∈ M'. As Hⁿ(M₊ ∖ M') = 0: Q(ω) = ∫_{M'} θ(x)J(x)ζ̂(x)(ω(f(x))) dHⁿ(x). Apply (A) to the positive and negative parts of h(x) := θ(x)ζ̂(x)(ω(f(x))); both have finite integral against J, since |h| ≤ θ·sup_z|ω(z)|_E (L2) and ∫_{M'} θJ < ∞. On the fibre over w we have f(x) = w, so
 (B) Q(ω) = ∫ V(w)(ω(w)) dHⁿ(w).
6. Tangent planes of the image. For each k apply (TL) with U := ℝ^P to (A, B) := (E ∩ Σ_k, Σ_k) and to (A, B) := (E ∩ Σ_k, E): these are Borel, and Hⁿ(Σ_k), Hⁿ(E) < ∞. So for Hⁿ-a.e. w ∈ E ∩ Σ_k, the sets E, E ∩ Σ_k and Σ_k have the same approximate tangent spaces at w. Let Bad_E be the union of these countably many null exceptional sets, of ℝ^P ∖ E₁, and of f(M' ∖ good), which is Hⁿ-null as f is Lipschitz. For w ∈ E ∖ Bad_E, every x ∈ f⁻¹(w) ∩ M' is good; if x ∈ K_m and k := k(m), then w ∈ E ∩ Σ_k, Σ_k has approximate tangent space Df(x)(T_xM) at w (good), and hence so does E. By uniqueness, Π_w := T_wE exists and Df(x)(T_xM) = Π_w for every x ∈ f⁻¹(w) ∩ M'.
7. Integer multiplicity in the fibres (Simon 3.7–3.8). Let w ∈ E ∖ Bad_E and fix a unit orientation ζ_w of Π_w. For x ∈ f⁻¹(w) ∩ M', ζ̂(x) is a unit orientation of Df(x)(T_xM) = Π_w (5(a), 6), so ζ̂(x) = ε(x)ζ_w with ε(x) ∈ {1, −1} (L3). Hence V(w) = m(w)ζ_w with m(w) := Σ_{x∈f⁻¹(w)∩M'} ε(x)θ(x) ∈ ℤ (a finite sum, w ∈ E₁) and |m(w)| ≤ Σ_{x∈f⁻¹(w)∩M'} θ(x).
8. Borel versions; restriction to positive multiplicity. ν(w) := |V(w)| is Borel and ν = |m| on E ∖ Bad_E (7 and (L2)). Define the Borel function N'(w) := ⌊ν(w) + 1/2⌋ ∈ ℕ (so N' = |m| on E ∖ Bad_E), the Borel map ζ'(w) := V(w)/ν(w) if ν(w) > 0 and ζ'(w) := 0 otherwise, and the Borel carrier C := {w ∈ E : N'(w) ≥ 1}. For w ∈ C ∖ Bad_E: m(w) ≠ 0, ζ'(w) = sgn(m(w))ζ_w is a unit orientation of Π_w, and N'(w)ζ'(w) = m(w)ζ_w = V(w). For w ∈ E ∖ (C ∪ Bad_E): m(w) = 0, so V(w) = 0. For w ∉ E, V(w) = 0 (empty fibre). Hence V = 1_C·N'·ζ' Hⁿ-a.e. This removes from the carrier the points where Simon's multiplicity |m| vanishes.
9. R' := (C, N', ζ') is an IMRep in U representing Q.
 - measurableSet_carrier: C is Borel.
 - carrier_subset: C ⊆ E ⊆ f(K) ⊆ U.
 - rectifiable: C ⊆ E is countably n-rectifiable by 3(c).
 - measurable_mult: N' is Borel. mult_pos: N' ≥ 1 on C by definition of C.
 - locallyIntegrable_mult: for compact K₀ ⊆ U, ∫_{C∩K₀} N' dHⁿ ≤ ∫_{E∖Bad_E} |m| dHⁿ ≤ ∫ Σ_{x∈f⁻¹(w)∩M'} θ(x) dHⁿ(w) < ∞ (7 and 4).
 - aestronglyMeasurable_orient: ζ' is Borel with values in the finite-dimensional Λ_n, hence strongly measurable.
 - orients: (TL) with U := ℝ^P and (A, B) := (C, E) (C ⊆ E Borel, Hⁿ(E) < ∞) shows that for Hⁿ-a.e. w ∈ C, C and E have the same approximate tangent spaces at w. For such w ∉ Bad_E, T_wE = Π_w exists, so HasApproximateTangentSpaceAt n C w Π_w, and ζ'(w) is a unit orientation of Π_w (8). So the orientation field holds Hⁿ⌞C-a.e.
 - Represents: for ω ∈ 𝒟ⁿ(U), w ↦ N'(w)ζ'(w)(ω(w)) is integrable on C (bounded by N'·sup|ω|_E via (L2), and N' is integrable on C ∩ tsupport ω). By 8 and (B): R'.action ω = ∫_C N'(w)ζ'(w)(ω(w)) dHⁿ(w) = ∫ V(w)(ω(w)) dHⁿ(w) = Q(ω).
 Hence Q is integer multiplicity (IsIntegerMultiplicity Q). (If n > P then Hⁿ = 0 on ℝ^P, every set above is null, C = ∅, and the same construction gives Q = 0 = τ(∅, 0, 0).) ∎

## Key steps

1. Reduce to M = M_R ∩ K and, by a cutoff, to a globally C¹ Lipschitz f; fix a Borel orientation ξ̃, the Jacobian J = |Df_#ξ̃| ≤ Λⁿ and M₊ = {J > 0}; (TL) shows a.e. point of M is oriented.
2. Bi-Lipschitz pieces of M (built from Lipschitz parametrizations, SimonGMT areaRegularSet and Mathlib's partition lemma) and the partition lemma for g = f∘F_i give countably many disjoint Borel pieces A_k covering M₊ a.e. with f injective on each; Lemma T gives the tangent planes of M and of f(A_k) along the pieces.
3. On disjoint compact K_m ⊆ A_k the area formula and J_{f∘F} = J_F·J give ∫_{M'}hJ = ∫ Σ_{x∈f⁻¹(w)∩M'} h(x) dHⁿ(w); hence Q(ω) = ∫ V(w)(ω(w)) dHⁿ with V(w) = Σ_{fibre} θζ̂.
4. (TL) identifies T_wE with Df(x)(T_xM) for every x in the fibre, so V(w) = m(w)ζ_w with m(w) ∈ ℤ (Simon 3.7–3.8).
5. Borel versions N' = ⌊|V| + 1/2⌋, ζ' = V/|V| on C = {w ∈ E : N'(w) ≥ 1} (positive multiplicity, correcting Simon 3.9) form an IMRep in U; (TL) on C ⊆ E gives the orientation field and (B) gives Q = τ(C, N', ζ').

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD (b4d606d, 25730c7c, 2b36630)`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `grep -n '^def|^structure|^abbrev|^theorem' SimonGMT Chapter06/{Currents,Forms,Mass,CurrentLocalEquality}.lean; sed -n 55,150p Chapter06/Forms.lean`
- `grep -n 'def CountablyRectifiable|def HasApproximateTangentSpaceAt|def blowUpMap' Chapter03/Rectifiable.lean; sed -n 1,60p Chapter03/SubmanifoldCover.lean; grep -n theorem Chapter03/DisjointCover.lean`
- `grep -n '^theorem|^def' Chapter02/{AreaLipschitz,AreaNoninjective,AreaFormula}.lean; grep -n 'def areaJacobianAt' Chapter02/Area.lean`
- `grep -rn 'pullback' mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean (extDeriv_pullback, extDerivWithin_pullback)`
- `grep -rn 'theorem exists_partition_approximatesLinearOn_of_hasFDerivWithinAt' mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `grep -rn 'measure_compl_support' mathlib/Mathlib/MeasureTheory/Measure/Support.lean; grep -rn 'LipschitzOnWith.extend_finite_dimension' mathlib/Mathlib`
- `grep -rln -i hadamard mathlib/Mathlib; grep -rn 'det_le_prod|normDet' mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean (no Gram Hadamard inequality; LinearMap.normDet)`
- `python3 dag.json scans: accepted declarations with lean_statement containing compContinuousLinearMap/IsUnitOrientationOf/indicator/orient; status and candidate_commit of the 6 reused nodes; collision scan of the 6 new dor_lmb_pc_* names (0 hits, 719 nodes)`
- `git grep -q dor_lmb_pc_ <sha> -- GMT/Ch07/Submission.lean over all 1347 ref objects (0 hits)`
- `sed -n runtime.py _existing_lean_name_problem and child activation (reuse of accepted nodes requires identical frozen type)`
- `lake env lean /tmp/pc-decomp/Types2.lean (12 child types in comparator scope); lake env lean /tmp/pc-decomp/Assembly.lean (#print axioms pc_assembly); lake env lean /tmp/pc-decomp/Checks.lean`
- `sed -n 200,260p book/chapter-07.txt; sed -n 400,445p and 755,870p book/chapter-06.txt`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-projected-comparison-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1/decomposition-audit-v6.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-bilipschi-4344c8c0d8/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/DisjointCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaNoninjective.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/pc-decomp/Types2.lean`
- `/tmp/pc-decomp/Assembly.lean`

Snapshot: project b4d606d, mathlib 25730c7c, SimonGMT 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

Reusable facts found:
- SimonGMT Chapter06: GeometricCurrentOn, TestFormOnConverges, boundary, massOn and massAdmissibleOn, support as U minus the zero region, and exteriorDerivativeOn_pullbackFormWithin. No C¹ or Lipschitz push-forward exists; only the affine push-forward does.
- SimonGMT Chapter03: CountablyRectifiable (global Lipschitz maps), HasApproximateTangentSpaceAt and .unique. SubmanifoldCover.lean states that the converse of Lemma 1.2 (C¹-submanifold cover of rectifiable sets) is not formalized.
- SimonGMT Chapter02: areaRegularSet, measurableSet_areaRegularSet, area_image_compl_regularSet_eq_zero, weighted_area_formula_lipschitz_injOn, and areaJacobianAt = normDet.
- Mathlib: extDeriv_pullback (naturality of d), exists_partition_approximatesLinearOn_of_hasFDerivWithinAt, Measure.measure_compl_support, Convex.norm_image_sub_le_of_norm_fderiv_le, LipschitzOnWith.extend_finite_dimension and LinearMap.normDet. Mathlib has no Hadamard inequality for Gram determinants; the accepted dpf_exists_orthonormal_frame_det_gram supplies it.

Accepted DAG declarations reused with identical frozen types:
- approxTangent_le_submanifold_tangentSpace
- covectorEuclideanNorm_gram_bounds
- dpf_exists_orthonormal_frame_det_gram
- rsdic_exists_imrep_int_combination
- rsdic_imrep_action_int_combination
- imrep_weighted_orient_indicator_ae_eq
Further accepted lemmas are cited as optional reuse targets for later decompositions: dpf_rectifiable_bilipschitz_pieces, dpf_pfc_*, dpf_smooth_approx_compact_perturbation and dpf_pb_*.

Lean checks:
- The 12 child types elaborate in the comparator scope.
- The conditional assembly of the exact parent type from the child types plus the resolved siblings dor_lmb_approx_tangent_locality and dor_lmb_int_combination_imrep compiles with axioms propext, Classical.choice and Quot.sound only.
- No new name collides in dag.json (719 nodes) or in any git ref.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
