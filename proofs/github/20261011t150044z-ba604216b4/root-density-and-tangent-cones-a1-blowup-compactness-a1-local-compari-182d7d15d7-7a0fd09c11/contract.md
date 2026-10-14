<!-- theorem-id: gmt-ch07/root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.pushforward-a1.pf_integer-a1 -->

## Theorem `Submission.dtc_bc_lc_pf_pushforward_isIntegerMultiplicity`

Assume (TL): for all P', n' ∈ ℕ, every open U' ⊆ ℝ^{P'} and all Borel sets A ⊆ B ⊆ U' with Hⁿ'(B ∩ C) < ∞ for every compact C ⊆ U', for Hⁿ'-a.e. x ∈ A and every linear subspace Q, B has approximate tangent space Q at x (HasApproximateTangentSpaceAt n' B x Q) if and only if A does. Let P, n ∈ ℕ with n ≥ 1, U ⊆ ℝ^P open, R = (M, θ, ξ) an integer multiplicity triple in U (IMRep U n), K ⊆ U compact with Hⁿ(M ∖ K) = 0 (Hⁿ = μHE[n]), O ⊆ ℝ^P open with K ⊆ O, f : ℝ^P → ℝ^P of class C¹ on O with f(K) ⊆ U, and Q ∈ 𝒟_n(U) with Q(ω) = ∫_M θ(x)·ξ(x)(ω(f(x))∘Df(x)) dHⁿ(x) for every ω ∈ 𝒟ⁿ(U) (Df(x) = fderiv ℝ f x, ω(f(x))∘Df(x) := (ω (f x)).compContinuousLinearMap (fderiv ℝ f x)). Then Q is integer multiplicity: Q = τ(N', θ', ξ') for some integer multiplicity triple in U (IsIntegerMultiplicity Q).

Node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.pushforward-a1.pf_integer-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5388

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4140, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4147, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5835, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5591, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7119, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7121, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7122, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7126, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7127, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7132, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7137, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7143

## Lean problem

Declaration: `Submission.dtc_bc_lc_pf_pushforward_isIntegerMultiplicity`

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

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.pushforward-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.pushforward-a1.pf_integer-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 6 of the parent proof (Simon Ch. 6, 3.3–3.9, chapter-06.txt lines 770–860, with the area formula of Ch. 3, 2.4–2.6, chapter-03.txt lines 360–410), generalized from the domain ℝ^P and K = spt Y to an open U and a compact K carrying Hⁿ⌞M. The parent's sketch 6(a)–(g) (tangential differential, M₊ = {J^M f > 0}, the area formula 3.6, tangent planes of the image 3.7, the integer N(y) of 3.8, the representation 3.9) is carried out with these precisions: M is parametrized by bi-Lipschitz pieces of Lipschitz maps from ℝⁿ, so that d^M f_x is Df(x) restricted to DG(u)(ℝⁿ) (step 5); the approximate tangent spaces of images come from Lemma T (step 3) and the hypothesis (TL) (the parent's "for Hⁿ-a.e. y the approximate tangent space exists"); and Simon's N(y)η(y) with N ≥ 0 is the signed integer k(y) times one orientation η(y), restricted to {k ≠ 0} (steps 9–11). The frozen type is byte-identical to those of dimred_mbl_pf_pushforward_isIntegerMultiplicity and dor_lmb_pc_pushforward_isIntegerMultiplicity in other branches.

Notation. Hⁿ := μHE[n]; on ℝⁿ = Euclid n it is Lebesgue measure Lⁿ (du). M = R.carrier, θ = R.mult, ξ = R.orient. e₁, …, eₙ is the standard basis of ℝⁿ. For an n-covector β, |β|_E := covectorEuclideanNorm β, ‖β‖ is its operator norm, and ⟨β, ζ⟩ := ζ(β) for an n-vector ζ. For a linear A : ℝⁿ → ℝ^P, A_#e is the n-vector β ↦ β(Ae₁, …, Aeₙ) and J_A := det(⟨Ae_i, Ae_j⟩)_{i,j}^{1/2} ≥ 0 (the area Jacobian, equal to LinearMap.normDet of A and to SimonGMT areaJacobianAt at differentiability points). For G : ℝⁿ → ℝ^P differentiable at u, J_G(u) := J_{DG(u)}. For orthonormal σ = (σ₁, …, σₙ), σ_# is the n-vector β ↦ β(σ₁, …, σₙ), a unit orientation of span σ. n ≥ 1 by hypothesis.

Algebra.
(A0) For an n-covector β and v₁, …, vₙ ∈ ℝ^P: |β(v)| ≤ |β|_E·det(⟨v_i, v_j⟩)^{1/2} ≤ |β|_E·Π_j|v_j|; for orthonormal σ also |β(σ)| ≤ |β|_E and |β(σ)| ≤ ‖β‖. Proof: expanding v_j in the standard basis of ℝ^P, multilinearity and the alternating property give β(v) = Σ_I β(e_I)·det(V_I) (I increasing, V_I the n×n minor of the matrix of v on the rows I); Cauchy–Schwarz and the Cauchy–Binet formula Σ_I det(V_I)² = det(VᵀV) = det(⟨v_i, v_j⟩) give the first inequality; Hadamard's inequality det(⟨v_i, v_j⟩) ≤ Π_j|v_j|² (zero for dependent v; for independent v, Gram–Schmidt writes VᵀV = TᵀT with T upper triangular and T_jj ≤ |v_j|) gives the second; for orthonormal σ the Gram determinant is 1, and |β(σ)| ≤ ‖β‖·Π_j|σ_j| = ‖β‖ (ContinuousAlternatingMap.le_opNorm).
(A1) Two unit orientations of the same n-dimensional subspace differ by a sign, and −ζ is a unit orientation of Q whenever ζ is. Proof: if τ, τ' are orthonormal bases of Q, then τ'_i = Σ_j O_ij τ_j with O orthogonal, and multilinear alternating expansion gives β(τ') = det(O)·β(τ) with det O = ±1; the definition of IsUnitOrientationOf allows either sign.
(A2) Let A : ℝⁿ → ℝ^P be linear. If A is injective, let σ be the Gram–Schmidt orthonormalization of Ae₁, …, Aeₙ: Ae_j = Σ_{i≤j} T_ij σ_i with T upper triangular and T_jj > 0. Then (⟨Ae_i, Ae_j⟩) = TᵀT, so J_A = det T > 0, and multilinear alternating expansion gives β(Ae₁, …, Aeₙ) = det(T)·β(σ) for every β, i.e. A_#e = J_A·σ_#, where σ_# is a unit orientation of span σ = A(ℝⁿ), an n-dimensional subspace. If A is not injective, Ae₁, …, Aeₙ are linearly dependent, so A_#e = 0 (β alternating) and J_A = 0 (singular Gram matrix). In both cases |⟨β, A_#e⟩| ≤ J_A·|β|_E (A0), and J_A ≤ Π_j|Ae_j| ≤ ‖A‖ⁿ.
(A3) For linear A : ℝⁿ → ℝ^P and L : ℝ^P → ℝ^P: (LA)_#e is the n-vector β ↦ (β∘L)(Ae₁, …, Aeₙ), and J_{LA} ≤ ‖L‖ⁿ·J_A. Proof of the inequality: if A is not injective, neither is LA, and both sides vanish. Otherwise, with σ and T from (A2) and the isometry V : ℝⁿ → ℝ^P, Ve_i := σ_i, we have A = V∘T, so (⟨LAe_i, LAe_j⟩) = Tᵀ·(⟨Lσ_i, Lσ_j⟩)·T, J_{LA} = det(T)·J_{LV} = J_A·J_{LV}, and J_{LV} ≤ Π_i|Lσ_i| ≤ ‖L‖ⁿ by (A2).

1. Reductions.
(a) M₁ := M ∩ K is Borel, Hⁿ(M ∖ M₁) = 0 by hypothesis, and Hⁿ(M₁) ≤ ∫⁻_{M∩K} θ dHⁿ < ∞ (θ ≥ 1 on M; R.locallyIntegrable_mult for the compact set K ⊆ U).
(b) Cut-off of f. Choose δ > 0 with cthickening(2δ, K) ⊆ O (IsCompact.exists_cthickening_subset_open) and a C^∞ function χ : ℝ^P → [0, 1] with χ = 1 on W₀ := thickening(δ, K) ⊇ K and tsupport χ ⊆ cthickening(2δ, K), a compact subset of O (smooth Urysohn lemma, exists_contDiff_support_eq_eq_one_iff). Put f̂(x) := x + χ(x)·(f(x) − x). Then f̂ is C¹ on ℝ^P (at points of O because f is C¹ on the open set O; near points outside tsupport χ because f̂ = id there; these two open sets cover ℝ^P), f̂ = id off the compact set tsupport χ, and f̂ = f on the open set W₀, so f̂(x) = f(x) and Df̂(x) = Df(x) for x ∈ K (Filter.EventuallyEq.fderiv_eq). Df̂ is continuous and equals the identity off a compact set, so Λ := max(1, sup_x ‖Df̂(x)‖) < ∞, and f̂ is Λ-Lipschitz on ℝ^P (mean value inequality on the convex set ℝ^P). Since Hⁿ(M ∖ K) = 0, for every ω ∈ 𝒟ⁿ(U): Q(ω) = ∫_{M₁} F_ω dHⁿ, where F_ω(x) := θ(x)·ξ(x)(ω(f̂(x))∘Df̂(x)) (the integrands agree Hⁿ⌞M-a.e.). Also f̂(M₁) ⊆ f̂(K) = f(K) ⊆ U.
(c) Integrability. By R.orients and (A0), |ξ(x)(β)| ≤ ‖β‖ for every β, for Hⁿ-a.e. x ∈ M; with ‖β∘A‖ ≤ ‖β‖·‖A‖ⁿ (ContinuousAlternatingMap.norm_compContinuousLinearMap_le), |F_ω| ≤ ‖ω‖_∞Λⁿθ Hⁿ-a.e. on M₁, where ‖ω‖_∞ := sup_z ‖ω(z)‖ < ∞. F_ω is a.e. strongly measurable for Hⁿ⌞M (θ measurable, ξ a.e. strongly measurable, x ↦ ω(f̂(x))∘Df̂(x) continuous), hence Hⁿ⌞M₁-integrable. Fix a Borel map ξ̃ with ξ̃ = ξ Hⁿ-a.e. on M (a.e. strong measurability).
(d) Good points. By (TL) with (U, A, B) := (U, M₁, M) (Borel sets, M₁ ⊆ M ⊆ U, Hⁿ(M ∩ C) ≤ ∫⁻_{M∩C} θ dHⁿ < ∞ for compact C ⊆ U), for Hⁿ-a.e. x ∈ M₁ the sets M and M₁ have the same approximate tangent spaces at x. With R.orients: for Hⁿ-a.e. x ∈ M₁ there is a subspace T_x with HasApproximateTangentSpaceAt n M₁ x T_x and IsUnitOrientationOf (ξ(x)) T_x, and ξ̃(x) = ξ(x). Such x are called good. Approximate tangent spaces are unique when they exist (SimonGMT HasApproximateTangentSpaceAt.unique).

2. Parametrization of M₁ (parent 6(a)–(b); the comparator-accepted DAG declaration dpf_rectifiable_bilipschitz_pieces states exactly this conclusion for Borel countably n-rectifiable sets, and a decomposition of this node may reuse it). There are Lipschitz maps G_i : ℝⁿ → ℝ^P, Borel sets A_i ⊆ ℝⁿ and constants κ_i > 0 (i ∈ ℕ) such that κ_i|u − v| ≤ |G_i(u) − G_i(v)| for u, v ∈ A_i, G_i is differentiable at every u ∈ A_i with DG_i(u) injective, the sets G_i(A_i) are Borel, contained in M₁ and pairwise disjoint, and Hⁿ(M₁ ∖ ⋃_i G_i(A_i)) = 0. Proof.
 (i) M₁ ⊆ M is countably n-rectifiable (R.rectifiable, CountablyRectifiable.mono): M₁ ⊆ M₀ ∪ ⋃_j F_j(ℝⁿ) with Hⁿ(M₀) = 0 and F_j : ℝⁿ → ℝ^P Lipschitz.
 (ii) By Rademacher's theorem (LipschitzWith.ae_differentiableAt), the set D_j of differentiability points of F_j is Borel with Lⁿ(ℝⁿ ∖ D_j) = 0, so Hⁿ(F_j(ℝⁿ ∖ D_j)) = 0 (Lipschitz images of null sets are null, LipschitzWith.hausdorffMeasure_image_le, with μHE[n] = Lⁿ on ℝⁿ).
 (iii) Z_j := {u ∈ D_j : DF_j(u) not injective} satisfies Hⁿ(F_j(Z_j)) = 0 (the area formula with vanishing Jacobian; SimonGMT area_image_criticalSet_eq_zero).
 (iv) E_j := (D_j ∖ Z_j) ∩ F_j⁻¹(M₁) is Borel (u ↦ DF_j(u) is Borel on D_j, measurable_fderiv; injectivity of DF_j(u) means det(⟨DF_j(u)e_p, DF_j(u)e_q⟩) ≠ 0). For an injective linear A : ℝⁿ → ℝ^P choose c_A > 0 with |Aw| ≥ c_A|w| for all w, and put r(A) := c_A/2; put r(A) := 1 for non-injective A. The partition lemma exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (applied to F_j on E_j with derivative DF_j and the positive function r) gives pairwise disjoint Borel sets t_l covering E_j and linear maps A_l, each equal to DF_j(y_l) for some y_l ∈ E_j (hence injective), such that |F_j(u) − F_j(v) − A_l(u − v)| ≤ r(A_l)|u − v| for u, v ∈ E_j ∩ t_l; therefore |F_j(u) − F_j(v)| ≥ (c_{A_l}/2)|u − v| there.
 (v) Enumerate the pieces E_j ∩ t_l (over all j, l) as E'_i, with G_i := F_j and κ_i := c_{A_l}/2. G_i is continuous and injective on the Borel set E'_i, so every G_i(S) with S ⊆ E'_i Borel is Borel (Lusin–Souslin, MeasurableSet.image_of_continuousOn_injOn). Disjointify: A_i := E'_i ∖ G_i⁻¹(⋃_{i'<i} G_{i'}(A_{i'})), recursively; the A_i are Borel, the G_i(A_i) ⊆ M₁ are pairwise disjoint Borel sets, and ⋃_i G_i(A_i) = ⋃_i G_i(E'_i).
 (vi) M₁ ∖ ⋃_i G_i(A_i) ⊆ M₀ ∪ ⋃_j F_j(ℝⁿ ∖ D_j) ∪ ⋃_j F_j(Z_j), which is Hⁿ-null. ∎
 Null-set transfer: (G_i|A_i)⁻¹ : G_i(A_i) → A_i is κ_i⁻¹-Lipschitz, so Lⁿ(A_i ∩ G_i⁻¹(Z)) ≤ κ_i^{−n}·Hⁿ(Z) for Z ⊆ G_i(A_i) (LipschitzOnWith.hausdorffMeasure_image_le), and Hⁿ(G_i(N)) ≤ Lip(G_i)ⁿ·Lⁿ(N) for N ⊆ ℝⁿ. Hence a property holds at Hⁿ-a.e. point of G_i(A_i) iff it holds at G_i(u) for Lⁿ-a.e. u ∈ A_i. The same transfer applies to every bi-Lipschitz piece below.

3. Lemma T (approximate tangent planes of bi-Lipschitz images). Let A ⊆ ℝⁿ be Borel, G : ℝⁿ → ℝ^P Lipschitz and differentiable at every u ∈ A, and κ > 0 with κ|u − v| ≤ |G(u) − G(v)| for u, v ∈ A. Then for Lⁿ-a.e. u ∈ A, DG(u) is injective and HasApproximateTangentSpaceAt n (G(A)) (G(u)) (DG(u)(ℝⁿ)). Proof.
 (i) The set of differentiability points of G is Borel and u ↦ DG(u) is Borel on it (measurableSet_of_differentiableAt, measurable_fderiv), with ‖DG(u)‖ ≤ Lip(G); so F := 1_A·J_G is Borel and bounded by Lip(G)ⁿ (A2), hence locally integrable. By the Lebesgue density theorem (Besicovitch.ae_tendsto_measure_inter_div) and the Lebesgue differentiation theorem (ae_tendsto_average_norm_sub), Lⁿ-a.e. u ∈ A is a density point of A and satisfies ⨍_{B_s(u)} |F(v) − F(u)| dv → 0 as s ↓ 0. Fix such u ∈ A; then F(u) = J_G(u).
 (ii) |DG(u)w| ≥ κ|w| for every w; in particular DG(u) is injective. Let w ≠ 0 and 0 < ε < 1. For all small r > 0 the ball B(u + rw, εr|w|) meets A: otherwise B(u, (1 + ε)r|w|) ∖ A would contain it, a fixed fraction (ε/(1 + ε))ⁿ > 0 of the volume of B(u, (1 + ε)r|w|), contradicting density 1 at u. Pick v_r ∈ A in that ball, so |v_r − u − rw| < εr|w| and |v_r − u| ≥ (1 − ε)r|w|. Differentiability at u gives |G(v_r) − G(u) − DG(u)(v_r − u)| = o(r), hence r|DG(u)w| ≥ |DG(u)(v_r − u)| − ‖DG(u)‖εr|w| ≥ |G(v_r) − G(u)| − o(r) − ‖DG(u)‖εr|w| ≥ κ(1 − ε)r|w| − ‖DG(u)‖εr|w| − o(r). Dividing by r and letting r ↓ 0 and then ε ↓ 0 gives |DG(u)w| ≥ κ|w|. So V_u := DG(u)(ℝⁿ) is n-dimensional and J_G(u) > 0.
 (iii) Blow-ups. Put x := G(u), η_r(y) := r⁻¹(y − x) (SimonGMT blowUpMap x r), and let h ∈ C_c(ℝ^P) vanish outside B_ρ(0). G(A) is Borel (Lusin–Souslin). Scaling: η_r is a translation (an isometry) followed by the homothety of ratio r⁻¹, so Hⁿ(η_r(S)) = r^{−n}·Hⁿ(S) for every S ⊆ ℝ^P (Mathlib Isometry.hausdorffMeasure_image and MeasureTheory.Measure.euclideanHausdorffMeasure_smul₀; μHE[n] is a fixed multiple of μH[n]). Hence the image of Hⁿ⌞S under η_r is rⁿ·Hⁿ⌞η_r(S) (for Borel B, Hⁿ(S ∩ η_r⁻¹(B)) = Hⁿ(η_r⁻¹(η_r(S) ∩ B)) = rⁿ·Hⁿ(η_r(S) ∩ B)), i.e. ∫_{η_r(S)} h dHⁿ = r^{−n}·∫_S h∘η_r dHⁿ for Borel S. By the scaling of Hⁿ under the similarity η_r and the injective area formula for the Lipschitz map G on the Borel set A (SimonGMT weighted_area_formula_lipschitz_injOn applied to the positive and negative parts of h∘η_r; its Jacobian areaJacobianAt G v equals J_G(v) for v ∈ A), followed by the substitution v = u + rw (dv = rⁿdw):
 I(r) := ∫_{η_r(G(A))} h dHⁿ = r^{−n}∫_A h((G(v) − x)/r)·J_G(v) dv = ∫_{ℝⁿ} F(u + rw)·h(D_r(w)) dw, where D_r(w) := (G(u + rw) − G(u))/r.
 If u + rw ∈ A then |D_r(w)| ≥ κ|w|, so the last integrand vanishes unless |w| < ρ' := ρ/κ; likewise h(DG(u)w) = 0 for |w| ≥ ρ' by (ii). Hence, with B' := B_{ρ'}(0) ⊆ ℝⁿ,
 |I(r) − J_G(u)·∫_{ℝⁿ} h(DG(u)w) dw| ≤ sup|h|·∫_{B'} |F(u + rw) − F(u)| dw + J_G(u)·Lⁿ(B')·sup_{w∈B'} |h(D_r(w)) − h(DG(u)w)|.
 The first term equals sup|h|·Lⁿ(B')·⨍_{B_{rρ'}(u)} |F − F(u)| → 0 by (i); the second tends to 0 because D_r → DG(u) uniformly on B' (differentiability at u) and h is uniformly continuous. Finally J_G(u)·∫_{ℝⁿ} h(DG(u)w) dw = ∫_{V_u} h dHⁿ: by the linear area formula (SimonGMT linear_area_formula, i.e. Mathlib LinearMap.euclideanHausdorffMeasure_image) Hⁿ(DG(u)(S)) = J_G(u)·Lⁿ(S) for every S ⊆ ℝⁿ, so Hⁿ⌞V_u is the image of J_G(u)·Lⁿ under the injective linear map DG(u) onto V_u, and integrating h gives the identity. Since finrank V_u = n and h is arbitrary, HasApproximateTangentSpaceAt n (G(A)) x V_u. ∎
 Remark (reuse; not a proof step). In both applications below (G_i on A_i in step 4 and H_i on A_il in step 9) the derivative is injective at every point of the piece by construction, so the instance of Lemma T that is used is exactly the statement of the DAG node ptd_piece_image_approxTangent_ae (not yet accepted), which a decomposition of this node may reuse once it is accepted.

4. Tangent planes and orientation along the pieces (parent 6(b); Simon 3.4–3.5). Fix i. By (TL) with (U, A, B) := (U, G_i(A_i), M₁) (Borel, G_i(A_i) ⊆ M₁ ⊆ U, Hⁿ(M₁) < ∞), for Hⁿ-a.e. x ∈ G_i(A_i) the sets G_i(A_i) and M₁ have the same approximate tangent spaces at x. Combining this with step 1(d), Lemma T for (A_i, G_i, κ_i), uniqueness of approximate tangent spaces and the null-set transfer of step 2: for Lⁿ-a.e. u ∈ A_i, the point x := G_i(u) is good, T_x = DG_i(u)(ℝⁿ), and ξ(x) = ξ̃(x) is a unit orientation of it. By (A2), DG_i(u)_#e/J_{G_i}(u) is also a unit orientation of DG_i(u)(ℝⁿ), so by (A1)
 (★) ξ(G_i(u)) = s_i(u)·DG_i(u)_#e/J_{G_i}(u), s_i(u) ∈ {1, −1},
 for Lⁿ-a.e. u ∈ A_i, where s_i(u) := 1 if ξ̃(G_i(u)) = DG_i(u)_#e/J_{G_i}(u) and s_i(u) := −1 otherwise (a Borel function on A_i). Put θ_i := θ∘G_i on A_i; θ_i ≥ 1 there, since G_i(A_i) ⊆ M.

5. The maps H_i := f̂∘G_i (parent 6(b): d^M f_{x#}ξ(x) = Df(x)_#ξ(x)). H_i : ℝⁿ → ℝ^P is Lipschitz and differentiable at every u ∈ A_i with DH_i(u) = Df̂(G_i(u))∘DG_i(u) (chain rule). By (★), for Lⁿ-a.e. u ∈ A_i and every n-covector β: ξ(G_i(u))(β∘Df̂(G_i(u))) = s_i(u)·β(Df̂(G_i(u))DG_i(u)e₁, …, Df̂(G_i(u))DG_i(u)eₙ)/J_{G_i}(u) = s_i(u)·⟨β, DH_i(u)_#e⟩/J_{G_i}(u); and by (A3), J_{H_i}(u) ≤ ‖Df̂(G_i(u))‖ⁿ·J_{G_i}(u) ≤ Λⁿ·J_{G_i}(u).

6. Pulling Q back (parent 6(c); Simon 3.3 and 3.6). Fix ω ∈ 𝒟ⁿ(U). By step 1(b)–(c) and step 2 (disjoint Borel pieces covering M₁ up to a null set, F_ω integrable), Q(ω) = Σ_i ∫_{G_i(A_i)} F_ω dHⁿ, absolutely convergent. The injective area formula for G_i on A_i (weighted_area_formula_lipschitz_injOn applied to the positive and negative parts of a Borel version of F_ω, which are integrable; by the null-set transfer of step 2 the choice of version does not matter. The same passage from the nonnegative area formula to integrable signed integrands is the content of the accepted DAG declaration dpfir_integral_eq_of_area_lintegral, which a decomposition of this node may reuse) and step 5 give
 ∫_{G_i(A_i)} F_ω dHⁿ = ∫_{A_i} F_ω(G_i(u))·J_{G_i}(u) du = ∫_{A_i} θ_i(u)·s_i(u)·⟨ω(H_i(u)), DH_i(u)_#e⟩ du,
 since F_ω(G_i(u)) = θ_i(u)·ξ(G_i(u))(ω(H_i(u))∘Df̂(G_i(u))). By (A2), |⟨ω(H_i(u)), DH_i(u)_#e⟩| ≤ |ω|_{E,∞}·J_{H_i}(u) with |ω|_{E,∞} := sup_z |ω(z)|_E, and by step 5 and the area formula, Σ_i ∫_{A_i} θ_i J_{H_i} du ≤ Λⁿ·Σ_i ∫_{A_i} θ_i J_{G_i} du = Λⁿ·∫_{M₁} θ dHⁿ < ∞.

7. Removing the critical part; bi-Lipschitz pieces of H_i (parent 6(c); Simon 3.4). A_i⁺ := {u ∈ A_i : DH_i(u) injective} is Borel. For u ∈ A_i ∖ A_i⁺, DH_i(u)_#e = 0 by (A2), so the integrand of step 6 vanishes there (these are the points with J^M f = 0). Exactly as in step 2(iv) (partition lemma with r(A) = c_A/2, applied to H_i on A_i⁺ with the derivative DH_i, which is injective there), A_i⁺ is the disjoint union of countably many Borel sets A_il with κ_il|u − v| ≤ |H_i(u) − H_i(v)| for u, v ∈ A_il, κ_il > 0. Hence ∫_{A_i} θ_i s_i ⟨ω∘H_i, DH_i_#e⟩ du = Σ_l ∫_{A_il} θ_i s_i ⟨ω∘H_i, DH_i_#e⟩ du.

8. Image pieces (Simon 3.6). N_il := H_i(A_il) is Borel (Lusin–Souslin), H_i|A_il is injective with κ_il⁻¹-Lipschitz inverse, and N_il ⊆ f̂(M₁) ⊆ f(K) ⊆ U. On N_il define g_il := (θ_i·s_i)∘(H_i|A_il)⁻¹, an integer-valued Borel function with |g_il| ≥ 1, and η_il := (DH_i(·)_#e/J_{H_i}(·))∘(H_i|A_il)⁻¹, Borel; for u ∈ A_il, DH_i(u)_#e/J_{H_i}(u) is a unit orientation of DH_i(u)(ℝⁿ) by (A2). Since ⟨ω(H_i(u)), DH_i(u)_#e⟩ = J_{H_i}(u)·⟨ω(H_i(u)), η_il(H_i(u))⟩, the injective area formula for H_i on A_il gives
 ∫_{A_il} θ_i s_i ⟨ω∘H_i, DH_i_#e⟩ du = ∫_{N_il} g_il(y)·⟨ω(y), η_il(y)⟩ dHⁿ(y),
 and Σ_{i,l} ∫_{N_il} |g_il| dHⁿ = Σ_{i,l} ∫_{A_il} θ_i J_{H_i} du ≤ Λⁿ·∫_{M₁} θ dHⁿ < ∞ (step 6). With steps 6–7, Q(ω) = Σ_{i,l} ∫_{N_il} g_il⟨ω, η_il⟩ dHⁿ, absolutely convergent (|⟨ω, η_il⟩| ≤ |ω|_{E,∞} by (A0)). Put N := ⋃_{i,l} N_il: N is Borel, N ⊆ U, and Hⁿ(N) ≤ Σ_{i,l} Hⁿ(N_il) ≤ Σ_{i,l} ∫_{N_il} |g_il| dHⁿ < ∞.

9. Common tangent planes (parent 6(d); Simon 3.7). Fix (i, l). Lemma T for (A_il, H_i, κ_il) and the null-set transfer give: for Hⁿ-a.e. y ∈ N_il, with u := (H_i|A_il)⁻¹(y), N_il has the approximate tangent space DH_i(u)(ℝⁿ) at y. (TL) with (U, A, B) := (ℝ^P, N_il, N) (Borel, N_il ⊆ N, Hⁿ(N) < ∞) shows that for Hⁿ-a.e. y ∈ N_il the sets N_il and N have the same approximate tangent spaces at y. Discarding countably many null sets: for Hⁿ-a.e. y ∈ N and every (i, l) with y ∈ N_il, N has the approximate tangent space T_yN = DH_i((H_i|A_il)⁻¹(y))(ℝⁿ) at y (unique), and η_il(y) is a unit orientation of T_yN. Fix an enumeration of ℕ × ℕ and let η(y) := η_{i₀l₀}(y) for the first (i₀, l₀) with y ∈ N_{i₀l₀}; η is Borel on N. By (A1), η_il(y) = ε_il(y)·η(y) with ε_il(y) ∈ {1, −1}, where ε_il(y) := 1 if η_il(y) = η(y) and −1 otherwise (Borel).

10. Integer multiplicity (parent 6(e); Simon 3.8). The function Σ_{i,l} |g_il|·1_{N_il} is integrable (step 8), hence finite Hⁿ-a.e.; since |g_il| ≥ 1, Hⁿ-a.e. y ∈ N lies in only finitely many N_il. For such y that are also good in the sense of step 9, put k(y) := Σ_{(i,l): y∈N_il} ε_il(y)·g_il(y) ∈ ℤ; then Σ_{i,l} 1_{N_il}(y)·g_il(y)·η_il(y) = k(y)·η(y) and |k(y)| ≤ Σ_{i,l} |g_il(y)|·1_{N_il}(y). k agrees Hⁿ-a.e. on N with a Borel ℤ-valued function k̃ (the limit of the Borel partial sums where it exists, 0 elsewhere). The partial sums of Σ_{i,l} 1_{N_il} g_il ⟨ω, η_il⟩ are dominated by |ω|_{E,∞}·Σ_{i,l} |g_il| 1_{N_il}, which is integrable, so by dominated convergence, for every ω ∈ 𝒟ⁿ(U),
 Q(ω) = ∫_N Σ_{i,l} 1_{N_il}·g_il·⟨ω, η_il⟩ dHⁿ = ∫_N k̃(y)·⟨ω(y), η(y)⟩ dHⁿ(y).

11. The integer multiplicity triple (parent 6(f)–(g); Simon 3.9). Let N₀ ⊆ N be a Borel Hⁿ-null set off which the conclusions of steps 9–10 hold and k = k̃ (Hⁿ is Borel regular). Put N' := {y ∈ N ∖ N₀ : k̃(y) ≠ 0}, θ'(y) := |k̃(y)| for y ∈ N' and θ'(y) := 0 otherwise (ℕ-valued, Borel), and ξ'(y) := sign(k̃(y))·η(y) for y ∈ N' and ξ'(y) := 0 otherwise (Borel). Then R' := (N', θ', ξ') is an IMRep in U:
 – N' is Borel and N' ⊆ N ⊆ U;
 – N' is countably n-rectifiable: N' ⊆ ⋃_i H_i(ℝⁿ) with every H_i Lipschitz on ℝⁿ (the definition of CountablyRectifiable with the null set ∅);
 – θ' is measurable and θ'(y) ≥ 1 for y ∈ N';
 – for every compact C ⊆ U, ∫⁻_{N'∩C} θ' dHⁿ ≤ ∫⁻_N Σ_{i,l} |g_il|·1_{N_il} dHⁿ < ∞;
 – ξ' is Borel, hence a.e. strongly measurable for Hⁿ⌞N';
 – orientation: by (TL) with (U, A, B) := (ℝ^P, N', N) (N' ⊆ N Borel, Hⁿ(N) < ∞), for Hⁿ-a.e. y ∈ N' the set N' has the approximate tangent space T_yN at y, and ξ'(y) = ±η(y) is a unit orientation of T_yN by step 9 and (A1).
Finally, for ω ∈ 𝒟ⁿ(U): R'.action ω = ∫_{N'} θ'(y)·ξ'(y)(ω(y)) dHⁿ(y) = ∫_{N'} k̃(y)·⟨ω(y), η(y)⟩ dHⁿ(y) = ∫_N k̃·⟨ω, η⟩ dHⁿ = Q(ω), because θ'ξ' = k̃η on N', k̃ = 0 on N ∖ (N' ∪ N₀) and Hⁿ(N₀) = 0 (step 10). So R' represents Q, and Q is integer multiplicity. ∎

## Key steps

1. Restrict to M₁ = M ∩ K (Hⁿ(M₁) < ∞) and replace f by a globally Lipschitz C¹ map f̂ equal to f near K; (TL) and R.orients give oriented approximate tangent planes Hⁿ-a.e. on M₁.
2. Parametrize M₁ up to a null set by disjoint bi-Lipschitz pieces G_i(A_i) (Rademacher, critical-set area formula, partition into approximately linear pieces, Lusin–Souslin).
3. Lemma T: at density and Lebesgue points the blow-ups of G(A) converge to DG(u)(ℝⁿ); with (TL) and the Gram–Schmidt algebra, ξ(G_i(u)) = ±DG_i(u)_#e/J_{G_i}(u) (Simon 3.4–3.5).
4. With H_i = f̂∘G_i and the area formula, Q(ω) = Σ_{i,l} ∫_{N_il} g_il⟨ω, η_il⟩ dHⁿ over bi-Lipschitz image pieces N_il = H_i(A_il), with Σ∫|g_il| ≤ Λⁿ∫_{M₁}θ (Simon 3.6).
5. Lemma T and (TL) give one orientation η of T_yN with η_il(y) = ±η(y); so Q(ω) = ∫_N k⟨ω, η⟩ with k integer valued, and (N′, |k|, sign(k)η) on {k ≠ 0} is an IMRep representing Q (Simon 3.7–3.9).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; read GMT/Ch07/Contract.lean, GMT/Ch07/README.md, PROBLEM.md and this node's parent-child-handoff.json, parent-supplied-plan.md, parent-supplied-natural-proof.md (proof identical to the handoff)`
- `grep '^theorem|^def|^structure|^abbrev|^instance' simongmt Poincare/SimonGMT/Chapter06/{Forms,Currents,Mass,CurrentLocalEquality,AffineCurrentPushforward}.lean and Chapter03/{Rectifiable,Differential}.lean`
- `grep '^theorem' simongmt Poincare/SimonGMT/Chapter02/{AreaLipschitz,AreaNoninjective,AreaCritical,AreaDomain,Area}.lean (weighted_area_formula_lipschitz_injOn, area_image_criticalSet_eq_zero, linear_area_formula)`
- `python3 -I scans of dag.json (995 nodes): lean_name/statement matching push|area|pullback|compContinuousLinearMap|mollif|fderiv|ContDiffOn; status and candidate_commit of dpf_pushforward_formula_current_exists, dpf_pushforward_formula_boundaryVanishes, dpf_smooth_approx_compact_perturbation, dpf_rectifiable_bilipschitz_pieces, covectorEuclideanNorm_gram_bounds, ptd_ae_approxTangent_iff_of_subset, ptd_piece_image_approxTangent_ae; parallel nodes dimred_mbl_pf_* and dor_lmb_pc_* (all decomposing); byte-identity comparisons; collision check of dtc_bc_lc_pf_* (none)`
- `git show <candidate_commit>:GMT/Ch07/Submission.lean | grep 'theorem Submission.<name>' for the six reused declarations (types identical); git log --all --oneline -S'dtc_bc_lc_pf_' (no match)`
- `read nodes/root-dimension-reduction-results-a1-moving-blowups-a1-pushforward-a1/decomposition-v1.json, nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-comparison-a1/decomposition-v1.json, and the parent-child-handoff.json of the reused nodes (audited proofs)`
- `grep -n '_existing_lean_name_problem|_accepted_checkpoint|_overlay_accepted_children' /runtime/flows/gmt-claude-9a0895c8c5e1/_recursive_lean/runtime.py`
- `grep Mathlib at the pin: exists_contDiff_support_eq_eq_one_iff, IsCompact.exists_cthickening_subset_open, exists_partition_approximatesLinearOn_of_hasFDerivWithinAt, MeasurableSet.image_of_continuousOn_injOn, LipschitzWith.ae_differentiableAt, ContDiffOn.continuousOn_fderiv_of_isOpen, norm_compContinuousLinearMap_le, ae_tendsto_average_norm_sub, ae_tendsto_measure_inter_div, norm_integral_le_of_norm_le, LipschitzOnWith.hausdorffMeasure_image_le, Filter.EventuallyEq.fderiv_eq, ContDiffBump.convolution_tendsto_right_of_continuous, Isometry.hausdorffMeasure_image, euclideanHausdorffMeasure_smul₀, LinearMap.euclideanHausdorffMeasure_image`
- `sed -n book/chapter-06.txt lines 395-540 and 760-870 (2.23-2.29, 3.1-3.10); book/chapter-03.txt lines 330-412 (2.1-2.6)`
- `lake env lean /tmp/pfdecomp/check/Types2.lean (12 child types in the scope from gmt-compare.py contract_scope); lake env lean /tmp/pfdecomp/check/Assembly2.lean with #print axioms; verifier lean_contract.validate_lean_statement on all 12 strings; topological sort of depends_on`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/PROBLEM.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-a685b45291/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-a685b45291/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-comparison-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-pushforward-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Differential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/runtime/flows/gmt-claude-9a0895c8c5e1/_recursive_lean/runtime.py`
- `/tmp/pfdecomp/check/Types2.lean`
- `/tmp/pfdecomp/check/Assembly2.lean`

The pinned SimonGMT library has currents, boundary, mass with the Euclidean coefficient norm, support and zero region, countable rectifiability, approximate tangent spaces and the Lipschitz area formula on ℝⁿ. It has only the affine push-forward, and no push-forward of integer multiplicity currents by C¹ maps. Comparator-accepted DAG declarations already prove, for compactly supported C¹ perturbations of the identity, that the push-forward formula defines a current and maps cycles to cycles (dpf_pushforward_formula_current_exists, dpf_pushforward_formula_boundaryVanishes). They are reused together with the node's four inherited dependencies (dtc_mass_eq_measure, dtc_vanish_off_support, cmc_imRep_locality_restrict_sub, rsd_cmr_support_subset_of_vanish), all with types identical to their accepted candidate commits. Five new types are byte-identical to the unaccepted dimred_mbl_pf_*/dor_lmb_pc_* nodes and get new unique names dtc_bc_lc_pf_*; c1_perturbation is new. All 12 types elaborate in the comparator scope, and a Lean assembly proves the exact frozen parent type from them using only propext, Classical.choice and Quot.sound.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
