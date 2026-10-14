<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.simons_cone-a1.simons_identity-a1 -->

## Theorem `Submission.codim1_hcp_sc_simons_identity`

Let P, m ∈ ℕ, A₀ ⊆ ℝ^P a subspace with dim A₀ = m + 1, M ⊆ A₀ with IsEmbeddedSubmanifold r m M for every r ∈ ℕ; let ν : ℝ^P → ℝ^P be C^∞ on some open O ⊇ M, with ν(x) ∈ A₀, |ν(x)| = 1 and ν(x)·v = 0 for every v ∈ tangentSpace M x, for every x ∈ M; and assume trace(P_x∘Dν(x)) = 0 for every x ∈ M. Throughout: P_y is the orthogonal projection onto span(tangentSpace M y), e_j = EuclideanSpace.single j 1, H^m = μHE[m], |A|²(y) := Σ_j |Dν(y)(P_ye_j)|² (Dν = fderiv ℝ ν), δ_jg(y) := fderivWithin ℝ g M y (P_ye_j). Let C(y) := Dν(y)∘P_y, D_aC := fderivWithin ℝ C M x a, |∇A|²(x) := Σ_{i,j,k}((D_{P_xe_k}C)(P_xe_i)·P_xe_j)² and Δ_Mg(x) := Σ_j δ_j(δ_jg)(x). Then for every x ∈ M: Δ_M|A|²(x) = 2|∇A|²(x) − 2(|A|²(x))².

Node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.simons_cone-a1.simons_identity-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6016

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6797, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6803, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6821

Decomposition children: None

## Lean problem

Declaration: `Submission.codim1_hcp_sc_simons_identity`

```lean
∀ (P m : ℕ) (A₀ : Submodule ℝ (Euclid P)) (M : Set (Euclid P)) (ν : Euclid P → Euclid P), Module.finrank ℝ A₀ = m + 1 → M ⊆ (A₀ : Set (Euclid P)) → (∀ r : ℕ, IsEmbeddedSubmanifold r m M) → (∃ O : Set (Euclid P), IsOpen O ∧ M ⊆ O ∧ ContDiffOn ℝ (⊤ : ℕ∞) ν O) → (∀ x ∈ M, ν x ∈ A₀ ∧ ‖ν x‖ = 1 ∧ ∀ v ∈ tangentSpace M x, inner ℝ (ν x) v = 0) → (∀ x ∈ M, LinearMap.trace ℝ (Euclid P) ((Submodule.span ℝ (tangentSpace M x)).starProjection.toLinearMap ∘ₗ (fderiv ℝ ν x).toLinearMap) = 0) → ∀ x ∈ M, (∑ j : Fin P, fderivWithin ℝ (fun y => fderivWithin ℝ (fun z => ∑ i : Fin P, ‖fderiv ℝ ν z ((Submodule.span ℝ (tangentSpace M z)).starProjection (EuclideanSpace.single i 1))‖ ^ 2) M y ((Submodule.span ℝ (tangentSpace M y)).starProjection (EuclideanSpace.single j 1))) M x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))) = 2 * (∑ i : Fin P, ∑ j : Fin P, ∑ k : Fin P, (inner ℝ (fderivWithin ℝ (fun y => (fderiv ℝ ν y).comp (Submodule.span ℝ (tangentSpace M y)).starProjection) M x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single k 1)) ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single i 1))) ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))) ^ 2) - 2 * (∑ i : Fin P, ‖fderiv ℝ ν x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single i 1))‖ ^ 2) ^ 2
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

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.simons_cone-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.simons_cone-a1.simons_identity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Simon Appendix B, B.4–B.9 (chapter-B.txt lines 88–160), as organized in step 1 of the parent proof. Parent (0c) and (0g) supply the bridge between the frame-free Lean quantities and the frame components. Documented erratum: as printed, the second line of B.7 carries the opposite sign on the two curvature terms relative to its first line and to B.6. One fixed convention is used below (II.4), and the result coincides with the printed B.8.

Notation. Fix an open O ⊇ M on which ν is C^∞. T_y := tangentSpace M y; P_y := orthogonal projection onto span T_y; e_1, …, e_P the standard basis; Π := orthogonal projection onto A₀. |A|²(y) := Σ_i |Dν(y)(P_ye_i)|². δ_jg(y) := fderivWithin ℝ g M y (P_ye_j) and Δ_Mg(x) := Σ_j δ_j(δ_jg)(x). C(y) := Dν(y)∘P_y and D_aC := fderivWithin ℝ C M x a. |∇A|²(x) := Σ_{i,j,k} ((D_{P_xe_k}C)(P_xe_i)·P_xe_j)². The claim is Δ_M|A|²(x) = 2|∇A|²(x) − 2(|A|²(x))² for x ∈ M.

Part I. Ambient extensions, a frame, and three bridges.

I.1 (Extensions.) P̃(y)w := Πw − (ν(y)·w)ν(y), C̃(y) := Dν(y)∘P̃(y) and Ã(y) := Σ_i |C̃(y)e_i|² are C^∞ on O (Dν is C^∞ on the open O by ContDiffOn.fderiv_of_isOpen). By the sibling normal_complement, for y ∈ M: T_y = A₀ ∩ ν(y)^⊥ (a subspace) and P_y = P̃(y). Hence C = C̃ and |A|² = Ã on M.
 Extension principle (E). Let g : ℝ^P → F agree on M ∩ U (U an open neighbourhood of y ∈ M) with a function G differentiable at y. Then fderivWithin ℝ g M y τ = DG(y)τ for every τ ∈ T_y. Reason: g has derivative DG(y) within M at y (congruence on M ∩ U; fderivWithin is local, fderivWithin_inter); now apply the sibling tangent_fderiv.
 Consequently δ_j|A|² = G_j on M with G_j(y) := DÃ(y)(P̃(y)e_j), and Δ_M|A|²(x) = Σ_j DG_j(x)(P_xe_j). Also D_aC = DC̃(x)a for a ∈ T_x.

I.2 (Second fundamental form.) By the sibling codazzi, for y ∈ M and a, b, d ∈ T_y: Dν(y)a ∈ T_y; Dν(y)a·b = Dν(y)b·a; and (D_aC)(b)·d is symmetric in (a, b) and in (b, d).

I.3 (Frame.) Fix x₀ ∈ M. The vectors P_{x₀}e_1, …, P_{x₀}e_P span T_{x₀}, which has dimension m. Choose j_1, …, j_m with P_{x₀}e_{j_1}, …, P_{x₀}e_{j_m} linearly independent. P̃ is continuous, so there is an open ball B ⊆ O around x₀ on which w_a(y) := P̃(y)e_{j_a} (a = 1, …, m) are linearly independent. Gram–Schmidt gives C^∞ maps E_1, …, E_m : B → ℝ^P, orthonormal at every y ∈ B, with span{E_a(y)} = span{w_a(y)}. For y ∈ M ∩ B, w_a(y) ∈ T_y and dim T_y = m. So (E_a(y))_a is an orthonormal basis of T_y.

I.4 (Tangent fields; connection.) A tangent field is a C^∞ map X : B → ℝ^P with X(y) ∈ T_y for y ∈ M ∩ B; examples are E_a and Σ_a f_aE_a with f_a C^∞. For a tangent field X and a C¹ map Z on B put D_XZ(y) := DZ(y)X(y). By (E), D_XZ at points of M ∩ B depends only on Z restricted to M ∩ B. Define ∇_XY := P(D_XY) and [X, Y] := D_XY − D_YX.
 (a) Gauss formula. For tangent X, Y and y ∈ M ∩ B: D_XY ∈ A₀. Indeed, let γ witness X(y) ∈ T_y. Then Y∘γ takes values in A₀ near s = 0 (Y(z) ∈ T_z ⊆ A₀ for z ∈ M). Its derivative at 0 is DY(y)X(y) = D_XY(y). The difference quotients lie in the closed subspace A₀, so D_XY(y) ∈ A₀. Also ν·D_XY = −Dν(X)·Y: differentiate ν·Y, which vanishes on M ∩ B, along X and use (E). Since A₀ = T_y ⊕ ℝν(y) orthogonally, D_XY = ∇_XY + h(X, Y)ν with h(X, Y) := −Dν(X)·Y = SX·Y, where SX := −Dν(X) is tangent (I.2). h is symmetric (I.2).
 (b) Torsion-freeness. ν·[X, Y] = h(X, Y) − h(Y, X) = 0 and [X, Y] ∈ A₀, so [X, Y] is tangent and ∇_XY − ∇_YX = P[X, Y] = [X, Y].
 (c) Metric compatibility. X(Y·Z) = ∇_XY·Z + Y·∇_XZ for tangent Y, Z. Indeed X(Y·Z) = D_XY·Z + Y·D_XZ, and only tangential parts pair with tangent vectors.
 (d) Flatness. For tangent X, Y and a C² map Z on B: D_XD_YZ − D_YD_XZ − D_{[X,Y]}Z = 0 on M ∩ B. This follows from D_X(DZ·Y) − D_Y(DZ·X) = D²Z(X, Y) + DZ(D_XY) − D²Z(Y, X) − DZ(D_YX) = DZ([X, Y]), using symmetry of D²Z (ContDiffAt.isSymmSndFDerivAt). Applied to scalar functions f, this gives XYf − YXf = [X, Y]f.

I.5 (Covariant derivatives in the frame.) Indices a, b, c, … run over 1, …, m and repeated indices are summed. For functions f on M ∩ B put E_cf := D_{E_c}f. Define:
 h_ab := h(E_a, E_b);
 h_{ab;c} := E_c(h_ab) − h(∇_{E_c}E_a, E_b) − h(E_a, ∇_{E_c}E_b);
 h_{ab;cd} := E_d(h_{ab;c}) − (∇h)(∇_{E_d}E_a, E_b, E_c) − (∇h)(E_a, ∇_{E_d}E_b, E_c) − (∇h)(E_a, E_b, ∇_{E_d}E_c), so the index c is differentiated first;
 f_{;c} := E_cf and f_{;cd} := E_d(E_cf) − (∇_{E_d}E_c)f;
 H := h_aa.
All are C^∞ functions on M ∩ B (restrictions of ambient C^∞ functions).

I.6 (Bridges.) At points of M ∩ B:
 (B1) h_{ab;c} = −(D_{E_c}C)(E_a)·E_b, and |∇A|² = Σ_{a,b,c} h_{ab;c}². For the first claim, h(X, Y) = −C X·Y for tangent X, Y, so E_c(h_ab) = −(D_{E_c}C)E_a·E_b − C(D_{E_c}E_a)·E_b − CE_a·D_{E_c}E_b. C kills normal components (C(y)w = Dν(y)(P_yw)), so C(D_{E_c}E_a) = C(∇_{E_c}E_a). CE_a is tangent (I.2), so CE_a·D_{E_c}E_b = CE_a·∇_{E_c}E_b. This gives the formula. For the second claim, use the Hilbert–Schmidt identity: for a linear functional ℓ on ℝ^P, Σ_jℓ(P_ye_j)² = Σ_aℓ(E_a)². Indeed P_ye_j = Σ_a(e_j·E_a)E_a and Σ_j(e_j·E_a)(e_j·E_b) = E_a·E_b = δ_ab. Apply it in each slot of the trilinear form (u, v, w) ↦ (D_{P_yu}C)(P_yv)·P_yw (D_·C is linear in the direction, by I.1).
 (B2) |A|² = h_ab h_ab. |A|²(y) = Σ_j|Dν(y)(P_ye_j)|² = Σ_a|Dν(y)E_a|², by the Hilbert–Schmidt identity for the linear map Dν(y). Then Σ_a|Dν(y)E_a|² = Σ_{a,b}(Dν(y)E_a·E_b)² because Dν(y)E_a ∈ T_y (Parseval).
 (B3) Δ_M|A|² = (|A|²)_{;cc}. Let g := |A|² and ∇g := (E_ag)E_a, a tangent field. For y ∈ M ∩ B, δ_jg(y) = Σ_a(e_j·E_a)E_ag = ∇g·e_j, by linearity of fderivWithin and P_ye_j = Σ_a(e_j·E_a)E_a. By (E), δ_j(δ_jg)(x₀) = D(∇g·e_j)(x₀)(P_{x₀}e_j) = (D_{P_{x₀}e_j}∇g)·e_j. Summing over j gives the trace of the linear map L∘P_{x₀}, where L := D(∇g)(x₀). This trace equals Σ_c(LE_c)·E_c, since L∘P_{x₀} vanishes on T_{x₀}^⊥. Moreover (LE_c)·E_c = (∇_{E_c}∇g)·E_c = E_c(∇g·E_c) − ∇g·∇_{E_c}E_c = E_c(E_cg) − (∇_{E_c}E_c)g = g_{;cc}, by (c) of I.4.

Part II. The intrinsic computation (Simon B.4–B.9, parent step 1), at points of M ∩ B.
II.1 (B.4) h_ab = h_ba (I.2). Hence h_{ab;c} and h_{ab;cd} are symmetric in a, b.
II.2 (Codazzi, B.5) h_{ab;c} is totally symmetric: by (B1), h_{ab;c} = −(D_{E_c}C)(E_a)·E_b, and I.2 gives symmetry in (c, a) and in (a, b).
II.3 (Gauss, B.6) R(X, Y)Z := ∇_X∇_YZ − ∇_Y∇_XZ − ∇_{[X,Y]}Z = h(Y, Z)SX − h(X, Z)SY for tangent X, Y, Z. Expand I.4(d) with D_YZ = ∇_YZ + h(Y, Z)ν and D_Xν = −SX: D_X(D_YZ) = ∇_X∇_YZ + h(X, ∇_YZ)ν + X(h(Y, Z))ν − h(Y, Z)SX. Do the same with X and Y exchanged, and use D_{[X,Y]}Z = ∇_{[X,Y]}Z + h([X, Y], Z)ν. The tangential component of I.4(d) is the Gauss equation. In components, R(E_a, E_b)E_c·E_d = h_bc h_ad − h_ac h_bd.
II.4 (Ricci identity, B.7, fixed convention) h_{ab;cd} − h_{ab;dc} = −h(R(E_d, E_c)E_a, E_b) − h(E_a, R(E_d, E_c)E_b). Here h_{ab;cd} = (∇²_{E_d,E_c}h)(E_a, E_b) with ∇²_{X,Y} := ∇_X∇_Y − ∇_{∇_XY}. Expand the definitions and use torsion-freeness ∇_XY − ∇_YX = [X, Y] (I.4(b)): ∇²_{X,Y}h − ∇²_{Y,X}h = ∇_X∇_Yh − ∇_Y∇_Xh − ∇_{[X,Y]}h. Evaluated on (U, W), the terms in which the operators act on the function h(U, W) cancel, because XYf − YXf − [X, Y]f = 0 (I.4(d)). The remaining terms are −h(R(X, Y)U, W) − h(U, R(X, Y)W).
II.5 (Commutation) Write SE_a = h_abE_b, (h²)_ab = h_ach_cb, (h³)_ab = h_ach_cdh_db (symmetric) and |A|² = h_abh_ab. Then
 Σ_c(h_{ca;bc} − h_{ca;cb}) = −h(R(E_c, E_b)E_c, E_a) − h(E_c, R(E_c, E_b)E_a)   [II.4 with (a, b, c, d) ↦ (c, a, b, c)]
 = −[(h³)_ba − H(h²)_ba] − [|A|²h_ba − (h³)_ab] = H(h²)_ab − |A|²h_ab.
 Here Gauss gives R(E_c, E_b)E_c = h_bcSE_c − h_ccSE_b, so h(R(E_c, E_b)E_c, E_a) = (h³)_ba − H(h²)_ba. Likewise R(E_c, E_b)E_a = h_baSE_c − h_caSE_b, so h(E_c, R(E_c, E_b)E_a) = |A|²h_ba − (h³)_ab.
II.6 (Laplacian of h) h_{ab;cc} = h_{ac;bc} (Codazzi II.2: the 3-tensors (a, b, c) ↦ h_{ab;c} and (a, b, c) ↦ h_{ac;b} coincide, hence so do their covariant derivatives) = h_{ca;bc} (II.1) = h_{ca;cb} + H(h²)_ab − |A|²h_ab (II.5) = H_{;ab} + H(h²)_ab − |A|²h_ab. For the last step, Σ_ch_{ca;c} = Σ_ch_{cc;a} = H_{;a} by Codazzi, because contraction commutes with ∇ for the orthonormal frame; hence Σ_ch_{ca;cb} = H_{;ab}.
II.7 (B.8) By metric compatibility, (|A|²)_{;c} = 2h_abh_{ab;c} and ½(|A|²)_{;cc} = h_{ab;c}h_{ab;c} + h_abh_{ab;cc}. With II.6:
 ½(|A|²)_{;cc} = Σ h²_{ab;c} − |A|⁴ + h_abH_{;ab} + H h_ab(h²)_ab.
II.8 (H = 0) H = h_aa = −Σ_aDν(y)E_a·E_a = −trace(Dν(y)∘P_y) = −trace(P_y∘Dν(y)) = 0 for every y ∈ M ∩ B, by hypothesis (trace is cyclic). A function vanishing on M ∩ B has vanishing derivative within M; by (E) all its derivatives along tangent fields vanish. So H_{;a} = 0, and H_{;ab} = E_b(E_aH) − (∇_{E_b}E_a)H = 0, because E_aH also vanishes on M ∩ B.

Part III. Conclusion. At x₀, II.7 and II.8 give ½(|A|²)_{;cc}(x₀) = Σ h²_{ab;c}(x₀) − (|A|²(x₀))². By (B3), (B1) and (B2), Δ_M|A|²(x₀) = 2|∇A|²(x₀) − 2(|A|²(x₀))². x₀ ∈ M was arbitrary. This is the identity of the statement, Σ_j fderivWithin ℝ (fun y => fderivWithin ℝ |A|² M y (P_ye_j)) M x (P_xe_j) = 2|∇A|²(x) − 2(|A|²(x))², with |A|² as defined. (Numerical check, not part of the proof: with ν = ∇F/|∇F| for the minimal catenoid x²+y² = cosh²z and for the Clifford cone x₁²+x₂² = x₃²+x₄², also inside A₀ ⊊ ℝ⁵, both sides agree.) ∎

## Key steps

1. Ambient C^∞ extensions (P_y = Π − ν⊗ν on M) and tangent_fderiv make all tangential derivatives derivatives of ambient smooth maps.
2. A C^∞ orthonormal tangent frame E_a near x₀; Levi-Civita connection ∇ = P∘D, Gauss formula D_XY = ∇_XY + h(X,Y)ν, torsion-freeness, flatness of ℝ^P.
3. Bridges: h_{ab;c} = −(D_{E_c}C)(E_a)·E_b, so |∇A|² = Σh²_{ab;c}; |A|² = Σh_ab²; Δ_M = Σ_c (·)_{;cc} (Hilbert–Schmidt identities).
4. B.4 symmetry, Codazzi (codazzi sibling), Gauss B.6, Ricci identity B.7 (fixed sign convention) ⇒ Σ_c(h_{ca;bc} − h_{ca;cb}) = H(h²)_ab − |A|²h_ab.
5. h_{ab;cc} = H_{;ab} + H(h²)_ab − |A|²h_ab, contraction gives B.8; H ≡ 0 on M kills the H-terms: ½Δ_M|A|² = |∇A|² − |A|⁴.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; sha256sum local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD`
- `rg -n 'Simons|Codazzi|Laplace|second fundamental' project/GMT`
- `rg -n 'def tangentSpace|def IsEmbeddedSubmanifold' project/GMT/Ch07/Contract.lean`
- `rg -n 'theorem HasFDerivWithinAt.unique_on|theorem DifferentiableWithinAt.hasFDerivWithinAt|mem_tangentConeAt_of_seq|irreducible_def tangentConeAt|irreducible_def fderivWithin' mathlib/Mathlib/Analysis/Calculus`
- `rg -n 'hausdorffMeasure_smul₀|hausdorffMeasure_image_le|EuclideanSpace.euclideanHausdorffMeasure_eq_volume' mathlib/Mathlib`
- `rg -n '^theorem|^lemma' mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `rg -n 'isSymmSndFDerivAt|exists_orthonormalBasis_extension|ContDiffOn.fderiv_of_isOpen|exists_contDiff_support_eq_eq_one_iff|eq_starProjection_of_mem_of_inner_eq_zero|eq_of_le_of_finrank_eq|IsLocalMin.hasDerivAt_eq_zero|tendsto_integral_of_dominated_convergence|ContinuousOn.aestronglyMeasurable|ae_restrict_iff' mathlib/Mathlib`
- `rg -n 'def localInverse|theorem eventually_left_inverse|theorem to_localInverse' mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem`
- `rg -n 'theorem exists_smooth_tsupport_subset|theorem HasStrictFDerivAt.to_localInverse|theorem LocallyLipschitzOn' mathlib/Mathlib (no match under these exact names)`
- `grep -n 'theorem|def' simongmt/Poincare/SimonGMT/AppendixB/{SimonsInequalities,ConeDefect,LagrangeIdentity}.lean; lean Avail.lean: #check Poincare.SimonGMT.AppendixB.cone_simonsDefect_lower_bound after import GMT.Ch07.Submission`
- `python3 scans of dag.json (nodes under hypercone_plane-a1, statuses and frozen types of chart_tangentSpace_eq_range_fderiv, dimred_rpd_submanifold_density_one, codim1_hcp_lipschitz_smooth_approx, codim1_hcp_smooth_charts); grep -c codim1_hcp_sc dag.json; git log --all -S codim1_hcp_sc -- GMT`
- `lean -DautoImplicit=false /tmp/simons-cone-split/check/{Parent,TypesAll,Assembly,Inst}.lean with LEAN_PATH = .lake/build/lib/lean plus every package's .lake/build/lib/lean`
- `python3 verifier/lean_contract.py validate_lean_statement on all 12 child types`
- `/tmp/simons-cone-venv/env/bin/python -I /tmp/simons-cone-split/scripts/jets.py {clifford,more} and generic2.py {ell,gen3,cubic}`
- `book/chapter-B.txt lines 1–282 (B.1–B.11 and proof of B.2)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/TangentCone/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/AppendixB/ConeDefect.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/AppendixB/SimonsInequalities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/AppendixB/LagrangeIdentity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-a3c4818ec8/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-b5d5990773/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-B.txt`
- `/tmp/simons-cone-split/check/TypesAll.lean`
- `/tmp/simons-cone-split/check/Assembly.lean`
- `/tmp/simons-cone-split/check/Inst.lean`
- `/tmp/simons-cone-split/scripts/jets.py`

Pins match. The snapshot manifest records project b4d606db and Mathlib 25730c7c; these equal the workspace HEAD and .lake/packages/mathlib (simongmt is at 2b366308). The snapshot's project/GMT/Ch07/Contract.lean, the workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f9503aa28…).

Project: there is no Simons, Codazzi or Laplace–Beltrami development. rg finds only the Ch02 B_y doc-comment, the Ch07 'Simons cone' remark and README pointers to the AppendixB numerics. tangentSpace (Contract.lean:228) and IsEmbeddedSubmanifold (:221) are the definitions used.

Mathlib snapshot: it contains every library fact the child proofs cite.
- HasFDerivWithinAt.unique_on (FDeriv/Basic.lean:159) and DifferentiableWithinAt.hasFDerivWithinAt (:391); the fderivWithin definition (FDeriv/Defs.lean:151); mem_tangentConeAt_of_seq (TangentCone/Defs.lean:96).
- Measure.hausdorffMeasure_smul₀ (Hausdorff.lean:753); LipschitzOnWith.hausdorffMeasure_image_le (:733); LipschitzOnWith.ae_differentiableWithinAt_of_mem (Rademacher.lean:361); EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Geometry/Euclidean/Volume/Measure.lean:187).
- ContDiffAt.isSymmSndFDerivAt (FDeriv/Symmetric.lean:533); Orthonormal.exists_orthonormalBasis_extension (PiL2.lean:1031); ContDiffOn.fderiv_of_isOpen (ContDiff/Defs.lean:907); exists_contDiff_support_eq_eq_one_iff (PartitionOfUnity.lean:789); HasStrictFDerivAt.localInverse, eventually_left_inverse and to_localInverse (InverseFunctionTheorem/FDeriv.lean:149–186).
- Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Projection/Basic.lean:180); Submodule.eq_of_le_of_finrank_eq (FiniteDimensional/Basic.lean:257); IsLocalMin.hasDerivAt_eq_zero (LocalExtr/Basic.lean:237); tendsto_integral_of_dominated_convergence (DominatedConvergence.lean:57); ae_restrict_iff' (Restrict.lean:629).
- No match for theorems named exists_smooth_tsupport_subset or HasStrictFDerivAt.to_localInverse. The proofs use exists_contDiff_support_eq_eq_one_iff and the namespaced inverse-function lemmas instead.

SimonGMT: AppendixB supplies the B.10–B.11 algebra (ConeDefect.lean:136–228, LagrangeIdentity.lean:122) and ε = 1/10 (SimonsInequalities.lean:88). However, #check of cone_simonsDefect_lower_bound after import GMT.Ch07.Submission gives Unknown identifier. Child statements therefore avoid it, and cone_defect's proof notes the extra import and includes the printed algebra.

DAG: chart_tangentSpace_eq_range_fderiv is accepted (candidate d626082a69a0) and is reused with an identical type. lipschitz_approx and smooth_charts are unaccepted children of this node's parent, so they cannot be reused here. lipschitz_approx's exact conclusion is passed as hypothesis (HL), and density one as a hypothesis; the parent discharges both from its own resolved dependencies. The codim1_hcp_sc_ names are free in dag.json, in the git history and in all reference trees.

Lean: all 12 types elaborate (TypesAll, exit 0), and the parent's frozen type is kernel-checked from them (Assembly, exit 0).


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
