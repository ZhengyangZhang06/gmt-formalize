<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.planar_constancy-a1.plane_constancy_reduction-a1 -->

## Theorem `Submission.idtp_pc_constancy_reduction`

Let P, n ∈ ℕ, V ⊆ ℝ^P open, τ = (τ_1, …, τ_n) an orthonormal family in ℝ^P, Q := span{τ_1, …, τ_n} with V ∩ Q connected, ι : ℝ^n → ℝ^P, ι(s) := Σ_i s_i τ_i, Ω := {s ∈ ℝ^n : ι(s) ∈ V}, H^n = μHE[n] and L^n = Lebesgue measure (volume) on ℝ^n. Let g : ℝ^P → ℝ satisfy: (i) g is a.e.-strongly measurable for H^n⌞Q; (ii) g(x) ∈ ℤ for H^n⌞Q-a.e. x; (iii) ∫_{K∩Q} |g| dH^n < ∞ for every compact K ⊆ V (|g| = ‖g‖ₑ, lower integral); (iv) ∫_{V∩Q} g(x)·Df(x)(τ_j) dH^n(x) = 0 for every C^∞ f : ℝ^P → ℝ with compact support and tsupport f ⊆ V and every j. Put h := g∘ι. Then (a) Ω is open; (b) Ω is preconnected; (c) h is locally integrable on Ω with respect to L^n; (d) ∫_{ℝ^n} h(s)·Dφ(s)(e_i) ds = 0 for every C¹ function φ : ℝ^n → ℝ with compact support and tsupport φ ⊆ Ω and every i, where e_i = EuclideanSpace.basisFun (Fin n) ℝ i; (e) for every c₀ ∈ ℝ with h(s) = c₀ for L^n-a.e. s ∈ Ω there is c ∈ ℤ with g(x) = c for H^n-a.e. x ∈ V ∩ Q.

Node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.planar_constancy-a1.plane_constancy_reduction-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4782

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5568, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5580, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2724

Decomposition children: None

## Lean problem

Declaration: `Submission.idtp_pc_constancy_reduction`

```lean
∀ (P n : ℕ) (V : Set (Euclid P)) (τ : Fin n → Euclid P) (g : Euclid P → ℝ), IsOpen V → Orthonormal ℝ τ → IsConnected (V ∩ (Submodule.span ℝ (Set.range τ) : Set (Euclid P))) → AEStronglyMeasurable g (μHE[n].restrict (Submodule.span ℝ (Set.range τ) : Set (Euclid P))) → (∀ᵐ x ∂(μHE[n].restrict (Submodule.span ℝ (Set.range τ) : Set (Euclid P))), ∃ m : ℤ, g x = m) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ V → ∫⁻ x in K ∩ (Submodule.span ℝ (Set.range τ) : Set (Euclid P)), ‖g x‖ₑ ∂μHE[n] ≠ ∞) → (∀ f : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → tsupport f ⊆ V → ∀ j : Fin n, ∫ x in V ∩ (Submodule.span ℝ (Set.range τ) : Set (Euclid P)), g x * fderiv ℝ f x (τ j) ∂μHE[n] = 0) → IsOpen {s : Euclid n | ∑ i, s i • τ i ∈ V} ∧ IsPreconnected {s : Euclid n | ∑ i, s i • τ i ∈ V} ∧ LocallyIntegrableOn (fun s : Euclid n => g (∑ i, s i • τ i)) {s : Euclid n | ∑ i, s i • τ i ∈ V} volume ∧ (∀ φ : Euclid n → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ {s : Euclid n | ∑ i, s i • τ i ∈ V} → ∀ i : Fin n, ∫ s, g (∑ k, s k • τ k) * fderiv ℝ φ s ((EuclideanSpace.basisFun (Fin n) ℝ) i) = 0) ∧ ∀ c₀ : ℝ, (∀ᵐ s ∂(volume.restrict {s : Euclid n | ∑ i, s i • τ i ∈ V}), g (∑ i, s i • τ i) = c₀) → ∃ c : ℤ, ∀ᵐ x ∂(μHE[n].restrict (V ∩ (Submodule.span ℝ (Set.range τ) : Set (Euclid P)))), g x = c
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

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.planar_constancy-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.planar_constancy-a1.plane_constancy_reduction-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 3, 6 (transfer to the parameter domain), 7 and the first half of 8 of the parent-supplied proof, except for the distributional constancy theorem itself: "Let Ω := ι^{−1}(V) ⊆ ℝ^n (open; ι restricts to a homeomorphism of Ω onto V ∩ Q, so Ω is connected and nonempty) and h := g∘ι ∈ L¹_loc(Ω) … 0 = ∂S(φ) = (−1)^{i−1}∫_Ω h(s)∂_iψ(s) ds by (3) and (5)"; "(If a library form of this fact tests against C¹_c functions, note that (6) extends from ψ ∈ C^∞_c(Ω) to ψ ∈ C¹_c(Ω) …) Since h takes integer values and h = c on a set of positive measure (Ω is open and nonempty), c ∈ ℤ"; "since ι maps L^n-null subsets of Ω onto H^n-null subsets of V ∩ Q (by (3)), g = c H^n-a.e. on V ∩ Q". Conclusions (a)–(d) are exactly the hypotheses of SimonGMT Poincare.SimonGMT.Chapter08.ae_eq_const_of_weak_coordinate_derivatives_zero (supplied step 7), which the parent applies (that module lies outside the import closure of the frozen contract, so its application stays in the parent); (e) then returns the integer constant on V ∩ Q. Notation: H^n := μHE[n], L^n := volume on ℝ^n; e_j = EuclideanSpace.single j 1 = EuclideanSpace.basisFun (Fin n) ℝ j; |g| := ‖g‖ₑ.
1. (Plane measure, supplied step 3.) By the sibling plane_measure_map (idtp_pc_plane_hausdorff_eq_map), H^n⌞Q = ι_#L^n. The map ι is an isometry (orthonormality: ‖ι(s)‖ = ‖s‖, ι linear), hence a closed embedding and therefore a measurable embedding (Isometry.isClosedEmbedding, IsClosedEmbedding.measurableEmbedding). Consequently, for every measurable A ⊆ ℝ^P:
 (1a) H^n⌞(A ∩ Q) = (H^n⌞Q)⌞A = ι_#(L^n⌞ι^{−1}(A)) (Measure.restrict_restrict, MeasurableEmbedding.restrict_map);
 (1b) ∫_{A∩Q} F dH^n = ∫_{ι^{−1}(A)} F(ι(s)) ds for every F : ℝ^P → ℝ (Bochner; MeasurableEmbedding.integral_map) and the same for lower integrals of F : ℝ^P → [0, ∞] (MeasurableEmbedding.lintegral_map);
 (1c) a property holds for H^n⌞(A ∩ Q)-a.e. x iff it holds at ι(s) for L^n⌞ι^{−1}(A)-a.e. s (MeasurableEmbedding.ae_map_iff);
 (1d) F is a.e.-strongly measurable for H^n⌞Q iff F∘ι is a.e.-strongly measurable for L^n (MeasurableEmbedding.aestronglyMeasurable_map_iff).
2. ((a) Ω is open.) Ω = ι^{−1}(V) with ι continuous and V open.
3. ((b) Ω is preconnected.) Let ι* : ℝ^P → ℝ^n, ι*(y) := (⟨τ_1, y⟩, …, ⟨τ_n, y⟩) (continuous). Every y ∈ Q has the form y = Σ_i c_iτ_i, and then ⟨τ_k, y⟩ = c_k, so y = ι(ι*(y)); also ι*(ι(s)) = s and ι(s) ∈ Q for all s. Hence ι*(V ∩ Q) = Ω: if y ∈ V ∩ Q then ι(ι*(y)) = y ∈ V, i.e. ι*(y) ∈ Ω; if s ∈ Ω then ι(s) ∈ V ∩ Q and ι*(ι(s)) = s. As V ∩ Q is connected and ι* is continuous, Ω = ι*(V ∩ Q) is connected (IsPreconnected.image), in particular preconnected and nonempty.
4. ((c) local integrability.) By (i) and (1d), h = g∘ι is a.e.-strongly measurable for L^n. Let K' ⊆ Ω be compact. Then ι(K') is compact with ι(K') ⊆ V, measurable (closed), and ι^{−1}(ι(K')) = K' (ι is injective). By (1b) with A := ι(K') and (iii): ∫_{K'} |h| dL^n = ∫_{ι(K')∩Q} |g| dH^n < ∞. So h is integrable on every compact subset of the open set Ω, i.e. locally integrable on Ω (locallyIntegrableOn_iff, Ω being open, hence locally closed).
5. (Smooth tests; supplied step 6, last equality.) Let ψ : ℝ^n → ℝ be C^∞ with compact support and tsupport ψ ⊆ Ω, and let j be an index. By the sibling plane_test_extension (idtp_pc_plane_test_extension) there is a C^∞ f : ℝ^P → ℝ with compact support, tsupport f ⊆ V and Df(ι(s))(τ_j) = Dψ(s)(e_j) for every s. By (1b) with A := V (open, hence measurable) and hypothesis (iv):
 ∫_Ω h(s)·Dψ(s)(e_j) ds = ∫_Ω g(ι(s))·Df(ι(s))(τ_j) ds = ∫_{V∩Q} g(x)·Df(x)(τ_j) dH^n(x) = 0.
6. ((d) C¹ tests; supplied step 7, parenthetical remark.) By the accepted sibling smooth_to_c1_tests (dgcr_smooth_tests_to_C1_tests), applied with D := Ω (open, step 2), G := h (locally integrable on Ω, step 4) and the identities of step 5, ∫_{ℝ^n} h(s)·Dφ(s)(e_i) ds = 0 for every C¹ function φ with compact support, tsupport φ ⊆ Ω and every i. [Reason, as in the supplied step 7: the mollifications φ_ε of φ are C^∞, have supports in a fixed compact subset of Ω for small ε, and ∂_iφ_ε → ∂_iφ uniformly, while h is integrable on that compact set; so ∫ h∂_iφ = lim ∫ h∂_iφ_ε = 0.]
7. ((e) integrality and transfer back; supplied steps 7 and 8.) Let c₀ ∈ ℝ with h = c₀ L^n-a.e. on Ω. By (ii) and (1c) (with A := ℝ^P), h(s) ∈ ℤ for L^n-a.e. s ∈ ℝ^n. Ω is open and nonempty (step 3), so L^n(Ω) > 0 (IsOpen.measure_pos); hence some s ∈ Ω satisfies both h(s) = c₀ and h(s) = m for an integer m (Measure.exists_mem_of_measure_ne_zero_of_ae). Put c := m ∈ ℤ; then c₀ = c, and g(ι(s)) = h(s) = c for L^n-a.e. s ∈ Ω = ι^{−1}(V). By (1a) and (1c) with A := V, g(x) = c for H^n⌞(V ∩ Q)-a.e. x, i.e. for H^n-a.e. x ∈ V ∩ Q. ∎

Formalization note (verified during the decomposition check; not part of the mathematical argument). The following single theorem proves exactly this frozen statement. It was compiled with `lake env lean` (Lean v4.35.0-rc3, Mathlib 25730c7c, SimonGMT 2b36630) after `import GMT.Ch07.Submission` only, inside `namespace GMT.Ch07` with the contract opens. It uses exactly the declared dependencies Submission.idtp_pc_plane_hausdorff_eq_map, Submission.idtp_pc_plane_test_extension, Submission.dgcr_smooth_tests_to_C1_tests (by these Submission.* names) and no import or helper declaration. In a build where those dependencies were sorry stubs, `#print axioms` showed only propext, Classical.choice and Quot.sound besides the stubs; in a fully merged build containing the dependencies' accepted code it gives exactly propext, Classical.choice and Quot.sound. It follows the numbered steps above and may be used directly as the leaf candidate:
```lean
theorem Submission.idtp_pc_constancy_reduction : ∀ (P n : ℕ) (V : Set (Euclid P)) (τ : Fin n → Euclid P) (g : Euclid P → ℝ), IsOpen V → Orthonormal ℝ τ → IsConnected (V ∩ (Submodule.span ℝ (Set.range τ) : Set (Euclid P))) → AEStronglyMeasurable g (μHE[n].restrict (Submodule.span ℝ (Set.range τ) : Set (Euclid P))) → (∀ᵐ x ∂(μHE[n].restrict (Submodule.span ℝ (Set.range τ) : Set (Euclid P))), ∃ m : ℤ, g x = m) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ V → ∫⁻ x in K ∩ (Submodule.span ℝ (Set.range τ) : Set (Euclid P)), ‖g x‖ₑ ∂μHE[n] ≠ ∞) → (∀ f : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → tsupport f ⊆ V → ∀ j : Fin n, ∫ x in V ∩ (Submodule.span ℝ (Set.range τ) : Set (Euclid P)), g x * fderiv ℝ f x (τ j) ∂μHE[n] = 0) → IsOpen {s : Euclid n | ∑ i, s i • τ i ∈ V} ∧ IsPreconnected {s : Euclid n | ∑ i, s i • τ i ∈ V} ∧ LocallyIntegrableOn (fun s : Euclid n => g (∑ i, s i • τ i)) {s : Euclid n | ∑ i, s i • τ i ∈ V} volume ∧ (∀ φ : Euclid n → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ {s : Euclid n | ∑ i, s i • τ i ∈ V} → ∀ i : Fin n, ∫ s, g (∑ k, s k • τ k) * fderiv ℝ φ s ((EuclideanSpace.basisFun (Fin n) ℝ) i) = 0) ∧ ∀ c₀ : ℝ, (∀ᵐ s ∂(volume.restrict {s : Euclid n | ∑ i, s i • τ i ∈ V}), g (∑ i, s i • τ i) = c₀) → ∃ c : ℤ, ∀ᵐ x ∂(μHE[n].restrict (V ∩ (Submodule.span ℝ (Set.range τ) : Set (Euclid P)))), g x = c := by
  intro P n V τ g hV hτ hconn hgm hgint hgloc hweak
  -- the parametrization ι and its basic properties
  let L : Euclid n →ₗ[ℝ] Euclid P :=
    { toFun := fun s => ∑ i, s i • τ i
      map_add' := fun s t => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c s => by simp [Finset.smul_sum, smul_smul] }
  have hLapp : ∀ s, L s = ∑ i, s i • τ i := fun s => rfl
  have hnorm : ∀ s, ‖L s‖ = ‖s‖ := by
    intro s
    have h1 : ‖L s‖ ^ 2 = ‖s‖ ^ 2 := by
      rw [hLapp, ← real_inner_self_eq_norm_sq, hτ.inner_sum, EuclideanSpace.norm_eq,
        Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
      simp [sq]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h1
  have hiso : Isometry L := AddMonoidHomClass.isometry_of_norm L hnorm
  have hcont : Continuous L := hiso.continuous
  have hemb : MeasurableEmbedding L := hiso.isClosedEmbedding.measurableEmbedding
  have hinj : Injective L := hiso.injective
  set Q : Set (Euclid P) := (Submodule.span ℝ (Set.range τ) : Set (Euclid P)) with hQ
  have hmap : (μHE[n] : Measure (Euclid P)).restrict Q = Measure.map L volume := Submission.idtp_pc_plane_hausdorff_eq_map P n τ hτ
  -- transfer of restricted measures
  have htr : ∀ A : Set (Euclid P), MeasurableSet A →
      (μHE[n] : Measure (Euclid P)).restrict (A ∩ Q) = Measure.map L (volume.restrict (L ⁻¹' A)) := by
    intro A hA
    rw [← Measure.restrict_restrict hA, hmap, hemb.restrict_map]
  set Ω : Set (Euclid n) := {s : Euclid n | ∑ i, s i • τ i ∈ V} with hΩ
  have hΩL : Ω = L ⁻¹' V := rfl
  have hΩo : IsOpen Ω := hV.preimage hcont
  -- the left inverse ι*
  let Ls : Euclid P → Euclid n := fun y => (WithLp.equiv 2 (Fin n → ℝ)).symm (fun k => inner ℝ (τ k) y)
  have hLscont : Continuous Ls := by
    refine (PiLp.continuous_toLp 2 _).comp ?_
    exact continuous_pi fun k => continuous_const.inner continuous_id
  have hLsL : ∀ s, Ls (L s) = s := by
    intro s
    ext k
    simp [Ls, hLapp, hτ.inner_right_fintype]
  have hrangeL : ∀ y ∈ Q, L (Ls y) = y := by
    intro y hy
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hy
    have : Ls (∑ i, c i • τ i) = (WithLp.equiv 2 (Fin n → ℝ)).symm c := by
      ext k
      simp [Ls, hτ.inner_right_fintype]
    rw [this]
    simp [hLapp]
  have hLmemQ : ∀ s, L s ∈ Q := by
    intro s
    rw [hLapp]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have himage : Ls '' (V ∩ Q) = Ω := by
    ext s
    constructor
    · rintro ⟨y, ⟨hyV, hyQ⟩, rfl⟩
      show L (Ls y) ∈ V
      rw [hrangeL y hyQ]; exact hyV
    · intro hs
      exact ⟨L s, ⟨hs, hLmemQ s⟩, hLsL s⟩
  have hΩc : IsPreconnected Ω := by
    rw [← himage]
    exact hconn.isPreconnected.image Ls hLscont.continuousOn
  -- measurability and local integrability of h = g ∘ L
  have hgm' : AEStronglyMeasurable (fun s => g (L s)) volume := by
    have : AEStronglyMeasurable g (Measure.map L volume) := hmap ▸ hgm
    exact (hemb.aestronglyMeasurable_map_iff).mp this
  have hloc : LocallyIntegrableOn (fun s : Euclid n => g (∑ i, s i • τ i)) Ω volume := by
    refine (locallyIntegrableOn_iff hΩo.isLocallyClosed).mpr fun k hkΩ hk => ?_
    refine ⟨hgm'.restrict, ?_⟩
    have hKc : IsCompact (L '' k) := hk.image hcont
    have hKV : L '' k ⊆ V := by
      rintro _ ⟨s, hs, rfl⟩; exact hkΩ hs
    have hfin := hgloc (L '' k) hKc hKV
    have h1 : ∫⁻ x in L '' k ∩ Q, ‖g x‖ₑ ∂μHE[n] = ∫⁻ s in k, ‖g (L s)‖ₑ := by
      rw [htr _ hKc.isClosed.measurableSet, hemb.lintegral_map, hinj.preimage_image]
    show ∫⁻ s in k, ‖g (L s)‖ₑ < ∞
    rw [← h1]
    exact lt_top_iff_ne_top.mpr hfin
  -- smooth tests
  have hsmooth : ∀ a : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) a → HasCompactSupport a → tsupport a ⊆ Ω →
      ∀ j : Fin n, ∫ v in Ω, g (∑ i, v i • τ i) * fderiv ℝ a v (EuclideanSpace.single j (1 : ℝ)) = 0 := by
    intro a ha hac has j
    obtain ⟨f, hf, hfc, hfV, hfa⟩ := Submission.idtp_pc_plane_test_extension P n V τ a hV hτ ha hac has
    have h0 := hweak f hf hfc hfV j
    have h2 : ∫ x in V ∩ Q, g x * fderiv ℝ f x (τ j) ∂μHE[n] =
        ∫ s in Ω, g (L s) * fderiv ℝ f (L s) (τ j) := by
      rw [htr V hV.measurableSet, hemb.integral_map]
      rfl
    rw [h2] at h0
    rw [← h0]
    refine setIntegral_congr_fun hΩo.measurableSet fun s _ => ?_
    simp only [hLapp] at *
    rw [(hfa s).2 j]
  refine ⟨hΩo, hΩc, hloc, Submission.dgcr_smooth_tests_to_C1_tests n Ω _ hΩo hloc hsmooth, ?_⟩
  -- back transfer
  intro c₀ hc₀
  have hne : Ω.Nonempty := by
    rw [← himage]; exact hconn.nonempty.image Ls
  have hint' : ∀ᵐ s ∂(volume : Measure (Euclid n)), ∃ m : ℤ, g (L s) = m := by
    have : ∀ᵐ x ∂(Measure.map L (volume : Measure (Euclid n))), ∃ m : ℤ, g x = m := hmap ▸ hgint
    exact (hemb.ae_map_iff).mp this
  have hpos : (volume : Measure (Euclid n)) Ω ≠ 0 := (hΩo.measure_pos volume hne).ne'
  obtain ⟨s, -, hs1, m, hm⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos
    (hc₀.and (ae_restrict_of_ae hint'))
  have hc : c₀ = m := hs1.symm.trans hm
  refine ⟨m, ?_⟩
  rw [show V ∩ Q = V ∩ Q from rfl, htr V hV.measurableSet, hemb.ae_map_iff]
  filter_upwards [hc₀] with s hs
  rw [← hc]; exact hs
```

## Key steps

1. H^n⌞Q = ι_#L^n (sibling plane_measure_map) and ι is a measurable embedding: transfer of restricted measures, integrals, a.e. statements and a.e.-measurability between V ∩ Q and Ω.
2. Ω = ι^{−1}(V) is open and Ω = ι*(V ∩ Q) is connected.
3. h = g∘ι is locally integrable on Ω: ∫_{K'}|h| = ∫_{ι(K')∩Q}|g| dH^n < ∞.
4. For ψ ∈ C^∞_c(Ω), extend to f (sibling plane_test_extension): ∫_Ω h ∂_jψ = ∫_{V∩Q} g D_{τ_j}f dH^n = 0; pass to C¹ tests (accepted dgcr_smooth_tests_to_C1_tests).
5. If h = c₀ a.e. on Ω, then c₀ ∈ ℤ (h integer a.e., L^n(Ω) > 0) and g = c₀ H^n-a.e. on V ∩ Q.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD (against manifest.json)`
- `python3 scan of dag.json: accepted nodes (status, lean_name, lean_statement, candidate_commit) for dimred_*, imrep_*, atsm_*, dgcr_*, dgid_*, dgoj_*, rsdic_*, regcomp_*; duplicate lean_names; cross-branch reuse precedents (children whose parent field differs)`
- `rg -n 'idtp_pc_' over dag.json, nodes/, the snapshot and all git refs (no match)`
- `git show <candidate>:GMT/Ch07/Submission.lean for 01ae2c59, d15b5cf4, 038573e4, d5e029d5, c1d60848, dcc3f4b7, 8a6855aa; diff against the contract (added declarations, imports, removed lines)`
- `grep -n theorem/def in .lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean, Chapter03/Rectifiable.lean, Chapter06/{Forms,Currents,Mass,CurrentLocalEquality}.lean`
- `rg -n 'Isometry.map_euclideanHausdorffMeasure|EuclideanSpace.euclideanHausdorffMeasure_eq_volume|exists_cthickening_subset_open|eq_of_le_of_finrank_eq|one_of_mem_closedBall' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `lake env lean /tmp/pc-decomp-k7q2/check/Probe2.lean and Names.lean (#check of the cited Mathlib/SimonGMT names after import GMT.Ch07.Submission; Chapter08 names unknown)`
- `lake env lean /tmp/pc-decomp-k7q2/check/{Types,Parent,Children}.lean and /tmp/pc-decomp-k7q2/merged/Merged.lean (#print axioms)`
- `sed -n 560,640p book/chapter-06.txt (Simon 2.34, Constancy Theorem and proof); sed -n 1830,1880p book/chapter-06.txt (deformation theorem (26)–(27))`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-77d7be4677/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-77d7be4677/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-im-mass-measure-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-im-mass-measure-a1/rlcr-plan-v1.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-regular-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/pc-decomp-k7q2/check/Types.lean`
- `/tmp/pc-decomp-k7q2/check/Parent.lean`
- `/tmp/pc-decomp-k7q2/check/Children.lean`
- `/tmp/pc-decomp-k7q2/merged/Merged.lean`

The pins match. The snapshot is project b4d606d (equal to workspace HEAD) with mathlib 25730c7c, and SimonGMT is 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

Reused accepted declarations. dimred_im_mass_measure, imrep_carrier_sdiff_support_null, atsm_approxTangent_le_of_flat, dgcr_unitOrientation_eq_or_neg, dgcr_smooth_tests_to_C1_tests and dgcr_bwd_coordinate_covector are comparator-accepted and are reused at byte-identical types. Their candidates only add pairwise-disjoint declarations to the contract.

Library support.
- Mathlib supplies Isometry.map_euclideanHausdorffMeasure and EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Geometry/Euclidean/Volume/Measure.lean:141,187).
- Mathlib also supplies IsCompact.exists_cthickening_subset_open, Submodule.eq_of_le_of_finrank_eq, the ContDiffBump API and the MeasurableEmbedding transfer lemmas, all inside the frozen import closure.
- SimonGMT supplies exteriorDerivative_apply (Chapter06/Forms.lean:119) and support_euclideanHausdorffMeasure_restrict_submodule (Chapter03).
- SimonGMT's ae_eq_const_of_weak_coordinate_derivatives_zero (Chapter08/DistributionalConstancy.lean) is outside the frozen import closure. It is applied in this node's parent proof with an added import, following the accepted precedent 8a6855aa.

Names. No idtp_pc_* name occurs anywhere.

Lean. All 12 child types elaborate. The exact parent type follows from three child types plus the SimonGMT theorem. Each new child has a verified single-theorem proof from its declared dependencies. A fully merged build with the reused accepted code has no sorry, and all seven new declarations depend only on propext, Classical.choice and Quot.sound.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
