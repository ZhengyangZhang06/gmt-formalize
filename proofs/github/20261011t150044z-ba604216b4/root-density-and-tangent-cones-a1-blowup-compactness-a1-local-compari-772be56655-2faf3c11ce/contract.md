<!-- theorem-id: gmt-ch07/root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.coarea-a1 -->

## Theorem `Submission.dtc_bc_lc_sl_coarea`

Let P, n ∈ ℕ, let M ⊆ ℝ^P be Borel and countably (n+1)-rectifiable with H^{n+1}(M ∩ K) < ∞ for every compact K (Hᵏ = μHE[k]), and let f : ℝ^P → ℝ be L-Lipschitz. Then there is a Borel map G : ℝ^P → ℝ^P (Simon's ∇^M f) with |G(x)| ≤ L for every x such that: (1) (tangential gradient) for H^{n+1}-a.e. x ∈ M, M has an approximate tangent space at x, namely T_xM := approxTangentPlane (n+1) M x, G(x) ∈ T_xM, and for every ε > 0, r^{−(n+1)}·H^{n+1}({y ∈ M ∩ B_r(x) : |f(y) − f(x) − ⟨G(x), y − x⟩| > ε|y − x|}) → 0 as r ↓ 0; (2) (co-area) for every Borel g : ℝ^P → [0, ∞], t ↦ ∫_{M∩f⁻¹(t)} g dHⁿ is L¹-a.e.-measurable and ∫_ℝ ∫_{M∩f⁻¹(t)} g dHⁿ dt = ∫_M |G| g dH^{n+1}; (3) (slices) for L¹-a.e. t, M ∩ f⁻¹(t) is countably n-rectifiable, and for Hⁿ-a.e. x ∈ M ∩ f⁻¹(t): G(x) ≠ 0 and M ∩ f⁻¹(t) has approximate tangent space T_xM ∩ G(x)^⊥ at x.

Node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.coarea-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5385

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6068, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6075, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6031, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4196

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/7060, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7069, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7071, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7077, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7082, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7086, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7089, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7091, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4196, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5405, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1255

## Lean problem

Declaration: `Submission.dtc_bc_lc_sl_coarea`

```lean
∀ (P n : ℕ) (M : Set (Euclid P)) (f : Euclid P → ℝ) (L : NNReal), MeasurableSet M → CountablyRectifiable (n + 1) M → (∀ K : Set (Euclid P), IsCompact K → μHE[n + 1] (M ∩ K) ≠ ∞) → LipschitzWith L f → ∃ G : Euclid P → Euclid P, Measurable G ∧ (∀ x, ‖G x‖ ≤ L) ∧ (∀ᵐ x ∂(μHE[n + 1].restrict M), HasApproximateTangentSpaceAt (n + 1) M x (approxTangentPlane (n + 1) M x) ∧ G x ∈ approxTangentPlane (n + 1) M x ∧ ∀ ε : ℝ, 0 < ε → Tendsto (fun r : ℝ => μHE[n + 1] (M ∩ ball x r ∩ {y | ε * ‖y - x‖ < |f y - f x - inner ℝ (G x) (y - x)|}) / ENNReal.ofReal (r ^ (n + 1))) (𝓝[>] 0) (𝓝 0)) ∧ (∀ g : Euclid P → ℝ≥0∞, Measurable g → AEMeasurable (fun t => ∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂μHE[n]) ∧ ∫⁻ t, ∫⁻ x in M ∩ f ⁻¹' {t}, g x ∂μHE[n] = ∫⁻ x in M, ENNReal.ofReal ‖G x‖ * g x ∂μHE[n + 1]) ∧ ∀ᵐ t, CountablyRectifiable n (M ∩ f ⁻¹' {t}) ∧ ∀ᵐ x ∂(μHE[n].restrict (M ∩ f ⁻¹' {t})), G x ≠ 0 ∧ HasApproximateTangentSpaceAt n (M ∩ f ⁻¹' {t}) x (approxTangentPlane (n + 1) M x ⊓ (ℝ ∙ G x)ᗮ)
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

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.coarea-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 6, Lemma 4.1 and its printed proof (chapter-06.txt lines 1156–1195, printed p. 154): "(1) is just a restatement of 2.10(2) of Ch. 3, and (2) follows from 1.6 of Ch. 3 together with the facts that … ∇^M f(x) ∈ T_xM … and ⟨∇^M f(x), τ⟩ = 0 ∀ τ ∈ T_xM_t … The last part of the lemma is just a restatement of the appropriate version of the co-area formula". The cited Ch. 3 results are 2.1 (∇^M f(y) := ∇^{N_j} f(y) on M_j ⊆ N_j), 2.8–2.9 ("this follows from the C¹ case (§6 of Ch. 2) by using the decomposition M = ⋃ M_j of Remark 1.3 and the C¹ Approximation Theorem 1.5 of Ch. 2") and 2.10(2) (chapter-03.txt lines 327–445). These printed arguments are followed:
 - the decomposition into C¹ pieces with C¹ representatives of f is the sibling chart_pieces;
 - the C¹ case on one piece is the sibling chart_coarea;
 - the null part of the decomposition is handled by Eilenberg's inequality (sibling eilenberg; Simon uses the "easily checked fact" that null sets have null images in the proof of 2.4);
 - locality of approximate tangent spaces is im_calculus (a) (called TL; used with U = ℝ^P).
Here M_t is all of M ∩ f⁻¹(t), not Simon's M₊ ∩ f⁻¹(t); by (2) the two differ by an Hⁿ-null set for a.e. t. The tangential gradient is characterised in (1) by approximate differentiability along M. This is the form in which the siblings lipschitz_leibniz and slice_family use it.

Notation. N := n + 1, Hᵏ := μHE[k]. B_r(x) := ball(x, r). For a set S and a point x, η_{x,r}(S) := r⁻¹(S − x) (SimonGMT blowUpMap).

1. Pieces. Apply chart_pieces to (M, f), obtaining ψ_j, V_j, Y_j, F_j (j ∈ ℕ). Put A_j := ψ_j(Y_j) (Borel, pairwise disjoint, ⊆ M) and M₀ := M ∖ ⋃_j A_j (Borel, H^N(M₀) = 0).
 - For y ∈ Y_j write B_{j,y} := Dψ_j(y) and Q_j(y) := B_{j,y}(ℝ^N). M has approximate tangent space Q_j(y) at ψ_j(y). By uniqueness (SimonGMT `HasApproximateTangentSpaceAt.unique`), approxTangentPlane N M (ψ_j(y)) = Q_j(y), and M has approximate tangent space approxTangentPlane N M x at every x ∈ ⋃_j A_j.
 - Bi-Lipschitz charts. Let Ȳ_j := closure(Y_j), compact ⊆ V_j. There are 0 < m_j ≤ Λ_j with m_j|a − b| ≤ |ψ_j(a) − ψ_j(b)| ≤ Λ_j|a − b| for a, b ∈ Ȳ_j.
  Upper bound: Ȳ_j lies in a closed ball, on which ‖Dψ_j‖ is bounded (ψ_j is C¹ on ℝ^N); apply the mean value inequality.
  Lower bound, by contradiction: if a_k ≠ b_k in Ȳ_j with |ψ_j(a_k) − ψ_j(b_k)| < k⁻¹|a_k − b_k|, pass to a subsequence with a_k → a, b_k → b and (a_k − b_k)/|a_k − b_k| → e, |e| = 1. If a ≠ b, then ψ_j(a) = ψ_j(b), contradicting injectivity on V_j. If a = b, write ψ_j(a_k) − ψ_j(b_k) = ∫₀¹ Dψ_j(b_k + τ(a_k − b_k))(a_k − b_k) dτ on a closed ball around a inside V_j and let k → ∞ to get Dψ_j(a)e = 0, contradicting injectivity of Dψ_j(a).
  Hence ψ_j|_{Ȳ_j} is a homeomorphism onto its image, with continuous inverse.

2. Definition of G (Simon's 2.1). For x = ψ_j(y) ∈ A_j put g_j(x) := B_{j,y}(B_{j,y}*B_{j,y})⁻¹∇F_j(y). This is the unique vector of Q_j(y) with ⟨g_j(x), B_{j,y}e⟩ = DF_j(y)e for all e ∈ ℝ^N, and g_j is Borel on A_j (continuous in y, composed with the continuous inverse chart).
 (a) |g_j| ≤ L at H^N-a.e. point of A_j.
  - Let y ∈ Y_j be a Lebesgue density point of Y_j; L^N-a.e. point of Y_j is one (Mathlib `Besicovitch.ae_tendsto_measure_inter_div`). Let e be a unit vector.
  - There are y_k ∈ Y_j with y_k → y and (y_k − y)/|y_k − y| → e. Otherwise, for some δ ∈ (0, 1), the truncated cone C_δ := {y' : 0 < |y' − y| < δ, ⟨y' − y, e⟩ > (1 − δ)|y' − y|} does not meet Y_j. C_δ ∩ B_r(y) occupies a fixed fraction c_δ > 0 of L^N(B_r(y)) for every r < δ (scaling), so L^N(Y_j ∩ B_r(y)) ≤ (1 − c_δ)L^N(B_r(y)), contradicting density 1 at y.
  - Since F_j = f∘ψ_j on Y_j, |F_j(y_k) − F_j(y)| ≤ L|ψ_j(y_k) − ψ_j(y)|. Dividing by |y_k − y| and letting k → ∞ gives |DF_j(y)e| ≤ L|B_{j,y}e|. Hence |⟨g_j(x), v⟩| ≤ L|v| for v ∈ Q_j(y), and v = g_j(x) gives |g_j(x)| ≤ L.
  - The non-density points form an L^N-null subset of Y_j, whose ψ_j-image is H^N-null (ψ_j is Lipschitz on Y_j).
  So the Borel set {y ∈ Y_j : |g_j(ψ_j(y))| > L} is L^N-null. Remove it from Y_j; its image goes into M₀, which remains H^N-null. Keep the names A_j, Y_j; all properties of step 1 persist.
 (b) Put G(x) := g_j(x) for x ∈ A_j and G(x) := 0 for x ∉ ⋃_j A_j. Then G is Borel and |G| ≤ L everywhere. For every j and y ∈ Y_j: G(ψ_j(y)) ∈ Q_j(y) and ⟨G(ψ_j(y)), B_{j,y}e⟩ = DF_j(y)e for all e. These are the hypotheses of chart_coarea for (ψ_j, V_j, Y_j, F_j, G). Also G(x) ∈ Q_j(y) = approxTangentPlane N M x.

3. Conclusion (1). Fix j.
 (a) Density of M ∖ A_j. By TL for the Borel pair A_j ⊆ M (M locally H^N-finite), for H^N-a.e. x ∈ A_j the sets A_j and M have the same approximate tangent spaces at x. So A_j has approximate tangent space T := approxTangentPlane N M x at x. Take φ ∈ C_c(ℝ^P) with 0 ≤ φ ≤ 1 and φ = 1 on closedBall(0, 1). Since η_{x,r} maps B_r(x) into closedBall(0, 1) and multiplies H^N by r^{−N}, and η_{x,r}(M) is the disjoint union of η_{x,r}(A_j) and η_{x,r}(M ∖ A_j):
  r^{−N}H^N((M ∖ A_j) ∩ B_r(x)) ≤ ∫_{η_{x,r}(M)} φ dH^N − ∫_{η_{x,r}(A_j)} φ dH^N → ∫_T φ − ∫_T φ = 0 as r ↓ 0.
 (b) First-order expansion along A_j. Let x = ψ_j(y), y ∈ Y_j, and ε > 0. For y' ∈ Y_j,
  f(ψ_j(y')) − f(x) = F_j(y') − F_j(y) = DF_j(y)(y' − y) + o(|y' − y|), and
  ⟨G(x), ψ_j(y') − x⟩ = ⟨G(x), B_{j,y}(y' − y)⟩ + o(|y' − y|) = DF_j(y)(y' − y) + o(|y' − y|),
  by differentiability of F_j and ψ_j at y and step 2(b). Since |y' − y| ≤ m_j⁻¹|ψ_j(y') − x|, and y' → y when ψ_j(y') → x (continuity of the inverse chart), there is r₀ > 0 with |f(x') − f(x) − ⟨G(x), x' − x⟩| ≤ ε|x' − x| for all x' ∈ A_j ∩ B_{r₀}(x).
 (c) Hence for r < r₀ the exceptional set {x' ∈ M ∩ B_r(x) : |f(x') − f(x) − ⟨G(x), x' − x⟩| > ε|x' − x|} is contained in (M ∖ A_j) ∩ B_r(x), whose H^N-measure is o(r^N) by (a). With step 1 (T_xM exists and equals Q_j(y)) and step 2(b) (G(x) ∈ T_xM), (1) holds at H^N-a.e. x ∈ A_j. Since H^N(M₀) = 0, (1) holds at H^N-a.e. x ∈ M.

4. Conclusion (2) (Ch. 3, 2.8–2.9). Let g ≥ 0 be Borel.
 - For each j, f∘ψ_j = F_j on Y_j, so A_j ∩ f⁻¹(t) = ψ_j(Y_j ∩ F_j⁻¹(t)). By chart_coarea (i), t ↦ ∫_{A_j∩f⁻¹(t)} g dHⁿ is a.e.-measurable and ∫_ℝ ∫_{A_j∩f⁻¹(t)} g dHⁿ dt = ∫_{A_j} |G| g dH^N.
 - eilenberg with A := M₀ (H^N(M₀) = 0) gives a Borel φ ≥ Hⁿ(M₀ ∩ f⁻¹(·)) with ∫φ ≤ C·L·0 = 0. So Hⁿ(M₀ ∩ f⁻¹(t)) = 0 for a.e. t.
 - For such t, M ∩ f⁻¹(t) is the disjoint union of the Borel sets A_j ∩ f⁻¹(t) and the Hⁿ-null set M₀ ∩ f⁻¹(t). By countable additivity, ∫_{M∩f⁻¹(t)} g dHⁿ = Σ_j ∫_{A_j∩f⁻¹(t)} g dHⁿ.
 - So t ↦ ∫_{M∩f⁻¹(t)} g dHⁿ is a.e. equal to a countable sum of a.e.-measurable functions, hence a.e.-measurable. By monotone convergence, ∫_ℝ ∫_{M∩f⁻¹(t)} g dHⁿ dt = Σ_j ∫_{A_j} |G| g dH^N = ∫_M |G| g dH^N, the last step because H^N(M₀) = 0.

5. Conclusion (3) (Lemma 4.1 (1), (2); Ch. 3, 2.10(2)). For each j, by chart_coarea (ii), for a.e. t the set S_{j,t} := A_j ∩ f⁻¹(t) = ψ_j(Y_j ∩ F_j⁻¹(t)) is countably n-rectifiable, and for Hⁿ-a.e. x = ψ_j(y) ∈ S_{j,t}: G(x) ≠ 0 and S_{j,t} has approximate tangent space Q_j(y) ∩ G(x)^⊥ at x.
 - By (2) with g := 1_{closedBall(0,k)}: ∫_ℝ Hⁿ(M ∩ f⁻¹(t) ∩ closedBall(0, k)) dt ≤ L·H^N(M ∩ closedBall(0, k)) < ∞ for every k ∈ ℕ. So for a.e. t, M ∩ f⁻¹(t) is locally Hⁿ-finite.
 - Let t lie in the intersection of the countably many full-measure sets above and of {t : Hⁿ(M₀ ∩ f⁻¹(t)) = 0} (step 4).
 - Rectifiability. M ∩ f⁻¹(t) ⊆ (M₀ ∩ f⁻¹(t)) ∪ ⋃_j S_{j,t}, so it is countably n-rectifiable (SimonGMT `countablyRectifiable_of_measure_zero`, `countablyRectifiable_iUnion`, `CountablyRectifiable.mono`).
 - Tangent planes. For each j, TL (dimension n) for the Borel pair S_{j,t} ⊆ M ∩ f⁻¹(t) (the latter Borel and locally Hⁿ-finite): for Hⁿ-a.e. x ∈ S_{j,t}, M ∩ f⁻¹(t) and S_{j,t} have the same approximate tangent spaces at x. With the above and Q_j(y) = approxTangentPlane N M x (step 1): for Hⁿ-a.e. x ∈ S_{j,t}, G(x) ≠ 0 and M ∩ f⁻¹(t) has approximate tangent space approxTangentPlane N M x ⊓ (span G(x))^⊥ at x.
 - Since M ∩ f⁻¹(t) = (M₀ ∩ f⁻¹(t)) ∪ ⋃_j S_{j,t} with the first set Hⁿ-null, this holds for Hⁿ-a.e. x ∈ M ∩ f⁻¹(t). ∎

## Key steps

1. chart_pieces: M = M₀ ∪ ⨆_j ψ_j(Y_j), H^{n+1}(M₀) = 0, f∘ψ_j = F_j C¹ on Y_j, T_{ψ_j y}M = Dψ_j(y)(ℝ^{n+1}).
2. Define G = ∇^M f piecewise by G(ψ_j y) = Dψ_j(Dψ_j*Dψ_j)⁻¹∇F_j(y) (Simon 2.1); |G| ≤ L at density points (remove a null set); G Borel.
3. Approximate differentiability (1): TL makes M∖A_j of density zero at a.e. point of A_j, and f is C¹ along the chart.
4. Co-area (2): sum chart_coarea (i) over the pieces; the null part contributes nothing by eilenberg.
5. Slices (3): chart_coarea (ii) on each piece, local finiteness from (2), and TL to pass from S_{j,t} to M ∩ f⁻¹(t).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD in the snapshot project (b4d606db1) and mathlib (25730c7c); diff snapshot GMT/Ch07/Contract.lean against the workspace Contract.lean and Submission.lean (identical; Submission is a byte copy)`
- `grep -rn 'coarea\|co_area\|CoArea\|Coarea' Poincare/SimonGMT (only Chapter02/CoareaLinear*.lean, CoareaProjection.lean: linear co-area 6.1–6.2)`
- `grep -n '^theorem\|^def' on SimonGMT Chapter02/{AreaFormula,AreaLipschitz,AreaCritical,AreaNoninjective,WeightedArea,AreaLinearWeighted,WhitneyExtension,WhitneyJet,Lipschitz,LipschitzMeasurability,UpperIntegral,Submanifold,SubmanifoldCalculus}.lean, Chapter01/Lusin.lean, Chapter03/{Rectifiable,Differential,SubmanifoldCover,DisjointCover,CoordinateProjection}.lean`
- `grep 'Eilenberg\|1\.9' and 'theorem.*[Ll]usin' in SimonGMT and Mathlib (no Eilenberg inequality; Lusin only as SimonGMT IsBorelRegularOuterMeasure.exists_isClosed_continuousOn)`
- `grep in snapshot mathlib for tendstoUniformlyOn_of_ae_tendsto, exists_measurable_superset_of_null, measurable_fderiv, integral_lineDeriv_mul_eq, LocallyIntegrable.ae_hasDerivAt_integral, lintegral_image_eq_lintegral_abs_det_fderiv_mul, Real.volume_le_diam, hausdorffMeasure_apply, ae_tendsto_measure_inter_div, LipschitzOnWith.extend_real, Integrable.exists_hasCompactSupport_integral_sub_le, ContDiffAt.toOpenPartialHomeomorph, OpenPartialHomeomorph.contDiffAt_symm, AlternatingMap.eq_smul_basis_det, EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp, measurePreserving_piFinSuccAbove; sed Mathlib/Geometry/Euclidean/Volume/Measure.lean (μHE[d] = addHaarScalarFactor • μH[d])`
- `python3 -I scans of dag.json (995 nodes) for slic|coarea|Lusin|C¹ approximation|approximate tangent|tangential gradient: dor_lmb_slicing_lipschitz and its children (speculative/decomposing), cmc_slice_mass_bounds (speculative-ready) with accepted cmcs_* children, codim1_rdo_c1_approximation (waiting-children), codim1_rdo_c1_piece_approxTangent (speculative-lean), codim1_rdo_rectifiable_ae_approxTangent (speculative-ready), codim1_rdo_c1cov_lipschitz_range_c1_cover (rlcr-lean), dimred_cs_sos_spine_coarea, idtp_carrier_area_formula, dpf_area_formula_bilipschitz_rectifiable (none accepted)`
- `git show <accepted candidate commit>:GMT/Ch07/Submission.lean and whitespace-normalised comparison for cmc_imRep_locality_restrict_sub (2af75d6), cmcs_cd_defect_identity (e32f0ad), cmcs_lipschitz_smoothing (00c458d): all IDENTICAL`
- `grep -c dtc_bc_lc_sl_ dag.json (0); git log --all -S 'dtc_bc_lc_sl_' over 4526 refs (no match)`
- `lake env lean /tmp/dtcslice/Types.lean, /tmp/dtcslice/Check1.lean, /tmp/dtcslice/challenges/Challenge_<key>.lean (12 modules generated by verifier gmt-compare.py child_modules, contract mode, after lean_contract.validate_lean_statement) and /tmp/dtcslice/AssemblyFinal.lean with #print axioms`
- `sed book/chapter-06.txt lines 1140–1370 (Ch. 6 §4: 4.1–4.9); book/chapter-03.txt lines 1–170 and 320–460 (1.1–1.6, 2.1–2.10); book/chapter-02.txt lines 160–430 (1.5–1.10) and 1360–1640 (6.1–6.7)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-09907e06c7/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-comparison-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/CoareaLinear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaFormula.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLinearWeighted.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WhitneyJet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/UpperIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/DisjointCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Differential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/LebesgueDifferentiationThm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Egorov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/ContinuousMap/SecondCountableSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/dtcslice/Types.lean`
- `/tmp/dtcslice/AssemblyFinal.lean`
- `/tmp/dtcslice/challenges`

The pinned SimonGMT library has the linear co-area formula, the injective, weighted and noninjective Lipschitz area formulas, null critical images, Rademacher, Lusin, the C¹ Whitney extension and the upper integral. It has no nonlinear co-area formula, no C¹ approximation theorem (Simon 2.1.5), no Eilenberg inequality (2.1.9), no Lemma 1.2 'only if', no tangential gradient of Lipschitz functions on rectifiable sets and no slicing. Mathlib supplies Egorov, Lebesgue differentiation, integration by parts for Lipschitz functions, change of variables, the inverse function theorem and the μHE normalisation. No DAG node proving the co-area formula or slicing is accepted. The closest node, dor_lmb_slicing_lipschitz, is the same theorem for open U; it is speculative, and its decomposition was reviewed and accepted with three children. So the needed results become nine new children, with the unique prefix dtc_bc_lc_sl_. Three accepted declarations are reused with identical frozen types: cmc_imRep_locality_restrict_sub, cmcs_cd_defect_identity and cmcs_lipschitz_smoothing. All 12 types pass validate_lean_statement and elaborate in the comparator's contract-mode challenge modules. A Lean assembly derives the exact frozen type of dtc_bc_lc_slice from slice_family, slice_identity, im_calculus and dtc_mass_eq_measure, with axioms propext, Classical.choice and Quot.sound only.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
