<!-- theorem-id: gmt-ch07/root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_coarea-a1 -->

## Theorem `Submission.dtc_bc_lc_sl_chart_coarea`

Let P, n ∈ ℕ. Let ψ : ℝ^{n+1} → ℝ^P be C¹, V ⊆ ℝ^{n+1} open with ψ injective on V and Dψ(y) injective for y ∈ V, F : ℝ^{n+1} → ℝ C¹, and Y ⊆ ℝ^{n+1} Borel with closure(Y) compact and contained in V. Let G : ℝ^P → ℝ^P satisfy, for every y ∈ Y, G(ψ(y)) ∈ Dψ(y)(ℝ^{n+1}) and ⟨G(ψ(y)), Dψ(y)e⟩ = DF(y)e for all e ∈ ℝ^{n+1} (so G∘ψ is the gradient of F∘ψ⁻¹ along ψ(V)). Write Hᵏ = μHE[k]. Then: (i) for every Borel g : ℝ^P → [0, ∞], the function t ↦ ∫_{ψ(Y ∩ F⁻¹(t))} g dHⁿ is L¹-a.e.-measurable and ∫_ℝ ∫_{ψ(Y ∩ F⁻¹(t))} g dHⁿ dt = ∫_{ψ(Y)} |G| g dH^{n+1}; (ii) for L¹-a.e. t, the set S_t := ψ(Y ∩ F⁻¹(t)) is countably n-rectifiable, and for Hⁿ-a.e. x ∈ S_t we have G(x) ≠ 0 and, for the y ∈ Y with ψ(y) = x, S_t has approximate tangent space Dψ(y)(ℝ^{n+1}) ∩ G(x)^⊥ at x.

Node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_coarea-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5385

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6031, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6044, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4196

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6851, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6859, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6865, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6872, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6875, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6879, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6887, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6892, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6898

## Lean problem

Declaration: `Submission.dtc_bc_lc_sl_chart_coarea`

```lean
∀ (P n : ℕ) (ψ : Euclid (n + 1) → Euclid P) (V Y : Set (Euclid (n + 1))) (F : Euclid (n + 1) → ℝ) (G : Euclid P → Euclid P), IsOpen V → ContDiff ℝ 1 ψ → InjOn ψ V → (∀ y ∈ V, Injective (fderiv ℝ ψ y)) → ContDiff ℝ 1 F → MeasurableSet Y → IsCompact (closure Y) → closure Y ⊆ V → (∀ y ∈ Y, G (ψ y) ∈ LinearMap.range (fderiv ℝ ψ y : Euclid (n + 1) →ₗ[ℝ] Euclid P) ∧ ∀ e, inner ℝ (G (ψ y)) (fderiv ℝ ψ y e) = fderiv ℝ F y e) → (∀ g : Euclid P → ℝ≥0∞, Measurable g → AEMeasurable (fun t => ∫⁻ x in ψ '' (Y ∩ F ⁻¹' {t}), g x ∂μHE[n]) ∧ ∫⁻ t, ∫⁻ x in ψ '' (Y ∩ F ⁻¹' {t}), g x ∂μHE[n] = ∫⁻ x in ψ '' Y, ENNReal.ofReal ‖G x‖ * g x ∂μHE[n + 1]) ∧ ∀ᵐ t, CountablyRectifiable n (ψ '' (Y ∩ F ⁻¹' {t})) ∧ ∀ᵐ x ∂(μHE[n].restrict (ψ '' (Y ∩ F ⁻¹' {t}))), G x ≠ 0 ∧ ∀ y ∈ Y, ψ y = x → HasApproximateTangentSpaceAt n (ψ '' (Y ∩ F ⁻¹' {t})) x (LinearMap.range (fderiv ℝ ψ y : Euclid (n + 1) →ₗ[ℝ] Euclid P) ⊓ (ℝ ∙ G x)ᗮ)
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
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_coarea-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 2, §6: the co-area formula 6.3 for C¹ maps on C¹ submanifolds, its weighted form 6.6, and the Sard-type Theorem 6.4 (chapter-02.txt lines 1405–1530, printed pp. 65–67), here for the submanifold ψ(V) and the real-valued C¹ function F∘ψ⁻¹. Simon prints no proof of 6.3; he says it "uses an approximation argument based on the linear case 6.2" and refers to [Fed69] (Federer 3.2.11–3.2.12). For a real-valued C¹ function with nonvanishing gradient, the implicit function theorem reduces it to Fubini's theorem and the area formula. That standard argument is written out below. The critical set is treated with Eilenberg's inequality (sibling eilenberg), as in Federer 3.2.12. The level-set structure is Simon's 6.4 (f⁻¹(y) ∖ C is a C¹ submanifold) together with the proof of Ch. 3, 1.6 "⇒" (sibling c1_tangent and locality im_calculus (a), called TL).

Notation. N := n + 1; Hᵏ := μHE[k]; on ℝᵏ it equals Lebesgue measure Lᵏ. For y ∈ V let A_y := Dψ(y) (injective), J(y) := J(A_y) = √det(A_y*A_y) > 0, and Q(y) := A_y(ℝ^N). ∇F(y) is the gradient of F. Ȳ := closure(Y), compact ⊆ V. For a linear map B from a k-dimensional space, J(B) := √det(B*B).

0. Preliminaries on the chart.
 (a) Bi-Lipschitz. There are 0 < m ≤ Λ with m|a − b| ≤ |ψ(a) − ψ(b)| ≤ Λ|a − b| for a, b ∈ Ȳ.
  - Upper bound. Ȳ is compact, so Ȳ ⊆ closedBall(0, R₀) for some R₀. ψ is C¹ on all of ℝ^N, so Λ := sup_{closedBall(0,R₀)} ‖Dψ‖ < ∞, and the mean value inequality on this convex ball gives the bound.
  - Lower bound, by contradiction. Suppose there are a_k ≠ b_k in Ȳ with |ψ(a_k) − ψ(b_k)| < k⁻¹|a_k − b_k|. By compactness pass to a subsequence with a_k → a ∈ Ȳ, b_k → b ∈ Ȳ and e_k := (a_k − b_k)/|a_k − b_k| → e, |e| = 1.
   If a ≠ b, continuity gives ψ(a) = ψ(b), contradicting injectivity of ψ on V ⊇ Ȳ.
   If a = b, choose ρ > 0 with closedBall(a, ρ) ⊆ V. For large k, a_k, b_k ∈ closedBall(a, ρ) (convex), and ψ(a_k) − ψ(b_k) = ∫₀¹ Dψ(b_k + τ(a_k − b_k))(a_k − b_k) dτ. Dividing by |a_k − b_k| and using continuity of Dψ at a gives |Dψ(a)e| = lim_k |ψ(a_k) − ψ(b_k)|/|a_k − b_k| = 0, contradicting injectivity of Dψ(a).
  Hence ψ|_Ȳ is injective and continuous on a compact set, so it is a homeomorphism onto ψ(Ȳ) with continuous inverse. ψ maps Borel subsets of Y onto Borel sets (Mathlib `MeasurableSet.image_of_continuousOn_injOn`).
 (b) The vector G(ψ(y)). For y ∈ V put Ĝ(y) := A_y(A_y*A_y)⁻¹∇F(y); Ĝ is continuous on V, and Ĝ(y) is the unique vector of Q(y) with ⟨Ĝ(y), A_ye⟩ = DF(y)e for all e. (Writing a vector of Q(y) as A_y w, the condition ⟨A_y w, A_y e⟩ = ⟨∇F(y), e⟩ for all e says A_y*A_y w = ∇F(y).) So the hypotheses give G(ψ(y)) = Ĝ(y) for y ∈ Y. Consequences:
  - Ĝ(y) = 0 iff ∇F(y) = 0;
  - Γ := sup_{y∈Ȳ}|Ĝ(y)| < ∞ (continuity on the compact Ȳ), so |G| ≤ Γ on ψ(Y);
  - on ψ(Y), G = Ĝ∘(ψ|_Ȳ)⁻¹, which is Borel on ψ(Y) (continuous inverse chart of (a)).
 (c) Jacobian identity in the target. Let y ∈ V with ∇F(y) ≠ 0, K_y := ker DF(y) (dimension n), ν := ∇F(y)/|∇F(y)|, and J_K(y) := J(A_y|_{K_y}) (computed with an orthonormal basis of K_y). Then
  A_y(K_y) = Q(y) ∩ Ĝ(y)^⊥ and J_K(y)·|∇F(y)| = |Ĝ(y)|·J(y).
  Proof. Take an orthonormal basis (k_1, …, k_n) of K_y, so (ν, k_1, …, k_n) is orthonormal in ℝ^N. The N-volume of (A_yν, A_yk_1, …, A_yk_n) is J(y), and it equals J_K(y)·dist(A_yν, A_y(K_y)) (base times height). Put Ĝ := Ĝ(y); Ĝ ∈ Q(y), and ⟨Ĝ, A_yk⟩ = DF(y)k = 0 for k ∈ K_y, so Ĝ ⊥ A_y(K_y). Also ⟨Ĝ, A_yν⟩ = DF(y)ν = |∇F(y)| ≠ 0, so Ĝ ≠ 0. Since A_y(K_y) is n-dimensional in the (n+1)-dimensional Q(y), Q(y) ∩ Ĝ^⊥ = A_y(K_y), and dist(A_yν, A_y(K_y)) = |⟨A_yν, Ĝ⟩|/|Ĝ| = |∇F(y)|/|Ĝ|. Hence J(y) = J_K(y)|∇F(y)|/|Ĝ|. For y ∈ Y, Ĝ(y) = G(ψ(y)).

1. The critical part (Sard-type Theorem 6.4). Let Y_c := Y ∩ {∇F = 0}, a Borel set. On ψ(Y_c), G = Ĝ∘(ψ|_Ȳ)⁻¹ = 0 by 0(b). We show Hⁿ(Y_c ∩ F⁻¹(t)) = 0 for L¹-a.e. t.
 - Let Ȳ₁ := {w : dist(w, Ȳ) ≤ 1} (compact) and c₁ := L^N(Ȳ₁) < ∞. Let ε ∈ (0, 1]. By uniform continuity of DF on Ȳ₁ choose δ ∈ (0, 1] with ‖DF(w) − DF(w')‖ ≤ ε for w, w' ∈ Ȳ₁ with |w − w'| ≤ δ.
 - Take the half-open dyadic cubes of side s with s√N ≤ δ that meet Y_c, say (Q_l)_l. They are disjoint. Each lies within distance δ ≤ 1 of a point p_l ∈ Y_c, so Q_l ⊆ Ȳ₁ and ‖DF‖ ≤ ε on Q_l (as DF(p_l) = 0). Hence Σ_l L^N(Q_l) ≤ c₁, and F is ε-Lipschitz on each convex Q_l (mean value inequality).
 - By eilenberg (in ℝ^N, with A := Q_l ∩ Y_c and Lipschitz constant ε) there are Borel φ_l with Hⁿ(Q_l ∩ Y_c ∩ F⁻¹(t)) ≤ φ_l(t) and ∫φ_l ≤ C·ε·H^N(Q_l) = C·ε·L^N(Q_l).
 - Φ_ε := Σ_l φ_l is Borel, Hⁿ(Y_c ∩ F⁻¹(t)) ≤ Φ_ε(t) for every t (countable subadditivity), and ∫Φ_ε ≤ C·ε·c₁.
 - Put Φ := liminf_k Φ_{2^{−k}}. Then Hⁿ(Y_c ∩ F⁻¹(t)) ≤ Φ(t) for all t, and by Fatou ∫Φ ≤ liminf_k C2^{−k}c₁ = 0. So Φ = 0 a.e.
 Consequently, by 0(a), Hⁿ(ψ(Y_c ∩ F⁻¹(t))) ≤ Λⁿ·Hⁿ(Y_c ∩ F⁻¹(t)) = 0 for a.e. t (SimonGMT `euclideanHausdorffMeasure_image_le_of_lipschitzOn`).

2. Local straightening of F on the regular part.
 - Y_r := Y ∩ {∇F ≠ 0} is Borel. For y₀ ∈ V with ∇F(y₀) ≠ 0, let (u_1, …, u_n) be an orthonormal basis of ∇F(y₀)^⊥ and define the C¹ self-map Φ_{y₀} : ℝ^N → ℝ^N by Φ_{y₀}(y)_0 := F(y) and Φ_{y₀}(y)_i := ⟨u_i, y⟩ (i = 1, …, n), using the coordinates indexed by Fin (n+1) = {0, …, n}. We write Φ_{y₀}(y) = (F(y), π_{y₀}(y)) with π_{y₀}(y) := (⟨u_i, y⟩)_{i=1..n} ∈ ℝⁿ.
 - DΦ_{y₀}(y₀) is invertible: its kernel is ∇F(y₀)^⊥ ∩ (span u)^⊥ = 0. By the inverse function theorem (Mathlib `ContDiffAt.toOpenPartialHomeomorph`, in Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff, to be added to the imports; C¹ of the inverse by `OpenPartialHomeomorph.contDiffAt_symm`) there is an open W_{y₀} ∋ y₀ with W_{y₀} ⊆ V ∩ {∇F ≠ 0} such that Φ_{y₀}|_{W_{y₀}} is a C¹ diffeomorphism onto an open set Ω_{y₀} ⊆ ℝ^N, with det DΦ_{y₀} ≠ 0 on W_{y₀}.
 - By second countability choose y_1, y_2, … with Y_r ⊆ ⋃_k W_k (W_k := W_{y_k}, Φ_k := Φ_{y_k}, Ω_k := Ω_{y_k}). Put Y_k := (Y_r ∩ W_k) ∖ ⋃_{k'<k} W_{k'}: Borel, pairwise disjoint, with union Y_r.
 - Splitting off the coordinate 0, ℝ^N = ℝ^{1+n} ≅ ℝ × ℝⁿ, (s, w) ↔ (s, w_1, …, w_n). Under this identification Lebesgue measure on ℝ^N is the product measure L¹ ⊗ Lⁿ (Mathlib `EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp` and `MeasureTheory.measurePreserving_piFinSuccAbove` at index 0). For t ∈ ℝ put Ω_k^t := {w ∈ ℝⁿ : (t, w) ∈ Ω_k} (open) and χ_k^t(w) := ψ(Φ_k⁻¹(t, w)) for w ∈ Ω_k^t, where Φ_k⁻¹ is the inverse of Φ_k|_{W_k}.
 - χ_k^t is C¹ on Ω_k^t and injective (Φ_k⁻¹ is injective and ψ is injective on V). Let y := Φ_k⁻¹(t, w) and B := DΦ_k(y). Then Dχ_k^t(w) = A_y∘B⁻¹∘ι, where ι(w') := (0, w'). B⁻¹∘ι maps ℝⁿ isomorphically onto K_y, because DF(y)B⁻¹(0, w') = 0. Hence Dχ_k^t(w) is injective, with image A_y(K_y) = Q(y) ∩ Ĝ(y)^⊥ (0(c)); for y ∈ Y this is Q(y) ∩ G(ψ(y))^⊥.
 - Jacobian identity in the domain: J(B⁻¹∘ι)·|det B| = |∇F(y)|. Indeed |det B⁻¹| is the N-volume of (B⁻¹(1, 0), B⁻¹ι e_1, …, B⁻¹ι e_n), which is J(B⁻¹ι)·dist(B⁻¹(1, 0), K_y), and DF(y)B⁻¹(1, 0) = 1 gives dist(B⁻¹(1, 0), K_y) = 1/|∇F(y)|.
 - Since J(A_y∘B⁻¹∘ι) = J_K(y)·J(B⁻¹ι) (B⁻¹ι maps onto K_y), 0(c) gives for every y = Φ_k⁻¹(t, w) ∈ W_k:
  (★) J(Dχ_k^t(w))·|det DΦ_k(y)| = J_K(y)·|∇F(y)| = |Ĝ(y)|·J(y).

3. The formula on one piece Y_k. Fix k and a Borel g ≥ 0 on ℝ^P. Put h_k := [|Ĝ|·(g∘ψ)·J/|det DΦ_k|]∘Φ_k⁻¹ on Ω_k (and 0 off Ω_k). It is Borel, since Ĝ, J, DΦ_k and Φ_k⁻¹ are continuous on the relevant open sets and g is Borel.
 (a) Right side. Weighted injective area formula for ψ on Y_k (SimonGMT `weighted_area_formula_volume_of_injective_derivative`; ψ is differentiable with injective derivative on Y_k ⊆ V and injective there), and G(ψ(y)) = Ĝ(y) on Y:
  ∫_{ψ(Y_k)} |G| g dH^N = ∫_{Y_k} |Ĝ(y)| g(ψ(y)) J(y) dy.
  By change of variables y = Φ_k⁻¹(t, w) (Mathlib `MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul` for the self-map Φ_k of ℝ^N on Y_k ⊆ W_k) and Tonelli in the product coordinates, this equals
  ∫_{Φ_k(Y_k)} h_k = ∫_ℝ ∫_{Ω_k^t} 1_{Φ_k(Y_k)}(t, w)·h_k(t, w) dw dt.
 (b) Left side for a fixed t. Since F(Φ_k⁻¹(t, w)) = t, ψ(Y_k ∩ F⁻¹(t)) = χ_k^t({w ∈ Ω_k^t : (t, w) ∈ Φ_k(Y_k)}). The weighted area formula for the injective C¹ map χ_k^t with injective derivative (from ℝⁿ, Hⁿ = Lⁿ there) gives
  ∫_{ψ(Y_k∩F⁻¹(t))} g dHⁿ = ∫_{Ω_k^t} 1_{Φ_k(Y_k)}(t, w)·g(χ_k^t(w))·J(Dχ_k^t(w)) dw.
  By (★), g(χ_k^t(w))J(Dχ_k^t(w)) = h_k(t, w) whenever (t, w) ∈ Φ_k(Y_k) ⊆ Ω_k.
 (c) So for every t, ∫_{ψ(Y_k∩F⁻¹(t))} g dHⁿ = ∫ 1_{Φ_k(Y_k)}(t, w)h_k(t, w) dw. By Tonelli this is a measurable function of t, and integrating over t and using (a):
  ∫_ℝ ∫_{ψ(Y_k ∩ F⁻¹(t))} g dHⁿ dt = ∫_{ψ(Y_k)} |G| g dH^N.

4. Proof of (i). The Borel sets ψ(Y_k) (k ∈ ℕ) and ψ(Y_c) are pairwise disjoint (ψ is injective on Y) and cover ψ(Y). For every t, ψ(Y ∩ F⁻¹(t)) is the disjoint union of the Borel sets ψ(Y_k ∩ F⁻¹(t)) and ψ(Y_c ∩ F⁻¹(t)). By countable additivity of set integrals, ∫_{ψ(Y∩F⁻¹(t))} g dHⁿ = Σ_k ∫_{ψ(Y_k∩F⁻¹(t))} g dHⁿ + ∫_{ψ(Y_c∩F⁻¹(t))} g dHⁿ. The last term vanishes for a.e. t by step 1, and the sum is a measurable function of t (step 3). Hence t ↦ ∫_{ψ(Y∩F⁻¹(t))} g dHⁿ is a.e.-measurable. By monotone convergence and step 3,
 ∫_ℝ ∫_{ψ(Y∩F⁻¹(t))} g dHⁿ dt = Σ_k ∫_{ψ(Y_k)} |G| g dH^N = ∫_{ψ(Y)} |G| g dH^N,
 using G = 0 on ψ(Y_c).

5. Good levels. Apply (i) with g ≡ 1: ∫_ℝ Hⁿ(S_t) dt = ∫_{ψ(Y)} |G| dH^N ≤ Γ·H^N(ψ(Ȳ)) ≤ Γ·Λ^N·L^N(Ȳ) < ∞ (0(a), 0(b)). Let T₀ be the set of t with Hⁿ(S_t) < ∞ and Hⁿ(ψ(Y_c ∩ F⁻¹(t))) = 0. By this and step 1, T₀ has full L¹-measure.

6. Rectifiability. Fix t ∈ T₀. S_t ∖ ψ(Y_c ∩ F⁻¹(t)) ⊆ ⋃_k χ_k^t(Ω_k^t). Cover each open Ω_k^t by countably many closed balls B̄ ⊆ Ω_k^t. On each B̄, χ_k^t is Lipschitz (it is C¹ on the open Ω_k^t ⊇ B̄, so the mean value inequality on the convex compact B̄ applies), so it extends to a Lipschitz map ℝⁿ → ℝ^P (McShane in each coordinate) whose range contains χ_k^t(B̄). Thus S_t is contained in an Hⁿ-null set together with countably many Lipschitz images of ℝⁿ, i.e. S_t is countably n-rectifiable.

7. Tangent planes. Fix t ∈ T₀. S_t is Borel (0(a)) and Hⁿ(S_t) < ∞.
 - Fix k and a closed ball closedBall(w₀, 2ρ) ⊆ Ω_k^t (countably many with rational data suffice to cover Ω_k^t by the balls closedBall(w₀, ρ)). Let Σ := χ_k^t(closedBall(w₀, 2ρ)): compact, Hⁿ(Σ) < ∞.
 - By c1_tangent (d := n, g := χ_k^t, U := Ω_k^t; χ_k^t is injective on the closed ball with injective derivative), for every w ∈ ball(w₀, 2ρ), Σ has approximate tangent space Dχ_k^t(w)(ℝⁿ) at χ_k^t(w). By step 2 this space is Q(y) ∩ Ĝ(y)^⊥, where y = Φ_k⁻¹(t, w); for y ∈ Y it is Q(y) ∩ G(ψ(y))^⊥.
 - Let A := S_t ∩ ψ(Y_k) ∩ χ_k^t(closedBall(w₀, ρ)), a Borel subset of Σ.
 - TL (im_calculus (a), U = ℝ^P, dimension n) for A ⊆ Σ and for A ⊆ S_t (both locally Hⁿ-finite): for Hⁿ-a.e. x ∈ A, S_t has the same approximate tangent spaces at x as Σ, namely Q(y) ∩ G(x)^⊥ for the y ∈ Y_k with ψ(y) = x.
 - These countably many sets A cover S_t ∩ ψ(Y_r) (every w ∈ Ω_k^t lies in some closedBall(w₀, ρ) of the family), and G ≠ 0 on ψ(Y_r) (0(b)). The rest of S_t is S_t ∩ ψ(Y_c), which is Hⁿ-null since t ∈ T₀.
 Hence for Hⁿ-a.e. x ∈ S_t: G(x) ≠ 0, and for the unique y ∈ Y with ψ(y) = x (ψ is injective on V), S_t has approximate tangent space Dψ(y)(ℝ^N) ∩ (span G(x))^⊥ at x. This is (ii). ∎

## Key steps

1. On Ȳ the chart ψ is bi-Lipschitz, G(ψ y) = Dψ(Dψ*Dψ)⁻¹∇F(y), and J_K·|∇F| = |G|·J with Dψ(ker DF) = range Dψ ∩ G^⊥ (linear algebra).
2. Critical part: Hⁿ({∇F=0} ∩ Y ∩ F⁻¹(t)) = 0 for a.e. t, by Eilenberg on small cubes where F is ε-Lipschitz (Sard-type 6.4).
3. Regular part: straighten F by the inverse function theorem, Φ = (F, π); change of variables, Tonelli and the area formula for the level parametrisations χ^t = ψ∘Φ⁻¹(t,·), with the identity J(Dχ^t)|det DΦ| = |G∘ψ| J, give the co-area formula on each piece.
4. Sum over pieces for (i); local finiteness of the slices for a.e. t; rectifiability from the Lipschitz parametrisations χ^t.
5. Tangent planes of the slices: c1_tangent for χ^t(closed balls) and TL (im_calculus (a)) give T_xS_t = Dψ(y)(ℝ^{n+1}) ∩ G(x)^⊥ with G(x) ≠ 0, a.e.

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
