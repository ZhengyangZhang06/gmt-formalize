<!-- theorem-id: gmt-ch07/root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.coarea-a1.approx_differentiable-a1 -->

## Theorem `Submission.dtc_bc_lc_sl_co_approx_differentiable`

Let P, d ∈ ℕ, let M ⊆ ℝ^P be Borel with H^d(M ∩ K) < ∞ for every compact K (H^d = μHE[d]), and let f : ℝ^P → ℝ and G : ℝ^P → ℝ^P be arbitrary maps. For j ∈ ℕ let ψ_j : ℝ^d → ℝ^P and F_j : ℝ^d → ℝ be C¹ and V_j, Y_j ⊆ ℝ^d, such that ψ_j is injective on V_j, Dψ_j(y) is injective for y ∈ V_j, closure(Y_j) is compact and contained in V_j, ψ_j(Y_j) is Borel and contained in M, and for every y ∈ Y_j: f(ψ_j(y)) = F_j(y); M has approximate tangent space Dψ_j(y)(ℝ^d) at ψ_j(y) (Simon Ch. 3, 1.4); G(ψ_j(y)) ∈ Dψ_j(y)(ℝ^d); and ⟨G(ψ_j(y)), Dψ_j(y)e⟩ = DF_j(y)e for all e ∈ ℝ^d. Assume H^d(M ∖ ⋃_j ψ_j(Y_j)) = 0. Then for H^d-a.e. x ∈ M: M has approximate tangent space T_xM := approxTangentPlane d M x at x, G(x) ∈ T_xM, and for every ε > 0, H^d({y ∈ M ∩ B_r(x) : ε|y − x| < |f(y) − f(x) − ⟨G(x), y − x⟩|})/r^d → 0 as r ↓ 0 (B_r(x) = ball x r; quotient in [0, ∞] with r^d entered as ENNReal.ofReal (r ^ d)).

Node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.coarea-a1.approx_differentiable-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6085

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/7060, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7082, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4196

Decomposition children: None

## Lean problem

Declaration: `Submission.dtc_bc_lc_sl_co_approx_differentiable`

```lean
∀ (P d : ℕ) (M : Set (Euclid P)) (f : Euclid P → ℝ) (G : Euclid P → Euclid P) (ψ : ℕ → Euclid d → Euclid P) (V Y : ℕ → Set (Euclid d)) (F : ℕ → Euclid d → ℝ), MeasurableSet M → (∀ K : Set (Euclid P), IsCompact K → μHE[d] (M ∩ K) ≠ ∞) → (∀ j, ContDiff ℝ 1 (ψ j)) → (∀ j, InjOn (ψ j) (V j)) → (∀ j, ∀ y ∈ V j, Injective (fderiv ℝ (ψ j) y)) → (∀ j, ContDiff ℝ 1 (F j)) → (∀ j, IsCompact (closure (Y j))) → (∀ j, closure (Y j) ⊆ V j) → (∀ j, MeasurableSet (ψ j '' Y j)) → (∀ j, ψ j '' Y j ⊆ M) → (∀ j, ∀ y ∈ Y j, f (ψ j y) = F j y) → (∀ j, ∀ y ∈ Y j, HasApproximateTangentSpaceAt d M (ψ j y) (LinearMap.range (fderiv ℝ (ψ j) y : Euclid d →ₗ[ℝ] Euclid P))) → (∀ j, ∀ y ∈ Y j, G (ψ j y) ∈ LinearMap.range (fderiv ℝ (ψ j) y : Euclid d →ₗ[ℝ] Euclid P) ∧ ∀ e : Euclid d, inner ℝ (G (ψ j y)) (fderiv ℝ (ψ j) y e) = fderiv ℝ (F j) y e) → μHE[d] (M \ ⋃ j, ψ j '' Y j) = 0 → ∀ᵐ x ∂(μHE[d].restrict M), HasApproximateTangentSpaceAt d M x (approxTangentPlane d M x) ∧ G x ∈ approxTangentPlane d M x ∧ ∀ ε : ℝ, 0 < ε → Tendsto (fun r : ℝ => μHE[d] (M ∩ ball x r ∩ {y | ε * ‖y - x‖ < |f y - f x - inner ℝ (G x) (y - x)|}) / ENNReal.ofReal (r ^ d)) (𝓝[>] 0) (𝓝 0)
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

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.coarea-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.coarea-a1.approx_differentiable-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3 of the parent proof ("Conclusion (1)"): Simon Ch. 3, 2.1 (∇^M f = ∇^{N_j} f on M_j) and Remark 1.8(1) (M ∖ M_j has density 0 at a.e. point of M_j), with the expansion of f along a chart.
Notation: μ := H^d = μHE[d]; A_j := ψ_j(Y_j); K_j := closure(Y_j); for y ∈ Y_j, Q_j(y) := Dψ_j(y)(ℝ^d) = range Dψ_j(y); B_r(x) := ball(x, r), B̄_r(x) := closedBall(x, r); for x ∈ ℝ^P let Π(x) be the conjunction of the three asserted properties at x.

1. (The approximate tangent plane is the unique one.) If M has approximate tangent space Q at x, then approxTangentPlane d M x = Q and M has approximate tangent space approxTangentPlane d M x at x. Indeed, by definition approxTangentPlane d M x = h.choose for h : ∃ Q′, HasApproximateTangentSpaceAt d M x Q′ (h holds, witnessed by Q), so it satisfies the predicate (unfold approxTangentPlane and rewrite with dite_eq_left; Exists.choose_spec), and by uniqueness (SimonGMT HasApproximateTangentSpaceAt.unique) it equals Q.
2. (Lower Lipschitz constants.) For each j, chart_bilipschitz applied to ψ_j and K_j (compact; ψ_j injective on K_j ⊆ V_j; Dψ_j(y) injective for y ∈ K_j ⊆ V_j) gives m_j > 0 with m_j|a − b| ≤ |ψ_j(a) − ψ_j(b)| for all a, b ∈ K_j ⊇ Y_j.
3. (Tangent locality.) Fix j. Apply im_calculus part (a) with U := ℝ^P (open), the Borel sets A_j ⊆ M ⊆ ℝ^P, and the finiteness μ(M ∩ K) < ∞ for compact K: for μ-a.e. x ∈ A_j (∀ᵐ x ∂ μ⌞A_j) and every linear subspace Q, A_j has approximate tangent space Q at x iff M does.
4. (Good points satisfy Π.) Let x ∈ A_j be a point where the conclusion of step 3 holds. Write x = ψ_j(y) with y ∈ Y_j and put Q := Q_j(y).
 (a) M has approximate tangent space Q at x (hypothesis), so by step 1 T_xM = Q and M has approximate tangent space T_xM at x. Also G(x) = G(ψ_j(y)) ∈ Q = T_xM (hypothesis).
 (b) By step 3 (⇐), A_j has approximate tangent space Q at x as well.
 (c) (Density of M ∖ A_j.) B̄_1(x) is compact, so μ(M ∩ B̄_1(x)) < ∞. tangent_complement_density applied to A_j ⊆ M (A_j Borel), x, Q, s := 1 and (a), (b) gives μ((M ∖ A_j) ∩ B_r(x))/ofReal(r^d) → 0 as r ↓ 0.
 (d) (First-order expansion along A_j.) Fix ε > 0. Put B := Dψ_j(y), ℓ := DF_j(y), η := εm_j/2 > 0 and κ := η/(|G(x)| + 1) > 0. F_j and ψ_j are differentiable at y (C¹), so there is δ > 0 such that every y′ with |y′ − y| < δ satisfies
  |F_j(y′) − F_j(y) − ℓ(y′ − y)| ≤ η|y′ − y| and |ψ_j(y′) − ψ_j(y) − B(y′ − y)| ≤ κ|y′ − y|.
 Put r₀ := m_jδ > 0. Let x′ ∈ A_j ∩ B_{r₀}(x), say x′ = ψ_j(y′) with y′ ∈ Y_j. By step 2, m_j|y′ − y| ≤ |x′ − x| < m_jδ, so |y′ − y| < δ. Using f(x′) = F_j(y′), f(x) = F_j(y) and ⟨G(x), B(y′ − y)⟩ = ℓ(y′ − y) (hypothesis with e := y′ − y),
  f(x′) − f(x) − ⟨G(x), x′ − x⟩ = [F_j(y′) − F_j(y) − ℓ(y′ − y)] − ⟨G(x), ψ_j(y′) − ψ_j(y) − B(y′ − y)⟩.
 By the Cauchy–Schwarz inequality, |f(x′) − f(x) − ⟨G(x), x′ − x⟩| ≤ η|y′ − y| + |G(x)|κ|y′ − y| ≤ 2η|y′ − y| = εm_j|y′ − y| ≤ ε|x′ − x|.
 (e) (Exceptional sets.) For 0 < r ≤ r₀ let E_r := M ∩ B_r(x) ∩ {x″ : ε|x″ − x| < |f(x″) − f(x) − ⟨G(x), x″ − x⟩|}. By (d) no point of A_j ∩ B_r(x) lies in E_r, so E_r ⊆ (M ∖ A_j) ∩ B_r(x) and 0 ≤ μ(E_r)/ofReal(r^d) ≤ μ((M ∖ A_j) ∩ B_r(x))/ofReal(r^d) for r ∈ (0, r₀], a set in 𝓝[>] 0. By (c) and the squeeze theorem (tendsto_of_tendsto_of_tendsto_of_le_of_le'), μ(E_r)/ofReal(r^d) → 0 as r ↓ 0. As ε > 0 was arbitrary, this and (a) give Π(x).
5. (Each piece.) Steps 3–4 and ae_restrict_mem (A_j is measurable, so μ⌞A_j-a.e. x lies in A_j) give: for every j, Π holds μ⌞A_j-a.e.
6. (Conclusion.) Put M₀ := M ∖ ⋃_j A_j; μ(M₀) = 0 by hypothesis, so μ⌞M₀ = 0 and Π holds μ⌞M₀-a.e. trivially. By ae_restrict_iUnion_iff and ae_restrict_union_iff, Π holds μ⌞(M₀ ∪ ⋃_j A_j)-a.e.; since M ⊆ M₀ ∪ ⋃_j A_j, Π holds μ⌞M-a.e. (ae_restrict_of_ae_restrict_of_subset). ∎

Lean realization note. The verified code below follows steps 1–6; step 1 is the helper aux_approxTangentPlane_of and the estimate of step 4(d) the helper aux_expansion (with κ = η/(|G(x)| + 1)). It uses r ∈ (0, r₀) in step 4(e) and handles M₀ in step 6 via ae_restrict_eq_bot.

Appendix (verified Lean realization of the proof above). The code below compiles with Lean v4.35.0-rc3, Mathlib 25730c7c and simongmt 2b36630 when placed after `import GMT.Ch07.Submission` in the frozen contract scope (inside `namespace GMT.Ch07` with the contract's `open` commands, after the contract's `noncomputable section … end`), i.e. where accepted `theorem Submission.…` declarations live in GMT/Ch07/Submission.lean. It refers to the sibling declarations Submission.dtc_bc_lc_sl_co_chart_bilipschitz, Submission.dtc_bc_lc_sl_co_tangent_complement_density and Submission.cmc_imRep_locality_restrict_sub (each with its exact frozen type, introduced by `have h_<key> : <type> := Submission.<name>` at the start of the proof). Auxiliary lemmas are named `Submission.dtc_bc_lc_sl_co_approx_differentiable_aux_approxTangentPlane_of`, `Submission.dtc_bc_lc_sl_co_approx_differentiable_aux_expansion` to stay globally unique; they may be renamed or inlined. It was checked twice: (i) with the exact frozen sibling types as hypotheses, giving no errors and no warnings and `#print axioms` = [propext, Classical.choice, Quot.sound]; (ii) end to end, in one file containing all eight new children of dtc_bc_lc_sl_coarea in dependency order, the parent theorem proved from them, and `sorry` placeholders only for the reused accepted declarations and the parent's resolved dependencies (no warning from any child declaration). `Submission.dtc_bc_lc_sl_co_approx_differentiable` has exactly the frozen type of this child.

```lean
/-- Step 1: if `M` has approximate tangent space `Q` at `x`, then `approxTangentPlane n M x = Q`
and `M` has approximate tangent space `approxTangentPlane n M x` at `x`. -/
theorem Submission.dtc_bc_lc_sl_co_approx_differentiable_aux_approxTangentPlane_of {P n : ℕ} {M : Set (Euclid P)} {x : Euclid P}
    {Q : Submodule ℝ (Euclid P)} (h : HasApproximateTangentSpaceAt n M x Q) :
    approxTangentPlane n M x = Q ∧
      HasApproximateTangentSpaceAt n M x (approxTangentPlane n M x) := by
  have hex : ∃ Q', HasApproximateTangentSpaceAt n M x Q' := ⟨Q, h⟩
  have h1 : approxTangentPlane n M x = hex.choose := by
    rw [approxTangentPlane, dite_eq_left hex]
  have h2 : HasApproximateTangentSpaceAt n M x hex.choose := hex.choose_spec
  rw [h1]
  exact ⟨h2.unique h, h2⟩

/-- Step 4(d): first-order expansion of `F y' - F y - ⟪g, ψ y' - ψ y⟫` near `y`. -/
theorem Submission.dtc_bc_lc_sl_co_approx_differentiable_aux_expansion {P d : ℕ} (ψ : Euclid d → Euclid P) (F : Euclid d → ℝ) (g : Euclid P)
    (y : Euclid d) (hψ : DifferentiableAt ℝ ψ y) (hF : DifferentiableAt ℝ F y)
    (hg : ∀ e : Euclid d, inner ℝ g (fderiv ℝ ψ y e) = fderiv ℝ F y e)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ y' : Euclid d, ‖y' - y‖ < δ →
      |F y' - F y - inner ℝ g (ψ y' - ψ y)| ≤ 2 * η * ‖y' - y‖ := by
  have hκ : 0 < η / (‖g‖ + 1) := div_pos hη (by positivity)
  have h1 := hF.hasFDerivAt.isLittleO.def hη
  have h2 := hψ.hasFDerivAt.isLittleO.def hκ
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp (h1.and h2)
  refine ⟨δ, hδ, fun y' hy' => ?_⟩
  have hdist : dist y' y < δ := by rwa [dist_eq_norm]
  obtain ⟨hF', hψ'⟩ := hδ' hdist
  have e1 : inner ℝ g (ψ y' - ψ y - fderiv ℝ ψ y (y' - y)) =
      inner ℝ g (ψ y' - ψ y) - inner ℝ g (fderiv ℝ ψ y (y' - y)) := inner_sub_right _ _ _
  have key : F y' - F y - inner ℝ g (ψ y' - ψ y) =
      (F y' - F y - fderiv ℝ F y (y' - y))
        - inner ℝ g (ψ y' - ψ y - fderiv ℝ ψ y (y' - y)) := by
    rw [e1, hg (y' - y)]; ring
  rw [key]
  have hgκ : ‖g‖ * (η / (‖g‖ + 1)) ≤ η := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg g]
  calc |(F y' - F y - fderiv ℝ F y (y' - y))
          - inner ℝ g (ψ y' - ψ y - fderiv ℝ ψ y (y' - y))|
      ≤ |F y' - F y - fderiv ℝ F y (y' - y)|
          + |inner ℝ g (ψ y' - ψ y - fderiv ℝ ψ y (y' - y))| := abs_sub _ _
    _ ≤ η * ‖y' - y‖ + ‖g‖ * ‖ψ y' - ψ y - fderiv ℝ ψ y (y' - y)‖ :=
        add_le_add (by rw [← Real.norm_eq_abs]; exact hF') (abs_real_inner_le_norm _ _)
    _ ≤ η * ‖y' - y‖ + ‖g‖ * (η / (‖g‖ + 1) * ‖y' - y‖) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hψ' (norm_nonneg g))
    _ ≤ 2 * η * ‖y' - y‖ := by
        nlinarith [mul_le_mul_of_nonneg_right hgκ (norm_nonneg (y' - y)), norm_nonneg (y' - y)]

theorem Submission.dtc_bc_lc_sl_co_approx_differentiable : ∀ (P d : ℕ) (M : Set (Euclid P)) (f : Euclid P → ℝ) (G : Euclid P → Euclid P) (ψ : ℕ → Euclid d → Euclid P) (V Y : ℕ → Set (Euclid d)) (F : ℕ → Euclid d → ℝ), MeasurableSet M → (∀ K : Set (Euclid P), IsCompact K → μHE[d] (M ∩ K) ≠ ∞) → (∀ j, ContDiff ℝ 1 (ψ j)) → (∀ j, InjOn (ψ j) (V j)) → (∀ j, ∀ y ∈ V j, Injective (fderiv ℝ (ψ j) y)) → (∀ j, ContDiff ℝ 1 (F j)) → (∀ j, IsCompact (closure (Y j))) → (∀ j, closure (Y j) ⊆ V j) → (∀ j, MeasurableSet (ψ j '' Y j)) → (∀ j, ψ j '' Y j ⊆ M) → (∀ j, ∀ y ∈ Y j, f (ψ j y) = F j y) → (∀ j, ∀ y ∈ Y j, HasApproximateTangentSpaceAt d M (ψ j y) (LinearMap.range (fderiv ℝ (ψ j) y : Euclid d →ₗ[ℝ] Euclid P))) → (∀ j, ∀ y ∈ Y j, G (ψ j y) ∈ LinearMap.range (fderiv ℝ (ψ j) y : Euclid d →ₗ[ℝ] Euclid P) ∧ ∀ e : Euclid d, inner ℝ (G (ψ j y)) (fderiv ℝ (ψ j) y e) = fderiv ℝ (F j) y e) → μHE[d] (M \ ⋃ j, ψ j '' Y j) = 0 → ∀ᵐ x ∂(μHE[d].restrict M), HasApproximateTangentSpaceAt d M x (approxTangentPlane d M x) ∧ G x ∈ approxTangentPlane d M x ∧ ∀ ε : ℝ, 0 < ε → Tendsto (fun r : ℝ => μHE[d] (M ∩ ball x r ∩ {y | ε * ‖y - x‖ < |f y - f x - inner ℝ (G x) (y - x)|}) / ENNReal.ofReal (r ^ d)) (𝓝[>] 0) (𝓝 0) := by
  have h_chart_bilipschitz : (∀ (P d : ℕ) (ψ : Euclid d → Euclid P) (K : Set (Euclid d)), ContDiff ℝ 1 ψ → IsCompact K → InjOn ψ K → (∀ y ∈ K, Injective (fderiv ℝ ψ y)) → ∃ m Λ : ℝ, 0 < m ∧ ∀ a ∈ K, ∀ b ∈ K, m * ‖a - b‖ ≤ ‖ψ a - ψ b‖ ∧ ‖ψ a - ψ b‖ ≤ Λ * ‖a - b‖) := Submission.dtc_bc_lc_sl_co_chart_bilipschitz
  have h_tangent_complement_density : (∀ (P N : ℕ) (A M : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)) (s : ℝ), MeasurableSet A → A ⊆ M → 0 < s → μHE[N] (M ∩ closedBall x s) ≠ ∞ → HasApproximateTangentSpaceAt N M x Q → HasApproximateTangentSpaceAt N A x Q → Tendsto (fun r : ℝ => μHE[N] ((M \ A) ∩ ball x r) / ENNReal.ofReal (r ^ N)) (𝓝[>] 0) (𝓝 0)) := Submission.dtc_bc_lc_sl_co_tangent_complement_density
  have h_im_calculus : ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) := Submission.cmc_imRep_locality_restrict_sub
  intro P d M f G ψ V Y F hM hfin hψ hinj hDinj hF hYc hYV hAmeas hAM hfF htan hG hnull
  -- Step 6: reduce to the null part and the pieces `ψ j '' Y j`.
  refine ae_restrict_of_ae_restrict_of_subset
    (t := (M \ ⋃ j, ψ j '' Y j) ∪ ⋃ j, ψ j '' Y j) (fun x hx => ?_) ?_
  · by_cases hx' : x ∈ ⋃ j, ψ j '' Y j
    · exact Or.inr hx'
    · exact Or.inl ⟨hx, hx'⟩
  rw [ae_restrict_union_iff, ae_restrict_iUnion_iff]
  refine ⟨?_, fun j => ?_⟩
  · rw [ae_restrict_eq_bot.mpr hnull]
    exact eventually_bot
  -- Step 2: lower Lipschitz constant of `ψ j` on `closure (Y j)`.
  obtain ⟨m, Λ, hm, hbi⟩ := h_chart_bilipschitz P d (ψ j) (closure (Y j)) (hψ j) (hYc j)
    ((hinj j).mono (hYV j)) (fun y hy => hDinj j y (hYV j hy))
  -- Step 3: tangent locality.
  have h3 := h_im_calculus.1 P d univ (ψ j '' Y j) M isOpen_univ (hAmeas j) hM (hAM j)
    (subset_univ _) (fun K hK _ => hfin K hK)
  -- Steps 4–5.
  filter_upwards [h3, ae_restrict_mem (hAmeas j)] with x hx hxA
  obtain ⟨y, hyY, rfl⟩ := hxA
  have hMQ := htan j y hyY
  obtain ⟨hTeq, hT⟩ := Submission.dtc_bc_lc_sl_co_approx_differentiable_aux_approxTangentPlane_of hMQ
  have hAQ := (hx _).mpr hMQ
  refine ⟨hT, ?_, ?_⟩
  · rw [hTeq]; exact (hG j y hyY).1
  intro ε hε
  have hdens := h_tangent_complement_density P d (ψ j '' Y j) M (ψ j y) _ 1 (hAmeas j) (hAM j)
    one_pos (hfin _ (isCompact_closedBall _ _)) hMQ hAQ
  have hψd : DifferentiableAt ℝ (ψ j) y := ((hψ j).differentiable one_ne_zero) y
  have hFd : DifferentiableAt ℝ (F j) y := ((hF j).differentiable one_ne_zero) y
  have hη : 0 < ε * m / 2 := by positivity
  obtain ⟨δ, hδ, hexp⟩ := Submission.dtc_bc_lc_sl_co_approx_differentiable_aux_expansion (ψ j) (F j) (G (ψ j y)) y hψd hFd (hG j y hyY).2 hη
  have hr₀ : 0 < m * δ := mul_pos hm hδ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdens
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [Ioo_mem_nhdsGT hr₀] with r hr
  refine ENNReal.div_le_div_right (measure_mono ?_) _
  rintro z ⟨⟨hzM, hzB⟩, hzε⟩
  refine ⟨⟨hzM, fun hzA => ?_⟩, hzB⟩
  obtain ⟨y', hy'Y, rfl⟩ := hzA
  simp only [mem_ofPred_eq] at hzε
  rw [mem_ball, dist_eq_norm] at hzB
  have hlow := (hbi y' (subset_closure hy'Y) y (subset_closure hyY)).1
  have hy'δ : ‖y' - y‖ < δ := by
    by_contra hcon
    have hcon' : δ ≤ ‖y' - y‖ := not_lt.mp hcon
    have : m * δ ≤ m * ‖y' - y‖ := mul_le_mul_of_nonneg_left hcon' hm.le
    linarith [hr.2]
  have hup := hexp y' hy'δ
  rw [hfF j y' hy'Y, hfF j y hyY] at hzε
  have hcmp : 2 * (ε * m / 2) * ‖y' - y‖ ≤ ε * ‖ψ j y' - ψ j y‖ := by
    calc 2 * (ε * m / 2) * ‖y' - y‖ = ε * (m * ‖y' - y‖) := by ring
      _ ≤ ε * ‖ψ j y' - ψ j y‖ := mul_le_mul_of_nonneg_left hlow hε.le
  linarith
```

## Key steps

1. approxTangentPlane d M x equals the approximate tangent plane whenever one exists (choice + uniqueness).
2. chart_bilipschitz on closure(Y_j): |y′ − y| ≤ m_j⁻¹|ψ_j(y′) − ψ_j(y)|.
3. im_calculus (a): at μ-a.e. x = ψ_j(y) ∈ A_j, A_j and M share approximate tangent planes; T_xM = Dψ_j(y)ℝ^d is also A_j's, and G(x) ∈ T_xM.
4. tangent_complement_density: H^d((M ∖ A_j) ∩ B_r(x)) = o(r^d).
5. First-order expansion of f along A_j (differentiability of F_j and ψ_j plus the gradient identity): for small r the exceptional set lies in M ∖ A_j.
6. Countably many pieces plus the null remainder give the statement H^d-a.e. on M.
7. Verified Lean realization supplied in the appendix (compiles warning-free; standard axioms only).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db1, mathlib 25730c7c); diff GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); cat .lake/packages manifest (simongmt 2b36630)`
- `python3 -I scans of dag.json (1523 nodes): slicing-a1 subtree and statuses; frozen types of chart_pieces, chart_coarea, eilenberg, im_calculus; nodes matching bi-Lipschitz|immersion|density point|Lebesgue density|blowUpMap|tangential gradient|co-area|Injective (fderiv; the dor_lmb...slicing-a1.slice_family-a1 subtree (lipschitz_chart_pieces, density_directions, piece_coarea, piece_slice_tangent, tangential_gradient)`
- `git show <commit>:GMT/Ch07/Submission.lean and whitespace-normalised type comparison for cmc_imRep_locality_restrict_sub (2af75d6), codim1_rdo_c1cov_local_lower_lipschitz (12e74ed), rsd_tendsto_closedBall_density_of_approxTangent (dbef2c1), dor_lmb_approx_tangent_locality (53d4678): all MATCH; nodes/*/accepted-candidate.json comparator_passed = true`
- `grep -c dtc_bc_lc_sl_co_ dag.json (0); git log --all -S 'dtc_bc_lc_sl_co_' over 6410 refs (no match); survey of 400 accepted candidate commits: added declarations are theorem Submission.*`
- `grep in the snapshot Mathlib: Besicovitch.ae_tendsto_measure_inter_div, MeasurableSet.image_of_continuousOn_injOn, LipschitzOnWith.hausdorffMeasure_image_le, Convex.norm_image_sub_le_of_norm_fderiv_le, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Measure.addHaar_smul, Measure.addHaar_closedBall, measure_inter_add_sdiff, lintegral_iUnion, lintegral_tsum, ENNReal.Tendsto.sub, ContinuousOn.measurable_piecewise, Measurable.find, ContinuousOn.preimage_isClosed_of_isClosed, InjOn.leftInvOn_invFunOn, ae_restrict_iUnion_iff, ae_restrict_union_iff, ae_restrict_iff', ae_lt_top', NormedRing.inverse_continuousAt, ContinuousLinearMap.adjoint_inner_left, toDual_symm_apply, IsCompact.exists_bound_of_continuousOn, LinearMap.isUnit_iff_ker_eq_bot`
- `grep in SimonGMT: Chapter03/Rectifiable.lean (CountablyRectifiable, blowUpMap, HasApproximateTangentSpaceAt, .unique, countablyRectifiable_iUnion, countablyRectifiable_of_measure_zero, CountablyRectifiable.mono); Chapter02/Lipschitz.lean (euclideanHausdorffMeasure_image_le_of_lipschitzOn); Chapter04/TangentDensity.lean; no nonlinear co-area, tangential gradient or slicing declarations`
- `sed book/chapter-03.txt lines 300-460 (Remark 1.8, 2.1-2.10) and book/chapter-06.txt lines 1140-1200 (Lemma 4.1)`
- `Lean checks through a persistent LSP worker: #check availability file under import GMT.Ch07.Submission; /tmp/coarea_split/v2/ch/Challenge_<key>.lean (11 modules from gmt-compare.py child_modules, contract mode); /tmp/coarea_split/asm/Assembly3.lean; /tmp/coarea_split/agents/{A,B,C,D,E} hypothesis-form proofs; /tmp/coarea_split/e2e2/E2E_from_json.lean and E2E_solution.lean (end to end, comparator form)`
- `sed /runtime/flows/gmt-claude-3b0b44b19c6a/_recursive_lean/runtime.py (_decompose depth gate, _dependency_problem, _existing_lean_name_problem) and prompts.py (DECOMPOSITION_AUDIT, RLCR_LEAN_TASK, LEAN_AUDIT, SPECULATIVE_PARENT_TASK)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-772be56655/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-09907e06c7/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-im-calculus-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1-unweighted-density-one-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-ec0e4b9204/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Ring/Units.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-3b0b44b19c6a/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-3b0b44b19c6a/_recursive_lean/prompts.py`
- `/tmp/coarea_split/v2/ch`
- `/tmp/coarea_split/asm/Assembly3.lean`
- `/tmp/coarea_split/e2e2/E2E_from_json.lean`
- `/tmp/coarea_split/e2e2/E2E_solution.lean`

Neither the pinned SimonGMT library nor Mathlib has a nonlinear co-area formula, a tangential gradient of Lipschitz functions on rectifiable sets, or slicing. They do supply every tool cited in the child proofs: the Lebesgue density theorem, Lusin–Souslin, the Lipschitz image bound, the mean value inequality, Haar scaling, adjoints, continuity of Ring.inverse, and the countable-rectifiability lemmas. Three comparator-accepted DAG declarations are reused with identical types: cmc_imRep_locality_restrict_sub, codim1_rdo_c1cov_local_lower_lipschitz and rsd_tendsto_closedBall_density_of_approxTangent. dor_lmbsf_density_directions (accepted) overlaps one step of density_gradient_bound but is not needed. The eight new names are unreserved. All 11 types elaborate in the exact comparator challenge modules. Every new child is proved in Lean exactly as typed, both in hypothesis form and end to end. The exact frozen parent type is proved from the children and its resolved dependencies, using only propext, Classical.choice and Quot.sound.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
