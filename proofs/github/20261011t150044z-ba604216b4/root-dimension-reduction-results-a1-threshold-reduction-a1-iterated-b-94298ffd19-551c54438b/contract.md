<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.threshold_reduction-a1.iterated_blowup_limit-a1 -->

## Theorem `Submission.dimred_tr_iterated_blowup_limit`

Let P, n ∈ ℕ, U ⊆ ℝ^P open, T ∈ 𝒟_n(U), x ∈ U, x_i ∈ ℝ^P with x_i → x, λ_i > 0 with λ_i → 0, y ∈ ℝ^P, s_k > 0 with s_k → 0, and S, C ∈ 𝒟_n(ℝ^P). Assume: (a) there are δ > 0 and Γ ∈ ℝ with M_{B_ρ(x′)}(T) ≤ ofReal(Γρⁿ) for all x′ ∈ B_δ(x) and 0 < ρ < δ; (b) η_{x_i,λ_i#}T ⇀ S in ℝ^P (ConvergesWeakly (fun i ↦ blowUp T x_i λ_i) S); (c) η_{y,s_k#}S ⇀ C in ℝ^P. Then there is a strictly increasing φ : ℕ → ℕ with η_{x_{φ(k)}+λ_{φ(k)}y, λ_{φ(k)}s_k #}T ⇀ C in ℝ^P, i.e. ConvergesWeakly (fun k ↦ blowUp T (x_{φ(k)} + λ_{φ(k)}•y) (λ_{φ(k)}·s_k)) C.

Node: `root.dimension_reduction_results-a1.threshold_reduction-a1.iterated_blowup_limit-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1030

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/7935

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5170, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2794, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4607, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8677, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8678, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4777, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6954

## Lean problem

Declaration: `Submission.dimred_tr_iterated_blowup_limit`

```lean
∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (xs : ℕ → Euclid P) (lams : ℕ → ℝ) (hlams : ∀ i, 0 < lams i) (S : GeometricCurrentOn (univ : Set (Euclid P)) n) (y : Euclid P) (ss : ℕ → ℝ) (hss : ∀ k, 0 < ss k) (C : GeometricCurrentOn (univ : Set (Euclid P)) n), IsOpen U → x ∈ U → Tendsto xs atTop (𝓝 x) → Tendsto lams atTop (𝓝 0) → Tendsto ss atTop (𝓝 0) → (∃ δ Γ : ℝ, 0 < δ ∧ ∀ x' ∈ ball x δ, ∀ ρ : ℝ, 0 < ρ → ρ < δ → T.massOn (ball x' ρ) ≤ ENNReal.ofReal (Γ * ρ ^ n)) → ConvergesWeakly (fun i => blowUp T (xs i) (lams i) (hlams i).ne') S → ConvergesWeakly (fun k => blowUp S y (ss k) (hss k).ne') C → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ConvergesWeakly (fun k => blowUp T (xs (φ k) + lams (φ k) • y) (lams (φ k) * ss k) (mul_pos (hlams (φ k)) (hss k)).ne') C
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

- Parent DAG node: `root.dimension_reduction_results-a1.threshold_reduction-a1`
- Child DAG node: `root.dimension_reduction_results-a1.threshold_reduction-a1.iterated_blowup_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 2(e), case λ = 0, "Diagonal selection" (with the uniform bounds of step 2(d) and criterion (C)), stated directly for blow-ups of T. Uses the sibling lemma blowup_calculus (Submission.dimred_tr_blowup_calculus: (i) mass scaling, (ii) currentEval(η_{a,t#}A, ω) = currentEval(A, η_{a,t}^#ω), (iii) composition). The countable-test criterion (C) of parent step 2(d) is proved in Step A below as Lemma CT.

Step A (Lemma CT; formerly the separate sibling countable_tests of attempt 4, merged here because this child is its only user). Within this step the letters below denote the objects of Lemma CT only.
Lemma CT (criterion (C) of parent step 2(d)). Let P, n ∈ ℕ. There is a sequence (ω_m) in 𝒟ⁿ(ℝ^P) (TestFormOn univ n) with the following property. Let V_k ⊆ ℝ^P (k ∈ ℕ) be sets, A_k ∈ 𝒟_n(V_k) and A ∈ 𝒟_n(ℝ^P). Suppose that for every R ∈ ℕ there are k₀ ∈ ℕ and Γ ∈ [0, ∞) with M_{B_{R+1}(0)}(A) ≤ Γ and, for all k ≥ k₀, B_{R+1}(0) ⊆ V_k and M_{B_{R+1}(0)}(A_k) ≤ Γ. Suppose also that currentEval(A_k, ω_m) → A(ω_m) as k → ∞ for every m. Then A_k ⇀ A in ℝ^P (ConvergesWeakly), i.e. currentEval(A_k, ω) → A(ω) for every ω ∈ 𝒟ⁿ(ℝ^P).
Proof of Lemma CT.
Source: parent proof, step 2(d), "Countable-test criterion for limits on ℝ^P approximated by currents whose domains exhaust ℝ^P" (criterion (C)). The parent builds the countable family from polynomials (Weierstrass). Stone–Weierstrass and the separability of C(X, Y) are not reachable from the frozen header (checked: polynomialFunctions_closure_eq_top and ContinuousMap.instSeparableSpace are unknown after import GMT.Ch07.Submission). The family is therefore built below from an explicit smooth partition of unity on a grid, with the same property (★). Steps CT2 and CT3 are the parent's argument. |·| denotes covectorEuclideanNorm, the coefficient norm in Simon's mass: |α| = (Σ_I α(e_{I(1)}, …, e_{I(n)})²)^{1/2} over strictly increasing I : Fin n → Fin P. It is the Euclidean norm of a linear image of α, hence a seminorm: |α + β| ≤ |α| + |β| and |cα| = |c||α|.

CT1. (A countable approximating family.) We construct a countable family {ω_m} ⊆ 𝒟ⁿ(ℝ^P) = TestFormOn univ n with property (★): for every R ∈ ℕ, every ω ∈ 𝒟ⁿ(ℝ^P) with tsupport ω ⊆ B_R(0) and every ε > 0, there is m with tsupport ω_m ⊆ B_{R+1}(0) and |ω(p) − ω_m(p)| < ε for all p ∈ ℝ^P.
(a) A partition of unity on ℝ. Let s := Real.smoothTransition: C^∞, monotone, s(u) = 0 for u ≤ 0, s(u) = 1 for u ≥ 1. Put β(u) := s(u + 1) − s(u). Then β is C^∞ and β ≥ 0 (monotone), and β(u) = 0 unless −1 < u < 1: for u ≥ 1 both terms are 1, for u ≤ −1 both are 0. For every u ∈ ℝ, Σ_{j∈ℤ} β(u − j) = 1. Indeed, let j₀ := ⌊u⌋. Only j ∈ {j₀ − 1, j₀, j₀ + 1} (in fact only j₀ and j₀ + 1) can contribute, and the three terms telescope to s(u − j₀ + 2) − s(u − j₀ − 1) = 1 − 0, because u − j₀ + 2 ≥ 2 and u − j₀ − 1 < 0.
(b) A partition of unity on ℝ^P. For δ > 0 and g ∈ ℤ^P put ψ^δ_g(x) := ∏_{i<P} β(x_i/δ − g_i), where x_i is the i-th coordinate of x ∈ Euclid P. Then:
 - ψ^δ_g is C^∞, as a finite product of C^∞ functions of continuous linear coordinates;
 - 0 ≤ ψ^δ_g;
 - if ψ^δ_g(x) ≠ 0, then |x_i − δg_i| < δ for every i, hence |x − δg| ≤ δ√P (with equality only if P = 0). So tsupport ψ^δ_g ⊆ B̄_{δ√P}(δg) and ψ^δ_g has compact support;
 - for every x, Σ_{g∈ℤ^P} ψ^δ_g(x) = ∏_{i<P} Σ_{j∈ℤ} β(x_i/δ − j) = 1, with only finitely many nonzero terms.
(c) Dense covectors. Covector (Euclid P) n = (Euclid P) [⋀^Fin n]→L[ℝ] ℝ is a normed space. It is finite-dimensional: α ↦ (α(e_{J(1)}, …, e_{J(n)}))_{J : Fin n → Fin P} is a linear map into the finite-dimensional space (Fin n → Fin P) → ℝ, and it is injective, because an alternating map is determined by its values on tuples of basis vectors (Module.Basis.ext_alternating, applied to the underlying alternating map). No FiniteDimensional or SeparableSpace instance for Covector is inferred after import GMT.Ch07.Submission; the local instance obtained here (FiniteDimensional.of_injective) makes SeparableSpace inferable. So it is proper and second countable, hence separable. Fix a sequence (α_l)_{l∈ℕ} dense for the operator norm ‖·‖. Each coefficient satisfies |α(e_{I(1)}, …, e_{I(n)})| ≤ ‖α‖·∏‖e_{I(i)}‖ = ‖α‖, so |α| ≤ √(Pⁿ)·‖α‖. Hence (α_l) is also dense for |·|.
(d) The family. For j ∈ ℕ put δ_j := 1/((j + 1)(P + 1)), so δ_j√P < 1. Take all forms
 ω_{j,G,a}(x) := Σ_{g∈G} ψ^{δ_j}_g(x) • α_{a(g)},
 with j ∈ ℕ, G ⊆ ℤ^P finite and a : G → ℕ. These index triples form a countable set. Each ω_{j,G,a} is a C^∞ map ℝ^P → Covector: a finite sum of C^∞ scalar functions times constant covectors. It has compact support (tsupport ⊆ ⋃_{g∈G} tsupport ψ^{δ_j}_g, a finite union of compact sets), so it is a test form in 𝒟ⁿ(ℝ^P) with tsupport ⊆ univ. The empty G gives the zero form, so the family is nonempty. Enumerate it surjectively as (ω_m)_{m∈ℕ}, by a surjection from ℕ onto a countable nonempty set.
(e) Proof of (★).
 - Let R, ω and ε be given. ω is continuous with compact support, hence uniformly continuous. Since |α| ≤ √(Pⁿ)·‖α‖ by (c), the seminorm |·| is Lipschitz for the operator norm. So there is δ₀ > 0 with |ω(x) − ω(y)| < ε/3 whenever |x − y| < δ₀.
 - Choose j with δ_j√P < δ₀ and put δ := δ_j. Let G := {g ∈ ℤ^P : |δg| < R}, which is finite. For g ∈ G choose a(g) with |ω(δg) − α_{a(g)}| < ε/3, by (c). Put ω′ := ω_{j,G,a}.
 - Support. tsupport ω′ ⊆ ⋃_{g∈G} B̄_{δ√P}(δg) ⊆ B̄_{R+δ√P}(0) ⊆ B_{R+1}(0), since |δg| < R and δ√P < 1.
 - Estimate. If g ∉ G, then |δg| ≥ R, so δg ∉ B_R(0) ⊇ tsupport ω and ω(δg) = 0. Using Σ_g ψ^δ_g(x) = 1, for every x:
 ω(x) − ω′(x) = Σ_{g∈ℤ^P} ψ^δ_g(x)·(ω(x) − ω(δg)) + Σ_{g∈G} ψ^δ_g(x)·(ω(δg) − α_{a(g)}),
 a finite sum, because only finitely many ψ^δ_g(x) ≠ 0. If ψ^δ_g(x) ≠ 0 then |x − δg| ≤ δ√P < δ₀, so |ω(x) − ω(δg)| < ε/3. By the seminorm property and ψ^δ_g ≥ 0, Σ_g ψ^δ_g(x) = 1,
 |ω(x) − ω′(x)| ≤ Σ_g ψ^δ_g(x)·ε/3 + Σ_g ψ^δ_g(x)·ε/3 ≤ 2ε/3 < ε.
 - So ω′ = ω_m for some m, and it has the properties required in (★).

CT2. (Mass controls test values.) Let A′ ∈ 𝒟_n(V′), O ⊆ ℝ^P and β ∈ 𝒟ⁿ(V′) with tsupport β ⊆ O and |β(p)| ≤ s for all p. Suppose M_O(A′) < ∞. Then |A′(β)| ≤ s·M_O(A′).toReal.
- If s > 0, then ±β/s belong to massAdmissibleOn V′ n O, so ofReal(±A′(β)/s) ≤ M_O(A′) by GeometricCurrentOn.le_massOn.
- If s = 0, then β = 0. Indeed |β(p)| = 0 forces every strictly increasing coefficient of β(p) to vanish. An alternating map that vanishes on all strictly increasing basis tuples is zero: permuting a tuple changes the value by a sign, and a tuple with a repeated basis vector gives 0.

CT3. (Proof of the criterion.)
- Let ω ∈ 𝒟ⁿ(ℝ^P). Choose R ∈ ℕ with tsupport ω ⊆ B_R(0), which exists by compact support. Take k₀ and Γ from the hypothesis for this R.
- Let ε > 0 and choose m by (★). For k ≥ k₀, tsupport ω and tsupport ω_m lie in B_{R+1}(0) ⊆ V_k. So currentEval(A_k, ω) = A_k(ω) and currentEval(A_k, ω_m) = A_k(ω_m).
- β := ω − ω_m has tsupport ⊆ B_{R+1}(0) and |β| ≤ ε. By linearity and step CT2 with O = B_{R+1}(0) and s = ε, |currentEval(A_k, ω) − currentEval(A_k, ω_m)| ≤ εΓ. Likewise |A(ω) − A(ω_m)| ≤ εΓ.
- Since currentEval(A_k, ω_m) → A(ω_m), limsup_k |currentEval(A_k, ω) − A(ω)| ≤ 2εΓ.
- As ε > 0 is arbitrary and Γ does not depend on ε, currentEval(A_k, ω) → A(ω).
This holds for every ω ∈ 𝒟ⁿ(ℝ^P), which is ConvergesWeakly (A_k) A. ∎

Main argument.
Notation: B_i := blowUp T x_i λ_i ∈ 𝒟_n(η_{x_i,λ_i}(U)); A_{k,i} := blowUp T (x_i + λ_iy) (λ_is_k); η_k^#ω := affinePullbackForm (dilationCLM P s_k) (−s_k⁻¹y) ω. Note η_{y,s_k}(ℝ^P) = ℝ^P, so blowUp S y s_k and S are currents on (sets equal to) ℝ^P.
0. (Normalization of Γ.) Hypothesis (a) stays true when Γ is replaced by max(Γ, 0), since ofReal is monotone. So assume Γ ≥ 0; then all the real bounds Γρⁿ below are nonnegative and ofReal(Γρⁿ) = Γρⁿ.
1. (Exhausting domains.) Choose δ′ > 0 with B_{2δ′}(x) ⊆ U (U open, x ∈ U). If x″ ∈ B_{δ′}(x) and t > 0, then dilation x″ t '' U ⊇ dilation x″ t '' B_{δ′}(x″) = B_{δ′/t}(0). Consequently, if x″_k → x and t_k → 0, every compact subset of ℝ^P lies in the domain of blowUp T x″_k t_k for all large k. This applies to (x_i, λ_i).
2. (Mass bounds for blow-ups of T.) By blowup_calculus (i) and dilation a t ⁻¹' B_ρ(p) = B_{tρ}(a + tp): M_{B_ρ(p)}(blowUp T a t) = t^{−n}M_{B_{tρ}(a+tp)}(T) ≤ t^{−n}Γ(tρ)ⁿ = Γρⁿ (as elements of [0, ∞], via ofReal) whenever a + tp ∈ B_δ(x) and tρ < δ.
3. (Mass bounds for S.) Let p ∈ ℝ^P, ρ > 0 and β ∈ 𝒟ⁿ(ℝ^P) admissible for M_{B_ρ(p)}(S), i.e. tsupport β ⊆ B_ρ(p) and |β| ≤ 1. For large i, tsupport β lies in the domain of B_i (step 1). Then β is admissible for M_{B_ρ(p)}(B_i), and currentEval(B_i, β) = B_i(β) ≤ M_{B_ρ(p)}(B_i).toReal ≤ Γρⁿ (GeometricCurrentOn.le_massOn and step 2, as x_i + λ_ip → x and λ_iρ → 0). By (b), S(β) = lim_i currentEval(B_i, β) ≤ Γρⁿ. Taking the supremum, M_{B_ρ(p)}(S) ≤ ofReal(Γρⁿ) for all p ∈ ℝ^P and ρ > 0.
4. (Mass bounds for η_{y,s_k#}S and for C.) By blowup_calculus (i), M_{B_ρ(0)}(blowUp S y s_k) = s_k^{−n}M_{B_{s_kρ}(y)}(S) ≤ ofReal(Γρⁿ) by step 3. If β is admissible for M_{B_ρ(0)}(C), then C(β) = lim_k currentEval(blowUp S y s_k, β) by (c). Each term equals (blowUp S y s_k)(β) ≤ Γρⁿ, since the domain is all of ℝ^P. Hence M_{B_ρ(0)}(C) ≤ ofReal(Γρⁿ).
5. (Inner convergence for fixed k.) Fix k and ω ∈ 𝒟ⁿ(ℝ^P). By blowup_calculus (iii), applied to B_i with centre y and scale s_k (note (x_i + λ_iy, λ_is_k) are the composed parameters), and then (ii):
currentEval(A_{k,i}, ω) = currentEval(blowUp B_i y s_k, ω) = currentEval(B_i, η_k^#ω).
η_k^#ω is a test form on ℝ^P (affine pull-backs by proper affine maps preserve test forms). So by (b), currentEval(B_i, η_k^#ω) → S(η_k^#ω) as i → ∞. Moreover S(η_k^#ω) = currentEval(S, η_k^#ω) = currentEval(blowUp S y s_k, ω) by (ii) for S. Hence currentEval(A_{k,i}, ω) → currentEval(blowUp S y s_k, ω) as i → ∞.
6. (Diagonal selection.) Let (ω_m) be the family given by Lemma CT (Step A) for (P, n). Choose inductively i(0) < i(1) < … such that for each k: i(k) > i(k − 1); λ_{i(k)} < 1/(k+1); |x_{i(k)} − x| < 1/(k+1); and |currentEval(A_{k,i(k)}, ω_m) − currentEval(blowUp S y s_k, ω_m)| < 1/(k+1) for all m ≤ k. These are finitely many conditions, each true for all large i by step 5, λ_i → 0 and x_i → x. Put φ(k) := i(k), x′_k := x_{φ(k)} + λ_{φ(k)}y, λ′_k := λ_{φ(k)}s_k and D_k := A_{k,φ(k)} = blowUp T x′_k λ′_k. Then φ is strictly increasing, x′_k → x and λ′_k → 0.
7. (Applying criterion (C).)
(a) Domains and masses. Given R ∈ ℕ, choose k₀ such that for k ≥ k₀: x′_k ∈ B_{min(δ,δ′)}(x), λ′_k(R + 1) < δ, and R + 1 < δ′/λ′_k. Then B_{R+1}(0) ⊆ dom D_k (step 1) and M_{B_{R+1}(0)}(D_k) ≤ ofReal(Γ(R+1)ⁿ) (step 2 with p = 0). Also M_{B_{R+1}(0)}(C) ≤ ofReal(Γ(R+1)ⁿ) (step 4). Take Γ_R := ofReal(Γ(R+1)ⁿ) < ∞.
(b) Tests. For each m and k ≥ m: |currentEval(D_k, ω_m) − C(ω_m)| < 1/(k+1) + |currentEval(blowUp S y s_k, ω_m) − C(ω_m)|, and the last term → 0 by (c). So currentEval(D_k, ω_m) → C(ω_m).
By Lemma CT (Step A), D_k ⇀ C in ℝ^P, i.e. ConvergesWeakly (fun k ↦ blowUp T (x_{φ(k)} + λ_{φ(k)}•y) (λ_{φ(k)}·s_k)) C. ∎
Formalization hint (not part of the argument): Filter.extraction_forall_of_eventually, reachable after import GMT.Ch07.Submission, produces the strictly increasing diagonal of step 6 directly from "for each k, the k-th finite list of conditions holds for all large i".

## Key steps

1. Lemma CT: a countable family of test forms (smooth grid partition of unity times a dense sequence of covectors) approximates every test form uniformly with controlled support; with local mass bounds, convergence on the family gives ConvergesWeakly.
2. Domains of blow-ups at centres near x ∈ U with scales → 0 exhaust ℝ^P; the mass hypothesis and blowup_calculus (i) give M_{B_ρ(p)}(η_{a,t#}T) ≤ Γρⁿ for a + tp near x and tρ small.
3. Lower semicontinuity of mass along the defining convergences gives M_{B_ρ(p)}(S) ≤ Γρⁿ, then M_{B_ρ(0)}(η_{y,s_k#}S) ≤ Γρⁿ and M_{B_ρ(0)}(C) ≤ Γρⁿ.
4. For fixed k, blowup_calculus (ii),(iii) give currentEval(η_{x_i+λ_iy, λ_is_k#}T, ω) = currentEval(η_{x_i,λ_i#}T, η_{y,s_k}^#ω) → (η_{y,s_k#}S)(ω) as i → ∞.
5. Choose i(k) strictly increasing so that the first k countable test values are within 1/(k+1), with x_{i(k)} → x and λ_{i(k)} → 0.
6. Uniform mass bounds plus convergence on the countable tests give ConvergesWeakly by Lemma CT.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD`
- `sha256sum GMT/Ch07/Submission.lean GMT/Ch07/Contract.lean .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `grep -n 'theorem hausdorffMeasure_image_le' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `grep -n 'addHaarScalarFactor_volume_hausdorffMeasure_ne_zero\|theorem euclideanHausdorffMeasure_def' <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -c dimred_tr_ <snapshot>/project (exit 1, no match); rg -l dimred_tr_ GMT .lake/packages/simongmt/Poincare --glob '*.lean' (exit 1, no match)`
- `grep -n 'def HasApproximateTangentSpaceAt' -A 14 and grep -n 'def blowUpMap' -A 5 .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `sed -n 85,125p .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean (VanishesOn, zeroRegion, support)`
- `python3 inspection of dag.json: status, candidate_commit and lean_statement of the selected node, of its registered dependencies im_mass_measure, monotonicity and moving_blowups, of root.abstract_dimension_reduction-a1 and of the six reused nodes; string comparison of the children's leading premises with these frozen types`
- `python3 /tmp/tr-a7/scripts/check_reuse_types.py dag.json (git show <candidate>:GMT/Ch07/Submission.lean, declared type vs dag.json up to whitespace, sorry occurrences); git cat-file -e <candidate>^{commit}; isolated-comparator-result.json and comparator-v1.log of the six reused nodes`
- `python3 /tmp/tr-a7/scripts/graph_check.py decomposition-v6.json dag.json 5000 12 (replica of _dependency_problem, _existing_lean_name_problem and the max_nodes bound)`
- `lake env lean /tmp/tr-a7/lean/Types.lean; lake env lean /tmp/tr-a7/lean/Assembly.lean; lake env lean /tmp/tr-a7/lean/TangentCheck.lean`
- `python3 reading of decomposition-v1..v6.json, decomposition-audit-v*.json, decomposition-review-receipt-v*.json and decomposition-scope-v*.json of the selected node; grep -l 'threshold_reduction' cluster-state/logs/gmt-ch07/*.log; max_nodes in .humanize/swarm-configs/9619fab3de46466e954c3c0e22455dff.json and 53f9bac0ca76443b9b296465895cebc9.json`
- `gh api repos/humanfia/math-lean-flow/contents/_recursive_lean/{runtime,store,github_runtime,decomposition_scope}.py?ref=feature/humanize-api-update-claude; grep -n '_decompose\|_solve_children\|_existing_lean_name_problem\|_overlay_accepted_children\|_reference_use_problem\|def ensure' on the fetched copies`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1/decomposition-v6.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1/decomposition-audit-v6.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1/decomposition-review-receipt-v5.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1/decomposition-scope-v6.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-abstract-dimension-reduction-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-stationary-of-minimizing-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-density-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-cone-measure-homogeneous-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-scaling-a1-rep-pushforward-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/swarm-configs/9619fab3de46466e954c3c0e22455dff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/swarm-configs/53f9bac0ca76443b9b296465895cebc9.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/cluster-state/logs/gmt-ch07/9619fab3de46466e954c3c0e22455dff.log`
- `/tmp/tr-a7/lean/Types.lean`
- `/tmp/tr-a7/lean/Assembly.lean`
- `/tmp/tr-a7/lean/TangentCheck.lean`
- `/tmp/tr-a7/scripts/graph_check.py`
- `/tmp/tr-a7/scripts/check_reuse_types.py`
- `/tmp/tr7-mlf/runtime.py`

Pins match. The snapshot manifest records project b4d606d and mathlib 25730c7c, equal to the workspace HEAD and to .lake/packages/mathlib; simongmt is 2b36630 as pinned in lakefile.toml. The snapshot Contract.lean, the workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).

Library facts the children use exist where cited:
- The snapshot mathlib has LipschitzWith.hausdorffMeasure_image_le (Hausdorff.lean:745), used in the parent assembly.
- It has addHaarScalarFactor_volume_hausdorffMeasure_ne_zero (Measure.lean:96), used for the normalization Hⁿ = c_n·μH[n].
- SimonGMT's HasApproximateTangentSpaceAt (Rectifiable.lean:102) and support = U ∖ zeroRegion are as the children's proofs use them. zeroRegion is a union of open sets with compact closure in U on which the current vanishes (CurrentLocalEquality.lean:99–117).

No dimred_tr_ identifier exists in the snapshot project, GMT, SimonGMT or dag.json.

The six reused declarations are accepted, and their candidate commits are present. Their dag.json types equal the children's lean_statements and the candidates' declarations (up to whitespace). Each candidate's only sorry is the frozen main_theorem, and each isolated comparator result passed.

Lean checks:
- All 12 child types elaborate after import GMT.Ch07.Submission.
- The parent assembly compiles from exactly the three registered dependencies, abstract_dimension_reduction and the three new children it uses, with no sorryAx.
- The tangent child compiles from exactly its four reused siblings.

The graph and name replica passes against the current 2327-node DAG, with room for 6 new nodes under max_nodes = 5000.

Attempt 6 was audited acceptable. It failed activation only because the old worker's max_nodes was 1000, below the DAG size, so it is resubmitted unchanged.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
