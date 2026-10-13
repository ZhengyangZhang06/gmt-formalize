<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.moving_blowups-a1.blowup_hypotheses-a1.moving_retractions-a1 -->

## Theorem `Submission.dimred_mbl_bh_moving_rescaled_retractions`

Let P ∈ ℕ, U ⊆ ℝ^P open, N ⊆ ℝ^P with (closure N ∖ N) ∩ U = ∅, and x ∈ U. Assume that if x ∈ N there are δ > 0 and π : ℝ^P → ℝ^P with π C¹ on B_δ(x), π(B_δ(x)) ⊆ N, π(y) = y for y ∈ N ∩ B_δ(x), and for every η > 0 some s ∈ (0, δ] with |π(y) − π(z)| ≤ (1 + η)|y − z| for y, z ∈ B_s(x). Let x_j ∈ ℝ^P with x_j → x and λ_j > 0 with λ_j → 0, and A_j := η_{x_j,λ_j}(U ∩ N) (η_{x_j,λ_j} = dilation x_j λ_j). Then for every G > 0 there are maps π_j : ℝ^P → ℝ^P (j ∈ ℕ) and G′ ∈ ℝ such that: for all large j, either A_j ∩ B_G(0) = ∅, or π_j is C¹ on B_G(0), maps B_G(0) into A_j ∩ B_{G′}(0) and π_j(y) = y for y ∈ A_j ∩ B_G(0); and for every η > 0, for all large j, either A_j ∩ B_G(0) = ∅ or |π_j(y) − π_j(z)| ≤ (1 + η)|y − z| for all y, z ∈ B_G(0). (B_s(y) = ball y s; 'for all large j' = eventually in atTop.)

Node: `root.dimension_reduction_results-a1.moving_blowups-a1.blowup_hypotheses-a1.moving_retractions-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5061

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.dimred_mbl_bh_moving_rescaled_retractions`

```lean
∀ (P : ℕ) (U N : Set (Euclid P)) (x : Euclid P) (xs : ℕ → Euclid P) (lams : ℕ → ℝ), IsOpen U → (closure N \ N) ∩ U = ∅ → x ∈ U → (x ∈ N → ∃ (δ : ℝ) (π : Euclid P → Euclid P), 0 < δ ∧ ContDiffOn ℝ 1 π (ball x δ) ∧ MapsTo π (ball x δ) N ∧ (∀ y ∈ N ∩ ball x δ, π y = y) ∧ ∀ η : ℝ, 0 < η → ∃ s : ℝ, 0 < s ∧ s ≤ δ ∧ ∀ y ∈ ball x s, ∀ z ∈ ball x s, ‖π y - π z‖ ≤ (1 + η) * ‖y - z‖) → (∀ j, 0 < lams j) → Tendsto xs atTop (𝓝 x) → Tendsto lams atTop (𝓝 0) → ∀ G : ℝ, 0 < G → ∃ (πs : ℕ → Euclid P → Euclid P) (G' : ℝ), (∀ᶠ j in atTop, dilation (xs j) (lams j) '' (U ∩ N) ∩ ball 0 G = ∅ ∨ (ContDiffOn ℝ 1 (πs j) (ball 0 G) ∧ MapsTo (πs j) (ball 0 G) (dilation (xs j) (lams j) '' (U ∩ N) ∩ ball 0 G') ∧ ∀ y ∈ dilation (xs j) (lams j) '' (U ∩ N) ∩ ball 0 G, πs j y = y)) ∧ ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, dilation (xs j) (lams j) '' (U ∩ N) ∩ ball 0 G = ∅ ∨ ∀ y ∈ ball 0 G, ∀ z ∈ ball 0 G, ‖πs j y - πs j z‖ ≤ (1 + η) * ‖y - z‖
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

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.blowup_hypotheses-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.blowup_hypotheses-a1.moving_retractions-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Part II.5–6 of the selected node's supplied proof (retractions onto N as in Simon 7.2.5(2), chapter-07.txt lines 166–174, rescaled for the blow-ups in the proof of 7.3.1, lines 317–337; the subsequence Cases A/B of the grandparent's proof become the disjunctions in the conclusion). No dependencies: the local retraction at x is a hypothesis, namely the conclusion of the sibling local_retraction, which the selected parent applies to N at x with d := m + 1 + ℓ when x ∈ N.
Notation: λ_j := lams j > 0, x_j := xs j, η_j := dilation x_j λ_j, so η_j(y) = −λ_j⁻¹x_j + λ_j⁻¹y = λ_j⁻¹(y − x_j); A_j := η_j(U ∩ N); B_s(y) := ball y s; a_j(z) := x_j + λ_jz. 'For all large j' means eventually in atTop. Fix G > 0.
1. (Elementary facts.) (a) η_j(a_j(z)) = λ_j⁻¹(λ_jz) = z for every z, and for every S ⊆ ℝ^P, z ∈ η_j(S) iff a_j(z) ∈ S (if z = η_j(y) then y = x_j + λ_jλ_j⁻¹(y − x_j) = a_j(z)). (b) If z ∈ B_G(0) and |x_j − x| + λ_jG ≤ t, then a_j(z) ∈ B_t(x), because |a_j(z) − x| ≤ |x_j − x| + λ_j|z| < |x_j − x| + λ_jG ≤ t. (c) For every c ∈ ℝ and t > 0, |x_j − x| + λ_jc → 0 (x_j → x, λ_j → 0), so |x_j − x| + λ_jc < t for all large j.
2. (Case A: x ∉ N.) Then x ∉ closure N, since otherwise x ∈ (closure N ∖ N) ∩ U = ∅ (x ∈ U). As closure N is closed, there is r_N > 0 with B_{r_N}(x) ∩ closure N = ∅. Put π_j := id for every j and G′ := 0. By 1(c) (c := G, t := r_N), |x_j − x| + λ_jG < r_N for all large j, and for such j, A_j ∩ B_G(0) = ∅: if z ∈ A_j ∩ B_G(0), then u := a_j(z) ∈ U ∩ N by 1(a) and u ∈ B_{r_N}(x) by 1(b), contradicting B_{r_N}(x) ∩ N = ∅. Hence the first eventual statement holds through its first alternative, and so does the second, for every η > 0 (same eventual set of j).
3. (Case B: x ∈ N, set-up.) The hypothesis gives δ > 0 and π : ℝ^P → ℝ^P with (i) π C¹ on B_δ(x), (ii) π(B_δ(x)) ⊆ N, (iii) π(y) = y for y ∈ N ∩ B_δ(x), (iv) for every η > 0 some s(η) ∈ (0, δ] with |π(y) − π(z)| ≤ (1 + η)|y − z| for y, z ∈ B_{s(η)}(x). Let s₁ := s(1) ∈ (0, δ], so π is 2-Lipschitz on B_{s₁}(x). U is open and x ∈ U: choose r > 0 with B_r(x) ⊆ U. Define, for every j, π_j(z) := η_j(π(a_j(z))) = λ_j⁻¹(π(x_j + λ_jz) − x_j), and G′ := 5G.
4. (Case B, first statement.) By 1(c), for all large j both |x_j − x| + λ_jG < s₁ and |x_j − x| + 5λ_jG < r hold. Fix such j. By 1(b), a_j maps B_G(0) into B_{s₁}(x) ⊆ B_δ(x). If A_j ∩ B_G(0) = ∅, the first alternative holds. Otherwise fix z₀ ∈ A_j ∩ B_G(0); we prove the second alternative. (a) (C¹.) a_j is affine (C^∞) and maps B_G(0) into B_δ(x), where π is C¹; η_j is a constant plus the continuous linear map λ_j⁻¹·id, hence C^∞; so π_j = η_j∘π∘a_j is C¹ on B_G(0) (ContDiffOn.comp, ContDiff.comp_contDiffOn). (b) (Identity.) Let z ∈ A_j ∩ B_G(0). By 1(a), u := a_j(z) ∈ U ∩ N, and u ∈ B_δ(x) by 1(b); by (iii), π(u) = u, so π_j(z) = η_j(u) = η_j(a_j(z)) = z. (c) (Range.) w := a_j(z₀) ∈ U ∩ N by 1(a), and w ∈ B_{s₁}(x) by 1(b), so π(w) = w by (iii). Let z ∈ B_G(0) and y := a_j(z) ∈ B_{s₁}(x). Then π(y) ∈ N by (ii), and, as |z − z₀| ≤ |z| + |z₀| < 2G, |π(y) − x_j| ≤ |π(y) − π(w)| + |w − x_j| ≤ 2|y − w| + λ_j|z₀| = 2λ_j|z − z₀| + λ_j|z₀| < 4λ_jG + λ_jG = 5λ_jG. Hence |π(y) − x| ≤ |π(y) − x_j| + |x_j − x| < 5λ_jG + |x_j − x| < r, so π(y) ∈ B_r(x) ⊆ U and π(y) ∈ U ∩ N. Therefore π_j(z) = η_j(π(y)) ∈ A_j and |π_j(z)| = λ_j⁻¹|π(y) − x_j| < 5G = G′, i.e. π_j(z) ∈ A_j ∩ B_{G′}(0). Thus, for all large j, A_j ∩ B_G(0) = ∅, or π_j is C¹ on B_G(0), maps B_G(0) into A_j ∩ B_{G′}(0) and is the identity on A_j ∩ B_G(0).
5. (Case B, second statement.) Let η > 0 and s := s(η). By 1(c), |x_j − x| + λ_jG < s for all large j; fix such j and y, z ∈ B_G(0). By 1(b), a_j(y), a_j(z) ∈ B_s(x), and |a_j(y) − a_j(z)| = λ_j|y − z|. Since π_j(y) − π_j(z) = λ_j⁻¹(π(a_j(y)) − x_j) − λ_j⁻¹(π(a_j(z)) − x_j) = λ_j⁻¹(π(a_j(y)) − π(a_j(z))), (iv) gives |π_j(y) − π_j(z)| ≤ λ_j⁻¹(1 + η)λ_j|y − z| = (1 + η)|y − z|. So the second alternative holds for all large j.
6. (Conclusion.) In both cases the maps π_j and the radius G′ are chosen before η, and steps 2, 4 and 5 give the two eventual statements, for every G > 0. ∎

Lean reference implementation (kernel-checked during this decomposition with Lean v4.35.0-rc3, Mathlib 25730c7c, simongmt 2b366308, after import GMT.Ch07.Submission in the contract scope `namespace GMT.Ch07`, with the contract's opens; it uses no Submission lemma; `#print axioms`: propext, Classical.choice, Quot.sound):

theorem Submission.dimred_mbl_bh_moving_rescaled_retractions : ∀ (P : ℕ) (U N : Set (Euclid P)) (x : Euclid P) (xs : ℕ → Euclid P) (lams : ℕ → ℝ), IsOpen U → (closure N \ N) ∩ U = ∅ → x ∈ U → (x ∈ N → ∃ (δ : ℝ) (π : Euclid P → Euclid P), 0 < δ ∧ ContDiffOn ℝ 1 π (ball x δ) ∧ MapsTo π (ball x δ) N ∧ (∀ y ∈ N ∩ ball x δ, π y = y) ∧ ∀ η : ℝ, 0 < η → ∃ s : ℝ, 0 < s ∧ s ≤ δ ∧ ∀ y ∈ ball x s, ∀ z ∈ ball x s, ‖π y - π z‖ ≤ (1 + η) * ‖y - z‖) → (∀ j, 0 < lams j) → Tendsto xs atTop (𝓝 x) → Tendsto lams atTop (𝓝 0) → ∀ G : ℝ, 0 < G → ∃ (πs : ℕ → Euclid P → Euclid P) (G' : ℝ), (∀ᶠ j in atTop, dilation (xs j) (lams j) '' (U ∩ N) ∩ ball 0 G = ∅ ∨ (ContDiffOn ℝ 1 (πs j) (ball 0 G) ∧ MapsTo (πs j) (ball 0 G) (dilation (xs j) (lams j) '' (U ∩ N) ∩ ball 0 G') ∧ ∀ y ∈ dilation (xs j) (lams j) '' (U ∩ N) ∩ ball 0 G, πs j y = y)) ∧ ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, dilation (xs j) (lams j) '' (U ∩ N) ∩ ball 0 G = ∅ ∨ ∀ y ∈ ball 0 G, ∀ z ∈ ball 0 G, ‖πs j y - πs j z‖ ≤ (1 + η) * ‖y - z‖ := by
  intro P U N x xs lams hU hcl hxU hret hlams hxs hlam0 G hG
  -- `η_{a,λ}(y) = λ⁻¹ • (y - a)`
  have hdil : ∀ (a : Euclid P) (lam : ℝ) (y : Euclid P), dilation a lam y = lam⁻¹ • (y - a) := by
    intro a lam y
    simp only [dilation, dilationCLM, FunLike.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.coe_id', id_eq, smul_sub]
    abel
  -- `z ∈ η_{a,λ}(S) ↔ a + λ z ∈ S`
  have hmem_img : ∀ (a : Euclid P) (lam : ℝ) (S : Set (Euclid P)) (z : Euclid P), lam ≠ 0 →
      (z ∈ dilation a lam '' S ↔ a + lam • z ∈ S) := by
    intro a lam S z hlam
    constructor
    · rintro ⟨y, hy, rfl⟩
      rwa [hdil, smul_smul, mul_inv_cancel₀ hlam, one_smul, add_sub_cancel]
    · intro h
      exact ⟨a + lam • z, h, by rw [hdil, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hlam,
        one_smul]⟩
  -- `|x_j - x| + λ_j c` is eventually below any positive bound
  have hsmall : ∀ (c t : ℝ), 0 < t → ∀ᶠ j in atTop, dist (xs j) x + lams j * c < t := by
    intro c t ht
    have h1 : Tendsto (fun j => dist (xs j) x) atTop (𝓝 0) :=
      (tendsto_iff_dist_tendsto_zero).1 hxs
    have h2 : Tendsto (fun j => lams j * c) atTop (𝓝 0) := by
      simpa using hlam0.mul_const c
    have h0 : Tendsto (fun j => dist (xs j) x + lams j * c) atTop (𝓝 0) := by
      simpa using h1.add h2
    exact (tendsto_order.1 h0).2 t ht
  -- `x_j + λ_j z ∈ B_t(x)` for `z ∈ B_G(0)` once `|x_j - x| + λ_j G ≤ t`
  have haff : ∀ (j : ℕ) (z : Euclid P) (t : ℝ), z ∈ ball (0 : Euclid P) G →
      dist (xs j) x + lams j * G ≤ t → xs j + lams j • z ∈ ball x t := by
    intro j z t hz ht
    have hlam := hlams j
    rw [mem_ball, dist_zero_right] at hz
    rw [mem_ball]
    calc dist (xs j + lams j • z) x ≤ dist (xs j + lams j • z) (xs j) + dist (xs j) x :=
          dist_triangle _ _ _
      _ = lams j * ‖z‖ + dist (xs j) x := by
          rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hlam.le]
      _ < lams j * G + dist (xs j) x := by
          have := mul_lt_mul_of_pos_left hz hlam
          linarith
      _ ≤ t := by linarith
  by_cases hxN : x ∈ N
  · -- Case B: `x ∈ N`; rescale the local retraction at `x`
    obtain ⟨δ, π, hδ, hC, hmaps, hid, hlip⟩ := hret hxN
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU x hxU
    obtain ⟨s₁, hs₁, hs₁δ, hlip1⟩ := hlip 1 one_pos
    refine ⟨fun j z => dilation (xs j) (lams j) (π (xs j + lams j • z)), 5 * G, ?_, ?_⟩
    · filter_upwards [hsmall G s₁ hs₁, hsmall (5 * G) r hr] with j hj1 hj2
      have hlam := hlams j
      by_cases hempty : dilation (xs j) (lams j) '' (U ∩ N) ∩ ball 0 G = ∅
      · exact Or.inl hempty
      right
      obtain ⟨z₀, hz₀A, hz₀G⟩ := Set.nonempty_iff_ne_empty.2 hempty
      have hw : xs j + lams j • z₀ ∈ U ∩ N := (hmem_img _ _ _ _ hlam.ne').1 hz₀A
      have hwball : xs j + lams j • z₀ ∈ ball x s₁ := haff j z₀ s₁ hz₀G hj1.le
      have hπw : π (xs j + lams j • z₀) = xs j + lams j • z₀ :=
        hid _ ⟨hw.2, ball_subset_ball hs₁δ hwball⟩
      have hmapsδ : MapsTo (fun z : Euclid P => xs j + lams j • z) (ball 0 G) (ball x δ) :=
        fun z hz => ball_subset_ball hs₁δ (haff j z s₁ hz hj1.le)
      refine ⟨?_, ?_, ?_⟩
      · -- `π_j` is `C¹` on `B_G(0)`
        have hdilC : ContDiff ℝ 1 (dilation (xs j) (lams j)) := by
          unfold dilation
          exact contDiff_const.add (dilationCLM P (lams j)).contDiff
        have haffC : ContDiff ℝ 1 (fun z : Euclid P => xs j + lams j • z) :=
          contDiff_const.add (contDiff_id.const_smul (lams j))
        exact hdilC.comp_contDiffOn (hC.comp haffC.contDiffOn hmapsδ)
      · -- `π_j` maps `B_G(0)` into `A_j ∩ B_{5G}(0)`
        intro z hz
        have hy1 : xs j + lams j • z ∈ ball x s₁ := haff j z s₁ hz hj1.le
        have hzG : ‖z‖ < G := by simpa using hz
        have hz₀G' : ‖z₀‖ < G := by simpa using hz₀G
        have hbound : ‖π (xs j + lams j • z) - xs j‖ < 5 * (lams j * G) := by
          have hl := hlip1 _ hy1 _ hwball
          rw [hπw] at hl
          have e1 : ‖xs j + lams j • z - (xs j + lams j • z₀)‖ = lams j * ‖z - z₀‖ := by
            rw [add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_of_nonneg hlam.le]
          have e2 : ‖xs j + lams j • z₀ - xs j‖ = lams j * ‖z₀‖ := by
            rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hlam.le]
          have hzz : ‖z - z₀‖ < 2 * G := by
            calc ‖z - z₀‖ ≤ ‖z‖ + ‖z₀‖ := norm_sub_le _ _
              _ < 2 * G := by linarith
          have h4 : lams j * ‖z - z₀‖ < lams j * (2 * G) := mul_lt_mul_of_pos_left hzz hlam
          have h5 : lams j * ‖z₀‖ < lams j * G := mul_lt_mul_of_pos_left hz₀G' hlam
          calc ‖π (xs j + lams j • z) - xs j‖
              ≤ ‖π (xs j + lams j • z) - (xs j + lams j • z₀)‖ + ‖xs j + lams j • z₀ - xs j‖ :=
                norm_sub_le_norm_sub_add_norm_sub _ _ _
            _ ≤ (1 + 1) * (lams j * ‖z - z₀‖) + lams j * ‖z₀‖ := by
                rw [e2, ← e1]
                linarith
            _ < 5 * (lams j * G) := by nlinarith
        have hπyU : π (xs j + lams j • z) ∈ U := by
          apply hrU
          rw [mem_ball, dist_eq_norm]
          calc ‖π (xs j + lams j • z) - x‖
              ≤ ‖π (xs j + lams j • z) - xs j‖ + ‖xs j - x‖ :=
                norm_sub_le_norm_sub_add_norm_sub _ _ _
            _ < 5 * (lams j * G) + dist (xs j) x := by
                rw [← dist_eq_norm (xs j) x]
                linarith
            _ < r := by linarith
        have hπyN : π (xs j + lams j • z) ∈ N := hmaps (hmapsδ hz)
        refine ⟨⟨π (xs j + lams j • z), ⟨hπyU, hπyN⟩, rfl⟩, ?_⟩
        show dilation (xs j) (lams j) (π (xs j + lams j • z)) ∈ ball 0 (5 * G)
        rw [mem_ball, dist_zero_right, hdil, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hlam.le)]
        calc (lams j)⁻¹ * ‖π (xs j + lams j • z) - xs j‖
            < (lams j)⁻¹ * (5 * (lams j * G)) :=
              mul_lt_mul_of_pos_left hbound (inv_pos.2 hlam)
          _ = 5 * G := by field_simp
      · -- `π_j` is the identity on `A_j ∩ B_G(0)`
        rintro z ⟨hzA, hz⟩
        have hu : xs j + lams j • z ∈ U ∩ N := (hmem_img _ _ _ _ hlam.ne').1 hzA
        show dilation (xs j) (lams j) (π (xs j + lams j • z)) = z
        rw [hid _ ⟨hu.2, hmapsδ hz⟩, hdil, add_sub_cancel_left, smul_smul,
          inv_mul_cancel₀ hlam.ne', one_smul]
    · -- the almost-isometry estimate
      intro η hη
      obtain ⟨s, hs, hsδ, hlipη⟩ := hlip η hη
      filter_upwards [hsmall G s hs] with j hj
      right
      intro y hy z hz
      have hlam := hlams j
      have hy' := haff j y s hy hj.le
      have hz' := haff j z s hz hj.le
      show ‖dilation (xs j) (lams j) (π (xs j + lams j • y)) -
          dilation (xs j) (lams j) (π (xs j + lams j • z))‖ ≤ (1 + η) * ‖y - z‖
      rw [hdil, hdil, ← smul_sub, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hlam.le)]
      have h1 := hlipη _ hy' _ hz'
      have h2 : ‖xs j + lams j • y - (xs j + lams j • z)‖ = lams j * ‖y - z‖ := by
        rw [add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_of_nonneg hlam.le]
      have h3 : π (xs j + lams j • y) - xs j - (π (xs j + lams j • z) - xs j) =
          π (xs j + lams j • y) - π (xs j + lams j • z) := by abel
      rw [h3]
      calc (lams j)⁻¹ * ‖π (xs j + lams j • y) - π (xs j + lams j • z)‖
          ≤ (lams j)⁻¹ * ((1 + η) * (lams j * ‖y - z‖)) := by
            rw [← h2]
            exact mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hlam.le)
        _ = (1 + η) * ‖y - z‖ := by field_simp
  · -- Case A: `x ∉ N`, so `x ∉ closure N` and `A_j ∩ B_G(0) = ∅` eventually
    have hxcl : x ∉ closure N := by
      intro h
      have : x ∈ (closure N \ N) ∩ U := ⟨⟨h, hxN⟩, hxU⟩
      rw [hcl] at this
      exact this
    obtain ⟨ε, hε, hεN⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl x hxcl
    have hev : ∀ᶠ j in atTop, dilation (xs j) (lams j) '' (U ∩ N) ∩ ball 0 G = ∅ := by
      filter_upwards [hsmall G ε hε] with j hj
      rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨hzA, hz⟩
      have hu : xs j + lams j • z ∈ U ∩ N := (hmem_img _ _ _ _ (hlams j).ne').1 hzA
      exact hεN (haff j z ε hz hj.le) (subset_closure hu.2)
    refine ⟨fun _ => id, 0, ?_, ?_⟩
    · filter_upwards [hev] with j hj
      exact Or.inl hj
    · intro η _
      filter_upwards [hev] with j hj
      exact Or.inl hj

## Key steps

1. z ∈ η_j(S) iff x_j + λ_jz ∈ S, and |x_j − x| + λ_jc is eventually below any t > 0.
2. x ∉ N: x ∉ closure N, so a ball B_{r_N}(x) misses N and A_j ∩ B_G(0) = ∅ for all large j (π_j := id, G′ := 0).
3. x ∈ N: π_j := η_j∘π∘(z ↦ x_j + λ_jz), G′ := 5G; C¹ and the identity on A_j ∩ B_G(0) follow from (i), (iii).
4. Given z₀ ∈ A_j ∩ B_G(0), the 2-Lipschitz bound on B_{s(1)}(x) gives |π(x_j + λ_jz) − x_j| < 5λ_jG, so π_j maps B_G(0) into A_j ∩ B_{5G}(0).
5. (1 + η)-Lipschitz bounds of π on B_{s(η)}(x) rescale to (1 + η)-Lipschitz bounds of π_j on B_G(0) for all large j.

## Reference use

### local-project

Queries:
- `cat SNAP/manifest.json; git -C SNAP/project rev-parse HEAD; git -C SNAP/mathlib rev-parse HEAD; cmp SNAP/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Submission.lean GMT/Ch07/Contract.lean`
- `rg -n 'def dilation|def blowUp|def IsEmbeddedSubmanifold|def IsMinimizingIn|def BoundaryVanishes' SNAP/project/GMT/Ch07/Contract.lean`
- `rg -n 'def toOpenPartialHomeomorph|def localInverse|theorem to_localInverse|theorem mem_toOpenPartialHomeomorph_source' SNAP/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/*.lean`
- `rg -n 'theorem OpenPartialHomeomorph.contDiffAt_symm' SNAP/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `rg -n 'norm_image_sub_le_of_norm_fderiv_le' SNAP/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `rg -n 'theorem starProjection_norm_le' SNAP/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean; rg -n 'noncomputable def ofInjective' SNAP/mathlib/Mathlib/Algebra/Module/Submodule/Equiv.lean`
- `rg -n 'theorem withDensity_apply|theorem restrict_restrict' SNAP/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean SNAP/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `rg -n 'Homeomorph.smulOfNeZero' SNAP/mathlib/Mathlib/Topology/Algebra/ConstMulAction.lean`
- `rg -ln 'retraction' SNAP/project/GMT (no match)`
- `sed -n / grep -n on simongmt Chapter06 AffineCurrentPushforward.lean (affinePullbackForm, affinePushforward_apply, boundary_affinePushforward), Mass.lean (massOn, massOn_mono), Currents.lean (GeometricCurrentOn.ext, zero_apply)`
- `python3 scans of RUN/dag.json: accepted declarations mentioning blowUp, dilation, IsEmbeddedSubmanifold or retraction; lean_name collisions for dimred_mbl_bh_* (none); status of dtc_bc_local_retraction and of the dtc_bc_blowUp_hypotheses subtree (not accepted)`
- `git show a8aa184/f64597f/17c63f2/d49dda9:GMT/Ch07/Submission.lean | grep -n 'theorem Submission.<reused name> '`
- `sed -n 160,185p and 285,345p book/chapter-07.txt (Remark 7.2.5, Theorem 7.3.1 and its proof)`
- `lake env lean on /tmp/bh_split/{Elab,AssemblyCond,N1check,N3check,Concrete}.lean and /tmp/bh_split/final/Final.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Module/Submodule/Equiv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/ConstMulAction.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-blowup-hypotheses-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-retraction-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/tmp/bh_split/final/Final.lean`

Pins match (project b4d606d, Mathlib 25730c7c, SimonGMT 2b366308 in the lake packages), and Submission.lean is byte-identical to the snapshot's frozen contract. The snapshot supplies everything the children need. From Mathlib: the C¹ inverse function theorem (ContDiffAt.toOpenPartialHomeomorph, localInverse, to_localInverse, OpenPartialHomeomorph.contDiffAt_symm), the mean value inequality (Convex.norm_image_sub_le_of_norm_fderiv_le), starProjection_norm_le, LinearEquiv.ofInjective, withDensity_apply, Measure.restrict_restrict and Homeomorph.smulOfNeZero. From SimonGMT: the affine pull-back and push-forward of currents, massOn and massOn_mono. There is no local retraction onto submanifolds in the project ('retraction' in project/GMT: no match) or among accepted DAG declarations, so local_retraction is a genuine new obligation. Accepted DAG declarations reused with identical types: dtc_blowUp_isMinimizingIn, dtc_blowUp_algebra, dtc_blowUp_massOn_image and dor_imrep_massOn_eq_measure_and_support, each verified verbatim in its commit. The analogous fixed-centre nodes (dtc_bc_blowUp_hypotheses and its children, dtc_bc_local_retraction) are not accepted and cannot be shared. All child types elaborate, and the assembly proves the selected type.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
