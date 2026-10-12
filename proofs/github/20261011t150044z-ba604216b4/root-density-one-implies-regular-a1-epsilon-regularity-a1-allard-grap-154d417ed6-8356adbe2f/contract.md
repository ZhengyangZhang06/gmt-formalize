<!-- theorem-id: gmt-ch07/root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.lipschitz_approximation-a1.cone_estimate-a1 -->

## Theorem `Submission.dorag_lip_good_set_cone_estimate`

For n, k ∈ ℕ and C₃, C₆ ≥ 1 there is C₈ > 0, depending only on n, k, C₃ and C₆ (it is chosen after n, k, C₃, C₆, as in the Lean quantifier order ∀ (n k : ℕ) (C₃ C₆ : ℝ), … ∃ C₈), with the following property. Let μ be a measure on ℝ^{n+k}, τ a map from ℝ^{n+k} to linear subspaces such that x ↦ p_{τ(x)} is μ-a.e. strongly measurable, T₀ a subspace (P := p_{T₀}, Qu := u − Pu), ξ ∈ ℝ^{n+k}, σ₀ > 0, ε ≥ 0, β > 0 and L > 0 with ε ≤ βL. Assume:
(H1) for every y ∈ spt μ ∩ B_{3σ₀/4}(ξ) and t ∈ (0, σ₀/2] there is a subspace S with |(x − y) − p_S(x − y)| ≤ C₃εt for all x ∈ spt μ ∩ B_t(y), and ∫_{B_{t/2}(y)} |p_{τ(x)} − p_S|² dμ ≤ C₃ε²(t/2)ⁿ;
(H2) ω_n tⁿ ≤ 2μ(B_t(y)) for all y ∈ spt μ ∩ B_{3σ₀/4}(ξ) and t ∈ (0, σ₀/4];
(H3) |Q(x − ξ)| ≤ C₆εσ₀ for all x ∈ spt μ ∩ B_{σ₀}(ξ).
Then for all y₁, y₂ ∈ spt μ ∩ B_{3σ₀/4}(ξ) such that ∫_{B_{t/2}(y₁)} |p_{τ(x)} − P|² dμ ≤ β²L²tⁿ for every t ∈ (0, σ₀/2], one has |Q(y₂ − y₁)| ≤ C₈βL|y₂ − y₁|.
Conventions: |A|² := Σ_i |A e_i|² (e_i = EuclideanSpace.single i 1); integrals are lower Lebesgue integrals of ENNReal.ofReal; balls are closed; ω_n = unitBallVolume n.

Node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.lipschitz_approximation-a1.cone_estimate-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2027

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.dorag_lip_good_set_cone_estimate`

```lean
∀ (n k : ℕ) (C₃ C₆ : ℝ), 1 ≤ C₃ → 1 ≤ C₆ → ∃ C₈ : ℝ, 0 < C₈ ∧ ∀ (μ : Measure (Euclid (n + k))) (τ : Euclid (n + k) → Submodule ℝ (Euclid (n + k))) (T₀ : Submodule ℝ (Euclid (n + k))) (ξ : Euclid (n + k)) (σ₀ ε β L : ℝ), AEStronglyMeasurable (fun x => (τ x).starProjection) μ → 0 < σ₀ → 0 ≤ ε → 0 < β → 0 < L → ε ≤ β * L → (∀ y ∈ μ.support ∩ closedBall ξ (3 * σ₀ / 4), ∀ t : ℝ, 0 < t → t ≤ σ₀ / 2 → ∃ S : Submodule ℝ (Euclid (n + k)), (∀ x ∈ μ.support ∩ closedBall y t, ‖(x - y) - S.starProjection (x - y)‖ ≤ C₃ * ε * t) ∧ ∫⁻ x in closedBall y (t / 2), ENNReal.ofReal (∑ i : Fin (n + k), ‖(τ x).starProjection (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ ≤ ENNReal.ofReal (C₃ * ε ^ 2 * (t / 2) ^ n)) → (∀ y ∈ μ.support ∩ closedBall ξ (3 * σ₀ / 4), ∀ t : ℝ, 0 < t → t ≤ σ₀ / 4 → unitBallVolume n * ENNReal.ofReal (t ^ n) ≤ 2 * μ (closedBall y t)) → (∀ x ∈ μ.support ∩ closedBall ξ σ₀, ‖(x - ξ) - T₀.starProjection (x - ξ)‖ ≤ C₆ * ε * σ₀) → ∀ y₁ ∈ μ.support ∩ closedBall ξ (3 * σ₀ / 4), ∀ y₂ ∈ μ.support ∩ closedBall ξ (3 * σ₀ / 4), (∀ t : ℝ, 0 < t → t ≤ σ₀ / 2 → ∫⁻ x in closedBall y₁ (t / 2), ENNReal.ofReal (∑ i : Fin (n + k), ‖(τ x).starProjection (EuclideanSpace.single i (1 : ℝ)) - T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ ≤ ENNReal.ofReal (β ^ 2 * L ^ 2 * t ^ n)) → ‖(y₂ - y₁) - T₀.starProjection (y₂ - y₁)‖ ≤ C₈ * β * L * ‖y₂ - y₁‖
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

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.lipschitz_approximation-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.lipschitz_approximation-a1.cone_estimate-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof Step 5, 'For y₁, y₂ ∈ G: |Q(y₂ − y₁)| ≤ C₈βL|y₂ − y₁|'. The first case is Simon Ch. 5, proof of 2.6, (3)–(4). The second case (t > σ₀/2) is the parent's correction: Simon treats only the first.
In the parent's application:
- μ = R.measure and τ = approxTangentPlane n R.carrier;
- ε = δ^α;
- (H1) is the sibling affine approximation at (y, t);
- (H2) is the lower density bound (b);
- (H3) is the parent hypothesis (ii).
Notation: P := T₀.starProjection, Qu := u − Pu, p_x := (τ x).starProjection, |A|² := Σ_i ‖A e_i‖² (so the integrands are ofReal|p_x − p_S|² and ofReal|p_x − P|²), ℝ≥0∞-valued lower integrals.
0. Constants. Let ω := (unitBallVolume n).toReal. unitBallVolume n is the Lebesgue measure of the open unit ball of ℝⁿ, which is positive (measure_ball_pos) and finite (measure_ball_lt_top). Hence ω > 0 and unitBallVolume n = ofReal ω. Define C₈ := max(C₃ + √((8C₃ + 2^{n+3})/ω), 4C₆) > 0. C₈ is fixed once n, k, C₃, C₆ are given, before μ, τ, T₀, ξ, σ₀, ε, β, L, as the statement's quantifier order requires. The formula happens not to involve k, but the statement claims only dependence on n, k, C₃ and C₆.
1. Hilbert–Schmidt facts.
   (a) ‖Au‖ ≤ |A|·‖u‖ for every linear map A of ℝ^{n+k} and every u. Write u = Σ_i u_i e_i; then Au = Σ_i u_i A e_i, so ‖Au‖ ≤ Σ_i |u_i|‖A e_i‖ ≤ (Σ_i u_i²)^{1/2}(Σ_i ‖A e_i‖²)^{1/2} = ‖u‖·|A| by Cauchy–Schwarz.
   (b) For subspaces S, T₀ and every x: |p_S − P|² ≤ 2|p_x − p_S|² + 2|p_x − P|². Indeed (p_S − P)e_i = (p_x − P)e_i − (p_x − p_S)e_i and ‖a − b‖² ≤ 2‖a‖² + 2‖b‖².
2. Measurability. For a fixed subspace S, the map A ↦ ofReal(Σ_i ‖A e_i − p_S e_i‖²) is continuous on E →L[ℝ] E. Composing it with the a.e. strongly measurable x ↦ p_x (Continuous.comp_aestronglyMeasurable, then aemeasurable) shows that x ↦ ofReal|p_x − p_S|² is μ-a.e. measurable, also for every restriction μ⌞B. The same holds with S = T₀.
3. Reduction. Fix y₁, y₂ as in the statement and put u := y₂ − y₁, t := ‖u‖. If t = 0, then u = 0 and both sides are 0. Assume t > 0.
4. Case 0 < t ≤ σ₀/2.
   (i) (H1) at (y₁, t) gives S with ‖(x − y₁) − p_S(x − y₁)‖ ≤ C₃εt for x ∈ spt μ ∩ B_t(y₁), and ∫_{B_{t/2}(y₁)} ofReal|p_x − p_S|² dμ ≤ ofReal(C₃ε²(t/2)ⁿ). Since y₂ ∈ spt μ and dist(y₂, y₁) = t, ‖u − p_S u‖ ≤ C₃εt.
   (ii) The good-set hypothesis at this t gives ∫_{B_{t/2}(y₁)} ofReal|p_x − P|² dμ ≤ ofReal(β²L²tⁿ).
   (iii) Let h := |p_S − P|² ≥ 0, a constant, and B := B_{t/2}(y₁).
      - Pointwise, ofReal(h) ≤ 2·ofReal|p_x − p_S|² + 2·ofReal|p_x − P|² (fact 1(b), ofReal_add, ofReal_mul).
      - Integrate over B. On the left use setLIntegral_const. On the right use additivity of the lower integral when one summand is a.e.-measurable (lintegral_add_left', by step 2) and pull out the constant 2.
      - Result: ofReal(h)·μ(B) ≤ 2·ofReal(C₃ε²(t/2)ⁿ) + 2·ofReal(β²L²tⁿ).
   (iv) Bound h.
      - (H2) at (y₁, t/2), valid since t/2 ≤ σ₀/4, gives ofReal(ω)·ofReal((t/2)ⁿ) ≤ 2μ(B).
      - Hence ofReal(h·ω·(t/2)ⁿ) ≤ 2·ofReal(h)·μ(B) ≤ ofReal(4C₃ε²(t/2)ⁿ + 4β²L²tⁿ).
      - Both sides are finite, so h·ω·(t/2)ⁿ ≤ 4C₃ε²(t/2)ⁿ + 4β²L²tⁿ (ENNReal.ofReal_le_ofReal_iff).
      - Divide by ω(t/2)ⁿ > 0 and use tⁿ = 2ⁿ(t/2)ⁿ and ε² ≤ β²L² (from 0 ≤ ε ≤ βL): h ≤ (4C₃ε² + 2^{n+2}β²L²)/ω ≤ (8C₃ + 2^{n+3})β²L²/ω.
      - Therefore √h ≤ √((8C₃ + 2^{n+3})/ω)·βL.
   (v) Qu = (u − p_S u) + (p_S − P)u. By (i) and fact 1(a), ‖Qu‖ ≤ C₃εt + √h·t ≤ (C₃ + √((8C₃ + 2^{n+3})/ω))·βL·t ≤ C₈βL‖y₂ − y₁‖, using ε ≤ βL.
5. Case t > σ₀/2.
   - Since 3σ₀/4 ≤ σ₀, y₁ and y₂ lie in spt μ ∩ B_{σ₀}(ξ), so (H3) gives ‖Q(yᵢ − ξ)‖ ≤ C₆εσ₀.
   - Q is linear and Qu = Q(y₂ − ξ) − Q(y₁ − ξ), so ‖Qu‖ ≤ 2C₆εσ₀.
   - Since σ₀ < 2t, ε ≤ βL and C₆ > 0: 2C₆εσ₀ ≤ 4C₆εt ≤ 4C₆βLt ≤ C₈βL‖y₂ − y₁‖. ∎
Formal check. The following declarations compile after import GMT.Ch07.Submission in the comparator scope, with no warnings, using the witness C₈ of step 0. They consist of seven helper theorems with the private prefix Submission.dorag_lip_cone_estimate_aux_ (Hilbert–Schmidt bound, the squared triangle inequality, the pointwise bound of fact 1(b) in ℝ≥0∞, a.e.-measurability, set integration, and two real-arithmetic steps), followed by Submission.dorag_lip_good_set_cone_estimate with the exact frozen type. #print axioms gives propext, Classical.choice, Quot.sound.
/-- Hilbert–Schmidt bound `‖A u‖ ≤ |A| ‖u‖` with `|A|² = ∑ᵢ ‖A eᵢ‖²`. -/
theorem Submission.dorag_lip_cone_estimate_aux_hs_bound {N : ℕ}
    (A : Euclid N →L[ℝ] Euclid N) (u : Euclid N) :
    ‖A u‖ ≤ Real.sqrt (∑ i : Fin N, ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * ‖u‖ := by
  have hu : u = ∑ i : Fin N, u i • EuclideanSpace.single i (1 : ℝ) := by
    have := (EuclideanSpace.basisFun (Fin N) ℝ).sum_repr u
    simpa using this.symm
  have hAu : A u = ∑ i : Fin N, u i • A (EuclideanSpace.single i (1 : ℝ)) := by
    conv_lhs => rw [hu]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smul A _ _
  have h1 : ‖A u‖ ≤ ∑ i : Fin N, |u i| * ‖A (EuclideanSpace.single i (1 : ℝ))‖ := by
    rw [hAu]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    rw [norm_smul, Real.norm_eq_abs]
  have h2 : (∑ i : Fin N, |u i| * ‖A (EuclideanSpace.single i (1 : ℝ))‖) ^ 2 ≤
      (∑ i : Fin N, |u i| ^ 2) * ∑ i : Fin N, ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h3 : ∑ i : Fin N, |u i| ^ 2 = ‖u‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.sum_congr rfl fun i _ => sq_abs _
  rw [h3] at h2
  have h4 : ∑ i : Fin N, |u i| * ‖A (EuclideanSpace.single i (1 : ℝ))‖ ≤
      Real.sqrt (‖u‖ ^ 2 * ∑ i : Fin N, ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) :=
    (le_abs_self _).trans (Real.abs_le_sqrt h2)
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h4
  calc ‖A u‖ ≤ _ := h1
    _ ≤ _ := h4
    _ = _ := mul_comm _ _

/-- `‖b - c‖² ≤ 2‖a - b‖² + 2‖a - c‖²`. -/
theorem Submission.dorag_lip_cone_estimate_aux_sq_tri {E : Type*} [SeminormedAddCommGroup E]
    (a b c : E) : ‖b - c‖ ^ 2 ≤ 2 * ‖a - b‖ ^ 2 + 2 * ‖a - c‖ ^ 2 := by
  have h : ‖b - c‖ ≤ ‖a - b‖ + ‖a - c‖ := by
    calc ‖b - c‖ = ‖(a - c) - (a - b)‖ := by congr 1; abel
      _ ≤ ‖a - c‖ + ‖a - b‖ := norm_sub_le _ _
      _ = ‖a - b‖ + ‖a - c‖ := add_comm _ _
  have h0 : 0 ≤ ‖b - c‖ := norm_nonneg _
  have hab := norm_nonneg (a - b)
  have hac := norm_nonneg (a - c)
  have hsq : ‖b - c‖ * ‖b - c‖ ≤ (‖a - b‖ + ‖a - c‖) * (‖a - b‖ + ‖a - c‖) :=
    mul_le_mul h h h0 (by positivity)
  nlinarith [sq_nonneg (‖a - b‖ - ‖a - c‖)]

/-- Pointwise Hilbert–Schmidt triangle bound, in `ℝ≥0∞`. -/
theorem Submission.dorag_lip_cone_estimate_aux_pt {N : ℕ} (A B C : Euclid N →L[ℝ] Euclid N) :
    ENNReal.ofReal (∑ i : Fin N, ‖B (EuclideanSpace.single i (1 : ℝ)) -
        C (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ≤
      2 * ENNReal.ofReal (∑ i : Fin N, ‖A (EuclideanSpace.single i (1 : ℝ)) -
        B (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) +
      2 * ENNReal.ofReal (∑ i : Fin N, ‖A (EuclideanSpace.single i (1 : ℝ)) -
        C (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) := by
  have hle : ∑ i : Fin N, ‖B (EuclideanSpace.single i (1 : ℝ)) -
        C (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 ≤
      2 * ∑ i : Fin N, ‖A (EuclideanSpace.single i (1 : ℝ)) -
        B (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 +
      2 * ∑ i : Fin N, ‖A (EuclideanSpace.single i (1 : ℝ)) -
        C (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => Submission.dorag_lip_cone_estimate_aux_sq_tri _ _ _
  refine (ENNReal.ofReal_le_ofReal hle).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]

/-- a.e.-measurability of the tilt integrand. -/
theorem Submission.dorag_lip_cone_estimate_aux_aemeas {N : ℕ} {μ : Measure (Euclid N)}
    {τ : Euclid N → Submodule ℝ (Euclid N)} (S : Submodule ℝ (Euclid N))
    (hτ : AEStronglyMeasurable (fun x => (τ x).starProjection) μ) :
    AEMeasurable (fun x => ENNReal.ofReal (∑ i : Fin N,
      ‖(τ x).starProjection (EuclideanSpace.single i (1 : ℝ)) -
        S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2)) μ := by
  have hc : Continuous (fun A : Euclid N →L[ℝ] Euclid N => ENNReal.ofReal (∑ i : Fin N,
      ‖A (EuclideanSpace.single i (1 : ℝ)) -
        S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2)) := by
    refine ENNReal.continuous_ofReal.comp ?_
    exact continuous_finsetSum _ fun i _ =>
      ((continuous_id.clm_apply continuous_const).sub continuous_const).norm.pow 2
  exact (hc.comp_aestronglyMeasurable hτ).aemeasurable

/-- Integrating a pointwise bound over a set. -/
theorem Submission.dorag_lip_cone_estimate_aux_lint {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s : Set α} {f g : α → ℝ≥0∞} {c : ℝ≥0∞}
    (hf : AEMeasurable f (μ.restrict s)) (hfg : ∀ x, c ≤ 2 * f x + 2 * g x) :
    c * μ s ≤ 2 * ∫⁻ x in s, f x ∂μ + 2 * ∫⁻ x in s, g x ∂μ := by
  rw [← setLIntegral_const]
  calc ∫⁻ _ in s, c ∂μ ≤ ∫⁻ x in s, (2 * f x + 2 * g x) ∂μ := lintegral_mono hfg
    _ = ∫⁻ x in s, 2 * f x ∂μ + ∫⁻ x in s, 2 * g x ∂μ :=
        lintegral_add_left' (hf.const_mul 2) _
    _ = 2 * ∫⁻ x in s, f x ∂μ + 2 * ∫⁻ x in s, g x ∂μ := by
        rw [lintegral_const_mul' 2 f ENNReal.ofNat_ne_top,
          lintegral_const_mul' 2 g ENNReal.ofNat_ne_top]

/-- From the `ℝ≥0∞` inequalities to a real inequality. -/
theorem Submission.dorag_lip_cone_estimate_aux_real {h w X Y s : ℝ} {m : ℝ≥0∞}
    (hh : 0 ≤ h) (hw : 0 ≤ w) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (h1 : ENNReal.ofReal h * m ≤ 2 * ENNReal.ofReal X + 2 * ENNReal.ofReal Y)
    (h2 : ENNReal.ofReal w * ENNReal.ofReal s ≤ 2 * m) :
    h * w * s ≤ 4 * X + 4 * Y := by
  have h3 : ENNReal.ofReal (h * w * s) ≤ ENNReal.ofReal (4 * X + 4 * Y) := by
    calc ENNReal.ofReal (h * w * s)
        = ENNReal.ofReal h * (ENNReal.ofReal w * ENNReal.ofReal s) := by
          rw [ENNReal.ofReal_mul (mul_nonneg hh hw), ENNReal.ofReal_mul hh, mul_assoc]
      _ ≤ ENNReal.ofReal h * (2 * m) := by gcongr
      _ = 2 * (ENNReal.ofReal h * m) := by ring
      _ ≤ 2 * (2 * ENNReal.ofReal X + 2 * ENNReal.ofReal Y) := by gcongr
      _ = ENNReal.ofReal (4 * X + 4 * Y) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num),
            ENNReal.ofReal_ofNat]
          ring
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3

/-- Dividing out the radius factor. -/
theorem Submission.dorag_lip_cone_estimate_aux_div {h w C₃ ε β L s : ℝ} (n : ℕ)
    (hw : 0 < w) (hs : 0 < s) (hC₃ : 0 ≤ C₃) (hε : 0 ≤ ε) (hεβL : ε ≤ β * L)
    (H : h * w * s ≤ 4 * (C₃ * ε ^ 2 * s) + 4 * (β ^ 2 * L ^ 2 * (2 ^ n * s))) :
    h ≤ (8 * C₃ + 2 ^ (n + 3)) / w * (β * L) ^ 2 := by
  have h1 : h * w ≤ 4 * C₃ * ε ^ 2 + 4 * 2 ^ n * (β * L) ^ 2 := by
    have : h * w * s ≤ (4 * C₃ * ε ^ 2 + 4 * 2 ^ n * (β * L) ^ 2) * s := by
      calc h * w * s ≤ _ := H
        _ = _ := by ring
    exact le_of_mul_le_mul_right this hs
  have hε2 : ε ^ 2 ≤ (β * L) ^ 2 := pow_le_pow_left₀ hε hεβL 2
  have h2n : (2:ℝ) ^ (n + 3) = 8 * 2 ^ n := by ring
  have hp : (0:ℝ) ≤ 2 ^ n := by positivity
  have hb : 0 ≤ (β * L) ^ 2 := sq_nonneg _
  have h2 : h * w ≤ (8 * C₃ + 2 ^ (n + 3)) * (β * L) ^ 2 := by
    rw [h2n]
    nlinarith [mul_le_mul_of_nonneg_left hε2 hC₃, mul_nonneg hC₃ hb, mul_nonneg hp hb]
  rw [div_mul_eq_mul_div, le_div_iff₀ hw]
  exact h2

theorem Submission.dorag_lip_good_set_cone_estimate : ∀ (n k : ℕ) (C₃ C₆ : ℝ), 1 ≤ C₃ → 1 ≤ C₆ → ∃ C₈ : ℝ, 0 < C₈ ∧ ∀ (μ : Measure (Euclid (n + k))) (τ : Euclid (n + k) → Submodule ℝ (Euclid (n + k))) (T₀ : Submodule ℝ (Euclid (n + k))) (ξ : Euclid (n + k)) (σ₀ ε β L : ℝ), AEStronglyMeasurable (fun x => (τ x).starProjection) μ → 0 < σ₀ → 0 ≤ ε → 0 < β → 0 < L → ε ≤ β * L → (∀ y ∈ μ.support ∩ closedBall ξ (3 * σ₀ / 4), ∀ t : ℝ, 0 < t → t ≤ σ₀ / 2 → ∃ S : Submodule ℝ (Euclid (n + k)), (∀ x ∈ μ.support ∩ closedBall y t, ‖(x - y) - S.starProjection (x - y)‖ ≤ C₃ * ε * t) ∧ ∫⁻ x in closedBall y (t / 2), ENNReal.ofReal (∑ i : Fin (n + k), ‖(τ x).starProjection (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ ≤ ENNReal.ofReal (C₃ * ε ^ 2 * (t / 2) ^ n)) → (∀ y ∈ μ.support ∩ closedBall ξ (3 * σ₀ / 4), ∀ t : ℝ, 0 < t → t ≤ σ₀ / 4 → unitBallVolume n * ENNReal.ofReal (t ^ n) ≤ 2 * μ (closedBall y t)) → (∀ x ∈ μ.support ∩ closedBall ξ σ₀, ‖(x - ξ) - T₀.starProjection (x - ξ)‖ ≤ C₆ * ε * σ₀) → ∀ y₁ ∈ μ.support ∩ closedBall ξ (3 * σ₀ / 4), ∀ y₂ ∈ μ.support ∩ closedBall ξ (3 * σ₀ / 4), (∀ t : ℝ, 0 < t → t ≤ σ₀ / 2 → ∫⁻ x in closedBall y₁ (t / 2), ENNReal.ofReal (∑ i : Fin (n + k), ‖(τ x).starProjection (EuclideanSpace.single i (1 : ℝ)) - T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ ≤ ENNReal.ofReal (β ^ 2 * L ^ 2 * t ^ n)) → ‖(y₂ - y₁) - T₀.starProjection (y₂ - y₁)‖ ≤ C₈ * β * L * ‖y₂ - y₁‖ := by
  intro n k C₃ C₆ hC₃ hC₆
  have hC₃0 : 0 < C₃ := by linarith
  have hvol_pos : 0 < unitBallVolume n := by
    unfold unitBallVolume; exact measure_ball_pos _ _ one_pos
  have hvol_lt : unitBallVolume n < ⊤ := by
    unfold unitBallVolume; exact measure_ball_lt_top
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = (unitBallVolume n).toReal := ⟨_, rfl⟩
  have hw_pos : 0 < w := by rw [hw]; exact ENNReal.toReal_pos hvol_pos.ne' hvol_lt.ne
  have hw_eq : unitBallVolume n = ENNReal.ofReal w := by
    rw [hw, ENNReal.ofReal_toReal hvol_lt.ne]
  obtain ⟨K, hK_def⟩ : ∃ K : ℝ, K = (8 * C₃ + 2 ^ (n + 3)) / w := ⟨_, rfl⟩
  have hK : 0 ≤ K := by rw [hK_def]; positivity
  obtain ⟨C₈, hC₈⟩ : ∃ C : ℝ, C = max (C₃ + Real.sqrt K) (4 * C₆) := ⟨_, rfl⟩
  have hC₈a : C₃ + Real.sqrt K ≤ C₈ := by rw [hC₈]; exact le_max_left _ _
  have hC₈b : 4 * C₆ ≤ C₈ := by rw [hC₈]; exact le_max_right _ _
  refine ⟨C₈, by linarith, ?_⟩
  intro μ τ T₀ ξ σ₀ ε β L hmeas hσ₀ hε hβ hL hεβL H1 H2 H3 y₁ hy₁ y₂ hy₂ Hgood
  have hβL : 0 < β * L := mul_pos hβ hL
  rcases (norm_nonneg (y₂ - y₁)).eq_or_lt with ht0 | htpos
  · have hu0 : y₂ - y₁ = 0 := norm_eq_zero.1 ht0.symm
    rw [hu0]; simp
  obtain ⟨t, ht⟩ : ∃ t : ℝ, ‖y₂ - y₁‖ = t := ⟨_, rfl⟩
  rw [ht] at htpos ⊢
  rcases le_or_gt t (σ₀ / 2) with hts | hts
  · -- Case `0 < t ≤ σ₀ / 2`.
    obtain ⟨S, hS1, hS2⟩ := H1 y₁ hy₁ t htpos hts
    have hgood := Hgood t htpos hts
    have hy₂ball : y₂ ∈ μ.support ∩ closedBall y₁ t :=
      ⟨hy₂.1, mem_closedBall.2 (le_of_eq (by rw [dist_eq_norm, ht]))⟩
    have hQS : ‖(y₂ - y₁) - S.starProjection (y₂ - y₁)‖ ≤ C₃ * ε * t := hS1 y₂ hy₂ball
    obtain ⟨h, hh_def⟩ : ∃ h : ℝ, h = ∑ i : Fin (n + k),
        ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) -
          T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := ⟨_, rfl⟩
    have hh0 : 0 ≤ h := by rw [hh_def]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
    have hint := Submission.dorag_lip_cone_estimate_aux_lint (s := closedBall y₁ (t / 2))
      (Submission.dorag_lip_cone_estimate_aux_aemeas S hmeas).restrict
      (fun x => Submission.dorag_lip_cone_estimate_aux_pt ((τ x).starProjection)
        S.starProjection T₀.starProjection)
    rw [← hh_def] at hint
    have hint2 : ENNReal.ofReal h * μ (closedBall y₁ (t / 2)) ≤
        2 * ENNReal.ofReal (C₃ * ε ^ 2 * (t / 2) ^ n) +
          2 * ENNReal.ofReal (β ^ 2 * L ^ 2 * t ^ n) := by
      refine hint.trans ?_
      gcongr
    have hdens := H2 y₁ hy₁ (t / 2) (by positivity) (by linarith)
    rw [hw_eq] at hdens
    have hreal := Submission.dorag_lip_cone_estimate_aux_real hh0 hw_pos.le
      (by positivity) (by positivity) hint2 hdens
    have htn : t ^ n = 2 ^ n * (t / 2) ^ n := by
      rw [← mul_pow]; congr 1; ring
    rw [htn] at hreal
    have hhK : h ≤ K * (β * L) ^ 2 := by
      rw [hK_def]
      exact Submission.dorag_lip_cone_estimate_aux_div n hw_pos (by positivity) hC₃0.le hε
        hεβL hreal
    have hsqrt : Real.sqrt h ≤ Real.sqrt K * (β * L) := by
      calc Real.sqrt h ≤ Real.sqrt (K * (β * L) ^ 2) := Real.sqrt_le_sqrt hhK
        _ = Real.sqrt K * (β * L) := by rw [Real.sqrt_mul hK, Real.sqrt_sq hβL.le]
    have hHS := Submission.dorag_lip_cone_estimate_aux_hs_bound
      (S.starProjection - T₀.starProjection) (y₂ - y₁)
    simp only [_root_.sub_apply] at hHS
    rw [← hh_def, ht] at hHS
    calc ‖(y₂ - y₁) - T₀.starProjection (y₂ - y₁)‖
        = ‖((y₂ - y₁) - S.starProjection (y₂ - y₁)) +
            (S.starProjection (y₂ - y₁) - T₀.starProjection (y₂ - y₁))‖ := by
          congr 1; abel
      _ ≤ ‖(y₂ - y₁) - S.starProjection (y₂ - y₁)‖ +
            ‖S.starProjection (y₂ - y₁) - T₀.starProjection (y₂ - y₁)‖ := norm_add_le _ _
      _ ≤ C₃ * ε * t + Real.sqrt h * t := add_le_add hQS hHS
      _ ≤ C₃ * (β * L) * t + Real.sqrt K * (β * L) * t := by
          have e1 : C₃ * ε * t ≤ C₃ * (β * L) * t :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hεβL hC₃0.le) htpos.le
          have e2 : Real.sqrt h * t ≤ Real.sqrt K * (β * L) * t :=
            mul_le_mul_of_nonneg_right hsqrt htpos.le
          linarith
      _ = (C₃ + Real.sqrt K) * (β * L * t) := by ring
      _ ≤ C₈ * (β * L * t) := mul_le_mul_of_nonneg_right hC₈a (by positivity)
      _ = C₈ * β * L * t := by ring
  · -- Case `t > σ₀ / 2`.
    have hsub : ∀ y ∈ μ.support ∩ closedBall ξ (3 * σ₀ / 4), y ∈ μ.support ∩ closedBall ξ σ₀ :=
      fun y hy => ⟨hy.1, closedBall_subset_closedBall (by linarith) hy.2⟩
    have h1 := H3 y₁ (hsub y₁ hy₁)
    have h2 := H3 y₂ (hsub y₂ hy₂)
    have hQ : (y₂ - y₁) - T₀.starProjection (y₂ - y₁) =
        ((y₂ - ξ) - T₀.starProjection (y₂ - ξ)) - ((y₁ - ξ) - T₀.starProjection (y₁ - ξ)) := by
      have e : y₂ - y₁ = (y₂ - ξ) - (y₁ - ξ) := by abel
      rw [e, map_sub T₀.starProjection (y₂ - ξ) (y₁ - ξ)]; abel
    have hC₆0 : 0 ≤ C₆ := by linarith
    have hCε : 0 ≤ C₆ * ε := mul_nonneg hC₆0 hε
    calc ‖(y₂ - y₁) - T₀.starProjection (y₂ - y₁)‖
        = ‖((y₂ - ξ) - T₀.starProjection (y₂ - ξ)) -
            ((y₁ - ξ) - T₀.starProjection (y₁ - ξ))‖ := by rw [hQ]
      _ ≤ ‖(y₂ - ξ) - T₀.starProjection (y₂ - ξ)‖ + ‖(y₁ - ξ) - T₀.starProjection (y₁ - ξ)‖ :=
          norm_sub_le _ _
      _ ≤ C₆ * ε * σ₀ + C₆ * ε * σ₀ := add_le_add h2 h1
      _ = 2 * (C₆ * ε) * σ₀ := by ring
      _ ≤ 2 * (C₆ * ε) * (2 * t) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 4 * C₆ * ε * t := by ring
      _ ≤ 4 * C₆ * (β * L) * t := by
          have : 0 ≤ 4 * C₆ := by linarith
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hεβL this) htpos.le
      _ = 4 * C₆ * (β * L * t) := by ring
      _ ≤ C₈ * (β * L * t) := mul_le_mul_of_nonneg_right hC₈b (by positivity)
      _ = C₈ * β * L * t := by ring

## Key steps

1. constants ω = (unitBallVolume n).toReal > 0 and C₈ := max(C₃ + √((8C₃ + 2^{n+3})/ω), 4C₆)
2. Hilbert–Schmidt facts: ‖Au‖ ≤ |A|‖u‖ and |p_S − P|² ≤ 2|p_x − p_S|² + 2|p_x − P|²
3. a.e. measurability of the tilt integrands from the measurability hypothesis
4. case t ≤ σ₀/2: plane S from (H1) at (y₁, t), good-set bound at t, integrate over B_{t/2}(y₁) and use (H2) to get |p_S − P|² ≤ (8C₃ + 2^{n+3})β²L²/ω
5. ‖Q(y₂ − y₁)‖ ≤ C₃εt + |p_S − P|t ≤ C₈βLt
6. case t > σ₀/2 via (H3): ‖Q(y₂ − y₁)‖ ≤ 2C₆εσ₀ ≤ 4C₆βLt ≤ C₈βLt

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json  (mode local-project; project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d; the workspace lake-manifest.json pins the same mathlib rev and simongmt 2b3663083f3fe399b6296fb8eaee52169170e197)`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean  (both identical)`
- `rg -n -i 'lipschitz.?approx|LipschitzApproximationLemma|LipschitzGraphCorollary|dorag_lip_' local-references/123e8435b4a2469b/project/GMT`
- `rg -c 'dorag_lip_' local-references/123e8435b4a2469b  (no match)`
- `rg -n "theorem exists_disjoint_subfamily_covering_enlargement_closedBall|theorem LipschitzOnWith.extend_real|lemma measure_compl_support|countable_of_nonempty_interior|lemma exp_le_two_add_div_two_sub|theorem withDensity_apply |theorem lintegral_add_left'|theorem lintegral_const_mul'|theorem setLIntegral_mono'|IsClosed.exists_infDist_eq_dist|lemma isClosed_support|theorem measure_toMeasurable|euclideanHausdorffMeasure_eq_volume|theorem addHaar_closedBall |norm_starProjection_apply_le|starProjection_orthogonal_val" local-references/123e8435b4a2469b/mathlib/Mathlib`
- `lean CheckNames.lean: #check of the 37 Mathlib/SimonGMT declarations cited by the children (all resolve, including Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn)`
- `python3: frozen lean_statement of the four sibling prerequisites (dorag_approxTangent_starProjection_aesm, dorag_monotonicity_density, dorag_standing_density_bounds, dorag_affine_approximation) and of dorag_lipschitz_approximation from dag.json, compared with the assembly's hypotheses and conclusion (all equal)`
- `python3 -I lean_contract.validate_lean_statement on the 8 lean_statements; scan of all 8 workspace dag.json files and GMT/ for dorag_lip_* and the dorag_lip_cone_estimate_aux_/dorag_lip_off_support_aux_ prefixes (no collision)`
- `lean ChallengeAll.lean (8 child types and the frozen parent type elaborate); lean FromFinal.lean (8 child proofs + LipApxAssembly + LipApxFromChildren regenerated from the submitted JSON, exit 0); lean perchild/Child_<key>.lean (each child with only its declared dependency); gmt-compare.py contract_scope emulation cmp/Sol_<key>.lean and cmp/Chal_<key>.lean (all exit 0)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch05/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Complex/Exponential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-464a20467f/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-464a20467f/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-464a20467f/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/tmp/lipapx-v2-work/FromFinal.lean`
- `/tmp/lipapx-v2-work/ChallengeAll.lean`
- `/tmp/lipapx-v2-work/CheckNames.lean`

The snapshot pins project b4d606d and Mathlib 25730c7c. The workspace builds against the same Mathlib revision. The snapshot's Ch07 Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean, which form the compiler context of every child.

Nothing in the snapshot proves the selected theorem or any child:
- GMT/Ch05 Contract/Submission (lines 272–309) define LipschitzApproximationLemma and LipschitzGraphCorollary only as Props for a different varifold type. They are used solely in the sorry-backed main_theorem (line 461).
- No dorag_lip_* name occurs in the snapshot.
So no comparator-approved declaration can be reused.

The tools the children cite exist at the pinned revision:
- Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall (MeasureTheory/Covering/Vitali.lean:158);
- Set.PairwiseDisjoint.countable_of_nonempty_interior (Topology/Bases.lean:493);
- LipschitzOnWith.extend_real (Topology/MetricSpace/Lipschitz.lean:308);
- IsClosed.exists_infDist_eq_dist (Topology/MetricSpace/HausdorffDistance.lean:615);
- Measure.isClosed_support and Measure.measure_compl_support (MeasureTheory/Measure/Support.lean:115, 202);
- withDensity_apply (WithDensity.lean:44);
- measure_toMeasurable (MeasureSpaceDef.lean:348);
- lintegral_add_left' and lintegral_const_mul' (Integral/Lebesgue/Add.lean:326, 420);
- setLIntegral_mono' (Integral/Lebesgue/Basic.lean:254);
- Real.exp_le_two_add_div_two_sub (Analysis/Complex/Exponential.lean:676);
- Submodule.starProjection_orthogonal_val and norm_starProjection_apply_le (InnerProductSpace/Projection/Basic.lean:203, 411);
- EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Geometry/Euclidean/Volume/Measure.lean:187);
- Measure.addHaar_closedBall (Lebesgue/EqHaar.lean:500);
- SimonGMT Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn, which lies in the contract's import closure.

Lean checks:
- All 8 child types and the frozen parent type elaborate in comparator scope.
- All 8 children are fully proved, warning-free.
- The exact frozen parent type is derived from the 4 frozen sibling types plus the 8 children, using only propext, Classical.choice and Quot.sound.
- No name collides with any DAG reservation.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
