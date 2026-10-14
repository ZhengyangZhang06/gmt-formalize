<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.positive_scale_family-a1 -->

## Theorem `Submission.idtp_fons_cc_positive_scale_family`

Let P, n ∈ ℕ with n ≥ 1, μ a measure on ℝ^P, z ∈ ℝ^P and r > 0 with μ(B_{2r}(z)) ≠ 0 and μ(B_{2r}(z)) ≠ ∞, and let μ₀ be the measure μ₀ = ofReal(r^{−n})•(μ⌞B_{2r}(z)).map(dilation z r). For x ∈ ℝ^P and λ > 0 write μ₀^{x,λ} := ofReal(λ^{−n})•μ₀.map(dilation x λ) and G_{x,λ} := dilation x λ '' B_2(0); call (x, λ) admissible if 0 < λ ≤ 1 and ‖x‖ ≤ 1 − λ; 'f_i → ν vaguely' means ∫ f dν_i → ∫ f dν for every continuous compactly supported f : ℝ^P → ℝ. Then: (1) for every w ∈ B_2(0): (μ₀(B_ε(w)) ≠ 0 for all ε > 0) ⟺ (μ(B_ε(z + r·w)) ≠ 0 for all ε > 0); (2) if λ, λ' > 0 and μ₀^{x,λ} = μ₀^{x',λ'}, then x = x' and λ = λ'; (3) for λ > 0, μ₀^{x,λ}(ℝ^P) ≠ 0 and μ₀^{x,λ}(ℝ^P) ≠ ∞; (4) for admissible (x, λ), G_{x,λ} is open and B_2(0) ⊆ G_{x,λ}; (5) if (x_i, λ_i) (i ∈ ℕ) are admissible, ν is a measure with ν(K') ≠ ∞ for every compact K', μ₀^{x_i,λ_i} → ν vaguely, K ⊆ ℝ^P is compact and K ⊄ G_{x_i,λ_i} for every i, then there is an admissible (x, λ) with ν = μ₀^{x,λ} and K ⊄ G_{x,λ}; (6) for λ > 0 and every f : ℝ^P → [0, ∞] with f(t·w) = f(w) for all t > 0 and w, μ₀^{x,λ} ≠ μHE[n].withDensity f; (7) if Λ₀ ≥ 0 and μ satisfies ofReal(e^{−(Λ₀σ)})·(ω_n·ofReal(σ^n)) ≤ μ(B_σ(p)) whenever μ(B_ε(p)) ≠ 0 for all ε > 0, closedBall p ρ ⊆ closedBall z (2r) and 0 < σ < ρ (ω_n = unitBallVolume n), then for all x, y ∈ ℝ^P, 0 < λ ≤ 1 and ρ > 0 with closedBall y ρ ⊆ G_{x,λ} and μ₀^{x,λ}(B_ε(y)) ≠ 0 for all ε > 0: ofReal(e^{−(r·Λ₀·ρ)})·(ω_n·ofReal(ρ^n)) ≤ μ₀^{x,λ}(B_ρ(y)).

Node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.positive_scale_family-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5745

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6873, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4643

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/7472, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7511, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7550, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7580, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7612, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7638, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7660, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4643, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7682, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7708

## Lean problem

Declaration: `Submission.idtp_fons_cc_positive_scale_family`

```lean
∀ (P n : ℕ) (μ μ₀ : Measure (Euclid P)) (z : Euclid P) (r : ℝ), 1 ≤ n → 0 < r → μ (ball z (2 * r)) ≠ 0 → μ (ball z (2 * r)) ≠ ∞ → μ₀ = ENNReal.ofReal (r⁻¹ ^ n) • (μ.restrict (ball z (2 * r))).map (dilation z r) → (∀ w ∈ ball (0 : Euclid P) 2, (∀ ε : ℝ, 0 < ε → μ₀ (ball w ε) ≠ 0) ↔ ∀ ε : ℝ, 0 < ε → μ (ball (z + r • w) ε) ≠ 0) ∧ (∀ (x x' : Euclid P) (lam lam' : ℝ), 0 < lam → 0 < lam' → (ENNReal.ofReal (lam⁻¹ ^ n) • μ₀.map (dilation x lam)) = (ENNReal.ofReal (lam'⁻¹ ^ n) • μ₀.map (dilation x' lam')) → x = x' ∧ lam = lam') ∧ (∀ (x : Euclid P) (lam : ℝ), 0 < lam → (ENNReal.ofReal (lam⁻¹ ^ n) • μ₀.map (dilation x lam)) univ ≠ 0 ∧ (ENNReal.ofReal (lam⁻¹ ^ n) • μ₀.map (dilation x lam)) univ ≠ ∞) ∧ (∀ (x : Euclid P) (lam : ℝ), 0 < lam → lam ≤ 1 → ‖x‖ ≤ 1 - lam → IsOpen (dilation x lam '' ball 0 2) ∧ ball 0 2 ⊆ dilation x lam '' ball 0 2) ∧ (∀ (xs : ℕ → Euclid P) (lams : ℕ → ℝ) (ν : Measure (Euclid P)) (K : Set (Euclid P)), (∀ i, 0 < lams i ∧ lams i ≤ 1 ∧ ‖xs i‖ ≤ 1 - lams i) → (∀ K' : Set (Euclid P), IsCompact K' → ν K' ≠ ∞) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun i => ∫ x, f x ∂(ENNReal.ofReal ((lams i)⁻¹ ^ n) • μ₀.map (dilation (xs i) (lams i)))) atTop (𝓝 (∫ x, f x ∂ν))) → IsCompact K → (∀ i, ¬ K ⊆ dilation (xs i) (lams i) '' ball 0 2) → ∃ (x : Euclid P) (lam : ℝ), (0 < lam ∧ lam ≤ 1 ∧ ‖x‖ ≤ 1 - lam) ∧ ν = (ENNReal.ofReal (lam⁻¹ ^ n) • μ₀.map (dilation x lam)) ∧ ¬ K ⊆ dilation x lam '' ball 0 2) ∧ (∀ (x : Euclid P) (lam : ℝ) (f : Euclid P → ℝ≥0∞), 0 < lam → (∀ t : ℝ, 0 < t → ∀ w : Euclid P, f (t • w) = f w) → (ENNReal.ofReal (lam⁻¹ ^ n) • μ₀.map (dilation x lam)) ≠ (μHE[n] : Measure (Euclid P)).withDensity f) ∧ ∀ Λ₀ : ℝ, 0 ≤ Λ₀ → (∀ p : Euclid P, (∀ ε : ℝ, 0 < ε → μ (ball p ε) ≠ 0) → ∀ σ ρ : ℝ, closedBall p ρ ⊆ closedBall z (2 * r) → 0 < σ → σ < ρ → ENNReal.ofReal (Real.exp (-(Λ₀ * σ))) * (unitBallVolume n * ENNReal.ofReal (σ ^ n)) ≤ μ (ball p σ)) → ∀ (x y : Euclid P) (lam ρ : ℝ), 0 < lam → lam ≤ 1 → 0 < ρ → closedBall y ρ ⊆ dilation x lam '' ball 0 2 → (∀ ε : ℝ, 0 < ε → (ENNReal.ofReal (lam⁻¹ ^ n) • μ₀.map (dilation x lam)) (ball y ε) ≠ 0) → ENNReal.ofReal (Real.exp (-(r * Λ₀ * ρ))) * (unitBallVolume n * ENNReal.ofReal (ρ ^ n)) ≤ (ENNReal.ofReal (lam⁻¹ ^ n) • μ₀.map (dilation x lam)) (ball y ρ)
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

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.positive_scale_family-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent steps 2, 3(a)–(g), 7, 12, 13 and 14 together with basic fact (F6) — the positive-scale part of the parent's departures [D1] (members encoded by their weights; the domain is recovered from total mass and barycenter) and [D2] (one rescaled ball); Simon 7.3.3, proof of 3.3(1), (6), (9) and (10) (chapter-07.txt lines 445–467: the members η_{x,λ#}T with |x| < 1 − λ and their domains U_S = η_{x,λ}(U)).
Notation. B := B_{2r}(z); η_{a,s} := dilation a s; for a measure ν and s > 0, ν^{a,s} := ofReal(s^{−n})•ν.map(η_{a,s}); m := μ(B) ∈ (0, ∞); ω_n := unitBallVolume n ∈ (0, ∞). 'AC (i)' refers to part (i) of the sibling ambient_calculus. By hypothesis μ₀ = (μ⌞B)^{z,r}, and by AC (7), μ₀^{x,λ} = (μ⌞B)^{z+rx, rλ}.
0. (Basic formulas.) (a) For Borel A: μ₀(A) = ofReal(r^{−n})·μ(η_{z,r}^{−1}(A) ∩ B) (AC (2), Measure.restrict_apply). (b) η_{z,r}^{−1}(B_2(0)) = B_{2r}(z) = B (AC (3)), so μ₀(B_2(0)ᶜ) = ofReal(r^{−n})·μ(Bᶜ ∩ B) = 0 and μ₀(ℝ^P) = ofReal(r^{−n})·m ∈ (0, ∞). (c) For λ > 0 and Borel A: μ₀^{x,λ}(A) = ofReal(λ^{−n})·μ₀(η_{x,λ}^{−1}(A)) (AC (2)); in particular μ₀^{x,λ}(ℝ^P) = ofReal(λ^{−n})·ofReal(r^{−n})·m, and μ₀^{x,λ}(G_{x,λ}ᶜ) = ofReal(λ^{−n})·μ₀(B_2(0)ᶜ) = 0 (η_{x,λ} is bijective, so η_{x,λ}^{−1}(G_{x,λ}ᶜ) = B_2(0)ᶜ). (d) For w ∈ ℝ^P and σ > 0: μ₀^{x,λ}(B_σ(w)) = ofReal((rλ)^{−n})·μ(B_{rλσ}(z + r(x + λw)) ∩ B), by (c), (a) and AC (3) twice (η_{x,λ}^{−1}(B_σ(w)) = B_{λσ}(x + λw) and η_{z,r}^{−1}(B_{λσ}(x + λw)) = B_{rλσ}(z + r(x + λw))) and ofReal(λ^{−n})·ofReal(r^{−n}) = ofReal((rλ)^{−n}). (e) The affine bijection v ↦ z + r(x + λv) maps G_{x,λ} onto B (v ∈ G_{x,λ} ⟺ x + λv ∈ B_2(0) ⟺ z + r(x + λv) ∈ B) and closedBall w σ onto closedBall (z + r(x + λw)) (rλσ). Hence closedBall w σ ⊆ G_{x,λ} implies closedBall (z + r(x + λw)) (rλσ) ⊆ B, and then the intersection with B in (d) can be dropped: μ₀^{x,λ}(B_σ(w)) = ofReal((rλ)^{−n})·μ(B_{rλσ}(z + r(x + λw))).
1. (Support relation; parent step 7.) Let w ∈ B_2(0) and δ := (2 − ‖w‖)/2 > 0, so closedBall w δ ⊆ B_2(0) = G_{0,1} (AC (8): η_{0,1} = id and μ₀^{0,1} = μ₀). For 0 < ε ≤ δ, 0(e) with x = 0, λ = 1 gives μ₀(B_ε(w)) = ofReal(r^{−n})·μ(B_{rε}(z + rw)). (⇒) Given ε' > 0, let ε := min(δ, ε'/r) > 0: then ofReal(r^{−n})·μ(B_{rε}(z + rw)) = μ₀(B_ε(w)) ≠ 0, so μ(B_{rε}(z + rw)) ≠ 0, and B_{rε}(z + rw) ⊆ B_{ε'}(z + rw) gives μ(B_{ε'}(z + rw)) ≠ 0. (⇐) Given ε > 0, let ε₁ := min(ε, δ): μ₀(B_{ε₁}(w)) = ofReal(r^{−n})·μ(B_{rε₁}(z + rw)) ≠ 0 (both factors nonzero), and μ₀(B_ε(w)) ≥ μ₀(B_{ε₁}(w)) > 0.
2. (Injectivity; parent step 3(b),(c).) Suppose λ, λ' > 0 and μ₀^{x,λ} = μ₀^{x',λ'}. Total masses (0(c)): ofReal(λ^{−n})·c = ofReal(λ'^{−n})·c with c := ofReal(r^{−n})·m ∈ (0, ∞), so λ^{−n} = λ'^{−n}; since n ≥ 1 and λ, λ' > 0, λ^{−1} = λ'^{−1} (pow_left_injective on [0, ∞)) and λ = λ'. Barycenters: by 0(b), μ₀ is a finite measure and ‖v‖ < 2 for μ₀-a.e. v, so v ↦ v is μ₀-integrable; put b₀ := ∫ v dμ₀(v) and m₀ := μ₀(ℝ^P).toReal > 0. By integral_smul_measure and integral_map (η_{x,λ} measurable, id continuous), ∫ v dμ₀^{x,λ}(v) = λ^{−n}·∫ η_{x,λ}(v) dμ₀(v) = λ^{−n}·(λ^{−1}b₀ − λ^{−1}m₀x), using η_{x,λ}(v) = λ^{−1}v − λ^{−1}x, linearity of the integral (integral_add, integral_smul) and ∫ const dμ₀ = m₀·const (integral_const). Equal measures have equal integrals, so (with λ = λ') λ^{−n−1}(b₀ − m₀x) = λ^{−n−1}(b₀ − m₀x'), hence m₀x = m₀x' and x = x'.
3. (Mass.) By 0(c), μ₀^{x,λ}(ℝ^P) = ofReal(λ^{−n})·ofReal(r^{−n})·m, a product of factors in (0, ∞); so it is ≠ 0 and ≠ ∞.
4. (Domains; parent step 3(d).) By AC (4), G_{x,λ} = η_{x,λ}(B_2(0)) = B_{2/λ}(−λ^{−1}x) (η_{x,λ}(0) = −λ^{−1}x), which is open. For ‖v‖ < 2: ‖v + λ^{−1}x‖ ≤ ‖v‖ + λ^{−1}‖x‖ < 2 + λ^{−1}(1 − λ) = 1 + λ^{−1} ≤ 2λ^{−1} (since λ ≤ 1), so B_2(0) ⊆ G_{x,λ}. Likewise for ‖v‖ < λ^{−1}: ‖v + λ^{−1}x‖ < λ^{−1} + λ^{−1}(1 − λ) < 2λ^{−1}, so B_{1/λ}(0) ⊆ G_{x,λ} (used in 5c).
5. (Domain recovery under vague limits; parent step 12.)
 5a. (Continuity in the parameters; parent step 3(g).) Let f be continuous with compact support and F(x, λ) := ∫ f dμ₀^{x,λ}. By integral_smul_measure and integral_map, F(x, λ) = λ^{−n}·∫ f(η_{x,λ}(v)) dμ₀(v). For each v, (x, λ) ↦ f(λ^{−1}(v − x)) is continuous on ℝ^P × (0, ∞); |f(·)| ≤ sup|f| < ∞, a constant that is μ₀-integrable (μ₀ finite). By dominated convergence (continuousOn version of continuous_of_dominated, or tendsto_integral_filter_of_dominated_convergence along sequences) and continuity of λ ↦ λ^{−n} on (0, ∞), F is continuous on ℝ^P × (0, ∞).
 5b. (Uniqueness of vague limits, parent (F6).) If ν₁, ν₂ are measures on ℝ^P, finite on compact sets, with ∫ f dν₁ = ∫ f dν₂ for all continuous compactly supported f, then ν₁ = ν₂. Proof: for open O and integers m ≥ 1 let f_m(v) := min(1, m·infDist(v, Oᶜ))·min(1, (m − ‖v‖)⁺) (first factor := 1 if O = ℝ^P). Each f_m is continuous with support in closedBall 0 m, 0 ≤ f_m ≤ 1_O, and f_m ↑ 1_O pointwise (for v ∈ O, infDist(v, Oᶜ) > 0 since Oᶜ is closed). By monotone convergence ν_i(O) = lim_m ∫ f_m dν_i, so ν₁(O) = ν₂(O). Open sets form a π-system generating the Borel σ-algebra (isPiSystem_isOpen, borel = generateFrom of open sets), and the open balls B_m(0) have finite measure and cover ℝ^P, so ν₁ = ν₂ (Measure.ext_of_generateFrom_of_iUnion). (Equivalently: finite on compacts gives IsFiniteMeasureOnCompacts, hence local finiteness and regularity on the σ-compact metric space ℝ^P (Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure), and Measure.ext_of_integral_eq_on_compactlySupported applies.)
 5c. (Proof of (5).) K is compact, so K ⊆ closedBall 0 R_K for some R_K ≥ 1. If λ_i < 1/R_K for some i, then K ⊆ closedBall 0 R_K ⊆ B_{1/λ_i}(0) ⊆ G_{x_i,λ_i} (step 4), contradicting K ⊄ G_{x_i,λ_i}. So λ_i ≥ λ₀ := 1/R_K > 0 for every i. The set Π := {(x, λ) : λ₀ ≤ λ ≤ 1, ‖x‖ ≤ 1 − λ} ⊆ ℝ^P × ℝ is closed and bounded, hence compact, and contains every (x_i, λ_i). By sequential compactness (IsCompact.tendsto_subseq) there are a strictly increasing ψ and (x*, λ*) ∈ Π with (x_{ψ(i)}, λ_{ψ(i)}) → (x*, λ*); (x*, λ*) is admissible since λ* ≥ λ₀ > 0. For every continuous compactly supported f: by 5a, ∫ f dμ₀^{x_{ψ(i)},λ_{ψ(i)}} → ∫ f dμ₀^{x*,λ*}; by hypothesis (composed with ψ, StrictMono.tendsto_atTop) the same integrals converge to ∫ f dν; by uniqueness of limits in ℝ, ∫ f dν = ∫ f dμ₀^{x*,λ*}. ν is finite on compacts by hypothesis and μ₀^{x*,λ*} is finite (step 3), so 5b gives ν = μ₀^{x*,λ*}. Finally suppose K ⊆ G_{x*,λ*} = B_{2/λ*}(c*), c* := −x*/λ*. K ≠ ∅ (otherwise K ⊆ G_{x_{ψ(0)},λ_{ψ(0)}} trivially), so the continuous function v ↦ ‖v − c*‖ attains a maximum M < 2/λ* on K. Put γ := (2/λ* − M)/2 > 0. Since c_i := −x_{ψ(i)}/λ_{ψ(i)} → c* and 2/λ_{ψ(i)} → 2/λ* (continuity on λ > 0), for large i we have ‖c_i − c*‖ < γ and 2/λ_{ψ(i)} > 2/λ* − γ; then every v ∈ K satisfies ‖v − c_i‖ ≤ M + ‖c* − c_i‖ < M + γ = 2/λ* − γ < 2/λ_{ψ(i)}, i.e. K ⊆ G_{x_{ψ(i)},λ_{ψ(i)}}, a contradiction. Hence K ⊄ G_{x*,λ*}, and (x, λ) := (x*, λ*) satisfies (5).
6. (Non-homogeneity; parent step 14.) Let f be as in (6) and ν := μHE[n].withDensity f. For t > 0, the sibling withdensity_dilate (Submission.dimred_cs_mi_withDensity_dilate with λ := t, its hypothesis f(t·w) = f(w) holding for all w, and the Borel set B_1(0)) gives ν((v ↦ t v) '' B_1(0)) = ofReal(t^n)·ν(B_1(0)), and (v ↦ t v) '' B_1(0) = B_t(0) (smul_ball, ‖t‖ = t). If ν(B_1(0)) = 0, then ν(B_t(0)) = 0 for all t > 0 and ν(ℝ^P) = ν(⋃_{m≥1} B_m(0)) = 0 (measure_iUnion_null). If ν(B_1(0)) ≠ 0, then ν(ℝ^P) ≥ ν(B_t(0)) = ofReal(t^n)·ν(B_1(0)) for all t > 0, and ofReal(t^n) → ∞ as t → ∞ (n ≥ 1), so ν(ℝ^P) = ∞. In both cases ν(ℝ^P) ∈ {0, ∞}, while μ₀^{x,λ}(ℝ^P) ∉ {0, ∞} by step 3. Hence μ₀^{x,λ} ≠ ν.
7. (Transferred lower bound; parent step 13.) Let Λ₀, x, y, λ, ρ be as in (7); put s := rλ ∈ (0, r] and p := z + r(x + λy). By 0(e) applied to closedBall y σ ⊆ closedBall y ρ ⊆ G_{x,λ}: closedBall p (sρ) ⊆ B, and μ₀^{x,λ}(B_σ(y)) = ofReal(s^{−n})·μ(B_{sσ}(p)) for every 0 < σ ≤ ρ.
 7a. μ(B_{ε'}(p)) ≠ 0 for every ε' > 0: with σ := min(ρ, ε'/s) > 0, ofReal(s^{−n})·μ(B_{sσ}(p)) = μ₀^{x,λ}(B_σ(y)) ≠ 0 by hypothesis, so μ(B_{sσ}(p)) ≠ 0, and B_{sσ}(p) ⊆ B_{ε'}(p).
 7b. closedBall p (sρ) is compact and contained in the open set B, so there is δ > 0 with cthickening δ (closedBall p (sρ)) ⊆ B (IsCompact.exists_cthickening_subset_open), and closedBall p (sρ + δ) ⊆ cthickening δ (closedBall p (sρ)) (a point q with ‖q − p‖ ≤ sρ + δ is within δ of p + min(1, sρ/‖q − p‖)(q − p) ∈ closedBall p (sρ)). Hence closedBall p (sρ + δ) ⊆ B ⊆ closedBall z (2r).
 7c. The hypothesis on μ, applied to p (by 7a), σ := sρ and ρ' := sρ + δ (0 < sρ < sρ + δ, closedBall p ρ' ⊆ closedBall z (2r) by 7b), gives ofReal(e^{−(Λ₀sρ)})·(ω_n·ofReal((sρ)^n)) ≤ μ(B_{sρ}(p)).
 7d. Therefore μ₀^{x,λ}(B_ρ(y)) = ofReal(s^{−n})·μ(B_{sρ}(p)) ≥ ofReal(s^{−n})·ofReal(e^{−(Λ₀sρ)})·ω_n·ofReal(s^n)·ofReal(ρ^n) = ofReal(e^{−(Λ₀rλρ)})·(ω_n·ofReal(ρ^n)) (ofReal(s^{−n})·ofReal(s^n) = ofReal(1) = 1, (sρ)^n = s^nρ^n). Since 0 < λ ≤ 1, Λ₀ ≥ 0, r > 0 and ρ > 0, Λ₀rλρ ≤ rΛ₀ρ, hence e^{−(r·Λ₀·ρ)} ≤ e^{−(Λ₀rλρ)} (Real.exp_le_exp) and ofReal is monotone; this gives ofReal(e^{−(r·Λ₀·ρ)})·(ω_n·ofReal(ρ^n)) ≤ μ₀^{x,λ}(B_ρ(y)). ∎

## Key steps

1. μ₀^{x,λ} = (μ⌞B_{2r}(z))^{z+rx, rλ} is concentrated on G_{x,λ}, and on balls with closure in G_{x,λ} it equals (rλ)^{−n}μ on the corresponding ball around z + r(x + λw).
2. Total mass λ^{−n}r^{−n}μ(B_{2r}(z)) recovers λ, the barycenter λ^{−n−1}(b₀ − m₀x) recovers x; masses are finite and positive.
3. G_{x,λ} = B_{2/λ}(−x/λ) ⊇ B_2(0) ∪ B_{1/λ}(0) for admissible (x, λ).
4. Vague limits: K ⊄ G_i forces λ_i ≥ 1/R_K; compactness of the parameter set, continuity of the integrals in (x, λ) and uniqueness of vague limits identify ν = μ₀^{x*,λ*}, and openness of G_{x*,λ*} shows K ⊄ G_{x*,λ*}.
5. withdensity_dilate makes Hⁿ⌞f homogeneous of degree n, so its total mass is 0 or ∞, unlike μ₀^{x,λ}.
6. The lower bound for μ at p = z + r(x + λy) with σ = rλρ transfers by the ball identity to e^{−rΛ₀ρ}ω_nρ^n ≤ μ₀^{x,λ}(B_ρ(y)).

## Reference use

### local-project

Queries:
- `python3 -I -c json.load(local-references/123e8435b4a2469b/manifest.json); cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD`
- `python3 scan of dag.json lean_statement fields for 'BoundaryVanishes (blowUp', 'blowUp', 'restrict', 'withDensity', 'map (dilation', 'IsEmbeddedSubmanifold 2 (n + k) univ', 'HasCompactSupport f → ∫', with status, candidate_commit and depends_on of each match`
- `python3 extraction of subproblem.lean_statement/natural_proof/proof_key_steps from the parent-child-handoff.json of the six reused accepted nodes; isolated-comparator-result.json of borel-restriction-a1 and of blowup_limit_cycle (node dir ...-34a94daa02)`
- `grep -n '^theorem|^def|^structure|^instance' .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/{Currents,CurrentLocalEquality,AffineCurrentPushforward,Mass}.lean; sed -n 20,120p Chapter03/Rectifiable.lean`
- `grep -rn 'ext_of_integral_eq_on_compactlySupported|Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure|isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts|theorem restrict_map|measure_null_of_locally_null|extraction_of_frequently_atTop|IsCompact.tendsto_subseq|continuous_of_dominated|tendsto_integral_filter_of_dominated_convergence|euclideanHausdorffMeasure_smul₀|ext_of_forall_integral_eq' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `grep -c 'idtp_fons_cc_\|idtp_fcc_' dag.json; grep -rl nodes/; grep -rl --include=Submission.lean ../.swarm-worktrees/*/gmt-ch07/GMT/Ch07/; git log --all -S idtp_fons_cc_ (all empty)`
- `sed -n 300,330p and 420,535p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt (Simon 7.3.1 and the proof of 7.3.3)`
- `lake env lean /tmp/ccd_k7q2/final/Types.lean; lake env lean /tmp/ccd_k7q2/final/AssemblyAx.lean (#print axioms); lake env lean /tmp/ccd_k7q2/final/AC.lean, DR.lean, CR.lean, TMB.lean`
- `python3 replay of Runtime._dependency_problem, Runtime._topological and Runtime._existing_lean_name_problem on /tmp/ccd_k7q2/final/subproblems_final.json against dag.json (updated_at 2026-10-13T19:24:44Z)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-5982ed9bb9/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-4fcbfb5d62/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-4fcbfb5d62/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-im-mass-measure-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-scaling-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-cone-measure-homogeneous-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-34a94daa02/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-34a94daa02/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-borel-restriction-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-borel-restriction-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-measure-invaria-4622bb5be6/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/tmp/ccd_k7q2/final/Types.lean`
- `/tmp/ccd_k7q2/final/AssemblyAx.lean`
- `/tmp/ccd_k7q2/final/AC.lean`
- `/tmp/ccd_k7q2/final/DR.lean`
- `/tmp/ccd_k7q2/final/CR.lean`
- `/tmp/ccd_k7q2/final/TMB.lean`

Pins match: manifest project b4d606db1 = workspace HEAD, Mathlib 25730c7c; SimonGMT 2b36630; the snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. Reusable accepted declarations (dag.json; candidate commits present locally; isolated comparator passed): dimred_im_mass_measure (01ae2c59), dtc_blowUp_scaling (a94d596c), cone_current_imrep_measure_smul_image (e183b985), idtp_tpf_blowUp_limit_boundaryVanishes (f498a8ef; exactly the parent's (F7)), dor_lmb_imrep_restrict_current (90d679af; Borel restriction of an IMRep with weight μ⌞A, used for 3(h)) and dimred_cs_mi_withDensity_dilate (fc55b748; n-homogeneity of Hⁿ.withDensity f, used for step 14). Their types are copied byte for byte. No accepted or library declaration states the ambient-submanifold fact, the dilation calculus of rescaled measures, (F9) from DEM, the monotonicity consequences, the tangent-measure statement or the positive-scale family, so these enter as the six fresh children (fresh idtp_fons_cc_ names occur nowhere). Library facts used in the child proofs: SimonGMT GeometricCurrentOn.boundary_affinePushforward (Chapter06/AffineCurrentPushforward.lean:188), restrictDomain_apply, zeroRegion and support (CurrentLocalEquality.lean), massOn (Mass.lean:68), countablyRectifiable_of_measure_zero (Chapter03/Rectifiable.lean:45). Snapshot Mathlib: Measure.ext_of_integral_eq_on_compactlySupported (RieszMarkovKakutani/Real.lean:412), Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure (Measure/Regular.lean:1183), MeasurableEmbedding.restrict_map (Measure/Restrict.lean:890), measure_null_of_locally_null (OuterMeasure/Basic.lean:150), extraction_of_frequently_atTop (AtTopBot/Basic.lean:114), IsCompact.tendsto_subseq (Topology/Sequences.lean:298), tendsto_integral_filter_of_dominated_convergence, euclideanHausdorffMeasure_smul₀ (Euclidean/Volume/Measure.lean:152). Lean: all 12 types elaborate. The parent's frozen type compiles from the child types (stated as axioms) and uses exactly the six new children plus dimred_im_mass_measure, dtc_blowUp_scaling, dor_lmb_imrep_restrict_current and the standard axioms. ambient_calculus and density_representation are fully proved; cycle_rescale is proved from its siblings' frozen types; tangent_measures (B) is derived from (A). The runtime replay accepts the split.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
