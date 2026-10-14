<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.boundary_im-a1.slice_localization-a1 -->

## Theorem `Submission.dmcbr_bim_slice_localization`

Assume (REP), (IMC)(b), (IMC)(d) and (SL), which appear verbatim, in this order, as the hypotheses of the Lean statement. (REP) is the first conjunct of the frozen statement of dimred_mbl_current_foundations; (IMC)(b) and (IMC)(d) are the second and fourth components of its second conjunct (IMC); (SL) is the frozen statement of dimred_mbl_slice_mass_bounds. In words: (REP) a current X ∈ 𝒟_n(U) with locally finite mass in an open U has a representation (μ, ξ) with μ finite on compact subsets of U, ξ μ-a.e. strongly measurable, |ξ(x)(α)| ≤ |α| for all x and α, and X(ω) = ∫ ξ(ω) dμ (plus further properties not used here). (IMC)(b) for an IMRep (M, θ, ξ) of an open U and a measurable E there are a current A and an IMRep of U representing A with carrier M ∩ E, multiplicity θ and orientation ξ. (IMC)(d) the orientation ξ of an IMRep (M, θ, ξ) satisfies |ξ(x)(α)| ≤ |α| for all α and Hⁿ⌞M-a.e. x. (SL) slicing by an L-Lipschitz f of a current X ∈ 𝒟_{k+1}(U) (U open) represented by (μ, ξ), with ∂X represented by (μ', ξ') (μ, μ' finite on compact subsets of U; ξ, ξ' a.e. strongly measurable with |ξ(x)(α)| ≤ |α| and |ξ'(x)(β)| ≤ |β| a.e.), gives currents A_t(ω) = ∫_{f<t} ξ(ω) dμ and B_t(η) = ∫_{f<t} ξ'(η) dμ' in U with ∂A_t(η) = B_t(η) whenever tsupport η misses {f = t}, and ∫⁻_{(a,b)} M_W(∂A_t − B_t) dt ≤ L·μ(W ∩ {a < f < b}) for open W and a, b ∈ ℝ (and a pointwise liminf bound not used here). Let P, d ∈ ℕ, U ⊆ ℝ^P open, R ∈ 𝒟_{d+1}(U) integer multiplicity with M_W(∂R) < ∞ for every open W with compact closure in U, and x₀ ∈ U. Then there are r > 0 with closedBall(x₀, r) ⊆ U, a current R' ∈ 𝒟_{d+1}(U) and an IMRep R'' of U representing R' with carrier ⊆ B_r(x₀), such that M(R') < ∞, M(∂R') < ∞ (M = mass in U), and ∂R'(η) = ∂R(η) for every η ∈ 𝒟^d(U) with tsupport η ⊆ B_r(x₀).

Node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.boundary_im-a1.slice_localization-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5771

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4695, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4710

Decomposition children: None

## Lean problem

Declaration: `Submission.dmcbr_bim_slice_localization`

```lean
(∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) → (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α) → (∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (L : NNReal), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (k + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) k, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ η : TestFormOn U k, T.boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') → LipschitzWith L f → ∃ (A : ℝ → GeometricCurrentOn U (k + 1)) (B : ℝ → GeometricCurrentOn U k), (∀ (t : ℝ) (ω : TestFormOn U (k + 1)), A t ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) ∧ (∀ (t : ℝ) (η : TestFormOn U k), B t η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') ∧ (∀ (t : ℝ) (η : TestFormOn U k), Disjoint (tsupport (η : DifferentialForm (Euclid P) k)) {x | f x = t} → (A t).boundary η = B t η) ∧ (∀ (W : Set (Euclid P)) (t : ℝ), IsOpen W → ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) ∧ (∀ (W : Set (Euclid P)) (a b : ℝ), IsOpen W → ∫⁻ t in Ioo a b, ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * μ (W ∩ {x | a < f x ∧ f x < b}))) → ∀ (P d : ℕ) (U : Set (Euclid P)) (R : GeometricCurrentOn U (d + 1)) (x₀ : Euclid P), IsOpen U → IsIntegerMultiplicity R → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → R.boundary.massOn W < ∞) → x₀ ∈ U → ∃ r : ℝ, 0 < r ∧ closedBall x₀ r ⊆ U ∧ ∃ (R' : GeometricCurrentOn U (d + 1)) (Rr : IMRep U (d + 1)), Rr.Represents R' ∧ Rr.carrier ⊆ ball x₀ r ∧ R'.mass < ∞ ∧ R'.boundary.mass < ∞ ∧ ∀ η : TestFormOn U d, tsupport (η : DifferentialForm (Euclid P) d) ⊆ ball x₀ r → R'.boundary η = R.boundary η
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

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.boundary_im-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.boundary_im-a1.slice_localization-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 1–5 and the first half of Step 10 of the parent proof of dmcbr_boundary_isIntegerMultiplicity (Simon, Introduction to GMT, Ch. 6: Lemma 4.5 — for Lipschitz f, ⟨T, f, t⟩ = ∂(T⌞{f < t}) − (∂T)⌞{f < t} has ∫ M_W(⟨T, f, t⟩) dt < ∞; proof of 6.2, general case — cut T at a level t with M(∂(T⌞{f < t})) < ∞). Uses the siblings lcmp_imRep_measure_restrict (key imrep_restrict) and lcmp_massOn_le_of_vanish_off_compact (key vanish_off_compact), both comparator-accepted declarations reused at their frozen types.
Notation: |α| = covectorEuclideanNorm α. M_W(X) = X.massOn W is the supremum of ofReal X(ω) over the ω ∈ 𝒟^k(U) with tsupport ω ⊆ W and |ω(x)| ≤ 1 for all x ("admissible for M_W"). M(X) = M_U(X) (GeometricCurrentOn.mass). B_t(x₀) = ball x₀ t, H = μHE[d + 1], and ξ(ω) denotes x ↦ ξ(x)(ω(x)).
Change from the supplied text: step 5 takes the good radius from the integrated bound of (SL), not from the measure-convergence tool (MM) of dmcbr_measure_convergence_tools applied to the constant sequence μ_j = μ (that tool is a sibling of the parent node, not of this child). For a constant sequence, (MM) only repackages this same integrated bound as a measurable majorant; the integrated bound gives a radius directly and needs no measurability of t ↦ M_G(∂A_t − B_t).
0. Mass is bounded by a representing measure (Step 0(iii) of the parent proof). Let k ∈ ℕ, X ∈ 𝒟_k(U), ν a measure on ℝ^P and ζ : ℝ^P → Λ_k(ℝ^P). Assume |ζ(x)(α)| ≤ |α| for ν-a.e. x and all k-covectors α, and X(ω) = ∫ ζ(ω) dν for every ω ∈ 𝒟^k(U). Then M_W(X) ≤ ν(W) for every W ⊆ ℝ^P. Proof: let ω be admissible for M_W and g := ζ(ω). Then ofReal(X(ω)) = ofReal(∫ g dν) ≤ ‖∫ g dν‖ₑ ≤ ∫⁻ ‖g‖ₑ dν (enorm_integral_le_lintegral_enorm). This holds without integrability, because the Bochner integral of a non-integrable function is 0. Now take ν-a.e. x. If x ∈ W, then ‖g(x)‖ₑ = ofReal|ζ(x)(ω(x))| ≤ ofReal|ω(x)| ≤ 1. If x ∉ W, then x ∉ tsupport ω, so ω(x) = 0 and g(x) = ζ(x)(0) = 0. Hence ‖g‖ₑ ≤ 1_W ν-a.e., and ∫⁻ ‖g‖ₑ dν ≤ ∫⁻ 1_W dν ≤ ν(W) (lintegral_mono_ae, lintegral_indicator_one_le; W need not be measurable). Taking the supremum over admissible ω proves the claim.
1. Representation of R. R is integer multiplicity, so some IMRep R₀ = (M, θ, ξ) of U represents R: R(ω) = ∫_M θ ξ(ω) dH for ω ∈ 𝒟^{d+1}(U). Put μ := R₀.measure = (H⌞M).withDensity θ. By lcmp_imRep_measure_restrict:
 (a) μ ≪ H⌞M;
 (b) ξ is μ-a.e. strongly measurable;
 (c) R′.action(ω) = ∫_E ξ(ω) dμ for every Borel E ⊆ ℝ^P, every IMRep R′ of U with carrier M ∩ E, multiplicity θ and orientation ξ, and every (d+1)-form ω.
 μ is finite on compact subsets of U. Let K ⊆ U be compact. K is closed, hence Borel, so μ(K) = ∫⁻_K θ d(H⌞M) = ∫⁻_{M∩K} θ dH (withDensity_apply, Measure.restrict_restrict). The IMRep field locallyIntegrable_mult makes this finite.
 By (IMC)(d), |ξ(x)(α)| ≤ |α| for all α and H⌞M-a.e. x; by (a) this also holds for μ-a.e. x (AbsolutelyContinuous.ae_le).
 Finally take E := ℝ^P and R′ := R₀ in (c); this is allowed because the carrier of R₀ is M = M ∩ ℝ^P. It gives R₀.action(ω) = ∫_{ℝ^P} ξ(ω) dμ = ∫ ξ(ω) dμ (Measure.restrict_univ). Hence R(ω) = ∫ ξ(ω) dμ for every ω ∈ 𝒟^{d+1}(U).
2. Representation of ∂R. ∂R ∈ 𝒟_d(U), and M_W(∂R) < ∞ for every open W with compact closure in U. So (REP), applied to ∂R in U, gives a measure μ' and ξ' : ℝ^P → Λ_d(ℝ^P) such that:
 - μ'(K) < ∞ for every compact K ⊆ U;
 - ξ' is μ'-a.e. strongly measurable;
 - |ξ'(x)(α)| ≤ |α| for all x and α;
 - ∂R(η) = ∫ ξ'(η) dμ' for every η ∈ 𝒟^d(U).
3. A radius r₀. U is open and x₀ ∈ U, so there is ε > 0 with B_ε(x₀) ⊆ U (Metric.isOpen_iff). Put r₀ := ε/2 > 0. Then closedBall(x₀, r₀) ⊆ B_ε(x₀) ⊆ U, and closedBall(x₀, r₀) is compact. By steps 1–2, μ(closedBall(x₀, r₀)) < ∞ and μ'(closedBall(x₀, r₀)) < ∞.
4. Slicing. Let f(x) := dist(x, x₀) = |x − x₀|. It is 1-Lipschitz (LipschitzWith.dist_left), {x : f(x) < t} = B_t(x₀) and {x : f(x) = t} = sphere(x₀, t). Apply (SL) with k := d, T := R, the pairs (μ, ξ) and (μ', ξ') of steps 1–2, f and L := 1. Its hypotheses hold:
 - U is open;
 - μ and μ' are finite on compact subsets of U;
 - ξ and ξ' are a.e. strongly measurable;
 - |ξ| ≤ |·| μ-a.e. (step 1), and |ξ'| ≤ |·| everywhere, hence μ'-a.e.;
 - R and ∂R are represented as required.
 This gives currents A_t ∈ 𝒟_{d+1}(U) and B_t ∈ 𝒟_d(U) (t ∈ ℝ) with:
 (i) A_t(ω) = ∫_{B_t(x₀)} ξ(ω) dμ for ω ∈ 𝒟^{d+1}(U);
 (ii) B_t(η) = ∫_{B_t(x₀)} ξ'(η) dμ' for η ∈ 𝒟^d(U);
 (iii) ∂A_t(η) = B_t(η) whenever tsupport η is disjoint from sphere(x₀, t);
 (iv) ∫⁻_{t∈(a,b)} M_W(∂A_t − B_t) dt ≤ μ(W ∩ {a < f < b}) for every open W and all a, b ∈ ℝ (as L = 1).
5. A good radius. Let G := B_{r₀}(x₀) and apply (iv) with W := G, a := 0, b := r₀. The right side is at most μ(closedBall(x₀, r₀)) < ∞, because G ∩ {0 < f < r₀} ⊆ G ⊆ closedBall(x₀, r₀). Suppose M_G(∂A_t − B_t) = ∞ for every t ∈ (0, r₀). Then the left side is ∫⁻_{(0,r₀)} ∞ dt = ∞·L¹((0, r₀)) = ∞·r₀ = ∞ (setLIntegral_congr_fun on the measurable set (0, r₀), lintegral_const, Real.volume_Ioo, r₀ > 0). This is a contradiction. Hence there is r ∈ (0, r₀) with M_G(Z) < ∞, where Z := ∂A_r − B_r ∈ 𝒟_d(U).
6. Total mass of Z (Step 4 of the parent proof). Let η ∈ 𝒟^d(U) have tsupport η disjoint from sphere(x₀, r). Then Z(η) = ∂A_r(η) − B_r(η) = 0 by (iii). The sphere is compact (isCompact_sphere) and lies in the open set G, because r < r₀. Apply lcmp_massOn_le_of_vanish_off_compact with C := sphere(x₀, r), V := G, X := Z and the arbitrary set U. It gives M(Z) = M_U(Z) ≤ M_G(Z) < ∞.
7. Mass of B_r. By (ii), B_r(η) = ∫ ξ'(η) d(μ'⌞B_r(x₀)) for η ∈ 𝒟^d(U). The bound |ξ'(x)(α)| ≤ |α| holds everywhere, hence μ'⌞B_r(x₀)-a.e. Step 0 with k := d, ν := μ'⌞B_r(x₀), ζ := ξ' and W := U gives M(B_r) ≤ (μ'⌞B_r(x₀))(U) ≤ μ'(B_r(x₀)) ≤ μ'(closedBall(x₀, r₀)) < ∞.
8. Mass of ∂A_r. For every η ∈ 𝒟^d(U), ∂A_r(η) = B_r(η) + Z(η), since Z(η) = ∂A_r(η) − B_r(η). Let η be admissible for M_U. Then ofReal(∂A_r(η)) ≤ ofReal(B_r(η)) + ofReal(Z(η)) (ENNReal.ofReal_add_le) ≤ M_U(B_r) + M_U(Z) (le_massOn). Taking the supremum, M(∂A_r) ≤ M(B_r) + M(Z), which is finite by steps 6–7.
9. A_r is represented by an IMRep with carrier in B_r(x₀) (Step 5 of the parent proof). Apply (IMC)(b) to R₀ and E := B_r(x₀), which is open and hence Borel. It gives an IMRep R'' of U with carrier M ∩ B_r(x₀), multiplicity θ and orientation ξ. Let ω ∈ 𝒟^{d+1}(U). Step 1(c) with E := B_r(x₀) and R′ := R'' gives R''.action(ω) = ∫_{B_r(x₀)} ξ(ω) dμ, and this is A_r(ω) by (i). So R'' represents R' := A_r, and its carrier M ∩ B_r(x₀) is contained in B_r(x₀).
10. Mass of R'. By (i), A_r(ω) = ∫ ξ(ω) d(μ⌞B_r(x₀)). The bound |ξ(x)(α)| ≤ |α| holds μ-a.e. (step 1), hence μ⌞B_r(x₀)-a.e. (ae_restrict_of_ae). Step 0 with k := d + 1, ν := μ⌞B_r(x₀) and W := U gives M(R') ≤ (μ⌞B_r(x₀))(U) ≤ μ(B_r(x₀)) ≤ μ(closedBall(x₀, r₀)) < ∞.
11. Agreement with ∂R (first half of Step 10 of the parent proof). Let η ∈ 𝒟^d(U) with tsupport η ⊆ B_r(x₀). Points of B_r(x₀) have distance < r from x₀, so tsupport η is disjoint from sphere(x₀, r). Hence ∂R'(η) = ∂A_r(η) = B_r(η) by (iii), and B_r(η) = ∫_{B_r(x₀)} ξ'(η) dμ' by (ii). This equals ∫ ξ'(η) dμ', because the integrand vanishes off B_r(x₀): there x ∉ tsupport η, so η(x) = 0 and ξ'(x)(0) = 0 (setIntegral_eq_integral_of_forall_compl_eq_zero). By step 2 it equals ∂R(η).
12. Conclusion. We have r > 0 and closedBall(x₀, r) ⊆ closedBall(x₀, r₀) ⊆ U, as r < r₀. Take R' = A_r and R''. Then R'' represents R' with carrier ⊆ B_r(x₀) (step 9), M(R') < ∞ (step 10) and M(∂R') < ∞ (step 8). Also ∂R'(η) = ∂R(η) for every η ∈ 𝒟^d(U) supported in B_r(x₀) (step 11). ∎

Lean note (verified realization of the numbered proof above; not part of the proof). The following tactic proof of `Submission.dmcbr_bim_slice_localization` compiles against the frozen contract (Lean v4.35.0-rc3, Mathlib 25730c7c, SimonGMT 2b366308). It is placed after `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the contract's `open` commands, with only the two declared sibling declarations `Submission.lcmp_imRep_measure_restrict` and `Submission.lcmp_massOn_le_of_vanish_off_compact` (their accepted proofs) in scope. `#print axioms` reports only propext, Classical.choice and Quot.sound, and `exact Submission.dmcbr_bim_slice_localization` closes the frozen type in the comparator scope. Do not open the ContDiff scope, whose notation makes ω a token; smoothness is written ContDiff ℝ (⊤ : ℕ∞).
```lean
  intro hREP hIMCb hIMCd hSL P d U R x₀ hU hRim hbd hx₀
  -- the local mass of a current is bounded by any representing measure
  have hmassle : ∀ {k : ℕ} (X : GeometricCurrentOn U k) (ν : Measure (Euclid P))
      (ζ : Euclid P → MultiVector P k),
      (∀ᵐ x ∂ν, ∀ α : Covector (Euclid P) k, |ζ x α| ≤ covectorEuclideanNorm α) →
      (∀ ω : TestFormOn U k, X ω = ∫ x, ζ x ((ω : DifferentialForm (Euclid P) k) x) ∂ν) →
      ∀ W : Set (Euclid P), X.massOn W ≤ ν W := by
    intro k X ν ζ hζ hrep W
    apply sSup_le
    rintro _ ⟨ω, ⟨hsupp, hnorm⟩, rfl⟩
    change ENNReal.ofReal (X ω) ≤ ν W
    rw [hrep ω]
    calc ENNReal.ofReal (∫ x, ζ x ((ω : DifferentialForm (Euclid P) k) x) ∂ν)
        ≤ ‖∫ x, ζ x ((ω : DifferentialForm (Euclid P) k) x) ∂ν‖ₑ := by
          rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ ∫⁻ x, ‖ζ x ((ω : DifferentialForm (Euclid P) k) x)‖ₑ ∂ν :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ x, W.indicator 1 x ∂ν := by
          apply lintegral_mono_ae
          filter_upwards [hζ] with x hx
          by_cases hxW : x ∈ W
          · rw [indicator_of_mem hxW, Pi.one_apply, Real.enorm_eq_ofReal_abs]
            exact ENNReal.ofReal_le_one.mpr ((hx _).trans (hnorm x))
          · have : (ω : DifferentialForm (Euclid P) k) x = 0 :=
              image_eq_zero_of_notMem_tsupport (fun h => hxW (hsupp h))
            simp [this]
      _ ≤ ν W := lintegral_indicator_one_le W
  -- the representation of R by the weight of an IMRep
  obtain ⟨R₀, hR₀⟩ := hRim
  obtain ⟨hac, haesm, hrestr⟩ := Submission.lcmp_imRep_measure_restrict P (d + 1) U R₀
  have hfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → R₀.measure K < ∞ := by
    intro K hK hKU
    rw [IMRep.measure, withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
    exact lt_top_iff_ne_top.mpr (R₀.locallyIntegrable_mult K hK hKU)
  have hξb : ∀ᵐ x ∂R₀.measure, ∀ α : Covector (Euclid P) (d + 1),
      |R₀.orient x α| ≤ covectorEuclideanNorm α :=
    hac.ae_le (hIMCd P (d + 1) U R₀)
  have hRrep : ∀ ω : TestFormOn U (d + 1),
      R ω = ∫ x, R₀.orient x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂R₀.measure := by
    intro ω
    have h := (hrestr univ R₀ MeasurableSet.univ (inter_univ _).symm rfl rfl).2
      (ω : DifferentialForm (Euclid P) (d + 1))
    rw [Measure.restrict_univ] at h
    rw [hR₀ ω, h]
  -- the representation of ∂R
  obtain ⟨μ', ξ', -, hfin', -, haesm', hξ'b, hbrep, -⟩ := hREP P d U R.boundary hU hbd
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x₀ hx₀
  have hr₀pos : 0 < ε / 2 := by positivity
  have hcb₀ : closedBall x₀ (ε / 2) ⊆ U := (closedBall_subset_ball (by linarith)).trans hεU
  have hfL : LipschitzWith 1 (fun x : Euclid P => dist x x₀) := LipschitzWith.dist_left x₀
  -- slicing by the distance from x₀
  obtain ⟨A, B, hA, hB, hAB, -, hint5⟩ := hSL P d U R R₀.measure μ' R₀.orient ξ'
    (fun x => dist x x₀) 1 hU hfin hfin' haesm haesm' hξb (Eventually.of_forall hξ'b) hRrep hbrep hfL
  have hfinball : R₀.measure (closedBall x₀ (ε / 2)) < ∞ := hfin _ (isCompact_closedBall _ _) hcb₀
  have hfinball' : μ' (closedBall x₀ (ε / 2)) < ∞ := hfin' _ (isCompact_closedBall _ _) hcb₀
  -- a good radius
  obtain ⟨r, hr, hZr⟩ : ∃ r ∈ Ioo 0 (ε / 2),
      ((A r).boundary - B r).massOn (ball x₀ (ε / 2)) < ∞ := by
    by_contra hcon
    push Not at hcon
    have hlint := hint5 (ball x₀ (ε / 2)) 0 (ε / 2) isOpen_ball
    have htop : ∫⁻ t in Ioo 0 (ε / 2), ((A t).boundary - B t).massOn (ball x₀ (ε / 2)) = ∞ := by
      rw [setLIntegral_congr_fun measurableSet_Ioo (fun t ht => top_le_iff.mp (hcon t ht))]
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero]
      exact ENNReal.top_mul (by simpa using hr₀pos)
    rw [htop, ENNReal.coe_one, one_mul] at hlint
    have hle : R₀.measure (ball x₀ (ε / 2) ∩ {x | 0 < dist x x₀ ∧ dist x x₀ < ε / 2}) < ∞ :=
      lt_of_le_of_lt (measure_mono (inter_subset_left.trans ball_subset_closedBall)) hfinball
    exact absurd (lt_of_le_of_lt hlint hle) (lt_irrefl _)
  set Z := (A r).boundary - B r with hZ
  have hZvan : ∀ η : TestFormOn U d,
      Disjoint (tsupport (η : DifferentialForm (Euclid P) d)) (sphere x₀ r) → Z η = 0 := by
    intro η hη
    have := hAB r η hη
    change (A r).boundary η - B r η = 0
    rw [this, sub_self]
  have hsph : sphere x₀ r ⊆ ball x₀ (ε / 2) := fun y hy => by
    rw [mem_sphere] at hy; rw [mem_ball, hy]; exact hr.2
  -- the slice has finite total mass
  have hZU : Z.massOn U < ∞ :=
    lt_of_le_of_lt (Submission.lcmp_massOn_le_of_vanish_off_compact P d U (ball x₀ (ε / 2))
      (sphere x₀ r) Z (isCompact_sphere _ _) isOpen_ball hsph hZvan U) hZr
  have hBU : (B r).massOn U < ∞ := by
    refine lt_of_le_of_lt (hmassle (B r) (μ'.restrict (ball x₀ r)) ξ'
      (ae_restrict_of_ae (Eventually.of_forall hξ'b)) (fun η => hB r η) U) ?_
    refine lt_of_le_of_lt ?_ hfinball'
    calc μ'.restrict (ball x₀ r) U ≤ μ'.restrict (ball x₀ r) univ := measure_mono (subset_univ _)
      _ = μ' (ball x₀ r) := Measure.restrict_apply_univ _
      _ ≤ μ' (closedBall x₀ (ε / 2)) :=
          measure_mono (ball_subset_closedBall.trans (closedBall_subset_closedBall hr.2.le))
  have hAbU : (A r).boundary.massOn U < ∞ := by
    refine lt_of_le_of_lt (b := (B r).massOn U + Z.massOn U) ?_ (ENNReal.add_lt_top.mpr ⟨hBU, hZU⟩)
    apply sSup_le
    rintro _ ⟨η, hη, rfl⟩
    have hsplit : (A r).boundary η = B r η + Z η := by
      change (A r).boundary η = B r η + ((A r).boundary η - B r η); ring
    change ENNReal.ofReal ((A r).boundary η) ≤ _
    rw [hsplit]
    exact ENNReal.ofReal_add_le.trans (add_le_add ((B r).le_massOn hη) (Z.le_massOn hη))
  -- R' := A r = R⌞B_r(x₀) is represented by the restricted IMRep
  obtain ⟨A', Rr, -, hcar, hmult, hor⟩ := hIMCb P (d + 1) U R₀ (ball x₀ r) hU measurableSet_ball
  have hRrA : Rr.Represents (A r) := by
    intro ω
    rw [hA r ω]
    exact ((hrestr (ball x₀ r) Rr measurableSet_ball hcar hmult hor).2 _).symm
  have hAU : (A r).massOn U < ∞ := by
    refine lt_of_le_of_lt (hmassle (A r) (R₀.measure.restrict (ball x₀ r)) R₀.orient
      (ae_restrict_of_ae hξb) (fun ω => hA r ω) U) ?_
    refine lt_of_le_of_lt ?_ hfinball
    calc R₀.measure.restrict (ball x₀ r) U ≤ R₀.measure.restrict (ball x₀ r) univ :=
          measure_mono (subset_univ _)
      _ = R₀.measure (ball x₀ r) := Measure.restrict_apply_univ _
      _ ≤ R₀.measure (closedBall x₀ (ε / 2)) :=
          measure_mono (ball_subset_closedBall.trans (closedBall_subset_closedBall hr.2.le))
  refine ⟨r, hr.1, (closedBall_subset_closedBall hr.2.le).trans hcb₀, A r, Rr, hRrA, ?_, hAU, hAbU, ?_⟩
  · rw [hcar]; exact inter_subset_right
  · intro η hη
    have hdisj : Disjoint (tsupport (η : DifferentialForm (Euclid P) d)) (sphere x₀ r) := by
      refine Set.disjoint_left.mpr fun y hy hys => ?_
      have h1 := hη hy
      rw [mem_ball] at h1; rw [mem_sphere] at hys
      linarith
    rw [hAB r η hdisj, hB r η, hbrep η]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have : (η : DifferentialForm (Euclid P) d) x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hx (hη h))
    rw [this, map_zero]
```

## Key steps

1. Bound local masses by representing measures (step 0); represent R by μ = θH^{d+1}⌞M and ξ (lcmp_imRep_measure_restrict, local integrability of θ, (IMC)(d)), and ∂R by (μ', ξ') from (REP).
2. Slice by f = |· − x₀| with (SL), L = 1; the integrated bound on (0, r₀) gives r ∈ (0, r₀) with M_{B_{r₀}(x₀)}(∂A_r − B_r) < ∞.
3. ∂A_r − B_r vanishes off the compact sphere {f = r} ⊆ B_{r₀}(x₀), so its total mass is finite (lcmp_massOn_le_of_vanish_off_compact); M(B_r) ≤ μ'(B_r(x₀)) < ∞, hence M(∂A_r) < ∞.
4. (IMC)(b) with E = B_r(x₀) and lcmp_imRep_measure_restrict give an IMRep with carrier M ∩ B_r(x₀) representing R' := A_r, and M(R') ≤ μ(B_r(x₀)) < ∞.
5. For η supported in B_r(x₀): ∂R'(η) = B_r(η) = ∫ξ'(η)dμ' = ∂R(η).

## Reference use

### local-project

Queries:
- `cat RUN/local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; cmp GMT/Ch07/Submission.lean GMT/Ch07/Contract.lean; cmp SNAPSHOT/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean`
- `python3 scans of RUN/dag.json: selected node and its siblings convergence_tools-a1 / im_local-a1 (frozen types, status); the five parent-dependency types against the hypotheses of the selected type (dimred_mbl_current_foundations == (REP) ∧ (IMC) byte-for-byte); lean_name lookups for rsd_mw_tfa_norm_props, cmr_abs_apply_le_massOn, lcmp_massOn_le_of_vanish_off_compact, lcmp_imRep_measure_restrict, dtc_extend_by_zero (each unique, status accepted, candidate commit set), cbr_bim_* (status decomposing, other parent) and dmcbr_bim_* (no node); identical-type search for the three new statements; dmcbr_isIntegerMultiplicity_of_local type == cbr_isIntegerMultiplicity_of_local type`
- `python3 difflib comparison of the parent-supplied proofs in RUN/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-10c568d35f and RUN/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-daf82ca7c6; reading decomposition-v3.json and decomposition-audit-v1..v3.json of the former`
- `grep -n '_existing_lean_name_problem|_accepted_checkpoint|def _solve_children' /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py; sed -n 179,215p /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/store.py`
- `git show <commit>:GMT/Ch07/Submission.lean and git diff <commit>^ <commit> for f492ba4a, 7a706164, a3cc98d1, ae810e9b, 2527748d (extraction of the accepted proofs; reused types compared byte-for-byte)`
- `rg -c dmcbr_bim SNAPSHOT (no match, exit 1); rg -c dmcbr_bim GMT (no match, exit 1); rg -n 'dmcbr_bim|cbr_bim' SNAPSHOT/project/GMT (no match, exit 1)`
- `rg -n -i 'boundary rectifiab|BoundaryRectif|deformation|closure theorem|isIntegerMultiplicity_boundary|boundary_isIntegerMultiplicity' SNAPSHOT/project/GMT -g '*.lean' (matches only GMT/Ch06 Contract/Submission defs DeformationTheorem, BoundaryRectifiability and GMT/Ch02 IsAdmissibleDeformation); cmp SNAPSHOT/project/GMT/Ch06/Submission.lean SNAPSHOT/project/GMT/Ch06/Contract.lean (identical, main_theorem unproved)`
- `rg -n -F over SNAPSHOT/mathlib/Mathlib: theorem enorm_integral_le_lintegral_enorm, theorem lintegral_indicator_one_le, theorem setIntegral_eq_integral_of_forall_compl_eq_zero, theorem setLIntegral_congr_fun, theorem withDensity_apply, theorem volume_Ioo, theorem dist_left, theorem isCompact_sphere, theorem ofReal_add_le, theorem ae_restrict_of_ae, theorem tendsto_pow_atTop_nhds_zero_of_lt_one, lemma squeeze_zero, lemma HasCompactMulSupport.exists_bound_of_continuous (all found)`
- `rg -l -F over .lake/packages/simongmt/Poincare: theorem WeaklyConvergesOn.boundary, theorem GeometricCurrentOn.boundary_boundary, theorem tsupport_exteriorDerivative_subset, theorem GeometricCurrentOn.massOn_mono, theorem GeometricCurrentOn.le_massOn, theorem GeometricCurrentOn.restrictDomain_apply, def testFormOnInclusion, theorem covectorEuclideanNorm_zero (all found)`
- `grep/sed on book/chapter-06.txt for Simon 4.5 (slicing lemma), 5.3 (scaled deformation theorem), 6.2 (weak polyhedral approximation), 6.3 (boundary rectifiability)`
- `lake env lean (v4.35.0-rc3) on /tmp/dmcbr-bim-split/lean/Challenge_*.lean (8 comparator challenges), /tmp/dmcbr-bim-split/lean/AllProofs.lean (accepted proofs + new children + assembly + exact-solution checks + #print axioms) and /tmp/dmcbr-bim-split/lean/Isolated_dmcbr_bim_*.lean (3 files); lean_contract.validate_lean_statement on all 8 types`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-daf82ca7c6/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-4c4627e694/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-10c568d35f/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-10c568d35f/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-10c568d35f/decomposition-audit-v3.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/store.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/ProperSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/tmp/dmcbr-bim-split/lean/AllProofs.lean`
- `/tmp/dmcbr-bim-split/lean/Isolated_dmcbr_bim_slice_localization.lean`
- `/tmp/dmcbr-bim-split/lean/Isolated_dmcbr_bim_extension_mass_bounds.lean`
- `/tmp/dmcbr-bim-split/lean/Isolated_dmcbr_bim_boundary_im_of_compact_support.lean`

Pins match: workspace HEAD b4d606d is the snapshot project commit, Mathlib is 25730c7c and SimonGMT is 2b366308. Submission.lean is byte-identical to the frozen contract and to the snapshot copy. The snapshot project has no dmcbr_bim or cbr_bim declaration and no proved boundary-rectifiability, closure or deformation theorem: GMT/Ch06/Contract.lean states DeformationTheorem (5.3) and BoundaryRectifiability (6.3) only as Prop definitions in namespace GMT.Ch06, over that chapter's own definitions, and its Submission.lean equals the contract (main_theorem unproved), so nothing there is reusable. The SimonGMT Chapter 6 API used by the child proofs (massOn, le_massOn, massOn_mono, boundary_boundary, WeaklyConvergesOn.boundary, restrictDomain, testFormOnInclusion, tsupport_exteriorDerivative_subset) is present. Every Mathlib lemma cited by the child proofs exists in the pinned sources. The DAG node cbr_boundary_isIntegerMultiplicity has a byte-identical frozen type and an audited split of this shape; its three new children are unaccepted and owned by another parent, so they are restated here under the fresh names dmcbr_bim_*, which match no DAG node or file. The five reused declarations are unique, accepted, with candidate commits, at byte-identical types. All 8 child types elaborate as comparator challenges. The 3 new child proofs compile with only their declared siblings. The hypothesis-only assembly proves the exact parent type from the children and the frozen type of dmcbr_isIntegerMultiplicity_of_local, with axioms propext, Classical.choice and Quot.sound.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
