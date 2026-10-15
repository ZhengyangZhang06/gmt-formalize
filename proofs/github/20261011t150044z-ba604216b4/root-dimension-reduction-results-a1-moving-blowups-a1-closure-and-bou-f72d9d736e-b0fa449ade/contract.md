<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.lower_density-a1 -->

## Theorem `Submission.dmcbr_lower_density_of_slice_property`

Assume (REP), (MR), (SL), (DT) and (VO). Here (REP), (MR), (IMC), (SL), (DT), (VO) denote the parent node's dependency theorems: (REP) and (IMC) are the first and second conjuncts of the frozen statement of dimred_mbl_current_foundations, (MR) is the mass identity of dor_imrep_massOn_eq_measure_and_support (the first conjunct of its conclusion: M_W(T) = R.measure(W) for every IMRep R of T in an open U and every open W; its support identity is not needed), and (SL), (DT), (VO) are the frozen statements of dimred_mbl_slice_mass_bounds, dimred_mbl_deformation_theorem and dtc_vanish_off_support. They are not available in this child's environment, so the needed ones appear as hypotheses of the Lean statement ((REP), (IMC), (SL), (DT), (VO) verbatim, (MR) as the stated mass identity) and are discharged by the parent proof. In words: (REP) a current with locally finite mass in an open U has a mass representation (μ, ξ) (μ(W) = M_W for open W, μ(ℝ^P∖U) = 0, μ finite on compacts of U, |ξ| ≤ 1, X(ω) = ∫ξ(ω)dμ, and μ(E) = 0 whenever Hⁿ(E) = 0 if also the boundary has locally finite mass); (MR) M_W(X) = R.measure(W) for an IMRep R of X and open W; (IMC) (a) locality of approximate tangent spaces for nested Borel sets, (b) the restriction of an IMRep to a Borel set is an IMRep of some current, (c) differences of IM currents are IM, (d) IMRep orientations satisfy |orient(x)(α)| ≤ |α| a.e.; (SL) slicing by an L-Lipschitz f of a current represented together with its boundary, with Z_t := ∂(X⌞{f<t}) − (∂X)⌞{f<t} vanishing on forms supported off {f = t}, M_W(Z_t) ≤ L liminf_h h⁻¹μ(W ∩ {t−h<f<t}) and the integrated bound; (DT) the deformation theorem with its mass and support bounds; (VO) a current vanishes on test forms whose support misses its support. For all P, d ∈ ℕ there is η₀ > 0 with the following property. A current Y ∈ 𝒟_{d+1}(ℝ^P) has the integer slice property (ISP) if for all admissible representations (μ, ξ) of Y and (μ', ξ') of ∂Y in ℝ^P (Borel measures finite on compact sets; a.e. strongly measurable fields of (d+1)- resp. d-vectors with |ξ(x)(α)| ≤ |α| a.e.; Y(ω) = ∫ξ(ω)dμ and ∂Y(η) = ∫ξ'(η)dμ' for all test forms) and every Lipschitz f : ℝ^P → ℝ, for L¹-a.e. t ∈ ℝ, every pair of currents A ∈ 𝒟_{d+1}(ℝ^P), B ∈ 𝒟_d(ℝ^P) with A(ω) = ∫_{f<t}ξ(ω)dμ and B(η) = ∫_{f<t}ξ'(η)dμ' for all test forms has ∂A − B integer multiplicity. If C ∈ 𝒟_{d+1}(ℝ^P) has ∂C = 0 and ISP, μ is a Borel measure on ℝ^P with μ(K) < ∞ for compact K and μ(W) = M_W(C) for every open W, and ξ is a μ-a.e. strongly measurable field of (d+1)-vectors with |ξ(x)(α)| ≤ |α| for μ-a.e. x and C(ω) = ∫ξ(ω)dμ for every test form ω, then liminf_{r↓0} μ(B_r(x))/(ω_{d+1}r^{d+1}) ≥ η₀ for μ-a.e. x (ω_{d+1} = unitBallVolume (d+1)).

Node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.lower_density-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5040

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5785

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5275, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5279, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6824, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5301, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5307, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6832, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6837

## Lean problem

Declaration: `Submission.dmcbr_lower_density_of_slice_property`

```lean
(∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → (∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (L : NNReal), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (k + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) k, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ η : TestFormOn U k, T.boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') → LipschitzWith L f → ∃ (A : ℝ → GeometricCurrentOn U (k + 1)) (B : ℝ → GeometricCurrentOn U k), (∀ (t : ℝ) (ω : TestFormOn U (k + 1)), A t ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) ∧ (∀ (t : ℝ) (η : TestFormOn U k), B t η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') ∧ (∀ (t : ℝ) (η : TestFormOn U k), Disjoint (tsupport (η : DifferentialForm (Euclid P) k)) {x | f x = t} → (A t).boundary η = B t η) ∧ (∀ (W : Set (Euclid P)) (t : ℝ), IsOpen W → ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) ∧ (∀ (W : Set (Euclid P)) (a b : ℝ), IsOpen W → ∫⁻ t in Ioo a b, ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * μ (W ∩ {x | a < f x ∧ f x < b}))) → (∀ (P m : ℕ), ∃ c : NNReal, 1 ≤ c ∧ ∀ (ρ : ℝ) (K : Set (Euclid P)) (Λ : NNReal), 0 < ρ → IsCompact K → ∃ 𝒬 : Set (GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), 𝒬.Finite ∧ ∀ T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), IsIntegerMultiplicity T → T.support ⊆ K → T.mass ≤ Λ → T.boundary.mass < ∞ → ∃ Q ∈ 𝒬, ∃ (R : GeometricCurrentOn (univ : Set (Euclid P)) (m + 2)) (S : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), IsIntegerMultiplicity Q ∧ IsIntegerMultiplicity Q.boundary ∧ IsIntegerMultiplicity R ∧ T - Q - S = R.boundary ∧ (Q = 0 ∨ ENNReal.ofReal (ρ ^ (m + 1)) ≤ Q.mass) ∧ Q.mass ≤ c * T.mass ∧ Q.boundary.mass ≤ c * T.boundary.mass ∧ R.mass ≤ c * ENNReal.ofReal ρ * T.mass ∧ S.mass ≤ c * ENNReal.ofReal ρ * T.boundary.mass ∧ Q.support ∪ R.support ⊆ thickening (3 * Real.sqrt P * ρ) T.support ∧ Q.boundary.support ∪ S.support ⊆ thickening (3 * Real.sqrt P * ρ) T.boundary.support) → (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → ∀ (P d : ℕ), ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ (C : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (d + 1)), C.boundary = 0 → (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → (∀ W : Set (Euclid P), IsOpen W → C.massOn W = μ W) → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (d + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), C ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (d + 1)) (ξ' : Euclid P → MultiVector P d), (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (d + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) d, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), C ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, (C).boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → ∀ (f : Euclid P → ℝ) (L : NNReal), LipschitzWith L f → ∀ᵐ t ∂(volume : Measure ℝ), ∀ (A : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (B : GeometricCurrentOn (univ : Set (Euclid P)) d), (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), A ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, B η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → IsIntegerMultiplicity (A.boundary - B)) → ∀ᵐ x ∂μ, ENNReal.ofReal η₀ ≤ liminf (fun r : ℝ => μ (ball x r) / (unitBallVolume (d + 1) * ENNReal.ofReal (r ^ (d + 1)))) (𝓝[>] 0)
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

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.lower_density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, V5 (Simon Ch. 6, 8.2 (2)–(6), with the corrections noted in the parent: the lower density replaces Θ^{*n} < η, and the filling's support is controlled by the deformation theorem) and T3 (cone inequality). The hypotheses (REP), (MR), (SL), (DT), (VO) are the relevant parts of the frozen statements of the parent node's dependency theorems (not available to this child, hence assumed) dimred_mbl_current_foundations (first conjunct), dor_imrep_massOn_eq_measure_and_support (mass identity), dimred_mbl_slice_mass_bounds, dimred_mbl_deformation_theorem and dtc_vanish_off_support. Sibling used: dmcbr_isoperimetric_filling (which needs only (DT)). ISP(C) is the integer slice property as in the statement (for all admissible representations of C and ∂C, every Lipschitz f and a.e. t, ∂A − B is IM for the restriction currents A, B). n := d + 1, ω_n := unitBallVolume n, Θ(x) := liminf_{r↓0} μ(B_r(x))/(ω_n rⁿ), ‖ω‖_∞ := sup_x |ω(x)|.

Constants. If n ≥ 2 let c ≥ 1 be the constant of dmcbr_isoperimetric_filling for (P, m := n − 2) and κ(η) := c(2c)^{1/(n−1)}(2n)^{n/(n−1)}(ηω_n)^{1/(n−1)}; if n = 1 let κ :≡ 0. Choose η₀ ∈ (0, 1/4) with κ(η₀) ≤ 1/2, 2η₀ω_1 < 1 (used only when n = 1) and, if n ≥ 2, 4cnη₀ω_n ≤ 1 (possible since κ(η) → 0 as η ↓ 0). η₀ depends only on (P, d).

Step 0 (cone inequality, parent T3). Claim: if X ∈ 𝒟_n(ℝ^P) has M(X) < ∞, ∂X = 0 and spt X ⊆ B̄_ϱ(x₀), then |X(ω)| ≤ ϱ M(X)‖dω‖_∞ for all ω ∈ 𝒟^n(ℝ^P). Proof: for a smooth j-form γ (j ≥ 1) let (Kγ)(x) := ∫_0^1 s^{j−1} ι_{x−x₀}γ(x₀ + s(x − x₀)) ds (homotopy operator of the contraction h_s(x) = x₀ + s(x − x₀)); differentiation under the integral sign shows Kγ is smooth, and Cartan's formula dι_v + ι_v d = L_v for the radial field v(x) = x − x₀ gives dKγ + Kdγ = γ − h₀^#γ = γ (h₀ is constant and j ≥ 1). Since |ι_vβ| ≤ |v||β| for the Euclidean coefficient norms, |Kγ(x)| ≤ |x − x₀|‖γ‖_∞/j. (The bound |ι_vβ| ≤ |v||β| uses the invariance of the coefficient norm under orthogonal changes of coordinates, recorded by the accepted DAG declarations regcomp_covector_sq_sum_orthonormalBasis and regcomp_covector_sq_sum_basis_invariant; without it, Cauchy–Schwarz in standard coordinates gives |ι_vβ|² = Σ_J (Σ_i v_iβ(e_i, e_J))² ≤ |v|² Σ_J Σ_i β(e_i, e_J)² = j|v|²|β|², hence |Kγ(x)| ≤ |x − x₀|‖γ‖_∞/√j ≤ |x − x₀|‖γ‖_∞, which suffices for the bound below.) Choose ζ ∈ C_c^∞(ℝ^P; [0, 1]) equal to 1 on a neighbourhood of spt X (spt X is compact). By (VO), X(ω) = X(ζω) (tsupport((1 − ζ)ω) misses spt X), and X(ζω) = X(ζdKω) + X(ζKdω); further X(ζdKω) = X(d(ζKω)) = ∂X(ζKω) = 0, because the test form ζdKω − d(ζKω) vanishes on the open set where ζ ≡ 1, a neighbourhood of spt X, so X annihilates it by (VO) again (by the Leibniz rule this form is −dζ ∧ Kω; the argument does not need that rule). Let (μ_X, ξ_X) be the (REP) representation of X (finite mass); μ_X is carried by spt X (μ_X(G) = M_G(X) = 0 for every open G disjoint from spt X, by (VO)). Hence |X(ω)| = |∫ ξ_X(ζKdω) dμ_X| ≤ ∫_{spt X} |Kdω| dμ_X ≤ ϱ‖dω‖_∞ μ_X(ℝ^P)/(n+1) ≤ ϱ M(X)‖dω‖_∞.

1. Measurability of Θ. For r > 0, x ↦ μ(B_r(x)) is lower semicontinuous (if x_m → x then 1_{B_r(x)} ≤ liminf 1_{B_r(x_m)}; Fatou), and r ↦ μ(B_r(x)) is left continuous (B_r = ⋃_{s<r} B_s); the quotient μ(B_r(x))/(ω_nrⁿ) is left continuous in r, so Θ(x) = lim_m inf_{r∈ℚ∩(0,1/m)} μ(B_r(x))/(ω_nrⁿ) is Borel.
2. Reduction. A := {x : Θ(x) < η₀} is Borel; μ is a locally finite Borel measure on ℝ^P, hence inner regular by compact sets on Borel sets, so it suffices to prove μ(K') = 0 for compact K' ⊆ A. Fix such K', ε₀ ∈ (0, 1) and W := {x : dist(x, K') < ε₀} (bounded open, μ(W) < ∞).
3. Good radii. Let x₁ ∈ K' and 0 < δ < ε₀/(2 + 3√P). Since Θ(x₁) < η₀ there is s ∈ (0, δ) with F(s) < η₀ω_n sⁿ, F(ρ) := μ(B_ρ(x₁)). F and F^{1/n} are nondecreasing, hence differentiable a.e., and, with F(0) := μ(B_0(x₁)) = μ(∅) = 0 (so F is nondecreasing on [0, s]), ∫_0^s (F^{1/n})' ≤ F(s)^{1/n} − F(0)^{1/n} = F(s)^{1/n} < (η₀ω_n)^{1/n}s (Mathlib MonotoneOn.intervalIntegral_deriv_mem_uIcc, module Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable, which GMT.Ch07.Submission does not import, so the formalization must import it). Hence the set of ρ ∈ (0, s) with (F^{1/n})'(ρ) ≤ 2(η₀ω_n)^{1/n} has positive measure. Remove the null sets where F or F^{1/n} is not differentiable, the countable set {ρ : μ(∂B_ρ(x₁)) > 0} (μ is σ-finite), and the null set of ρ where the ISP conclusion fails for f := |· − x₁| (1-Lipschitz) with the admissible representations (μ, ξ) of C and (0, 0) of ∂C = 0. Choose ρ in the remaining (non-empty) set.
4. The slice. (SL) with k := n − 1, T := C, (μ, ξ), (0, 0), f := |· − x₁|, L := 1 gives currents A_ρ with A_ρ(ω) = ∫_{B_ρ(x₁)} ξ(ω) dμ =: (C⌞B_ρ(x₁))(ω), B_ρ = 0, and Z := ∂A_ρ with Z(η) = 0 whenever tsupport η ∩ ∂B_ρ(x₁) = ∅ (so spt Z ⊆ ∂B_ρ(x₁), compact) and M(Z) ≤ liminf_{h↓0} h⁻¹μ({ρ − h < |· − x₁| < ρ}) ≤ liminf_{h↓0} h⁻¹(F(ρ) − F(ρ − h)) = F'(ρ). By the choice of ρ, Z = ∂A_ρ − 0 is IM; if n ≥ 2, ∂Z = ∂∂A_ρ = 0.
5. Mass bound. As F = (F^{1/n})ⁿ with both differentiable at ρ, F'(ρ) = nF(ρ)^{(n−1)/n}(F^{1/n})'(ρ) ≤ 2n(η₀ω_n)^{1/n}F(ρ)^{(n−1)/n}; with F(ρ) ≤ F(s) < η₀ω_nsⁿ this gives M(Z) ≤ 2nη₀ω_n s^{n−1}, and also M(Z)^{n/(n−1)} ≤ (2n)^{n/(n−1)}(η₀ω_n)^{1/(n−1)}F(ρ) when n ≥ 2.
6. Filling. If n ≥ 2: dmcbr_isoperimetric_filling (m := n − 2; Z IM, spt Z compact, ∂Z = 0, M(Z) < ∞) gives an IM S ∈ 𝒟_n(ℝ^P) with ∂S = Z, M(S) ≤ c(2cM(Z))^{1/(n−1)}M(Z) = c(2c)^{1/(n−1)}M(Z)^{n/(n−1)} ≤ κ(η₀)F(ρ) = κ(η₀)μ(B_ρ(x₁)), and spt S ⊆ thickening(3√P(2cM(Z))^{1/(n−1)}, ∂B_ρ(x₁)) ⊆ B̄_{ρ + 3√P(4cnη₀ω_n)^{1/(n−1)}s}(x₁) ⊆ B̄_{(1+3√P)δ}(x₁) (since 2cM(Z) ≤ 4cnη₀ω_n s^{n−1}, 4cnη₀ω_n ≤ 1 and ρ < s < δ). If n = 1: M(Z) ≤ 2η₀ω_1 < 1; Z is an IM 0-current and by (MR) its mass equals Σ_{x∈carrier} mult(x) (H⁰ is the counting measure), which is ≥ 1 unless the carrier is empty; so the carrier is empty, Z = 0, and S := 0 satisfies ∂S = Z, M(S) = 0 = κμ(B_ρ(x₁)) and spt S = ∅.
7. Covering. For fixed δ and x₁ ∈ K' let 𝓡_δ(x₁) be the set of radii ρ ∈ (0, δ) that arise as in step 3 for some s ∈ (ρ, δ) with F(s) < η₀ω_nsⁿ (and satisfy all the requirements of steps 3–6); applying step 3 with δ replaced by any δ'' ∈ (0, δ) shows that 𝓡_δ(x₁) contains arbitrarily small radii, so the closed balls B̄_ρ(x₁), ρ ∈ 𝓡_δ(x₁), form a fine family at every point of K'. By the Besicovitch–Vitali covering theorem (Mathlib Besicovitch.exists_disjoint_closedBall_covering_ae, for the locally finite measure μ) there are countably many pairwise disjoint balls B_i = B̄_{ρ_i}(x_i) of this family with μ(K' ∖ ⋃_i B_i) = 0; B_i ⊆ W since ρ_i < δ < ε₀. Let S_i be the fillings of step 6 and C_i(ω) := ∫_{B_i} ξ(ω) dμ = A_{ρ_i}(ω) (μ(∂B_{ρ_i}(x_i)) = 0). Then X_i := S_i − C_i has ∂X_i = Z_i − Z_i = 0, M(X_i) ≤ M(S_i) + μ(B_i) ≤ (1 + κ)μ(B_i), and spt X_i ⊆ B̄_{(1+3√P)δ}(x_i).
8. Comparison currents. Step 0 with ϱ := (1 + 3√P)δ gives |X_i(ω)| ≤ (1 + 3√P)δ(1 + κ)μ(B_i)‖dω‖_∞. The B_i are disjoint subsets of W, so Σ_iμ(B_i) ≤ μ(W) < ∞. For a Borel set E, C⌞E(ω) := ∫_E ξ(ω) dμ is a current (linear; |C⌞E(ω)| ≤ ‖ω‖_∞μ(tsupport ω) gives sequential continuity) with M_{W'}(C⌞E) ≤ μ(W' ∩ E) for open W'. The series ω ↦ Σ_iS_i(ω) converges absolutely (|S_i(ω)| ≤ κμ(B_i)‖ω‖_∞) and defines a current Σ_iS_i (the partial sums are uniformly bounded by κμ(W)‖ω‖_∞), with M(Σ_iS_i) ≤ Σ_iM(S_i) ≤ κμ(W). With E := ℝ^P ∖ ⋃_iB_i, countable additivity of the integral gives C = C⌞E + Σ_iC_i, hence C_δ := C⌞E + Σ_iS_i = C + Σ_iX_i and |C_δ(ω) − C(ω)| ≤ (1 + 3√P)δ(1 + κ)μ(W)‖dω‖_∞.
9. Lower semicontinuity. Along δ = δ_m ↓ 0 we get C_{δ_m} ⇀ C, so by SimonGMT WeaklyConvergesOn.massOn_le_liminf, μ(W) = M_W(C) ≤ liminf_m M_W(C_{δ_m}) ≤ liminf_m (μ(W ∖ ⋃_iB_i^{(m)}) + Σ_iM(S_i^{(m)})) ≤ μ(W ∖ K') + κ(η₀)μ(W), using μ(W ∖ ⋃_iB_i) ≤ μ(W ∖ K') + μ(K' ∖ ⋃_iB_i) = μ(W ∖ K') and Σ_iM(S_i) ≤ κΣ_iμ(B_i) ≤ κμ(W).
10. Since κ(η₀) ≤ 1/2 and μ(W) < ∞: μ(W) ≤ 2μ(W ∖ K'), i.e. μ(K') ≤ μ({dist(·, K') < ε₀} ∖ K'). As ε₀ ↓ 0 these sets decrease to ∅ (K' is closed) and have finite measure, so μ(K') = 0. Hence μ(A) = 0, i.e. ENNReal.ofReal η₀ ≤ Θ(x) for μ-a.e. x. ∎

## Key steps

1. Cone inequality: a finite-mass cycle supported in B̄_ϱ(x₀) satisfies |X(ω)| ≤ ϱM(X)‖dω‖_∞ (homotopy operator, (VO), (REP)).
2. The lower density is Borel; by inner regularity it suffices to show μ(K') = 0 for compact K' in the low-density set.
3. At x₁ ∈ K' choose radii ρ with F'(ρ) ≤ 2n(η₀ω_n)^{1/n}F(ρ)^{(n−1)/n}, μ(∂B_ρ) = 0 and IM slice Z = ∂(C⌞B_ρ(x₁)) with M(Z) ≤ F'(ρ) ((SL), ISP).
4. Fill Z by isoperimetric (n ≥ 2) with M(S) ≤ κ(η₀)μ(B_ρ(x₁)) and spt S ⊆ B̄_{(1+3√P)δ}(x₁); for n = 1, Z = 0 by (MR).
5. Besicovitch–Vitali gives disjoint balls covering μ-almost all of K'; the cone inequality shows C⌞(ℝ^P∖⋃B_i) + ΣS_i ⇀ C as δ ↓ 0.
6. Lower semicontinuity of M_W gives μ(W) ≤ μ(W∖K') + κμ(W) ≤ μ(W∖K') + μ(W)/2, hence μ(K') = 0.

## Reference use

### local-project

Queries:
- `cat RUN/local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; cmp GMT/Ch07/Submission.lean GMT/Ch07/Contract.lean; cmp SNAPSHOT/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean`
- `python3 scans of RUN/dag.json: selected node, frozen types and status of its five dependencies, lean_name matches for cbr_isoperimetric_filling (accepted, other parent) and for the prefix dmcbr_ (none among 937 nodes), byte comparison of the child types with the children of root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1`
- `grep -n '_existing_lean_name_problem|_accepted_checkpoint' /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `rg -c dmcbr SNAPSHOT (no match, exit 1); rg -n -i 'isoperimetric|closure theorem|FedererFleming|DeformationTheorem' SNAPSHOT/project/GMT -g '*.lean'`
- `rg -n -F over SNAPSHOT/mathlib/Mathlib, found: EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Isometry.euclideanHausdorffMeasure_image, MeasureTheory.Measure.euclideanHausdorffMeasure_smul₀, euclideanHausdorffMeasure_zero, euclideanHausdorffMeasure_zero_or_top, exists_disjoint_closedBall_covering_ae, ae_tendsto_average_norm_sub, tendsto_filterAt, tendstoUniformlyOn_of_ae_tendsto, lintegral_liminf_le, countable_meas_level_set_pos, measure_inter_add_sdiff, ext_of_generate_finite, isPiSystem_isOpen, MonotoneOn.intervalIntegral_deriv_mem_uIcc, MonotoneOn.intervalIntegrable_deriv, Monotone.ae_differentiableAt, measurable_deriv, rieszMeasure, LipschitzOnWith.extend_real, LipschitzOnWith.extend_pi, finite_approx_of_totallyBounded, hausdorffMeasure_zero_singleton, one_le_hausdorffMeasure_zero_of_nonempty, IsOpen.locallyCompactSpace, ext_of_forall_integral_eq_of_IsFiniteMeasure; not found as literal 'theorem X' headers but located as to_additive/namespace/alias/instance declarations: isAddLeftInvariant_eq_smul, AlternatingMap.map_linearDependent, MeasurableSet.exists_isClosed_diff_lt, Module.Finite.multilinearMap; no match: measure_inter_add_diff (the cited name is measure_inter_add_sdiff)`
- `rg -n over .lake/packages/simongmt/Poincare, all found: simon_theorem_4_16_compact_metrizable, simon_theorem_3_3, simon_theorem_3_26_i, exists_isClosed_continuousOn_of_measurable, simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure, realUnitBallVolume_nat_eq, measure_toOuterMeasure_isBorelRegular, exteriorDerivative_affinePullbackForm, GeometricCurrentOn.boundary_affinePushforward, WeaklyConvergesOn.massOn_le_liminf, WeaklyConvergesOn.boundary, GeometricCurrentOn.boundary_boundary, countablyRectifiable_of_measure_zero, countablyRectifiable_range, countablyRectifiable_iUnion, CountablyRectifiable.mono; sed on the massOn, support, restrictDomain, HasApproximateTangentSpaceAt and blowUpMap definitions`
- `lake env lean (v4.35.0-rc3) on /tmp/dimred_cbr2/lean/AllTypes.lean (12 types, sorry warnings only), /tmp/dimred_cbr2/lean/Assembly.lean (#print axioms: propext, Classical.choice, Quot.sound) and /tmp/dimred_cbr2/lean/InstCheck.lean; lean_contract.validate_lean_statement on all 12 types`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-4c4627e694/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-4c4627e694/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-ba6febc1b9/decomposition-audit-v1.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/Unique.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/HausdorffDensityBounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/CompactMetrizableCompactness.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/dimred_cbr2/lean/AllTypes.lean`
- `/tmp/dimred_cbr2/lean/Assembly.lean`
- `/tmp/dimred_cbr2/lean/InstCheck.lean`

Pins match (HEAD b4d606d = snapshot project commit, Mathlib 25730c7c, SimonGMT 2b366308), and Submission.lean is byte-identical to the frozen contract and to the snapshot copy. The snapshot has no dmcbr declaration and no proved closure, deformation or isoperimetric theorem; its Chapter 6 matches are contract definitions only. Every Mathlib and SimonGMT name cited by the child proofs exists in the pinned sources. The five dependency types in dag.json are unchanged since attempt 1. cbr_isoperimetric_filling is accepted but owned by another parent and was reported reserved, so it is not reused; dmcbr_isoperimetric_filling and the other dmcbr_ names match no DAG node. All 12 child types elaborate, and the sorry-free conditional assembly proves the exact parent type with axioms propext, Classical.choice, Quot.sound.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
