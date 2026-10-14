<!-- theorem-id: gmt-ch07/root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1 -->

## Theorem `Submission.cbr_cycle_isIntegerMultiplicity`

Assume (REP), (MR), (IMC), (SL), (DT) and (VO). Here (REP), (MR), (IMC), (SL), (DT), (VO) denote the exact frozen statements of the parent node's dependency theorems cmc_exists_massRepresentation, cmc_massOn_eq_imRep_measure, cmc_imRep_locality_restrict_sub, cmc_slice_mass_bounds, cmc_deformation_theorem and dtc_vanish_off_support; they are not available in this child's environment, so the needed ones appear verbatim as hypotheses of the Lean statement and are discharged by the parent proof. In words: (REP) a current with locally finite mass in an open U has a mass representation (μ, ξ) (μ(W) = M_W for open W, μ(ℝ^P∖U) = 0, μ finite on compacts of U, |ξ| ≤ 1, X(ω) = ∫ξ(ω)dμ, and μ(E) = 0 whenever Hⁿ(E) = 0 if also the boundary has locally finite mass); (MR) M_W(X) = R.measure(W) for an IMRep R of X and open W; (IMC) (a) locality of approximate tangent spaces for nested Borel sets, (b) the restriction of an IMRep to a Borel set is an IMRep of some current, (c) differences of IM currents are IM, (d) IMRep orientations satisfy |orient(x)(α)| ≤ |α| a.e.; (SL) slicing by an L-Lipschitz f of a current represented together with its boundary, with Z_t := ∂(X⌞{f<t}) − (∂X)⌞{f<t} vanishing on forms supported off {f = t}, M_W(Z_t) ≤ L liminf_h h⁻¹μ(W ∩ {t−h<f<t}) and the integrated bound; (DT) the deformation theorem with its mass and support bounds; (VO) a current vanishes on test forms whose support misses its support. Let d ∈ ℕ and assume CL(d) (CL(d) denotes: for all P, open U ⊆ ℝ^P and integer multiplicity T_j ∈ 𝒟_d(U) with sup_j (M_W(T_j) + boundaryMassOn(T_j, W)) < ∞ for every open W with compact closure in U, and T_j ⇀ T ∈ 𝒟_d(U), T is integer multiplicity; BR(d) denotes: for all P, open U and integer multiplicity R ∈ 𝒟_{d+1}(U) with M_W(∂R) < ∞ for every such W, ∂R is integer multiplicity.) A current Y ∈ 𝒟_{d+1}(ℝ^P) has the integer slice property (ISP) if for all admissible representations (μ, ξ) of Y and (μ', ξ') of ∂Y in ℝ^P (Borel measures finite on compact sets; a.e. strongly measurable fields of (d+1)- resp. d-vectors with |ξ(x)(α)| ≤ |α| a.e.; Y(ω) = ∫ξ(ω)dμ and ∂Y(η) = ∫ξ'(η)dμ' for all test forms) and every Lipschitz f : ℝ^P → ℝ, for L¹-a.e. t ∈ ℝ, every pair of currents A ∈ 𝒟_{d+1}(ℝ^P), B ∈ 𝒟_d(ℝ^P) with A(ω) = ∫_{f<t}ξ(ω)dμ and B(η) = ∫_{f<t}ξ'(η)dμ' for all test forms has ∂A − B integer multiplicity. If Γ ∈ 𝒟_{d+1}(ℝ^P) has ∂Γ = 0, M(Γ) < ∞, compact support and ISP, then Γ is integer multiplicity.

Node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4232

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4763, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4772, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4801, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4811, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4823

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5533, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5539, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5543, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5547, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5555, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5561, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5570, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5624, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5640, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5674, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5684, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5712

## Lean problem

Declaration: `Submission.cbr_cycle_isIntegerMultiplicity`

```lean
(∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) → (∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (L : NNReal), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (k + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) k, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ η : TestFormOn U k, T.boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') → LipschitzWith L f → ∃ (A : ℝ → GeometricCurrentOn U (k + 1)) (B : ℝ → GeometricCurrentOn U k), (∀ (t : ℝ) (ω : TestFormOn U (k + 1)), A t ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) ∧ (∀ (t : ℝ) (η : TestFormOn U k), B t η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') ∧ (∀ (t : ℝ) (η : TestFormOn U k), Disjoint (tsupport (η : DifferentialForm (Euclid P) k)) {x | f x = t} → (A t).boundary η = B t η) ∧ (∀ (W : Set (Euclid P)) (t : ℝ), IsOpen W → ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) ∧ (∀ (W : Set (Euclid P)) (a b : ℝ), IsOpen W → ∫⁻ t in Ioo a b, ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * μ (W ∩ {x | a < f x ∧ f x < b}))) → (∀ (P m : ℕ), ∃ c : NNReal, 1 ≤ c ∧ ∀ (ρ : ℝ) (K : Set (Euclid P)) (Λ : NNReal), 0 < ρ → IsCompact K → ∃ 𝒬 : Set (GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), 𝒬.Finite ∧ ∀ T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), IsIntegerMultiplicity T → T.support ⊆ K → T.mass ≤ Λ → T.boundary.mass < ∞ → ∃ Q ∈ 𝒬, ∃ (R : GeometricCurrentOn (univ : Set (Euclid P)) (m + 2)) (S : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), IsIntegerMultiplicity Q ∧ IsIntegerMultiplicity Q.boundary ∧ IsIntegerMultiplicity R ∧ T - Q - S = R.boundary ∧ (Q = 0 ∨ ENNReal.ofReal (ρ ^ (m + 1)) ≤ Q.mass) ∧ Q.mass ≤ c * T.mass ∧ Q.boundary.mass ≤ c * T.boundary.mass ∧ R.mass ≤ c * ENNReal.ofReal ρ * T.mass ∧ S.mass ≤ c * ENNReal.ofReal ρ * T.boundary.mass ∧ Q.support ∪ R.support ⊆ thickening (3 * Real.sqrt P * ρ) T.support ∧ Q.boundary.support ∪ S.support ⊆ thickening (3 * Real.sqrt P * ρ) T.boundary.support) → (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → ∀ d : ℕ, (∀ (P : ℕ) (U : Set (Euclid P)) (Ts : ℕ → GeometricCurrentOn U d) (T : GeometricCurrentOn U d), IsOpen U → (∀ j, IsIntegerMultiplicity (Ts j)) → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → ⨆ j, ((Ts j).massOn W + boundaryMassOn (Ts j) W) < ∞) → WeaklyConvergesOn Ts T → IsIntegerMultiplicity T) → ∀ (P : ℕ) (Γ : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)), Γ.boundary = 0 → Γ.mass < ∞ → IsCompact Γ.support → (∀ (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (d + 1)) (ξ' : Euclid P → MultiVector P d), (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (d + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) d, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), Γ ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, (Γ).boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → ∀ (f : Euclid P → ℝ) (L : NNReal), LipschitzWith L f → ∀ᵐ t ∂(volume : Measure ℝ), ∀ (A : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (B : GeometricCurrentOn (univ : Set (Euclid P)) d), (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), A ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, B η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → IsIntegerMultiplicity (A.boundary - B)) → IsIntegerMultiplicity Γ
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

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, V6–V12, V14, V15 (B. White's tangent-plane argument replacing Simon's Rectifiability Theorem 6.8.1, with integrality read off from slices), together with the parts of T5 (dilations) and V4(iii) (dilation invariance of the slice property) that this argument uses. The hypotheses (REP), (MR), (IMC), (SL), (DT), (VO) are the exact frozen statements of the parent node's dependency theorems (not available to this child, hence assumed) cmc_exists_massRepresentation, cmc_massOn_eq_imRep_measure, cmc_imRep_locality_restrict_sub, cmc_slice_mass_bounds, cmc_deformation_theorem, dtc_vanish_off_support; CL(d) is the closure statement in degree d. Siblings used: cbr_setIntegral_eq_of_integral_eq (restrict_unique), cbr_measure_convergence_tools ((T1), (T2), (MM)), cbr_slice_property_of_weak_limit (slice_limit), cbr_lower_density_of_slice_property (lower_density), cbr_rectifiable_of_approx_tangent (rectifiable). n := d + 1 ≥ 1, Hⁿ := μHE[n], ω_n := unitBallVolume n, ‖ω‖_∞ := sup|ω(x)|; for n-vectors |ζ| is the dual norm. ISP is the integer slice property of the statement. For a current X in ℝ^P with an admissible representation (μ, ξ) and a Borel set E, X⌞E(ω) := ∫_E ξ(ω) dμ defines a current (linear; |X⌞E(ω)| ≤ ‖ω‖_∞μ(tsupport ω) gives sequential continuity) with M_W(X⌞E) ≤ μ(W ∩ E); by restrict_unique it does not depend on the admissible representation. If n > P all n-currents vanish and Γ = 0 is IM (empty IMRep); the argument below also covers this case (then μ_Γ = 0 in step 3).

Step 1 (dilations, parent T5). For a ∈ ℝ^P and λ > 0 let η(y) := λ⁻¹(y − a) (an affine bijection, proper, inverse y ↦ a + λy) and, for X ∈ 𝒟_n(ℝ^P), η_#X := the affine push-forward of X (SimonGMT GeometricCurrentOn.affinePushforward with linear part λ⁻¹·id and translation −λ⁻¹a): η_#X(ω) = X(η^#ω), (η^#ω)(x) = λ^{−n}ω(η(x)) as n-covectors. (a) ∂η_#X = η_#∂X (SimonGMT GeometricCurrentOn.boundary_affinePushforward). (b) η^# maps the admissible forms for M_{η(W)} bijectively onto λ^{−n}·(admissible forms for M_W), so M_{η(W)}(η_#X) = λ^{−n}M_W(X). (c) If (μ, ξ) is an admissible representation of X, the change of variables x = η⁻¹(y) gives η_#X(ω) = ∫ ⟨λ^{−n}ω(η(x)), ξ(x)⟩ dμ(x) = ∫ ξ(η⁻¹y)(ω(y)) d(λ^{−n}η_*μ)(y); so (λ^{−n}η_*μ, ξ∘η⁻¹) is an admissible representation of η_#X, and it is the mass representation if μ(W) = M_W(X) for all open W (by (b)); for Lipschitz f and t ∈ ℝ, the change of variables also gives (η_#X)⌞{f < t} = η_#(X⌞{f∘η < t}) for these representations. (d) Hⁿ(η(A)) = λ^{−n}Hⁿ(A) (translation invariance and scaling of Hausdorff measure). If X = τ(M, θ, ξ) is IM, then η_#X is represented by (η(M), θ∘η⁻¹, ξ∘η⁻¹): by (d), ∫_M θ(x)⟨λ^{−n}ω(η x), ξ(x)⟩ dHⁿ(x) = ∫_{η(M)} θ(η⁻¹y)⟨ω(y), ξ(η⁻¹y)⟩ dHⁿ(y); η(M) is Borel and countably n-rectifiable (compose Lipschitz parametrizations with η; η maps Hⁿ-null sets to Hⁿ-null sets); θ∘η⁻¹ is Borel, positive and locally integrable on η(M); ξ∘η⁻¹ is a.e. strongly measurable; and since blowUpMap (η x) r (η y) = (λr)⁻¹(y − x) = blowUpMap x (λr) y, the approximate tangent space of η(M) at η(x) equals that of M at x. So η_# preserves integer multiplicity.

Step 2 (dilation invariance of ISP, parent V4(iii)). Let X ∈ 𝒟_n(ℝ^P) with ∂X = 0, locally finite mass and ISP, (μ_X, ξ_X) its (REP) representation, and η as in step 1; then X' := η_#X has ISP. Proof: ∂X' = 0 by step 1(a). Let (μ, ξ), (μ', ξ') be admissible representations of X', ∂X' and f L-Lipschitz; f∘η is (L/λ)-Lipschitz. ISP of X instantiated with (μ_X, ξ_X), (0, 0) (admissible for ∂X = 0) and f∘η gives a null set N such that ∂(X⌞{f∘η < t}) − 0 is IM for t ∉ N (X⌞{f∘η < t} is a current, see the preamble). For t ∉ N and A, B with A(ω) = ∫_{f<t} ξ(ω) dμ, B(η') = ∫_{f<t} ξ'(η') dμ': restrict_unique (U := ℝ^P) with the two admissible representations (μ, ξ) and (λ^{−n}η_*μ_X, ξ_X∘η⁻¹) of X' (and (0, 0)) gives A = (η_#X)⌞{f < t} = η_#(X⌞{f∘η < t}) (step 1(c)); restrict_unique with (μ', ξ') and (0, 0), both representing ∂X' = 0, gives B = 0. Hence ∂A − B = ∂η_#(X⌞{f∘η<t}) = η_#∂(X⌞{f∘η<t}) is IM by step 1(a), (d).

Step 3 (V6, representation of Γ). Γ has finite mass, so (REP) gives (μ_Γ, ξ_Γ): μ_Γ(W) = M_W(Γ) for open W, μ_Γ(ℝ^P) = M(Γ) < ∞, |ξ_Γ| ≤ 1, Γ(ω) = ∫ ξ_Γ(ω) dμ_Γ. Replacing ξ_Γ by a strongly measurable (Borel) function equal to it μ_Γ-a.e. and then by ζ ↦ ζ/max(1, |ζ|) of it (which changes it only on a μ_Γ-null set) we may assume ξ_Γ is Borel with |ξ_Γ(x)(α)| ≤ |α| everywhere; the representation and the mass identities are unaffected; since ∂Γ = 0, boundaryMassOn(Γ, W) = M_W(0) = 0, so the last clause of (REP) gives μ_Γ(E) = 0 whenever Hⁿ(E) = 0. Let η₀ > 0 be the constant of lower_density for (P, d). lower_density (C := Γ, μ := μ_Γ, ξ := ξ_Γ; ∂Γ = 0, ISP Γ) gives Θ(x) := liminf_{r↓0} μ_Γ(B_r(x))/(ω_nrⁿ) ≥ η₀ for μ_Γ-a.e. x; Θ is Borel: for fixed r > 0, x ↦ μ_Γ(B_r(x)) is lower semicontinuous (if x_m → x then 1_{B_r(x)} ≤ liminf_m 1_{B_r(x_m)} pointwise; Fatou), and r ↦ μ_Γ(B_r(x)) is left continuous (B_r(x) = ⋃_{s<r}B_s(x)), so Θ(x) = lim_m inf_{r ∈ ℚ∩(0,1/m)} μ_Γ(B_r(x))/(ω_nrⁿ) is a countable lim/inf of Borel functions. Let M₀ := {x ∈ spt Γ : Θ(x) ≥ η₀} (Borel). μ_Γ(ℝ^P ∖ spt Γ) = 0 (for open G disjoint from spt Γ, μ_Γ(G) = M_G(Γ) = 0 by (VO)), so μ_Γ(ℝ^P ∖ M₀) = 0. For x ∈ M₀ the upper density with closed balls satisfies limsup_r μ_Γ(B̄_r(x))/(ω_nrⁿ) ≥ Θ(x) ≥ η₀, so SimonGMT Chapter01 simon_theorem_3_3 (density comparison; Simon's Hⁿ equals μHE[n] by SimonGMT simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure) gives η₀Hⁿ(M₀) ≤ μ_Γ(ℝ^P) < ∞. Thus μ_Γ ≪ Hⁿ⌞M₀ (if Hⁿ(E ∩ M₀) = 0 then μ_Γ(E) ≤ μ_Γ(E ∩ M₀) + μ_Γ(ℝ^P ∖ M₀) = 0), and by Radon–Nikodym (Hⁿ⌞M₀ finite) μ_Γ = θHⁿ⌞M₀ with θ ≥ 0 Borel and ∫θ dHⁿ⌞M₀ = M(Γ). Put M' := M₀ ∩ {θ > 0} (Borel; μ_Γ(M₀ ∖ M') = 0) and τ := θξ_Γ (a.e. strongly measurable for Hⁿ⌞M'). Then Γ(ω) = ∫_{M'}⟨ω, τ⟩ dHⁿ. Moreover |ξ_Γ| = 1 μ_Γ-a.e.: for open G, μ_Γ(G) = M_G(Γ) = sup_ω ∫ ξ_Γ(ω) dμ_Γ ≤ ∫_G |ξ_Γ| dμ_Γ ≤ μ_Γ(G), so ∫_G (1 − |ξ_Γ|) dμ_Γ = 0 for every open G, hence (outer regularity of the finite measure (1 − |ξ_Γ|)μ_Γ) 1 − |ξ_Γ| = 0 μ_Γ-a.e. Hence |τ| = θ Hⁿ-a.e. on M'. If μ_Γ = 0 then Γ = 0 is IM and we are done; assume Hⁿ(M') > 0 in what follows (the steps below are pointwise statements at Hⁿ-a.e. a ∈ M').

Step 4 (V7, good points). For Hⁿ-a.e. a ∈ M': (i) limsup_{r↓0} Hⁿ(M' ∩ B̄_r(a))/(ω_nrⁿ) ≤ 1 (SimonGMT simon_theorem_3_26_i, Hⁿ(M') < ∞); (ii) a is a Lebesgue point of τ for Hⁿ⌞M' with closed balls: Hⁿ(M' ∩ B̄_r(a))⁻¹∫_{M'∩B̄_r(a)}|τ − τ(a)| dHⁿ → 0 (Mathlib VitaliFamily.ae_tendsto_average_norm_sub for the Besicovitch Vitali family of the finite measure Hⁿ⌞M', and Besicovitch.tendsto_filterAt to pass to radii r ↓ 0); (iii) Θ(a) ≥ η₀ and 0 < θ(a) = |τ(a)| < ∞. Fix such a; τ₀ := τ(a), θ₀ := θ(a). Since |θ − θ₀| ≤ |τ − τ₀| a.e. on M', μ_Γ(B_r(a)) ≤ θ₀Hⁿ(M' ∩ B_r(a)) + ∫_{M'∩B̄_r(a)}|τ − τ₀| dHⁿ = θ₀Hⁿ(M' ∩ B_r(a)) + o(rⁿ) (by (i), (ii)); with μ_Γ(B_r(a)) ≥ (η₀/2)ω_nrⁿ for small r (iii) we get Hⁿ(M' ∩ B_r(a)) ≥ (η₀/(4θ₀))ω_nrⁿ for all small r.

Step 5 (V8, blow-ups). Let λ_i > 0, λ_i → 0, η_i := η_{a,λ_i}, Γ_i := η_{i#}Γ and μ_i := Hⁿ⌞η_i(M'). By step 1(c),(d), Γ_i(ω) = ∫_{η_i(M')}⟨ω(y), τ(a + λ_iy)⟩ dHⁿ(y) and μ_i(B_R(0)) = λ_i^{−n}Hⁿ(M' ∩ B_{λ_iR}(a)); so for each R > 0 and all large i, (η₀/(4θ₀))ω_nRⁿ ≤ μ_i(B_R(0)) ≤ 2ω_nRⁿ (step 4), and sup_i μ_i(K) < ∞ for compact K. For ω with tsupport ω ⊆ B_R(0): |Γ_i(ω) − ∫⟨ω, τ₀⟩ dμ_i| ≤ ‖ω‖_∞λ_i^{−n}∫_{M'∩B̄_{λ_iR}(a)}|τ − τ₀| dHⁿ → 0 (step 4 (i), (ii)). By (T1) (U := ℝ^P) a subsequence (not relabeled) has μ_i → ν: ∫ g dμ_i → ∫ g dν for g ∈ C_c(ℝ^P), limsup μ_i(K) ≤ ν(K) for compact K, ν(G) ≤ liminf μ_i(G) for open G. Then Γ_i ⇀ C, where C(ω) := ∫⟨ω, τ₀⟩ dν (a current: |C(ω)| ≤ θ₀‖ω‖_∞ν(tsupport ω)). Properties: (α) ν(B_R(0)) ≤ liminf μ_i(B_R(0)) ≤ ω_nRⁿ for every R > 0 (step 4(i)). (β) ν(B̄_R(0)) ≥ limsup μ_i(B̄_R(0)) ≥ (η₀/(4θ₀))ω_nRⁿ > 0 for all R > 0, so 0 ∈ spt ν. (γ) ∂C = 0: ∂C(φ) = lim ∂Γ_i(φ) = 0 since ∂Γ_i = η_{i#}∂Γ = 0. (δ) For a locally finite measure ν' and a constant n-vector ζ₀, the current Ξ(ω) := ∫⟨ω, ζ₀⟩ dν' has M_G(Ξ) = |ζ₀|ν'(G) for open G (≤ since |⟨ω, ζ₀⟩| ≤ |ω||ζ₀|; ≥ by testing with φβ₀, β₀ a covector with |β₀| = 1 and ⟨β₀, ζ₀⟩ = |ζ₀|, φ ∈ C_c^∞(G; [0, 1]) increasing to 1_G). Hence M_G(C) = θ₀ν(G): (θ₀ν, τ₀/θ₀) is the mass representation of C (admissible, |τ₀/θ₀| = 1). Also, with Ξ_i(ω) := ∫⟨ω, τ₀⟩ dμ_i, |M_G(Γ_i) − θ₀μ_i(G)| ≤ M_G(Γ_i − Ξ_i) ≤ λ_i^{−n}∫_{M'∩η_i^{−1}(G)}|τ − τ₀| dHⁿ → 0 for bounded open G. Writing μ_{Γ_i} := λ_i^{−n}η_{i*}μ_Γ (the mass representation of Γ_i, step 1(c)), it follows that sup_i μ_{Γ_i}(B_R(0)) < ∞ for every R, limsup_i μ_{Γ_i}(K) ≤ θ₀ν(K) for compact K (take bounded open G ⊇ K: limsup μ_{Γ_i}(K) ≤ limsup θ₀μ_i(Ḡ) ≤ θ₀ν(Ḡ), and let G shrink to K), and θ₀ν(G) ≤ liminf_i μ_{Γ_i}(G) for bounded open G. (ε) By step 2 each Γ_i has ISP; the Γ_i satisfy sup_i (M_W(Γ_i) + M_W(∂Γ_i)) = sup_i μ_{Γ_i}(W) < ∞ for bounded open W and Γ_i ⇀ C; by slice_limit (with CL(d), (REP), (MR), (IMC), (SL)), C has ISP.

Step 6 (V9, invariance and simplicity). For an (n−1)-covector α define v_α ∈ ℝ^P by ⟨v_α, w⟩ := ⟨w^♭ ∧ α, τ₀⟩ (w^♭ := ⟨w, ·⟩; for n = 1, α is a scalar and v_α = ατ₀ under Λ_1 ≅ ℝ^P). For φ ∈ C_c^∞(ℝ^P): 0 = ∂C(φα) = C(dφ ∧ α) = ∫ Dφ·v_α dν. Applying this to φ(· + s v_α) gives (d/ds)∫φ(y + s v_α) dν(y) = 0 (differentiation under the integral, φ ∈ C_c^∞, ν locally finite), so ν is invariant under translations by multiples of v_α, hence by V₀ := span{v_α}. Let r := dim V₀ and choose an orthonormal basis e'_1, …, e'_P with V₀ = span(e'_1, …, e'_r). For an increasing multi-index I with |I| = n containing some i > r: ⟨e'^I, τ₀⟩ = ±⟨e'^i ∧ e'^{I∖i}, τ₀⟩ = ±⟨v_{e'^{I∖i}}, e'_i⟩ = 0. Hence τ₀ = Σ_{I⊆{1,…,r}}⟨e'^I, τ₀⟩e'_I, and τ₀ ≠ 0 forces r ≥ n. Growth: pick y₀ ∈ spt ν and m₀ := ν(B_1(y₀)) > 0; for large R the balls B_1(y₀ + v), v ∈ 2ℤ^r (coordinates w.r.t. e'_1, …, e'_r), |v| ≤ R/2, are pairwise disjoint, contained in B_R(0), at least c_rR^r in number and of ν-measure m₀ each (invariance); so c_rm₀R^r ≤ ν(B_R(0)) ≤ ω_nRⁿ (step 5(α)) for all large R, forcing r ≤ n. Hence dim V₀ = n, Λ_n(V₀) is one-dimensional, and τ₀ = θ₀ v_1 ∧ ⋯ ∧ v_n for a suitably oriented orthonormal basis (v_1, …, v_n) of V₀ (|τ₀| = θ₀ and the unit simple n-vector of V₀ has norm 1).

Step 7 (V10, structure of ν). Write ℝ^P = V₀ ⊕ V₀^⊥, y = v + w. For bounded Borel B ⊆ V₀^⊥, A ↦ ν(A + B) (A ⊆ V₀ Borel) is a translation-invariant, locally finite Borel measure on V₀ ≅ ℝⁿ, hence equals σ(B)·Hⁿ⌞V₀ (uniqueness of Haar measure, Mathlib MeasureTheory.Measure.isAddLeftInvariant_eq_smul; Hⁿ⌞V₀ is Lebesgue measure under an isometry); σ is a locally finite Borel measure on V₀^⊥ and ν = (Hⁿ⌞V₀) ⊗ σ (agreement on the π-system of products A + B). By lower_density applied to C with (μ, ξ) := (θ₀ν, τ₀/θ₀) (step 5(γ), (δ), (ε)), liminf_r θ₀ν(B_r(y))/(ω_nrⁿ) ≥ η₀ for ν-a.e. y. Since B_r(v + w) ⊆ (V₀ ∩ B_r(v)) + (V₀^⊥ ∩ B_r(w)), ν(B_r(y)) ≤ ω_nrⁿσ(B_r(w)), so σ({w}) = lim_{r↓0}σ(B_r(w)) ≥ η₀/θ₀ for all w outside a σ-null set (ν((V₀ ∩ B_1(0)) + G) = ω_nσ(G)). As σ is locally finite, the atoms of mass ≥ η₀/θ₀ form a locally finite set and carry σ: σ = Σ_iα_iδ_{w_i}, α_i ≥ η₀/θ₀, i.e. ν = Σ_iα_iHⁿ⌞(V₀ + w_i). Then ν(B_R(0)) = Σ_iα_iω_n(R² − |w_i|²)_+^{n/2} ≤ ω_nRⁿ; for each finite subfamily, dividing by ω_nRⁿ and letting R → ∞ gives Σα_i ≤ 1. So there are finitely many planes w_1, …, w_N, Σ_iα_i ≤ 1, and some w_i = 0 since 0 ∈ spt ν = ⋃_i(V₀ + w_i).

Step 8 (V11, each α_i ≥ 1). Fix i₀, α := α_{i₀}, w := w_{i₀}; index the blow-up sequence by k (Γ_k, μ_k, λ_k). With the orthonormal basis (v_1, …, v_n) of V₀ from step 6 let p : ℝ^P → ℝⁿ, p(x) := (⟨x, v_1⟩, …, ⟨x, v_n⟩) (in coordinates adapted to an orthonormal basis extending (v_i), V₀ = ℝⁿ × {0}, τ₀ = θ₀e_1 ∧ ⋯ ∧ e_n and p is the coordinate projection; the Euclidean coefficient norm of covectors is invariant under orthogonal changes of coordinates, which justifies |p^#γ| = |γ∘p| and |Σ_jH_jε_j| = |H| below); δ' := min_{j≠i₀}|w_j − w|/3 (δ' := 1 if N = 1); g := dist(·, V₀ + w) (1-Lipschitz); fix R > 0 and Ω := p^{−1}(B_{3R}). (a) A'' := Ω̄ ∩ {δ' ≤ g ≤ 2δ'} is compact and ν(A'') = 0 (no plane V₀ + w_j meets it: on V₀ + w_j, g = |w_j − w|, which is 0 for j = i₀ and ≥ 3δ' otherwise), so limsup_k μ_{Γ_k}(A'') ≤ θ₀ν(A'') = 0 (step 5(δ)). (SL) for Γ_k with its mass representation, (0, 0) for ∂Γ_k = 0, f := g, L := 1 gives Z_{k,t} := Γ_k⌞{g < t} with M_Ω(∂Z_{k,t}) ≤ liminf_h h⁻¹μ_{Γ_k}(Ω ∩ {t − h < g < t}). (MM) with μs k := μ_{Γ_k}, G := Ω, (a, b) := (δ', 2δ'), L := 1 (μ_{Γ_k}(Ω ∩ {δ' < g < 2δ'}) ≤ μ_{Γ_k}(A'') < ∞ and → 0) gives a measurable majorant with integral 0, so liminf_k M_Ω(∂Z_{k,t}) = 0 for a.e. t ∈ (δ', 2δ'). Fix such t and a subsequence with M_Ω(∂Z_k) → 0, Z_k := Z_{k,t}. As θ₀ν({g = t}) = 0 (no plane meets {g = t}), (T2) (Xs := Γ_k with mass representations, X := C with (θ₀ν, τ₀/θ₀), limit measure θ₀ν from step 5(δ)) gives Z_k ⇀ C⌞{g < t} = τ₀αHⁿ⌞(V₀ + w). (This covers N = 1 and n = P, where g ≡ 0 and A'' = ∅.) (b) Projection. For b ∈ C_c^∞(B_{2R}) (B_{2R} ⊆ ℝⁿ) let Y_k(b dy) := ∫_{g<t} b(p(x))⟨dy¹ ∧ ⋯ ∧ dyⁿ, ξ_{Γ_k}(x)⟩ dμ_{Γ_k}(x) (dyⁱ pulled back by p; absolutely convergent since μ_{Γ_k}(p^{−1}(spt b) ∩ {g ≤ t}) < ∞). Y_k ∈ 𝒟_n(B_{2R}) with M(Y_k) ≤ μ_{Γ_k}({g ≤ t} ∩ Ω) (bounded in k). For an (n−1)-form γ on B_{2R} choose χ ∈ C_c^∞(Ω) equal to 1 near {g ≤ t} ∩ p^{−1}(spt γ); then ∂Y_k(γ) = Z_k(χp^#dγ) = Z_k(d(χp^#γ)) − Z_k(dχ ∧ p^#γ) = ∂Z_k(χp^#γ) (VO: spt Z_k ⊆ {g ≤ t} and dχ ∧ p^#γ vanishes near {g ≤ t}), so M_{B_{2R}}(∂Y_k) ≤ M_Ω(∂Z_k) → 0 (|p^#γ| = |γ∘p|). Testing Z_k ⇀ τ₀αHⁿ⌞(V₀ + w) with χ(b∘p)p^#dy, χ ∈ C_c^∞(Ω) a fixed function equal to 1 on the compact set {g ≤ t} ∩ p^{−1}(B̄_{2R}), gives Y_k(b dy) → θ₀α∫b dy. (c) Density. By (REP) applied to Y_k in the open set B_{2R} ⊆ ℝⁿ (degree n, locally finite mass and boundary mass), μ_{Y_k} ≪ Hⁿ = Lⁿ, so Y_k(b dy) = ∫ b u_k dLⁿ with u_k ∈ L¹(B_{2R}) (Radon–Nikodym). The signed measure b ↦ Y_k(b dy) is the push-forward under p of ⟨dy, τ(a + λ_k·)⟩Hⁿ⌞(N_k ∩ Ω), N_k := η_k(M') ∩ {g < t} (step 5), so |u_k|Lⁿ vanishes on every Borel set disjoint from p(N_k ∩ Ω); hence u_k = 0 Lⁿ-a.e. outside E_k := toMeasurable(Lⁿ, p(N_k ∩ Ω)) (Lⁿ(B ∩ E_k) = Lⁿ(B ∩ p(N_k ∩ Ω)) for Borel B; no measurability of p(N_k ∩ Ω) is needed). (d) L¹ convergence. For 0 < s₀ < R and a mollifier φ_{s₀}: (u_k ∗ φ_{s₀})(x) = Y_k(φ_{s₀}(x − ·)dy) → θ₀α for x ∈ B̄_R, uniformly in x (equicontinuity: |Y_k(φ_{s₀}(x − ·)dy) − Y_k(φ_{s₀}(x' − ·)dy)| ≤ |x − x'|Lip(φ_{s₀})M(Y_k)). Further ∫_{B_R}|u_k − u_k ∗ φ_{s₀}| ≤ s₀M_{B_{2R}}(∂Y_k): for v := u_k ∗ φ_ϑ (0 < ϑ small), ∫_{B_R}|v(x) − v(x − z)| dx ≤ |z|∫_{B_{R+|z|}}|∇v| (fundamental theorem of calculus along segments), and ∫_{B_{R+s₀}}|∇v| ≤ M_{B_{2R}}(∂Y_k) because for every smooth compactly supported vector field G on B_{R+s₀} with |G| ≤ 1, ∫∇v·G = −∫u_k div(φ̌_ϑ ∗ G) = −Y_k(div(φ̌_ϑ ∗ G)dy) = −∂Y_k(Σ_j(φ̌_ϑ ∗ G)_jε_j) with |Σ_j(φ̌_ϑ ∗ G)_jε_j| ≤ 1, ε_j := (−1)^{j−1}dy¹∧⋯∧dy^{j−1}∧dy^{j+1}∧⋯∧dyⁿ; average over z against φ_{s₀}(z) and let ϑ ↓ 0 (v → u_k in L¹_loc). Hence ∫_{B_R}|u_k − θ₀α| ≤ s₀M_{B_{2R}}(∂Y_k) + ω_nRⁿsup_{B_R}|u_k ∗ φ_{s₀} − θ₀α|, so limsup_k ∫_{B_R}|u_k − θ₀α| ≤ 0 for each s₀, i.e. → 0. (e) Conclusion. Lⁿ(B_R ∖ E_k) ≤ (θ₀α)^{−1}∫_{B_R}|u_k − θ₀α| → 0. And Lⁿ(B_R ∩ E_k) = Lⁿ(B_R ∩ p(N_k ∩ Ω)) ≤ Hⁿ(N_k ∩ p^{−1}(B_R)) (p is 1-Lipschitz and Hⁿ = Lⁿ on ℝⁿ) ≤ μ_k(A'), A' := {g ≤ t} ∩ p^{−1}(B̄_R) compact, and limsup_k μ_k(A') ≤ ν(A') = αω_nRⁿ (only V₀ + w meets A' since t < 2δ' < 3δ'). Therefore ω_nRⁿ ≤ αω_nRⁿ, i.e. α_{i₀} ≥ 1.

Step 9 (V12, approximate tangent plane). By steps 7–8, 1 ≥ Σ_iα_i ≥ N, so N = 1, α_1 = 1, w_1 = 0 and ν = Hⁿ⌞V₀. V₀ is determined by τ₀ alone (step 6), so every sequence λ_i ↓ 0 has a subsequence with Hⁿ⌞η_{a,λ_i}(M') → Hⁿ⌞V₀ against C_c(ℝ^P); by the subsequence principle ∫_{blowUpMap a λ '' M'} f dHⁿ → ∫_{V₀} f dHⁿ as λ → 0⁺ for every f ∈ C_c(ℝ^P), and dim V₀ = n: HasApproximateTangentSpaceAt n M' a V₀. Moreover ξ_Γ(a) = τ₀/θ₀ = v_1 ∧ ⋯ ∧ v_n, i.e. ξ_Γ(a)(β) = β(v_1, …, v_n) for all n-covectors β: IsUnitOrientationOf ξ_Γ(a) V₀. This holds for Hⁿ-a.e. a ∈ M'. The map a ↦ p_{V₀(a)} is Borel on M': V₀(a) is the range of the linear map α ↦ v_α(a) (defined from τ(a) as in step 6), whose matrix entries are linear in τ(a) = θ(a)ξ_Γ(a) and hence Borel functions of a (θ and the chosen ξ_Γ are Borel, step 3); at good points this matrix has rank n; the map sending a matrix of rank n to the orthogonal projection onto its range (A ↦ AA⁺, Moore–Penrose pseudo-inverse) is continuous on the Borel set of rank-n matrices, and we set it to 0 on other matrices; the composite is Borel and agrees with a ↦ p_{V₀(a)} at Hⁿ-a.e. a ∈ M', so x ↦ p_{V₀(x)} is Hⁿ⌞M'-a.e. strongly measurable.

Step 10 (V14, integrality). At a as in step 9, C = θ₀[[V₀]], [[V₀]](ω) := ∫_{V₀}ω(v_1, …, v_n) dHⁿ, and C has ISP (step 5(ε)). Let f(y) := ⟨y, v_1⟩ (1-Lipschitz). For every t, by the divergence theorem in V₀ ≅ ℝⁿ on the half-space {f < t}: ∂(C⌞{f<t})(η) = ±θ₀∫_{L_t}η(v_2, …, v_n) dH^{n−1}, L_t := V₀ ∩ {f = t} (for n = 1: ±θ₀η(tv_1)). Instantiating ISP of C with (θ₀Hⁿ⌞V₀, τ₀/θ₀), (0, 0) and f: for a.e. t this (n−1)-current Z_t is IM; fix such t and an IMRep (M_t, θ', ξ') of Z_t. By (MR), M_G(Z_t) = ∫_{M_t∩G}θ' dH^{n−1} for open G; by the mass formula of step 5(δ), whose proof holds verbatim in every degree (here: the constant (n−1)-vector ±θ₀v_2∧⋯∧v_n of norm θ₀ and ν' := H^{n−1}⌞L_t; for n = 1 the 0-vector ±θ₀ and ν' := δ_{tv_1}), M_G(Z_t) = θ₀H^{n−1}(L_t ∩ G). Two locally finite Borel measures agreeing on open sets agree, so θ'1_{M_t}H^{n−1} = θ₀1_{L_t}H^{n−1}. Evaluating on Borel subsets of L_t ∩ B_1(tv_1) shows H^{n−1}((L_t ∩ B_1(tv_1)) ∖ M_t) = 0 and θ' = θ₀ H^{n−1}-a.e. on M_t ∩ L_t ∩ B_1(tv_1), a set of positive H^{n−1}-measure; θ' is integer-valued, so θ₀ ∈ ℤ (for n = 1, M_t = {tv_1} and θ₀ = θ'(tv_1)). Hence θ(a) is a positive integer for Hⁿ-a.e. a ∈ M'.

Step 11 (V15, conclusion). Let M'' ⊆ M' be a Borel set with Hⁿ(M' ∖ M'') = 0 such that every a ∈ M'' satisfies the conclusions of steps 9 and 10 (the exceptional sets are Hⁿ-null; take a Borel subset of full measure). Define mult(x) := θ(x) ∈ ℕ_{≥1} for x ∈ M'' and 0 otherwise (Borel), orient := ξ_Γ. Then (M'', mult, orient) is an IMRep in ℝ^P: M'' is Borel; it is countably n-rectifiable because M' is (rectifiable applied to M' with Q(x) := V₀(x): M' Borel, Hⁿ(M') < ∞, x ↦ p_{V₀(x)} Hⁿ⌞M'-a.e. strongly measurable and HasApproximateTangentSpaceAt n M' x V₀(x) for Hⁿ-a.e. x ∈ M', step 9) and M'' ⊆ M' (SimonGMT CountablyRectifiable.mono); mult > 0 on M''; ∫_{M''∩K} mult dHⁿ ≤ ∫θ dHⁿ⌞M' = M(Γ) < ∞; ξ_Γ is a.e. strongly measurable for Hⁿ⌞M'' (it is so for μ_Γ = θHⁿ⌞M', and θ > 0 on M'' gives Hⁿ⌞M'' ≪ μ_Γ); and for Hⁿ-a.e. a ∈ M'', HasApproximateTangentSpaceAt n M' a V₀(a) (step 9), hence by (IMC)(a) (M'' ⊆ M' Borel, Hⁿ(M') < ∞) HasApproximateTangentSpaceAt n M'' a V₀(a), and ξ_Γ(a) is a unit orientation of V₀(a) (step 9). It represents Γ: Γ(ω) = ∫_{M'}⟨ω, τ⟩ dHⁿ = ∫_{M''} θ ξ_Γ(ω) dHⁿ (step 3, Hⁿ(M' ∖ M'') = 0, τ = θξ_Γ). So Γ is integer multiplicity. ∎

## Key steps

1. Dilations push forward currents, representations and IMReps and preserve ISP for cycles (restrict_unique).
2. lower_density and (REP) give μ_Γ = θHⁿ⌞M' with Hⁿ(M') < ∞ and Γ(ω) = ∫_{M'}⟨ω, τ⟩dHⁿ, |τ| = θ.
3. At Hⁿ-a.e. a ∈ M' (density ≤ 1, Lebesgue point of τ, lower density ≥ η₀) the blow-ups converge (T1) to C = τ₀ν with C having ISP (slice_limit).
4. ∂C = 0 makes ν invariant along an n-plane V₀, τ₀ simple, and ν a finite sum of parallel planes with weights α_i ≥ η₀/θ₀ (lower_density, Haar uniqueness), Σα_i ≤ 1.
5. Each α_i ≥ 1 by slicing with dist(·, V₀ + w_i), projecting to V₀, (REP) absolute continuity and an L¹/BV estimate; so ν = Hⁿ⌞V₀ and M' has approximate tangent plane V₀(a).
6. Slices of C = θ₀[[V₀]] are IM, so θ(a) ∈ ℤ via (MR).
7. rectifiable gives countable rectifiability of M'; (IMC)(a) transfers tangent planes; assemble the IMRep of Γ.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); cmp of snapshot project/GMT/Ch07/Contract.lean with workspace GMT/Ch07/Contract.lean (identical); diff GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `grep -rn 'cbr_' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT (no match); python3 scan of dag.json lean_name values for prefix 'cbr' (none) and for the 12 proposed names (no collision among 518 names)`
- `grep -rn --include=*.lean in /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib for: 'theorem Monotone.ae_differentiableAt', 'theorem measurable_deriv', 'theorem MonotoneOn.intervalIntegrable_deriv', 'theorem MonotoneOn.intervalIntegral_deriv_mem_uIcc', 'theorem lintegral_liminf_le', 'exists_disjoint_closedBall_covering_ae', 'theorem ae_tendsto_average_norm_sub', 'theorem tendsto_filterAt', 'theorem tendstoUniformlyOn_of_ae_tendsto', 'theorem LipschitzOnWith.extend_pi', 'theorem LipschitzOnWith.extend_real', 'theorem ext_of_generate_finite', 'isAddLeftInvariant_eq_smul', 'def rieszMeasure', 'map_linearDependent', 'euclideanHausdorffMeasure_zero', 'theorem hausdorffMeasure_zero_singleton', 'measure_inter_add_diff', 'theorem countable_meas_level_set_pos'`
- `grep -rn --include=*.lean in /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT for: simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure, 'theorem simon_theorem_3_3', 'theorem simon_theorem_3_26_i', 'theorem exists_isClosed_continuousOn_of_measurable', 'theorem simon_theorem_4_16_compact_metrizable', 'theorem countablyRectifiable_of_measure_zero', 'theorem CountablyRectifiable.mono', 'theorem countablyRectifiable_iUnion', 'theorem WeaklyConvergesOn.massOn_le_liminf', 'theorem WeaklyConvergesOn.boundary ', 'theorem GeometricCurrentOn.boundary_affinePushforward', 'def dimensionalUpperDensity'; sed -n 1,160p Chapter03/Rectifiable.lean; reading Chapter06/{Currents,Mass,CurrentLocalEquality,AffineCurrentPushforward,Forms}.lean`
- `python3 scan of dag.json: frozen lean_statement of the parent's six dependencies (cmc_exists_massRepresentation, cmc_massOn_eq_imRep_measure, cmc_imRep_locality_restrict_sub, cmc_slice_mass_bounds, cmc_deformation_theorem, dtc_vanish_off_support) and their statuses; accepted statements containing IsIntegerMultiplicity, blowUp, affinePushforward, massOn/measure or HasApproximateTangentSpaceAt (e.g. dtc_restrictDomain_isIntegerMultiplicity, dtc_extend_by_zero, rsd_isIntegerMultiplicity_int_combination, dor_imrep_massOn_eq_measure_and_support, regcomp_approx_tangent_locality, dtc_blowUp_scaling); cross-branch depends_on edges`
- `grep -n 'def _existing_lean_name_problem' -A 40 and sed -n 1800,1960p /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py; sed -n 1,40p /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/speculation.py (prerequisites of a node = its children + depends_on)`
- `python3 -I scope.py: verifier/lean_contract.py validate_lean_statement on all 12 statements (pass) and verifier/gmt-compare.py contract_scope(Contract.lean, GMT.Ch07.main_theorem) (replay: open Filter Function Set MeasureTheory Metric; open scoped ENNReal Topology; namespace GMT.Ch07; open Poincare.SimonGMT.Chapter06; open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt); noncomputable section; end)`
- `lake env lean /tmp/cbr-decomp-7q2k/lean/Types.lean, Assembly.lean (#print axioms CbrCheck.assembly: propext, Classical.choice, Quot.sound), Coe.lean (pp.coercions), Types3.lean (12 types + parent wiring + slice_limit→cycle_im/lower_density wiring), Final.lean (exact final lean_statements, exit 0)`
- `sed -n 2297,2473p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt (Simon Ch. 6, 8.2–8.3 closure theorem)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Egorov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/Unique.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/CompactMetrizableCompactness.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/HausdorffDensityBounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLiteral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-ba6febc1b9/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/speculation.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/cbr-decomp-7q2k/lean/Types3.lean`
- `/tmp/cbr-decomp-7q2k/lean/Assembly.lean`
- `/tmp/cbr-decomp-7q2k/lean/Final.lean`

The snapshot contract is byte-identical to the workspace Contract.lean and Submission.lean; no 'cbr_' declaration exists in the snapshot project or the DAG, and the 12 proposed bare names collide with none of the 518 frozen DAG names. Every Mathlib lemma cited in the child proofs exists in the snapshot (measure_inter_add_diff is now a deprecated alias of measure_inter_add_sdiff, which the proofs cite) and every cited SimonGMT declaration exists in the pinned package; SimonGMT Chapter03 has the definitions of CountablyRectifiable and HasApproximateTangentSpaceAt but no rectifiability criterion (Simon 3.1.6), and Chapter06 has no slicing, deformation or closure theorem, which justifies the split. The runtime gives a child only its own depends_on and children as prerequisites, and five of the parent's six dependencies are unaccepted and owned by another parent, so the children take the exact frozen statements of those dependencies as hypotheses. All 12 exact propositions pass the verifier's lexical check and elaborate in the replayed contract scope; a hypothesis-only assembly proves the frozen parent type from closure_zero, boundary_im, closure_succ and the six dependency types with axioms propext, Classical.choice, Quot.sound only.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
