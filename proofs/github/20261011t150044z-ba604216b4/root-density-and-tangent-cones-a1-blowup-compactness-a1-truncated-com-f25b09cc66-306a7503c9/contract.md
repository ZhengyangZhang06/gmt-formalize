<!-- theorem-id: gmt-ch07/root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1.cycle_im-a1 -->

## Theorem `Submission.dtc_bc_tc_cl_cycle_isIntegerMultiplicity`

Assume (MR), (IMC), (VO) (types of the accepted cmc_massOn_eq_imRep_measure, cmc_imRep_locality_restrict_sub, dtc_vanish_off_support). Let P, d ∈ ℕ with d + 1 < P, n := d + 1, and let ISP be the integer slice property of sibling slice_limit. Assume SLIM_{P,d} (weak limits X of ISP currents X_i ∈ 𝒟_n(ℝ^P) with sup_i(M_W(X_i) + M_W(∂X_i)) < ∞ for bounded open W have ISP) and LD_{P,d} (there is η₀ > 0 such that for every ISP cycle C ∈ 𝒟_n(ℝ^P) and every representation (μ, ξ) of C with μ finite on compacts, μ(W) = M_W(C) for open W and |ξ(x)(α)| ≤ |α| μ-a.e., liminf_{r↓0} μ(B_r(x))/(ω_nrⁿ) ≥ η₀ for μ-a.e. x). Then CYC_{P,d}: every Γ ∈ 𝒟_n(ℝ^P) with ∂Γ = 0, M(Γ) < ∞, compact support and ISP(Γ) is IM.

Node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1.cycle_im-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6629

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4200, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4763, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8057, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8063

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5555, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5712, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5547, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8581, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6179, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6200, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6217, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8582, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5624, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5640, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5674, https://github.com/ZhengyangZhang06/gmt-formalize/issues/8589

## Lean problem

Declaration: `Submission.dtc_bc_tc_cl_cycle_isIntegerMultiplicity`

```lean
(∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) → (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → ∀ (P d : ℕ), d + 1 < P → (∀ (Xs : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (X : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)), (∀ i, (∀ (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (d + 1)) (ξ' : Euclid P → MultiVector P d), (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (d + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) d, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), Xs i ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, (Xs i).boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → ∀ (f : Euclid P → ℝ) (L : NNReal), LipschitzWith L f → ∀ᵐ t ∂(volume : Measure ℝ), ∀ (A : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (B : GeometricCurrentOn (univ : Set (Euclid P)) d), (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), A ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, B η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → IsIntegerMultiplicity (A.boundary - B))) → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W univ → ⨆ i, ((Xs i).massOn W + (Xs i).boundary.massOn W) < ∞) → WeaklyConvergesOn Xs X → (∀ (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (d + 1)) (ξ' : Euclid P → MultiVector P d), (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (d + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) d, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), X ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, (X).boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → ∀ (f : Euclid P → ℝ) (L : NNReal), LipschitzWith L f → ∀ᵐ t ∂(volume : Measure ℝ), ∀ (A : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (B : GeometricCurrentOn (univ : Set (Euclid P)) d), (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), A ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, B η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → IsIntegerMultiplicity (A.boundary - B))) → (∃ η₀ : ℝ, 0 < η₀ ∧ ∀ (C : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (d + 1)), C.boundary = 0 → (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → (∀ W : Set (Euclid P), IsOpen W → C.massOn W = μ W) → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (d + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), C ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (d + 1)) (ξ' : Euclid P → MultiVector P d), (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (d + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) d, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), C ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, (C).boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → ∀ (f : Euclid P → ℝ) (L : NNReal), LipschitzWith L f → ∀ᵐ t ∂(volume : Measure ℝ), ∀ (A : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (B : GeometricCurrentOn (univ : Set (Euclid P)) d), (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), A ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, B η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → IsIntegerMultiplicity (A.boundary - B)) → ∀ᵐ x ∂μ, ENNReal.ofReal η₀ ≤ liminf (fun r : ℝ => μ (ball x r) / (unitBallVolume (d + 1) * ENNReal.ofReal (r ^ (d + 1)))) (𝓝[>] 0)) → (∀ (Γ : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)), Γ.boundary = 0 → Γ.mass < ∞ → IsCompact Γ.support → (∀ (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (d + 1)) (ξ' : Euclid P → MultiVector P d), (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (d + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) d, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), Γ ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, (Γ).boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → ∀ (f : Euclid P → ℝ) (L : NNReal), LipschitzWith L f → ∀ᵐ t ∂(volume : Measure ℝ), ∀ (A : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (B : GeometricCurrentOn (univ : Set (Euclid P)) d), (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), A ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, B η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → IsIntegerMultiplicity (A.boundary - B)) → IsIntegerMultiplicity Γ)
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

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1.cycle_im-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent V6–V15 together with T5 and V4(iii) (B. White's tangent-plane argument, Comment. Math. Helv. 64 (1989) 207–220, replacing Simon's Rectifiability Theorem 6.8.1; integrality is read off from slices as in parent V14). Version 2 of this proof makes the three required repairs: (1) Step 8 is parent V11(a)–(e) with its localized construction: R is fixed, Ω := p⁻¹(B_{3R}), the level t is selected with the compact annulus A'' ⊆ Ω̄, only M_Ω(∂Z_k) → 0 is proved and used, the projected currents Y_k live on B_{2R} with M_{B_{2R}}(∂Y_k) ≤ M_Ω(∂Z_k); no global mass of ∂(Γ_k⌞{g < t}) is claimed (it need not tend to 0: for blow-ups of a circle the restriction to a tangent strip has two boundary points); (2) Step 8 contains the measurable hull E_k of the projected carrier, the proof that the projected densities u_k vanish off E_k, the mollifier/BV estimate and the volume comparison giving α_i ≥ 1; (3) the sharp density comparison and the normalization of Hⁿ used in Steps 3–4 are proved in Step 0(d)–(f): the isodiametric normalization μHE[n] ≤ (ω_n/2ⁿ)μH[n] and the Vitali covering with the finite-tail argument of Simon 1.3.5, which removes the enlargement factor 5ⁿ, so Θ^{*n}(Hⁿ⌞M, a) ≤ 1 for Hⁿ-a.e. a ∈ M.
Tools. (SL) = sibling slicing, (RU) = sibling restrict_unique, (REP), (T1), (T2), (MM) = the first two conjuncts of sibling foundations, (RECT) = sibling rectifiable; hypotheses of this statement: (MR), (IMC), (VO), SLIM_{P,d}, LD_{P,d}. Reuse note (not a proof step): the general facts established in Step 0(b), Step 0(d), Step 1, Step 2, Step 3, Steps 6–7, Step 10 and Step 11 are exactly the statements of the comparator-accepted declarations cbr_ci_const_vector_massOn, cbr_ci_euclideanHausdorff_le_isodiametric, cbr_ci_dilation_calculus, cbr_ci_dilation_slice_property, cbr_ci_density_representation, cbr_ci_constant_cycle_planes, cbr_ci_plane_multiplicity_nat and cbr_ci_isIntegerMultiplicity_of_ae_tangent, whose hypotheses (SL), (RU), (MR), (RECT) are character-for-character the frozen types of slicing, restrict_unique, (MR) and rectifiable; a decomposition of this node may reuse them with their identical frozen types. The arguments are nevertheless given in full below.
Notation. n := d + 1, so 1 ≤ n < P. Hⁿ := μHE[n]; Lⁿ := volume on ℝⁿ = Euclid n, and Hⁿ = Lⁿ on ℝⁿ (Mathlib EuclideanSpace.euclideanHausdorffMeasure_eq_volume); ω_k := unitBallVolume k = Lᵏ(B_1); B_r(x), B̄_r(x) open and closed balls, B_r := B_r(0). |α| := covectorEuclideanNorm α; for an m-vector ζ (MultiVector P m), |ζ|* := sup{ζ(β) : |β| ≤ 1} (dual norm, attained since the unit ball of |·| is compact) and ‖ζ‖ is its operator norm; ‖ω‖_∞ := sup_x|ω(x)|. An admissible representation of X ∈ 𝒟_k(ℝ^P) is a pair (μ, ξ) with μ a Borel measure finite on compact sets, ξ μ-a.e. strongly measurable, |ξ(x)(α)| ≤ |α| for μ-a.e. x and all α, and X(ω) = ∫ξ(x)(ω(x))dμ(x) for every test form ω. ISP is the integer slice property of the statement. Currents are added as X + Y := X − (0 − Y).
Step 0 (Preliminaries).
(a) Coefficient norms. (O) For every orthonormal basis f = (f_1, …, f_P) of ℝ^P and every k-covector α, Σ_{j : Fin k → Fin P}α(f_{j(1)}, …, f_{j(k)})² = k!|α|². Proof: write f_i = Σ_l O_{li}e_l with O orthogonal and expand α(f_{j(1)}, …, f_{j(k)}) = Σ_{l}O_{l_1j(1)}⋯O_{l_kj(k)}α(e_{l_1}, …, e_{l_k}); summing the squares over j and using Σ_iO_{li}O_{l'i} = δ_{ll'} gives Σ_{l : Fin k → Fin P}α(e_l)²; non-injective l contribute 0 and each increasing multi-index I contributes k! equal terms α(e_I)² (alternation). Consequences: (O1) if v = (v_1, …, v_k) is orthonormal then |α(v)| ≤ |α| (extend v to an orthonormal basis; the k! permutations of (1, …, k) already contribute k!α(v)²); (O2) β_v(u) := det(⟨u_i, v_j⟩)_{i,j} is a k-covector with β_v(v) = 1 and |β_v| = 1 (in a basis extending v its only non-zero values are ±1 on the permutations of (v_1, …, v_k)); (O3) if v = (v_1, …, v_n) is orthonormal in ℝ^P and p(x) := (⟨x, v_1⟩, …, ⟨x, v_n⟩) ∈ ℝⁿ, then the pulled-back covector p^#γ := γ∘(p × ⋯ × p) of an l-covector γ on ℝⁿ satisfies |p^#γ| = |γ| (in an orthonormal basis f of ℝ^P extending v, p(f_i) = e_i for i ≤ n and p(f_i) = 0 for i > n, so the sums in (O) for p^#γ and γ coincide); (F1) ‖α‖_op ≤ Pᵏ|α| (expand unit vectors u_l = Σ_iu_l^ie_i with |u_l^i| ≤ 1; each |α(e_J)| ≤ |α|), hence |ζ|* ≤ Pᵏ‖ζ‖ and |ζ(α)| ≤ |ζ|*|α| for k-vectors ζ; |ζ|* ≤ 1 iff |ζ(α)| ≤ |α| for all α.
(b) Mass of a constant-vector current (accepted cbr_ci_const_vector_massOn). Let ν' be a Borel measure on ℝ^P finite on compact sets, ζ' an m-vector and s ≥ 0 with |ζ'(α)| ≤ s|α| for all α and ζ'(β₀) = s for some |β₀| ≤ 1, and Ξ ∈ 𝒟_m(ℝ^P) with Ξ(ω) = ∫ζ'(ω(x))dν'(x). Then M_W(Ξ) = s·ν'(W) for every open W. Proof: for ω admissible for M_W (tsupport ω ⊆ W, |ω| ≤ 1), Ξ(ω) ≤ ∫_W s|ω|dν' ≤ sν'(W). Conversely take φ_j ∈ C_c^∞(W; [0, 1]) increasing to 1_W (smooth cut-offs equal to 1 on an exhaustion of W by compact sets); φ_jβ₀ is admissible and Ξ(φ_jβ₀) = s∫φ_jdν' → sν'(W) by monotone convergence.
(c) Measures and test functions. If O ⊆ ℝᵏ is open and σ₁, σ₂ are finite Borel measures on ℝᵏ with σ_i(ℝᵏ ∖ O) = 0 and ∫b dσ₁ = ∫b dσ₂ for every b ∈ C_c^∞(O), then σ₁ = σ₂: for open G ⊆ O take b_j ∈ C_c^∞(G; [0, 1]) increasing to 1_G, so σ₁(G) = σ₂(G) by monotone convergence; for an arbitrary open G ⊆ ℝᵏ, σ_i(G) = σ_i(G ∩ O), so σ₁ and σ₂ agree on all open subsets of ℝᵏ, which form a π-system generating the Borel σ-algebra, and σ₁(ℝᵏ) = σ₂(ℝᵏ) < ∞ (Measure.ext_of_generate_finite). Likewise two Borel measures on ℝ^P that are finite on bounded sets and agree on open sets are equal (open sets form a generating π-system and the balls B_m exhaust ℝ^P with finite measure).
(d) Normalization of Hⁿ (accepted cbr_ci_euclideanHausdorff_le_isodiametric, frozen type ∀ (P n : ℕ), (μHE[n] : Measure (Euclid P)) ≤ (unitBallVolume n / 2 ^ n) • (μH[(n : ℝ)] : Measure (Euclid P)); Simon Ch. 1, 2.9–2.10; also SimonGMT simon_theorem_2_10, outside the contract's import closure). Claim: Hⁿ(S) ≤ (ω_n/2ⁿ)μH[n](S) for every S ⊆ ℝ^P, where μH[n](S) = sup_{δ>0}inf{Σ_jdiam(C_j)ⁿ : S ⊆ ⋃_jC_j, diam C_j ≤ δ} is Mathlib's unnormalized Hausdorff measure. Proof: by definition μHE[n] = c_n•μH[n] on every metric space, where c_n := addHaarScalarFactor(Lⁿ, μH[n]) satisfies Lⁿ = c_n•μH[n] on ℝⁿ (euclideanHausdorffMeasure_def, EuclideanSpace.euclideanHausdorffMeasure_eq_volume). Isodiametric inequality: Lⁿ(A) ≤ ω_n(diam A/2)ⁿ for every A ⊆ ℝⁿ. Indeed, it suffices to treat compact non-empty A (pass to the closure, which has the same diameter; the cases diam A = ∞ and A = ∅ are trivial). For j ≤ n let S_j(A) := {ξ + te_j : ξ ⊥ e_j, A_ξ ≠ ∅, |t| ≤ L¹(A_ξ)/2}, A_ξ := {t : ξ + te_j ∈ A} (Steiner symmetrization). ξ ↦ L¹(A_ξ) is upper semicontinuous (given ξ_i → ξ and an open U ⊇ A_ξ with L¹(U) ≤ L¹(A_ξ) + ε, compactness of A gives A_{ξ_i} ⊆ U for large i, since otherwise points ξ_i + t_ie_j ∈ A with t_i ∉ U would have a limit ξ + te_j ∈ A with t ∉ U), so S_j(A) is compact; Tonelli gives Lⁿ(S_j(A)) = Lⁿ(A); for x = ξ + se_j, y = η + te_j ∈ S_j(A), with a_ξ := min A_ξ, b_ξ := max A_ξ, |s − t| ≤ (L¹(A_ξ) + L¹(A_η))/2 ≤ max(b_η − a_ξ, b_ξ − a_η), so |x − y| is at most the distance between two points of A and diam S_j(A) ≤ diam A; S_j(A) is symmetric in {x_j = 0}, and S_j preserves symmetry in {x_i = 0} for i ≠ j. Hence Ã := S_n(⋯S_1(A)⋯) is compact, Lⁿ(Ã) = Lⁿ(A), diam Ã ≤ diam A and Ã = −Ã, so 2|x| ≤ diam Ã for x ∈ Ã, Ã ⊆ B̄_{diam A/2}(0) and Lⁿ(A) ≤ ω_n(diam A/2)ⁿ. Now for any countable cover (C_j) of a set A ⊆ ℝⁿ, Lⁿ(A) ≤ Σ_jLⁿ(C_j) ≤ (ω_n/2ⁿ)Σ_jdiam(C_j)ⁿ, so Lⁿ ≤ (ω_n/2ⁿ)μH[n] on ℝⁿ. For the unit cube K, 0 < μH[n](K) < ∞ (μH[n] is an additive Haar measure on ℝⁿ) and c_nμH[n](K) = Lⁿ(K) ≤ (ω_n/2ⁿ)μH[n](K), so c_n ≤ ω_n/2ⁿ and Hⁿ(S) = c_nμH[n](S) ≤ (ω_n/2ⁿ)μH[n](S) for every S ⊆ ℝ^P.
(e) Sharp density comparison (Simon Ch. 1, 3.3 with the finite-tail argument 3.5). Let ν₀ be a finite Borel measure on ℝ^P, A ⊆ ℝ^P and t₀ ∈ (0, ∞) with limsup_{ρ↓0}ν₀(B̄_ρ(x))/(ω_nρⁿ) > t₀ for every x ∈ A. Then t₀Hⁿ(A) ≤ ν₀(ℝ^P). Proof: fix δ > 0 and let 𝓑 be the family of closed balls B̄_ρ(x), indexed by the pairs (x, ρ) with x ∈ A, 0 < ρ < δ and ν₀(B̄_ρ(x)) ≥ t₀ω_nρⁿ; every x ∈ A is the centre of balls of 𝓑 with arbitrarily small radii. By the Vitali covering lemma in the form 'meets a larger chosen ball' (Mathlib Vitali.exists_disjoint_subfamily_covering_enlargement with index set the pairs (x, ρ) above, B(x, ρ) := B̄_ρ(x), δ(x, ρ) := ρ, τ := 2, R := δ) there is a pairwise disjoint subfamily 𝓑' ⊆ 𝓑 such that every B ∈ 𝓑 meets some B' ∈ 𝓑' with radius(B) ≤ 2·radius(B'); then B ⊆ B̂' := the concentric closed ball with 5 times the radius of B'. 𝓑' is countable, because its members are disjoint and each has ν₀-measure ≥ t₀ω_nρⁿ > 0 while ν₀ is finite; enumerate 𝓑' = {B_j = B̄_{ρ_j}(x_j)}. Then Σ_jω_nρ_jⁿ ≤ t₀⁻¹Σ_jν₀(B_j) ≤ t₀⁻¹ν₀(ℝ^P) < ∞. Finite tail: for every N, A ⊆ B_1 ∪ ⋯ ∪ B_N ∪ ⋃_{j>N}B̂_j. Indeed, let x ∈ A ∖ (B_1 ∪ ⋯ ∪ B_N); this finite union of closed balls is closed, so some B ∈ 𝓑 centred at x is disjoint from B_1, …, B_N; B meets some B_j ∈ 𝓑' with radius(B) ≤ 2ρ_j, necessarily with j > N, and x ∈ B ⊆ B̂_j. These covers consist of sets of diameter ≤ 10δ, and Σ_{j≤N}(2ρ_j)ⁿ + Σ_{j>N}(10ρ_j)ⁿ = (2ⁿ/ω_n)[Σ_{j≤N}ω_nρ_jⁿ + 5ⁿΣ_{j>N}ω_nρ_jⁿ] ≤ (2ⁿ/ω_n)[t₀⁻¹ν₀(ℝ^P) + 5ⁿΣ_{j>N}ω_nρ_jⁿ]. The tail of a convergent series tends to 0, so letting N → ∞ the infimum over covers of A by sets of diameter ≤ 10δ of Σdiamⁿ is at most (2ⁿ/ω_n)t₀⁻¹ν₀(ℝ^P); this holds for every δ > 0, so (Mathlib Measure.hausdorffMeasure_le_liminf_tsum along δ = 1/m, or Measure.hausdorffMeasure_apply) μH[n](A) ≤ (2ⁿ/ω_n)t₀⁻¹ν₀(ℝ^P). By (d), Hⁿ(A) ≤ (ω_n/2ⁿ)μH[n](A) ≤ t₀⁻¹ν₀(ℝ^P). No enlargement factor survives, because the enlarged balls only cover the tail.
(f) Upper density ≤ 1 (Simon Ch. 1, 3.26(1)). Let M ⊆ ℝ^P be Borel with Hⁿ(M) < ∞ and Θ*(x) := limsup_{ρ↓0}Hⁿ(M ∩ B̄_ρ(x))/(ω_nρⁿ). Then Θ*(x) ≤ 1 for Hⁿ-a.e. x ∈ M. Proof: for 1 < t < ∞ let A_t := {x ∈ M : Θ*(x) > t}, a := Hⁿ(A_t) ≤ Hⁿ(M) < ∞. Given ε > 0, the finite Borel measure Hⁿ⌞M on the metric space ℝ^P is outer regular (Set.exists_isOpen_lt_of_lt), so there is an open U ⊇ A_t with Hⁿ(M ∩ U) < a + ε. For x ∈ A_t, B̄_ρ(x) ⊆ U for small ρ, so the upper density of ν₀ := Hⁿ⌞(M ∩ U) at x equals Θ*(x) > t. By (e) with ν₀, A := A_t, t₀ := t: t·a ≤ Hⁿ(M ∩ U) < a + ε. Hence t·a ≤ a, and as a < ∞ and t > 1, a = 0. Since {x ∈ M : Θ*(x) > 1} = ⋃_k A_{1+1/(k+1)}, it is Hⁿ-null.
(g) Restricted currents. If (μ, ξ) is an admissible representation of X ∈ 𝒟_k(ℝ^P) and E is Borel, X⌞E(ω) := ∫_Eξ(ω)dμ is a current (linear; |X⌞E(ω)| ≤ ‖ω‖_∞μ(tsupport ω), so test forms converging in 𝒟ᵏ, which have supports in a fixed compact set and converge uniformly, are mapped to a convergent sequence), M_W(X⌞E) ≤ μ(W ∩ E), and by (RU) X⌞E does not depend on the admissible representation.
Step 1 (Dilations; parent T5; accepted cbr_ci_dilation_calculus). For a ∈ ℝ^P and λ > 0 let η(y) := dilation a λ y = λ⁻¹(y − a) = blowUpMap a λ y, an affine homeomorphism with inverse y ↦ a + λy. For X ∈ 𝒟_m(ℝ^P), a dilation of X is an X' ∈ 𝒟_m(ℝ^P) with X'(ω) = λ^{−m}X(ω∘η) for all test m-forms ω, where (ω∘η)(y) := ω(η(y)) as m-covectors. (1) Every X has a dilation: the proper affine push-forward η_#X (SimonGMT GeometricCurrentOn.affinePushforward, as in the contract's blowUp), since the pull-back of ω by η is λ^{−m}(ω∘η) (the linear part of η is λ⁻¹·id). (2) If X' is a dilation of X ∈ 𝒟_{m+1}(ℝ^P), then ∂X' is a dilation of ∂X: d(φ∘η) = λ⁻¹(dφ)∘η (chain rule), so ∂X'(φ) = X'(dφ) = λ^{−m−1}X((dφ)∘η) = λ^{−m}X(d(φ∘η)) = λ^{−m}∂X(φ∘η). (3) Dilations of IM currents are IM: if X = τ(M, θ, ξ), then X' = τ(η(M), θ∘η⁻¹, ξ∘η⁻¹), because Hᵐ(η(A)) = λ^{−m}Hᵐ(A) (translation invariance and homogeneity of Hausdorff measure) gives λ^{−m}∫_Mθξ(ω∘η)dHᵐ = ∫_{η(M)}(θ∘η⁻¹)(ξ∘η⁻¹)(ω)dHᵐ; η(M) is Borel and countably m-rectifiable (compose the Lipschitz parametrizations with η; η maps Hᵐ-null sets to null sets); θ∘η⁻¹ is Borel, ≥ 1 on η(M) and locally integrable; ξ∘η⁻¹ is a.e. strongly measurable; and blowUpMap (η x) r '' η(M) = blowUpMap x (λr) '' M (since r⁻¹(η y − η x) = (λr)⁻¹(y − x)), so η(M) has approximate tangent space Q at η(x) iff M has it at x, with the same orientation. (4) If X(ω) = ∫ξ(ω)dμ for all ω, then X'(ω) = ∫ξ(a + λy)(ω(y))d(λ^{−m}η_*μ)(y) (change of variables). (5) M_{η(W)}(X') = λ^{−m}M_W(X) for every W (ω ↦ ω∘η is a bijection between the test forms admissible for M_{η(W)} and those admissible for M_W). (6) Hᵐ(η(A)) = λ^{−m}Hᵐ(A).
Step 2 (ISP under dilations; parent V4(iii); accepted cbr_ci_dilation_slice_property). Let X ∈ 𝒟_n(ℝ^P) with ∂X = 0, an admissible representation (μ_X, ξ_X) and ISP, and X' a dilation by η = dilation a λ. Then ∂X' = 0 (Step 1(2)) and X' has ISP. Proof: let (μ, ξ), (μ', ξ') be admissible representations of X', ∂X' and f L-Lipschitz; f∘η is (L/λ)-Lipschitz. ISP of X with (μ_X, ξ_X), the representation (0, 0) of ∂X = 0 and f∘η gives a Lebesgue-null set N₀ such that, for t ∉ N₀, ∂(X⌞{f∘η < t}) is IM (Step 0(g); the B-current is ∫_{f∘η<t}0 d0 = 0). Fix t ∉ N₀ and A, B with A(ω) = ∫_{f<t}ξ(ω)dμ, B(φ) = ∫_{f<t}ξ'(φ)dμ'. By Step 1(4), (λ^{−n}η_*μ_X, ξ_X(a + λ·)) is an admissible representation of X'; (RU) (with U := ℝ^P, this pair, (μ, ξ) and the zero pair) gives A(ω) = λ^{−n}∫_{f∘η<t}ξ_X(x)(ω(η(x)))dμ_X(x) = λ^{−n}(X⌞{f∘η < t})(ω∘η), i.e. A is the dilation of X⌞{f∘η < t}; (RU) with (μ', ξ') and (0, 0), both representing ∂X' = 0, gives B = 0. Hence ∂A − B = ∂A is the dilation of ∂(X⌞{f∘η < t}) (Step 1(2)) and is IM by Step 1(3).
Step 3 (Representation of Γ; parent V6; accepted cbr_ci_density_representation). M_W(Γ) ≤ M(Γ) < ∞ for every W, and boundaryMassOn(Γ, W) = M_W(∂Γ) = M_W(0) = 0 (n ≥ 1). So (REP) with U := ℝ^P gives μ with μ(W) = M_W(Γ) for open W (so μ(ℝ^P) = M(Γ) < ∞), a μ-a.e. strongly measurable ξ with |ξ(x)(α)| ≤ |α| for all x, α, Γ(ω) = ∫ξ(ω)dμ, and μ(E) = 0 whenever Hⁿ(E) = 0. Let η₀ > 0 be the constant of LD_{P,d}; LD_{P,d} applied to C := Γ, (μ, ξ) (∂Γ = 0, ISP of Γ) gives liminf_{r↓0}μ(B_r(x))/(ω_nrⁿ) ≥ η₀ for μ-a.e. x.
(a) |ξ|* = 1 μ-a.e.: for ω admissible for M_{ℝ^P}(Γ), Γ(ω) ≤ ∫|ξ|*dμ, so μ(ℝ^P) = M(Γ) ≤ ∫|ξ|*dμ ≤ μ(ℝ^P) < ∞ and ∫(1 − |ξ|*)dμ = 0.
(b) Choose ξ₀ strongly measurable with ξ₀ = ξ μ-a.e. and put ζ(x) := ξ₀(x)/max(1, |ξ₀(x)|*): ζ is strongly measurable, |ζ(x)(α)| ≤ |α| for all x, α, ζ = ξ μ-a.e., Γ(ω) = ∫ζ(ω)dμ and |ζ|* = 1 μ-a.e.
(c) Let N₁ be a Borel μ-null set containing {x : liminf_rμ(B_r(x))/(ω_nrⁿ) < η₀} (toMeasurable) and M₀ := ℝ^P ∖ N₁. For x ∈ M₀, limsup_ρμ(B̄_ρ(x))/(ω_nρⁿ) ≥ η₀ > η₀/2, so Step 0(e) (ν₀ := μ, t₀ := η₀/2) gives Hⁿ(M₀) ≤ 2μ(ℝ^P)/η₀ < ∞.
(d) μ ≪ Hⁿ⌞M₀ (if Hⁿ(E ∩ M₀) = 0 then μ(E) ≤ μ(E ∩ M₀) + μ(N₁) = 0), so by the Lebesgue decomposition (Measure.haveLebesgueDecomposition_add, singularPart_eq_zero_of_ac) μ = (Hⁿ⌞M₀).withDensity(h), h := μ.rnDeriv(Hⁿ⌞M₀) Borel with values in [0, ∞], finite Hⁿ⌞M₀-a.e.
(e) M := M₀ ∩ {0 < h < ∞} ∩ {|ζ|* = 1} is Borel, μ(ℝ^P ∖ M) = 0 and Hⁿ(M) < ∞; θ := (1_M·h).toReal is Borel, θ > 0 on M, μ = (Hⁿ⌞M).withDensity(ofReal∘θ), and Γ(ω) = ∫_Mθ(x)ζ(x)(ω(x))dHⁿ(x) (integral_withDensity_eq_integral_toReal_smul). On M: |ζ(x)|* = 1, i.e. ζ(x)(β) = 1 for some |β| ≤ 1; and liminf_rμ(B_r(x))/(ω_nrⁿ) ≥ η₀. Put τ := θζ; for x ∈ M, |τ(x)|* = θ(x), and ∫‖τ‖dHⁿ⌞M ≤ C∫_Mθ dHⁿ = C·M(Γ) < ∞ (‖ζ(x)‖ is bounded by a constant C, all norms on Λ_n being equivalent).
Step 4 (Good points; parent V7). Let Θ*(x) := limsup_{r↓0}Hⁿ(M ∩ B̄_r(x))/(ω_nrⁿ). For Hⁿ-a.e. a ∈ M: (i) Θ*(a) ≤ 1 (Step 0(f)); (ii) Lebesgue points: the Besicovitch Vitali family of the finite measure Hⁿ⌞M (Besicovitch.vitaliFamily) and VitaliFamily.ae_tendsto_average_norm_sub applied to τ ∈ L¹(Hⁿ⌞M) give, for Hⁿ⌞M-a.e. a, ⨍_{M∩B̄_r(a)}‖τ − τ(a)‖dHⁿ → 0 as r ↓ 0 (Besicovitch.tendsto_filterAt: r ↦ B̄_r(a) tends to the filter of the family; for Hⁿ⌞M-a.e. a the denominators are positive); combined with (i), Hⁿ(M ∩ B̄_r(a)) ≤ 2ω_nrⁿ for small r, so o(r) := ∫_{M∩B̄_r(a)}‖τ − τ(a)‖dHⁿ satisfies o(r)/(ω_nrⁿ) → 0; (iii) a ∈ M, so θ₀ := θ(a) > 0, |ζ(a)|* = 1 and liminf_rμ(B_r(a))/(ω_nrⁿ) ≥ η₀. Call such a good points and fix one; ζ₀ := ζ(a), τ₀ := τ(a) = θ₀ζ₀. Density bounds at a: for x ∈ M, |θ(x) − θ₀| = ||τ(x)|* − |τ₀|*| ≤ |τ(x) − τ₀|* ≤ Pⁿ‖τ(x) − τ₀‖ (Step 0(a)(F1)), so μ(B_r(a)) = ∫_{M∩B_r(a)}θ dHⁿ ≤ θ₀Hⁿ(M ∩ B_r(a)) + Pⁿo(r); with μ(B_r(a)) ≥ (η₀/2)ω_nrⁿ and Pⁿo(r) ≤ (η₀/4)ω_nrⁿ for small r, there is r₀ > 0 with (η₀/(4θ₀))ω_nrⁿ ≤ Hⁿ(M ∩ B_r(a)) and Hⁿ(M ∩ B̄_r(a)) ≤ 2ω_nrⁿ for 0 < r < r₀.
Step 5 (Blow-ups; parent V8). Let λ_i > 0, λ_i → 0, η_i := dilation a λ_i, Γ_i a dilation of Γ by η_i (Step 1(1)), μ_i := λ_i^{−n}(η_i)_*μ, ξ_i(y) := ζ(a + λ_iy), N_i := η_i(M) = blowUpMap a λ_i '' M (Borel) and ν_i := Hⁿ⌞N_i. By Step 1: ∂Γ_i = 0; (μ_i, ξ_i) is an admissible representation of Γ_i with |ξ_i(y)(α)| ≤ |α| for all y, μ_i(ℝ^P) = λ_i^{−n}M(Γ) < ∞; M_W(Γ_i) = μ_i(W) for open W (Step 1(5) with W' := η_i⁻¹(W)); μ_i(ℝ^P ∖ N_i) = λ_i^{−n}μ(ℝ^P ∖ M) = 0; by Step 1(6) and change of variables, ν_i(K) = λ_i^{−n}Hⁿ(M ∩ η_i⁻¹(K)), μ_i = ν_i.withDensity(ofReal θ(a + λ_i·)) and Γ_i(ω) = ∫_{N_i}τ(a + λ_iy)(ω(y))dHⁿ(y).
(a) Bounds. For R > 0 and compact K ⊆ B̄_R: ν_i(K) ≤ λ_i^{−n}Hⁿ(M ∩ B̄_{λ_iR}(a)) ≤ 2ω_nRⁿ when λ_iR < r₀, and ν_i(K) ≤ λ_i^{−n}Hⁿ(M) < ∞ for every i, so sup_iν_i(K) < ∞; for λ_iR < r₀, ν_i(B_R) ≥ (η₀/(4θ₀))ω_nRⁿ. With ε_i(R) := λ_i^{−n}o(λ_iR) = ω_nRⁿ·o(λ_iR)/(ω_n(λ_iR)ⁿ) → 0: ∫_{N_i∩B̄_R}‖τ(a + λ_iy) − τ₀‖dHⁿ(y) = ε_i(R) (*).
(b) Compactness. (T1) with U := ℝ^P applied to (ν_i) gives a subsequence (relabelled by k) and a Borel ν finite on compact sets with ∫f dν_k → ∫f dν for continuous compactly supported f, limsup_kν_k(K) ≤ ν(K) for compact K and ν(G) ≤ liminf_kν_k(G) for open G.
(c) The limit current. C(ω) := ∫τ₀(ω(y))dν(y) defines C ∈ 𝒟_n(ℝ^P) (the integrand is continuous with compact support; |C(ω)| ≤ θ₀‖ω‖_∞ν(tsupport ω), so test forms converging in 𝒟ⁿ are mapped to a convergent sequence). For ω with tsupport ω ⊆ B_R: |Γ_k(ω) − ∫τ₀(ω)dν_k| ≤ ∫_{N_k∩B_R}‖τ(a + λ_ky) − τ₀‖‖ω(y)‖_op dHⁿ(y) ≤ Pⁿ‖ω‖_∞ε_k(R) → 0 by (*) and (F1), and ∫τ₀(ω)dν_k → C(ω); hence Γ_k ⇀ C.
(d) Properties of ν and C. (α) ν(B_R) ≤ liminf_kν_k(B_R) ≤ liminf_kλ_k^{−n}Hⁿ(M ∩ B̄_{λ_kR}(a)) ≤ ω_nRⁿΘ*(a) ≤ ω_nRⁿ for every R > 0. (β) ν(B_R) ≥ ν(B̄_{R/2}) ≥ limsup_kν_k(B̄_{R/2}) ≥ (η₀/(4θ₀))ω_n(R/2)ⁿ > 0 for every R > 0. (γ) ∂C = 0: ∂C(φ) = C(dφ) = lim_kΓ_k(dφ) = lim_k∂Γ_k(φ) = 0. (δ) M_W(C) = θ₀ν(W) for open W, by Step 0(b) with ζ' := τ₀, s := θ₀ (|τ₀(α)| ≤ θ₀|α|, τ₀(β) = θ₀ for the β with ζ₀(β) = 1). (ε) For compact K ⊆ B̄_R: μ_k(K) = ∫_{N_k∩K}θ(a + λ_ky)dHⁿ ≤ θ₀ν_k(K) + Pⁿε_k(R), so limsup_kμ_k(K) ≤ θ₀ν(K) and sup_kμ_k(K) < ∞. (ζ) limsup_kHⁿ(N_k ∩ K) = limsup_kν_k(K) ≤ ν(K) for compact K.
(e) ISP of C. Each Γ_k has ISP by Step 2 (X := Γ with (μ, ζ), ∂Γ = 0, ISP of Γ). For open W with compact closure K, M_W(Γ_k) + M_W(∂Γ_k) = μ_k(W) + 0 ≤ μ_k(K), bounded in k by (ε). With Γ_k ⇀ C, SLIM_{P,d} gives that C has ISP.
Step 6 (Invariance and simplicity; parent V9; with Step 7 accepted cbr_ci_constant_cycle_planes). For a test d-form φ, 0 = ∂C(φ) = θ₀∫ζ₀(dφ(y))dν(y). For an (n−1)-covector α define v_α ∈ ℝ^P by ⟨v_α, w⟩ := ζ₀(w^♭ ∧ α) (w^♭ := ⟨w, ·⟩; for n = 1, α is a scalar). For ψ ∈ C_c^∞(ℝ^P), φ := ψα gives dφ = dψ ∧ α and 0 = ∫ζ₀(dψ ∧ α)dν = ∫Dψ(y)[v_α]dν(y). Applied to ψ(· + sv_α) this gives (d/ds)∫ψ(y + sv_α)dν(y) = 0 (differentiation under the integral sign), so ∫ψ(y + v)dν(y) = ∫ψ dν for v ∈ ℝv_α, and by composition for v ∈ V₀ := span{v_α}; by Step 0(c), applied to the restrictions of ν and of its translate to the balls B_m (finite measures with equal integrals against C_c^∞(B_m)), ν(A − v) = ν(A) for every Borel A and v ∈ V₀. Let r := dim V₀ and e'_1, …, e'_P an orthonormal basis with V₀ = span(e'_1, …, e'_r), e'^i := (e'_i)^♭. For an increasing multi-index I of length n containing some i > r, e'^I = ±e'^i ∧ e'^{I∖i}, so ζ₀(e'^I) = ±⟨v_{e'^{I∖i}}, e'_i⟩ = 0 (e'_i ⊥ V₀). Every n-covector is β = Σ_Iβ(e'_I)e'^I, so ζ₀(β) = Σ_{I⊆{1,…,r}}β(e'_I)ζ₀(e'^I); as |ζ₀|* = 1, ζ₀ ≠ 0 and r ≥ n. Growth: pick y₀ in the support of ν (non-empty by (β)), m₀ := ν(B_1(y₀)) > 0. For R ≥ 2(|y₀| + 1) the balls B_1(y₀ + v), v ∈ 2ℤ^r in the coordinates e'_1, …, e'_r with |v| ≤ R/2, are pairwise disjoint, contained in B_R, at least c_rR^r in number for R large (c_r > 0 depending on r), and each has ν-measure m₀; so c_rm₀R^r ≤ ν(B_R) ≤ ω_nRⁿ (Step 5(α)) for all large R, which forces r ≤ n. Hence r = n and ζ₀(β) = β(e'_1, …, e'_n)ζ₀(e'^{1…n}); since |β(e'_1, …, e'_n)| ≤ |β| with equality for β = e'^{1…n} (Step 0(a)(O1),(O2)) and |ζ₀|* = 1, ζ₀(e'^{1…n}) = ±1, and after replacing e'_1 by −e'_1 if necessary, ζ₀(β) = β(v) for all β with v := (e'_1, …, e'_n) orthonormal and V₀ = span v. Note: for every (n−1)-covector α, v_α = Σ_i(−1)^{i−1}α(v_1, …, v̂_i, …, v_n)v_i, and α := β_{(v_1,…,v̂_i,…,v_n)} (Step 0(a)(O2)) gives v_α = ±v_i; so V₀ = span{v_α : α} is determined by ζ₀ alone (Plane uniqueness: if also ζ₀(β) = β(v') for an orthonormal v', then span v' = V₀).
Step 7 (Structure of ν; parent V10). (a) Product structure. For bounded Borel B ⊆ V₀^⊥, A ↦ ν(A + B) (A ⊆ V₀ Borel; A + B is Borel as the image of A × B under the linear isomorphism V₀ × V₀^⊥ → ℝ^P) is a translation-invariant Borel measure on V₀ ≅ ℝⁿ, finite on compact sets, hence equal to σ(B)·Hⁿ⌞V₀ (uniqueness of Haar measure, Mathlib MeasureTheory.Measure.isAddLeftInvariant_eq_smul; Hⁿ⌞V₀ is the image of Lⁿ under an isometry); σ extends to a Borel measure on V₀^⊥ finite on compact sets, and ν(A) = ∫_{V₀}σ({w ∈ V₀^⊥ : s + w ∈ A})dHⁿ(s) for Borel A (agreement on the generating π-system of sets A + B, σ-finiteness). (b) Atoms. LD_{P,d} applied to C with (θ₀ν, ζ₀) (∂C = 0; θ₀ν finite on compacts; M_W(C) = θ₀ν(W) by Step 5(δ); ζ₀ constant with |ζ₀(α)| ≤ |α|; C(ω) = ∫ζ₀(ω)d(θ₀ν); ISP by Step 5(e)) gives liminf_rν(B_r(y))/(ω_nrⁿ) ≥ c := η₀/θ₀ for ν-a.e. y. As B_r(s + w) ⊆ (V₀ ∩ B_r(s)) + (V₀^⊥ ∩ B_r(w)), ν(B_r(s + w)) ≤ ω_nrⁿσ(B_r(w)), so liminf_rν(B_r(s + w))/(ω_nrⁿ) ≤ σ({w}). The set Z_c := {w ∈ V₀^⊥ : σ({w}) ≥ c} meets every bounded set in finitely many points (σ is finite on compact sets), so it is closed and countable; for Z := V₀^⊥ ∖ Z_c, the Borel set (V₀ ∩ B_1) + Z consists of points with lower density < c, so ω_nσ(Z) = ν((V₀ ∩ B_1) + Z) = 0. Hence σ = Σ_{w∈Z_c}σ({w})δ_w and ν = Σ_{w∈Z_c}σ({w})Hⁿ⌞(V₀ + w). (c) Finiteness. ν(B_R) = Σ_{w∈Z_c}σ({w})ω_n(R² − |w|²)_+^{n/2} ≤ ω_nRⁿ; for a finite F ⊆ Z_c, dividing by ω_nRⁿ and letting R → ∞ gives Σ_{w∈F}σ({w}) ≤ 1. As each σ({w}) ≥ c > 0, Z_c = {w_1, …, w_N} is finite with α_i := σ({w_i}) ≥ c and Σ_iα_i ≤ 1. By (β), 0 lies in the support of ν, which is the closed set ⋃_i(V₀ + w_i), so 0 ∈ V₀ + w_i for some i, i.e. w_i = 0 (w_i ∈ V₀^⊥). Thus ν = Σ_{i=1}^Nα_iHⁿ⌞(V₀ + w_i), the w_i ⊥ V₀ distinct, α_i ≥ η₀/θ₀ > 0, Σα_i ≤ 1, some w_i = 0, and C(ω) = θ₀∫ω(y)(v)dν(y).
Step 8 (Each α_i ≥ 1; parent V11(a)–(e), localized). Fix i₀; α := α_{i₀}, w := w_{i₀}. Write μ_k, ξ_k, N_k, ν_k for the blow-up data of Step 5 (along the subsequence there). Extend v to an orthonormal basis v_1, …, v_P; p : ℝ^P → ℝⁿ, p(x) := (⟨x, v_1⟩, …, ⟨x, v_n⟩); q(x) := x − Σ_{j≤n}⟨x, v_j⟩v_j (orthogonal projection onto V₀^⊥). p is 1-Lipschitz and maps each plane V₀ + w_j isometrically onto ℝⁿ. dy := dy¹ ∧ ⋯ ∧ dyⁿ on ℝⁿ and β_v := p^#dy, β_v(u) = det(⟨u_i, v_j⟩), so β_v(v) = 1 and |β_v| = 1 (Step 0(a)(O2)). δ' := min_{j≠i₀}|w_j − w|/3 (δ' := 1 if N = 1), δ' > 0. g(x) := dist(x, V₀ + w) = |q(x) − w|, 1-Lipschitz; on V₀ + w_j, g ≡ |w_j − w|, which is 0 for j = i₀ and ≥ 3δ' for j ≠ i₀. Fix R > 0 and put Ω := p⁻¹(B_{3R}) (open; B_ρ ⊆ ℝⁿ).
(a) Compact annulus. A'' := p⁻¹(B̄_{3R}) ∩ {δ' ≤ g ≤ 2δ'} is closed and bounded (|x|² = |p(x)|² + |q(x)|² ≤ 9R² + (|w| + 2δ')²), hence compact, and meets no plane V₀ + w_j; so ν(A'') = 0 and limsup_kμ_k(A'') ≤ θ₀ν(A'') = 0 (Step 5(ε)).
(b) Slicing. For each k, (SL) with U := ℝ^P, T := Γ_k, the admissible representation (μ_k, ξ_k), the admissible representation (0, 0) of ∂Γ_k = 0, f := g, L := 1 gives currents Z_{k,t} ∈ 𝒟_n(ℝ^P) (the A_t of (SL)) with Z_{k,t}(ω) = ∫_{g<t}ξ_k(ω)dμ_k and B_t = ∫_{g<t}0 d0 = 0, and M_Ω(∂Z_{k,t}) ≤ liminf_{h↓0}h⁻¹μ_k(Ω ∩ {t − h < g < t}) for all t.
(c) Good level. (MM) with μs := (μ_k), f := g, G := Ω, (a, b) := (δ', 2δ'), L := 1 and Z_k(t) := M_Ω(∂Z_{k,t}) (μ_k(Ω ∩ {δ' < g < 2δ'}) ≤ μ_k(ℝ^P) < ∞) gives a measurable G̃ with liminf_kM_Ω(∂Z_{k,t}) ≤ G̃(t) for a.e. t ∈ (δ', 2δ') and ∫⁻_{(δ',2δ')}G̃ ≤ liminf_kμ_k(Ω ∩ {δ' < g < 2δ'}) ≤ liminf_kμ_k(A'') = 0. So G̃ = 0 a.e. on (δ', 2δ'); fix t ∈ (δ', 2δ') with liminf_kM_Ω(∂Z_{k,t}) = 0. The level set {g = t} meets no plane, so ν({g = t}) = 0.
(d) Convergence of the restrictions. (T2) with U := ℝ^P, Xs := (Γ_k) with (μ_k, ξ_k), X := C with the admissible representation (θ₀ν, ξ_v), ξ_v the constant n-vector β ↦ β(v) (|β(v)| = |ζ₀(β)| ≤ |β|), limit measure θ₀ν (finite on compacts, limsup_kμ_k(K) ≤ θ₀ν(K) by Step 5(ε), θ₀ν({g = t}) = 0), f := g: for every ω, Z_{k,t}(ω) → θ₀∫_{g<t}ω(y)(v)dν(y) = θ₀α∫_{V₀+w}ω(y)(v)dHⁿ(y), since among the planes only V₀ + w meets {g < t} (t < 2δ' < 3δ') and it lies in {g < t}. Pass to a subsequence (not relabelled; Steps 5 and 8(a) persist) with M_Ω(∂Z_k) → 0, Z_k := Z_{k,t}, and drop finitely many k so that M_Ω(∂Z_k) < ∞ for all k. Only this cylinder-local boundary mass is controlled; nothing is claimed about the total mass of ∂Z_k.
(e) Localization. If ω is a test form with tsupport ω ∩ {g ≤ t} = ∅, then ω = 0 on {g < t} and Z_k(ω) = ∫_{g<t}ξ_k(ω(x))dμ_k = 0.
(f) Projected currents on B_{2R}. Test n-forms on B_{2R} ⊆ ℝⁿ are b·dy with b ∈ C_c^∞(B_{2R}). Set Y_k(b dy) := ∫_{g<t}b(p(x))ξ_k(x)(β_v)dμ_k(x) = ∫_{g<t}ξ_k(x)((p^#(b dy))(x))dμ_k(x); the integrand is bounded by sup|b| (|ξ_k(β_v)| ≤ |β_v| = 1) and vanishes off the compact set p⁻¹(spt b) ∩ {g ≤ t}. Y_k is linear and |Y_k(b dy)| ≤ sup|b|·μ_k(ℝ^P), so Y_k ∈ 𝒟_n(B_{2R}) (GeometricCurrentOn (ball 0 (2R)) n with ambient ℝⁿ = Euclid n). Mass: for admissible b dy (spt b ⊆ B_{2R}, |b| ≤ 1), |Y_k(b dy)| ≤ μ_k(p⁻¹(B̄_{2R}) ∩ {g ≤ t}), a compact set; so limsup_kM(Y_k) ≤ θ₀ν(p⁻¹(B̄_{2R}) ∩ {g ≤ t}) < ∞, and since also each M(Y_k) ≤ μ_k(ℝ^P) < ∞, Λ := sup_kM(Y_k) < ∞; consequently |Y_k(b dy)| ≤ Λ sup|b| for all test forms.
(g) M_{B_{2R}}(∂Y_k) ≤ M_Ω(∂Z_k). Let γ be a test (n−1)-form on B_{2R} with |γ| ≤ 1 and χ ∈ C_c^∞(Ω; [0, 1]) with χ = 1 on an open neighbourhood O of the compact set {g ≤ t} ∩ p⁻¹(tsupport γ) ⊆ p⁻¹(B_{2R}) ⊆ Ω. On {g < t}, χ·p^#dγ = p^#dγ (either p(x) ∉ tsupport γ and both vanish, or x ∈ O), so ∂Y_k(γ) = Y_k(dγ) = Z_k(χ·p^#dγ). Since p^#dγ = d(p^#γ), χ·p^#dγ = d(χp^#γ) − dχ ∧ p^#γ, and tsupport(dχ ∧ p^#γ) ⊆ (ℝ^P ∖ O) ∩ p⁻¹(tsupport γ) is disjoint from {g ≤ t}; by (e), Z_k(dχ ∧ p^#γ) = 0. Hence ∂Y_k(γ) = Z_k(d(χp^#γ)) = ∂Z_k(χp^#γ). The test form χp^#γ has tsupport ⊆ Ω and |χ(x)(p^#γ)(x)| ≤ |γ(p(x))| ≤ 1 (Step 0(a)(O3)), so it is admissible for M_Ω(∂Z_k) and ∂Y_k(γ) ≤ M_Ω(∂Z_k). Taking the supremum over admissible γ: M_{B_{2R}}(∂Y_k) ≤ M_Ω(∂Z_k) → 0.
(h) Weak limit of Y_k. Fix χ₀ ∈ C_c^∞(Ω; [0, 1]) with χ₀ = 1 on the compact set {g ≤ t} ∩ p⁻¹(B̄_{2R}). For b ∈ C_c^∞(B_{2R}), b(p(x))ξ_k(x)(β_v) = ξ_k(x)(χ₀(x)b(p(x))β_v) on {g < t}, so Y_k(b dy) = Z_k(χ₀·(b∘p)·β_v) → θ₀α∫_{V₀+w}χ₀(y)b(p(y))β_v(v)dHⁿ(y) = θ₀α∫_{V₀+w}b(p(y))dHⁿ(y) = θ₀α∫_{ℝⁿ}b dLⁿ by (d), using χ₀ = 1 on (V₀ + w) ∩ p⁻¹(spt b), β_v(v) = 1, the isometry p|_{V₀+w} : V₀ + w → ℝⁿ (Isometry.euclideanHausdorffMeasure_image) and Hⁿ = Lⁿ on ℝⁿ.
(i) Densities. (REP) with ambient ℝⁿ (P := n), U := B_{2R}, degree n and T := Y_k applies: M_W(Y_k) ≤ Λ and boundaryMassOn(Y_k, W) = M_W(∂Y_k) ≤ M_{B_{2R}}(∂Y_k) < ∞. It gives a Borel μ_{Y_k} null off B_{2R} with μ_{Y_k}(B_{2R}) = M(Y_k) ≤ Λ, a field ξ_{Y_k} with |ξ_{Y_k}(x)(α)| ≤ |α|, Y_k(ω) = ∫ξ_{Y_k}(ω)dμ_{Y_k}, and μ_{Y_k}(E) = 0 whenever Lⁿ(E) = Hⁿ(E) = 0. By the Lebesgue decomposition μ_{Y_k} = ρ_kLⁿ with ρ_k := μ_{Y_k}.rnDeriv Lⁿ, ∫ρ_k ≤ Λ, ρ_k = 0 a.e. off B_{2R}; u_k := ρ_k·ξ_{Y_k}(dy) (choosing ξ_{Y_k} strongly measurable, which changes it only on a μ_{Y_k}-null set) is a Borel function in L¹(Lⁿ), zero a.e. off B_{2R}, with ∫|u_k| ≤ Λ and Y_k(b dy) = ∫b u_k dLⁿ for every b ∈ C_c^∞(B_{2R}) (integral_withDensity_eq_integral_toReal_smul; |dy| = 1).
(j) Measurable hull and vanishing of u_k off it. Let S_k := p(N_k ∩ F), F := {g < t} ∩ p⁻¹(B_{2R}) (Borel), and E_k := toMeasurable(Lⁿ, S_k): a measurable superset of S_k with Lⁿ(E_k ∩ B) = Lⁿ(S_k ∩ B) for every measurable B (Mathlib Measure.measure_toMeasurable_inter_of_sFinite; no measurability of S_k is needed). Claim: u_k = 0 Lⁿ-a.e. on B_{2R} ∖ E_k. Let h_k := ξ_k(β_v) (|h_k| ≤ 1) and consider the finite Borel measures on ℝⁿ σ₁ := u_k⁺Lⁿ + p_*(h_k⁻·μ_k⌞F) and σ₂ := u_k⁻Lⁿ + p_*(h_k⁺·μ_k⌞F) (finite: ∫|u_k| < ∞, μ_k(F) < ∞), both null off B_{2R} (p(F) ⊆ B_{2R}). By (f) and (i), ∫b dσ₁ = ∫b dσ₂ for every b ∈ C_c^∞(B_{2R}), so σ₁ = σ₂ by Step 0(c). For a Borel set B ⊆ B_{2R} ∖ E_k we have F ∩ p⁻¹(B) ∩ N_k = ∅ (a point x of it would give p(x) ∈ S_k ∩ B ⊆ E_k ∩ B = ∅), hence μ_k(F ∩ p⁻¹(B)) ≤ μ_k(ℝ^P ∖ N_k) = 0, p_*(h_k^±μ_k⌞F)(B) = 0, and σ₁(B) = σ₂(B) gives ∫_Bu_k⁺dLⁿ = ∫_Bu_k⁻dLⁿ. Taking B := (B_{2R} ∖ E_k) ∩ {u_k > 0} gives ∫_Bu_k⁺ = 0, i.e. Lⁿ(B) = 0, and likewise for {u_k < 0}: u_k = 0 Lⁿ-a.e. on B_{2R} ∖ E_k.
(k) L¹ convergence on B_R. Fix s₀ ∈ (0, R/2) (so B_{R+2s₀} ⊆ B_{2R}), a mollifier φ₁ ∈ C_c^∞(B_1) with φ₁ ≥ 0, ∫φ₁ = 1, φ_s(z) := s^{−n}φ₁(z/s), and (u_k ∗ φ_{s₀})(x) := ∫u_k(y)φ_{s₀}(x − y)dy. (k1) Uniform convergence of the mollified densities. For x ∈ B̄_R, y ↦ φ_{s₀}(x − y) lies in C_c^∞(B_{R+s₀}), so (u_k ∗ φ_{s₀})(x) = Y_k(φ_{s₀}(x − ·)dy) → θ₀α∫φ_{s₀} = θ₀α by (h); and |(u_k ∗ φ_{s₀})(x) − (u_k ∗ φ_{s₀})(x')| ≤ Λ·Lip(φ_{s₀})|x − x'| for all k (by (f)). Pointwise convergence and uniform equicontinuity on the compact set B̄_R give sup_{B̄_R}|u_k ∗ φ_{s₀} − θ₀α| → 0. (k2) BV estimate ∫_{B_R}|u_k − u_k ∗ φ_{s₀}| ≤ s₀M_{B_{2R}}(∂Y_k), by duality. Let κ be Borel with |κ| ≤ 1 and κ = 0 off B_R; for ϑ ∈ (0, s₀) put κ_ϑ := κ ∗ φ_ϑ ∈ C_c^∞(B_{R+ϑ}) (|κ_ϑ| ≤ 1) and h_ϑ(x) := ∫φ_{s₀}(z)(κ_ϑ(x) − κ_ϑ(x + z))dz ∈ C_c^∞(B_{R+2s₀}). By Fubini, ∫u_kh_ϑ = ∫(u_k − u_k ∗ φ_{s₀})κ_ϑ. On the other hand h_ϑ(x) = −∫φ_{s₀}(z)∫_0^1∇κ_ϑ(x + sz)·z ds dz, so by Fubini (the integrand is bounded by |u_k(x)|φ_{s₀}(z)‖∇κ_ϑ‖_∞|z|) ∫u_kh_ϑ = Y_k(h_ϑdy) = −∫φ_{s₀}(z)∫_0^1Y_k((∇κ_ϑ(· + sz)·z)dy)ds dz. With ε_j := (−1)^{j−1}dy¹ ∧ ⋯ ∧ dy^{j−1} ∧ dy^{j+1} ∧ ⋯ ∧ dyⁿ (ε_1 := 1 if n = 1), every smooth compactly supported K₁ satisfies (∇K₁·z)dy = d(K₁Σ_jz_jε_j), and |K₁Σ_jz_jε_j| ≤ |z|sup|K₁| (the ε_j are distinct standard basis covectors up to sign, hence orthonormal for the coefficient norm); for K₁ := κ_ϑ(· + sz) (support in B_{R+ϑ+s₀} ⊆ B_{2R}, |K₁| ≤ 1) this gives |Y_k((∇K₁·z)dy)| = |∂Y_k(K₁Σ_jz_jε_j)| ≤ |z|M_{B_{2R}}(∂Y_k). Since |z| < s₀ on spt φ_{s₀} and ∫φ_{s₀} = 1, |∫(u_k − u_k ∗ φ_{s₀})κ_ϑ| ≤ s₀M_{B_{2R}}(∂Y_k). As ϑ ↓ 0, κ_ϑ → κ at every Lebesgue point of κ, i.e. Lⁿ-a.e. (|κ ∗ φ_ϑ(x) − κ(x)| ≤ ω_n sup φ₁·⨍_{B_ϑ(x)}|κ − κ(x)|; Lebesgue differentiation, VitaliFamily.ae_tendsto_average_norm_sub), with |κ_ϑ| ≤ 1, so dominated convergence (u_k − u_k ∗ φ_{s₀} is integrable on B_{R+s₀}) gives |∫(u_k − u_k ∗ φ_{s₀})κ| ≤ s₀M_{B_{2R}}(∂Y_k). Choosing κ := sign(u_k − u_k ∗ φ_{s₀})·1_{B_R} gives the estimate. (k3) Hence ∫_{B_R}|u_k − θ₀α| ≤ s₀M_{B_{2R}}(∂Y_k) + Lⁿ(B_R)sup_{B̄_R}|u_k ∗ φ_{s₀} − θ₀α| → 0 as k → ∞, by (g) and (k1).
(l) Volume comparison. Since u_k = 0 a.e. on B_R ∖ E_k, θ₀α·Lⁿ(B_R ∖ E_k) ≤ ∫_{B_R}|u_k − θ₀α| → 0 (θ₀α > 0). Moreover Lⁿ(B_R ∩ E_k) = Lⁿ(B_R ∩ S_k) ≤ Lⁿ(p(N_k ∩ {g < t} ∩ p⁻¹(B_R))) ≤ Hⁿ(N_k ∩ {g < t} ∩ p⁻¹(B_R)) ≤ Hⁿ(N_k ∩ A'), A' := {g ≤ t} ∩ p⁻¹(B̄_R) (compact), because p is 1-Lipschitz (Mathlib LipschitzWith.hausdorffMeasure_image_le for μH[n], hence for μHE[n] = c_nμH[n]) and Hⁿ = Lⁿ on ℝⁿ. Therefore ω_nRⁿ = Lⁿ(B_R) ≤ Lⁿ(B_R ∖ E_k) + Hⁿ(N_k ∩ A'), and by Step 5(ζ), ω_nRⁿ ≤ limsup_kHⁿ(N_k ∩ A') ≤ ν(A') = αHⁿ((V₀ + w) ∩ p⁻¹(B̄_R)) = αLⁿ(B̄_R) = αω_nRⁿ, because only V₀ + w meets A' (t < 3δ') and (V₀ + w) ⊆ {g ≤ t}. Hence α_{i₀} = α ≥ 1.
Step 9 (Approximate tangent plane; parent V12). By Steps 7–8, 1 ≥ Σ_iα_i ≥ N ≥ 1, so N = 1, α_1 = 1 and w_1 = 0: ν = Hⁿ⌞V₀ and C(ω) = θ₀∫_{V₀}ω(y)(v)dHⁿ(y). Claim: HasApproximateTangentSpaceAt n M a V₀. First, dim V₀ = n (v is orthonormal). Let f ∈ C_c(ℝ^P), F(r) := ∫_{blowUpMap a r '' M}f dHⁿ and L₀ := ∫_{V₀}f dHⁿ. As 𝓝[>]0 is countably generated, it suffices (Mathlib tendsto_of_subseq_tendsto) that every sequence r_j tending to 0 within (0, ∞) has a subsequence along which F → L₀. Dropping the finitely many indices with r_j ≤ 0 and applying Steps 5–8 to the positive sequence λ_j := r_j gives a subsequence with F(r_{j_k}) = ∫f dν_k → ∫f dν', where ν' = Hⁿ⌞span(v') for an orthonormal v' with ζ₀(β) = β(v') for all β; by the plane uniqueness of Step 6, span v' = V₀, so F(r_{j_k}) → L₀. Moreover ζ(a)(β) = β(v) with v orthonormal spanning V₀, i.e. IsUnitOrientationOf ζ(a) V₀. This holds at every good point a, hence for Hⁿ-a.e. a ∈ M; write Q(a) := V₀(a) there and Q(a) := ⊥ elsewhere.
Measurability of the plane field. For an n-vector ζ' let L_{ζ'} : Λ^{n−1}(ℝ^P) → ℝ^P be the linear map α ↦ v_α, ⟨v_α, w⟩ := ζ'(w^♭ ∧ α) (its matrix entries ζ'(e^k ∧ e^J) are linear in ζ'), and Π(ζ') := L_{ζ'}L_{ζ'}ᵀ, where the transpose uses the coefficient inner product on Λ^{n−1}, for which the standard covectors e^J (J increasing) are orthonormal; Π is a polynomial, hence continuous, function of ζ'. If ζ'(β) = β(v) with v orthonormal, then v_α = Σ_i(−1)^{i−1}α(v^{(i)})v_i, v^{(i)} := (v_1, …, v̂_i, …, v_n), so Π(ζ')w = Σ_J⟨v_{e^J}, w⟩v_{e^J} = Σ_{i,l}(−1)^{i+l}⟨v_i, w⟩v_l·Σ_Je^J(v^{(i)})e^J(v^{(l)}), and by the Cauchy–Binet formula Σ_Je^J(v^{(i)})e^J(v^{(l)}) = det(⟨v^{(i)}_s, v^{(l)}_r⟩)_{s,r} = δ_{il}; hence Π(ζ') is the orthogonal projection onto span v. So x ↦ Q(x).starProjection agrees Hⁿ⌞M-a.e. with the strongly measurable map x ↦ Π(ζ(x)) and is Hⁿ⌞M-a.e. strongly measurable.
Step 10 (Integrality; parent V14; accepted cbr_ci_plane_multiplicity_nat). At a good point a, C = θ₀∫_{V₀}ω(y)(v)dHⁿ(y) has ISP (Step 5(e)). Claim: θ₀ ∈ ℕ. Let f(y) := ⟨y, v_1⟩ (1-Lipschitz). Parametrize V₀ by s ∈ ℝⁿ ↦ Σ_is_iv_i (an isometry, so Hⁿ⌞V₀ is the image of Lⁿ). For every t, A_t := C⌞{f < t} (Step 0(g) with the admissible representation (θ₀Hⁿ⌞V₀, ξ_v)) satisfies, for every test (n−1)-form φ with g_i(s) := φ(Σs_jv_j)(v_1, …, v̂_i, …, v_n): dφ(Σs_jv_j)(v_1, …, v_n) = Σ_i(−1)^{i−1}∂_{s_i}g_i(s) (constant vector fields), so ∂A_t(φ) = θ₀∫_{s_1<t}Σ_i(−1)^{i−1}∂_{s_i}g_i ds = θ₀∫_{ℝ^{n−1}}g_1(t, s_2, …, s_n)ds_2⋯ds_n (the terms i ≥ 2 vanish by compact support and the fundamental theorem of calculus in s_i; the term i = 1 integrates to its value at s_1 = t), i.e. ∂A_t(φ) = θ₀∫_{L_t}φ(y)(v_2, …, v_n)dH^{n−1}(y), L_t := tv_1 + span(v_2, …, v_n); for n = 1, ∂A_t(φ) = θ₀φ(tv_1) (with another sign convention for the exterior derivative the right sides change sign; only the masses below are used, so this is immaterial). ISP of C with (θ₀Hⁿ⌞V₀, ξ_v), the representation (0, 0) of ∂C = 0 and f gives a t for which ∂A_t − 0 = ∂A_t is IM; let (M_t, θ', ξ') be an IMRep. By (MR), M_G(∂A_t) = (θ'H^{n−1}⌞M_t)(G) for open G; by Step 0(b) in degree n − 1 (ν' := H^{n−1}⌞L_t, the constant (n−1)-vector β ↦ β(v_2, …, v_n), which has |β(v_2, …, v_n)| ≤ |β| by (O1) and value 1 at β_{(v_2,…,v_n)} by (O2), s := θ₀; for n = 1, ν' := δ_{tv_1} and the 0-vector β ↦ β), M_G(∂A_t) = θ₀H^{n−1}(L_t ∩ G). The two Borel measures θ'H^{n−1}⌞M_t and θ₀H^{n−1}⌞L_t are finite on bounded sets (θ' is locally integrable) and agree on open sets, so they are equal (Step 0(c)). With S := L_t ∩ B_1(tv_1) (H^{n−1}(S) = ω_{n−1} > 0): θ₀H^{n−1}(S ∖ M_t) = 0, so H^{n−1}(S ∩ M_t) > 0, and ∫_Eθ'dH^{n−1} = θ₀H^{n−1}(E) for Borel E ⊆ S ∩ M_t, so θ' = θ₀ H^{n−1}-a.e. on S ∩ M_t. Hence θ₀ = θ'(x) for some x, and θ₀ ∈ ℕ. Thus θ(a) is a positive integer for Hⁿ-a.e. a ∈ M.
Step 11 (Conclusion; parent V13, V15; accepted cbr_ci_isIntegerMultiplicity_of_ae_tangent). (RECT) applied to M (Borel, Hⁿ(M) < ∞) with the plane field Q of Step 9 (x ↦ Q(x).starProjection Hⁿ⌞M-a.e. strongly measurable; HasApproximateTangentSpaceAt n M x Q(x) for Hⁿ⌞M-a.e. x) shows that M is countably n-rectifiable. Let N₂ := M ∩ toMeasurable(Hⁿ⌞M, X), X the set of non-good points of M (a Borel Hⁿ-null subset of M containing X), and M'' := M ∖ N₂ (Borel, Hⁿ(M ∖ M'') = 0). Define mult(x) := ⌊θ(x)⌋₊ for x ∈ M'' and 0 otherwise (Borel, ℕ-valued, = θ(x) ≥ 1 on M'' by Step 10) and orient := ζ. Then (M'', mult, ζ) is an IMRep in ℝ^P: M'' is Borel, contained in ℝ^P and countably n-rectifiable (CountablyRectifiable.mono); mult > 0 on M''; ∫⁻_{M''∩K}mult dHⁿ ≤ ∫⁻_M ofReal(θ)dHⁿ = M(Γ) < ∞; ζ is strongly measurable; and for Hⁿ⌞M''-a.e. x, HasApproximateTangentSpaceAt n M x Q(x) (Step 9), hence by (IMC)(a) (U := ℝ^P, M'' ⊆ M Borel, Hⁿ(M ∩ K) ≤ Hⁿ(M) < ∞) HasApproximateTangentSpaceAt n M'' x Q(x), and IsUnitOrientationOf ζ(x) Q(x) (Step 9). It represents Γ: Γ(ω) = ∫_Mθζ(ω)dHⁿ = ∫_{M''}(mult x : ℝ)·ζ(x)(ω(x))dHⁿ (Step 3, Hⁿ(M ∖ M'') = 0). Hence Γ is integer multiplicity (if μ = 0, then Γ = 0 and M = ∅ gives the empty IMRep). ∎

## Key steps

1. Step 0: coefficient-norm invariance, constant-vector mass formula, isodiametric normalization μHE[n] ≤ (ω_n/2ⁿ)μH[n], and the sharp density comparison by Vitali covering with the finite-tail argument (no enlargement factor), giving Θ*(Hⁿ⌞M, ·) ≤ 1 Hⁿ-a.e. on M.
2. Steps 1–2: dilations preserve integer multiplicity, representations and masses, and (via restrict_unique) the integer slice property of cycles.
3. Step 3: (REP), LD_{P,d} and Step 0(e) give μ_Γ = θHⁿ⌞M with Hⁿ(M) < ∞, Γ(ω) = ∫_Mθζ(ω)dHⁿ and |ζ|* = 1 on M.
4. Steps 4–5: at good points (upper density ≤ 1, Lebesgue point of θζ, lower density ≥ η₀) the blow-ups converge (T1) to C = θ₀ζ(a)ν with ∂C = 0, M_W(C) = θ₀ν(W), limsup μ_{Γ_k}(K) ≤ θ₀ν(K), and ISP by SLIM_{P,d}.
5. Steps 6–7: ∂C = 0, growth ν(B_R) ≤ ω_nRⁿ, Haar uniqueness and LD_{P,d} make ζ(a) the unit n-vector of an n-plane V₀ and ν = Σα_iHⁿ⌞(V₀ + w_i), finitely many planes, α_i ≥ η₀/θ₀, Σα_i ≤ 1, some w_i = 0.
6. Step 8 (localized V11): on Ω = p⁻¹(B_{3R}) a level t chosen with the compact annulus gives M_Ω(∂(Γ_k⌞{g<t})) → 0; projected currents Y_k on B_{2R} satisfy M_{B_{2R}}(∂Y_k) ≤ M_Ω(∂Z_k) and Y_k ⇀ θ₀α dy; their densities u_k vanish off the measurable hull E_k of the projected carrier; the mollifier/BV estimate gives u_k → θ₀α in L¹(B_R); the volume comparison gives α_i ≥ 1.
7. Step 9: hence ν = Hⁿ⌞V₀, so M has approximate tangent plane V₀ at a (subsequence principle, plane uniqueness), oriented by ζ(a), and the plane field is a.e. strongly measurable (Π(ζ) = L_ζL_ζᵀ).
8. Step 10: slices of θ₀[[V₀]] by ⟨·, v_1⟩ are θ₀ times an (n−1)-plane and IM for a.e. level, so (MR) and the constant-vector mass formula force θ₀ ∈ ℕ.
9. Step 11: (RECT) makes M countably n-rectifiable; with (IMC)(a), (M'', θ, ζ) is an IMRep of Γ.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); git rev-parse HEAD (b4d606db)`
- `cmp GMT/Ch07/Contract.lean local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean (identical); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `grep -rn 'theorem exists_disjoint_subfamily_covering_enlargement_closedBall|theorem exists_disjoint_subfamily_covering_enlargement |theorem hausdorffMeasure_le_liminf_tsum|theorem exists_disjoint_closedBall_covering_ae |theorem ae_tendsto_average_norm_sub|theorem tendsto_filterAt|theorem exists_isOpen_lt_of_lt|theorem measure_toMeasurable_inter_of_sFinite|euclideanHausdorffMeasure_eq_volume|theorem hausdorffMeasure_image_le|lemma isMulLeftInvariant_eq_smul |theorem tendsto_of_subseq_tendsto' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `sed -n 40,75p and 150,185p mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean; sed -n 545,575p mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean; sed -n 1,140p and 185,200p mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (μHE[d] := addHaarScalarFactor(volume, μH[d]) • μH[d])`
- `grep -rn 'theorem simon_theorem_3_3|theorem simon_theorem_3_26_i|theorem simon_theorem_2_10|simonHausdorffMeasureReal_nat_eq_smul_euclideanHausdorffMeasure' lake-packages-25730c7c/simongmt/Poincare/SimonGMT; sed -n 1,280p Chapter03/Rectifiable.lean (HasApproximateTangentSpaceAt, CountablyRectifiable, blowUpMap); grep -n 'def massAdmissibleOn|def GeometricCurrentOn.massOn|massOn_le_liminf' Chapter06/Mass.lean`
- `lake env lean (run.py) Reach.lean / Reach2.lean / Reach3.lean / Reach4.lean after import GMT.Ch07.Submission: #check of Vitali.exists_disjoint_subfamily_covering_enlargement, Measure.hausdorffMeasure_le_liminf_tsum, Besicovitch.exists_disjoint_closedBall_covering_ae, Besicovitch.tendsto_filterAt, VitaliFamily.ae_tendsto_average_norm_sub, Set.exists_isOpen_lt_of_lt, Measure.measure_toMeasurable_inter_of_sFinite, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, LipschitzWith.hausdorffMeasure_image_le, Isometry.euclideanHausdorffMeasure_image, Measure.isAddLeftInvariant_eq_smul, tendsto_of_subseq_tendsto, integral_withDensity_eq_integral_toReal_smul, Measure.haveLebesgueDecomposition_add, Measure.singularPart_eq_zero_of_ac, CountablyRectifiable.mono, WeaklyConvergesOn.massOn_le_liminf (all found); Poincare.SimonGMT.Chapter01.simon_theorem_3_26_i and simon_theorem_2_10 (unknown identifier)`
- `python3 -I over dag.json: statuses/candidate commits of cmc_slice_mass_bounds, cbr_setIntegral_eq_of_integral_eq, cbr_isoperimetric_filling, dimred_mbl_fnd_exists_massRepresentation_core, dimred_mbl_fnd_null_of_representation, cbr_vague_*, cbr_sublevel_restriction_tendsto, cbr_slice_mass_majorant, cbr_isIntegerMultiplicity_of_local_reps, cbr_imRep_measure_basic, cbr_orient_ae_eq_of_setIntegral_eq, cmcdt_*, cbrcs_localize_at_point, cmc_deformation_theorem, dimred_mbl_deformation_theorem, cmc_closure_and_boundary_rectifiability, cbr_ci_*; prefix scan dtc_bc_tc_cl`
- `python3 -I string comparison: frozen types of slicing/restrict_unique/rectifiable/(MR) versus the hypothesis prefixes of cbr_ci_dilation_slice_property, cbr_ci_plane_multiplicity_nat, cbr_ci_isIntegerMultiplicity_of_ae_tangent and the type of cbr_rectifiable_of_approx_tangent (all equal)`
- `lake env lean (run.py) /tmp/dtc_closure_v2/lean/Types.lean (12 frozen types, exit 0) and Assembly.lean (#print axioms: propext, Classical.choice, Quot.sound); verifier/lean_contract.py validate_lean_statement on all 12 types`
- `sed of the parallel-branch proofs: nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-{33509b6e86,951a399d2e,479700eeeb,87895248bb,3684511996,af13c47156,d8eab44069,57440db406}/parent-supplied-natural-proof.md (cycle_im, weight_ge_one, good_points, upper_density, isodiametric, density_rep, blowup_limit, pointwise)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/Unique.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/CountablyGenerated.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/HausdorffDensityBounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/EuclideanNormalization.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaNormalization.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-truncated-com-e6c3d0d31e/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-truncated-com-e6c3d0d31e/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-truncated-com-e6c3d0d31e/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-truncated-compactness-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-951a399d2e/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-33509b6e86/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-479700eeeb/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-3684511996/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/dtc_closure_v2/lean/Types.lean`
- `/tmp/dtc_closure_v2/lean/Assembly.lean`
- `/tmp/dtc_closure_v2/lean/Reach.lean`

The snapshot (local-project, project b4d606db, Mathlib 25730c7c) has a Ch07 Contract.lean byte-identical to the workspace Contract.lean and Submission.lean. It contains no proved closure, deformation, density-comparison or rectifiability theorem. Every Mathlib lemma named in the repaired cycle_im proof exists in the snapshot and resolves after import GMT.Ch07.Submission: Vitali.exists_disjoint_subfamily_covering_enlargement (the 'meets a larger chosen ball' form needed for the finite tail), hausdorffMeasure_le_liminf_tsum, Besicovitch Lebesgue differentiation, outer regularity, Measure.measure_toMeasurable_inter_of_sFinite, LipschitzWith.hausdorffMeasure_image_le, Isometry.euclideanHausdorffMeasure_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Haar uniqueness and tendsto_of_subseq_tendsto. SimonGMT's simon_theorem_3_3, simon_theorem_3_26_i and simon_theorem_2_10 exist in the pinned library but are not importable from the contract. The sharp density comparison and the isodiametric normalization are therefore proved inline; the latter is also the accepted declaration cbr_ci_euclideanHausdorff_le_isodiametric. Mathlib defines μHE[n] = c_n•μH[n], so the isodiametric bound c_n ≤ ω_n/2ⁿ is exactly what the upper-density bound Θ* ≤ 1 needs. All twelve frozen types still elaborate, and the parent assembly compiles with only propext, Classical.choice and Quot.sound. The reused declarations are accepted with identical types. The cited accepted cbr_ci_* declarations have hypotheses identical to the sibling frozen types. No dtc_bc_tc_cl_* name is reserved.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
