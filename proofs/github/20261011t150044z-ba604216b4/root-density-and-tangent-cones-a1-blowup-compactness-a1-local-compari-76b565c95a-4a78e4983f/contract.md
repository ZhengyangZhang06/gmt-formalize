<!-- theorem-id: gmt-ch07/root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.deformation-a1.skeleton-a1 -->

## Theorem `Submission.dtc_bc_lc_fd_dfm_skeleton_deformation`

Assume, as hypotheses of the statement, (VO) the frozen type of Submission.dtc_vanish_off_support: for all P, n, U, S ∈ 𝒟_n(U) and ω ∈ 𝒟ⁿ(U) with tsupport ω disjoint from spt S, S(ω) = 0; (MR) the frozen type of Submission.cmc_massOn_eq_imRep_measure: for U open and an IMRep R representing T ∈ 𝒟_n(U), M_W(T) = R.measure(W) for every open W; (REP) the frozen type of the sibling Submission.dtc_bc_lc_fd_dfm_mass_representation_core (identical to the frozen type of cmr_exists_massRepresentation_core): for U open and T ∈ 𝒟_n(U) with M_W(T) < ∞ for every open W ⊂⊂ U there are a Borel measure μ (μ(ℝ^P ∖ U) = 0, finite on compact subsets of U) and ξ (μ-a.e. strongly measurable, |ξ(x)(α)| ≤ |α| for all x, α) with M_W(T) = μ(W) for every open W and T(ω) = ∫ξ(ω)dμ for every ω ∈ 𝒟ⁿ(U); (IMC) the frozen type of Submission.cmc_imRep_locality_restrict_sub: (a) locality of approximate tangent spaces for Borel M ⊆ M' ⊆ U with Hⁿ(M' ∩ K) < ∞ (K ⊆ U compact); (b) the restriction (M ∩ E, θ, ξ) of an IMRep to a Borel E is an IMRep representing some current; (c) A − B is integer multiplicity for integer multiplicity A, B (U open); (d) |R.orient(x)(α)| ≤ |α| for Hⁿ-a.e. x in the carrier; (SL) the frozen type of Submission.cmc_slice_mass_bounds: for T ∈ 𝒟_{k+1}(U) and ∂T represented by measures (μ, ξ), (μ', ξ') with |ξ|, |ξ'| ≤ 1 a.e. and f L-Lipschitz there are A_t(ω) = ∫_{f<t}ξ(ω)dμ, B_t(η) = ∫_{f<t}ξ'(η)dμ' with ∂A_t(η) = B_t(η) when tsupport η misses {f = t}, M_W(∂A_t − B_t) ≤ L·liminf_{h↓0} h⁻¹μ(W ∩ {t − h < f < t}) and ∫⁻_{(a,b)} M_W(∂A_t − B_t)dt ≤ L·μ(W ∩ {a < f < b}). (These are the exact frozen Lean types of the declarations named above, written as antecedents. The parent node discharges them: VO with Submission.dtc_vanish_off_support, MR from its dependency Submission.dtc_mass_eq_measure, REP with the sibling mass_rep, IMC with its dependency Submission.cmc_imRep_locality_restrict_sub, and SL with the sibling slicing.) For all P, m ∈ ℕ (n := m + 1) there is c ∈ ℝ≥0 with c ≥ 1 such that for every integer multiplicity T ∈ 𝒟_n(ℝ^P) (domain univ) with compact support, M(T) < ∞ and M(∂T) < ∞ there are Q₀ ∈ 𝒟_n(ℝ^P), R₁ ∈ 𝒟_{n+1}(ℝ^P) and S₁ ∈ 𝒟_n(ℝ^P) with: Q₀ and R₁ integer multiplicity; T − Q₀ − S₁ = ∂R₁; spt Q₀ ⊆ L_n := {x : there is a set s of coordinate indices with P ≤ n + |s| and x_i ∈ ℤ for i ∈ s} (the n-skeleton of the unit cubical grid); M(Q₀) ≤ cM(T), M(∂Q₀) ≤ cM(∂T), M(R₁) ≤ cM(T), M(S₁) ≤ cM(∂T); spt Q₀ ∪ spt R₁ ⊆ cthickening(√P, spt T) and spt ∂Q₀ ∪ spt S₁ ⊆ cthickening(√P, spt ∂T) (Metric.cthickening, the closed thickening {x : dist(x, A) ≤ √P}).

Node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.deformation-a1.skeleton-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6346

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/7438, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5183, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7469, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5198

Decomposition children: None

## Lean problem

Declaration: `Submission.dtc_bc_lc_fd_dfm_skeleton_deformation`

```lean
(∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ)) → ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) → (∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (L : NNReal), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (k + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) k, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ η : TestFormOn U k, T.boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') → LipschitzWith L f → ∃ (A : ℝ → GeometricCurrentOn U (k + 1)) (B : ℝ → GeometricCurrentOn U k), (∀ (t : ℝ) (ω : TestFormOn U (k + 1)), A t ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) ∧ (∀ (t : ℝ) (η : TestFormOn U k), B t η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') ∧ (∀ (t : ℝ) (η : TestFormOn U k), Disjoint (tsupport (η : DifferentialForm (Euclid P) k)) {x | f x = t} → (A t).boundary η = B t η) ∧ (∀ (W : Set (Euclid P)) (t : ℝ), IsOpen W → ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) ∧ (∀ (W : Set (Euclid P)) (a b : ℝ), IsOpen W → ∫⁻ t in Ioo a b, ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * μ (W ∩ {x | a < f x ∧ f x < b}))) → ∀ (P m : ℕ), ∃ c : NNReal, 1 ≤ c ∧ ∀ T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), IsIntegerMultiplicity T → IsCompact T.support → T.mass < ∞ → T.boundary.mass < ∞ → ∃ (Q₀ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (R₁ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 2)) (S₁ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), IsIntegerMultiplicity Q₀ ∧ IsIntegerMultiplicity R₁ ∧ T - Q₀ - S₁ = R₁.boundary ∧ Q₀.support ⊆ {x : Euclid P | ∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, x i = z} ∧ Q₀.mass ≤ c * T.mass ∧ Q₀.boundary.mass ≤ c * T.boundary.mass ∧ R₁.mass ≤ c * T.mass ∧ S₁.mass ≤ c * T.boundary.mass ∧ Q₀.support ∪ R₁.support ⊆ cthickening (Real.sqrt P) T.support ∧ Q₀.boundary.support ∪ S₁.support ⊆ cthickening (Real.sqrt P) T.boundary.support
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

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.deformation-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.deformation-a1.skeleton-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 6, proof of the deformation theorem 5.1, displays (1)–(25) (chapter-06.txt lines 1651–1843, printed pp. 163–166), with Lemma 5.4. The good centre, the retraction, the push-forward/homotopy calculus and the summation of integer multiplicity pieces are the sibling theorems cmcdt_good_center (GC), dtc_bc_lc_fd_dfm_skeleton_retraction (RET), dtc_bc_lc_fd_dfm_lipschitz_pushforward_homotopy (PF) and cmcdt_im_series (IMS). Simon's currents T − T_ε are decomposed into dyadic shells (his (17)), and each shell is deformed with its own Lipschitz extension of ψ. Integrality of Q₀ and R₁ is obtained by summing the integer multiplicity shell contributions with IMS, in place of Simon's appeal to 3.13. The statement is that of cmcdt_skeleton_deformation (compactness_of_minimizing_currents branch, not yet accepted) except that the hypothesis REP is the representation theorem without the absolute-continuity clause (that clause is never used); the argument below is the one written and reviewed for that statement, with the choice of good radii (step 5) carried out with Stieltjes measures instead of the fundamental theorem of calculus for monotone functions, which is not in the frozen import closure.

Notation. n := m + 1. (VO), (MR), (REP), (IMC), (SL) are the five displayed hypotheses (frozen types of Submission.dtc_vanish_off_support, Submission.cmc_massOn_eq_imRep_measure, the sibling Submission.dtc_bc_lc_fd_dfm_mass_representation_core, Submission.cmc_imRep_locality_restrict_sub and Submission.cmc_slice_mass_bounds). All currents are on univ in ℝ^P. For currents A, B, “A + B” abbreviates A − (0 − B) (the contract's subtraction is pointwise, and currents are equal when their values agree, GeometricCurrentOn.ext). ‖ω‖ := sup_x|ω(x)|, and |X(ω)| ≤ M(X)‖ω‖ for every current X. NC_k := k-currents with compact support, finite mass and (k ≥ 1) finite boundary mass; NC_k is closed under differences. Support facts used below (all from the definitions and (VO)): spt(A − B) ⊆ spt A ∪ spt B; spt ∂A ⊆ spt A; spt 0 = ∅; a current that vanishes on every test form whose support is disjoint from a closed set E has support in E (every x ∉ E has a ball with compact closure disjoint from E). L_n := {x : ∃ s, P ≤ n + |s|, x_i ∈ ℤ (i ∈ s)} is closed (a finite union of the closed sets {x : x_i ∈ ℤ, i ∈ s}).

1. Trivial cases. If n ≥ P then L_n = ℝ^P (s = ∅). Take Q₀ := T, R₁ := 0, S₁ := 0 and c := 1: T − T − 0 = 0 = ∂0, T and 0 are integer multiplicity, the mass bounds are equalities or 0 ≤ ·, and spt T ⊆ cthickening(√P, spt T), spt ∂T ⊆ cthickening(√P, spt ∂T), spt 0 = ∅. From now on n < P, so RET and GC apply. Let c_R > 0 be RET's constant, C_G := (GC's constant) + 1 > 0, c₄ := 8(1 + √P c_R), and
 c := max(1, c₄ⁿ(1 + 2C_G), √P 2ⁿ c₄ⁿ(1 + 2C_G), √P (2c₄)^{n−1}(1 + 2C_G), c₄^{n−1}(1 + 2C_G)),
 which depends only on P and m. Let (push, homot) be the operators given by PF applied to (VO), (MR), (REP), (IMC). The zero current (in every degree) is integer multiplicity: the IMRep with empty carrier, multiplicity 0 and orientation 0 represents it (∅ is Borel and countably rectifiable, the remaining fields hold vacuously, and the representing integral over ∅ is 0). Let T be as in the statement. If M(T) = 0 then T = 0 (|T(ω)| ≤ M(T)‖ω‖), ∂T = 0, and Q₀ = R₁ = S₁ = 0 work. Assume M(T) > 0.

2. Measures. Let R_T = (M, θ, ξ) be an IMRep of T and μ_T := R_T.measure. By (MR), μ_T(W) = M_W(T) for open W, so μ_T(ℝ^P) = M(T) < ∞, and μ_T(ℝ^P ∖ spt T) = 0 by (VO). Further:
 - T(ω) = ∫ ξ(ω) dμ_T (definition of Represents and of the density measure);
 - ξ is μ_T-a.e. strongly measurable (μ_T ≪ Hⁿ⌞M);
 - |ξ(x)(α)| ≤ |α| μ_T-a.e. by (IMC)(d);
 - μ_T is finite on compact sets.
 Since M(∂T) < ∞, (REP) (U = univ) gives μ_∂, ξ_∂ with μ_∂(W) = M_W(∂T) for open W, |ξ_∂| ≤ 1 and ∂T(η) = ∫ ξ_∂(η) dμ_∂; moreover μ_∂(ℝ^P) = M(∂T) and μ_∂(ℝ^P ∖ spt ∂T) = 0 by (VO).

3. Good centre (Simon (1)–(7); GC). GC applied to the finite measures μ_T, μ_∂ gives a with |a_i − 1/2| < 1/4 such that, for d := dist(·, L*(a)), L*(a) the set of y with at least m + 2 coordinates in a_i + ℤ,
 (6) μ_T({d < r}) ≤ C_G r^{n+1} M(T), (7) μ_∂({d < r}) ≤ C_G r^{n+1} M(∂T) for r ∈ (0, 1/4].
 In particular μ_T({d = 0}) = μ_∂({d = 0}) = 0.

4. Retraction (RET). RET with this a gives ψ with: if d(x) > 0 then ψ(x) ∈ L_n and |ψ(x) − x| ≤ √P; and ψ is (c_R/r)-Lipschitz on {d ≥ r} for r ∈ (0, 1/4]. For r ∈ (0, 1/4] let φ_r be the componentwise McShane extension of ψ|{d ≥ r} (Mathlib LipschitzOnWith.extend_real for each coordinate x ↦ ψ(x)_i, which is (c_R/r)-Lipschitz on {d ≥ r}). Then φ_r : ℝ^P → ℝ^P is (√P c_R/r)-Lipschitz and φ_r = ψ on {d ≥ r}. Put Λ(r) := max(1, √P c_R/r); id and φ_r are Λ(r)-Lipschitz, and Λ(r) ≤ c₄2^j whenever r ≥ 2^{−j−3}.

5. Slicing and good radii (Simon (8)–(10)). Apply (SL) with U = univ, k = m, T, μ := μ_T, μ' := μ_∂, ξ, ξ' := ξ_∂, f := d, L := 1 (d is 1-Lipschitz; the measures are finite on compact sets, and the a.e. bounds and representations hold by 2). This gives currents A_t ∈ 𝒟_n, B_t ∈ 𝒟_{n−1} with A_t(ω) = ∫_{d<t} ξ(ω) dμ_T, B_t(η) = ∫_{d<t} ξ_∂(η) dμ_∂, ∂A_t(η) = B_t(η) when tsupport η ∩ {d = t} = ∅, and, for Z_t := ∂A_t − B_t, M(Z_t) ≤ liminf_{h↓0} h^{−1}μ_T({t − h < d < t}). If m ≥ 1, write m = k' + 1 and apply (SL) also to ∂T, which has degree k' + 1 (k := k' = m − 1, μ := μ_∂, ξ := ξ_∂, μ' := 0, ξ' := 0, valid because ∂∂T = 0; f := d). Its A'_t has the same values as B_t, so A'_t = B_t; its B'_t = 0; and M(∂B_t) ≤ liminf_{h↓0} h^{−1}μ_∂({t − h < d < t}).
 Let G(t) := μ_T({d ≤ t}) and G_∂(t) := μ_∂({d ≤ t}) for t ∈ ℝ. They are nondecreasing, bounded and right-continuous (continuity from above of finite measures), i.e. Stieltjes functions, and their Stieltjes measures satisfy G.measure(Ioo(a, b)) = leftLim G b − G(a) = μ_T({a < d < b}) (Mathlib StieltjesFunction.measure_Ioo; leftLim G b = μ_T({d < b}) because {d ≤ b − 1/j} increases to {d < b} and finite measures are continuous from below), likewise for G_∂. By Mathlib StieltjesFunction.ae_hasDerivAt, for Lebesgue-a.e. t ∈ ℝ the functions G and G_∂ are differentiable at t, with derivatives D(t) := (rnDeriv G.measure volume t).toReal and D_∂(t) := (rnDeriv G_∂.measure volume t).toReal. At such t, for h > 0, {t − h < d < t} ⊆ {t − h < d ≤ t}, so μ_T({t − h < d < t}) ≤ G(t) − G(t − h), i.e. ENNReal.ofReal(h⁻¹)·μ_T({t − h < d < t}) ≤ ENNReal.ofReal((G(t) − G(t − h))/h). Since G has derivative D(t) at t, the left difference quotients (G(t) − G(t − h))/h tend to D(t) as h ↓ 0, so the right side tends to ENNReal.ofReal(D(t)) along 𝓝[>] 0, and the liminf of the left side is at most ENNReal.ofReal(D(t)). Hence M(Z_t) ≤ ENNReal.ofReal(D(t)), and likewise M(∂B_t) ≤ ENNReal.ofReal(D_∂(t)) < ∞ (if m ≥ 1). (G and G_∂ are bundled as elements of StieltjesFunction ℝ: monotone and right-continuous.)
 For ν ≥ 0 let ρ_ν := 2^{−ν−2} ≤ 1/4. The density ρ ↦ rnDeriv G.measure volume ρ is measurable (Mathlib Measure.measurable_rnDeriv), and by Mathlib Measure.withDensity_rnDeriv_le with withDensity_apply,
 ∫⁻_{Ioo(ρ_ν/2, ρ_ν)} rnDeriv G.measure volume dt ≤ G.measure(Ioo(ρ_ν/2, ρ_ν)) = μ_T({ρ_ν/2 < d < ρ_ν}) ≤ μ_T({d < ρ_ν}) ≤ C_G ρ_ν^{n+1} M(T)
 by (6). Put λ_ν := 4C_Gρ_νⁿM(T) > 0 (M(T) > 0 by step 1). By Markov's inequality (Mathlib mul_meas_ge_le_lintegral₀), the set of t ∈ (ρ_ν/2, ρ_ν) with rnDeriv G.measure volume t ≥ ENNReal.ofReal λ_ν has Lebesgue measure ≤ C_Gρ_ν^{n+1}M(T)/λ_ν = ρ_ν/4. As (ρ_ν/2, ρ_ν) has length ρ_ν/2 > ρ_ν/4 and the points where G or G_∂ is not differentiable form a null set, there is r_ν ∈ (ρ_ν/2, ρ_ν) at which G and G_∂ are differentiable and rnDeriv G.measure volume r_ν < ENNReal.ofReal λ_ν, so D(r_ν) ≤ λ_ν. Hence
 (10) M(Z_{r_ν}) ≤ 4C_Gρ_νⁿM(T) and M(∂B_{r_ν}) < ∞ (if m ≥ 1).
 (Simon also takes radii with μ_T({d = r_ν}) = 0; this is not needed below because the shells are taken half-open.)
 Since r_{ν+1} < ρ_{ν+1} = ρ_ν/2 < r_ν, the r_ν strictly decrease to 0, r_ν ≤ 1/4 and r_ν > 2^{−ν−3}. Write A_ν := A_{r_ν}, B_ν := B_{r_ν}, Z_ν := Z_{r_ν}.

6. The pieces (Simon (8), (17)). For j ≥ 0 define W_0 := T − A_0, W_j := A_{j−1} − A_j (j ≥ 1), D_0 := ∂T − B_0, D_j := B_{j−1} − B_j (j ≥ 1). Let E_0 := {d ≥ r_0} and E_j := {r_j ≤ d < r_{j−1}} (j ≥ 1).
 (6a) W_j(ω) = ∫_{E_j} ξ(ω) dμ_T and D_j(η) = ∫_{E_j} ξ_∂(η) dμ_∂. Hence M(W_0) ≤ M(T) and M(D_0) ≤ M(∂T), and for j ≥ 1, by (6), (7) with r_{j−1} < ρ_{j−1} = 2^{−j−1}: M(W_j) ≤ C_G 2^{−(j+1)(n+1)}M(T) and M(D_j) ≤ C_G 2^{−(j+1)(n+1)}M(∂T).
 (6b) W_j is integer multiplicity: (IMC)(b) with E := E_j gives a current represented by (M ∩ E_j, θ, ξ), whose values are ∫_{E_j} ξ(ω) dμ_T = W_j(ω).
 (6c) Supports: spt W_j ⊆ spt T ∩ closure(E_j) ⊆ spt T ∩ {d ≥ r_j} and spt D_j ⊆ spt ∂T ∩ {d ≥ r_j}. Indeed, if ω vanishes on spt T ∩ closure(E_j), the integrand of (6a) vanishes μ_T-a.e. on E_j (μ_T(ℝ^P ∖ spt T) = 0), so W_j vanishes on forms supported off this closed set. spt Z_j ⊆ {d = r_j} by the third clause of (SL). Also spt A_t ⊆ spt T and spt B_t ⊆ spt ∂T ⊆ spt T, so all supports above are compact.
 (6d) Boundaries: ∂A_t = B_t + Z_t, hence ∂W_0 = D_0 − Z_0 and ∂W_j = D_j + Z_{j−1} − Z_j (j ≥ 1). For m ≥ 1, ∂D_0 = −∂B_0, ∂D_j = ∂B_{j−1} − ∂B_j and ∂Z_j = −∂B_j have finite mass by (10). Hence W_j ∈ NC_n and D_j, Z_j ∈ NC_{n−1} (for m = 0 there is no boundary condition in degree 0).
 (6e) Σ_{j=0}^{N} W_j = T − A_N and M(A_N) ≤ μ_T({d < r_N}) ≤ C_G ρ_N^{n+1}M(T) → 0.

7. Deforming the pieces (Simon (11)–(20)). For j ≥ 0 let φ_j := φ_{r_j} and Λ_j := Λ(r_j) ≤ c₄2^j (as r_j > 2^{−j−3}); Λ_j ≤ Λ_{j+1}. Then φ_j = ψ on spt W_j ∪ spt D_j ∪ spt Z_j ⊆ {d ≥ r_j}, and φ_{j+1} = ψ = φ_j on spt Z_j ⊆ {d = r_j} ⊆ {d ≥ r_{j+1}}. Define
 V_j := push n φ_j W_j, H_j := homot n id φ_j W_j, Y_j := push (n−1) φ_j D_j, E'_j := homot (n−1) id φ_j D_j, L_j := push (n−1) φ_j Z_j, K_j := homot (n−1) id φ_j Z_j.
 - By PF (locality, maps Λ_{j+1}-Lipschitz): push (n−1) φ_{j+1} Z_j = L_j and homot (n−1) id φ_{j+1} Z_j = K_j.
 - By PF (identity and homotopy formula in degree n = m + 1, with F = id, G = φ_j, Λ = Λ_j): V_j − W_j − homot (n−1) id φ_j (∂W_j) = ∂H_j.
 - By PF (linearity, all pieces in NC_{n−1}) and (6d): homot (n−1) id φ_j (∂W_0) = E'_0 − K_0 and homot (n−1) id φ_j (∂W_j) = E'_j + K_{j−1} − K_j (j ≥ 1).
 - By PF (boundary commutation and linearity): ∂V_0 = Y_0 − L_0 and ∂V_j = Y_j + L_{j−1} − L_j (j ≥ 1).
 Summing over j = 0,…,N (telescoping):
 (S1) Σ_{j≤N}(V_j − W_j − ∂H_j) = Σ_{j≤N}E'_j − K_N, (S2) ∂(Σ_{j≤N}V_j) = Σ_{j≤N}Y_j − L_N.
 W_j is integer multiplicity, so by the integrality clause of PF (degree k + 1 = n), push n φ_j W_j = V_j is integer multiplicity (with F := φ_j) and homot n id φ_j W_j = H_j is integer multiplicity (with F := id, G := φ_j).
 Estimates (PF mass bounds; |φ_j(x) − x| = |ψ(x) − x| ≤ √P on the supports, since d > 0 there):
 M(V_0) ≤ c₄ⁿM(T), M(V_j) ≤ c₄ⁿ2^{jn}C_G2^{−(j+1)(n+1)}M(T) ≤ c₄ⁿC_G2^{−j}M(T);
 M(H_0) ≤ √P(2c₄)ⁿM(T), M(H_j) ≤ √P(2c₄)ⁿC_G2^{−j}M(T);
 M(Y_0) ≤ c₄^{n−1}M(∂T), M(Y_j) ≤ c₄^{n−1}C_G2^{−2j}M(∂T); M(E'_0) ≤ √P(2c₄)^{n−1}M(∂T), M(E'_j) ≤ √P(2c₄)^{n−1}C_G2^{−2j}M(∂T);
 M(L_N) ≤ Λ_{N}^{n−1}M(Z_N) ≤ c₄^{n−1}2^{N(n−1)}·4C_G2^{−(N+2)n}M(T) ≤ 4C_Gc₄^{n−1}2^{−N}M(T) → 0, and likewise M(K_N) ≤ √P(2Λ_N)^{n−1}M(Z_N) → 0.
 Hence Σ_j M(V_j) ≤ c₄ⁿ(1 + 2C_G)M(T), Σ_j M(H_j) ≤ √P(2c₄)ⁿ(1 + 2C_G)M(T), Σ_j M(E'_j) ≤ √P(2c₄)^{n−1}(1 + 2C_G)M(∂T) and Σ_j M(Y_j) ≤ c₄^{n−1}(1 + 2C_G)M(∂T).

8. Limits (Simon (19)–(21), (24)–(25); IMS).
 - IMS (degree n = m + 1) gives Q₀ with Q₀(ω) = Σ_j V_j(ω): integer multiplicity, M(Q₀) ≤ Σ_j M(V_j) ≤ cM(T), spt Q₀ ⊆ closure ⋃_j spt V_j.
 - By (IMC)(c), 0 − H_j is integer multiplicity (0 and H_j are), with M(0 − H_j) ≤ M(H_j). IMS (degree m + 2) gives R₁ with R₁(ζ) = Σ_j(0 − H_j)(ζ): integer multiplicity, M(R₁) ≤ cM(T), spt R₁ ⊆ closure ⋃_j spt H_j.
 - IMS (degree m + 1, existence part) gives S₁ with S₁(ω) = Σ_j(0 − E'_j)(ω), M(S₁) ≤ cM(∂T), spt S₁ ⊆ closure ⋃_j spt E'_j.
 Identity (21). Evaluate (S1) at ω: Σ_{j≤N}V_j(ω) − T(ω) + A_N(ω) − Σ_{j≤N}H_j(dω) = Σ_{j≤N}E'_j(ω) − K_N(ω). As N → ∞, A_N(ω) → 0 and K_N(ω) → 0 (masses → 0), so Q₀(ω) − T(ω) + R₁(dω) = −S₁(ω), i.e. (T − Q₀ − S₁)(ω) = ∂R₁(ω). Hence T − Q₀ − S₁ = R₁.boundary.
 Boundary mass (25). The finite sums Ŝ_N := Σ_{j≤N}V_j converge weakly to Q₀, so ∂Ŝ_N converge weakly to ∂Q₀ (SimonGMT WeaklyConvergesOn.boundary), and M(∂Q₀) ≤ liminf_N M(∂Ŝ_N) (SimonGMT WeaklyConvergesOn.massOn_le_liminf). By (S2), M(∂Ŝ_N) ≤ Σ_jM(Y_j) + M(L_N), so M(∂Q₀) ≤ c₄^{n−1}(1 + 2C_G)M(∂T) ≤ cM(∂T).

9. Supports (Simon (22)–(23)).
 - spt V_j ⊆ φ_j(spt W_j) = ψ(spt W_j) ⊆ L_n ∩ cthickening(√P, spt T) (RET, as d > 0 and the points lie in spt T). Both sets are closed, so spt Q₀ ⊆ L_n ∩ cthickening(√P, spt T).
 - spt H_j ⊆ {x + t(φ_j(x) − x) : x ∈ spt W_j, t ∈ [0,1]} ⊆ cthickening(√P, spt T) (PF), so spt R₁ ⊆ cthickening(√P, spt T) (spt(0 − H_j) ⊆ spt H_j).
 - Likewise spt E'_j ⊆ cthickening(√P, spt ∂T), so spt S₁ ⊆ cthickening(√P, spt ∂T).
 - Finally, if tsupport ω ∩ cthickening(√P, spt ∂T) = ∅, then Y_j(ω) = 0 for all j (spt Y_j ⊆ φ_j(spt D_j) ⊆ cthickening(√P, spt ∂T); (VO)). So ∂Ŝ_N(ω) = −L_N(ω) → 0 and ∂Q₀(ω) = lim ∂Ŝ_N(ω) = 0; hence spt ∂Q₀ ⊆ cthickening(√P, spt ∂T).

10. Q₀, R₁, S₁ satisfy all conclusions with the constant c of 1 (c ≥ 1): integrality (8), the identity (8), spt Q₀ ⊆ L_n (9), the four mass bounds (7)–(8) and the support inclusions (9). ∎

## Key steps

1. Trivial cases n ≥ P (Q₀ := T) and T = 0; constants from RET and GC.
2. Measures μ_T (IMRep, MR, VO) and μ_∂ (REP); good centre a with μ_T, μ_∂({d < r}) ≤ C r^{n+1}·mass (GC).
3. Retraction ψ (RET) and its McShane extensions φ_r with Lipschitz constant √P c_R/r.
4. Slicing (SL); the Stieltjes functions G(t) = μ_T({d ≤ t}), G_∂(t) = μ_∂({d ≤ t}) are a.e. differentiable with derivative the Radon–Nikodym density of their Stieltjes measures; the bound ∫⁻ density ≤ μ_T({ρ/2 < d < ρ}) and Markov's inequality give radii r_ν ∈ (ρ_ν/2, ρ_ν) with M(Z_{r_ν}) ≤ 4Cρ_νⁿM(T) and finite boundary slices.
5. Dyadic shells W_j, D_j (integer multiplicity, normal, supports in {d ≥ r_j}) with ∂W_j = D_j + Z_{j−1} − Z_j.
6. PF: deformations V_j, homotopies H_j, E'_j; telescoping of the slice terms by locality; geometric mass estimates.
7. IMS: Q₀ := ΣV_j and R₁ := Σ(0 − H_j) integer multiplicity, S₁ := Σ(0 − E'_j); identity T − Q₀ − S₁ = ∂R₁; M(∂Q₀) by lower semicontinuity.
8. Supports: ψ maps into L_n and moves points by ≤ √P; homotopy supports; ∂Q₀ via vanishing of the deformed ∂T-pieces and of the slice terms in the limit.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (mode local-project, project b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `rg -n -i 'deform|skeleton|retraction|homotop|latticeFace|flatDistance|cube_bv|polyhedral' local-references/123e8435b4a2469b/project/GMT/Ch07 -g '*.lean' (no match)`
- `rg -n 'def latticeFace|def IsLatticeChain|def DeformationTheorem|theorem main_theorem' local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean; sed -n 260,300p (DeformationTheorem = Simon 5.3 as a sorry-based definition in namespace GMT.Ch06; formulation reference only)`
- `rg -n 'theorem measure_Ioo' mathlib/Mathlib/MeasureTheory/Measure/Stieltjes.lean; rg -n 'ae_hasDerivAt' mathlib/Mathlib/Analysis/Calculus/Monotone.lean; rg -n 'theorem integral_lineDeriv_mul_eq' mathlib/Mathlib/Analysis/Calculus/Rademacher.lean; rg -n 'theorem ae_tendsto_average_norm_sub' mathlib/Mathlib/MeasureTheory/Covering/; rg -n 'theorem LipschitzOnWith.extend_real' mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean; rg -n 'theorem exists_partition_approximatesLinearOn_of_hasFDerivWithinAt' mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean (all found in the snapshot)`
- `rg -n 'area_image_criticalSet_eq_zero|weighted_area_formula_lipschitz_injOn|area_image_nondifferentiable_eq_zero' .lake/packages/simongmt/Poincare/SimonGMT/Chapter02 (AreaCritical.lean:185, AreaLipschitz.lean:45 and :101); grep boundary_boundary / WeaklyConvergesOn.boundary / WeaklyConvergesOn.massOn_le_liminf in .lake/packages/simongmt/Poincare/SimonGMT/Chapter06 (Currents.lean:365, :389; Mass.lean:100)`
- `python3 -I scans of the run dag.json: statuses, candidate commits, updated_at and byte comparison of lean_statement for cmcdt_good_center, cmcdt_dilation_pushforward, cmcdt_im_series, cmr_vector_riesz_representation, ptd_piece_image_approxTangent_ae and cmc_slice_mass_bounds (all accepted, identical); subtrees of deformation_theorem-a1 and mass_representation-a1 (cmc_deformation_theorem, cmcdt_skeleton_retraction, cmcdt_cube_bv_median, cmcdt_lipschitz_pushforward_homotopy, cmcdt_skeleton_deformation, cmcdt_face_replacement and cmr_exists_massRepresentation_core not accepted); freedom of the six new names; inherited-prerequisite computation for this node (dtc_vanish_off_support)`
- `git show <candidate>:GMT/Ch07/Submission.lean for 42b2a510, fba5d30a, 9b823b56, 5d41e1d4, 6ae39d3e and a1c12d76 (types byte-identical, the only sorry is the root theorem, no axiom declarations); grep of the cited helpers in 9b823b56; git show 58a0bf378 (adds import Poincare.SimonGMT.Chapter02.AreaLipschitz)`
- `throwaway clone /tmp/dfm4_sim: from 4eedbcf, git merge --no-ff of 2af75d69, bff81d31, 44ef61f7, then 9b823b56 + 6ae39d3e (pushforward base), 5d41e1d4 + 9b823b56 (mass_rep base), or all six reused candidates (parent base); de-duplicate and run lake env lean on the merged file (no errors)`
- `lake env lean on /tmp/dfm4_work/lean/{Assembly,Challenges,AvailAll,AvailAreaAll,AvailReuse,Avail6}.lean; python3 -I /tmp/dfm4_scripts/check_assembly.py; verifier/lean_contract.py validate_lean_statement`
- `sed -n 1440,1560p book/chapter-06.txt (Simon 5.1–5.4); runtime source /runtime/flows/gmt-claude-60a586062ee7/_recursive_lean/{runtime.py (_existing_lean_name_problem, _accepted_checkpoint, _decompose, _overlay_accepted_children, _merge_candidate_history, _drop_merged_duplicates), store.py (update, refresh), inherited.py, leaf_verification.py, prompts.py}`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Stieltjes.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-57991f1e6d/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-57991f1e6d/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-57991f1e6d/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-57991f1e6d/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/cluster-state/logs/gmt-ch07/5b793d9d6e634c829bcf09ec49beaff8.log`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-good-center-a1/accepted-candidate.json`
- `/runtime/flows/gmt-claude-60a586062ee7/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-60a586062ee7/_recursive_lean/store.py`
- `/runtime/flows/gmt-claude-60a586062ee7/_recursive_lean/inherited.py`
- `/runtime/flows/gmt-claude-60a586062ee7/_recursive_lean/leaf_verification.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/dfm4_work/lean/Assembly.lean`
- `/tmp/dfm4_work/lean/Challenges.lean`
- `/tmp/dfm4_work/MergedAll.lean`

Neither the pinned snapshot nor the workspace has a deformation theorem usable from GMT.Ch07. The snapshot's Ch06 DeformationTheorem is a sorry-based formulation in namespace GMT.Ch06 (formulation reference only). Mathlib has no Federer–Fleming theorem. The equivalent cmc_deformation_theorem and its large pieces are not accepted, so they cannot be shared. All Mathlib and SimonGMT lemmas cited by the new leaves exist at the pinned revisions; the AreaLipschitz lemmas are imported through the accepted piece_tangent candidate. The six reused declarations were accepted before this attempt began (22:58:17Z), with byte-identical types and clean candidates. This makes the cmcdt_good_center reuse valid under runtime.py _existing_lean_name_problem; attempt 3 failed only because its DAG snapshot predated the 22:12:22Z acceptance. The merged bases compile, and the Lean assembly derives this node's exact type from the children with the standard axioms only.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
