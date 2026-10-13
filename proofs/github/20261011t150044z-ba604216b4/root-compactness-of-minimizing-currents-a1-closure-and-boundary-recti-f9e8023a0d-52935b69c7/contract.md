<!-- theorem-id: gmt-ch07/root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_succ-a1.localize-a1 -->

## Theorem `Submission.cbrcs_localize_at_point`

Assume (REP), (MR), (IMC), (SL) and (TOOLS); they appear verbatim as hypotheses of the Lean statement. (REP), (MR), (IMC), (SL) are the exact frozen statements of cmc_exists_massRepresentation, cmc_massOn_eq_imRep_measure, cmc_imRep_locality_restrict_sub and cmc_slice_mass_bounds (dependencies of the grandparent node), and (TOOLS) = (T1) ∧ (T2) ∧ (MM) is the exact frozen statement of cbr_measure_convergence_tools (a dependency of the parent cbr_closure_succ). In words: (REP) a current X ∈ 𝒟_n(U), U open, with M_W(X) < ∞ for every open W ⊂⊂ U has a representation (μ, ξ): μ(ℝ^P ∖ U) = 0, μ(K) < ∞ for compact K ⊆ U, μ(W) = M_W(X) for open W, ξ μ-a.e. strongly measurable with |ξ(x)(α)| ≤ |α| for all x and α, and X(ω) = ∫ ξ(ω) dμ for ω ∈ 𝒟ⁿ(U) (plus an Hⁿ-null-set clause not used here); (MR) M_W(X) = R.measure(W) for every IMRep R in open U representing X and every open W; (IMC) (a) locality of approximate tangent spaces, (b) for an IMRep R in open U and a Borel set E there are a current A and an IMRep R′ representing A with carrier R.carrier ∩ E, multiplicity R.mult and orientation R.orient, (c) differences of IM currents are IM, (d) for every IMRep R, |R.orient(x)(α)| ≤ |α| for Hⁿ⌞R.carrier-a.e. x and all α; (SL) for X ∈ 𝒟_{k+1}(U), U open, with admissible representations (μ, ξ) of X and (μ′, ξ′) of ∂X (measures finite on compact subsets of U, a.e. strongly measurable fields with a.e. bound |·| ≤ 1) and an L-Lipschitz f there are currents A_t ∈ 𝒟_{k+1}(U), B_t ∈ 𝒟_k(U) with A_t(ω) = ∫_{f<t} ξ(ω) dμ, B_t(η) = ∫_{f<t} ξ′(η) dμ′, ∂A_t(η) = B_t(η) when tsupport η ∩ {f = t} = ∅, M_W(∂A_t − B_t) ≤ L·liminf_{h↓0} h⁻¹μ(W ∩ {t − h < f < t}) for open W, and an integrated bound; (T1) a sequence of measures with sup_j μ_j(K) < ∞ for compact K ⊆ U (U open) has a subsequence μ_{φ(j)} and a measure μ with μ(K) < ∞ and limsup_j μ_{φ(j)}(K) ≤ μ(K) for compact K ⊆ U (and further properties); (T2) if X_j ⇀ X in 𝒟_k(U), (μ_j, ξ_j) and (μ_X, ξ_X) are admissible representations of X_j and X, μ is finite on compact subsets of U with limsup_j μ_j(K) ≤ μ(K), f is continuous and μ{f = t} = 0, then ∫_{f<t} ξ_j(ω) dμ_j → ∫_{f<t} ξ_X(ω) dμ_X for every ω ∈ 𝒟^k(U); (MM) if μ_j(G ∩ {a < f < b}) < ∞, f is continuous and Z_j(t) ≤ L·liminf_{h↓0} h⁻¹μ_j(G ∩ {t − h < f < t}) for t ∈ (a, b), then there is a measurable g ≥ 0 with liminf_j Z_j(t) ≤ g(t) for L¹-a.e. t ∈ (a, b) and ∫_{(a,b)} g ≤ L·liminf_j μ_j(G ∩ {a < f < b}). Let d, P ∈ ℕ, U ⊆ ℝ^P open, T_j, T ∈ 𝒟_{d+1}(U) with every T_j integer multiplicity, sup_j (M_W(T_j) + M_W(∂T_j)) < ∞ for every open W with compact closure contained in U (boundaryMassOn(T_j, W) = M_W(∂T_j) in degree d + 1), T_j ⇀ T in U, and x₀ ∈ U. Then there are r > 0 with closedBall(x₀, r) ⊆ U, currents S_j ∈ 𝒟_{d+1}(U), IMReps R′_j in U and A ∈ 𝒟_{d+1}(U) such that: R′_j represents S_j and R′_j.carrier ⊆ closedBall(x₀, r); S_j(ω) = 0 whenever tsupport ω is disjoint from closedBall(x₀, r); sup_j (M(S_j) + M(∂S_j)) < ∞ (total masses in U, M = massOn U); S_j ⇀ A in U; and A(ω) = T(ω) for every ω ∈ 𝒟^{d+1}(U) with tsupport ω ⊆ ball(x₀, r).

Node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_succ-a1.localize-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4843

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4710, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4704, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4695, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1258, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1286, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5042

Decomposition children: None

## Lean problem

Declaration: `Submission.cbrcs_localize_at_point`

```lean
(∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) → (∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (L : NNReal), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (k + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) k, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ η : TestFormOn U k, T.boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') → LipschitzWith L f → ∃ (A : ℝ → GeometricCurrentOn U (k + 1)) (B : ℝ → GeometricCurrentOn U k), (∀ (t : ℝ) (ω : TestFormOn U (k + 1)), A t ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) ∧ (∀ (t : ℝ) (η : TestFormOn U k), B t η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') ∧ (∀ (t : ℝ) (η : TestFormOn U k), Disjoint (tsupport (η : DifferentialForm (Euclid P) k)) {x | f x = t} → (A t).boundary η = B t η) ∧ (∀ (W : Set (Euclid P)) (t : ℝ), IsOpen W → ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) ∧ (∀ (W : Set (Euclid P)) (a b : ℝ), IsOpen W → ∫⁻ t in Ioo a b, ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * μ (W ∩ {x | a < f x ∧ f x < b}))) → ((∀ (P : ℕ) (U : Set (Euclid P)) (μs : ℕ → Measure (Euclid P)), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ⨆ j, μs j K < ∞) → ∃ (φ : ℕ → ℕ) (μ : Measure (Euclid P)), StrictMono φ ∧ μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U → Tendsto (fun j => ∫ x, f x ∂(μs (φ j))) atTop (𝓝 (∫ x, f x ∂μ))) ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → limsup (fun j => μs (φ j) K) atTop ≤ μ K) ∧ (∀ G : Set (Euclid P), IsOpen G → G ⊆ U → μ G ≤ liminf (fun j => μs (φ j) G) atTop)) ∧ (∀ (P k : ℕ) (U : Set (Euclid P)) (Xs : ℕ → GeometricCurrentOn U k) (X : GeometricCurrentOn U k) (μs : ℕ → Measure (Euclid P)) (ξs : ℕ → Euclid P → MultiVector P k) (μX μ : Measure (Euclid P)) (ξX : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (t : ℝ), IsOpen U → Continuous f → WeaklyConvergesOn Xs X → (∀ j, ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μs j K < ∞) → (∀ j, AEStronglyMeasurable (ξs j) (μs j)) → (∀ j, ∀ᵐ x ∂(μs j), ∀ α : Covector (Euclid P) k, |ξs j x α| ≤ covectorEuclideanNorm α) → (∀ j, ∀ ω : TestFormOn U k, Xs j ω = ∫ x, ξs j x ((ω : DifferentialForm (Euclid P) k) x) ∂(μs j)) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μX K < ∞) → AEStronglyMeasurable ξX μX → (∀ᵐ x ∂μX, ∀ α : Covector (Euclid P) k, |ξX x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U k, X ω = ∫ x, ξX x ((ω : DifferentialForm (Euclid P) k) x) ∂μX) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → limsup (fun j => μs j K) atTop ≤ μ K) → μ {x | f x = t} = 0 → ∀ ω : TestFormOn U k, Tendsto (fun j => ∫ x in {x | f x < t}, ξs j x ((ω : DifferentialForm (Euclid P) k) x) ∂(μs j)) atTop (𝓝 (∫ x in {x | f x < t}, ξX x ((ω : DifferentialForm (Euclid P) k) x) ∂μX))) ∧ (∀ (P : ℕ) (μs : ℕ → Measure (Euclid P)) (f : Euclid P → ℝ) (G : Set (Euclid P)) (a b : ℝ) (L : NNReal) (Z : ℕ → ℝ → ℝ≥0∞), Continuous f → (∀ j, μs j (G ∩ {x | a < f x ∧ f x < b}) < ∞) → (∀ (j : ℕ) (t : ℝ), t ∈ Ioo a b → Z j t ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μs j (G ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) → ∃ g : ℝ → ℝ≥0∞, Measurable g ∧ (∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo a b → liminf (fun j => Z j t) atTop ≤ g t) ∧ ∫⁻ t in Ioo a b, g t ≤ (L : ℝ≥0∞) * liminf (fun j => μs j (G ∩ {x | a < f x ∧ f x < b})) atTop)) → ∀ (d P : ℕ) (U : Set (Euclid P)) (Ts : ℕ → GeometricCurrentOn U (d + 1)) (T : GeometricCurrentOn U (d + 1)) (x₀ : Euclid P), IsOpen U → (∀ j, IsIntegerMultiplicity (Ts j)) → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → ⨆ j, ((Ts j).massOn W + boundaryMassOn (Ts j) W) < ∞) → WeaklyConvergesOn Ts T → x₀ ∈ U → ∃ (r : ℝ) (Ss : ℕ → GeometricCurrentOn U (d + 1)) (Rs : ℕ → IMRep U (d + 1)) (A : GeometricCurrentOn U (d + 1)), 0 < r ∧ closedBall x₀ r ⊆ U ∧ (∀ j, (Rs j).Represents (Ss j) ∧ (Rs j).carrier ⊆ closedBall x₀ r) ∧ (∀ (j : ℕ) (ω : TestFormOn U (d + 1)), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (d + 1))) (closedBall x₀ r) → Ss j ω = 0) ∧ ⨆ j, ((Ss j).mass + (Ss j).boundary.mass) < ∞ ∧ WeaklyConvergesOn Ss A ∧ ∀ ω : TestFormOn U (d + 1), tsupport (ω : DifferentialForm (Euclid P) (d + 1)) ⊆ ball x₀ r → A ω = T ω
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

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_succ-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_succ-a1.localize-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the parent-supplied proof of cbr_closure_succ, steps 1–7 (Part V, V2 of the grandparent proof; Simon Ch. 6, Remark 8.3(1)), specialised to one point x₀. (REP), (MR), (IMC), (SL), (TOOLS) = (T1) ∧ (T2) ∧ (MM) are hypotheses (exact frozen statements). Sibling dependencies (comparator-accepted declarations reused with their exact frozen types):
- VOM = lcmp_massOn_le_of_vanish_off_compact (key vanish_off_mass): if C is compact, V open, C ⊆ V and X(ω) = 0 whenever tsupport ω ∩ C = ∅, then M_G(X) ≤ M_V(X) for every set G;
- TRI = lcmp_massOn_le_add_of_eval_eq (key mass_triangle): if |c| ≤ 1 and Z(ω) = X(ω) + c·Y(ω) for every ω with tsupport ω ⊆ G, then M_G(Z) ≤ M_G(X) + M_G(Y);
- IR = lcmp_imRep_measure_restrict (key imrep_restrict): for an IMRep R, R.measure ≪ Hⁿ⌞R.carrier, R.orient is R.measure-a.e. strongly measurable, and for Borel E and an IMRep R′ with carrier R.carrier ∩ E, multiplicity R.mult and orientation R.orient, R′.action(ω) = ∫_E R.orient(ω) dR.measure for every n-form ω;
- ICF = rsd_imrep_compact_measure_ne_top (key imrep_compact_finite): R.measure(K) ≠ ∞ for compact K ⊆ U;
- IAI = dor_ims_action_eq_integral (key imrep_action_integral): R.action(ω) = ∫ R.orient(ω) dR.measure for ω ∈ 𝒟ⁿ(U);
- GR = dor_lmb_glc_good_radius (key good_radius): if ρ < ρ′, μ(closedBall(y, ρ′)) ≠ ∞, g : ℝ → [0, ∞] is a.e. measurable with ∫ g dL¹ ≤ I and p holds L¹-a.e., then some t ∈ (ρ, ρ′) has p(t), μ(sphere(y, t)) = 0 and g(t) ≤ ofReal(2/(ρ′ − ρ))·I.
Notation: n := d + 1; for X of degree n, boundaryMassOn(X, W) = M_W(∂X) (definitional in degree d + 1); M(X) := X.mass = M_U(X) (definition of total mass on the domain U); f(x) := dist(x, x₀), continuous and 1-Lipschitz (LipschitzWith.dist_left); {f < t} = ball(x₀, t) and {f = t} = sphere(x₀, t) (definitions of Metric.ball and Metric.sphere). Simplification relative to the supplied step 2: the admissible representation of ∂T_j needed by (SL) is taken from (REP) applied to ∂T_j instead of an IMRep of ∂T_j produced by BR(d); (SL) only needs an admissible representation.

0. (Mass of a set-integral current; used in steps 9(c) and 9(d).) Claim: let k ∈ ℕ, s ⊆ ℝ^P, X ∈ 𝒟_k(U), ν a measure on ℝ^P and v : ℝ^P → Λ_k with |v(x)(α)| ≤ |α| for every k-covector α for ν-a.e. x; if X(ω) = ∫_s v(x)(ω(x)) dν(x) for every ω ∈ 𝒟^k(U), then M(X) ≤ ν(s). Proof: let ω ∈ 𝒟^k(U) be admissible for M(X) = M_U(X), i.e. |ω(x)| ≤ 1 for all x. For ν-a.e. x, hence for ν⌞s-a.e. x, |v(x)(ω(x))| ≤ |ω(x)| ≤ 1. Then ofReal(X(ω)) = ofReal(∫_s v(ω) dν) ≤ ofReal(|∫_s v(ω) dν|) = ‖∫_s v(ω) dν‖ₑ ≤ ∫⁻_s ‖v(ω)‖ₑ dν (Mathlib enorm_integral_le_lintegral_enorm, valid without any integrability or measurability assumption) ≤ ∫⁻_s 1 dν (lintegral_mono_ae) = ν(s) (setLIntegral_const; ν⌞s(ℝ^P) = ν(s) for every set s). M(X) is the supremum of ofReal(X(ω)) over the admissible ω, so M(X) ≤ ν(s).
1. (Radius r₀, the set G and the bound Λ.) U is open and x₀ ∈ U, so there is ε > 0 with ball(x₀, ε) ⊆ U; put r₀ := ε/2 > 0, so closedBall(x₀, r₀) ⊆ ball(x₀, ε) ⊆ U. Let G := ball(x₀, r₀). G is open and closure G ⊆ closedBall(x₀, r₀) (closure_ball_subset_closedBall), so closure G is compact (a closed subset of a compact set) and contained in U: G ⊂⊂ U. Put Λ := sup_j (M_G(T_j) + M_G(∂T_j)), finite by hypothesis (W := G). Then M_G(T_j) ≤ Λ and M_G(∂T_j) ≤ Λ for every j.
2. (Locally finite masses.) Let W be open with W ⊂⊂ U and Λ_W := sup_j (M_W(T_j) + M_W(∂T_j)) < ∞. Then M_W(∂T_j) ≤ Λ_W for every j. Since T_j ⇀ T, also ∂T_j ⇀ ∂T (SimonGMT WeaklyConvergesOn.boundary), and lower semicontinuity of mass (SimonGMT WeaklyConvergesOn.massOn_le_liminf) gives M_W(T) ≤ liminf_j M_W(T_j) ≤ limsup_j M_W(T_j) ≤ sup_j M_W(T_j) ≤ Λ_W < ∞, and likewise M_W(∂T) ≤ liminf_j M_W(∂T_j) ≤ Λ_W < ∞.
3. (Representations.) (a) For each j, (REP) applied to ∂T_j ∈ 𝒟_d(U), which has locally finite mass by step 2, gives a measure μ′_j and ξ′_j : ℝ^P → Λ_d with μ′_j(W) = M_W(∂T_j) for open W, μ′_j(K) < ∞ for compact K ⊆ U, ξ′_j μ′_j-a.e. strongly measurable, |ξ′_j(x)(α)| ≤ |α| for all x and α, and ∂T_j(η) = ∫ ξ′_j(η) dμ′_j for η ∈ 𝒟^d(U). (b) (REP) applied to T ∈ 𝒟_n(U) and to ∂T ∈ 𝒟_d(U) (step 2) gives (μ_T, ξ_T) and (μ_{∂T}, ξ_{∂T}) with the same properties; in particular T(ω) = ∫ ξ_T(ω) dμ_T for ω ∈ 𝒟ⁿ(U). (c) For each j choose an IMRep R_j = (M_j, θ_j, ξ_j) in U representing T_j (hypothesis) and put μ_j := R_j.measure. Then μ_j(K) < ∞ for compact K ⊆ U (ICF); μ_j ≪ Hⁿ⌞M_j and ξ_j is μ_j-a.e. strongly measurable (IR); the fourth conjunct (IMC)(d) of (IMC) gives |ξ_j(x)(α)| ≤ |α| for all α for Hⁿ⌞M_j-a.e. x, hence for μ_j-a.e. x by absolute continuity; T_j(ω) = R_j.action(ω) = ∫ ξ_j(ω) dμ_j for ω ∈ 𝒟ⁿ(U) (R_j represents T_j, then IAI); and μ_j(W) = M_W(T_j) for every open W ((MR)).
4. (Uniform bounds on compact sets.) Let K ⊆ U be compact. There is an open W with K ⊆ W, closure W compact and closure W ⊆ U (Mathlib exists_open_between_and_isCompact_closure); so W ⊂⊂ U, and μ_j(K) ≤ μ_j(W) = M_W(T_j) ≤ Λ_W for every j. Hence sup_j μ_j(K) < ∞.
5. (Measure compactness.) (T1) applied to (μ_j) in U gives a strictly increasing φ : ℕ → ℕ and a measure μ with μ(K) < ∞ and limsup_j μ_{φ(j)}(K) ≤ μ(K) for every compact K ⊆ U.
6. (Slicing.) For each j apply (SL) with k := d, the current T_{φ(j)}, (μ, ξ) := (μ_{φ(j)}, ξ_{φ(j)}), (μ′, ξ′) := (μ′_{φ(j)}, ξ′_{φ(j)}), the function f and L := 1; its hypotheses are steps 3(a) and 3(c) (the everywhere bound for ξ′_{φ(j)} implies the a.e. bound). This gives currents A_j(t) ∈ 𝒟_n(U) and B_j(t) ∈ 𝒟_d(U), t ∈ ℝ, with (i) A_j(t)(ω) = ∫_{f<t} ξ_{φ(j)}(ω) dμ_{φ(j)}; (ii) B_j(t)(η) = ∫_{f<t} ξ′_{φ(j)}(η) dμ′_{φ(j)}; (iii) ∂A_j(t)(η) = B_j(t)(η) whenever tsupport η ∩ {f = t} = ∅; (iv) for every open W, M_W(Z_j(t)) ≤ 1·liminf_{h↓0} h⁻¹μ_{φ(j)}(W ∩ {t − h < f < t}), where Z_j(t) := ∂A_j(t) − B_j(t) ∈ 𝒟_d(U). Likewise (SL) applied to T with (μ_T, ξ_T), (μ_{∂T}, ξ_{∂T}), f and L := 1 (step 3(b)) gives currents A_T(t) ∈ 𝒟_n(U) with A_T(t)(ω) = ∫_{f<t} ξ_T(ω) dμ_T.
7. (Measurable majorant.) Put z_j(t) := M_G(Z_j(t)). Apply (MM) to the measures μ_{φ(j)}, f, G, a := 0, b := r₀, L := 1 and z: f is continuous; μ_{φ(j)}(G ∩ {0 < f < r₀}) ≤ μ_{φ(j)}(G) = M_G(T_{φ(j)}) ≤ Λ < ∞; and z_j(t) ≤ 1·liminf_{h↓0} h⁻¹μ_{φ(j)}(G ∩ {t − h < f < t}) by 6(iv) with W := G. (MM) gives a measurable g : ℝ → [0, ∞] with liminf_j z_j(t) ≤ g(t) for L¹-a.e. t ∈ (0, r₀) and ∫_{(0,r₀)} g dL¹ ≤ 1·liminf_j μ_{φ(j)}(G ∩ {0 < f < r₀}) ≤ Λ (every term is at most μ_{φ(j)}(G) = M_G(T_{φ(j)}) ≤ Λ, and liminf ≤ limsup ≤ sup).
8. (Good radius.) Let g̃ := 1_{(0,r₀)}·g; it is measurable, hence a.e. measurable, and ∫_ℝ g̃ dL¹ = ∫_{(0,r₀)} g dL¹ ≤ Λ (lintegral_indicator). Let p(t) be the statement “t ∈ (0, r₀) implies liminf_j z_j(t) ≤ g(t)”; by step 7, p holds for L¹-a.e. t. Since closedBall(x₀, r₀) is a compact subset of U, μ(closedBall(x₀, r₀)) < ∞ (step 5). GR, with μ, y := x₀, ρ := 0 < ρ′ := r₀, g̃, I := Λ and p, gives r with 0 < r < r₀, p(r), μ(sphere(x₀, r)) = 0 and g̃(r) ≤ ofReal(2/r₀)·Λ < ∞. As r ∈ (0, r₀), g̃(r) = g(r); hence g(r) < ∞ and liminf_j z_j(r) ≤ g(r) < g(r) + 1 = C, where C := (g(r) as an element of ℝ≥0) + 1. By the definition of the liminf, z_j(r) < C for infinitely many j (Filter.frequently_lt_of_liminf_lt), so there is a strictly increasing ψ : ℕ → ℕ with z_{ψ(j)}(r) < C for every j (Filter.extraction_of_frequently_atTop). Moreover closedBall(x₀, r) ⊆ closedBall(x₀, r₀) ⊆ U, and sphere(x₀, r) is compact and contained in G because r < r₀.
9. (The localized currents.) Fix j and let i := φ(ψ(j)). Apply (IMC)(b), the second conjunct of (IMC), to R_i and the Borel set ball(x₀, r): there are S_j ∈ 𝒟_n(U) and an IMRep R′_j in U representing S_j, with carrier M_i ∩ ball(x₀, r), multiplicity θ_i and orientation ξ_i. By IR (with E := ball(x₀, r) and R′ := R′_j), for every ω ∈ 𝒟ⁿ(U), S_j(ω) = R′_j.action(ω) = ∫_{ball(x₀,r)} ξ_i(ω) dμ_i. Since {f < r} = ball(x₀, r), 6(i) gives S_j(ω) = A_{ψ(j)}(r)(ω) for all ω, i.e. S_j = A_{ψ(j)}(r).
 (a) The carrier of R′_j is M_i ∩ ball(x₀, r) ⊆ closedBall(x₀, r).
 (b) If tsupport ω ∩ closedBall(x₀, r) = ∅, then every x ∈ ball(x₀, r) lies outside tsupport ω, so ω(x) = 0 and ξ_i(x)(ω(x)) = 0; hence S_j(ω) = ∫_{ball(x₀,r)} ξ_i(ω) dμ_i = 0.
 (c) Step 0 (ν := μ_i, v := ξ_i, s := ball(x₀, r), the μ_i-a.e. bound of 3(c) and the formula above) gives M(S_j) ≤ μ_i(ball(x₀, r)) ≤ μ_i(G) = M_G(T_i) ≤ Λ.
 (d) Let Z := Z_{ψ(j)}(r) = ∂A_{ψ(j)}(r) − B_{ψ(j)}(r). If η ∈ 𝒟^d(U) and tsupport η ∩ sphere(x₀, r) = ∅, then Z(η) = ∂A_{ψ(j)}(r)(η) − B_{ψ(j)}(r)(η) = 0 by 6(iii), because {f = r} = sphere(x₀, r). VOM (C := sphere(x₀, r), compact; V := G, open; C ⊆ V; evaluated at the set U) gives M(Z) = M_U(Z) ≤ M_G(Z) = z_{ψ(j)}(r) ≤ C. Step 0 (ν := μ′_i, v := ξ′_i, s := ball(x₀, r), the everywhere bound of 3(a), and formula 6(ii) with {f < r} = ball(x₀, r)) gives M(B_{ψ(j)}(r)) ≤ μ′_i(ball(x₀, r)) ≤ μ′_i(G) = M_G(∂T_i) ≤ Λ. Since S_j = A_{ψ(j)}(r), every η ∈ 𝒟^d(U) satisfies ∂S_j(η) = ∂A_{ψ(j)}(r)(η) = Z(η) + 1·B_{ψ(j)}(r)(η); TRI (with G := U, X := Z, Y := B_{ψ(j)}(r), the current ∂S_j in place of Z, and c := 1) gives M(∂S_j) = M_U(∂S_j) ≤ M_U(Z) + M_U(B_{ψ(j)}(r)) = M(Z) + M(B_{ψ(j)}(r)) ≤ C + Λ.
 (e) Hence M(S_j) + M(∂S_j) ≤ Λ + (C + Λ) < ∞ for every j, so sup_j (M(S_j) + M(∂S_j)) < ∞.
10. (Convergence.) Apply (T2) with degree n, X_j := T_{φ(ψ(j))}, X := T, μ_j := μ_{φ(ψ(j))}, ξ_j := ξ_{φ(ψ(j))}, μ_X := μ_T, ξ_X := ξ_T, the measure μ of step 5, f and t := r. Its hypotheses hold: U is open and f is continuous; T_{φ(ψ(j))} ⇀ T because φ ∘ ψ is strictly increasing and hence tends to infinity; the representation properties of (μ_{φ(ψ(j))}, ξ_{φ(ψ(j))}) are step 3(c), and those of (μ_T, ξ_T) are step 3(b) (the everywhere bound gives the a.e. bound); μ(K) < ∞ for compact K ⊆ U (step 5); for compact K ⊆ U, limsup_j μ_{φ(ψ(j))}(K) ≤ limsup_j μ_{φ(j)}(K) ≤ μ(K), because the limsup along ψ is the limsup along the filter map ψ(atTop) ≤ atTop (Filter.limsup_comp, Filter.limsup_le_limsup_of_le); and μ({f = r}) = μ(sphere(x₀, r)) = 0 (step 8). (T2) gives, for every ω ∈ 𝒟ⁿ(U), S_j(ω) = ∫_{f<r} ξ_{φ(ψ(j))}(ω) dμ_{φ(ψ(j))} → ∫_{f<r} ξ_T(ω) dμ_T = A_T(r)(ω). So S_j ⇀ A := A_T(r).
11. (Agreement with T.) If ω ∈ 𝒟ⁿ(U) and tsupport ω ⊆ ball(x₀, r), then ω(x) = 0, hence ξ_T(x)(ω(x)) = 0, for every x ∉ ball(x₀, r) = {f < r}; so A(ω) = ∫_{f<r} ξ_T(ω) dμ_T = ∫ ξ_T(ω) dμ_T = T(ω) (Mathlib setIntegral_eq_integral_of_forall_compl_eq_zero and step 3(b)).
12. (Conclusion.) r, (S_j), (R′_j) and A satisfy: 0 < r and closedBall(x₀, r) ⊆ U (step 8); R′_j represents S_j and R′_j.carrier ⊆ closedBall(x₀, r) (step 9 and 9(a)); S_j(ω) = 0 whenever tsupport ω is disjoint from closedBall(x₀, r) (9(b)); sup_j (M(S_j) + M(∂S_j)) < ∞ (9(e)); S_j ⇀ A (step 10); A(ω) = T(ω) whenever tsupport ω ⊆ ball(x₀, r) (step 11). ∎

Appendix (verified Lean realization of the numbered proof above; not part of the proof). The declaration below was compiled in this decomposition session with Lean v4.35.0-rc3, Mathlib 25730c7c and SimonGMT 2b366308, after `import GMT.Ch07.Submission` in the replayed contract scope (inside `namespace GMT.Ch07` with the frozen contract's `open` commands, after its `noncomputable section ... end`), with the six sibling declarations present under their exact frozen types; apart from those declarations, `#print axioms` reports only propext, Classical.choice and Quot.sound. Step 0 is the `have hMSI`; the remaining `have`/`obtain` blocks follow steps 1–12.

```lean
theorem Submission.cbrcs_localize_at_point : (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) → (∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (L : NNReal), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (k + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) k, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ η : TestFormOn U k, T.boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') → LipschitzWith L f → ∃ (A : ℝ → GeometricCurrentOn U (k + 1)) (B : ℝ → GeometricCurrentOn U k), (∀ (t : ℝ) (ω : TestFormOn U (k + 1)), A t ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) ∧ (∀ (t : ℝ) (η : TestFormOn U k), B t η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') ∧ (∀ (t : ℝ) (η : TestFormOn U k), Disjoint (tsupport (η : DifferentialForm (Euclid P) k)) {x | f x = t} → (A t).boundary η = B t η) ∧ (∀ (W : Set (Euclid P)) (t : ℝ), IsOpen W → ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) ∧ (∀ (W : Set (Euclid P)) (a b : ℝ), IsOpen W → ∫⁻ t in Ioo a b, ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * μ (W ∩ {x | a < f x ∧ f x < b}))) → ((∀ (P : ℕ) (U : Set (Euclid P)) (μs : ℕ → Measure (Euclid P)), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ⨆ j, μs j K < ∞) → ∃ (φ : ℕ → ℕ) (μ : Measure (Euclid P)), StrictMono φ ∧ μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U → Tendsto (fun j => ∫ x, f x ∂(μs (φ j))) atTop (𝓝 (∫ x, f x ∂μ))) ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → limsup (fun j => μs (φ j) K) atTop ≤ μ K) ∧ (∀ G : Set (Euclid P), IsOpen G → G ⊆ U → μ G ≤ liminf (fun j => μs (φ j) G) atTop)) ∧ (∀ (P k : ℕ) (U : Set (Euclid P)) (Xs : ℕ → GeometricCurrentOn U k) (X : GeometricCurrentOn U k) (μs : ℕ → Measure (Euclid P)) (ξs : ℕ → Euclid P → MultiVector P k) (μX μ : Measure (Euclid P)) (ξX : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (t : ℝ), IsOpen U → Continuous f → WeaklyConvergesOn Xs X → (∀ j, ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μs j K < ∞) → (∀ j, AEStronglyMeasurable (ξs j) (μs j)) → (∀ j, ∀ᵐ x ∂(μs j), ∀ α : Covector (Euclid P) k, |ξs j x α| ≤ covectorEuclideanNorm α) → (∀ j, ∀ ω : TestFormOn U k, Xs j ω = ∫ x, ξs j x ((ω : DifferentialForm (Euclid P) k) x) ∂(μs j)) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μX K < ∞) → AEStronglyMeasurable ξX μX → (∀ᵐ x ∂μX, ∀ α : Covector (Euclid P) k, |ξX x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U k, X ω = ∫ x, ξX x ((ω : DifferentialForm (Euclid P) k) x) ∂μX) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → limsup (fun j => μs j K) atTop ≤ μ K) → μ {x | f x = t} = 0 → ∀ ω : TestFormOn U k, Tendsto (fun j => ∫ x in {x | f x < t}, ξs j x ((ω : DifferentialForm (Euclid P) k) x) ∂(μs j)) atTop (𝓝 (∫ x in {x | f x < t}, ξX x ((ω : DifferentialForm (Euclid P) k) x) ∂μX))) ∧ (∀ (P : ℕ) (μs : ℕ → Measure (Euclid P)) (f : Euclid P → ℝ) (G : Set (Euclid P)) (a b : ℝ) (L : NNReal) (Z : ℕ → ℝ → ℝ≥0∞), Continuous f → (∀ j, μs j (G ∩ {x | a < f x ∧ f x < b}) < ∞) → (∀ (j : ℕ) (t : ℝ), t ∈ Ioo a b → Z j t ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μs j (G ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) → ∃ g : ℝ → ℝ≥0∞, Measurable g ∧ (∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo a b → liminf (fun j => Z j t) atTop ≤ g t) ∧ ∫⁻ t in Ioo a b, g t ≤ (L : ℝ≥0∞) * liminf (fun j => μs j (G ∩ {x | a < f x ∧ f x < b})) atTop)) → ∀ (d P : ℕ) (U : Set (Euclid P)) (Ts : ℕ → GeometricCurrentOn U (d + 1)) (T : GeometricCurrentOn U (d + 1)) (x₀ : Euclid P), IsOpen U → (∀ j, IsIntegerMultiplicity (Ts j)) → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → ⨆ j, ((Ts j).massOn W + boundaryMassOn (Ts j) W) < ∞) → WeaklyConvergesOn Ts T → x₀ ∈ U → ∃ (r : ℝ) (Ss : ℕ → GeometricCurrentOn U (d + 1)) (Rs : ℕ → IMRep U (d + 1)) (A : GeometricCurrentOn U (d + 1)), 0 < r ∧ closedBall x₀ r ⊆ U ∧ (∀ j, (Rs j).Represents (Ss j) ∧ (Rs j).carrier ⊆ closedBall x₀ r) ∧ (∀ (j : ℕ) (ω : TestFormOn U (d + 1)), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (d + 1))) (closedBall x₀ r) → Ss j ω = 0) ∧ ⨆ j, ((Ss j).mass + (Ss j).boundary.mass) < ∞ ∧ WeaklyConvergesOn Ss A ∧ ∀ ω : TestFormOn U (d + 1), tsupport (ω : DifferentialForm (Euclid P) (d + 1)) ⊆ ball x₀ r → A ω = T ω := by
  have hVOM := Submission.lcmp_massOn_le_of_vanish_off_compact
  have hTRI := Submission.lcmp_massOn_le_add_of_eval_eq
  have hIR := Submission.lcmp_imRep_measure_restrict
  have hICF := Submission.rsd_imrep_compact_measure_ne_top
  have hIAI := Submission.dor_ims_action_eq_integral
  have hGR := Submission.dor_lmb_glc_good_radius
  have hMSI : (∀ (P k : ℕ) (U s : Set (Euclid P)) (X : GeometricCurrentOn U k) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P k), (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) k, |ξ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U k, X ω = ∫ x in s, ξ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ) → X.mass ≤ μ s) := by
    intro P k U s X μ ξ hbd hrep
    unfold GeometricCurrentOn.mass GeometricCurrentOn.massOn
    apply sSup_le
    rintro _ ⟨ω, ⟨-, hω⟩, rfl⟩
    show ENNReal.ofReal (X ω) ≤ μ s
    rw [hrep ω]
    have hae : ∀ᵐ x ∂(μ.restrict s), ‖ξ x ((ω : DifferentialForm (Euclid P) k) x)‖ₑ ≤ 1 := by
      filter_upwards [ae_restrict_of_ae hbd] with x hx
      rw [Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_one.2 ((hx _).trans (hω x))
    calc ENNReal.ofReal (∫ x in s, ξ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ)
        ≤ ‖∫ x in s, ξ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ‖ₑ := by
          rw [Real.enorm_eq_ofReal_abs]
          exact ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ ∫⁻ x in s, ‖ξ x ((ω : DifferentialForm (Euclid P) k) x)‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ x in s, 1 ∂μ := lintegral_mono_ae hae
      _ = μ s := by rw [setLIntegral_const, one_mul]
  intro hREP hMR hIMC hSL hTOOLS d P U Ts T x₀ hU hIM hbd hconv hx₀
  obtain ⟨_, hIMCb, _, hIMCd⟩ := hIMC
  obtain ⟨hT1, hT2, hMM⟩ := hTOOLS
  -- the slicing function
  set f : Euclid P → ℝ := fun x => dist x x₀ with hf_def
  have hf_cont : Continuous f := continuous_id.dist continuous_const
  have hf_lip : LipschitzWith 1 f := LipschitzWith.dist_left x₀
  -- Step 1: r₀ and G
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
  have hr₀ : 0 < ε / 2 := half_pos hε
  have hcb₀ : closedBall x₀ (ε / 2) ⊆ U := (closedBall_subset_ball (half_lt_self hε)).trans hεU
  set r₀ := ε / 2 with hr₀_def
  set G : Set (Euclid P) := ball x₀ r₀ with hG_def
  have hGo : IsOpen G := isOpen_ball
  have hGcc : CompactlyContained G U :=
    ⟨(isCompact_closedBall x₀ r₀).of_isClosed_subset isClosed_closure closure_ball_subset_closedBall,
     closure_ball_subset_closedBall.trans hcb₀⟩
  have hΛ := hbd G hGo hGcc
  set Λ := ⨆ j, ((Ts j).massOn G + boundaryMassOn (Ts j) G) with hΛ_def
  have hTjG : ∀ j, (Ts j).massOn G ≤ Λ := fun j =>
    le_self_add.trans (le_iSup (fun j => (Ts j).massOn G + boundaryMassOn (Ts j) G) j)
  have hbTjG : ∀ j, (Ts j).boundary.massOn G ≤ Λ := fun j =>
    (le_add_self : (Ts j).boundary.massOn G ≤ (Ts j).massOn G + (Ts j).boundary.massOn G).trans
      (le_iSup (fun j => (Ts j).massOn G + boundaryMassOn (Ts j) G) j)
  -- Step 2: locally finite masses
  have hlocT : ∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞ := by
    intro W hW hWU
    have h1 := hconv.massOn_le_liminf W
    have h2 : liminf (fun j => (Ts j).massOn W) atTop ≤
        ⨆ j, ((Ts j).massOn W + boundaryMassOn (Ts j) W) :=
      (liminf_le_limsup).trans (limsup_le_iSup.trans (iSup_mono fun j => le_self_add))
    exact lt_of_le_of_lt (h1.trans h2) (hbd W hW hWU)
  have hlocbT : ∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.boundary.massOn W < ∞ := by
    intro W hW hWU
    have h1 := (hconv.boundary).massOn_le_liminf W
    have h2 : liminf (fun j => (Ts j).boundary.massOn W) atTop ≤
        ⨆ j, ((Ts j).massOn W + boundaryMassOn (Ts j) W) :=
      (liminf_le_limsup).trans (limsup_le_iSup.trans (iSup_mono fun j =>
        (le_add_self : (Ts j).boundary.massOn W ≤ (Ts j).massOn W + (Ts j).boundary.massOn W)))
    exact lt_of_le_of_lt (h1.trans h2) (hbd W hW hWU)
  have hlocbTj : ∀ j, ∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U →
      (Ts j).boundary.massOn W < ∞ := by
    intro j W hW hWU
    exact lt_of_le_of_lt ((le_add_self : (Ts j).boundary.massOn W ≤ (Ts j).massOn W + (Ts j).boundary.massOn W).trans
      (le_iSup (fun j => (Ts j).massOn W + boundaryMassOn (Ts j) W) j)) (hbd W hW hWU)
  -- Step 3: representations
  choose μ' ξ' _ hμ'K hμ'W hξ'meas hξ'bd hξ'rep _ using
    fun j => hREP P d U (Ts j).boundary hU (hlocbTj j)
  obtain ⟨μT, ξT, -, hμTK, -, hξTmeas, hξTbd, hξTrep, -⟩ := hREP P (d + 1) U T hU hlocT
  obtain ⟨μbT, ξbT, -, hμbTK, -, hξbTmeas, hξbTbd, hξbTrep, -⟩ := hREP P d U T.boundary hU hlocbT
  choose R hR using hIM
  have hRK : ∀ j, ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → (R j).measure K < ∞ :=
    fun j K hK hKU => lt_top_iff_ne_top.2 (hICF P (d + 1) U (R j) K hK hKU).2
  have hRmeas : ∀ j, AEStronglyMeasurable (R j).orient (R j).measure :=
    fun j => (hIR P (d + 1) U (R j)).2.1
  have hRbd : ∀ j, ∀ᵐ x ∂(R j).measure, ∀ α : Covector (Euclid P) (d + 1),
      |(R j).orient x α| ≤ covectorEuclideanNorm α :=
    fun j => (hIR P (d + 1) U (R j)).1.ae_le (hIMCd P (d + 1) U (R j))
  have hRrep : ∀ j, ∀ ω : TestFormOn U (d + 1), Ts j ω =
      ∫ x, (R j).orient x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂(R j).measure :=
    fun j ω => (hR j ω).trans (hIAI P (d + 1) U (R j) ω).2
  have hRW : ∀ j, ∀ W : Set (Euclid P), IsOpen W → (Ts j).massOn W = (R j).measure W :=
    fun j W hW => hMR P (d + 1) U (Ts j) (R j) hU (hR j) W hW
  -- Step 4: uniform bounds on compact sets
  have hsupK : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ⨆ j, (R j).measure K < ∞ := by
    intro K hK hKU
    obtain ⟨W, hWo, hKW, hWU, hWc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
    refine lt_of_le_of_lt ?_ (hbd W hWo ⟨hWc, hWU⟩)
    refine iSup_mono fun j => ?_
    calc (R j).measure K ≤ (R j).measure W := measure_mono hKW
      _ = (Ts j).massOn W := (hRW j W hWo).symm
      _ ≤ _ := le_self_add
  -- Step 5: measure compactness
  obtain ⟨φ, μ, hφ, -, hμK, -, hμlimsup, -⟩ := hT1 P U (fun j => (R j).measure) hU hsupK
  -- Step 6: slicing
  choose A B hA hB hAB hZ _ using fun j =>
    hSL P d U (Ts (φ j)) (R (φ j)).measure (μ' (φ j)) (R (φ j)).orient (ξ' (φ j)) f 1 hU
      (hRK (φ j)) (hμ'K (φ j)) (hRmeas (φ j)) (hξ'meas (φ j)) (hRbd (φ j))
      (Filter.Eventually.of_forall (hξ'bd (φ j))) (hRrep (φ j)) (hξ'rep (φ j)) hf_lip
  obtain ⟨AT, BT, hAT, -, -, -, -⟩ := hSL P d U T μT μbT ξT ξbT f 1 hU hμTK hμbTK hξTmeas hξbTmeas
    (Filter.Eventually.of_forall hξTbd) (Filter.Eventually.of_forall hξbTbd) hξTrep hξbTrep hf_lip
  -- Step 7: measurable majorant
  set z : ℕ → ℝ → ℝ≥0∞ := fun j t => ((A j t).boundary - B j t).massOn G with hz_def
  have hfinG : ∀ j, (R (φ j)).measure (G ∩ {x | 0 < f x ∧ f x < r₀}) < ∞ := by
    intro j
    refine lt_of_le_of_lt (measure_mono inter_subset_left) ?_
    rw [← hRW (φ j) G hGo]
    exact lt_of_le_of_lt (hTjG (φ j)) hΛ
  obtain ⟨g, hgm, hgae, hgint⟩ := hMM P (fun j => (R (φ j)).measure) f G 0 r₀ 1 z hf_cont hfinG
    (fun j t _ => hZ j G t hGo)
  have hgint' : ∫⁻ t in Ioo 0 r₀, g t ≤ Λ := by
    refine hgint.trans ?_
    rw [ENNReal.coe_one, one_mul]
    refine (liminf_le_limsup).trans (limsup_le_iSup.trans (iSup_le fun j => ?_))
    calc (R (φ j)).measure (G ∩ {x | 0 < f x ∧ f x < r₀}) ≤ (R (φ j)).measure G :=
          measure_mono inter_subset_left
      _ = (Ts (φ j)).massOn G := (hRW (φ j) G hGo).symm
      _ ≤ Λ := hTjG (φ j)
  -- Step 8: good radius
  have hμcb : μ (closedBall x₀ r₀) ≠ ∞ := (hμK _ (isCompact_closedBall x₀ r₀) hcb₀).ne
  obtain ⟨r, hr0, hrr₀, hpr, hsph, hgr⟩ := hGR P μ x₀ 0 r₀ ((Ioo 0 r₀).indicator g) Λ
    (fun t => t ∈ Ioo 0 r₀ → liminf (fun j => z j t) atTop ≤ g t) hr₀ hμcb
    ((hgm.indicator measurableSet_Ioo).aemeasurable)
    (by rw [lintegral_indicator measurableSet_Ioo]; exact hgint') hgae
  have hrI : r ∈ Ioo 0 r₀ := ⟨hr0, hrr₀⟩
  have hgr' : g r < ∞ := by
    rw [indicator_of_mem hrI] at hgr
    exact lt_of_le_of_lt hgr (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hΛ)
  set C : NNReal := (g r).toNNReal + 1 with hC_def
  have hlim : liminf (fun j => z j r) atTop < (C : ℝ≥0∞) := by
    calc liminf (fun j => z j r) atTop ≤ g r := hpr hrI
      _ < g r + 1 := ENNReal.lt_add_right hgr'.ne one_ne_zero
      _ = (C : ℝ≥0∞) := by rw [hC_def, ENNReal.coe_add, ENNReal.coe_toNNReal hgr'.ne, ENNReal.coe_one]
  obtain ⟨ψ, hψ, hψC⟩ := extraction_of_frequently_atTop (frequently_lt_of_liminf_lt (by isBoundedDefault) hlim)
  -- Step 9: the localized currents
  have hball_meas : MeasurableSet (ball x₀ r) := measurableSet_ball
  choose S R' hR'rep hR'car hR'mult hR'or using
    fun j => hIMCb P (d + 1) U (R (φ (ψ j))) (ball x₀ r) hU hball_meas
  have hSval : ∀ j, ∀ ω : TestFormOn U (d + 1), S j ω = ∫ x in ball x₀ r,
      (R (φ (ψ j))).orient x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂(R (φ (ψ j))).measure := by
    intro j ω
    rw [hR'rep j ω]
    exact ((hIR P (d + 1) U (R (φ (ψ j)))).2.2 (ball x₀ r) (R' j) hball_meas (hR'car j) (hR'mult j)
      (hR'or j)).2 _
  have hSA : ∀ j, S j = A (ψ j) r := by
    intro j
    ext ω
    rw [hSval j ω, hA (ψ j) r ω]
    rfl
  have hcarr : ∀ j, (R' j).carrier ⊆ closedBall x₀ r := by
    intro j
    rw [hR'car j]
    exact inter_subset_right.trans ball_subset_closedBall
  have hvan : ∀ (j : ℕ) (ω : TestFormOn U (d + 1)),
      Disjoint (tsupport (ω : DifferentialForm (Euclid P) (d + 1))) (closedBall x₀ r) → S j ω = 0 := by
    intro j ω hdisj
    rw [hSval j ω]
    refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
    have hx' : x ∉ tsupport (ω : DifferentialForm (Euclid P) (d + 1)) :=
      fun h => hdisj.ne_of_mem h (ball_subset_closedBall hx) rfl
    rw [image_eq_zero_of_notMem_tsupport hx', map_zero]
  have hSmass : ∀ j, (S j).mass ≤ Λ := by
    intro j
    calc (S j).mass ≤ (R (φ (ψ j))).measure (ball x₀ r) :=
          hMSI P (d + 1) U (ball x₀ r) (S j) (R (φ (ψ j))).measure (R (φ (ψ j))).orient
            (hRbd _) (hSval j)
      _ ≤ (R (φ (ψ j))).measure G := measure_mono (ball_subset_ball hrr₀.le)
      _ = (Ts (φ (ψ j))).massOn G := (hRW _ G hGo).symm
      _ ≤ Λ := hTjG _
  have hsphG : sphere x₀ r ⊆ G := sphere_subset_ball hrr₀
  have hbmass : ∀ j, (S j).boundary.mass ≤ (C : ℝ≥0∞) + Λ := by
    intro j
    set Zd := (A (ψ j) r).boundary - B (ψ j) r with hZd_def
    have hZdvan : ∀ η : TestFormOn U d,
        Disjoint (tsupport (η : DifferentialForm (Euclid P) d)) (sphere x₀ r) → Zd η = 0 := by
      intro η hη
      change (A (ψ j) r).boundary η - B (ψ j) r η = 0
      rw [hAB (ψ j) r η hη, sub_self]
    have hZd : Zd.mass ≤ (C : ℝ≥0∞) :=
      calc Zd.mass = Zd.massOn U := rfl
        _ ≤ Zd.massOn G := hVOM P d U G (sphere x₀ r) Zd (isCompact_sphere x₀ r) hGo hsphG hZdvan U
        _ = z (ψ j) r := rfl
        _ ≤ (C : ℝ≥0∞) := (hψC j).le
    have hBm : (B (ψ j) r).mass ≤ Λ :=
      calc (B (ψ j) r).mass ≤ μ' (φ (ψ j)) (ball x₀ r) :=
            hMSI P d U (ball x₀ r) (B (ψ j) r) (μ' (φ (ψ j))) (ξ' (φ (ψ j)))
              (Filter.Eventually.of_forall (hξ'bd _)) (hB (ψ j) r)
        _ ≤ μ' (φ (ψ j)) G := measure_mono (ball_subset_ball hrr₀.le)
        _ = (Ts (φ (ψ j))).boundary.massOn G := (hμ'W _ G hGo).symm
        _ ≤ Λ := hbTjG _
    have htri : (S j).boundary.massOn U ≤ Zd.massOn U + (B (ψ j) r).massOn U := by
      refine hTRI P d U U Zd (B (ψ j) r) (S j).boundary 1 (by simp) fun η _ => ?_
      rw [hSA j]
      change (A (ψ j) r).boundary η = ((A (ψ j) r).boundary η - B (ψ j) r η) + 1 * B (ψ j) r η
      ring
    calc (S j).boundary.mass = (S j).boundary.massOn U := rfl
      _ ≤ Zd.massOn U + (B (ψ j) r).massOn U := htri
      _ = Zd.mass + (B (ψ j) r).mass := rfl
      _ ≤ (C : ℝ≥0∞) + Λ := add_le_add hZd hBm
  have hsup : ⨆ j, ((S j).mass + (S j).boundary.mass) < ∞ := by
    refine lt_of_le_of_lt (iSup_le fun j => add_le_add (hSmass j) (hbmass j)) ?_
    exact ENNReal.add_lt_top.2 ⟨hΛ, ENNReal.add_lt_top.2 ⟨ENNReal.coe_lt_top, hΛ⟩⟩
  -- Step 10: convergence
  have hconv' : WeaklyConvergesOn (fun j => Ts (φ (ψ j))) T :=
    fun ω => (hconv ω).comp ((hφ.comp hψ).tendsto_atTop)
  have hlimsup' : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      limsup (fun j => (R (φ (ψ j))).measure K) atTop ≤ μ K := by
    intro K hK hKU
    refine le_trans ?_ (hμlimsup K hK hKU)
    have h1 : limsup (fun j => (R (φ (ψ j))).measure K) atTop =
        limsup (fun j => (R (φ j)).measure K) (map ψ atTop) :=
      limsup_comp (fun j => (R (φ j)).measure K) ψ atTop
    rw [h1]
    exact limsup_le_limsup_of_le hψ.tendsto_atTop (by isBoundedDefault) (by isBoundedDefault)
  have hSconv : WeaklyConvergesOn S (AT r) := by
    intro ω
    have h := hT2 P (d + 1) U (fun j => Ts (φ (ψ j))) T (fun j => (R (φ (ψ j))).measure)
      (fun j => (R (φ (ψ j))).orient) μT μ ξT f r hU hf_cont hconv' (fun j => hRK _)
      (fun j => hRmeas _) (fun j => hRbd _) (fun j => hRrep _) hμTK hξTmeas
      (Filter.Eventually.of_forall hξTbd) hξTrep hμK hlimsup' hsph ω
    rw [hAT r ω]
    convert h using 2 with j
    exact hSval j ω
  -- Step 11: agreement
  have hagree : ∀ ω : TestFormOn U (d + 1),
      tsupport (ω : DifferentialForm (Euclid P) (d + 1)) ⊆ ball x₀ r → AT r ω = T ω := by
    intro ω hω
    rw [hAT r ω, hξTrep ω]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    have hx' : x ∉ tsupport (ω : DifferentialForm (Euclid P) (d + 1)) := fun h => hx (hω h)
    rw [image_eq_zero_of_notMem_tsupport hx', map_zero]
  exact ⟨r, S, R', AT r, hr0, (closedBall_subset_closedBall hrr₀.le).trans hcb₀,
    fun j => ⟨hR'rep j, hcarr j⟩, hvan, hsup, hSconv, hagree⟩
```

## Key steps

1. Step 0: a current given by a set integral of a field bounded by 1 against ν over s has mass at most ν(s).
2. Choose r₀ with closedBall(x₀, r₀) ⊆ U; G := ball(x₀, r₀) ⊂⊂ U, Λ := Λ_G < ∞; lower semicontinuity gives T and ∂T locally finite mass.
3. REP represents ∂T_j, T, ∂T; ICF, IR, IAI, (IMC)(d) and MR make (R_j.measure, R_j.orient) admissible representations of T_j with μ_j(W) = M_W(T_j).
4. T1 gives a subsequence φ and a limit measure μ; SL slices T_{φ(j)} by dist(·, x₀); MM gives a measurable majorant g of the slice defects M_G(Z_j(t)).
5. GR gives r ∈ (0, r₀) with μ(sphere(x₀, r)) = 0 and g(r) < ∞; a further subsequence ψ has M_G(Z_{ψ(j)}(r)) ≤ C.
6. S_j := (IMC)(b)-restriction of T_{φψ(j)} to ball(x₀, r) equals the SL slice (IR); it vanishes off closedBall(x₀, r), and step 0 (mass of a set-integral current), VOM and TRI give M(S_j) + M(∂S_j) ≤ 2Λ + C.
7. T2 gives S_j ⇀ A := A_T(r) = T⌞ball(x₀, r), which agrees with T on forms supported in ball(x₀, r).

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); cmp snapshot project/GMT/Ch07/Contract.lean with workspace GMT/Ch07/Contract.lean (identical); diff GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `python3 scan of dag.json: state of closure_succ-a1 (decomposing, attempt 2, no children; decomposition-v1.json was accepted but never activated), frozen statements of convergence_tools-a1, im_local-a1, closure_compact-a1 and of the six parent dependencies with their statuses`
- `python3 scan of the 578 accepted dag.json nodes with candidate_commit for 'massOn G', 'withDensity|R.measure', 'Countable|{x | f x = t}|sphere', 'TestFormOnConverges', 'cutoff', 'testFormOnInclusion (subset_univ', 'ω = ∫ x in' (found lcmp_massOn_le_of_vanish_off_compact, lcmp_massOn_le_add_of_eval_eq, lcmp_imRep_measure_restrict, rsd_imrep_compact_measure_ne_top, dor_ims_action_eq_integral, dor_lmb_glc_good_radius, dtc_extend_by_zero; no accepted cutoff-continuity or set-integral-mass lemma)`
- `replay of runtime _existing_lean_name_problem/_accepted_checkpoint on the final eight subproblems against the 975-node dag.json (six reuses accepted, two new names unused) and of _dependency_problem (acyclic)`
- `grep -n in SimonGMT Chapter06 Currents.lean, Mass.lean, CurrentLocalEquality.lean, Forms.lean for GeometricCurrentOn, TestFormOnConverges, WeaklyConvergesOn.boundary, massOn, mass, massOn_mono, massOn_le_liminf, restrictDomain, testFormOnInclusion, zeroRegion, support, exteriorDerivative (abbrev of Mathlib extDeriv)`
- `grep -n in the snapshot mathlib for Filter.EventuallyEq.extDeriv_eq, norm_iteratedFDeriv_smul_le, support_iteratedFDeriv_subset, exists_open_between_and_isCompact_closure, exists_contDiff_support_eq_eq_one_iff, integral_withDensity_eq_integral_smul, enorm_integral_le_lintegral_enorm, setIntegral_eq_integral_of_forall_compl_eq_zero, lintegral_indicator, extraction_of_frequently_atTop, limsup_le_iSup, limsup_le_limsup_of_le`
- `python3 -I scope.py: verifier/lean_contract.py validate_lean_statement on all eight statements (pass) and verifier/gmt-compare.py contract_scope(Contract.lean, GMT.Ch07.main_theorem) (replay: open Filter Function Set MeasureTheory Metric; open scoped ENNReal Topology; namespace GMT.Ch07; open Poincare.SimonGMT.Chapter06; open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt); noncomputable section; end)`
- `lake env lean /tmp/cbr-succ-v2-k7m3/final/Challenge_<key>.lean for all eight keys (elaborate), Assembly.lean, LocalizeFolded.lean, AppendixLocalize.lean (#print axioms: propext, Classical.choice, Quot.sound only, apart from the six stand-in sibling declarations in the appendix test)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-932152a15b/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-932152a15b/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-932152a15b/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-local-comparison-a1-mass-l-9981f1246a/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-local-comparison-a1-mass-triangle-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-local-comparison-a1-imrep-1bd5f15878/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1-imrep-local-finiteness-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1-action-188f3b5994/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-level-cut-a1-c2deed446a/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Bounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Separation/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/store.py`
- `/tmp/cbr-succ-v2-k7m3/final/Assembly.lean`
- `/tmp/cbr-succ-v2-k7m3/final/LocalizeFolded.lean`
- `/tmp/cbr-succ-v2-k7m3/final/AppendixLocalize.lean`

The snapshot contract is byte-identical to the workspace Contract.lean and Submission.lean. The node's earlier accepted decomposition was never activated (no children exist). Six small facts used by the localization already exist as comparator-accepted declarations with candidate commits and are reused with byte-identical frozen types: lcmp_massOn_le_of_vanish_off_compact, lcmp_massOn_le_add_of_eval_eq, lcmp_imRep_measure_restrict, rsd_imrep_compact_measure_ne_top, dor_ims_action_eq_integral and dor_lmb_glc_good_radius. No accepted declaration gives continuity of multiplication by a cutoff in the test-form topology, or a cutoff extension of non-IM currents to ℝ^P with weak-convergence control (dtc_extend_by_zero needs an IM representation and is not uniform), so cutoff_extension is new. Every cited Mathlib and SimonGMT declaration exists; SimonGMT's exteriorDerivative is Mathlib's extDeriv. All eight child statements pass the verifier's lexical check and elaborate in the exact comparator challenge format. A hypothesis-only assembly proves the frozen parent type from cutoff_extension, localize and the three declared sibling contracts. localize is proved from exactly the six reused types; this proof is attached verbatim as an appendix and compiles. All checks use only propext, Classical.choice and Quot.sound.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
