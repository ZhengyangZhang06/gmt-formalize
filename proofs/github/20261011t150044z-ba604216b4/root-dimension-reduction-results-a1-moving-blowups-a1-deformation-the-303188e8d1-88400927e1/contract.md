<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.skeleton_deformation-a1.shell_decomposition-a1 -->

## Theorem `Submission.dimred_mbl_dtsd_shell_decomposition`

Dyadic shell decomposition of an integer multiplicity current around the dual skeleton (Simon Ch. 6, proof of 5.1, displays (8)–(10) and the shells of E3). Assume, as hypotheses of the statement, the five antecedents of the parent statement, verbatim: (VO) for all P, n, U, S ∈ 𝒟_n(U) and ω ∈ 𝒟ⁿ(U) with tsupport ω disjoint from spt S, S(ω) = 0; (MR) for U open and an IMRep R representing T ∈ 𝒟_n(U), M_W(T) = R.measure(W) for every open W; (REP) for U open and T ∈ 𝒟_n(U) with M_W(T) < ∞ for open W ⊂⊂ U there are a Borel measure μ (μ(ℝ^P ∖ U) = 0, finite on compact subsets of U) and ξ (μ-a.e. strongly measurable, |ξ(x)(α)| ≤ |α| for all x, α) with M_W(T) = μ(W) for open W, T(ω) = ∫ξ(ω)dμ, and, if also M_W(∂T) < ∞ for open W ⊂⊂ U, μ(E) = 0 whenever Hⁿ(E) = 0; (IMC) (a) locality of approximate tangent spaces for Borel M ⊆ M' ⊆ U with Hⁿ(M' ∩ K) < ∞ (K ⊆ U compact); (b) the restriction (M ∩ E, θ, ξ) of an IMRep to a Borel E is an IMRep representing some current; (c) A − B is integer multiplicity for integer multiplicity A, B (U open); (d) |R.orient(x)(α)| ≤ |α| for Hⁿ-a.e. x in the carrier; (SL) for U open, T ∈ 𝒟_{k+1}(U) and ∂T represented by measures (μ, ξ), (μ', ξ') finite on compacts of U with |ξ|, |ξ'| ≤ 1 a.e. and f L-Lipschitz there are A_t(ω) = ∫_{f<t}ξ(ω)dμ, B_t(η) = ∫_{f<t}ξ'(η)dμ' with ∂A_t(η) = B_t(η) when tsupport η misses {f = t}, M_W(∂A_t − B_t) ≤ L·liminf_{h↓0} h⁻¹μ(W ∩ {t − h < f < t}) and ∫⁻_{(a,b)} M_W(∂A_t − B_t)dt ≤ L·μ(W ∩ {a < f < b}) for open W. (These are verbatim the antecedents (VO), (MR), (REP), (IMC), (SL) of the parent statement, which receives them as antecedents itself; the parent passes its own hypotheses on, so the child needs no declaration outside its own subtree.) Let P, m ∈ ℕ (n := m + 1), T ∈ 𝒟_n(ℝ^P) (domain univ) integer multiplicity with compact support, M(T) < ∞ and M(∂T) < ∞, let d : ℝ^P → ℝ be 1-Lipschitz and C ∈ ℝ≥0, and assume the density bounds M_{{d<r}}(T) ≤ C·r^{m+2}·M(T) and M_{{d<r}}(∂T) ≤ C·r^{m+2}·M(∂T) for every real r with 0 < r ≤ 1/4 (in [0, ∞], r^{m+2} through ENNReal.ofReal). Then there are radii r : ℕ → ℝ and currents W_j ∈ 𝒟_n(ℝ^P), D_j, Z_j ∈ 𝒟_m(ℝ^P) (j ∈ ℕ) such that: (1/2)^{j+3} < r_j < (1/2)^{j+2}; Σ_j W_j(ω) = T(ω) for every ω ∈ 𝒟ⁿ(ℝ^P) (HasSum); ∂W_0 = D_0 − Z_0 and ∂W_{j+1} = D_{j+1} − (Z_{j+1} − Z_j); every W_j is integer multiplicity; spt W_j, spt D_j, spt Z_j are compact, M(W_j), M(∂W_j), M(D_j), M(Z_j) are finite and boundaryMassOn D_j ℝ^P, boundaryMassOn Z_j ℝ^P are finite; spt W_j ⊆ spt T ∩ {d ≥ r_j}, spt D_j ⊆ spt ∂T ∩ {d ≥ r_j}, spt Z_j ⊆ spt T ∩ {d = r_j}; M(W_0) ≤ M(T), M(W_{j+1}) ≤ C·(1/2)^{(j+2)(m+2)}·M(T), M(D_0) ≤ M(∂T), M(D_{j+1}) ≤ C·(1/2)^{(j+2)(m+2)}·M(∂T) and M(Z_j) ≤ 4C·(1/2)^{(j+2)(m+1)}·M(T). Conventions: ℝ^P = Euclid P (EuclideanSpace ℝ (Fin P)); for U ⊆ ℝ^P, 𝒟^k(U) = TestFormOn U k (smooth k-forms on ℝ^P whose compact tsupport lies in U) and 𝒟_k(U) = GeometricCurrentOn U k (SimonGMT Chapter06), X(ω) the value of X on ω; X − Y is the contract subtraction, (X − Y)(ω) = X(ω) − Y(ω) (definitional); 0 is the zero current; ∂X = X.boundary, ∂X(η) = X(dη) (GeometricCurrentOn.boundary_apply, dη = exteriorDerivativeTestOn U k η, whose underlying form is exteriorDerivative η); currents are equal when their values agree (GeometricCurrentOn.ext). |α| = covectorEuclideanNorm α is the Euclidean coefficient norm of a covector. M_G(X) = X.massOn G ∈ [0, ∞] is the supremum of ENNReal.ofReal X(ω) over the ω ∈ 𝒟^k(U) with tsupport ω ⊆ G and |ω(x)| ≤ 1 for all x (such ω are admissible for M_G, massAdmissibleOn U k G); M(X) = X.mass = M_U(X); boundaryMassOn X G = M_G(∂X) if k ≥ 1 and 0 if k = 0. spt X = X.support (Simon 6.2.11) = U minus the zero region, the union of the open W with compact closure contained in U on which X vanishes (X(ω) = 0 whenever tsupport ω ⊆ W). IM = IsIntegerMultiplicity: X is represented by an IMRep R = (M, θ, ξ) of the contract (R.carrier, R.mult, R.orient), i.e. X(ω) = R.action ω = ∫_M θ⟨ω, ξ⟩ dHⁿ, and R.measure = θ·Hⁿ⌞M (Hⁿ = μHE[n]).

Node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.skeleton_deformation-a1.shell_decomposition-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5939

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/7085, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5129, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7088, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4695, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4912, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4607

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/7848, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7859, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7869, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7876, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7889, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7893, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7898, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4695, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4912, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4607

## Lean problem

Declaration: `Submission.dimred_mbl_dtsd_shell_decomposition`

```lean
(∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) → (∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (L : NNReal), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (k + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) k, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ η : TestFormOn U k, T.boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') → LipschitzWith L f → ∃ (A : ℝ → GeometricCurrentOn U (k + 1)) (B : ℝ → GeometricCurrentOn U k), (∀ (t : ℝ) (ω : TestFormOn U (k + 1)), A t ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) ∧ (∀ (t : ℝ) (η : TestFormOn U k), B t η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') ∧ (∀ (t : ℝ) (η : TestFormOn U k), Disjoint (tsupport (η : DifferentialForm (Euclid P) k)) {x | f x = t} → (A t).boundary η = B t η) ∧ (∀ (W : Set (Euclid P)) (t : ℝ), IsOpen W → ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) ∧ (∀ (W : Set (Euclid P)) (a b : ℝ), IsOpen W → ∫⁻ t in Ioo a b, ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * μ (W ∩ {x | a < f x ∧ f x < b}))) → ∀ (P m : ℕ) (T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (d : Euclid P → ℝ) (C : NNReal), IsIntegerMultiplicity T → IsCompact T.support → T.mass < ∞ → T.boundary.mass < ∞ → LipschitzWith 1 d → (∀ r : ℝ, 0 < r → r ≤ 1 / 4 → T.massOn {x | d x < r} ≤ C * ENNReal.ofReal (r ^ (m + 2)) * T.mass ∧ T.boundary.massOn {x | d x < r} ≤ C * ENNReal.ofReal (r ^ (m + 2)) * T.boundary.mass) → ∃ (r : ℕ → ℝ) (W : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (D Z : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) m), (∀ j, (1 / 2 : ℝ) ^ (j + 3) < r j ∧ r j < (1 / 2 : ℝ) ^ (j + 2)) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), HasSum (fun j => W j ω) (T ω)) ∧ (W 0).boundary = D 0 - Z 0 ∧ (∀ j, (W (j + 1)).boundary = D (j + 1) - (Z (j + 1) - Z j)) ∧ (∀ j, IsIntegerMultiplicity (W j)) ∧ (∀ j, IsCompact (W j).support ∧ (W j).mass < ∞ ∧ (W j).boundary.mass < ∞) ∧ (∀ j, IsCompact (D j).support ∧ (D j).mass < ∞ ∧ boundaryMassOn (D j) univ < ∞) ∧ (∀ j, IsCompact (Z j).support ∧ (Z j).mass < ∞ ∧ boundaryMassOn (Z j) univ < ∞) ∧ (∀ j, (W j).support ⊆ T.support ∩ {x | r j ≤ d x}) ∧ (∀ j, (D j).support ⊆ T.boundary.support ∩ {x | r j ≤ d x}) ∧ (∀ j, (Z j).support ⊆ T.support ∩ {x | d x = r j}) ∧ (W 0).mass ≤ T.mass ∧ (∀ j, (W (j + 1)).mass ≤ C * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((j + 2) * (m + 2))) * T.mass) ∧ (D 0).mass ≤ T.boundary.mass ∧ (∀ j, (D (j + 1)).mass ≤ C * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((j + 2) * (m + 2))) * T.boundary.mass) ∧ (∀ j, (Z j).mass ≤ 4 * C * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((j + 2) * (m + 1))) * T.mass)
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

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.skeleton_deformation-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.skeleton_deformation-a1.shell_decomposition-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 2, 5 and 6 of the parent's supplied proof (parent E0, E2–E3; Simon Ch. 6, proof of 5.1, displays (8)–(10), with the half-open shells E_0 = {d ≥ ρ*_0}, E_{j+1} = shell_j of the parent's E3). Here the density bounds, which the parent obtains from the good centre, are hypotheses, and the shells are taken half-open. Siblings used: S = dimred_mbl_dtsd_support_calculus, ML = cmc_fcl_massOn_le_measure_inter, GR = dimred_mbl_dtsd_good_radius, IR = lcmp_imRep_measure_restrict, MS = cmc_fc_cs_massOn_sub_le (M_G(A − B) ≤ M_G(A) + M_G(B)), EB = cmr_abs_apply_le_massOn (|X(ω)| ≤ c·M_W(X).toReal if M_W(X) ≠ ∞, tsupport ω ⊆ W, |ω| ≤ c).

Notation. n := m + 1; all currents are on univ = ℝ^P, which is open; M(X) = M_{ℝ^P}(X). d is continuous, so {d < t} is open, {d ≥ t} and {d = t} are closed, and all are Borel. ρ_j := (1/2)^{j+2}, so 0 < ρ_j ≤ 1/4, ρ_j/2 = (1/2)^{j+3} and ρ_j → 0. For a test form ω let c_ω := sup_x |ω(x)| < ∞: x ↦ |ω(x)| is continuous (covectorEuclideanNorm is the square root of a finite sum of squares of continuous evaluation maps) and vanishes outside the compact set tsupport ω (Continuous.bounded_above_of_compact_support).

1. (The mass measure of T.) Choose an IMRep R representing T and put μ_T := R.measure, ξ := R.orient.
   (1a) By (MR) (U = ℝ^P open), M_W(T) = μ_T(W) for every open W; in particular μ_T(ℝ^P) = M(T) < ∞, so μ_T is a finite measure and is finite on compact sets.
   (1b) By IR (a), (b), μ_T ≪ Hⁿ⌞R.carrier and ξ is μ_T-a.e. strongly measurable. By (IMC)(d), |ξ(x)(α)| ≤ |α| for all α for Hⁿ⌞R.carrier-a.e. x, hence for μ_T-a.e. x (absolute continuity, AbsolutelyContinuous.ae_le).
   (1c) By IR (c) with E := ℝ^P and R′ := R (R.carrier = R.carrier ∩ ℝ^P), R.action ω = ∫_{ℝ^P} ξ(ω) dμ_T = ∫ ξ(x)(ω(x)) dμ_T(x) (Measure.restrict_univ); since R represents T, T(ω) = ∫ ξ(ω) dμ_T for every ω ∈ 𝒟ⁿ.
   (1d) μ_T(ℝ^P \ spt T) = 0. Indeed spt T is closed (S (ii)), so G := ℝ^P \ spt T is open and μ_T(G) = M_G(T) by (1a); every ω admissible for M_G has tsupport ω ⊆ G, i.e. disjoint from spt T, so T(ω) = 0 by (VO); hence M_G(T) is the supremum of a set contained in {0}, i.e. 0.
2. (A measure for ∂T.) For every W, M_W(∂T) ≤ M(∂T) < ∞ (massOn_mono). So (REP) with U := ℝ^P and the current ∂T ∈ 𝒟_m gives a measure μ_∂ and ξ_∂ : ℝ^P → Λ_m with: μ_∂ finite on compact sets; M_W(∂T) = μ_∂(W) for open W, so μ_∂(ℝ^P) = M(∂T) < ∞ and μ_∂ is finite; ξ_∂ is μ_∂-a.e. strongly measurable; |ξ_∂(x)(α)| ≤ |α| for all x and α; ∂T(η) = ∫ ξ_∂(η) dμ_∂ for every η ∈ 𝒟^m. Exactly as in (1d) (S (ii), (VO)), μ_∂(ℝ^P \ spt ∂T) = 0.
3. (Integrability.) For ω ∈ 𝒟ⁿ, x ↦ ξ(x)(ω(x)) is μ_T-a.e. strongly measurable (image of the a.e. strongly measurable pair (ξ, ω) under the continuous evaluation map (L, α) ↦ L(α)) and bounded by c_ω for μ_T-a.e. x (1b), hence μ_T-integrable (Integrable.of_bound, μ_T finite), and integrable on every subset. Likewise x ↦ ξ_∂(x)(η(x)) is μ_∂-integrable for η ∈ 𝒟^m.
4. (Slicing by d.) Apply (SL) with k := m, U := ℝ^P, T, μ := μ_T, μ' := μ_∂, ξ, ξ' := ξ_∂, f := d, L := 1 (its hypotheses are (1a)–(1c), step 2 and LipschitzWith 1 d; the a.e. bound for ξ_∂ holds everywhere). It gives A : ℝ → 𝒟_n, B : ℝ → 𝒟_m with
   (SL1) A_t(ω) = ∫_{{d<t}} ξ(ω) dμ_T; (SL2) B_t(η) = ∫_{{d<t}} ξ_∂(η) dμ_∂;
   (SL3) ∂A_t(η) = B_t(η) whenever tsupport η is disjoint from {d = t};
   (SL4) for W := ℝ^P (open; ℝ^P ∩ S = S): M(∂A_t − B_t) ≤ 1·liminf_{h→0+} ofReal(h⁻¹)·μ_T({t − h < d < t}).
5. (Good radii.) Fix j. Put β_j := C·ofReal(ρ_j^{m+2})·M(T). Since {d < ρ_j} is open, μ_T({d < ρ_j}) = M_{{d<ρ_j}}(T) ≤ β_j by (1a) and the density hypothesis (0 < ρ_j ≤ 1/4). d is measurable (continuous) and μ_T, μ_∂ are finite, so GR (with μ := μ_T, μ' := μ_∂, f := d, ρ := ρ_j, B := β_j) gives r_j with ρ_j/2 < r_j < ρ_j and
   (5a) liminf_{h→0+} ofReal(h⁻¹)·μ_T({r_j − h < d < r_j}) ≤ ofReal(4/ρ_j)·β_j = 4C·ofReal(ρ_j^{m+1})·M(T) (ofReal(4/ρ)·ofReal(ρ^{m+2}) = ofReal(4ρ^{m+1}) = 4·ofReal(ρ^{m+1}) for ρ > 0);
   (5b) liminf_{h→0+} ofReal(h⁻¹)·μ_∂({r_j − h < d < r_j}) < ∞.
   Choose such r_j for every j (choice). Then (1/2)^{j+3} < r_j < (1/2)^{j+2} (first conclusion), and r_{j+1} < ρ_{j+1} = ρ_j/2 < r_j, so the r_j strictly decrease.
6. (Definitions.) W_0 := T − A_{r_0}, W_{j+1} := A_{r_j} − A_{r_{j+1}}; D_0 := ∂T − B_{r_0}, D_{j+1} := B_{r_j} − B_{r_{j+1}}; Z_j := ∂A_{r_j} − B_{r_j}. Shells: E_0 := {d ≥ r_0}, E_{j+1} := {r_{j+1} ≤ d < r_j}. They are Borel and pairwise disjoint (the r_j decrease), and E_j ⊆ {d ≥ r_j}.
7. (Integral formulas.) For ω ∈ 𝒟ⁿ, η ∈ 𝒟^m and all j: W_j(ω) = ∫_{E_j} ξ(ω) dμ_T and D_j(η) = ∫_{E_j} ξ_∂(η) dμ_∂. For j = 0: by (1c), (SL1), {d < r_0}ᶜ = E_0 and integral_add_compl (integrability, step 3), T(ω) − A_{r_0}(ω) = ∫ ξ(ω) dμ_T − ∫_{{d<r_0}} ξ(ω) dμ_T = ∫_{E_0} ξ(ω) dμ_T. For j + 1: {d < r_{j+1}} ⊆ {d < r_j} and {d < r_j} \ {d < r_{j+1}} = E_{j+1}, so ∫_{{d<r_j}} − ∫_{{d<r_{j+1}}} = ∫_{E_{j+1}} (setIntegral_sdiff, step 3). The same computations with step 2, (SL2) give the formulas for D_j.
8. (W_j is integer multiplicity.) (IMC)(b) with U := ℝ^P, R and the Borel set E_j gives a current W′_j and an IMRep R′_j representing W′_j with carrier R.carrier ∩ E_j, multiplicity R.mult and orientation R.orient. By IR (c), R′_j.action ω = ∫_{E_j} ξ(ω) dμ_T = W_j(ω) (step 7). Hence W′_j(ω) = W_j(ω) for every ω, so W′_j = W_j (GeometricCurrentOn.ext) and W_j is IM.
9. (Boundary relations.) For η ∈ 𝒟^m (pointwise identities; then GeometricCurrentOn.ext): ∂W_0(η) = T(dη) − A_{r_0}(dη) = ∂T(η) − ∂A_{r_0}(η) = (∂T(η) − B_{r_0}(η)) − (∂A_{r_0}(η) − B_{r_0}(η)) = D_0(η) − Z_0(η); and ∂W_{j+1}(η) = ∂A_{r_j}(η) − ∂A_{r_{j+1}}(η) = (B_{r_j}(η) − B_{r_{j+1}}(η)) − ((∂A_{r_{j+1}}(η) − B_{r_{j+1}}(η)) − (∂A_{r_j}(η) − B_{r_j}(η))) = D_{j+1}(η) − (Z_{j+1}(η) − Z_j(η)). So ∂W_0 = D_0 − Z_0 and ∂W_{j+1} = D_{j+1} − (Z_{j+1} − Z_j).
10. (Supports.)
   (10a) K_j := spt T ∩ {d ≥ r_j} is closed (S (ii); d continuous). Let tsupport ω be disjoint from K_j. For x ∈ E_j ∩ spt T we have x ∈ K_j, so x ∉ tsupport ω, ω(x) = 0 and ξ(x)(ω(x)) = 0; since μ_T(ℝ^P \ spt T) = 0 (1d), the integrand of step 7 vanishes μ_T-a.e. on E_j, so W_j(ω) = 0 (integral_eq_zero_of_ae). By S (i), spt W_j ⊆ spt T ∩ {d ≥ r_j}.
   (10b) In the same way, using step 7 for D_j and μ_∂(ℝ^P \ spt ∂T) = 0 (step 2), spt D_j ⊆ spt ∂T ∩ {d ≥ r_j}.
   (10c) If tsupport η is disjoint from the closed set {d = r_j}, then Z_j(η) = ∂A_{r_j}(η) − B_{r_j}(η) = 0 by (SL3); so spt Z_j ⊆ {d = r_j} (S (i)). If tsupport η is disjoint from spt T, then ∂A_{r_j}(η) = A_{r_j}(dη) = ∫_{{d<r_j}} ξ(dη) dμ_T = 0, because the form underlying dη vanishes outside tsupport(dη) ⊆ tsupport η (tsupport_exteriorDerivative_subset), hence on spt T, and μ_T(ℝ^P \ spt T) = 0; and B_{r_j}(η) = ∫_{{d<r_j}} ξ_∂(η) dμ_∂ = 0, because η vanishes on spt T ⊇ spt ∂T (S (v)) and μ_∂(ℝ^P \ spt ∂T) = 0. Hence Z_j(η) = 0 and spt Z_j ⊆ spt T (S (i)). Together spt Z_j ⊆ spt T ∩ {d = r_j}.
   (10d) spt ∂T ⊆ spt T (S (v)). Each of spt W_j, spt D_j, spt Z_j is closed (S (ii)) and contained in the compact set spt T, hence compact (IsCompact.of_isClosed_subset).
11. (Masses.) By ML (a.e. bounds (1b) and step 2; formulas of step 7 and (SL1)), M(W_j) ≤ μ_T(E_j), M(D_j) ≤ μ_∂(E_j) and M(A_t) ≤ μ_T({d < t}).
   (11a) M(W_0) ≤ μ_T(ℝ^P) = M(T) and M(D_0) ≤ μ_∂(ℝ^P) = M(∂T).
   (11b) E_{j+1} ⊆ {d < r_j} ⊆ {d < ρ_j}, so M(W_{j+1}) ≤ μ_T({d < ρ_j}) = M_{{d<ρ_j}}(T) ≤ C·ofReal(ρ_j^{m+2})·M(T) = C·ofReal((1/2)^{(j+2)(m+2)})·M(T) (density hypothesis with r := ρ_j; ρ_j^{m+2} = (1/2)^{(j+2)(m+2)} by pow_mul), and likewise M(D_{j+1}) ≤ μ_∂({d < ρ_j}) = M_{{d<ρ_j}}(∂T) ≤ C·ofReal((1/2)^{(j+2)(m+2)})·M(∂T).
   (11c) By (SL4) and (5a), M(Z_j) ≤ 4C·ofReal(ρ_j^{m+1})·M(T) = 4C·ofReal((1/2)^{(j+2)(m+1)})·M(T).
   All these bounds are finite (C, the ofReal values, M(T) and M(∂T) are finite).
12. (Boundary masses.)
   (12a) By step 9 and MS, M(∂W_0) ≤ M(D_0) + M(Z_0) and M(∂W_{j+1}) ≤ M(D_{j+1}) + M(Z_{j+1}) + M(Z_j), finite by step 11.
   (12b) If m = 0, boundaryMassOn D_j ℝ^P = boundaryMassOn Z_j ℝ^P = 0 by definition. Let m = k + 1. Apply (SL) a second time with k, U := ℝ^P, the current ∂T ∈ 𝒟_{k+1}, μ := μ_∂, μ' := 0 (the zero measure), ξ := ξ_∂, ξ' := 0, f := d, L := 1. Its hypotheses hold: μ_∂ and 0 are finite on compacts; ξ_∂ and 0 are a.e. strongly measurable and satisfy the a.e. bounds (step 2; trivially for the zero measure); ∂T(η) = ∫ ξ_∂(η) dμ_∂ (step 2); ∂(∂T) = 0 (GeometricCurrentOn.boundary_boundary) and ∫ 0 d0 = 0 (integral_zero_measure). It yields A′, B′ with A′_t(η) = ∫_{{d<t}} ξ_∂(η) dμ_∂ = B_t(η), so A′_t = B_t (ext), and B′_t(ζ) = ∫_{{d<t}} 0 d0 = 0, so B′_t = 0, and M(∂A′_t − B′_t) ≤ liminf_{h→0+} ofReal(h⁻¹)·μ_∂({t − h < d < t}). As ∂A′_t − B′_t = ∂B_t (ext: ∂B_t(ζ) − 0 = ∂B_t(ζ)), (5b) gives M(∂B_{r_j}) < ∞ for every j. Using (X − Y).boundary = ∂X − ∂Y (ext), ∂∂ = 0, M(0) = 0 and MS: ∂D_0 = ∂∂T − ∂B_{r_0} = 0 − ∂B_{r_0}, ∂D_{j+1} = ∂B_{r_j} − ∂B_{r_{j+1}} and ∂Z_j = ∂∂A_{r_j} − ∂B_{r_j} = 0 − ∂B_{r_j} have finite mass. For degree k + 1, boundaryMassOn X ℝ^P = M(∂X) by definition, which proves the claim.
13. (Σ_j W_j(ω) = T(ω).) Fix ω ∈ 𝒟ⁿ. (i) Absolute convergence: by EB (W := ℝ^P, c := c_ω) and step 11, |W_j(ω)| ≤ c_ω·M(W_j).toReal ≤ c_ω·μ_T(E_j).toReal; the E_j are pairwise disjoint Borel sets, so Σ_j μ_T(E_j) = μ_T(⋃_j E_j) ≤ μ_T(ℝ^P) < ∞ (measure_iUnion); hence Σ_j |W_j(ω)| < ∞ (ENNReal.summable_toReal) and (W_j(ω))_j is summable (Summable.of_norm_bounded). (ii) Partial sums: by induction on N, Σ_{j=0}^{N} W_j(ω) = T(ω) − A_{r_N}(ω), because W_0(ω) = T(ω) − A_{r_0}(ω) and W_{N+1}(ω) = A_{r_N}(ω) − A_{r_{N+1}}(ω). (iii) M(A_{r_N}) ≤ μ_T({d < r_N}) ≤ μ_T({d < ρ_N}) ≤ C·ofReal(ρ_N^{m+2})·M(T) → 0 as N → ∞ (ρ_N → 0, M(T) < ∞; ENNReal.Tendsto.const_mul), so by EB |A_{r_N}(ω)| ≤ c_ω·M(A_{r_N}).toReal → 0. Hence the partial sums tend to T(ω), and by (i) HasSum (j ↦ W_j(ω)) (T(ω)) (Summable.hasSum_iff_tendsto_nat).
14. (Conclusion.) The radii r_j (step 5) and the currents W_j, D_j, Z_j (step 6) satisfy: the radius bounds (step 5); HasSum (step 13); the boundary relations (step 9); integrality of W_j (step 8); compactness of supports (10d), finiteness of M(W_j), M(D_j), M(Z_j) (step 11), of M(∂W_j) (12a) and of boundaryMassOn D_j ℝ^P, boundaryMassOn Z_j ℝ^P (12b); the support inclusions (10a)–(10c); and the mass bounds (11a)–(11c). ∎

## Key steps

1. μ_T := R.measure (R an IMRep of T) represents T with |ξ| ≤ 1 a.e. and M_W(T) = μ_T(W) for open W (MR, IR, IMC(d)); (REP) gives (μ_∂, ξ_∂) for ∂T; both are finite and null off spt T, spt ∂T (VO).
2. Slice T by d with (SL): A_t = T⌞{d<t}, B_t = (∂T)⌞{d<t}, ∂A_t = B_t off {d = t}, M(∂A_t − B_t) ≤ liminf h⁻¹μ_T({t−h<d<t}).
3. Good radii r_j ∈ (ρ_j/2, ρ_j), ρ_j = 2^{−j−2} (GR + density bound): M(Z_j) ≤ 4Cρ_j^{m+1}M(T) and M(∂B_{r_j}) < ∞ (second slicing of ∂T).
4. W_0 = T − A_{r_0}, W_{j+1} = A_{r_j} − A_{r_{j+1}}, D_j likewise from B, Z_j = ∂A_{r_j} − B_{r_j}; W_j, D_j are integrals over the half-open shells E_j, W_j is IM by (IMC)(b) + IR.
5. ∂W_0 = D_0 − Z_0, ∂W_{j+1} = D_{j+1} − (Z_{j+1} − Z_j); supports via S(i); masses via ML and the density bounds; Σ_j W_j(ω) = T(ω) since M(A_{r_N}) → 0 and Σ_j μ_T(E_j) ≤ M(T).

## Reference use

### local-project

Queries:
- `cat RUN/local-references/123e8435b4a2469b/manifest.json (project_commit b4d606db, mathlib_commit 25730c7c); git -C SNAPSHOT/mathlib rev-parse HEAD (25730c7c); git rev-parse HEAD (b4d606db); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); cmp SNAPSHOT/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical)`
- `rg -n -i -l 'deformation|skeleton|telescop|mcshane' SNAPSHOT/project/GMT -g '*.lean' (only Ch06 Contract/Submission: the unproved specification DeformationTheorem under main_theorem := by sorry, not imported by Ch07; and Ch02 IsAdmissibleDeformation, the unrelated smooth first-variation deformations)`
- `rg -n 'theorem LipschitzOnWith.extend_real|theorem Monotone.ae_differentiableAt|theorem mul_meas_ge_le_lintegral₀|theorem ENNReal.tsum_geometric|theorem lipschitz_infDist_pt|theorem isClosed_cthickening|theorem enorm_integral_le_lintegral_enorm|theorem measurable_deriv|theorem HasDerivAt.tendsto_slope_zero_left|theorem mem_cthickening_of_dist_le|theorem isClosedEmbedding_coe_real|theorem ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one' SNAPSHOT/mathlib/Mathlib (all found)`
- `rg -n 'theorem countablyRectifiable_of_measure_zero|theorem tsupport_exteriorDerivative_subset|theorem GeometricCurrentOn.isOpen_zeroRegion|theorem WeaklyConvergesOn.massOn_le_liminf' lake-packages-25730c7c/simongmt/Poincare/SimonGMT (all found); sed of SimonGMT Chapter06 Currents.lean, Mass.lean, CurrentLocalEquality.lean (GeometricCurrentOn, ext, zero_apply, boundary_apply, massAdmissibleOn, massOn, mass, le_massOn, VanishesOn, zeroRegion, support)`
- `rg -n 'dimred_mbl_dtsd_' SNAPSHOT/project SNAPSHOT/mathlib/Mathlib lake-packages-25730c7c/simongmt/Poincare (no match); python3 scan of RUN/dag.json lean_names (1609 nodes) for the prefix dimred_mbl_dtsd_ (no match)`
- `python3 scans of RUN/dag.json: the selected frozen type and the frozen types of its four sibling dependencies RET, GC, PF, IMS are byte-identical to those of the twin node cmcdt_skeleton_deformation and its siblings; the six new child types generated from the selected pieces are byte-identical to the twin's audited child types (decomposition-v1.json of the twin node directory ...-ske-9a64d46574); accepted declarations with exactly the needed types: cmc_fcl_massOn_le_measure_inter (= the twin's mass child), cbr_cc_current_algebra (conjunct (a) = the twin's zero-IM child), cmcs_smi_lintegral_ofReal_deriv_le, cmc_fc_cs_massOn_sub_le, cmr_abs_apply_le_massOn, lcmp_imRep_measure_restrict (status accepted, candidate commits present)`
- `grep/sed of the active runtime (_recursive_lean/runtime.py _decompose, _existing_lean_name_problem, _accepted_checkpoint, _install_parent_supplied_child_handoff, _render_parent_supplied_natural; inherited.py cited_inherited) and of verifier/gmt-compare.py (child_modules, contract_scope); python3 -I check that no child proof, key step or this ledger cites, as a whole identifier, the Lean name of a dependency of the selected node or of its ancestors`
- `git show <accepted commit>:GMT/Ch07/Submission.lean for the six reused declarations (1041782e, 791f7d72, 6efe397f, ea5c1199, 7a706164, ae810e9b); lake env lean on each with #print axioms (propext, Classical.choice, Quot.sound only)`
- `lake env lean SCRATCH/Types.lean (4 sibling types, 12 child types and the selected type elaborate; only sorry warnings); python3 -I build_challenges.py with the verifier's own child_modules(contract mode) and lake env lean SCRATCH/chal/Challenge_*.lean (13 files, 0 errors); both validate_lean_statement implementations on all 12 child types (accepted unchanged); lake env lean SCRATCH/AssemblyAx.lean (#print axioms of the selected theorem: propext, Classical.choice, Quot.sound and the ten named stubs, no sorryAx)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Deriv/Slope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/Int.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-9b75b9802b/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-ske-9a64d46574/decomposition-v1.json`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/inherited.py`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/dimred_mbl_dtsd_skeleton_deformation_decomposition/Types.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/dimred_mbl_dtsd_skeleton_deformation_decomposition/AssemblyAx.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/dimred_mbl_dtsd_skeleton_deformation_decomposition/build_challenges.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/dimred_mbl_dtsd_skeleton_deformation_decomposition/chal/Challenge_dimred_mbl_dtsd_shell_decomposition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/dimred_mbl_dtsd_skeleton_deformation_decomposition/chal/Challenge_dimred_mbl_dtsd_telescoping_deformation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/dimred_mbl_dtsd_skeleton_deformation_decomposition/ReusedML.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/dimred_mbl_dtsd_skeleton_deformation_decomposition/ReusedCA.lean`

Pins match (project b4d606db, Mathlib 25730c7c) and Submission.lean is byte-identical to the frozen contract. Neither the snapshot project nor Mathlib contains a deformation theorem, Lipschitz push-forward of currents or skeleton retraction: the snapshot's Ch06 DeformationTheorem is an unproved specification that Ch07 does not import, and Ch02 IsAdmissibleDeformation is unrelated. Mathlib supplies every tool the child proofs cite (McShane extension LipschitzOnWith.extend_real, Monotone.ae_differentiableAt, measurable_deriv, HasDerivAt.tendsto_slope_zero_left, Markov mul_meas_ge_le_lintegral₀, enorm_integral_le_lintegral_enorm, ENNReal.tsum_geometric, lipschitz_infDist_pt, isClosed_cthickening, mem_cthickening_of_dist_le, Int.isClosedEmbedding_coe_real); SimonGMT supplies countablyRectifiable_of_measure_zero, tsupport_exteriorDerivative_subset, isOpen_zeroRegion and the mass/support definitions. The DAG supplies six accepted declarations with exactly the needed types, which are reused (their proofs recompile with standard axioms). The six new child types are byte-identical to the twin node's audited child types, carry the fresh prefix dimred_mbl_dtsd_ (no collision), elaborate in the comparator's challenge form and pass both validators; the assembly of the selected frozen type from the sibling and child types compiles with only propext, Classical.choice and Quot.sound beyond the named stubs. No child proof, key step or this ledger names a dependency of the selected node or of its ancestors, so no child is held on an unaccepted inherited prerequisite.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
