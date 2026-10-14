<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.skeleton_deformation-a1.telescoping_deformation-a1 -->

## Theorem `Submission.dimred_mbl_dtsd_telescoping_deformation`

Deformation of a decomposed current and summation of the deformed series (Simon Ch. 6, proof of 5.1, displays (11)–(25)). Assume, as a hypothesis of the statement, (VO): the first antecedent of the parent statement (for all P, n, U, S ∈ 𝒟_n(U) and ω ∈ 𝒟ⁿ(U): S(ω) = 0 whenever tsupport ω is disjoint from spt S). Let P, m ∈ ℕ and let push_k(F, X) ∈ 𝒟_k(ℝ^P), homot_k(F, G, X) ∈ 𝒟_{k+1}(ℝ^P) be operations (k ∈ ℕ, F, G : ℝ^P → ℝ^P, X ∈ 𝒟_k(ℝ^P), domain univ) satisfying (PF), the conclusion, for this P, of the frozen type of the parent's sibling PF (the Lipschitz push-forward and homotopy theorem of the parent's decomposition; its conclusion is taken verbatim as a hypothesis): calling X normal with compact support (NC) when spt X is compact, M(X) < ∞ and boundaryMassOn X univ < ∞ (= M(∂X) for k ≥ 1, 0 for k = 0), (1) push_k(id, X) = X for every NC X of degree k; and, for all Λ ∈ ℝ≥0, all Λ-Lipschitz F, G, F', G' and all NC X, Y of degree k: (2) push_k(F, X − Y) = push_k(F, X) − push_k(F, Y) and homot_k(F, G, X − Y) = homot_k(F, G, X) − homot_k(F, G, Y); (3) if F = F' and G = G' on spt X then push_k(F, X) = push_k(F', X) and homot_k(F, G, X) = homot_k(F', G', X); (4) M(push_k(F, X)) ≤ Λ^k M(X), spt push_k(F, X) ⊆ F(spt X), M(homot_k(F, G, X)) ≤ δ′(2Λ)^k M(X) whenever δ′ ∈ ℝ and |F(x) − G(x)| ≤ δ′ for x ∈ spt X, and spt homot_k(F, G, X) ⊆ {F(x) + t(G(x) − F(x)) : x ∈ spt X, t ∈ [0, 1]}; (5) for X ∈ 𝒟_{k+1}(ℝ^P) with compact support, M(X) < ∞, M(∂X) < ∞: ∂ push_{k+1}(F, X) = push_k(F, ∂X), push_{k+1}(G, X) − push_{k+1}(F, X) − homot_k(F, G, ∂X) = ∂ homot_{k+1}(F, G, X), and if X is integer multiplicity then push_{k+1}(F, X) and homot_{k+1}(F, G, X) are integer multiplicity; (6) for X ∈ 𝒟_0(ℝ^P) with compact support and finite mass, push_0(G, X) − push_0(F, X) = ∂ homot_0(F, G, X). Assume also (IMS), the conclusion, for this P, of the frozen type of the parent's sibling IMS (the summation theorem for integer multiplicity series of the parent's decomposition; its conclusion is taken verbatim as a hypothesis): for every k ∈ ℕ and all W_i ∈ 𝒟_{k+1}(ℝ^P) (i ∈ ℕ, domain univ) with Σ_i M(W_i) < ∞ (tsum in [0, ∞]) there is S ∈ 𝒟_{k+1}(ℝ^P) such that: for every test form ω, the series Σ_i W_i(ω) has sum S(ω) (HasSum); M(S) ≤ Σ_i M(W_i); spt S ⊆ closure(⋃_i spt W_i); and if every W_i is integer multiplicity then S is integer multiplicity. Let T ∈ 𝒟_{m+1}(ℝ^P), W_j ∈ 𝒟_{m+1}(ℝ^P), D_j, Z_j ∈ 𝒟_m(ℝ^P), φ_j : ℝ^P → ℝ^P, Λ_j ∈ ℝ≥0 (j ∈ ℕ), δ ∈ ℝ and L, A, A' ⊆ ℝ^P, and assume: Σ_j W_j(ω) = T(ω) (HasSum) for every ω; ∂W_0 = D_0 − Z_0 and ∂W_{j+1} = D_{j+1} − (Z_{j+1} − Z_j); every W_j is integer multiplicity; spt W_j, spt D_j, spt Z_j are compact, M(W_j), M(∂W_j), M(D_j), M(Z_j) < ∞ and boundaryMassOn D_j ℝ^P, boundaryMassOn Z_j ℝ^P < ∞; φ_j is Λ_j-Lipschitz, 1 ≤ Λ_j ≤ Λ_{j+1}; φ_{j+1} = φ_j on spt Z_j; dist(φ_j(x), x) ≤ δ for x ∈ spt W_j ∪ spt D_j ∪ spt Z_j; L is closed and φ_j(x) ∈ L for x ∈ spt W_j; spt W_j ⊆ A and spt D_j ⊆ A'; Σ_j (2Λ_j)^{m+1}M(W_j) < ∞, Σ_j (2Λ_j)^m M(D_j) < ∞ and (2Λ_j)^m M(Z_j) → 0 (in [0, ∞]). Then there are Q₀ ∈ 𝒟_{m+1}(ℝ^P), R₁ ∈ 𝒟_{m+2}(ℝ^P), S₁ ∈ 𝒟_{m+1}(ℝ^P) with: Q₀ and R₁ integer multiplicity; T − Q₀ − S₁ = ∂R₁; spt Q₀ ⊆ L ∩ cthickening(δ, A), spt R₁ ⊆ cthickening(δ, A), spt ∂Q₀ ⊆ cthickening(δ, A'), spt S₁ ⊆ cthickening(δ, A') (Metric.cthickening); M(Q₀) ≤ Σ_j (2Λ_j)^{m+1}M(W_j), M(∂Q₀) ≤ Σ_j (2Λ_j)^m M(D_j), M(R₁) ≤ δ·Σ_j (2Λ_j)^{m+1}M(W_j) and M(S₁) ≤ δ·Σ_j (2Λ_j)^m M(D_j) (δ read as ENNReal.ofReal δ). Conventions: ℝ^P = Euclid P (EuclideanSpace ℝ (Fin P)); for U ⊆ ℝ^P, 𝒟^k(U) = TestFormOn U k (smooth k-forms on ℝ^P whose compact tsupport lies in U) and 𝒟_k(U) = GeometricCurrentOn U k (SimonGMT Chapter06), X(ω) the value of X on ω; X − Y is the contract subtraction, (X − Y)(ω) = X(ω) − Y(ω) (definitional); 0 is the zero current; ∂X = X.boundary, ∂X(η) = X(dη) (GeometricCurrentOn.boundary_apply, dη = exteriorDerivativeTestOn U k η, whose underlying form is exteriorDerivative η); currents are equal when their values agree (GeometricCurrentOn.ext). |α| = covectorEuclideanNorm α is the Euclidean coefficient norm of a covector. M_G(X) = X.massOn G ∈ [0, ∞] is the supremum of ENNReal.ofReal X(ω) over the ω ∈ 𝒟^k(U) with tsupport ω ⊆ G and |ω(x)| ≤ 1 for all x (such ω are admissible for M_G, massAdmissibleOn U k G); M(X) = X.mass = M_U(X); boundaryMassOn X G = M_G(∂X) if k ≥ 1 and 0 if k = 0. spt X = X.support (Simon 6.2.11) = U minus the zero region, the union of the open W with compact closure contained in U on which X vanishes (X(ω) = 0 whenever tsupport ω ⊆ W). IM = IsIntegerMultiplicity: X is represented by an IMRep R = (M, θ, ξ) of the contract (R.carrier, R.mult, R.orient), i.e. X(ω) = R.action ω = ∫_M θ⟨ω, ξ⟩ dHⁿ, and R.measure = θ·Hⁿ⌞M (Hⁿ = μHE[n]).

Node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.skeleton_deformation-a1.telescoping_deformation-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5939

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/7085, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4912, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4607

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2794, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5097, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4607, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4912, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6981, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6995, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7008, https://github.com/ZhengyangZhang06/gmt-formalize/issues/7017

## Lean problem

Declaration: `Submission.dimred_mbl_dtsd_telescoping_deformation`

```lean
(∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → ∀ (P m : ℕ) (push : ∀ k : ℕ, (Euclid P → Euclid P) → GeometricCurrentOn (univ : Set (Euclid P)) k → GeometricCurrentOn (univ : Set (Euclid P)) k) (homot : ∀ k : ℕ, (Euclid P → Euclid P) → (Euclid P → Euclid P) → GeometricCurrentOn (univ : Set (Euclid P)) k → GeometricCurrentOn (univ : Set (Euclid P)) (k + 1)), ((∀ (k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → push k (fun x => x) X = X) ∧ (∀ (k : ℕ) (Λ : NNReal) (F G : Euclid P → Euclid P) (X Y : GeometricCurrentOn (univ : Set (Euclid P)) k), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact Y.support → Y.mass < ∞ → boundaryMassOn Y univ < ∞ → push k F (X - Y) = push k F X - push k F Y ∧ homot k F G (X - Y) = homot k F G X - homot k F G Y) ∧ (∀ (k : ℕ) (Λ : NNReal) (F G F' G' : Euclid P → Euclid P) (X : GeometricCurrentOn (univ : Set (Euclid P)) k), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith Λ F' → LipschitzWith Λ G' → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → EqOn F F' X.support → EqOn G G' X.support → push k F X = push k F' X ∧ homot k F G X = homot k F' G' X) ∧ (∀ (k : ℕ) (Λ : NNReal) (F G : Euclid P → Euclid P) (X : GeometricCurrentOn (univ : Set (Euclid P)) k), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (push k F X).mass ≤ (Λ : ℝ≥0∞) ^ k * X.mass ∧ (push k F X).support ⊆ F '' X.support ∧ (∀ δ : ℝ, (∀ x ∈ X.support, dist (F x) (G x) ≤ δ) → (homot k F G X).mass ≤ ENNReal.ofReal δ * (2 * (Λ : ℝ≥0∞)) ^ k * X.mass) ∧ (homot k F G X).support ⊆ {y : Euclid P | ∃ x ∈ X.support, ∃ t ∈ Icc (0 : ℝ) 1, y = F x + t • (G x - F x)}) ∧ (∀ (k : ℕ) (Λ : NNReal) (F G : Euclid P → Euclid P) (X : GeometricCurrentOn (univ : Set (Euclid P)) (k + 1)), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact X.support → X.mass < ∞ → X.boundary.mass < ∞ → (push (k + 1) F X).boundary = push k F X.boundary ∧ push (k + 1) G X - push (k + 1) F X - homot k F G X.boundary = (homot (k + 1) F G X).boundary ∧ (IsIntegerMultiplicity X → IsIntegerMultiplicity (push (k + 1) F X) ∧ IsIntegerMultiplicity (homot (k + 1) F G X))) ∧ ∀ (Λ : NNReal) (F G : Euclid P → Euclid P) (X : GeometricCurrentOn (univ : Set (Euclid P)) 0), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact X.support → X.mass < ∞ → push 0 G X - push 0 F X = (homot 0 F G X).boundary) → (∀ (k : ℕ) (W : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (k + 1)), ∑' i, (W i).mass < ∞ → ∃ S : GeometricCurrentOn (univ : Set (Euclid P)) (k + 1), (∀ ω : TestFormOn (univ : Set (Euclid P)) (k + 1), HasSum (fun i => W i ω) (S ω)) ∧ S.mass ≤ ∑' i, (W i).mass ∧ S.support ⊆ closure (⋃ i, (W i).support) ∧ ((∀ i, IsIntegerMultiplicity (W i)) → IsIntegerMultiplicity S)) → ∀ (T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (W : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (D Z : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) m) (φ : ℕ → Euclid P → Euclid P) (Λ : ℕ → NNReal) (δ : ℝ) (L A A' : Set (Euclid P)), (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), HasSum (fun j => W j ω) (T ω)) → (W 0).boundary = D 0 - Z 0 → (∀ j, (W (j + 1)).boundary = D (j + 1) - (Z (j + 1) - Z j)) → (∀ j, IsIntegerMultiplicity (W j)) → (∀ j, IsCompact (W j).support ∧ (W j).mass < ∞ ∧ (W j).boundary.mass < ∞) → (∀ j, IsCompact (D j).support ∧ (D j).mass < ∞ ∧ boundaryMassOn (D j) univ < ∞) → (∀ j, IsCompact (Z j).support ∧ (Z j).mass < ∞ ∧ boundaryMassOn (Z j) univ < ∞) → (∀ j, LipschitzWith (Λ j) (φ j)) → (∀ j, 1 ≤ Λ j) → (∀ j, Λ j ≤ Λ (j + 1)) → (∀ j, EqOn (φ (j + 1)) (φ j) (Z j).support) → (∀ j, ∀ x ∈ (W j).support ∪ (D j).support ∪ (Z j).support, dist (φ j x) x ≤ δ) → IsClosed L → (∀ j, ∀ x ∈ (W j).support, φ j x ∈ L) → (∀ j, (W j).support ⊆ A) → (∀ j, (D j).support ⊆ A') → ∑' j, (2 * (Λ j : ℝ≥0∞)) ^ (m + 1) * (W j).mass < ∞ → ∑' j, (2 * (Λ j : ℝ≥0∞)) ^ m * (D j).mass < ∞ → Tendsto (fun j => (2 * (Λ j : ℝ≥0∞)) ^ m * (Z j).mass) atTop (𝓝 0) → ∃ (Q₀ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (R₁ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 2)) (S₁ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), IsIntegerMultiplicity Q₀ ∧ IsIntegerMultiplicity R₁ ∧ T - Q₀ - S₁ = R₁.boundary ∧ Q₀.support ⊆ L ∩ cthickening δ A ∧ R₁.support ⊆ cthickening δ A ∧ Q₀.boundary.support ⊆ cthickening δ A' ∧ S₁.support ⊆ cthickening δ A' ∧ Q₀.mass ≤ ∑' j, (2 * (Λ j : ℝ≥0∞)) ^ (m + 1) * (W j).mass ∧ Q₀.boundary.mass ≤ ∑' j, (2 * (Λ j : ℝ≥0∞)) ^ m * (D j).mass ∧ R₁.mass ≤ ENNReal.ofReal δ * ∑' j, (2 * (Λ j : ℝ≥0∞)) ^ (m + 1) * (W j).mass ∧ S₁.mass ≤ ENNReal.ofReal δ * ∑' j, (2 * (Λ j : ℝ≥0∞)) ^ m * (D j).mass
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
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.skeleton_deformation-a1.telescoping_deformation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 7–9 of the parent's supplied proof (parent E3–E5; Simon Ch. 6, proof of 5.1, displays (11)–(25)). The parent deforms with F := id, G := φ_j and sums 0 − H_j, 0 − E'_j, which needs (IMC)(c) for the integrality of 0 − H_j; here the homotopy is taken from φ_j to the identity (F := φ_j, G := id in (PF)), so the homotopy currents already enter with the sign needed for T − Q₀ − S₁ = ∂R₁ and no negation of currents (hence no (IMC)(c)) is required. All other steps are the parent's. Siblings used: S = dimred_mbl_dtsd_support_calculus, MS = cmc_fc_cs_massOn_sub_le, EB = cmr_abs_apply_le_massOn.

Notation. All currents are on univ = ℝ^P; M(X) = M_{ℝ^P}(X); id := (x ↦ x). PF1, …, PF6 are the six conjuncts of (PF): PF1 push_k(id, X) = X; PF2 linearity of push_k(F, ·) and homot_k(F, G, ·) on differences; PF3 locality; PF4 mass bounds M(push_k(F, X)) ≤ Λ^k M(X) and M(homot_k(F, G, X)) ≤ δ'(2Λ)^k M(X) when dist(F x, G x) ≤ δ' on spt X, and support bounds spt push_k(F, X) ⊆ F(spt X), spt homot_k(F, G, X) ⊆ {F(x) + t(G(x) − F(x)) : x ∈ spt X, t ∈ [0, 1]}; PF5 for X ∈ 𝒟_{k+1} with compact support, M(X), M(∂X) < ∞: ∂push_{k+1}(F, X) = push_k(F, ∂X), push_{k+1}(G, X) − push_{k+1}(F, X) − homot_k(F, G, ∂X) = ∂homot_{k+1}(F, G, X), and integrality of push_{k+1}(F, X), homot_{k+1}(F, G, X) for IM X (PF6 is not used). PF1–PF4 require X (and Y) to be NC_k: compact support, finite mass and boundaryMassOn X ℝ^P < ∞; maps must be Λ-Lipschitz for one common Λ. For a test form ω, c_ω := sup_x |ω(x)| < ∞ (x ↦ |ω(x)| is continuous and vanishes outside the compact tsupport ω), and dω denotes the exterior-derivative test form, so ∂X(ω) = X(dω).

0. (Preliminaries.)
   (0a) φ_j is Λ_j- and Λ_{j+1}-Lipschitz (Λ_j ≤ Λ_{j+1}, LipschitzWith.weaken); id is 1-Lipschitz, hence Λ_j- and Λ_{j+1}-Lipschitz (1 ≤ Λ_j ≤ Λ_{j+1}).
   (0b) W_j ∈ NC_{m+1} (for degree m + 1, boundaryMassOn W_j ℝ^P = M(∂W_j) by definition); D_j, Z_j ∈ NC_m (hypotheses).
   (0c) Z_{j+1} − Z_j ∈ NC_m: spt(Z_{j+1} − Z_j) ⊆ spt Z_{j+1} ∪ spt Z_j (S (iii)), a compact set, and spt(Z_{j+1} − Z_j) is closed (S (ii)), hence compact; M(Z_{j+1} − Z_j) ≤ M(Z_{j+1}) + M(Z_j) < ∞ (MS); for m = 0 boundaryMassOn of a 0-current is 0, and for m ≥ 1, ∂(Z_{j+1} − Z_j) = ∂Z_{j+1} − ∂Z_j (ext), so its mass is ≤ M(∂Z_{j+1}) + M(∂Z_j) < ∞ (MS).
   (0d) (Evaluation.) If M(X) < ∞ then |X(ω)| ≤ c_ω·M(X).toReal (EB with W := ℝ^P, tsupport ω ⊆ ℝ^P). Hence M(X_N) → 0 implies X_N(ω) → 0 (ENNReal.toReal is continuous at 0), and Σ_j M(X_j) < ∞ implies Σ_j |X_j(ω)| < ∞ (ENNReal.summable_toReal), so (X_j(ω))_j is summable (Summable.of_norm_bounded).
1. (Deformed pieces.) V_j := push_{m+1}(φ_j, W_j), H_j := homot_{m+1}(φ_j, id, W_j) ∈ 𝒟_{m+2}, Y_j := push_m(φ_j, D_j), E′_j := homot_m(φ_j, id, D_j) ∈ 𝒟_{m+1}, L′_j := push_m(φ_j, Z_j), K_j := homot_m(φ_j, id, Z_j) ∈ 𝒟_{m+1}.
2. (Locality.) PF3 with Λ := Λ_{j+1}, F := φ_{j+1}, G := id, F' := φ_j, G' := id (all Λ_{j+1}-Lipschitz by (0a)), X := Z_j ∈ NC_m and φ_{j+1} = φ_j on spt Z_j (hypothesis), id = id: push_m(φ_{j+1}, Z_j) = L′_j and homot_m(φ_{j+1}, id, Z_j) = K_j.
3. (Deforming the boundaries.) PF2 with Λ := Λ_0, F := φ_0, G := id and ∂W_0 = D_0 − Z_0 (D_0, Z_0 ∈ NC_m): push_m(φ_0, ∂W_0) = Y_0 − L′_0 and homot_m(φ_0, id, ∂W_0) = E′_0 − K_0. PF2 with Λ := Λ_{j+1}, F := φ_{j+1}, G := id, applied to ∂W_{j+1} = D_{j+1} − (Z_{j+1} − Z_j) (D_{j+1}, Z_{j+1} − Z_j ∈ NC_m by (0b), (0c)) and then to Z_{j+1} − Z_j (Z_{j+1}, Z_j ∈ NC_m), together with step 2: push_m(φ_{j+1}, ∂W_{j+1}) = Y_{j+1} − (L′_{j+1} − L′_j) and homot_m(φ_{j+1}, id, ∂W_{j+1}) = E′_{j+1} − (K_{j+1} − K_j).
4. (Homotopy formula and integrality.) PF5 with k := m, Λ := Λ_j, F := φ_j, G := id and X := W_j (compact support, M(W_j), M(∂W_j) < ∞) gives
   (4a) ∂V_j = push_m(φ_j, ∂W_j);
   (4b) push_{m+1}(id, W_j) − V_j − homot_m(φ_j, id, ∂W_j) = ∂H_j, and push_{m+1}(id, W_j) = W_j by PF1 (W_j ∈ NC_{m+1}); hence W_j − V_j − homot_m(φ_j, id, ∂W_j) = ∂H_j;
   (4c) since W_j is IM, V_j and H_j are IM.
5. (Bounds; PF4 with Λ := Λ_j, F := φ_j, G := id, and δ, using dist(φ_j(x), id(x)) ≤ δ on spt W_j, spt D_j, spt Z_j.)
   (5a) M(V_j) ≤ Λ_j^{m+1}M(W_j) ≤ (2Λ_j)^{m+1}M(W_j); M(Y_j) ≤ Λ_j^m M(D_j) ≤ (2Λ_j)^m M(D_j); M(L′_j) ≤ (2Λ_j)^m M(Z_j); M(H_j) ≤ δ(2Λ_j)^{m+1}M(W_j); M(E′_j) ≤ δ(2Λ_j)^m M(D_j); M(K_j) ≤ δ(2Λ_j)^m M(Z_j) (δ read as ENNReal.ofReal δ; Λ_j ≤ 2Λ_j, pow_le_pow_left). Write Σ_W := Σ_j (2Λ_j)^{m+1}M(W_j) < ∞ and Σ_D := Σ_j (2Λ_j)^m M(D_j) < ∞. Then Σ_j M(V_j) ≤ Σ_W, Σ_j M(H_j) ≤ δ·Σ_W, Σ_j M(Y_j) ≤ Σ_D and Σ_j M(E′_j) ≤ δ·Σ_D, all finite (ENNReal.tsum_le_tsum, ENNReal.tsum_mul_left, ENNReal.mul_lt_top).
   (5b) M(L′_N) → 0 and M(K_N) → 0 as N → ∞: they are bounded by (2Λ_N)^m M(Z_N) → 0 and δ·(2Λ_N)^m M(Z_N) → δ·0 = 0 (ENNReal.Tendsto.const_mul, δ ≠ ∞), and squeezed below by 0.
   (5c) If x ∈ spt W_j then x ∈ A and dist(φ_j(x), x) ≤ δ, so φ_j(x) ∈ cthickening(δ, A) (mem_cthickening_of_dist_le) and φ_j(x) ∈ L; for y = φ_j(x) + t(x − φ_j(x)) with t ∈ [0, 1], y − x = (1 − t)(φ_j(x) − x), so dist(y, x) = (1 − t)·dist(φ_j(x), x) ≤ dist(φ_j(x), x) ≤ δ (as 0 ≤ 1 − t ≤ 1) and y ∈ cthickening(δ, A) (mem_cthickening_of_dist_le). Hence spt V_j ⊆ φ_j(spt W_j) ⊆ L ∩ cthickening(δ, A) and spt H_j ⊆ cthickening(δ, A). Likewise (spt D_j ⊆ A') spt Y_j ⊆ φ_j(spt D_j) ⊆ cthickening(δ, A') and spt E′_j ⊆ cthickening(δ, A').
6. (Limits by IMS.) IMS with k := m and (V_j) (Σ M(V_j) < ∞) gives Q₀ ∈ 𝒟_{m+1}: HasSum (V_j(ω)) (Q₀(ω)) for every ω; M(Q₀) ≤ Σ_j M(V_j) ≤ Σ_W; spt Q₀ ⊆ closure ⋃_j spt V_j ⊆ L ∩ cthickening(δ, A), the latter set being closed (L closed, isClosed_cthickening; closure_minimal); Q₀ IM by (4c). IMS with k := m + 1 and (H_j) gives R₁ ∈ 𝒟_{m+2} (= 𝒟_{(m+1)+1}): HasSum (H_j(ζ)) (R₁(ζ)) for every ζ ∈ 𝒟^{m+2}; M(R₁) ≤ δ·Σ_W; spt R₁ ⊆ cthickening(δ, A); R₁ IM. IMS with k := m and (E′_j) gives S₁ ∈ 𝒟_{m+1}: HasSum (E′_j(ω)) (S₁(ω)); M(S₁) ≤ δ·Σ_D; spt S₁ ⊆ cthickening(δ, A').
7. (T − Q₀ − S₁ = ∂R₁.) Fix ω ∈ 𝒟^{m+1} and let a_j := W_j(ω) − V_j(ω) − E′_j(ω) − H_j(dω). Evaluating (4b) at ω and using step 3: for j = 0, W_0(ω) − V_0(ω) − (E′_0(ω) − K_0(ω)) = H_0(dω), i.e. a_0 = −K_0(ω); for j + 1, W_{j+1}(ω) − V_{j+1}(ω) − (E′_{j+1}(ω) − (K_{j+1}(ω) − K_j(ω))) = H_{j+1}(dω), i.e. a_{j+1} = K_j(ω) − K_{j+1}(ω). By induction, Σ_{j=0}^{N} a_j = −K_N(ω), which tends to 0 by (5b) and (0d). On the other hand, from the hypothesis HasSum (W_j(ω)) (T(ω)) and step 6 (with ζ := dω), HasSum (a_j) (T(ω) − Q₀(ω) − S₁(ω) − R₁(dω)) (HasSum.sub), so the partial sums also tend to this number (HasSum.tendsto_sum_nat). By uniqueness of limits, T(ω) − Q₀(ω) − S₁(ω) = R₁(dω) = ∂R₁(ω). As ω is arbitrary, T − Q₀ − S₁ = ∂R₁ (GeometricCurrentOn.ext; (T − Q₀ − S₁)(ω) = T(ω) − Q₀(ω) − S₁(ω) definitionally).
8. (∂Q₀.) Fix η ∈ 𝒟^m. By (0d) and (5a), (Y_j(η))_j is summable; let y(η) := Σ_j Y_j(η). Put b_j := V_j(dη) − Y_j(η) = ∂V_j(η) − Y_j(η). By (4a) and step 3: b_0 = (Y_0(η) − L′_0(η)) − Y_0(η) = −L′_0(η) and b_{j+1} = L′_j(η) − L′_{j+1}(η); so Σ_{j=0}^{N} b_j = −L′_N(η) → 0 ((5b), (0d)). Also HasSum (V_j(dη)) (Q₀(dη)) (step 6), hence HasSum (b_j) (Q₀(dη) − y(η)), and by uniqueness of limits ∂Q₀(η) = Q₀(dη) = y(η) = Σ_j Y_j(η).
   (8a) Mass. If η is admissible for M_{ℝ^P} (|η(x)| ≤ 1 for all x), EB with c := 1 gives |Y_j(η)| ≤ M(Y_j).toReal, so ENNReal.ofReal ∂Q₀(η) ≤ ENNReal.ofReal(Σ_j |Y_j(η)|) = Σ_j ENNReal.ofReal |Y_j(η)| (ENNReal.ofReal_tsum_of_nonneg, summable) ≤ Σ_j M(Y_j) (ENNReal.ofReal_toReal_le) ≤ Σ_D. Taking the supremum over admissible η, M(∂Q₀) ≤ Σ_D.
   (8b) Support. K' := cthickening(δ, A') is closed. If tsupport η is disjoint from K', then it is disjoint from spt Y_j ⊆ K' (5c), so Y_j(η) = 0 by (VO) for every j and ∂Q₀(η) = Σ_j 0 = 0. By S (i), spt ∂Q₀ ⊆ K'.
9. (Conclusion.) Q₀, R₁ and S₁ satisfy: Q₀ and R₁ are IM (step 6); T − Q₀ − S₁ = ∂R₁ (step 7); spt Q₀ ⊆ L ∩ cthickening(δ, A), spt R₁ ⊆ cthickening(δ, A), spt S₁ ⊆ cthickening(δ, A') (step 6) and spt ∂Q₀ ⊆ cthickening(δ, A') (8b); M(Q₀) ≤ Σ_W, M(R₁) ≤ δ·Σ_W, M(S₁) ≤ δ·Σ_D (step 6) and M(∂Q₀) ≤ Σ_D (8a). ∎

## Key steps

1. Deform each piece by φ_j: V_j = push(φ_j, W_j), H_j = homot(φ_j, id, W_j), Y_j, E′_j from D_j, L′_j, K_j from Z_j; locality (φ_{j+1} = φ_j on spt Z_j) identifies the slice terms of consecutive shells.
2. Linearity on ∂W_j = D_j − (Z_j − Z_{j−1}) and the homotopy formula give W_j − V_j − E′_j + K_j − K_{j−1} = ∂H_j and ∂V_j = Y_j − L′_j + L′_{j−1}; V_j, H_j are IM.
3. PF4 bounds the masses by (2Λ_j)^p-weighted masses and the supports by L ∩ cthickening(δ, A) resp. cthickening(δ, A').
4. IMS sums V_j, H_j, E′_j to IM Q₀, IM R₁ and S₁; the telescoping remainders K_N, L′_N → 0 in mass give T − Q₀ − S₁ = ∂R₁ and ∂Q₀ = Σ_j Y_j.
5. M(∂Q₀) ≤ Σ M(Y_j) via EB; spt ∂Q₀ ⊆ cthickening(δ, A') via (VO) and S(i).

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
