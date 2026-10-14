<!-- theorem-id: gmt-ch07/root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.skeleton_deformation-a1.telescoping_deformation-a1.shell_deformation-a1 -->

## Theorem `Submission.cmcsdtd_shell_deformation`

Deformation of the shells of a decomposed current (Simon Ch. 6, proof of 5.1, displays (11)–(16), (20), (22)–(23)). Let P, m ∈ ℕ and let push_k(F, X) ∈ 𝒟_k(ℝ^P), homot_k(F, G, X) ∈ 𝒟_{k+1}(ℝ^P) be operations (k ∈ ℕ, F, G : ℝ^P → ℝ^P, X ∈ 𝒟_k(ℝ^P), domain univ) satisfying (PF), the property that the conclusion of the frozen type of Submission.cmcdt_lipschitz_pushforward_homotopy asserts, for this P, of the operations push and homot it provides (the body after its ∃ push homot, taken verbatim as a hypothesis): calling X normal with compact support (NC) when spt X is compact, M(X) < ∞ and boundaryMassOn X univ < ∞ (= M(∂X) for k ≥ 1, 0 for k = 0), for all Λ ∈ ℝ≥0, all Λ-Lipschitz F, G, F', G' and all NC X, Y of degree k: (1) push_k(id, X) = X; (2) push_k(F, X − Y) = push_k(F, X) − push_k(F, Y) and homot_k(F, G, X − Y) = homot_k(F, G, X) − homot_k(F, G, Y); (3) if F = F' and G = G' on spt X then push_k(F, X) = push_k(F', X) and homot_k(F, G, X) = homot_k(F', G', X); (4) M(push_k(F, X)) ≤ Λ^k M(X), spt push_k(F, X) ⊆ F(spt X), M(homot_k(F, G, X)) ≤ δ(2Λ)^k M(X) whenever δ ∈ ℝ and |F(x) − G(x)| ≤ δ for x ∈ spt X, and spt homot_k(F, G, X) ⊆ {F(x) + t(G(x) − F(x)) : x ∈ spt X, t ∈ [0, 1]}; (5) for X ∈ 𝒟_{k+1}(ℝ^P) with compact support, M(X) < ∞, M(∂X) < ∞: ∂ push_{k+1}(F, X) = push_k(F, ∂X), push_{k+1}(G, X) − push_{k+1}(F, X) − homot_k(F, G, ∂X) = ∂ homot_{k+1}(F, G, X), and if X is integer multiplicity then push_{k+1}(F, X) and homot_{k+1}(F, G, X) are integer multiplicity; (6) for X ∈ 𝒟_0(ℝ^P) with compact support and finite mass, push_0(G, X) − push_0(F, X) = ∂ homot_0(F, G, X). Assume moreover (S-ii) every X ∈ 𝒟_m(ℝ^P) (domain univ) has closed support, and (S-iii) spt(A − B) ⊆ spt A ∪ spt B for all A, B ∈ 𝒟_m(ℝ^P) (these are conjuncts (ii) and (iii), in degree m, of the frozen type of Submission.cmcsd_support_calculus, taken as hypotheses). Let W_j ∈ 𝒟_{m+1}(ℝ^P), D_j, Z_j ∈ 𝒟_m(ℝ^P), φ_j : ℝ^P → ℝ^P, Λ_j ∈ ℝ≥0 (j ∈ ℕ), δ ∈ ℝ and L, A, A' ⊆ ℝ^P, and assume: ∂W_0 = D_0 − Z_0 and ∂W_{j+1} = D_{j+1} − (Z_{j+1} − Z_j) for all j; every W_j is integer multiplicity; spt W_j, spt D_j, spt Z_j are compact, M(W_j), M(∂W_j), M(D_j), M(Z_j) < ∞ and boundaryMassOn D_j ℝ^P, boundaryMassOn Z_j ℝ^P < ∞; φ_j is Λ_j-Lipschitz, 1 ≤ Λ_j and Λ_j ≤ Λ_{j+1}; φ_{j+1} = φ_j on spt Z_j; dist(φ_j(x), x) ≤ δ for x ∈ spt W_j ∪ spt D_j ∪ spt Z_j; φ_j(x) ∈ L for x ∈ spt W_j; spt W_j ⊆ A and spt D_j ⊆ A'. Write id := (x ↦ x) and V_j := push_{m+1}(φ_j, W_j), H_j := homot_{m+1}(φ_j, id, W_j) ∈ 𝒟_{m+2}(ℝ^P), Y_j := push_m(φ_j, D_j), E′_j := homot_m(φ_j, id, D_j), L′_j := push_m(φ_j, Z_j), K_j := homot_m(φ_j, id, Z_j). Then: (c1) W_0 − V_0 − (E′_0 − K_0) = ∂H_0; (c2) W_{j+1} − V_{j+1} − (E′_{j+1} − (K_{j+1} − K_j)) = ∂H_{j+1} for all j; (c3) ∂V_0 = Y_0 − L′_0; (c4) ∂V_{j+1} = Y_{j+1} − (L′_{j+1} − L′_j) for all j; (c5) V_j and H_j are integer multiplicity for all j; (c6) for all j, M(V_j) ≤ (2Λ_j)^{m+1}M(W_j), M(H_j) ≤ δ·((2Λ_j)^{m+1}M(W_j)), M(Y_j) ≤ (2Λ_j)^m M(D_j), M(E′_j) ≤ δ·((2Λ_j)^m M(D_j)), M(L′_j) ≤ (2Λ_j)^m M(Z_j) and M(K_j) ≤ δ·((2Λ_j)^m M(Z_j)) (in [0, ∞], δ read as ENNReal.ofReal δ); (c7) for all j, spt V_j ⊆ L ∩ cthickening(δ, A), spt H_j ⊆ cthickening(δ, A), spt Y_j ⊆ cthickening(δ, A') and spt E′_j ⊆ cthickening(δ, A') (Metric.cthickening). Conventions: ℝ^P = Euclid P (EuclideanSpace ℝ (Fin P)); for U ⊆ ℝ^P, 𝒟^k(U) = TestFormOn U k (smooth k-forms on ℝ^P whose compact tsupport lies in U) and 𝒟_k(U) = GeometricCurrentOn U k (SimonGMT Chapter06), X(ω) the value of X on ω; X − Y is the contract subtraction, (X − Y)(ω) = X(ω) − Y(ω) (definitional); ∂X = X.boundary, ∂X(η) = X(dη) (GeometricCurrentOn.boundary_apply, dη = exteriorDerivativeTestOn U k η, whose underlying form is exteriorDerivative η); currents are equal when their values agree (GeometricCurrentOn.ext). |α| = covectorEuclideanNorm α is the Euclidean coefficient norm of a covector. M_G(X) = X.massOn G ∈ [0, ∞] is the supremum of ENNReal.ofReal X(ω) over the ω ∈ 𝒟^k(U) with tsupport ω ⊆ G and |ω(x)| ≤ 1 for all x (such ω are admissible for M_G, massAdmissibleOn U k G); M(X) = X.mass = M_U(X); boundaryMassOn X G = M_G(∂X) if k ≥ 1 and 0 if k = 0. spt X = X.support (Simon 6.2.11) = U minus the zero region, the union of the open W with compact closure contained in U on which X vanishes (X(ω) = 0 whenever tsupport ω ⊆ W). IM = IsIntegerMultiplicity: X is represented by an IMRep R = (M, θ, ξ) of the contract, i.e. X(ω) = R.action ω = ∫_M θ⟨ω, ξ⟩ dHⁿ. Metric.cthickening δ E = {x : infEdist x E ≤ ENNReal.ofReal δ}; in a mass bound, a real factor δ is read as ENNReal.ofReal δ.

Node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.skeleton_deformation-a1.telescoping_deformation-a1.shell_deformation-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6336

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4912

Decomposition children: None

## Lean problem

Declaration: `Submission.cmcsdtd_shell_deformation`

```lean
∀ (P m : ℕ) (push : ∀ k : ℕ, (Euclid P → Euclid P) → GeometricCurrentOn (univ : Set (Euclid P)) k → GeometricCurrentOn (univ : Set (Euclid P)) k) (homot : ∀ k : ℕ, (Euclid P → Euclid P) → (Euclid P → Euclid P) → GeometricCurrentOn (univ : Set (Euclid P)) k → GeometricCurrentOn (univ : Set (Euclid P)) (k + 1)), ((∀ (k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → push k (fun x => x) X = X) ∧ (∀ (k : ℕ) (Λ : NNReal) (F G : Euclid P → Euclid P) (X Y : GeometricCurrentOn (univ : Set (Euclid P)) k), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact Y.support → Y.mass < ∞ → boundaryMassOn Y univ < ∞ → push k F (X - Y) = push k F X - push k F Y ∧ homot k F G (X - Y) = homot k F G X - homot k F G Y) ∧ (∀ (k : ℕ) (Λ : NNReal) (F G F' G' : Euclid P → Euclid P) (X : GeometricCurrentOn (univ : Set (Euclid P)) k), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith Λ F' → LipschitzWith Λ G' → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → EqOn F F' X.support → EqOn G G' X.support → push k F X = push k F' X ∧ homot k F G X = homot k F' G' X) ∧ (∀ (k : ℕ) (Λ : NNReal) (F G : Euclid P → Euclid P) (X : GeometricCurrentOn (univ : Set (Euclid P)) k), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (push k F X).mass ≤ (Λ : ℝ≥0∞) ^ k * X.mass ∧ (push k F X).support ⊆ F '' X.support ∧ (∀ δ : ℝ, (∀ x ∈ X.support, dist (F x) (G x) ≤ δ) → (homot k F G X).mass ≤ ENNReal.ofReal δ * (2 * (Λ : ℝ≥0∞)) ^ k * X.mass) ∧ (homot k F G X).support ⊆ {y : Euclid P | ∃ x ∈ X.support, ∃ t ∈ Icc (0 : ℝ) 1, y = F x + t • (G x - F x)}) ∧ (∀ (k : ℕ) (Λ : NNReal) (F G : Euclid P → Euclid P) (X : GeometricCurrentOn (univ : Set (Euclid P)) (k + 1)), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact X.support → X.mass < ∞ → X.boundary.mass < ∞ → (push (k + 1) F X).boundary = push k F X.boundary ∧ push (k + 1) G X - push (k + 1) F X - homot k F G X.boundary = (homot (k + 1) F G X).boundary ∧ (IsIntegerMultiplicity X → IsIntegerMultiplicity (push (k + 1) F X) ∧ IsIntegerMultiplicity (homot (k + 1) F G X))) ∧ ∀ (Λ : NNReal) (F G : Euclid P → Euclid P) (X : GeometricCurrentOn (univ : Set (Euclid P)) 0), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact X.support → X.mass < ∞ → push 0 G X - push 0 F X = (homot 0 F G X).boundary) → (∀ X : GeometricCurrentOn (univ : Set (Euclid P)) m, IsClosed X.support) → (∀ A B : GeometricCurrentOn (univ : Set (Euclid P)) m, (A - B).support ⊆ A.support ∪ B.support) → ∀ (W : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (D Z : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) m) (φ : ℕ → Euclid P → Euclid P) (Λ : ℕ → NNReal) (δ : ℝ) (L A A' : Set (Euclid P)), (W 0).boundary = D 0 - Z 0 → (∀ j, (W (j + 1)).boundary = D (j + 1) - (Z (j + 1) - Z j)) → (∀ j, IsIntegerMultiplicity (W j)) → (∀ j, IsCompact (W j).support ∧ (W j).mass < ∞ ∧ (W j).boundary.mass < ∞) → (∀ j, IsCompact (D j).support ∧ (D j).mass < ∞ ∧ boundaryMassOn (D j) univ < ∞) → (∀ j, IsCompact (Z j).support ∧ (Z j).mass < ∞ ∧ boundaryMassOn (Z j) univ < ∞) → (∀ j, LipschitzWith (Λ j) (φ j)) → (∀ j, 1 ≤ Λ j) → (∀ j, Λ j ≤ Λ (j + 1)) → (∀ j, EqOn (φ (j + 1)) (φ j) (Z j).support) → (∀ j, ∀ x ∈ (W j).support ∪ (D j).support ∪ (Z j).support, dist (φ j x) x ≤ δ) → (∀ j, ∀ x ∈ (W j).support, φ j x ∈ L) → (∀ j, (W j).support ⊆ A) → (∀ j, (D j).support ⊆ A') → W 0 - push (m + 1) (φ 0) (W 0) - (homot m (φ 0) (fun x => x) (D 0) - homot m (φ 0) (fun x => x) (Z 0)) = (homot (m + 1) (φ 0) (fun x => x) (W 0)).boundary ∧ (∀ j, W (j + 1) - push (m + 1) (φ (j + 1)) (W (j + 1)) - (homot m (φ (j + 1)) (fun x => x) (D (j + 1)) - (homot m (φ (j + 1)) (fun x => x) (Z (j + 1)) - homot m (φ j) (fun x => x) (Z j))) = (homot (m + 1) (φ (j + 1)) (fun x => x) (W (j + 1))).boundary) ∧ (push (m + 1) (φ 0) (W 0)).boundary = push m (φ 0) (D 0) - push m (φ 0) (Z 0) ∧ (∀ j, (push (m + 1) (φ (j + 1)) (W (j + 1))).boundary = push m (φ (j + 1)) (D (j + 1)) - (push m (φ (j + 1)) (Z (j + 1)) - push m (φ j) (Z j))) ∧ (∀ j, IsIntegerMultiplicity (push (m + 1) (φ j) (W j)) ∧ IsIntegerMultiplicity (homot (m + 1) (φ j) (fun x => x) (W j))) ∧ (∀ j, (push (m + 1) (φ j) (W j)).mass ≤ (2 * (Λ j : ℝ≥0∞)) ^ (m + 1) * (W j).mass ∧ (homot (m + 1) (φ j) (fun x => x) (W j)).mass ≤ ENNReal.ofReal δ * ((2 * (Λ j : ℝ≥0∞)) ^ (m + 1) * (W j).mass) ∧ (push m (φ j) (D j)).mass ≤ (2 * (Λ j : ℝ≥0∞)) ^ m * (D j).mass ∧ (homot m (φ j) (fun x => x) (D j)).mass ≤ ENNReal.ofReal δ * ((2 * (Λ j : ℝ≥0∞)) ^ m * (D j).mass) ∧ (push m (φ j) (Z j)).mass ≤ (2 * (Λ j : ℝ≥0∞)) ^ m * (Z j).mass ∧ (homot m (φ j) (fun x => x) (Z j)).mass ≤ ENNReal.ofReal δ * ((2 * (Λ j : ℝ≥0∞)) ^ m * (Z j).mass)) ∧ (∀ j, (push (m + 1) (φ j) (W j)).support ⊆ L ∩ cthickening δ A ∧ (homot (m + 1) (φ j) (fun x => x) (W j)).support ⊆ cthickening δ A ∧ (push m (φ j) (D j)).support ⊆ cthickening δ A' ∧ (homot m (φ j) (fun x => x) (D j)).support ⊆ cthickening δ A')
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

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.skeleton_deformation-a1.telescoping_deformation-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.skeleton_deformation-a1.telescoping_deformation-a1.shell_deformation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 0–5 of the parent's supplied proof (Simon Ch. 6, proof of 5.1: the deformed pieces and their mass bounds (11)–(16), the homotopy formula (20) applied to each shell, and the support statements (22)–(23); chapter-06.txt lines 1740–1830), with the homotopy taken from φ_j to the identity (F := φ_j, G := id in (PF)), so that the homotopy currents enter with the signs of (c1)–(c2). Sibling used: MS = cmc_fc_cs_massOn_sub_le (key mass_sub): M_G(A − B) ≤ M_G(A) + M_G(B) for all currents A, B on a common domain and every set G.
Notation. All currents are on univ = ℝ^P and M(X) = M_{ℝ^P}(X). PF1, …, PF5 are the first five conjuncts of (PF) (PF6 is not used). NC_k is the class of X ∈ 𝒟_k(ℝ^P) with compact support, finite mass and boundaryMassOn X ℝ^P < ∞; PF1–PF4 require their arguments to be NC_k, and PF2–PF5 require all maps involved to be Λ-Lipschitz for one common Λ.
1. (Lipschitz constants.) id is 1-Lipschitz (LipschitzWith.id), hence Λ_j-Lipschitz for every j because 1 ≤ Λ_j (LipschitzWith.weaken). φ_j is Λ_j-Lipschitz and Λ_j ≤ Λ_{j+1}, hence also Λ_{j+1}-Lipschitz.
2. (Normality of the pieces.) W_j ∈ NC_{m+1}: spt W_j is compact, M(W_j) < ∞, and in degree m + 1 boundaryMassOn W_j ℝ^P is M_{ℝ^P}(∂W_j) = M(∂W_j) < ∞ by definition. D_j, Z_j ∈ NC_m by hypothesis.
3. (Normality of Z_{j+1} − Z_j.) (a) By (S-iii), spt(Z_{j+1} − Z_j) ⊆ spt Z_{j+1} ∪ spt Z_j, which is compact; by (S-ii), spt(Z_{j+1} − Z_j) is closed; a closed subset of a compact set is compact (IsCompact.of_isClosed_subset). (b) M(Z_{j+1} − Z_j) ≤ M(Z_{j+1}) + M(Z_j) < ∞ by MS (with U = G = ℝ^P). (c) For every n ∈ ℕ and X, Y ∈ 𝒟_n(ℝ^P) with boundaryMassOn X ℝ^P < ∞ and boundaryMassOn Y ℝ^P < ∞, also boundaryMassOn (X − Y) ℝ^P < ∞: if n = 0 the value is 0 < ∞ by definition; if n = k + 1, then ∂(X − Y) = ∂X − ∂Y, because both currents take the value X(dη) − Y(dη) at every η ∈ 𝒟^k(ℝ^P) (definitions of − and ∂; GeometricCurrentOn.ext), so M(∂(X − Y)) ≤ M(∂X) + M(∂Y) < ∞ by MS. Applying (c) with n = m, X = Z_{j+1}, Y = Z_j shows Z_{j+1} − Z_j ∈ NC_m.
4. (Locality.) PF3 with k := m, Λ := Λ_{j+1}, F := φ_{j+1}, G := id, F' := φ_j, G' := id (all four Λ_{j+1}-Lipschitz by step 1), X := Z_j ∈ NC_m, the hypothesis φ_{j+1} = φ_j on spt Z_j and id = id on spt Z_j gives push_m(φ_{j+1}, Z_j) = push_m(φ_j, Z_j) = L′_j and homot_m(φ_{j+1}, id, Z_j) = homot_m(φ_j, id, Z_j) = K_j.
5. (Deforming the boundaries.) (a) PF2 with k := m, Λ := Λ_0, F := φ_0, G := id, X := D_0, Y := Z_0 (both NC_m) gives push_m(φ_0, D_0 − Z_0) = Y_0 − L′_0 and homot_m(φ_0, id, D_0 − Z_0) = E′_0 − K_0. (b) Fix j. PF2 with Λ := Λ_{j+1}, F := φ_{j+1}, G := id, X := D_{j+1}, Y := Z_{j+1} − Z_j (NC_m by step 3) gives push_m(φ_{j+1}, D_{j+1} − (Z_{j+1} − Z_j)) = Y_{j+1} − push_m(φ_{j+1}, Z_{j+1} − Z_j) and homot_m(φ_{j+1}, id, D_{j+1} − (Z_{j+1} − Z_j)) = E′_{j+1} − homot_m(φ_{j+1}, id, Z_{j+1} − Z_j). PF2 again with X := Z_{j+1}, Y := Z_j gives push_m(φ_{j+1}, Z_{j+1} − Z_j) = L′_{j+1} − push_m(φ_{j+1}, Z_j) and homot_m(φ_{j+1}, id, Z_{j+1} − Z_j) = K_{j+1} − homot_m(φ_{j+1}, id, Z_j), and by step 4 the last terms are L′_j and K_j. Hence push_m(φ_{j+1}, D_{j+1} − (Z_{j+1} − Z_j)) = Y_{j+1} − (L′_{j+1} − L′_j) and homot_m(φ_{j+1}, id, D_{j+1} − (Z_{j+1} − Z_j)) = E′_{j+1} − (K_{j+1} − K_j).
6. (Homotopy formula; (c1)–(c5).) PF5 with k := m, Λ := Λ_j, F := φ_j, G := id and X := W_j (compact support, M(W_j) < ∞, M(∂W_j) < ∞) gives: (i) ∂V_j = push_m(φ_j, ∂W_j); (ii) push_{m+1}(id, W_j) − V_j − homot_m(φ_j, id, ∂W_j) = ∂H_j; (iii) since W_j is integer multiplicity, V_j and H_j are integer multiplicity, which is (c5). By PF1 (W_j ∈ NC_{m+1}, step 2), push_{m+1}(id, W_j) = W_j, so (ii) reads W_j − V_j − homot_m(φ_j, id, ∂W_j) = ∂H_j. For j = 0, substitute ∂W_0 = D_0 − Z_0 and step 5(a): (ii) becomes (c1) and (i) becomes (c3). For j + 1, substitute ∂W_{j+1} = D_{j+1} − (Z_{j+1} − Z_j) and step 5(b): (ii) becomes (c2) and (i) becomes (c4).
7. (Mass bounds; (c6).) PF4 with Λ := Λ_j, F := φ_j, G := id, applied to X := W_j (k = m + 1), X := D_j and X := Z_j (k = m), all NC by step 2, gives M(push_k(φ_j, X)) ≤ Λ_j^k·M(X); and, since dist(φ_j(x), id(x)) = dist(φ_j(x), x) ≤ δ for every x ∈ spt X ⊆ spt W_j ∪ spt D_j ∪ spt Z_j, it gives M(homot_k(φ_j, id, X)) ≤ δ·(2Λ_j)^k·M(X). In [0, ∞], Λ_j ≤ 2Λ_j (as 1 ≤ 2), hence Λ_j^k ≤ (2Λ_j)^k (monotonicity of powers) and Λ_j^k·M(X) ≤ (2Λ_j)^k·M(X); and δ·(2Λ_j)^k·M(X) = δ·((2Λ_j)^k·M(X)) by associativity. These are the six inequalities of (c6).
8. (Supports; (c7).) Let x ∈ spt W_j. Then x ∈ A and dist(φ_j(x), x) ≤ δ, so φ_j(x) ∈ cthickening(δ, A) (Metric.mem_cthickening_of_dist_le), and φ_j(x) ∈ L by hypothesis. By PF4, spt V_j ⊆ φ_j(spt W_j) ⊆ L ∩ cthickening(δ, A). By PF4 also spt H_j ⊆ {φ_j(x) + t(x − φ_j(x)) : x ∈ spt W_j, t ∈ [0, 1]}. For such y = φ_j(x) + t(x − φ_j(x)) we have y − x = (1 − t)(φ_j(x) − x), so dist(y, x) = (1 − t)·dist(φ_j(x), x) ≤ dist(φ_j(x), x) ≤ δ (as 0 ≤ 1 − t ≤ 1); since x ∈ A, y ∈ cthickening(δ, A). Hence spt H_j ⊆ cthickening(δ, A). The same two arguments with D_j in place of W_j, spt D_j ⊆ A' and dist(φ_j(x), x) ≤ δ on spt D_j give spt Y_j ⊆ φ_j(spt D_j) ⊆ cthickening(δ, A') and spt E′_j ⊆ cthickening(δ, A'). ∎
Lean note (compiled route, about 150 lines): `obtain ⟨PF1, PF2, PF3, PF4, PF5, -⟩ := hPF`; `LipschitzWith.id.weaken (h1 j)` and `(hLip j).weaken (hmono j)` for step 1. For step 3(c), prove the general claim `∀ (n : ℕ) (X Y : GeometricCurrentOn (univ : Set (Euclid P)) n), boundaryMassOn X univ < ∞ → boundaryMassOn Y univ < ∞ → boundaryMassOn (X - Y) univ < ∞` by `intro n X Y hX hY; cases n` (zero: `exact ENNReal.zero_lt_top`; succ: `(X - Y).boundary = X.boundary - Y.boundary` by `ext ω; rfl`, then `show (X - Y).boundary.massOn univ < ∞` and MS); a hypothesis `(W j).boundary.mass < ∞` is accepted where `boundaryMassOn (W j) univ < ∞` is expected (definitional). For (c1)–(c4): `have e := (PF5 m (Λ 0) (φ 0) (fun x => x) (W 0) …).2.1; rw [PF1-instance, hW0, (PF2-instance).2] at e; exact e`, and `rw [(PF5 …).1, hW0, (PF2-instance).1]`. For (c6), `gcongr` reduces `(Λ j : ℝ≥0∞) ^ k * M ≤ (2 * (Λ j : ℝ≥0∞)) ^ k * M` to `le_mul_of_one_le_left zero_le one_le_two`, and `rw [← mul_assoc]` matches the δ-bounds. For (c7), prove `φ j x + t • (x - φ j x) - x = (1 - t) • (φ j x - x)` by `rw [sub_smul, one_smul, smul_sub, smul_sub]; abel`, then use `dist_eq_norm`, `norm_smul`, `Real.norm_eq_abs`, `abs_of_nonneg`.

## Key steps

1. id and φ_j are Λ_j- resp. Λ_{j+1}-Lipschitz; W_j, D_j, Z_j and (via (S-ii), (S-iii), MS and ∂(X − Y) = ∂X − ∂Y) Z_{j+1} − Z_j are normal with compact support.
2. Locality (PF3, φ_{j+1} = φ_j on spt Z_j) gives push_m(φ_{j+1}, Z_j) = L′_j and homot_m(φ_{j+1}, id, Z_j) = K_j.
3. Linearity (PF2) deforms ∂W_0 = D_0 − Z_0 and ∂W_{j+1} = D_{j+1} − (Z_{j+1} − Z_j) into Y − L′ and E′ − K telescoping differences.
4. The homotopy formula PF5 with F := φ_j, G := id and PF1 give (c1)–(c4); PF5 integrality gives (c5).
5. PF4 with Λ_j^k ≤ (2Λ_j)^k gives the mass bounds (c6); PF4 support bounds and dist(φ_j(x) + t(x − φ_j(x)), x) ≤ δ give (c7).

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); git -C local-references/123e8435b4a2469b/mathlib rev-parse HEAD (25730c7c759d108ef87ab70af2342a196760f79d, matches manifest)`
- `rg -c -i 'telescop' local-references/123e8435b4a2469b/project/GMT -g '*.lean' (no match)`
- `rg -n 'cmcsdtd_' local-references/123e8435b4a2469b (no match); python3 -I scan of runs/20261011T150044Z-ba604216b4/dag.json lean_name values for the prefix cmcsdtd_ (no match)`
- `rg -n "theorem tendsto_nhds_unique |theorem tendsto_add_atTop_nat|theorem summable_toReal|theorem tsum_toReal_eq|theorem ne_top_of_tsum_ne_top|theorem mem_cthickening_of_dist_le|theorem isClosed_cthickening|theorem tendsto_toReal |theorem Tendsto.const_mul |theorem IsCompact.of_isClosed_subset|theorem Summable.of_norm_bounded |theorem closure_minimal" local-references/123e8435b4a2469b/mathlib/Mathlib -g '*.lean'`
- `grep -n 'def \|theorem \|instance' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/{Currents,Mass,CurrentLocalEquality}.lean (GeometricCurrentOn.ext, boundary_apply, exteriorDerivativeTestOn, massOn, le_massOn, support; no Sub instance) and grep -n instance GMT/Ch07/Contract.lean (only the contract Sub instance)`
- `python3 -I scan of dag.json: frozen types and status of cmr_abs_apply_le_massOn, cmc_fc_cs_massOn_sub_le, cmc_fc_sc_testForm_coeff_bound, rsd_mw_tfa_norm_props (accepted) and cmcsd_support_calculus (decomposing); search for accepted test-form coefficient bounds (lean_statement containing covectorEuclideanNorm and ∃ c)`
- `git show f492ba4a003c8f1324077e050d48667ae23c7100 / 827f2b91f9f4bc56c57c61f028ddb49fff28d5b8 / 7a706164baaf42fc7f55751247396a8836928310 / ea5c1199c9160b359cf351e442ec9e8b76e9a258 :GMT/Ch07/Submission.lean (accepted proofs, byte-compared with the recompiled blocks)`
- `sed -n 1405,1930p book/chapter-06.txt (Simon 6.5.1, displays (10)–(25) at lines 1734–1838)`
- `lean Types.lean, InstCheck.lean, InstCheck2.lean (pp.explicit), ProbeTel.lean, ProbeMassEval.lean, ProbeShell.lean, ProbeSeries.lean, AssemblyFromJson.lean, FullFromJson.lean (#print axioms) in GMT/Scratch/cmcsdtd_telescoping_deformation_decomposition`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/InfiniteSum.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Separation/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Closure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-ske-ae4abe6dc4/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-series-896eab3360/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-mass-eq-weight-a1-test-form-approx-a1-norm-props-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcsd_skeleton_deformation_decomposition/draft_subproblems.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcsdtd_telescoping_deformation_decomposition/AssemblyFromJson.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcsdtd_telescoping_deformation_decomposition/FullFromJson.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcsdtd_telescoping_deformation_decomposition/draft_subproblems.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`

The snapshot (project b4d606d, Mathlib 25730c7c) matches the workspace: its Contract.lean is identical to the workspace Contract.lean, which is identical to Submission.lean.

No telescoping or deformed-series material exists in the snapshot project, and the prefix cmcsdtd_ is unused in both the snapshot and the DAG. The pinned Mathlib supplies every lemma the child proofs cite: tendsto_nhds_unique, tendsto_add_atTop_nat, ENNReal.summable_toReal / tsum_toReal_eq / ne_top_of_tsum_ne_top / tendsto_toReal / Tendsto.const_mul, Summable.of_norm_bounded, mem_cthickening_of_dist_le, isClosed_cthickening, IsCompact.of_isClosed_subset and closure_minimal. SimonGMT supplies GeometricCurrentOn.ext, boundary_apply, massOn / le_massOn and support. The contract's Sub instance is the only Sub instance on currents.

The DAG has four accepted declarations with identical types that are reused: rsd_mw_tfa_norm_props, cmc_fc_sc_testForm_coeff_bound, cmr_abs_apply_le_massOn and cmc_fc_cs_massOn_sub_le. Their accepted proofs recompile byte-identically with standard axioms. cmcsd_support_calculus is not accepted, so its conjuncts are passed to the children as hypotheses.

All child types elaborate. The selected frozen type is assembled from the child types, and every child is fully proved in scratch using only propext, Classical.choice and Quot.sound.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
