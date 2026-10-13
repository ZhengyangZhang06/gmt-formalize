# Parent-supplied natural-language proof

- Parent DAG node: `root.besicovitch_federer-a1`
- Child DAG node: `root.besicovitch_federer-a1.cone_density_infinite-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. This is Step 6 of the parent proof (M. G. Dall'Alba, The Besicovitch-Federer Projection Theorem, Lemma 5.3; P. Mattila, Geometry of Sets and Measures in Euclidean Spaces, Ch. 18), written out.

Notation. N := n + ℓ, Hⁿ := μHE[n], P := W.starProjection, X(a, r, s) := {x : |P(x − a)| < s|x − a|} ∩ B(a, r), and
 A₂ := {a ∈ A : for every K ∈ ℝ and ε > 0 there are s ∈ (0, ε) and r ∈ (0, δ) with K(rs)ⁿ ≤ Hⁿ(A ∩ X(a, r, s))},
which is exactly the set in the statement (Φ_δ(a, W^⊥) = ∞). We show Hⁿ(P(A₂)) = 0.
Facts used.
 (F1) P is linear, 1-Lipschitz, and P(ℝ^N) = W.
 (F2) W with the induced metric is an n-dimensional inner product space; for subsets of W, Hⁿ computed in ℝ^N equals Hⁿ computed in W (isometric inclusion; Mathlib Isometry.euclideanHausdorffMeasure_image), and on W, μHE[n] is the volume (Lebesgue) measure (Mathlib InnerProductSpace.euclideanHausdorffMeasure_eq_volume), an additive Haar measure. Hence, with ω := Hⁿ(W ∩ B̄(0, 1)) ∈ (0, ∞), Hⁿ(W ∩ B̄(y, ρ)) = ωρⁿ for y ∈ W, ρ > 0; in particular Hⁿ restricted to W is locally finite and doubling: Hⁿ(W ∩ B̄(y, 3ρ)) = 3ⁿ Hⁿ(W ∩ B̄(y, ρ)).
 (F3) A is compact, hence Borel, so A ∩ U is Borel for every open U.

1. Fix K > 0. For every y ∈ P(A₂) choose a_y ∈ A₂ with Pa_y = y. Let I := {(y, r, s) : y ∈ P(A₂), s > 0, 0 < r < δ, K(rs)ⁿ ≤ Hⁿ(A ∩ X(a_y, r, s))} and, for i = (y, r, s) ∈ I, let D_i := W ∩ B̄(y, rs), the closed ball of W with centre y and radius rs > 0.

2. Fineness. Let y ∈ P(A₂) and η > 0. Applying the defining property of a_y ∈ A₂ with this K and ε := η/δ gives s ∈ (0, η/δ) and r ∈ (0, δ) with K(rs)ⁿ ≤ Hⁿ(A ∩ X(a_y, r, s)); thus (y, r, s) ∈ I and the radius rs < δ·η/δ = η. So every point of P(A₂) is the centre of sets D_i of arbitrarily small radius.

3. Vitali covering. Work on the subtype W (an n-dimensional inner product space with its volume measure, which by (F2) is μHE[n] on W; it is locally finite and doubling with constant C = 3ⁿ for closed balls). Apply the Vitali covering theorem there (Simon Ch. 1, 3.11–3.12; Mathlib Vitali.exists_disjoint_covering_ae, with the closed balls of W, which are closed with nonempty interior) to the preimage in W of the (possibly non-measurable) set P(A₂) ⊆ W under the inclusion W → ℝ^N, and to the family of closed balls of W corresponding to (D_i)_{i∈I} (fine by step 2): there is a countable I′ ⊆ I such that the D_i, i ∈ I′, are pairwise disjoint and the part of P(A₂) not covered by ⋃_{i∈I′} D_i has measure 0 in W. Transporting back along the isometric inclusion (Mathlib Isometry.euclideanHausdorffMeasure_image) gives Hⁿ(P(A₂) ∖ ⋃_{i∈I′} D_i) = 0 in ℝ^N; likewise Hⁿ(D_i) computed in ℝ^N equals its measure in W, namely ω·(radius)ⁿ.

4. Disjoint cone pieces. For i = (y, r, s) ∈ I′ let S_i := A ∩ X(a_y, r, s). If x ∈ X(a_y, r, s) then |Px − y| = |P(x − a_y)| < s|x − a_y| < sr, so P(S_i) ⊆ D_i. As the D_i (i ∈ I′) are pairwise disjoint, so are the S_i; each S_i is Borel by (F3). Hence Σ_{i∈I′} Hⁿ(S_i) = Hⁿ(⋃_{i∈I′} S_i) ≤ Hⁿ(A).

5. Estimate. By subadditivity, 3, (F2) and the defining inequality of I:
 Hⁿ(P(A₂)) ≤ Hⁿ(P(A₂) ∖ ⋃_{i∈I′} D_i) + Σ_{i∈I′} Hⁿ(D_i) = Σ_{(y,r,s)∈I′} ω(rs)ⁿ ≤ (ω/K) Σ_{i∈I′} Hⁿ(S_i) ≤ (ω/K) Hⁿ(A).

6. Since Hⁿ(A) < ∞ and K > 0 is arbitrary, letting K → ∞ gives Hⁿ(P(A₂)) = 0, i.e. μHE[n] (W.starProjection '' A₂) = 0. ∎

## Key steps

1. Fix K > 0; every y ∈ P(A₂) is the centre of closed n-balls W ∩ B̄(y, rs) of arbitrarily small radius with K(rs)ⁿ ≤ Hⁿ(A ∩ X(a_y, r, s)).
2. Vitali covering for Lebesgue measure on the n-plane W: countably many disjoint such balls cover Hⁿ-almost all of P(A₂).
3. The corresponding cone pieces A ∩ X(a_i, r_i, s_i) project into these disjoint balls, so they are disjoint Borel sets with total mass ≤ Hⁿ(A).
4. Hⁿ(P(A₂)) ≤ Σ ω(r_i s_i)ⁿ ≤ (ω/K)Hⁿ(A); let K → ∞.

## Reference use

### local-project

Queries:
- `cat manifest.json (project d09bc8a18ce60face651f042976e8465f21f0f68, mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `rg -n "^def ForAlmostAllProjections|^noncomputable def frameProjection|^def BesicovitchFedererProjectionTheorem" project/GMT/Ch03/Contract.lean`
- `rg -n "theorem measurable_rectifiable_purelyUnrectifiable_decomposition|theorem PurelyUnrectifiable.mono|theorem countablyRectifiable_iUnion" simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `rg -n "theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn" simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `rg -n "theorem exists_disjoint_subfamily_covering_enlargement|theorem exists_disjoint_covering_ae" mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `rg -n "theorem _root_.Monotone.measure_iUnion" mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `rg -n "theorem LipschitzOnWith.extend_real|theorem LipschitzOnWith.extend_pi" mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `rg -n "theorem ae_tendsto_measure_inter_div" mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `rg -n "instance instInnerRegularCompactLTTopOfIsCompletelyPseudoMetrizableSpace" mathlib/Mathlib/MeasureTheory/Measure/RegularityCompacts.lean`
- `rg -n "InnerProductSpace.euclideanHausdorffMeasure_eq_volume|Isometry.euclideanHausdorffMeasure_image|euclideanHausdorffMeasure_zero" mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n "theorem hausdorffMeasure_zero_singleton" mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n "theorem starProjection_norm_le" mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `rg -n "theorem finrank_span_eq_card" mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean`
- `rg -n "lemma isMulInvariant_eq_smul_of_compactSpace" mathlib/Mathlib/MeasureTheory/Measure/Haar/Unique.lean`
- `rg -n "IsTopologicalGroup \(unitary R\)" mathlib/Mathlib/Topology/Algebra/Star/Unitary.lean`
- `rg -l -i "besicovitch.?federer|purely.?unrectifiable" mathlib/Mathlib`
- `rg -l -i "CompactSpace \(Matrix.orthogonalGroup|orthogonalGroup.*CompactSpace" mathlib/Mathlib`
- `rg -n -i "orthogonalGroup|haar|grassmann" simongmt/Poincare/SimonGMT (only Ch02 additive-Haar area lemmas and a Ch08 Grassmannian type; no O(N) Haar measure)`
- `lake env lean on comparator-scope test files (import GMT.Ch03.Submission + replayed contract scope) elaborating all 8 child types and three Lean assemblies (parent; compact_case; cone_density_positive)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/RegularityCompacts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Haar/Unique.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Algebra/Star/Unitary.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/SymmetricVitali.lean`

Pinned snapshot (project d09bc8a, Mathlib 25730c7c) plus the pinned simongmt package. Reused by the children: SimonGMT measurable_rectifiable_purelyUnrectifiable_decomposition (measurable Lemma 3.2, used by compact_reduction instead of the sibling node, avoiding a cycle), PurelyUnrectifiable.mono, CountablyRectifiable.mono/countablyRectifiable_iUnion, euclideanHausdorffMeasure_image_le_of_lipschitzOn (Lipschitz image bound for μHE); Mathlib Vitali.exists_disjoint_subfamily_covering_enlargement (5r-lemma) and Vitali.exists_disjoint_covering_ae, Monotone.measure_iUnion (continuity from below for arbitrary sets), LipschitzOnWith.extend_real/extend_pi (McShane), Besicovitch.ae_tendsto_measure_inter_div (density theorem for finite measures), InnerRegularCompactLTTop for all measures on Polish spaces, InnerProductSpace.euclideanHausdorffMeasure_eq_volume, Isometry.euclideanHausdorffMeasure_image, euclideanHausdorffMeasure_zero + hausdorffMeasure_zero_singleton, Submodule.starProjection_norm_le, finrank_span_eq_card, Haar uniqueness on compact groups (isMulInvariant_eq_smul_of_compactSpace), IsTopologicalGroup (unitary R). No match: neither Mathlib nor SimonGMT contains the Besicovitch–Federer theorem, the cone lemmas, a CompactSpace instance or Haar measure for the orthogonal group, or invariant measures on Grassmannians/spheres in Hausdorff normalization; these are supplied by the children's proofs (cone_trichotomy carries the O(N) Haar-averaging argument).
