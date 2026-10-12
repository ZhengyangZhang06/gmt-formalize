# Parent-supplied natural-language proof

- Parent DAG node: `root.besicovitch_federer-a1.cone_trichotomy-a1.sphere_good_directions-a1`
- Child DAG node: `root.besicovitch_federer-a1.cone_trichotomy-a1.sphere_good_directions-a1.axis_free_measurable-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 2 of the parent proof (first half): the axis set C is σ-compact, hence Borel.

Notation: E := Rn N; |·| is the norm; p_H := H.starProjection; S(H) := {θ ∈ H : |θ| = 1}; g(θ, b) := p_H(b − a) − (p_H(b − a)·θ)θ for θ, b ∈ E. The set in the statement is X := {θ : θ ∈ H ∧ |θ| = 1 ∧ ¬∃ b ∈ A, b ≠ a ∧ dist(b, a) < δ ∧ g(θ, b) = 0}.

1. S(H) is compact. H is a finite-dimensional subspace of E, hence closed (Submodule.closed_of_finiteDimensional). The unit sphere {θ : |θ| = 1} is closed and bounded. So S(H) = H ∩ sphere(0, 1) is closed and bounded in the proper space E, hence compact (Metric.isCompact_of_isClosed_isBounded); in particular S(H) is Borel. A is compact by hypothesis, so S(H) × A is compact in E × E.

2. g is continuous on E × E: p_H is a continuous linear map, and subtraction, the inner product and scalar multiplication are continuous.

3. For j ∈ ℕ let K_j := {(θ, b) ∈ S(H) × A : 1/(j + 1) ≤ dist(b, a), dist(b, a) ≤ δ − 1/(j + 1), g(θ, b) = 0}. Each of the three extra conditions defines a closed set, namely the preimage of a closed set under a continuous function of (θ, b). So K_j is a closed subset of the compact set S(H) × A, hence compact. Let P_j := π₁(K_j) be its image under the continuous projection π₁(θ, b) := θ. Then P_j is compact, hence closed, hence Borel, and P_j ⊆ S(H).

4. Claim: for θ ∈ S(H), (∃ b ∈ A, b ≠ a ∧ dist(b, a) < δ ∧ g(θ, b) = 0) ⟺ θ ∈ ⋃_{j ∈ ℕ} P_j.
 (⇒) Let b be such a point and d := dist(b, a). Then d > 0 since b ≠ a, and δ − d > 0. By the Archimedean property choose j ∈ ℕ with 1/(j + 1) ≤ min(d, δ − d). Then 1/(j + 1) ≤ d and d ≤ δ − 1/(j + 1), so (θ, b) ∈ K_j and θ ∈ P_j.
 (⇐) If θ ∈ P_j, choose b with (θ, b) ∈ K_j. Then b ∈ A. Since dist(b, a) ≥ 1/(j + 1) > 0, b ≠ a. Also dist(b, a) ≤ δ − 1/(j + 1) < δ and g(θ, b) = 0.

5. By 4, X = S(H) ∖ ⋃_j P_j = S(H) ∩ (⋃_j P_j)ᶜ. This is the intersection of the closed set S(H) with the complement of a countable union of closed sets, so X is Borel, i.e. MeasurableSet X. No assumption on δ is needed: if δ ≤ 0, every K_j is empty and X = S(H). ∎

## Key steps

1. S(H) = H ∩ sphere(0, 1) is compact, S(H) × A is compact, and g(θ, b) := p_H(b − a) − (p_H(b − a)·θ)θ is continuous.
2. K_j := {(θ, b) ∈ S(H) × A : 1/(j+1) ≤ dist(b, a) ≤ δ − 1/(j+1), g(θ, b) = 0} is compact, so P_j := π₁(K_j) is closed.
3. For θ ∈ S(H): some b ∈ A has b ≠ a, dist(b, a) < δ and g(θ, b) = 0 iff θ ∈ ⋃_j P_j (Archimedean choice of j).
4. The set equals S(H) ∖ ⋃_j P_j and is therefore Borel.

## Reference use

### local-project

Queries:
- `cat manifest.json (project d09bc8a18ce60face651f042976e8465f21f0f68, mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `rg -n "^structure OuterMeasure" -A 12 mathlib/Mathlib/MeasureTheory/OuterMeasure/Defs.lean`
- `rg -n "theorem ae_tendsto_measure_inter_div\b" -A 8 mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `rg -n "theorem exists_disjoint_subfamily_covering_enlargement\b" -A 8 mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `rg -n "theorem exists_disjoint_subfamily_covering_enlargement_ball|theorem exists_disjoint_subfamily_covering_enlargement_closedBall" -A 8 mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `rg -n "exists_isClosed_sdiff_lt|exists_isClosed_diff_lt" mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `rg -n "HasBesicovitchCovering" mathlib/Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean`
- `rg -n "countable_of_isOpen" mathlib/Mathlib/Topology/Bases.lean`
- `rg -n "infDist_pos|theorem infDist_lt_iff|theorem infDist_le_dist_of_mem" mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `rg -n "theorem measure_biUnion_le\b" mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean; rg -n "theorem measure_biUnion\b" mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `rg -n "theorem restrict_apply'" mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `rg -n "lemma starProjection_apply_mem|theorem starProjection_eq_self_iff" mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `rg -n -i "densityDichotomy|doubleCone|axisFree|sphereGood|slabGood" project/ (no match)`
- `grep -rl "bf_sphereGood_" .humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes dag.json GMT/Ch03 (no match: proposed names are fresh)`
- `rg -l "ae_tendsto_measure_inter_div|exists_disjoint_subfamily_covering_enlargement" .lake/packages/simongmt; grep -n "^theorem" Chapter01/DensityCovering.lean Chapter01/Densities.lean`
- `lake env lean GMT/Scratch/SphereGoodSplitApi.lean (BorelSpace, SecondCountableTopology, HasBesicovitchCovering, WeaklyRegular, SeparableSpace, ProperSpace at Rn N; cited lemmas applied at Rn N)`
- `lake env lean GMT/Scratch/SphereGoodSplitDecision.lean (child types elaborate; parent frozen type proved from children + sibling without sorry in the assembly)`
- `lake env lean GMT/Scratch/SphereGoodSplitReplay.lean (#print axioms of the three proved children: propext, Classical.choice, Quot.sound)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/OuterMeasure/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityCovering.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/SphereGoodSplitApi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/SphereGoodSplitDecision.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/SphereGoodSplitReplay.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/SGDReviewFull.lean`

Mathlib 25730c7c supplies every library ingredient the children cite:
- OuterMeasure.mk, with fields measureOf, empty, mono and iUnion_nat; iUnion_nat only needs pairwise-disjoint sequences.
- Besicovitch.ae_tendsto_measure_inter_div (∀ᵐ x ∂μ.restrict s, closed-ball density ratio → 1 for locally finite μ).
- Vitali.exists_disjoint_subfamily_covering_enlargement and its _ball variant.
- MeasurableSet.exists_isClosed_sdiff_lt (exists_isClosed_diff_lt is a deprecated alias).
- The HasBesicovitchCovering instance for finite-dimensional normed spaces.
- Set.PairwiseDisjoint.countable_of_isOpen, IsClosed.notMem_iff_infDist_pos, Metric.infDist_lt_iff and Metric.infDist_le_dist_of_mem.
- measure_biUnion_le for outer measures and measure_biUnion for measures.
- Measure.restrict_apply' and Submodule.starProjection_apply_mem.
All needed instances resolve at Rn N: BorelSpace, SecondCountableTopology, HasBesicovitchCovering, WeaklyRegular for finite measures, SeparableSpace and ProperSpace. SimonGMT's exists_fiveTimesCovering is a closed-ball variant and is not needed. No existing project declaration states a density dichotomy, a double-cone outer measure or axis-set measurability, and the three proposed names are fresh. The child types elaborate after import GMT.Ch03.Submission in namespace GMT.Ch03 and imply the parent's frozen type. Scratch Lean proofs of all three children compile using only standard axioms.
