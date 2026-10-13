# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1.covering-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1.covering-a1.disjoint_sum-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 5 of the parent proof, which uses countable additivity of μ and of the integral over the disjoint admissible balls. Here it is stated for an arbitrary countable disjoint family of measurable sets B(x), x ∈ t. Write V := ⋃_{x∈t} B(x). All measures are read as real numbers via ENNReal.toReal.

1. (Reindexing by the subtype.) Since t is countable, the subtype ↥t = {i // i ∈ t} is a countable type (Set.Countable.to_subtype). By Set.biUnion_eq_iUnion, V = ⋃_{i : ↥t} B(i). Each B(i), i : ↥t, is measurable because i ∈ t. The family i ↦ B(i) on ↥t is pairwise disjoint: if i ≠ j in ↥t, their underlying points are distinct (the coercion ↥t → ℝ^P is injective) and both lie in t, so B(i) and B(j) are disjoint by t.PairwiseDisjoint B.

2. (Countable additivity of the integral.) g is μ-integrable on V = ⋃_{i : ↥t} B(i), the index type is countable, and the sets B(i) are measurable and pairwise disjoint. By MeasureTheory.hasSum_integral_iUnion, the real family i ↦ ∫_{B(i)} g dμ has sum ∫_V g dμ (HasSum).

3. (Countable additivity of the measure.) By measure_iUnion, μ(V) = Σ'_{i : ↥t} μ(B(i)) in [0, ∞].
- For every i, μ(B(i)) ≤ μ(V) < ∞ by monotonicity, so every term is finite. By ENNReal.tsum_toReal_eq, μ(V).toReal = Σ'_i μ(B(i)).toReal.
- Since Σ'_i μ(B(i)) = μ(V) ≠ ∞, the real family i ↦ μ(B(i)).toReal is summable (ENNReal.summable_toReal). So it has sum μ(V).toReal (HasSum).
- Multiplying by the constant θ (HasSum.mul_left), the family i ↦ θ·μ(B(i)).toReal has sum θ·μ(V).toReal.

4. (Termwise comparison.) For every i : ↥t, the hypothesis at the point i ∈ t gives ∫_{B(i)} g dμ ≤ θ·μ(B(i)).toReal. Two real families with sums that are ordered term by term have ordered sums (hasSum_le). Applied to the sums from Steps 2 and 3, this gives ∫_V g dμ ≤ θ·μ(V).toReal. No sign condition on θ is needed, because both series converge and are compared term by term. If t = ∅, both sides are 0. ∎

## Key steps

1. Reindex V = ⋃_{x∈t} B x as ⋃_{i : ↥t} B i over the countable subtype. Measurability and pairwise disjointness carry over.
2. hasSum_integral_iUnion gives HasSum (i ↦ ∫ y in B i, g y ∂μ) (∫ y in V, g y ∂μ).
3. measure_iUnion, ENNReal.tsum_toReal_eq and ENNReal.summable_toReal give HasSum (i ↦ (μ (B i)).toReal) (μ V).toReal. Multiply by θ.
4. hasSum_le with the termwise hypothesis gives ∫ y in V, g y ∂μ ≤ θ * (μ V).toReal.

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `grep -n 'exists_disjoint_closedBall_covering_ae|exists_closedBall_covering_tsum_measure_le' mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean; sed -n 1,80p, 640,670p, 800,900p of that file`
- `grep -rn 'instance.*HasBesicovitchCovering' mathlib/Mathlib/ (hit: Covering/BesicovitchVectorSpace.lean:499 instHasBesicovitchCovering); sed -n 490,505p`
- `grep -rn 'theorem hasSum_integral_iUnion|theorem integral_iUnion|theorem hasSum_integral_iUnion_ae|theorem integral_iUnion_ae' mathlib/Mathlib/; sed -n 310,345p Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `grep -rn 'theorem tsum_toReal_eq|theorem summable_toReal' mathlib/Mathlib/ (Topology/Algebra/InfiniteSum/ENNReal.lean:350, 491)`
- `grep -rn 'integrableOn_of_bounded' mathlib/Mathlib/MeasureTheory/ (Integral/IntegrableOn.lean:716 Measure.integrableOn_of_bounded)`
- `#check integral_biUnion in Probe.lean (unknown identifier: no match; use integral/hasSum over the countable subtype instead)`
- `Probe.lean: inferInstance for HasBesicovitchCovering (Euclid P), SFinite μ from IsFiniteMeasureOnCompacts μ, BorelSpace (Euclid P), SecondCountableTopology (Euclid P) (all succeed)`
- `python3 -I scan of dag.json lean_statements for PairwiseDisjoint, 'closedBall x (r x)', Besicovitch, HasSum, tsum, ∑', 'IntegrableOn g', 'μ W < ∞', Countable, and of ids containing null_sets/covering/vitali`
- `name-collision check of cbrldvc_exists_disjoint_closedBall_cover, cbrldvc_setIntegral_biUnion_le_mul_measure, cbrldvc_setIntegral_le_sub_of_subset against all 944 DAG lean_names, grep -rln cbrldvc over GMT/ and lake-packages-25730c7c/simongmt, and git log --all -S cbrldvc_`
- `python3 -I scripts/scope.py: verifier/gmt-compare.py contract_scope(Contract.lean, GMT.Ch07.main_theorem) and verifier/lean_contract.py validate_lean_statement on the 3 child statements`
- `lake env lean /tmp/cbrldvc-decomp-k7q2/{Probe,Children,Assembly,FullCheck}.lean`
- `grep -n -i besicovitch book/chapter-0*.txt; sed -n 770,880p book/chapter-01.txt (Simon Ch. 1 Remark 3.11(3), Lemma 3.12, Theorem 3.13)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-77789fb32b/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-77789fb32b/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-77789fb32b/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/tmp/cbrldvc-decomp-k7q2/Probe.lean`
- `/tmp/cbrldvc-decomp-k7q2/Children.lean`
- `/tmp/cbrldvc-decomp-k7q2/Assembly.lean`
- `/tmp/cbrldvc-decomp-k7q2/FullCheck.lean`

Pinned Mathlib supplies everything the child proofs need:
- Besicovitch.exists_disjoint_closedBall_covering_ae: an s-finite measure, an arbitrary set s, admissible radii accumulating at 0 and a bound R give a countable t ⊆ s and r(x) ∈ f(x) ∩ (0, R(x)) with disjoint closed balls covering μ-almost all of s.
- The instance HasBesicovitchCovering for finite-dimensional real normed spaces.
- With IsFiniteMeasureOnCompacts μ, the instances SFinite, SecondCountableTopology and BorelSpace on Euclid P are inferred.
- hasSum_integral_iUnion, measure_iUnion, ENNReal.tsum_toReal_eq, ENNReal.summable_toReal, hasSum_le, Measure.integrableOn_of_bounded, setIntegral_union, integral_mono_ae, measure_sdiff and ENNReal.toReal_sub_of_le.
integral_biUnion does not exist, so the countable index set is handled through its subtype.

No accepted DAG node and no project or SimonGMT lemma states the covering, summation or complement bound. The only Vitali-type node, dorag_lip_vitali_two_measure_bound, is a different bound using 5r-balls. The three new cbrldvc_ names have no collisions.

All three child types elaborate in the replayed contract scope and pass the verifier's lexical check. Each has a complete proof without sorry. Together they prove the frozen parent type with axioms propext, Classical.choice and Quot.sound only.
