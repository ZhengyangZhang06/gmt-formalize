# Parent-supplied natural-language proof

- Parent DAG node: `root.integral_compactness-a1.allard_lemma-a1.bad_set_bound-a1`
- Child DAG node: `root.integral_compactness-a1.allard_lemma-a1.bad_set_bound-a1.besicovitch_cover-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1, 5 and 7 and the summation part of step 6 of the parent proof. This is the Besicovitch deduction in Simon 8.5.10 (p. 221: "Since then {B_{ρ_y}(y)}_{y∈A_1∪A_2} covers A_1 ∪ A_2 we deduce from (4), (5) and the Besicovitch Covering (§3.12 of Ch. 1) that μ(A_1 ∪ A_2) ≤ cε^{-1}(∫_{B_3(0)}‖p_S − p‖dW + ‖δW‖(B_3(0)))"). It is stated for general measures μ, ν, a general set A, a set O containing all selected balls, a radius bound R and a ratio t. The parent applies it with (μ, ν, A, O, R, t) = (μ_W, ofReal(1/ε)·‖δW‖ + ofReal(eΛ/ε)·τ, E, B°_3(0), 1, 1). Notation: B_r(x) := closedBall x r, B°_r(x) := ball x r. All quantities lie in [0,∞]. μ(A) and ν(O) are outer measures, so A and O need not be measurable.

1. The constant. Euclidean N = EuclideanSpace ℝ (Fin N) is a finite-dimensional real normed space. So it has the Besicovitch covering property (Mathlib instance HasBesicovitchCovering for finite-dimensional real normed spaces, MeasureTheory/Covering/BesicovitchVectorSpace.lean). HasBesicovitchCovering.no_satelliteConfig (α := Euclidean N) gives C ∈ ℕ and τ > 1 such that there is no satellite configuration of C + 1 balls with parameter τ. Fix this C. It depends only on N.

2. The ball family. Let μ, ν, A, O, R, t satisfy the hypothesis. For every x ∈ A choose a radius σ(x) with:
 – 0 < σ(x) ≤ R;
 – B_x := B_{σ(x)}(x) ⊆ O;
 – μ(B_x) ≤ t·ν(B_x).
 The centres x ∈ A, indexed by the subtype A, with radii σ(x) ∈ (0, R] form a Besicovitch ball package (Besicovitch.BallPackage with c the coercion A → ℝ^N, r := σ, rpos from σ(x) > 0, r_bound := R and r_le from σ(x) ≤ R).

3. Besicovitch covering. Apply Besicovitch.exist_disjoint_covering_families to τ, the emptiness of satellite configurations from step 1, and this package. It gives subsets s_1, …, s_C of A (indexed by Fin C) with two properties:
 – for each k, the closed balls B_x (x ∈ s_k) are pairwise disjoint;
 – every centre lies in ⋃_k ⋃_{x∈s_k} B°_{σ(x)}(x).
 Since B°_{σ(x)}(x) ⊆ B_x (ball_subset_closedBall), A ⊆ ⋃_k ⋃_{x∈s_k} B_x.

4. Countability. Each s_k is countable by Set.PairwiseDisjoint.countable_of_nonempty_interior, for three reasons:
 – its balls B_x are pairwise disjoint;
 – each B_x has nonempty interior: x ∈ B°_{σ(x)}(x) ⊆ interior B_x, because σ(x) > 0 (mem_ball_self, ball_subset_interior_closedBall);
 – ℝ^N is separable.

5. Summation. Each step below holds in [0,∞]:
 μ(A) ≤ μ(⋃_k ⋃_{x∈s_k} B_x)  (measure_mono, step 3)
 ≤ Σ_k μ(⋃_{x∈s_k} B_x)  (finite subadditivity, measure_iUnion_fintype_le)
 ≤ Σ_k Σ'_{x∈s_k} μ(B_x)  (countable subadditivity with step 4, measure_biUnion_le)
 ≤ Σ_k Σ'_{x∈s_k} t·ν(B_x)  (choice of σ(x), ENNReal.tsum_le_tsum)
 = Σ_k t·ν(⋃_{x∈s_k} B_x)  (ENNReal.tsum_mul_left, then measure_biUnion with step 4: ν is countably additive on the pairwise disjoint closed, hence measurable, balls B_x, measurableSet_closedBall)
 ≤ Σ_k t·ν(O)  (each B_x ⊆ O, so ⋃_{x∈s_k} B_x ⊆ O; measure_mono, then monotonicity of multiplication by t)
 = C·t·ν(O)  (Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul).
 The chain also covers t = ∞, ν(O) = ∞, A = ∅ and C = 0. If C = 0, the union in step 3 is empty, so A = ∅ and the chain reads 0 ≤ 0. ∎

## Key steps

1. C := the Besicovitch number of Euclidean N from HasBesicovitchCovering.no_satelliteConfig (no satellite configuration of C+1 balls with parameter τ > 1)
2. Choose for each x ∈ A a radius σ(x) ∈ (0,R] with B_{σ(x)}(x) ⊆ O and μ(B) ≤ t·ν(B); form the Besicovitch ball package indexed by A
3. Besicovitch.exist_disjoint_covering_families: C subfamilies s_k of pairwise disjoint balls whose union covers A
4. Each s_k is countable (disjoint closed balls with nonempty interior in the separable ℝ^N)
5. Sum: μ(A) ≤ Σ_k Σ_{x∈s_k} μ(B_x) ≤ Σ_k t·ν(⋃_{x∈s_k} B_x) ≤ C·t·ν(O) by subadditivity, the ratio bound, countable additivity of ν on disjoint balls and B_x ⊆ O

## Reference use

### local-project

Queries:
- `cat local-references/5a882a57db723346/manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum snapshot project/GMT/Ch08/Contract.lean, workspace GMT/Ch08/Contract.lean, GMT/Ch08/Submission.lean (all 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487)`
- `rg -n 'theorem exist_disjoint_covering_families|no_satelliteConfig' mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean (lines 156, 455)`
- `rg -n 'instance.*HasBesicovitchCovering' mathlib/Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean (line 499)`
- `rg -n 'theorem withDensity_apply' mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean (line 44: only MeasurableSet s required)`
- `rg -n 'theorem map_apply' mathlib/Mathlib/MeasureTheory/Measure/Map.lean (line 170); rg -n 'theorem prod_univ' mathlib/Mathlib/Data/Set/Prod.lean (line 97)`
- `rg -n 'countable_of_nonempty_interior' mathlib/Mathlib/Topology (Bases.lean:493); rg -n 'theorem measure_biUnion_le|theorem measure_iUnion_fintype_le' mathlib/Mathlib/MeasureTheory (OuterMeasure/Basic.lean:74,84); rg -n 'theorem measure_biUnion' mathlib/Mathlib/MeasureTheory (Measure/Basic.lean:132)`
- `rg -n 'theorem tsum_mul_left|theorem tsum_le_tsum' mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean (116, 180); rg -n 'theorem add_apply|theorem smul_apply' mathlib/Mathlib/MeasureTheory/Measure/Module.lean (91, 120); rg -n 'ball_subset_interior_closedBall|mem_ball_self|ball_subset_closedBall' mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean (1216, 379, 477)`
- `grep -n 'abbrev Grassmannian|structure Varifold|def weight' simongmt Chapter08/Varifold.lean (60, 335, 557: weight = measure.map Prod.fst)`
- `python3 scan of dag.json: Besicovitch nodes (besicovitch_ratio_cover_estimate accepted in root.density_semicontinuity-a1; intcpt_vdb_besicovitch_cover_estimate decomposing, identical thickening type) and duplicate lean_names (none; no cross-branch reuse in the run)`
- `git show b70dd9d5 (accepted proof of besicovitch_ratio_cover_estimate); git show da0a42e7:GMT/Ch08/Submission.lean and 3beae5a3:GMT/Ch08/Submission.lean (leaf bases = contract + tracked dependency declarations only)`
- `grep -n Besicovitch book/chapter-08.txt; sed -n 776,850p (Simon 8.5.10 printed (1)-(5) and the Besicovitch deduction, p. 221)`
- `lake env lean /tmp/bsb-decomp-v1/Check0.lean (#check of the cited lemmas after import GMT.Ch08.Submission)`
- `lake env lean /tmp/bsb-decomp-v1/Assembly.lean (both children proved; frozen parent proved from them + stubbed accepted sibling; comparator wrappers; #print axioms)`
- `python3 gmt-compare.child_modules -> /tmp/bsb-decomp-v1/gen/Both.lean; lake env lean (exact challenge modules elaborate)`
- `python3 -I validate_lean_statement (verifier/lean_contract.py) on both lean_statements`
- `grep intcpt_allard_bsb_ in dag.json and the run directory; git grep -l intcpt_allard_bsb_ over all 523 refs (0 hits)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Data/Set/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Module.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-allard-lemma-a1-bad-set-bound-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-allard-lemma-a1-good-point-monotonicity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-density-semicontinuity-a1-besicovitch-ratio-cover-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-variation-density-bound-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-08.txt`
- `/tmp/bsb-decomp-v1/Check0.lean`
- `/tmp/bsb-decomp-v1/Assembly.lean`
- `/tmp/bsb-decomp-v1/gen/Both.lean`

The snapshot is project 63436ae6 + Mathlib 25730c7c; its Contract is byte-identical to the workspace Contract and Submission. Every lemma cited in the two child proofs exists in the snapshot with suitable hypotheses: withDensity_apply needs only a measurable set; exist_disjoint_covering_families needs 1 < τ, no satellite configurations and a bounded-radius BallPackage; Euclidean N has a HasBesicovitchCovering instance. Each lemma was #checked from import GMT.Ch08.Submission. The accepted thickening-form lemma besicovitch_ratio_cover_estimate is in another branch and not in this node's base. Leaf bases contain only the contract plus tracked dependencies, and the run never reuses a declaration across branches (variation_density_bound re-proves it as intcpt_vdb_besicovitch_cover_estimate). So the more general containing-set form is proposed under a fresh name; its proof is the accepted one with the thickening containment replaced by the hypothesis B ⊆ O. In the comparator's replayed scope both child statements elaborate, pass validate_lean_statement, and are fully proved with axioms propext, Classical.choice and Quot.sound only. The frozen parent type (byte-identical) is proved from them plus the accepted sibling good_point_monotonicity, with no sorry of its own. An independent reviewer re-ran all checks and accepted. Neither lean_name occurs in dag.json, the run directory or any git ref.
