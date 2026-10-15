# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.retraction-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.retraction-a1.dual_dist-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 6 of the parent proof, Claim C (D(x) ≤ √(n+1)·κ(x) via the explicit point x* ∈ Λ(a) ⊆ L*(a), n + 1 = m + 2), stated for a point x and a representative y of x in another integer translate of the cube (x − y ∈ ℤ^P), which is how steps 5 and 7 of the parent proof use it (y = x − z).
1. From |a_j − 1/2| < 1/4 we get 1/4 < a_j < 3/4, so 0 < a_j ≤ 1 and 0 < 1 − a_j ≤ 1 for every j.
2. For every j, |y_j − a_j| ≤ r_j(y) (the parent's δ_j ≤ r_j). If y_j ≥ a_j: r_j(y) ≥ (y_j − a_j)/(1 − a_j) ≥ y_j − a_j = |y_j − a_j|, because y_j − a_j ≥ 0 and 0 < 1 − a_j ≤ 1. If y_j < a_j: r_j(y) ≥ (a_j − y_j)/a_j ≥ a_j − y_j = |y_j − a_j|, because a_j − y_j > 0 and 0 < a_j ≤ 1.
3. Apply the hypothesis on κ to u := r(y): there is s with |s| ≥ m + 2 and r_i(y) ≤ κ(r(y)) for i ∈ s. Choose J ⊆ s with |J| = m + 2. For i ∈ J, step 2 gives |y_i − a_i| ≤ r_i(y) ≤ κ(r(y)); since J is nonempty, κ(r(y)) ≥ 0.
4. For each i choose k_i ∈ ℤ with x_i − y_i = k_i. Define x* ∈ Euclid P by x*_i := x_i − y_i + a_i (= k_i + a_i) for i ∈ J and x*_i := x_i for i ∉ J. For i ∈ J, x*_i − a_i = k_i ∈ ℤ, and |J| = m + 2, so x* ∈ L*(a) (with witness s := J).
5. Therefore infDist(x, L*(a)) ≤ dist(x, x*) = (Σ_{i∈J} (x_i − x*_i)²)^{1/2} = (Σ_{i∈J} (y_i − a_i)²)^{1/2} ≤ ((m + 2)·κ(r(y))²)^{1/2} = √(m + 2)·κ(r(y)), using x_i − x*_i = y_i − a_i for i ∈ J and = 0 for i ∉ J, the bound of step 3, |J| = m + 2 and κ(r(y)) ≥ 0. ∎

## Key steps

1. 1/4 < a_j < 3/4 gives |y_j − a_j| ≤ r_j(y) for every j.
2. The hypothesis on κ at u = r(y) gives J with |J| = m + 2 and |y_i − a_i| ≤ r_i(y) ≤ κ(r(y)) on J (so κ(r(y)) ≥ 0).
3. x* := x with x*_i := x_i − y_i + a_i on J lies in L*(a) because x_i − y_i ∈ ℤ.
4. infDist(x, L*(a)) ≤ |x − x*| = (Σ_{i∈J}(y_i − a_i)²)^{1/2} ≤ √(m+2)·κ(r(y)).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (mode local-project, project b4d606db, mathlib 25730c7c)`
- `cmp project/GMT/Ch07/Contract.lean against workspace GMT/Ch07/Contract.lean and GMT/Ch07/Submission.lean (identical)`
- `rg -n -i "skeleton|retraction|orderStatistic|order statistic|kth largest|k-th largest" project -g "*.lean" (no match)`
- `rg -n "latticeFace|IsLatticeChain|DeformationTheorem" project -g "*.lean" (only GMT/Ch06/Submission.lean, not imported by GMT.Ch07.Submission)`
- `rg -n -i "order statistic|orderStatistic|kthLargest|k-th largest" mathlib/Mathlib (no match: no Lipschitz order-statistic lemma)`
- `rg -n "theorem infDist_le_dist_of_mem|theorem infDist_le_infDist_add_dist|theorem segment_eq_image'|theorem dist_apply_le|theorem exists_mem_eq_sup'" mathlib/Mathlib`
- `rg -n "exists_subset_card_eq|Icc_subset_of_forall_mem_nhdsWithin|abs_projIcc_sub_projIcc|sum_le_card_nsmul|EuclideanSpace.dist_eq|dist_le_range_sum_dist" in the snapshot Mathlib files listed`
- `python3 -I scans of dag.json: twin types (cmcdt_skeleton_retraction speculative-ready, dimred_mbl_dt_skeleton_retraction decomposing, children unaccepted) and name freshness of prefix dor_lmb_fcdr_`
- `sed -n 1488,1500p book/chapter-06.txt (Simon Lemma 5.4)`
- `lake env lean on chal/Challenge_*.lean, Instances.lean, Assembly.lean, Child_*.lean, EndToEnd.lean with #print axioms; verifier lean_contract.validate_lean_statement and gmt-compare.child_modules regeneration`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Convex/Segment.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Finset/Card.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Finset/Lattice/Fold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/IntermediateValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/UnitInterval.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/BigOperators/Group/Finset.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-94b1aae78b/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcdtsr_skeleton_retraction_decomposition/Types.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/dimred_mbl_dtsr_skeleton_retraction_decomposition/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/dor_lmb_fcdr_retraction_decomposition/Assembly.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/dor_lmb_fcdr_retraction_decomposition/EndToEnd.lean`

Snapshot: project b4d606db, mathlib 25730c7c. The snapshot Ch07 Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. The snapshot project has no skeleton retraction, Lemma 5.4 or order-statistic declaration, and Mathlib has no Lipschitz order-statistic lemma (no match), so all six children are new obligations. Ch06's latticeFace/DeformationTheorem are frozen definitions only and are not imported by GMT.Ch07.Submission. Every Mathlib lemma the child proofs and the assembly rely on exists in the pinned snapshot: Metric.infDist_le_dist_of_mem, Metric.infDist_le_infDist_add_dist, segment_eq_image', EuclideanSpace.dist_eq, PiLp.dist_apply_le, Finset.exists_subset_card_eq, Finset.exists_mem_eq_sup'/inf', Finset.sum_le_card_nsmul, dist_le_range_sum_dist, IsClosed.Icc_subset_of_forall_mem_nhdsWithin and Set.abs_projIcc_sub_projIcc. Twin nodes cmcdt_skeleton_retraction and dimred_mbl_dt_skeleton_retraction carry this byte-identical frozen type, but their children (cmcdtsr_*, dimred_mbl_dtsr_*) follow the face-induction proof and none is accepted, so nothing is reused. The new prefix dor_lmb_fcdr_ is unused in the DAG and in GMT/. Lean checks: all six child types elaborate as exact comparator challenges, and Assembly.lean proves the frozen parent type from the six child axioms. EndToEnd.lean proves all six children and the parent with axioms [propext, Classical.choice, Quot.sound] only.
