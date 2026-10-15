# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.retraction-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.retraction-a1.cube_periodic-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4(iii) of the parent proof (Φ(x + z) = Φ(x) + z for z ∈ ℤ^P with x, x + z ∈ C: in the coordinates with z_i ≠ 0 both points have r_i = 1, so κ is unchanged and max(r_i, κ) = 1 there).
1. From |a_j − 1/2| < 1/4 we get 0 < a_j < 1 for every j.
2. For t ∈ ℝ let ρ_j(t) := max((t − a_j)/(1 − a_j), (a_j − t)/a_j), so r_j(y) = ρ_j(y_j). Then ρ_j(0) = max(−a_j/(1 − a_j), 1) = 1 and ρ_j(1) = max(1, (a_j − 1)/a_j) = 1, the other entry being negative in each case. For t ∈ [0, 1], ρ_j(t) ≤ 1, because t − a_j ≤ 1 − a_j and a_j − t ≤ a_j.
3. For each j, k_j := y'_j − y_j is an integer with |k_j| ≤ 1 since y_j, y'_j ∈ [0, 1]; so k_j ∈ {−1, 0, 1}. If k_j = 0 then y'_j = y_j. If k_j = 1 then y_j = 0 and y'_j = 1; if k_j = −1 then y_j = 1 and y'_j = 0. In every case r_j(y') = r_j(y) (by step 2 in the last two cases). Hence r(y') = r(y) as functions of j, and k₀ := κ(r(y)) = κ(r(y')).
4. k₀ ≤ 1: the hypothesis on κ applied to u = r(y) gives s with |s| ≥ P − (m + 1) ≥ 1, so there is i₀ ∈ s, and k₀ ≤ r_{i₀}(y) = ρ_{i₀}(y_{i₀}) ≤ 1 by step 2.
5. Fix i. If y'_i = y_i, then by step 3 both Φ(y')_i and Φ(y)_i equal a_i + (y_i − a_i)/max(r_i(y), k₀), and y'_i − y_i = 0, so the identity holds. Otherwise {y_i, y'_i} = {0, 1}, r_i(y) = r_i(y') = 1 and max(1, k₀) = 1 by step 4, so Φ(y)_i = a_i + (y_i − a_i)/1 = y_i and likewise Φ(y')_i = y'_i; hence Φ(y')_i = y'_i = Φ(y)_i + (y'_i − y_i). ∎

## Key steps

1. r_j(0) = r_j(1) = 1, and r_j(y) ≤ 1 when y_j ∈ [0, 1].
2. y'_j − y_j ∈ {−1, 0, 1}, and in the nonzero cases {y_j, y'_j} = {0, 1}; hence r(y') = r(y) and κ(r(y')) = κ(r(y)).
3. κ(r(y)) ≤ 1, since at least P − m − 1 ≥ 1 indices have κ(r(y)) ≤ r_i(y) ≤ 1.
4. Coordinates with y'_i = y_i agree; coordinates with {y_i, y'_i} = {0, 1} have max(r_i, κ) = 1, where Φ is the identity.

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
