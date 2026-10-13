# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.retraction-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.retraction-a1.cube_lipschitz-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 6 of the parent proof, Claim B (|Φ(x) − Φ(z)| ≤ 4√P|x − z|/κ(x)), with the Lipschitz bounds of step 2; the second point is not required to satisfy κ > 0 (the degenerate case is step 4(b) below).
1. From |a_i − 1/2| < 1/4 we get 1/4 < a_i < 3/4, so 1/a_i < 4, 1/(1 − a_i) < 4, a_i < 3/4 and 1 − a_i < 3/4. Let d := dist(y, y'); for every j, |y_j − y'_j| ≤ d (a coordinate is bounded by the Euclidean norm).
2. For every j, |r_j(y) − r_j(y')| ≤ 4|y_j − y'_j| ≤ 4d: the two entries of the max change by |y_j − y'_j|/(1 − a_j) ≤ 4|y_j − y'_j| and |y_j − y'_j|/a_j ≤ 4|y_j − y'_j| respectively, and |max(p, q) − max(p', q')| ≤ max(|p − p'|, |q − q'|). By the hypothesis on κ with t := 4d, |κ(r(y)) − κ(r(y'))| ≤ 4d.
3. Fix i and put u := y_i − a_i, u' := y'_i − a_i, μ := max(r_i(y), κ(r(y))), μ' := max(r_i(y'), κ(r(y'))). Then μ ≥ κ(r(y)) > 0, |u − u'| = |y_i − y'_i| ≤ d, and |μ − μ'| ≤ max(|r_i(y) − r_i(y')|, |κ(r(y)) − κ(r(y'))|) ≤ 4d by step 2. Also r_i(y') ≥ 0 (one of its two entries is ≥ 0), so μ' ≥ 0. Note Φ(y)_i − Φ(y')_i = u/μ − u'/μ'.
4. Claim: |u/μ − u'/μ'| ≤ 4d/μ.
   (a) If μ' > 0: |u'|/μ' ≤ 3/4. Indeed, if u' ≥ 0 then μ' ≥ r_i(y') ≥ u'/(1 − a_i), so u'/μ' ≤ 1 − a_i < 3/4; if u' < 0 then μ' ≥ r_i(y') ≥ (a_i − y'_i)/a_i = −u'/a_i, so |u'|/μ' ≤ a_i < 3/4. Writing u/μ − u'/μ' = (u − u')/μ + (u'/μ')·(μ' − μ)/μ, we get |u/μ − u'/μ'| ≤ d/μ + (3/4)(4d)/μ = 4d/μ.
   (b) If μ' = 0: then r_i(y') = 0, which forces u' = 0 (if u' > 0 then r_i(y') ≥ u'/(1 − a_i) > 0; if u' < 0 then r_i(y') ≥ −u'/a_i > 0). So Φ(y')_i = a_i (the quotient u'/μ' has numerator 0, so it is 0, also under the convention x/0 = 0), and |u/μ − u'/μ'| = |u − u'|/μ ≤ d/μ ≤ 4d/μ.
5. Since μ ≥ κ(r(y)) > 0, step 4 gives |Φ(y)_i − Φ(y')_i| ≤ 4d/κ(r(y)) for every i. Summing squares over the P coordinates, dist(Φ(y), Φ(y')) = (Σ_i (Φ(y)_i − Φ(y')_i)²)^{1/2} ≤ (P·(4d/κ(r(y)))²)^{1/2} = (4√P/κ(r(y)))·d. ∎

## Key steps

1. Coordinates are 1-Lipschitz for the Euclidean distance; r_j is 4-Lipschitz in y_j because 1/a_j, 1/(1 − a_j) < 4.
2. The sup-norm 1-Lipschitz hypothesis on κ gives |κ(r(y)) − κ(r(y'))| ≤ 4·dist(y, y'), so μ = max(r_i, κ∘r) changes by at most 4·dist(y, y').
3. |y'_i − a_i|/μ' ≤ max(a_i, 1 − a_i) < 3/4 (or y'_i = a_i when μ' = 0), whence |Φ(y)_i − Φ(y')_i| ≤ 4·dist(y, y')/κ(r(y)).
4. Summing squares over the P coordinates gives the factor √P.

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
