# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.retraction-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.retraction-a1.order_stat-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 of the parent proof ("r_(k) = max over k-element index sets I of min_{i∈I} r_i", which gives |r_(k)(x) − r_(k)(z)| ≤ max_i |r_i(x) − r_i(z)|), applied to an arbitrary vector u in place of (r_i(x))_i.
1. Put ℓ := P − (m + 1). Since m + 1 < P we have ℓ ≥ 1 and P = m + 1 + ℓ. Let 𝓕 be the family of all ℓ-element subsets I of Fin P. 𝓕 is finite, and it is nonempty because ℓ ≤ P = |Fin P|. Every I ∈ 𝓕 is nonempty because |I| = ℓ ≥ 1.
2. For u : Fin P → ℝ and I ∈ 𝓕 put g_I(u) := min_{i∈I} u_i (a minimum over a finite nonempty set, attained at some index of I), and define κ(u) := max_{I∈𝓕} g_I(u) (a maximum over the finite nonempty family 𝓕, attained at some member of 𝓕).
3. Property (1). Choose I* ∈ 𝓕 with κ(u) = g_{I*}(u). For every i ∈ I*, κ(u) = min_{j∈I*} u_j ≤ u_i. Take s := I*; then |s| = ℓ, so P = m + 1 + ℓ ≤ m + 1 + |s|.
4. Property (2). Let s := {i : u_i ≤ κ(u)}. Suppose |s| ≤ m + 1. Then the complement {i : κ(u) < u_i} has at least P − (m + 1) = ℓ elements, so it contains a subset I with |I| = ℓ. Then I ∈ 𝓕 and g_I(u) = u_{i₀} for some i₀ ∈ I, so g_I(u) > κ(u). This contradicts κ(u) = max_{J∈𝓕} g_J(u) ≥ g_I(u). Hence |s| ≥ m + 2, and u_i ≤ κ(u) for all i ∈ s by the definition of s.
5. Property (3). Assume |u_i − v_i| ≤ t for all i. Fix I ∈ 𝓕 and choose i₀ ∈ I with g_I(v) = v_{i₀}. Then g_I(u) ≤ u_{i₀} ≤ v_{i₀} + t = g_I(v) + t ≤ κ(v) + t. Taking the maximum over I ∈ 𝓕 gives κ(u) ≤ κ(v) + t. The hypothesis is symmetric in u and v (|v_i − u_i| = |u_i − v_i|), so likewise κ(v) ≤ κ(u) + t. Therefore |κ(u) − κ(v)| ≤ t. ∎

## Key steps

1. ℓ := P − (m + 1) ≥ 1; 𝓕 := ℓ-element index sets (nonempty family of nonempty sets); κ(u) := max_{I∈𝓕} min_{i∈I} u_i.
2. (1): a maximizing I* gives ℓ indices with κ(u) ≤ u_i, so P ≤ m + 1 + |I*|.
3. (2): if at most m + 1 entries were ≤ κ(u), ℓ entries > κ(u) would form I ∈ 𝓕 with min_I u > κ(u), contradicting maximality.
4. (3): each g_I is 1-Lipschitz for the sup norm (g_I(u) ≤ u_{i₀} ≤ v_{i₀} + t = g_I(v) + t), hence so is their maximum; symmetrize.

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
