# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.retraction-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.retraction-a1.grid_segment-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 7(i) of the parent proof (cut the segment at the walls of the unit cubes it meets, apply the cube estimate on each piece, and sum over the collinear ordered pieces), with the cube estimate (3') of step 6 abstracted as the hypothesis.
1. Let γ(t) := x + t(y − x) for t ∈ [0, 1]. Then γ(0) = x, γ(1) = y, γ([0, 1]) = [x, y] ⊆ S, γ_i(t) = x_i + t(y_i − x_i), and dist(γ(t), γ(t')) = |t − t'|·dist(x, y).
2. Breakpoints. Let I₀ := {i : x_i ≠ y_i}. For i ∈ I₀ the map t ↦ γ_i(t) is affine and strictly monotone, hence injective, and it maps T_i := {t ∈ [0, 1] : γ_i(t) ∈ ℤ} into the finite set ℤ ∩ [min(x_i, y_i), max(x_i, y_i)]; so T_i is finite. Let T := {0, 1} ∪ ⋃_{i∈I₀} T_i. T is a finite subset of [0, 1] containing 0 and 1; list it increasingly as 0 = t_0 < t_1 < ⋯ < t_N = 1 (N ≥ 1; in Mathlib, e.g. via Finset.orderEmbOfFin or Finset.sort).
3. Each piece lies in one closed cube. Fix k < N, put s := (t_k + t_{k+1})/2 and z_i := ⌊γ_i(s)⌋ for every i. Claim: z_i ≤ γ_i(t) ≤ z_i + 1 for all t ∈ [t_k, t_{k+1}] and all i. If i ∉ I₀, then γ_i(t) = x_i = γ_i(s) ∈ [z_i, z_i + 1). Let i ∈ I₀. Since t_k < s < t_{k+1} and t_k, t_{k+1} are consecutive in T, s ∉ T, so γ_i(s) ∉ ℤ and z_i < γ_i(s) < z_i + 1. Suppose γ_i(t) < z_i for some t ∈ [t_k, t_{k+1}]. As γ_i is affine and γ_i(t) < z_i < γ_i(s), the parameter t' := (z_i − x_i)/(y_i − x_i), at which γ_i(t') = z_i, lies strictly between t and s, hence in (t_k, t_{k+1}); and t' ∈ T_i ⊆ T. This contradicts that t_k and t_{k+1} are consecutive elements of T. The case γ_i(t) > z_i + 1 is excluded in the same way with z_i + 1 in place of z_i.
4. Estimate on a piece. By step 3, γ(t_k) and γ(t_{k+1}) both lie in the closed cube z + [0, 1]^P, and both lie in S by step 1. By the hypothesis, dist(f(γ(t_k)), f(γ(t_{k+1}))) ≤ K·dist(γ(t_k), γ(t_{k+1})) = K(t_{k+1} − t_k)·dist(x, y).
5. Summation. By the triangle inequality along γ(t_0), …, γ(t_N) (Mathlib dist_le_range_sum_dist), dist(f(x), f(y)) ≤ Σ_{k<N} dist(f(γ(t_k)), f(γ(t_{k+1}))) ≤ K·dist(x, y)·Σ_{k<N}(t_{k+1} − t_k) = K·dist(x, y)·(t_N − t_0) = K·dist(x, y). ∎

## Key steps

1. Parametrize [x, y] by γ(t) = x + t(y − x); the parameters where a non-constant coordinate is an integer, together with 0 and 1, form a finite set 0 = t_0 < ⋯ < t_N = 1.
2. Between consecutive breakpoints no non-constant coordinate crosses an integer, so each piece [γ(t_k), γ(t_{k+1})] lies in the closed cube ⌊γ(midpoint)⌋ + [0, 1]^P.
3. The cube hypothesis bounds each piece by K(t_{k+1} − t_k)·dist(x, y); the triangle inequality and the telescoping sum give K·dist(x, y).

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
