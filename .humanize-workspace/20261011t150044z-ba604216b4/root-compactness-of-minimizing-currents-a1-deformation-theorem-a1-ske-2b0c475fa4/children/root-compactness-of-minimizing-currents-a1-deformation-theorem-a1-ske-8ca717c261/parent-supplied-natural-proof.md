# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.skeleton_retraction-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.skeleton_retraction-a1.cube_cover-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 5 ('Points y near x lie in one of the finitely many closed unit cubes containing x') and its use in step 6. This child proves that local finiteness fact.
1. One-dimensional claim. For t ∈ ℝ let A(t) := {k ∈ {⌊t⌋ − 1, ⌊t⌋} : k ≤ t ≤ k + 1} and V(t) := ⋃_{k ∈ A(t)} [k, k + 1]. Then V(t) is a neighbourhood of t. If t ∉ ℤ then ⌊t⌋ < t < ⌊t⌋ + 1, so ⌊t⌋ ∈ A(t) and V(t) ⊇ (⌊t⌋, ⌊t⌋ + 1) ∋ t. If t ∈ ℤ then ⌊t⌋ = t, both t − 1 and t lie in A(t), and V(t) ⊇ [t − 1, t + 1] ⊇ (t − 1, t + 1) ∋ t. (Int.floor_le, Int.lt_floor_add_one.)
2. Let Z be the set of z ∈ ℤ^P with z_i ∈ {⌊x_i⌋ − 1, ⌊x_i⌋} and z_i ≤ x_i ≤ z_i + 1 for all i. It is a subset of the finite product ∏_i {⌊x_i⌋ − 1, ⌊x_i⌋} (Fintype.piFinset, then Finset.filter), hence a Finset, and by construction x ∈ z + [0,1]^P for every z ∈ Z. This is the first conclusion.
3. For each coordinate i the map y ↦ y_i is continuous, so by 1 the set W_i := {y : y_i ∈ V(x_i)} is a neighbourhood of x. Since there are finitely many coordinates, eventually (in 𝓝 x) y ∈ W_i holds for all i (Filter.eventually_all).
4. Let y ∈ W_i for all i. For each i choose k_i ∈ A(x_i) with k_i ≤ y_i ≤ k_i + 1 (possible because y_i ∈ V(x_i)) and put z := (k_i)_i. Then z_i ∈ {⌊x_i⌋ − 1, ⌊x_i⌋} and z_i ≤ x_i ≤ z_i + 1 for every i, so z ∈ Z, and z_i ≤ y_i ≤ z_i + 1 for every i. This is the second conclusion. ∎
Lean reference (not part of the argument): a complete Lean proof of exactly this type, using only propext, Classical.choice and Quot.sound, is the theorem GMT.Ch07.ElemCheck.cube_cover in /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcdtsr_skeleton_retraction_decomposition/EndToEnd.lean; its structure follows the numbered steps above.

## Key steps

1. In one dimension, the unit intervals [k, k + 1] ∋ t with k ∈ {⌊t⌋ − 1, ⌊t⌋} cover a neighbourhood of t.
2. Z := the cubes with corner in ∏_i {⌊x_i⌋ − 1, ⌊x_i⌋} that contain x; Z is finite.
3. Intersect the finitely many coordinate neighbourhoods and choose the corner coordinate by coordinate.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); git -C local-references/123e8435b4a2469b/mathlib rev-parse HEAD (25730c7c759d108ef87ab70af2342a196760f79d, matches manifest)`
- `rg -n -i 'skeleton|cubical|retraction|latticeFace|dual skeleton' project/GMT -g '*.lean'`
- `rg -n 'cmcdtsr_' local-references/123e8435b4a2469b -g '*.lean' (no match)`
- `grep -c for each proposed name in dag.json: cmcdtsr_segment_lipschitz, cmcdtsr_cube_cover, cmcdtsr_dual_dist_count, cmcdtsr_face_radial, cmcdtsr_face_retraction_family, cmcdtsr_face_count_induction (0 each)`
- `rg -n 'theorem IsClosed.Icc_subset_of_forall_mem_nhdsWithin|theorem IsClosed.mem_of_ge_of_forall_exists_gt' mathlib/Mathlib`
- `rg -n 'theorem infDist_le_dist_of_mem|theorem infDist_le_infDist_add_dist|theorem infDist_nonneg|theorem infDist_empty' mathlib/Mathlib`
- `rg -n 'theorem exists_mem_eq_sup.|theorem le_sup.' mathlib/Mathlib/Data/Finset/Lattice/Fold.lean`
- `rg -n 'exists_subset_card_eq|sum_lt_sum_of_nonempty|lemma le_induction|piFinset|eventually_nhdsWithin_iff|abs_max_sub_max_le_max|theorem dist_apply_le|ContinuousOn.preimage_isClosed_of_isClosed' mathlib/Mathlib`
- `lake env lean /tmp/cmcdtsr2/lean/FinalTypes.lean (six child types elaborate in namespace GMT.Ch07 with the contract's opens)`
- `lake env lean /tmp/cmcdtsr2/lean/FinalAssembly.lean (#print axioms: propext, Classical.choice, Quot.sound + five child axioms)`
- `lake env lean /tmp/cmcdtsr2/lean/Instances.lean (L2 dist, Metric.infDist, ofLp coordinates, Finset.sup' = max)`
- `lake env lean GMT/Scratch/cmcdtsr_skeleton_retraction_decomposition/EndToEnd.lean (all six child types and the parent type proved; axioms propext, Classical.choice, Quot.sound)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/IntermediateValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Finset/Lattice/Fold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Finset/Card.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Nat/Init.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fintype/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/NhdsWithin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/Group/MinMax.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/ContinuousOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/BigOperators/Group/Finset.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-ske-2b0c475fa4/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-ske-2b0c475fa4/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcdtsr_skeleton_retraction_decomposition/Types.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcdtsr_skeleton_retraction_decomposition/Assembly.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcdtsr_skeleton_retraction_decomposition/Instances.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcdtsr_skeleton_retraction_decomposition/EndToEnd.lean`

The snapshot (project b4d606d, Mathlib 25730c7c) has a Ch07 contract byte-identical to the workspace Submission.lean. The only related project material is the unsolved Ch06 specification (latticeFace, LatticeFaceIndex, IsLatticeChain over the incompatible type Eucl). It has no retraction or skeleton theorem, so nothing is reusable. No cmcdtsr_ declaration exists in the snapshot, and none of the six proposed names occurs in the DAG (0 matches each). Mathlib provides every tool cited by the child proofs: IsClosed.Icc_subset_of_forall_mem_nhdsWithin, ContinuousOn.preimage_isClosed_of_isClosed, infDist_le_dist_of_mem, infDist_le_infDist_add_dist, infDist_empty, Finset.exists_mem_eq_sup', Finset.le_sup', Finset.exists_subset_card_eq, Finset.sum_lt_sum_of_nonempty, Nat.le_induction, Fintype.piFinset, eventually_nhdsWithin_iff, abs_max_sub_max_le_max, PiLp.dist_apply_le and EuclideanSpace.dist_eq. All six child types elaborate. The assembly proves the frozen parent type from five of them using only the standard axioms. EndToEnd.lean contains complete Lean proofs of all six children and of the parent with only propext, Classical.choice and Quot.sound.
