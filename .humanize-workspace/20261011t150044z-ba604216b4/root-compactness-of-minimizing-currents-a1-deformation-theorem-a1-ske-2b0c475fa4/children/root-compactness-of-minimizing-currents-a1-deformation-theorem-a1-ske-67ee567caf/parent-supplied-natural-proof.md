# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.skeleton_retraction-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.skeleton_retraction-a1.retraction_family-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 3 (ψ^{(j)} := ⋃_{|J| = j} ψ_F is well defined, because two j-faces meet only in their boundaries, where the retractions are the identity) and step 4 (ψ := ψ^{(n+1)} ∘ ⋯ ∘ ψ^{(P)}). The parent only needs these maps on ℝ^P ∖ L*(a); the gluing argument below never uses that restriction, so the recursion is proved at every point of every face.
Notation. For b ∈ ℤ^P and a finite index set J, F(b, J) := {u : b_i ≤ u_i ≤ b_i + 1 (i ∈ J), u_i = b_i (i ∉ J)}. For J ≠ ∅ let R_{b,J} : ℝ^P → ℝ^P be the map (built with WithLp.toLp) with R_{b,J}(u)_i = b_i + a_i + (u_i − b_i − a_i)/N_{b,J}(u) for i ∈ J and R_{b,J}(u)_i = u_i for i ∉ J, where N_{b,J}(u) = max_{k ∈ J} max((u_k − b_k − a_k)/(1 − a_k), (b_k + a_k − u_k)/a_k) (Finset.sup'; its value does not depend on the nonemptiness proof). For J = ∅ let R_{b,J} := id. For J ≠ ∅, R_{b,J} satisfies the coordinate hypothesis on ψF in the sibling face_radial.
1. Boundary lemma. Let |J| = |J'|, u ∈ F(b, J) ∩ F(b', J') and (b, J) ≠ (b', J'). Then u_i ∈ {b_i, b_i + 1} for some i ∈ J.
 Proof. If J ≠ J', then J ⊄ J' (a subset of the same finite cardinality would be equal), so pick i ∈ J ∖ J'. Then u_i = b'_i ∈ ℤ and b_i ≤ u_i ≤ b_i + 1, and the only integers in [b_i, b_i + 1] are b_i and b_i + 1.
 If J = J', then b_i ≠ b'_i for some i. The case i ∉ J is impossible, since then b_i = u_i = b'_i. So i ∈ J and u_i ∈ [b_i, b_i + 1] ∩ [b'_i, b'_i + 1]. For distinct integers this intersection is empty unless b'_i = b_i ± 1, and then it is {b_i + 1} or {b_i}. Either way u_i ∈ {b_i, b_i + 1}.
 By symmetry, u_{i'} ∈ {b'_{i'}, b'_{i'} + 1} for some i' ∈ J'.
2. Consistency. If |J| = |J'| ≥ 1 and u ∈ F(b, J) ∩ F(b', J'), then R_{b,J}(u) = R_{b',J'}(u). If (b, J) = (b', J') this is trivial. Otherwise, by 1, u has a coordinate i ∈ J with u_i ∈ {b_i, b_i + 1}. From |a_i − 1/2| < 1/4 we get 1/4 < a_i < 3/4, so u_i ≠ b_i + a_i; hence face_radial applies to the face (b, J), the map R_{b,J} and the point u, and its conclusion (5) (ψF x = x at boundary points) gives R_{b,J}(u) = u. In the same way R_{b',J'}(u) = u.
3. Step maps (the parent's ψ^{(j)}). For j ∈ ℕ and u ∈ ℝ^P: if some pair (b', J') with |J'| = j satisfies u ∈ F(b', J'), choose such a pair p_j(u) (classical choice) and put φ_j(u) := R_{p_j(u)}(u). Otherwise put φ_j(u) := u.
4. The composite (the parent's ψ = ψ^{(n+1)} ∘ ⋯ ∘ ψ^{(P)}). Define Ψ by recursion on k: Ψ_k := id for k ≤ m + 1, and Ψ_k := Ψ_{k−1} ∘ φ_k for k ≥ m + 2. Then Ψ_{m+1} = id, and Ψ_j(u) = Ψ_{j−1}(φ_j(u)) for every j ≥ m + 2 and every u.
5. The recursion. Let m + 2 ≤ j ≤ P, let J have |J| = j (so J ≠ ∅), b ∈ ℤ^P, x ∈ F(b, J), and y as in the statement. All coordinates of y and R_{b,J}(x) agree (the nonemptiness proof inside Finset.sup' is irrelevant), so y = R_{b,J}(x) (PiLp.ext). The pair (b, J) shows that the choice in 3 is made, so φ_j(x) = R_p(x) for some p = (b', J') with |J'| = j ≥ 1 and x ∈ F(b', J'). By 2, R_p(x) = R_{b,J}(x) = y. Hence Ψ_j(x) = Ψ_{j−1}(φ_j(x)) = Ψ_{j−1}(y). ∎
Lean reference (not part of the argument): a complete Lean proof of exactly this type, using only propext, Classical.choice and Quot.sound, is the theorem GMT.Ch07.RevCheck.retraction_family in /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcdtsr_skeleton_retraction_decomposition/EndToEnd.lean; its structure follows the numbered steps above.

## Key steps

1. Two distinct j-faces through a point meet only where the point has a boundary coordinate in each face.
2. At boundary points both radial retractions are the identity (face_radial (5)), so all j-faces through a point give the same value.
3. Define the step map φ_j by choosing any j-face through the point, and Ψ_k := Ψ_{k−1} ∘ φ_k for k ≥ m + 2, with Ψ_{m+1} = id.
4. For x in a j-face, φ_j(x) equals that face's retraction, i.e. the given y, so Ψ_j(x) = Ψ_{j−1}(y); no restriction to the complement of L*(a) is needed.

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
