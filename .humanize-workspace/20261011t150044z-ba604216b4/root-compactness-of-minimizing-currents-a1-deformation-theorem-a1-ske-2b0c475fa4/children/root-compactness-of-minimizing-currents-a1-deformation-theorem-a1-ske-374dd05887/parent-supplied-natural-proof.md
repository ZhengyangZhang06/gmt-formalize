# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.skeleton_retraction-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.skeleton_retraction-a1.face_induction-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 5 (pointwise bound D̄ψ ≤ c₁/d, proved by induction on the codimension). Here the induction runs over the faces of ℝ^P themselves: a j-face F(b, J) together with the planes of L*(a) through its centre is the parent's situation (j, n, a') after the identification aff F ≅ ℝ^j, and the parent's inductive hypothesis 'ψ̃ on the (P − 1)-faces' becomes Claim(j − 1) below, for Ψ_{j−1} on the (j − 1)-faces. The parent measures the distance to the cone K₀ of planes through the face centre (dist(y₀, K₀) = λ·dist(x, K₀)); here that distance is kept in the coordinate form of the counting condition C below, which scales exactly under the homothety y₀ = a_F + λ(x − a_F). So the periodic planes L₁ and the parent's 1/4 margin are not needed. The radial estimate of step 3 is used in its gauge form (1 + 4√j)|y − x|/N_F(x − a_F), from the sibling face_radial, so the factor N_F = 1/λ cancels in the chain rule.
Notation. For b ∈ ℤ^P and a finite index set J:
- F(b, J) := {u : b_i ≤ u_i ≤ b_i + 1 (i ∈ J), u_i = b_i (i ∉ J)}, with centre a_F (coordinates b_i + a_i on J, b_i off J);
- for J ≠ ∅, N_{b,J}(u) := max_{k ∈ J} max((u_k − b_k − a_k)/(1 − a_k), (b_k + a_k − u_k)/a_k) (Finset.sup'; independent of the nonemptiness proof);
- ψ_{b,J} : ℝ^P → ℝ^P is the map (built with WithLp.toLp) with ψ_{b,J}(u)_i = b_i + a_i + (u_i − b_i − a_i)/N_{b,J}(u) for i ∈ J and ψ_{b,J}(u)_i = u_i for i ∉ J; it satisfies the coordinate hypothesis on ψF in face_radial;
- for u ∈ ℝ^P and ρ > 0, C(b, J, u, ρ) means #{i ∈ J : |u_i − b_i − a_i| < ρ} ≤ m + 1.
REC denotes the recursion hypothesis on Ψ. Applied with y := ψ_{b,J}(u), whose coordinates are exactly the required ones, it gives Ψ_j(u) = Ψ_{j−1}(ψ_{b,J}(u)) whenever m + 2 ≤ j ≤ P, |J| = j and u ∈ F(b, J).
Put K := 1 + 4√P ≥ 1 and c := K^P > 0; c depends only on P.
Claim(j), for m + 2 ≤ j ≤ P: for all b, all J with |J| = j, all x ∈ F(b, J) and all ρ > 0 with C(b, J, x, ρ):
 (A) Ψ_j(x) ∈ F(b, J);
 (B) there is a set s with P ≤ m + 1 + |s| and Ψ_j(x)_i ∈ ℤ for i ∈ s;
 (C) there is δ > 0 with |Ψ_j(y) − Ψ_j(x)| ≤ (K^{j−m−1}/ρ)|y − x| for all y ∈ F(b, J) with |y − x| < δ.
0. Claim(j) for all j ∈ [m + 2, P] gives the theorem with this c. (A) and (B) are its first two conclusions. Because K ≥ 1 and 0 ≤ j − m − 1 ≤ P, K^{j−m−1} ≤ K^P = c, so (C) gives dist(Ψ_j y, Ψ_j x) ≤ (c/ρ)·dist(y, x) for all y ∈ F(b, J) with dist(y, x) < δ, i.e. eventually in 𝓝[F(b, J)] x (Metric.mem_nhdsWithin_iff). Claim(j) is proved by induction on j starting at m + 2 (Nat.le_induction), carrying the hypothesis j ≤ P (if j + 1 ≤ P then j ≤ P).
1. Preliminaries. Fix j with m + 2 ≤ j ≤ P, b, J with |J| = j (so J ≠ ∅), F := F(b, J), x ∈ F and ρ > 0 with C(b, J, x, ρ). Write N := N_{b,J} and ψ_F := ψ_{b,J}.
 (a) Since |J| = j ≥ m + 2 > m + 1, some i ∈ J has |x_i − b_i − a_i| ≥ ρ > 0 (otherwise all j indices of J would be counted). In particular x_i ≠ b_i + a_i, so face_radial applies to x, and by its conclusion (1), N(x) ≥ |x_i − b_i − a_i| ≥ ρ.
 (b) If y ∈ F and |y − x| < ρ/2, then C(b, J, y, ρ/2) holds. Indeed, if |y_i − b_i − a_i| < ρ/2, then |x_i − b_i − a_i| ≤ |x_i − y_i| + |y_i − b_i − a_i| < ρ/2 + ρ/2 = ρ, since |x_i − y_i| ≤ |x − y| (PiLp.dist_apply_le). So the set counted for (y, ρ/2) is contained in the set counted for (x, ρ). Applying (a) to y and ρ/2: y_i ≠ b_i + a_i for some i ∈ J.
 (c) By REC, Ψ_j(u) = Ψ_{j−1}(ψ_F(u)) for every u ∈ F.
 (d) By face_radial at x: 0 < N(x) ≤ 1; ψ_F(x) ∈ F; ψ_F(x)_i ∈ {b_i, b_i + 1} for some i ∈ J; and |ψ_F(y) − ψ_F(x)| ≤ (1 + 4√j)/N(x)·|y − x| for every y ∈ F with y_i ≠ b_i + a_i for some i ∈ J, in particular, by (b), for every y ∈ F with |y − x| < ρ/2. For every such y, face_radial at y gives ψ_F(y) ∈ F and ψ_F(y)_i ∈ {b_i, b_i + 1} for some i ∈ J.
2. Base case j = m + 2. By (c) and Ψ_{m+1} = id, Ψ_j(u) = ψ_F(u) for every u ∈ F.
 (A) Ψ_j(x) = ψ_F(x) ∈ F by 1(d).
 (B) Take i₀ ∈ J with ψ_F(x)_{i₀} ∈ {b_{i₀}, b_{i₀} + 1} (1(d)) and let s := (all indices ∖ J) ∪ {i₀}. For i ∉ J, ψ_F(x)_i = x_i = b_i ∈ ℤ, and ψ_F(x)_{i₀} ∈ ℤ. Since i₀ ∈ J, |s| = (P − (m + 2)) + 1, so P = m + 1 + |s|.
 (C) Take δ := ρ/2. For y ∈ F with |y − x| < δ, 1(d), N(x) ≥ ρ from 1(a), and m + 2 ≤ P give |Ψ_j(y) − Ψ_j(x)| = |ψ_F(y) − ψ_F(x)| ≤ (1 + 4√(m + 2))/N(x)·|y − x| ≤ (K/ρ)|y − x|, and K = K^{j−m−1}.
3. Inductive step: m + 3 ≤ j ≤ P, and Claim(j − 1) holds. Put y₀ := ψ_F(x) and λ := 1/N(x) > 0. By the formula for ψ_F, y₀_k − b_k − a_k = λ(x_k − b_k − a_k) for k ∈ J (parent: y₀ = a + λ(x − a)) and y₀_k = x_k = b_k for k ∉ J. By (c), Ψ_j(x) = Ψ_{j−1}(y₀).
 (i) Faces through y₀. For i ∈ J and an integer β ∈ {b_i, b_i + 1} put b^{i,β} := b with the i-th entry replaced by β (Function.update), J^i := J ∖ {i} (so |J^i| = j − 1 ≥ m + 2), and G_{i,β} := F(b^{i,β}, J^i). Then G_{i,β} ⊆ F: for u ∈ G_{i,β}, b_k ≤ u_k ≤ b_k + 1 for k ∈ J^i, u_i = β ∈ [b_i, b_i + 1], and u_k = b_k for k ∉ J. If y₀_i = β, then y₀ ∈ G_{i,β}: b_k ≤ y₀_k ≤ b_k + 1 for k ∈ J^i since y₀ ∈ F, y₀_i = β, and y₀_k = b_k for k ∉ J. By 1(d) at least one pair (i, β) with y₀_i = β exists, and there are at most 2j pairs in all.
 (ii) Scaling (parent: dist(y₀, K₀) = λ·dist(x, K₀)). If y₀_i = β, then C(b^{i,β}, J^i, y₀, λρ) holds. For k ∈ J^i, b^{i,β}_k = b_k and |y₀_k − b_k − a_k| = λ|x_k − b_k − a_k|, which is < λρ iff |x_k − b_k − a_k| < ρ, since λ > 0. So the counted set is a subset of the one for (b, J, x, ρ), which has at most m + 1 elements.
 (iii) For every pair with y₀_i = β apply Claim(j − 1) to (b^{i,β}, J^i, y₀, λρ). Its (A) gives Ψ_{j−1}(y₀) ∈ G_{i,β} ⊆ F; this is (A) for Ψ_j(x) = Ψ_{j−1}(y₀). Its (B) is (B) for Ψ_j(x). Its (C) gives δ_{i,β} > 0 such that |Ψ_{j−1}(y') − Ψ_{j−1}(y₀)| ≤ (K^{j−m−2}/(λρ))|y' − y₀| = (K^{j−m−2}N(x)/ρ)|y' − y₀| for all y' ∈ G_{i,β} with |y' − y₀| < δ_{i,β}.
 (iv) Nearby boundary points lie on faces through y₀ (parent: every face meeting B_δ(y₀) contains y₀). Choose η > 0 with η ≤ δ_{i,β} for every pair with y₀_i = β and η ≤ |y₀_i − β| for every pair (i ∈ J, β ∈ {b_i, b_i + 1}) with y₀_i ≠ β; for instance the minimum of these finitely many positive numbers and 1.
 (v) Put δ := min(ρ/2, η·N(x)/(1 + 4√j)) > 0. For y ∈ F with |y − x| < δ, 1(d) gives |ψ_F(y) − y₀| ≤ (1 + 4√j)/N(x)·|y − x| < η.
 (vi) Let y ∈ F with |y − x| < δ. By (c), Ψ_j(y) = Ψ_{j−1}(ψ_F(y)). By 1(d) (note |y − x| < ρ/2), ψ_F(y) ∈ F and ψ_F(y)_i = β for some i ∈ J and some β ∈ {b_i, b_i + 1}. If y₀_i ≠ β, then |y₀_i − β| = |y₀_i − ψ_F(y)_i| ≤ |y₀ − ψ_F(y)| < η ≤ |y₀_i − β|, which is impossible; so y₀_i = β and (i, β) is one of the pairs in (iii). Then ψ_F(y) ∈ G_{i,β}: its coordinates k ∈ J^i lie in [b_k, b_k + 1] because ψ_F(y) ∈ F, its i-th coordinate is β, and ψ_F(y)_k = y_k = b_k for k ∉ J. Since |ψ_F(y) − y₀| < η ≤ δ_{i,β}, (iii) and (v) give
 |Ψ_j(y) − Ψ_j(x)| = |Ψ_{j−1}(ψ_F(y)) − Ψ_{j−1}(y₀)| ≤ (K^{j−m−2}N(x)/ρ)·|ψ_F(y) − y₀| ≤ (K^{j−m−2}N(x)/ρ)·((1 + 4√j)/N(x))·|y − x| ≤ (K^{j−m−1}/ρ)|y − x|,
 because 1 + 4√j ≤ 1 + 4√P = K. This is (C) of Claim(j) with this δ.
4. By induction Claim(j) holds for all m + 2 ≤ j ≤ P, and step 0 gives the theorem. ∎
Lean reference (not part of the argument): a complete Lean proof of exactly this type, using only propext, Classical.choice and Quot.sound, is the theorem GMT.Ch07.IndCheck.face_induction in /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcdtsr_skeleton_retraction_decomposition/EndToEnd.lean; its structure follows the numbered steps above.

## Key steps

1. Counting condition C(x, ρ) gives a coordinate with |x_i − b_i − a_i| ≥ ρ, hence x ≠ a_F and N(x) ≥ ρ, and it passes to y near x with radius ρ/2.
2. REC plus face_radial: on F, Ψ_j = Ψ_{j−1} ∘ ψ_F, and ψ_F has the radial bound (1 + 4√j)/N(x) near x.
3. Base case j = m + 2: Ψ_j = ψ_F on F, constant (1 + 4√P)/ρ, plus one extra integer coordinate from the boundary.
4. Inductive step: y₀ = ψ_F(x) lies on the (j − 1)-faces G_{i,β}; the counting condition scales to radius ρ/N(x) at y₀ (homothety of the cone K₀).
5. Points ψ_F(y) for y near x lie on faces through y₀; chain the inductive constant K^{j−m−2}N(x)/ρ with (1 + 4√j)/N(x), cancelling N(x).
6. Constants K^{j−m−1} ≤ (1 + 4√P)^P = c give the uniform bound c/ρ, eventually in 𝓝[F] x.

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
