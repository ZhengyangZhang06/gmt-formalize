# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.cone_set_finite_planes-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.cone_set_finite_planes-a1.subspace_eq_of_inter_ball-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1 (uniqueness of planes) of the supplied proof of idtp_tdc_cone_set_finite_planes, which details Simon's claim in the proof of 7.3.3(1) (chapter-07.txt lines 502-504) that spt S0 lies in finitely many 2-planes P_i with P_i ∩ P_j = {0}. Notation: B_t(x) = {y : |y − x| < t} (Mathlib `ball x t`); Q₁, Q₂ are also viewed as subsets of ℝ^P. No dimension hypothesis is needed.
1. (x ∈ Q₂.) Since |x − x| = 0 < t, x ∈ Q₁ ∩ B_t(x) = Q₂ ∩ B_t(x); hence x ∈ Q₂.
2. (One inclusion, in general form.) Let A, B be linear subspaces of ℝ^P with x ∈ A, x ∈ B and A ∩ B_t(x) = B ∩ B_t(x). We show A ⊆ B. Let v ∈ A and put s := t/(2(|v| + 1)). Then s > 0 and s|v| ≤ s(|v| + 1) = t/2 < t. The point y := x + s·v lies in A (A contains x and s·v and is closed under addition), and |y − x| = |s·v| = s|v| < t, so y ∈ A ∩ B_t(x) = B ∩ B_t(x), i.e. y ∈ B. As x ∈ B, s·v = y − x ∈ B, and therefore v = s⁻¹·(s·v) ∈ B.
3. (Conclusion.) Step 2 with (A, B) := (Q₁, Q₂), using x ∈ Q₁, x ∈ Q₂ (step 1) and the hypothesis Q₁ ∩ B_t(x) = Q₂ ∩ B_t(x), gives Q₁ ≤ Q₂. Step 2 with (A, B) := (Q₂, Q₁), using the reversed equality Q₂ ∩ B_t(x) = Q₁ ∩ B_t(x), gives Q₂ ≤ Q₁. By antisymmetry of ≤ on submodules, Q₁ = Q₂. ∎
(Lean pointers: Metric.mem_ball_self, Submodule.add_mem / smul_mem / sub_mem, norm_smul, Real.norm_of_nonneg, smul_smul, inv_mul_cancel₀, le_antisymm.)

## Key steps

1. x lies in Q₁ ∩ B_t(x) = Q₂ ∩ B_t(x), so x ∈ Q₂.
2. For v ∈ Q₁ and s = t/(2(|v|+1)) > 0, the point x + s·v lies in Q₁ ∩ B_t(x) = Q₂ ∩ B_t(x), so s·v = (x + s·v) − x ∈ Q₂ and v = s⁻¹·(s·v) ∈ Q₂.
3. The same argument with Q₁ and Q₂ exchanged, and antisymmetry of ≤, give Q₁ = Q₂.

## Reference use

### local-project

Queries:
- `cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; cmp GMT/Ch07/Contract.lean local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD (compared with manifest.json)`
- `rg -n 'theorem isConnected_sphere|theorem isPreconnected_sphere|theorem IsCompact.elim_nhds_subcover|theorem IsPreconnected.subset_of_closure_inter_subset|theorem isCompact_sphere|theorem IsCompact.elim_finite_subcover|def equivFin|theorem eq_bot_iff' mathlib/Mathlib`
- `rg -n 'noncomputable def Finset.equivFin|theorem ne_bot_iff \(p : Submodule|theorem mem_inf \{p q : Submodule|theorem ball_subset_ball.|theorem mem_closure_iff \{|theorem finrank_eq_rank|theorem IsConnected.image|theorem IsCompact.inter_left|theorem ball_mem_nhds' mathlib/Mathlib; rg -n finite_of_finrank_eq_succ mathlib/Mathlib`
- `python3 scan of dag.json lean_name/lean_statement fields: prefix idtp, substrings csfp, great_circle, subspace_eq, and statements containing Submodule and ball`
- `grep -c / grep -rl for idtp_tdc_csfp_subspace_eq_of_inter_ball, idtp_tdc_csfp_great_circle_local_plane, idtp_tdc_csfp_planes_eq_or_inf_bot in dag.json, nodes/, GMT/; git log --all -S idtp_tdc_csfp`
- `git log --all --oneline -S 'import Mathlib.Analysis' -- GMT/Ch07/Submission.lean; git show bff81d31e (precedent for adding pinned Mathlib imports)`
- `grep -n 'finite union|Whi82' book/chapter-07.txt`
- `lake env lean on Statements.lean, ChildA.lean, ChildB.lean (+ import Mathlib.Analysis.Normed.Module.Connected), ChildC.lean, Assembly.lean, EndToEnd.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Connected.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Connected/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/ProperSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fintype/EquivFin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Module/Submodule/Lattice.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/Free.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/StrongRankCondition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-badaf3b232/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/idtp_tdc_csfp_split_decision/Statements.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/idtp_tdc_csfp_split_decision/ChildA.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/idtp_tdc_csfp_split_decision/ChildB.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/idtp_tdc_csfp_split_decision/ChildC.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/idtp_tdc_csfp_split_decision/Assembly.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/idtp_tdc_csfp_split_decision/EndToEnd.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/idtp_tdc_csfp_split_decision/EndToEnd.log`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/idtp_tdc_csfp_split_decision/proposal.json`

Pins and contract:
- The pins match manifest.json: project b4d606db, mathlib 25730c7c.
- The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

Mathlib snapshot:
- It contains every cited fact: isConnected_sphere (Analysis/Normed/Module/Connected.lean:233), IsConnected.image, isCompact_sphere and IsCompact.inter_left.
- It also contains IsCompact.elim_nhds_subcover (Compact.lean:236), Finset.equivFin (EquivFin.lean:320), Submodule.ne_bot_iff, Submodule.mem_inf, Module.finite_of_finrank_eq_succ (Dimension/Free.lean:276), Module.finrank_eq_rank, Metric.ball_subset_ball', Metric.mem_closure_iff, Metric.isOpen_iff and Metric.ball_mem_nhds.
- Connected.lean is not reachable from the frozen imports: isConnected_sphere is an unknown identifier after import GMT.Ch07.Submission. Child great_circle_local_plane therefore adds the pinned import Mathlib.Analysis.Normed.Module.Connected. This follows accepted commit bff81d31e, which added pinned Mathlib imports, and the reviewer's hash check found that the frozen constants are unchanged.

Reuse:
- No DAG node (974 entries) states plane uniqueness from local agreement, great-circle propagation, or equal-or-disjoint planes, so nothing is reused.
- The three idtp_tdc_csfp_* names occur nowhere in dag.json, nodes/, the GMT sources or git history.

Book:
- chapter-07.txt lines 502–504 state the target claim, spt S0 ⊆ ∪ P_i with P_i ∩ P_j = {0}, and cite [Whi82].

Lean checks:
- All three exact lean_statement strings elaborate.
- ChildA, ChildB and ChildC, and Assembly (the exact frozen parent type from child planes_eq_or_inf_bot), all compile.
- EndToEnd.lean compiles the three children as Submission.X with full proofs and Submission.idtp_tdc_cone_set_finite_planes with its exact frozen type. Axioms are propext, Classical.choice and Quot.sound only.
- An independent reviewer reproduced these results and returned ACCEPT.
