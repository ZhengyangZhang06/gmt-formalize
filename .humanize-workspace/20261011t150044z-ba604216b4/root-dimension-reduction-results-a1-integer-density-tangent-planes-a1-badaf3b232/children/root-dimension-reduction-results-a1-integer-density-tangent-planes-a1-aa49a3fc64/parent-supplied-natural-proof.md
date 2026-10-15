# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.cone_set_finite_planes-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.cone_set_finite_planes-a1.planes_eq_or_inf_bot-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 4, 5 and the core of step 8 of the supplied proof of idtp_tdc_cone_set_finite_planes (the great circles through two seeds are equal or disjoint, so distinct planes meet only in 0). Notation: B_r(y) = ball y r.
1. (Reduction.) If Q₁ ⊓ Q₂ = ⊥, the right disjunct holds. Otherwise, by Submodule.ne_bot_iff there is v ∈ Q₁ ⊓ Q₂ with v ≠ 0, and by Submodule.mem_inf, v ∈ Q₁ and v ∈ Q₂. We prove the left disjunct Q₁ = Q₂.
2. (A common unit vector.) Since v ≠ 0, |v| > 0. Put u := |v|⁻¹·v. Then |u| = |v|⁻¹·|v| = 1, and u ∈ Q₁, u ∈ Q₂ because subspaces are closed under scalar multiplication.
3. (S is locally Q₁ and locally Q₂ at u.) The sibling theorem idtp_tdc_csfp_great_circle_local_plane applied to (P, S, Q₁, x₀ := p₁, ε₀ := δ₁) has hypotheses IsClosed S, the local-planarity hypothesis (verbatim the one assumed here), finrank Q₁ = 2, p₁ ∈ Q₁, |p₁| = 1, 0 < δ₁ and S ∩ B_δ₁(p₁) = Q₁ ∩ B_δ₁(p₁), all given; evaluated at x := u (u ∈ Q₁, |u| = 1) it yields ε₁ > 0 with S ∩ B_ε₁(u) = Q₁ ∩ B_ε₁(u). In the same way, applied to (P, S, Q₂, p₂, δ₂) and evaluated at u (u ∈ Q₂, |u| = 1), it yields ε₂ > 0 with S ∩ B_ε₂(u) = Q₂ ∩ B_ε₂(u).
4. (Q₁ and Q₂ agree near u.) Let t := min(ε₁, ε₂) > 0. Then B_t(u) ⊆ B_ε₁(u) and B_t(u) ⊆ B_ε₂(u) (Metric.ball_subset_ball), so
 Q₁ ∩ B_t(u) = (Q₁ ∩ B_ε₁(u)) ∩ B_t(u) = (S ∩ B_ε₁(u)) ∩ B_t(u) = S ∩ B_t(u) = (S ∩ B_ε₂(u)) ∩ B_t(u) = (Q₂ ∩ B_ε₂(u)) ∩ B_t(u) = Q₂ ∩ B_t(u).
5. (Conclusion.) Since u ∈ Q₁ and t > 0, the sibling theorem idtp_tdc_csfp_subspace_eq_of_inter_ball applied to (P, Q₁, Q₂, u, t) gives Q₁ = Q₂. ∎

## Key steps

1. If Q₁ ⊓ Q₂ ≠ ⊥, normalise a nonzero common vector to a unit vector u ∈ Q₁ ∩ Q₂.
2. idtp_tdc_csfp_great_circle_local_plane, seeded at (p₁, δ₁) resp. (p₂, δ₂), gives balls about u on which S equals Q₁ resp. Q₂.
3. On the smaller of the two balls Q₁ and Q₂ agree, so idtp_tdc_csfp_subspace_eq_of_inter_ball gives Q₁ = Q₂.

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
