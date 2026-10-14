# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.edge_tangent_plane-a1.localization-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.edge_tangent_plane-a1.localization-a1.frame_projection-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1 (F1) of the supplied localization proof, isolated as the frame formula. Notation: π := Q.starProjection. ⟨·,·⟩ is the real Euclidean inner product, so it is symmetric (⟨u, w⟩ = ⟨w, u⟩, real_inner_comm). |·| is the Euclidean norm.
1. (Orthonormality.) The two-element family (a, e), written ![a, e] in Lean, is orthonormal: ⟨a, a⟩ = |a|² = 1, ⟨e, e⟩ = |e|² = 1, and ⟨a, e⟩ = 0 = ⟨e, a⟩ by hypothesis and symmetry (orthonormal_iff_ite). So it is linearly independent (Orthonormal.linearIndependent).
2. (span{a, e} = Q.) Since a ∈ Q and e ∈ Q, span{a, e} ≤ Q (Submodule.span_le). A linearly independent family of two vectors spans a subspace of dimension 2 (finrank_span_eq_card), and Module.finrank ℝ Q = 2 by hypothesis; Q is finite-dimensional, being a subspace of ℝ^P. A subspace contained in a finite-dimensional subspace of the same dimension equals it (Submodule.eq_of_le_of_finrank_eq). So span{a, e} = Q.
3. (Candidate.) Put y := ⟨x, a⟩a + ⟨x, e⟩e. Since a, e ∈ Q and Q is a linear subspace, y ∈ Q.
4. (Orthogonality.) Let w ∈ Q. By step 2, w ∈ span{a, e}, so w = c₀a + c₁e for some reals c₀, c₁ (Submodule.mem_span_range_iff_exists_fun). Using bilinearity, |a|² = |e|² = 1 and ⟨a, e⟩ = ⟨e, a⟩ = 0:
⟨x − y, a⟩ = ⟨x, a⟩ − ⟨x, a⟩⟨a, a⟩ − ⟨x, e⟩⟨e, a⟩ = 0,
⟨x − y, e⟩ = ⟨x, e⟩ − ⟨x, a⟩⟨a, e⟩ − ⟨x, e⟩⟨e, e⟩ = 0.
Hence ⟨x − y, w⟩ = c₀⟨x − y, a⟩ + c₁⟨x − y, e⟩ = 0.
5. (Characterization of π.) Q is finite-dimensional, hence complete, so it has an orthogonal projection. The projection of x is the unique point of Q whose difference from x is orthogonal to Q: if y ∈ Q and ⟨x − y, w⟩ = 0 for every w ∈ Q, then πx = y (Submodule.eq_starProjection_of_mem_of_inner_eq_zero). By steps 3 and 4, Q.starProjection x = ⟨x, a⟩a + ⟨x, e⟩e. ∎

## Key steps

1. (a, e) is orthonormal, hence linearly independent; span{a, e} ≤ Q and both have finrank 2, so span{a, e} = Q (Submodule.eq_of_le_of_finrank_eq).
2. y := ⟨x,a⟩a + ⟨x,e⟩e lies in Q, and ⟨x − y, a⟩ = ⟨x − y, e⟩ = 0, so ⟨x − y, w⟩ = 0 for every w = c₀a + c₁e ∈ Q.
3. Submodule.eq_starProjection_of_mem_of_inner_eq_zero gives Q.starProjection x = ⟨x,a⟩a + ⟨x,e⟩e.

## Reference use

### local-project

Queries:
- `python3 scan of dag.json: node record of idtp_cse_etp_localization (depth 5, status decomposing; max_depth 6 in swarm-project.json), its six siblings under edge_tangent_plane-a1, and a depth/status census (178 accepted depth-6 nodes)`
- `python3 regex scan of dag.json lean_statements: 'starProjection' (short statements), 'starProjection [a-z] = inner', '= inner ℝ [a-z] [a-z] • [a-z] \+ inner ℝ [a-z] [a-z] • [a-z]', '‖Q.starProjection [a-z]‖ \^ 2 = inner', 'arctan', 'Orthonormal ℝ !\['`
- `grep -o 'idtp_cse_etp_loc[a-z_]*' dag.json; grep -rl 'idtp_cse_etp_loc_' nodes/ GMT/ local-references/123e8435b4a2469b/project; ls ../.swarm-worktrees/*/gmt-ch07/GMT/Ch07/Submission.lean | xargs -P 16 grep -l 'idtp_cse_etp_loc_\|idtp_cse_etp_localization'`
- `rg -n 'starProjection [a-z] = inner|inner ℝ x a • a \+ inner ℝ x e • e|Orthonormal ℝ !\[a, e\]' project mathlib/Mathlib; rg -c arctan project/GMT (both: no match)`
- `grep/rg in local-references/123e8435b4a2469b/mathlib for: eq_starProjection_of_mem_of_inner_eq_zero, starProjection_inner_eq_zero, starProjection_apply_mem, norm_sq_eq_add_norm_sq_starProjection, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero, eq_of_le_of_finrank_eq, finrank_span_eq_card, Orthonormal.linearIndependent, orthonormal_iff_ite, Submodule.mem_span_range_iff_exists_fun, cos_arctan, one_sub_sq_div_two_le_cos, sqrt_eq_iff_mul_self_eq_of_pos, pow_le_pow_iff_left₀, inv_anti₀, div_le_one, real_inner_comm, real_inner_self_eq_norm_sq`
- `git -C local-references/123e8435b4a2469b/mathlib rev-parse HEAD; git -C local-references/123e8435b4a2469b/project rev-parse HEAD; cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean GMT/Ch07/Submission.lean`
- `lake env lean /tmp/loc_split_check/A.lean; lake env lean /tmp/loc_split_check/B.lean; lake env lean /tmp/loc_split_check/Full.lean; lake env lean /tmp/loc_split_check/FullAx.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/swarm-project.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-47b0e3a61b/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-47b0e3a61b/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Finsupp/LinearCombination.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Arctan.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Bounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Real/Sqrt.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/GroupWithZero/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/Field/Basic.lean`
- `/tmp/loc_split_check/A.lean`
- `/tmp/loc_split_check/B.lean`
- `/tmp/loc_split_check/Full.lean`
- `/tmp/loc_split_check/FullAx.lean`

Pins match the manifest: project b4d606db1da5… and mathlib 25730c7c759d…. The snapshot's Ch07 Submission.lean is byte-identical to the workspace contract. Nothing in the snapshot, the DAG, the node records or any worktree declares the orthonormal-frame projection formula or the polar distance bound; the rg and regex searches found no match. The closest DAG statements, idtp_cse_rc_angle_fderiv and idtp_tdc_dlc_ld_orthonormal_partner, have different types and are not accepted, so both children are new. The names idtp_cse_etp_loc_frame_projection and idtp_cse_etp_loc_dist_bound appear nowhere: not in dag.json, nodes/, GMT/, the snapshot, or the 1467 worktree Submission.lean files. Every Mathlib lemma cited in the child proofs exists at the pinned revision with the signature used. Running lake env lean at the pins, both child types elaborate after import GMT.Ch07.Submission inside namespace GMT.Ch07 with the contract's opens. Both children are fully proved, and the parent's exact frozen type is proved from child B alone (B from A), with axioms [propext, Classical.choice, Quot.sound] only.
