# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.density_locally_constant-a1.light_disc-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.density_locally_constant-a1.light_disc-a1.orthonormal_partner-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 of the supplied proof of idtp_tdc_dlc_light_disc (Gram–Schmidt inside the plane Q), with the details written out.
Hypotheses: finrank ℝ Q = 2, z ∈ Q, ‖z‖ = 1. All inner products are real, so ⟨a, b⟩ = ⟨b, a⟩.
1. z ≠ 0, since ‖0‖ = 0 ≠ 1 = ‖z‖.
2. (A vector of Q off the line through z.) The line ℝ∙z = span{z} has finrank 1 (finrank_span_singleton, as z ≠ 0). If Q ≤ ℝ∙z, then finrank Q ≤ finrank (ℝ∙z) (Submodule.finrank_mono; ℝ∙z is finite-dimensional), i.e. 2 ≤ 1, which is false. Hence Q ⊄ ℝ∙z, so there is u ∈ Q with u ∉ ℝ∙z (IsConcreteLE.not_le_iff_exists).
3. (Orthogonalize.) Put v := u − ⟨z, u⟩ z. Then v ∈ Q, because u ∈ Q, z ∈ Q and Q is a subspace.
   - v ≠ 0: otherwise u = ⟨z, u⟩ z ∈ ℝ∙z, contradicting step 2.
   - ⟨z, v⟩ = ⟨z, u⟩ − ⟨z, u⟩⟨z, z⟩ = ⟨z, u⟩ − ⟨z, u⟩‖z‖² = ⟨z, u⟩ − ⟨z, u⟩ = 0.
4. (Normalize.) Put e := ‖v‖⁻¹ • v. As v ≠ 0, ‖v‖ > 0.
   - e ∈ Q, since v ∈ Q.
   - ‖e‖ = ‖v‖⁻¹ ‖v‖ = 1.
   - ⟨z, e⟩ = ‖v‖⁻¹ ⟨z, v⟩ = 0, and hence also ⟨e, z⟩ = 0.
5. (span{z, e} = Q.) The family (z, e) is orthonormal: ⟨z, z⟩ = ‖z‖² = 1, ⟨e, e⟩ = ‖e‖² = 1 and ⟨z, e⟩ = ⟨e, z⟩ = 0. So it is linearly independent (Orthonormal.linearIndependent), and span{z, e} has finrank 2 (finrank_span_eq_card). Since z ∈ Q and e ∈ Q, span{z, e} ≤ Q (Submodule.span_le). Q is finite-dimensional and both have finrank 2, so span{z, e} = Q (Submodule.eq_of_le_of_finrank_eq).
6. (Expansion.) Let w ∈ Q and put d := w − ⟨w, z⟩ z − ⟨w, e⟩ e. Then d ∈ Q, because w, z, e ∈ Q. Using ⟨z, z⟩ = ⟨e, e⟩ = 1 and ⟨z, e⟩ = ⟨e, z⟩ = 0:
   - ⟨d, z⟩ = ⟨w, z⟩ − ⟨w, z⟩⟨z, z⟩ − ⟨w, e⟩⟨e, z⟩ = ⟨w, z⟩ − ⟨w, z⟩ − 0 = 0;
   - ⟨d, e⟩ = ⟨w, e⟩ − ⟨w, z⟩⟨z, e⟩ − ⟨w, e⟩⟨e, e⟩ = ⟨w, e⟩ − 0 − ⟨w, e⟩ = 0.
7. By step 5, d ∈ span{z, e}, so d = a z + b e for some a, b ∈ ℝ (Submodule.mem_span_range_iff_exists_fun for the family (z, e)). Then ⟨d, d⟩ = a⟨d, z⟩ + b⟨d, e⟩ = 0 by step 6, so d = 0 (inner_self_eq_zero). Therefore w = ⟨w, z⟩ z + ⟨w, e⟩ e.
8. The vector e of step 4 has e ∈ Q, ‖e‖ = 1 and ⟨z, e⟩ = 0, and by step 7 every w ∈ Q satisfies w = ⟨w, z⟩ z + ⟨w, e⟩ e. ∎

## Key steps

1. finrank Q = 2 > 1 = finrank (ℝ∙z), so some u ∈ Q lies off the line ℝ∙z.
2. v := u − ⟨z,u⟩z is a nonzero vector of Q orthogonal to z, and e := ‖v‖⁻¹v is a unit vector of Q orthogonal to z.
3. (z, e) is orthonormal, so span{z, e} ≤ Q has finrank 2 and equals Q.
4. For w ∈ Q, d := w − ⟨w,z⟩z − ⟨w,e⟩e lies in span{z, e} and is orthogonal to z and e, so ⟨d,d⟩ = 0 and d = 0.

## Reference use

### local-project

Queries:
- `cat nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-28222a0d38/{parent-child-handoff.json,parent-supplied-plan.md,parent-supplied-natural-proof.md}`
- `python3 scan of dag.json: lean_statement/status/depends_on of idtp_cone_constant_density_planar, idtp_tdc_arc_continuation, idtp_tdc_cone_dilation, idtp_tdc_dlc_normalize_dist_le, idtp_tdc_dlc_subspace_eq_of_inter_ball_eq, idtp_tdc_dlc_light_disc, and the ancestor chain's depends_on`
- `python3 scan of dag.json lean_statements for 'inner ℝ z e = 0', 'Real.cos φ • z + Real.sin φ • e', 'Real.cos', 'arccos', 'Orthonormal', '‖y‖⁻¹ • y', 's⁻¹ •', 'IsConeCurrent C → ∀ s', 'finrank ℝ Q = 2 → z ∈ Q'`
- `python3 scan of dag.json for lean_name prefix idtp_tdc_dlc_ld and the five proposed names; scan of accepted depth>=5 nodes whose natural proofs cite ancestor-level prerequisites`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp ... GMT/Ch07/Submission.lean; cat manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD`
- `rg -n "theorem one_sub_sq_div_two_le_cos|theorem mul_le_sin |theorem cos_arccos|theorem sin_arccos|theorem arccos_nonneg|theorem arccos_le_pi|theorem pi_le_four|theorem cos_two_mul_eq_one_sub|theorem sqrt_sq_eq_abs|theorem sin_nonneg_of_nonneg_of_le_pi" mathlib/Mathlib`
- `rg -n "theorem finrank_span_singleton|theorem finrank_mono|theorem eq_of_le_of_finrank_eq|theorem Orthonormal.linearIndependent|theorem finrank_span_eq_card|theorem norm_add_sq_real|theorem norm_sub_sq_real|theorem real_inner_self_eq_norm_sq|theorem inner_self_eq_zero|theorem smul_mem_iff|theorem not_le_iff_exists" mathlib/Mathlib`
- `rg -n "one_sub_sq_div_two_le_cos|finrank_mono|mem_span_range_iff_exists_fun|smul_inv_smul₀|IsConcreteLE" mathlib/Mathlib`
- `rg -n "idtp_tdc_dlc_ld|idtp_tdc|orthonormal_partner|arc_point_bounds|unit_vector_angle|cone_scale_piece|piece_mass_bound" project mathlib/Mathlib`
- `git show 4b8c28a1:GMT/Ch07/Submission.lean (layout of the accepted Submission.idtp_tdc_cone_dilation)`
- `lake env lean /tmp/ld-split-a1/Names.lean; lake env lean /tmp/ld-split-a1/gen/Stmts.lean; lake env lean /tmp/ld-split-a1/gen/Assembly.lean; lake env lean /tmp/ld-split-a1/gen/Children.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-28222a0d38/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-28222a0d38/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-28222a0d38/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Bounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Inverse.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Complex/Trigonometric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Real/Sqrt.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Module/Submodule/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/GroupWithZero/Action/Units.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Atoms.lean`
- `/tmp/ld-split-a1/Names.lean`
- `/tmp/ld-split-a1/gen/Stmts.lean`
- `/tmp/ld-split-a1/gen/Assembly.lean`
- `/tmp/ld-split-a1/gen/Children.lean`

Pins and contract:
- manifest.json pins project b4d606db and mathlib 25730c7c. The workspace HEAD and .lake mathlib match these pins.
- The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.
- Accepted declarations sit in namespace GMT.Ch07 as `theorem Submission.X`, as in the accepted cone_dilation commit 4b8c28a1.

Reuse:
- No DAG node, snapshot file or workspace source contains any of the five proposed idtp_tdc_dlc_ld_* names (rg: no match).
- No accepted DAG declaration has any child's exact type.
- idtp_tdc_acont_great_circle implies arc_point_bounds, but it is still decomposing, so it is not reused.
- Accepted depth-5 and depth-6 nodes, e.g. codim1_rdo_dg_rc_ball_cone_measurable, already cite ancestor-level prerequisites. So the children may cite idtp_tdc_cone_dilation (accepted) and idtp_cone_constant_density_planar, as the supplied proof does.

Mathlib snapshot: it contains every lemma the child proofs cite. Examples: Real.one_sub_sq_div_two_le_cos (Bounds.lean:124), Real.mul_le_sin (Bounds.lean:83), Real.cos_arccos/sin_arccos/arccos_nonneg/arccos_le_pi (Inverse.lean), Real.pi_le_four, Real.cos_two_mul_eq_one_sub, Real.sqrt_sq_eq_abs, finrank_span_singleton, Submodule.finrank_mono, Submodule.eq_of_le_of_finrank_eq, Orthonormal.linearIndependent, finrank_span_eq_card, norm_add_sq_real, norm_sub_sq_real, inner_self_eq_zero, Submodule.smul_mem_iff, smul_inv_smul₀ and IsConcreteLE.not_le_iff_exists.

Lean checks:
- All five lean_statements elaborate after import GMT.Ch07.Submission.
- A hypothesis-only assembly derives the exact frozen selected type from the five child types and the frozen types of idtp_cone_constant_density_planar, idtp_tdc_arc_continuation and idtp_tdc_dlc_normalize_dist_le.
- Every child is fully proved in Lean.
- All of these use only the axioms propext, Classical.choice and Quot.sound.
- An independent reviewer re-ran the checks and confirmed byte-exactness against dag.json.
