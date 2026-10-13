# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.fibre_area-a1.polar_jacobian-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.fibre_area-a1.polar_jacobian-a1.proj_norm_sq-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1 (F1) of the parent-supplied proof. Notation: α := ⟨x,a⟩, β := ⟨x,e⟩, π := Q.starProjection.
1. (Orthonormality.) ⟨a,a⟩ = |a|² = 1 and ⟨e,e⟩ = |e|² = 1 (`real_inner_self_eq_norm_sq`), and ⟨e,a⟩ = ⟨a,e⟩ = 0 (`real_inner_comm`). So the family (a, e), indexed by Fin 2 as ![a, e], is orthonormal (`orthonormal_iff_ite`, checking the four index pairs). Hence it is linearly independent (`Orthonormal.linearIndependent`).
2. (span{a,e} = Q.) span{a,e} ⊆ Q because a, e ∈ Q (`Submodule.span_le`). The finite dimension of span{a,e} is 2, the size of the linearly independent family (`finrank_span_eq_card`), which equals dim Q. So span{a,e} = Q (`Submodule.eq_of_le_of_finrank_eq`).
3. (πx = αa + βe.) Put w₀ := αa + βe ∈ Q (Q is a subspace containing a and e). Let w ∈ Q. By step 2, w = c₀a + c₁e for some reals c₀, c₁ (`Submodule.mem_span_range_iff_exists_fun`, `Fin.sum_univ_two`). Then ⟨x − w₀, a⟩ = α − α⟨a,a⟩ − β⟨e,a⟩ = α − α − 0 = 0. Likewise ⟨x − w₀, e⟩ = β − α⟨a,e⟩ − β⟨e,e⟩ = β − 0 − β = 0. Hence ⟨x − w₀, w⟩ = c₀·0 + c₁·0 = 0. By the characterization of the orthogonal projection (`Submodule.eq_starProjection_of_mem_of_inner_eq_zero`: if w₀ ∈ Q and x − w₀ ⊥ Q, then πx = w₀), πx = w₀.
4. (Norm.) Write |πx|² = ⟨w₀, w₀⟩ (`real_inner_self_eq_norm_sq`). Expand bilinearly: α²⟨a,a⟩ + αβ⟨a,e⟩ + βα⟨e,a⟩ + β²⟨e,e⟩ = α² + β², by step 1. So |Q.starProjection x|² = ⟨x,a⟩² + ⟨x,e⟩². ∎

## Key steps

1. (a, e) is orthonormal, hence linearly independent; span{a,e} ⊆ Q has dimension 2 = dim Q, so span{a,e} = Q.
2. w₀ := ⟨x,a⟩a + ⟨x,e⟩e ∈ Q and x − w₀ ⊥ a, e, hence ⊥ Q; so Q.starProjection x = w₀ (eq_starProjection_of_mem_of_inner_eq_zero).
3. |w₀|² = ⟨x,a⟩² + ⟨x,e⟩² by bilinear expansion and orthonormality.

## Reference use

### local-project

Queries:
- `python3 over dag.json nodes: ids under ...cone_sector_endpoint_density-a1.fibre_area-a1 (siblings area_formula_prod, polar_jacobian, sector_open_smooth) and lean_names containing 'idtp_cse', 'polar' or 'gram' (dpf_det_gram_stdOrthonormalBasis_eq accepted; idtp_cse_rc_angle_fderiv, idtp_cse_fc_planar_fibre_geometry, idtp_cse_fc_jacobian_upper still decomposing)`
- `grep -c idtp_cse_fa_pj_ dag.json (0); grep -rl 'idtp_cse_fa_pj_polar_fderiv_apply|idtp_cse_fa_pj_gram_det_two_plane|idtp_cse_fa_pj_starProjection_norm_sq|idtp_cse_fa_pj_' .humanize GMT (no match); rg -n 'idtp_cse_fa_pj_|polar_gram|gram_det_two_plane' local-references/123e8435b4a2469b/project (no match); git grep idtp_cse_fa_pj_ on this node's and the parent's proof/dispatch branches (no match)`
- `rg -n 'theorem hasStrictFDerivAt_norm_sq|theorem HasFDerivAt.sqrt|theorem hasFDerivAt_inv |theorem HasFDerivAt.mul |theorem HasFDerivAt.arctan|nonrec theorem HasFDerivAt.prodMk|theorem det_fin_two |protected theorem sum_inner_mul_inner|theorem sum_sq_inner_left|theorem starProjection_inner_eq_zero|theorem eq_starProjection_of_mem_of_inner_eq_zero|theorem inner_starProjection_left_eq_right|lemma coe_orthogonalProjectionOnto_apply|theorem norm_coe \[Ring|theorem eq_of_le_of_finrank_eq|theorem finrank_span_eq_card|theorem orthonormal_iff_ite|theorem starProjection_eq_self_iff' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -n 'mem_span_range_iff_exists_fun|theorem Submodule.coe_inner' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `grep -rn 'HasFDerivAt (‖·‖)|hasStrictFDerivAt_norm\b|HasFDerivAt.norm\b|fderiv_norm\b|HasFDerivAt.inv\b|HasFDerivAt.div\b' .lake/packages/mathlib/Mathlib (no closed-form fderiv of the Euclidean norm and no fderiv quotient rule at the pin; hence sqrt ∘ norm_sq and inverse + product rules)`
- `diff GMT/Ch07/Submission.lean against local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean and against git show 22aa3aa64ed3:GMT/Ch07/Submission.lean (identical); git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD`
- `lake env lean /tmp/pj-decomp-4f2a/check/{Stmts,Parent,C1,C2,C3,Full}.lean and /tmp/pj-review-9c1d/{ElabC1,ElabC2,ElabC3,ElabParent,C1,C2,C3,Parent,Full}.lean (+ #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-b6873e076a/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-b6873e076a/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-2d6a9d83f4/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-2d6a9d83f4/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/Sqrt.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/ArctanDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Subspace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Submodule.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Finsupp/LinearCombination.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Norm.lean`
- `/tmp/pj-decomp-4f2a/check/Stmts.lean`
- `/tmp/pj-decomp-4f2a/check/Parent.lean`
- `/tmp/pj-decomp-4f2a/check/C1.lean`
- `/tmp/pj-decomp-4f2a/check/C2.lean`
- `/tmp/pj-decomp-4f2a/check/C3.lean`
- `/tmp/pj-decomp-4f2a/check/Full.lean`
- `/tmp/pj-review-9c1d/Full.lean`
- `/tmp/pj-review-9c1d/Parent.lean`
- `/tmp/pj-review-9c1d/num_check.py`

The pins match. The workspace Submission.lean, the snapshot's project/GMT/Ch07/Submission.lean and the node's proof base 22aa3aa64e are byte-identical. Mathlib is 25730c7c, equal to the snapshot's mathlib_commit, and SimonGMT is 2b36630.

There is nothing to reuse. No accepted DAG declaration gives the polar-map derivative, the 2-plane Gram determinant or the projection-norm identity:
- dpf_det_gram_stdOrthonormalBasis_eq applies only to L : Euclid P →L Euclid P, not to the ℝ × ℝ-valued Gram matrix.
- The cousin idtp_cse_rc_angle_fderiv is still decomposing and has a different, conjunctive type.

Every Mathlib name cited in the child proofs exists at the pin, located by rg in the snapshot. The Mathlib at the pin has no closed-form fderiv of the Euclidean norm and no fderiv quotient rule, so child 1 goes through sqrt ∘ norm_sq and the inverse and product rules. The idtp_cse_fa_pj_* names are unreserved.

Kernel checks, all with only propext, Classical.choice and Quot.sound:
- All three child types elaborate verbatim.
- The frozen parent type, string-identical to the handoff and dag.json, is proved from the three child types.
- Each child is fully proved.
- Full.lean proves Submission.idtp_cse_fa_polar_gram_jacobian outright.

An independent reviewer reproduced all of this and returned ACCEPT.
