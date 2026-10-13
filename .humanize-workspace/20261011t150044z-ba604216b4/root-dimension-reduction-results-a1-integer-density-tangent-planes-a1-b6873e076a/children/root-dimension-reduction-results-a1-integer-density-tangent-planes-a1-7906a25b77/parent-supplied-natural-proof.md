# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.fibre_area-a1.polar_jacobian-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.fibre_area-a1.polar_jacobian-a1.gram_det_two_plane-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 4 and 5 (Gram determinant, Lagrange's identity, Parseval in T) of the parent-supplied proof, stated for arbitrary vectors p, q in place of x̂ and g. Notation: u_i := stdOrthonormalBasis ℝ T i ∈ T for i ∈ Fin(dim T), p_T := T.starProjection, and P_T := T.orthogonalProjectionOnto : ℝ^P → T, so that (P_T v : ℝ^P) = p_T v (`Submodule.coe_orthogonalProjectionOnto_apply`).
1. (Lagrange's identity on the 2×2 index type.) Claim: for every n ∈ ℕ with n = 2 and all f, g : Fin n → ℝ, det[f_i f_j + g_i g_j]_{i,j ∈ Fin n} = (Σ_i f_i²)(Σ_i g_i²) − (Σ_i f_i g_i)². Proof: n is a variable, so substitute n = 2. Expand the determinant with `Matrix.det_fin_two` and the sums with `Fin.sum_univ_two`. The left side is (f₀² + g₀²)(f₁² + g₁²) − (f₀f₁ + g₀g₁)(f₁f₀ + g₁g₀), the right side is (f₀² + f₁²)(g₀² + g₁²) − (f₀g₀ + f₁g₁)², and both equal (f₀g₁ − f₁g₀)² (`ring`). Apply the claim with n := dim T (= 2 by hypothesis), f_i := ⟨p,u_i⟩ and g_i := ⟨q,u_i⟩; G is exactly the matrix [f_i f_j + g_i g_j]. This avoids rewriting the dependent index type Fin(dim T). Hence det G = (Σ_i ⟨p,u_i⟩²)(Σ_i ⟨q,u_i⟩²) − (Σ_i ⟨p,u_i⟩⟨q,u_i⟩)².
2. (Reduction to T.) Let v ∈ ℝ^P and i be given. Since u_i ∈ T and v − p_T v ⊥ T (`Submodule.starProjection_inner_eq_zero`), ⟨v,u_i⟩ = ⟨p_T v, u_i⟩. The inner product of T is the restriction of that of ℝ^P (`Submodule.coe_inner`), so this equals ⟨P_T v, u_i⟩_T.
3. (Parseval in T.) (u_i) is an orthonormal basis of the inner product space T. Hence for y, z ∈ T: Σ_i ⟨y,u_i⟩² = |y|² (`OrthonormalBasis.sum_sq_inner_left`), and Σ_i ⟨y,u_i⟩⟨u_i,z⟩ = ⟨y,z⟩ (`OrthonormalBasis.sum_inner_mul_inner`). By symmetry ⟨u_i,z⟩ = ⟨z,u_i⟩ (`real_inner_comm`), so Σ_i ⟨y,u_i⟩⟨z,u_i⟩ = ⟨y,z⟩.
4. (The three sums.) By steps 2 and 3 with y := P_T p and z := P_T q:
   Σ_i ⟨p,u_i⟩² = |P_T p|²;
   Σ_i ⟨q,u_i⟩² = |P_T q|²;
   Σ_i ⟨p,u_i⟩⟨q,u_i⟩ = ⟨P_T p, P_T q⟩_T.
   Norms and inner products in T are those of the underlying vectors in ℝ^P (`Submodule.norm_coe`, `Submodule.coe_inner`), and (P_T v : ℝ^P) = p_T v. So these equal |p_T p|², |p_T q|² and ⟨p_T p, p_T q⟩.
5. (Conclusion.) Substituting step 4 into step 1 gives det G = |p_T p|²·|p_T q|² − ⟨p_T p, p_T q⟩². ∎

## Key steps

1. Lagrange's identity on Fin n with n = 2: det[f_i f_j + g_i g_j] = (Σf_i²)(Σg_i²) − (Σf_i g_i)² (subst n, Matrix.det_fin_two, Fin.sum_univ_two, ring); apply with n = dim T.
2. ⟨v,u_i⟩ = ⟨p_T v, u_i⟩ = ⟨P_T v, u_i⟩_T because v − p_T v ⊥ T ∋ u_i.
3. Parseval in T (sum_sq_inner_left, sum_inner_mul_inner) gives Σ⟨p,u_i⟩² = |p_T p|², Σ⟨q,u_i⟩² = |p_T q|², Σ⟨p,u_i⟩⟨q,u_i⟩ = ⟨p_T p, p_T q⟩.
4. Substitute into Lagrange's identity.

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
