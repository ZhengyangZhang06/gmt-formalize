# Parent-supplied natural-language proof

- Parent DAG node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.orientation_pushforward-a1`
- Child DAG node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.orientation_pushforward-a1.gram_schmidt_frame-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 3–5 of the parent proof (Gram–Schmidt, G = AᵀA, and the upper-triangular determinant bound), with the details filled in. This is Simon 6.3.4–3.5's expansion in an orthonormal basis of the image space, with the basis chosen by Gram–Schmidt.

Notation: ⟨·,·⟩ and |·| are the Euclidean inner product and norm of ℝ^P.

1. The subspace W.
   - Let W := span{v_1, …, v_n} ⊆ ℝ^P with the restricted inner product, a finite-dimensional inner product space. Let ι_W : W → ℝ^P be the inclusion.
   - Since v is linearly independent, dim W = n = card(Fin n) (finrank_span_eq_card).
   - Each v_b lies in W. Let w_b ∈ W be v_b regarded as an element of W, so ι_W(w_b) = v_b.
   - w is linearly independent in W, because ι_W ∘ w = v is linearly independent (LinearIndependent.of_comp).
   - w spans W. The map ι_W sends span(w) onto span(ι_W ∘ w) = span v = W = ι_W(W) (Submodule.map_span, Set.range_comp, Submodule.map_top, Submodule.range_subtype). The induced map on submodules is injective (Submodule.map_injective_of_injective), so span(w) = W, the top submodule of W.

2. Gram–Schmidt. Apply Gram–Schmidt orthonormalisation in W to w, in the order of Fin n (Mathlib InnerProductSpace.gramSchmidtOrthonormalBasis, with the hypothesis finrank W = card(Fin n) from step 1).
   - This yields an orthonormal basis b = (b_1, …, b_n) of W.
   - Its coefficient matrix for w is upper triangular: ⟨b_a, w_c⟩ = 0 whenever c < a (gramSchmidtOrthonormalBasis_inv_triangular).
   - Consequently the basis determinant of the family w with respect to b is the product of the diagonal entries: det_b(w) = ∏_a ⟨b_a, w_a⟩ (gramSchmidtOrthonormalBasis_det; det_b is Module.Basis.det of b.toBasis).

3. The frame σ. Define σ_a := ι_W(b_a) ∈ ℝ^P.
   - Norms and inner products of elements of W are computed in ℝ^P, so |σ_a| = 1 and ⟨σ_a, σ_c⟩ = 0 for a ≠ c. Hence σ is orthonormal.
   - b is a basis, so span b = W. Therefore span σ = span(ι_W ∘ b) = ι_W(span b) = ι_W(W) = W = span v (Set.range_comp, Submodule.map_span, Submodule.map_top, Submodule.range_subtype).

4. The coefficient matrix.
   - For an orthonormal basis, the a-th coordinate of w_c is ⟨b_a, w_c⟩ (OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply).
   - Inner products in W are those of ℝ^P, so ⟨b_a, w_c⟩ = ⟨σ_a, v_c⟩ = A_{ac}. Thus A is the matrix of the family w in the basis b (Module.Basis.toMatrix_apply).
   - Hence det A = det_b(w) (Module.Basis.det_apply) = ∏_a ⟨σ_a, v_a⟩ by step 2.

5. (i) Gram identity.
   - Fix a and c. Parseval's identity for the orthonormal basis b of W (OrthonormalBasis.sum_inner_mul_inner) gives ⟨v_a, v_c⟩ = ⟨w_a, w_c⟩ = Σ_k ⟨w_a, b_k⟩⟨b_k, w_c⟩.
   - By symmetry of the real inner product (real_inner_comm), Σ_k ⟨w_a, b_k⟩⟨b_k, w_c⟩ = Σ_k ⟨σ_k, v_a⟩⟨σ_k, v_c⟩ = Σ_k A_{ka} A_{kc} = (AᵀA)_{ac}.
   - So (⟨v_a, v_c⟩)_{a,c} = AᵀA, and det(⟨v_a, v_c⟩) = det(Aᵀ)·det(A) = (det A)² (Matrix.det_mul, Matrix.det_transpose).

6. (ii) det A ≠ 0. By step 4, det A = det_b(w). By step 1, w is linearly independent and spans W, so det_b(w) is a unit (Module.Basis.is_basis_iff_det), hence nonzero.

7. (iii) The bound.
   - By step 4 and multiplicativity of the absolute value (Finset.abs_prod), |det A| = ∏_a |⟨σ_a, v_a⟩|.
   - For each a, Cauchy–Schwarz and |σ_a| = 1 give |⟨σ_a, v_a⟩| ≤ |σ_a|·|v_a| = |v_a| (abs_real_inner_le_norm).
   - All factors are nonnegative, so the products compare factor by factor (Finset.prod_le_prod₀): |det A| ≤ ∏_a |v_a|.

8. The case n = 0 is covered by steps 1–7, which never assume n > 0. All families are empty, W = {0}, A is the empty matrix with det A = 1 ≠ 0, det(⟨v_a, v_b⟩) = 1 = 1², and the empty product is 1. ∎

Formalization notes (everything cited, including gramSchmidtOrthonormalBasis and gramSchmidtOrthonormalBasis_det, is available after import GMT.Ch07.Submission):
- Take W := Submodule.span ℝ (Set.range v), w j := ⟨v j, Submodule.subset_span ⟨j, rfl⟩⟩ and b := InnerProductSpace.gramSchmidtOrthonormalBasis (finrank_span_eq_card hv) w. Use fun i => (b i : Euclid P) as σ.
- Mathlib's GramMatrix and NormDet files are not imported. So prove the Gram identity entrywise with Matrix.mul_apply, Matrix.transpose_apply and b.sum_inner_mul_inner (w i) (w j), after simp only [Submodule.coe_inner] and real_inner_comm.
- For (ii), use (Module.Basis.is_basis_iff_det b.toBasis).mp ⟨hw, hspan_w⟩, not basisOfLinearIndependentOfCardEqFinrank, which needs a Nonempty index.
- For (iii), use Finset.prod_le_prod₀. Plain Finset.prod_le_prod needs MulLeftMono and fails for ℝ.

## Key steps

1. W := span v has dimension n; v regarded in W is a linearly independent spanning family w.
2. Gram–Schmidt in W gives an orthonormal basis b with det_b(w) = ∏⟨b_a, w_a⟩ (upper-triangular coefficients).
3. σ := b regarded in ℝ^P is orthonormal, with span σ = W = span v.
4. A_{ac} = ⟨σ_a, v_c⟩ is the coefficient matrix of w in b, so det A = det_b(w) = ∏⟨σ_a, v_a⟩.
5. Parseval gives G(v) = AᵀA, hence det G(v) = (det A)².
6. det A = det_b(w) is a unit because w is a basis of W, so det A ≠ 0.
7. |det A| = ∏|⟨σ_a, v_a⟩| ≤ ∏|v_a| by Cauchy–Schwarz and |σ_a| = 1.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (project b4d606d, mathlib 25730c7c)`
- `diff -q <snapshot>/project/GMT/Ch07/Submission.lean GMT/Ch07/Submission.lean (identical)`
- `rg -n 'theorem gramSchmidtOrthonormalBasis_det|theorem normDet_sq_eq_det_gram|theorem gram_eq_conjTranspose_mul|theorem AlternatingMap.eq_smul_basis_det|theorem det_toMatrix|theorem adjoint_inner_right|theorem is_basis_iff_det|theorem finrank_span_eq_card|theorem sum_inner_mul_inner|lemma prod_le_prod₀' <snapshot>/mathlib/Mathlib`
- `rg -n -i 'hadamard.*inequality|det_le_prod_norm|abs_det_le_prod' <snapshot>/mathlib/Mathlib (no match: Mathlib has no Hadamard determinant inequality)`
- `rg -n 'gramSchmidt|stdOrthonormalBasis|IsUnitOrientationOf|normDet' <snapshot>/project/GMT --glob '*.lean' (only contract definitions; no prior proof of this statement)`
- `rg -n 'def compContinuousLinearMapCLM' and 'gramSchmidtOrthonormalBasis(_inv_triangular)' in the snapshot Mathlib`
- `grep -n theorem/def in Mathlib/Analysis/InnerProductSpace/{NormDet,GramMatrix,GramSchmidtOrtho}.lean`
- `python3 -I dag.json scans: lean_name/lean_statement for dgoj_*, covectorEuclideanNorm_gram_bounds, stdOrthonormalBasis, LinearIndependent+Orthonormal, gramSchmidt; collision checks for dpf_det_gram_stdOrthonormalBasis_eq and dpf_exists_orthonormal_frame_det_gram (no hits)`
- `grep -l <new names> nodes/*/*.json (no hits); git grep over 1083 branch tips -- GMT (no hits)`
- `git show 73310ec:GMT/Ch07/Submission.lean (accepted proof of Submission.dgoj_covector_eq_det_mul_of_mem_span)`
- `read controller /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_existing_lean_name_problem, child materialization by lean_name, _install_parent_supplied_child_handoff, _overlay_accepted_children) and leaf_verification.py (single-theorem leaf delta, no import)`
- `lake env lean /tmp/dpf-orient-split/Avail.lean and Avail2.lean (gramSchmidtOrthonormalBasis(_det), LinearMap.adjoint, LinearMap.det_toMatrix available; LinearMap.normDet_sq_eq_det_gram, Matrix.gram_eq_conjTranspose_mul, Matrix.det_gram_ne_zero_iff_linearIndependent NOT available after import GMT.Ch07.Submission)`
- `lake env lean /tmp/dpf-orient-split/{Types,Assembly,Child1,Child2,Full}.lean and /tmp/dpf-orient-split/final/Final.lean (#print axioms: propext, Classical.choice, Quot.sound)`
- `sed -n 780,835p book/sources/chapter-06-source.txt (Simon 6.3.4-3.7)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/GramSchmidtOrtho.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/GramMatrix.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/BigOperators/GroupWithZero/Finset.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-orientati-f9454fcfd5/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/parent_verification.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-06-source.txt`
- `/tmp/dpf-orient-split/final/Final.lean`
- `/tmp/dpf-orient-split/Child1.lean`
- `/tmp/dpf-orient-split/Child2.lean`
- `/tmp/dpf-orient-split/Assembly.lean`

The pinned local snapshot (project b4d606d, mathlib 25730c7c) does not prove this statement or either new child. Snapshot Ch07 Submission is identical to the workspace one and contains only contract definitions. One required step already exists as the comparator-accepted Submission.dgoj_covector_eq_det_mul_of_mem_span (candidate commit 73310ec). Its frozen type is byte-identical, so it is reused rather than re-proved.

Library facts in the Submission's import closure:
- gramSchmidtOrthonormalBasis and gramSchmidtOrthonormalBasis_det (GramSchmidtOrtho.lean:318, 374);
- LinearMap.adjoint and adjoint_inner_right (Adjoint.lean:592);
- LinearMap.det_toMatrix and Module.Basis.is_basis_iff_det (Determinant.lean:206, 625);
- AlternatingMap.eq_smul_basis_det (Determinant.lean:650);
- OrthonormalBasis.sum_inner_mul_inner (PiL2.lean:506);
- finrank_span_eq_card (Constructions.lean:463);
- Finset.prod_le_prod₀ (BigOperators/GroupWithZero/Finset.lean:38).

Not available after import GMT.Ch07.Submission, so the child proofs avoid them:
- LinearMap.normDet_sq_eq_det_gram (NormDet.lean:303);
- Matrix.gram_eq_conjTranspose_mul (GramMatrix.lean:130).

Mathlib has no Hadamard determinant inequality (rg: no match), so the bound J ≤ ‖L‖^n uses the Gram–Schmidt upper-triangular determinant. Leaf candidates may insert only one theorem without imports. Both new children were proved in exactly that form in scratch Lean, and the parent assembly compiles from the three child types. Final.lean (both children, the accepted text of (c) and the assembly) depends only on propext, Classical.choice and Quot.sound.
