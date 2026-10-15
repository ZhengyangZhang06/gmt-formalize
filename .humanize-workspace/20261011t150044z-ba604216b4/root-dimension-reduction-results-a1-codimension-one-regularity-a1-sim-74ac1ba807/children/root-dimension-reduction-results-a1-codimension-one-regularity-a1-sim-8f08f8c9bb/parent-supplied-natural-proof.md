# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.stability-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.stability-a1.det_second_order-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. The expansion det(I + E) = 1 + tr E + ½((tr E)² − tr(E²)) + O(|E|³) used in parent step (1c) for the Gram matrix b(t) = I + tc + t²d, made uniform in the entries. No dependencies.

Notation. For an n×n real matrix A let p_A := det(1 + 𝐗·A) ∈ ℝ[𝐗] (the entries of A are viewed as constant polynomials) and let e_k(A) be the coefficient of 𝐗^k in p_A. By Matrix.coeff_det_one_add_X_smul_eq_sum_minors, e_k(A) is the sum of the determinants of the k×k principal submatrices of A.

1. (Low coefficients and degree.) e_0(A) = 1 (the only 0-element subset gives the empty determinant 1), e_1(A) = tr A (Matrix.coeff_det_one_add_X_smul_one), and e_k(A) = 0 for k > n (there is no k-element subset of an n-element set), so deg p_A ≤ n.

2. (Second coefficient: e_2(A) = ((tr A)² − tr(A·A))/2.) Since 𝐗·A commutes with itself, (1 + 𝐗A)(1 − 𝐗A) = 1 − 𝐗²(A·A), hence p_A·p_{−A} = det(1 − 𝐗²(A·A)) (Matrix.det_mul). Compare the coefficients of 𝐗²:
 left side: e_0(A)e_2(−A) + e_1(A)e_1(−A) + e_2(A)e_0(−A) = 2e_2(A) − (tr A)², because e_1(−A) = −tr A and e_2(−A) = e_2(A) (every 2×2 principal submatrix N of −A is −N' for the corresponding submatrix N' of A, and det(−N') = (−1)² det N');
 right side: put B := A·A and q := p_B. Applying the ring homomorphism 'substitute −𝐗² for 𝐗' entrywise (RingHom.map_det) shows det(1 − 𝐗²B) = q(−𝐗²). Writing q = 1 + (tr B)𝐗 + 𝐗²r (Matrix.det_one_add_X_smul), q(−𝐗²) = 1 − (tr B)𝐗² + 𝐗⁴·r(−𝐗²), whose 𝐗²-coefficient is −tr B.
 Hence 2e_2(A) − (tr A)² = −tr(A·A).

3. (Crude bound for determinants.) If N is a k×k real matrix with |N_ij| ≤ b, then |det N| ≤ k!·b^k: the Leibniz formula writes det N as a sum of k! terms ±∏_i N_{σ(i)i}, each of absolute value ≤ b^k.

4. (Constants.) Put κ' := max(κ, 0), b := max(1, 2κ'), β := 2^N·N!·b^N and C := 3N²κ'² + N·β (≥ 0).

5. (Coefficient bound.) Let n ≤ N and let A be an n×n matrix with |A_ij| ≤ b. A k×k principal submatrix (k ≤ n; reindex its index set to Fin k by an equivalence, which does not change the determinant) has determinant of absolute value ≤ k!·b^k ≤ n!·b^n (b ≥ 1), and there are binom(n,k) ≤ 2^n ≤ 2^N of them. Hence |e_k(A)| ≤ 2^N·N!·b^N = β for every k.

6. (Expansion.) Fix n ≤ N, X, Y with entries bounded by κ (hence by κ'), and |t| ≤ 1. Put A := X + tY. Then I + tX + t²Y = I + tA and |A_ij| ≤ κ' + |t|κ' ≤ 2κ' ≤ b. Evaluating p_A at t (RingHom.map_det with the evaluation homomorphism) and using deg p_A < n + 3:
 det(I + tX + t²Y) = Σ_{k<n+3} e_k(A)t^k = 1 + t·tr A + t²e_2(A) + Σ_{i<n} e_{i+3}(A)t^{i+3}.
 By step 5 and |t|^{i+3} ≤ |t|³, the last sum has absolute value ≤ n·β|t|³ ≤ N·β|t|³.

7. (Comparison of the low-order terms.) tr A = tr X + t·tr Y and tr(A·A) = tr(X·X) + t(tr(X·Y) + tr(Y·X)) + t²tr(Y·Y). Using step 2,
 1 + t·tr A + t²e_2(A) − [1 + t·tr X + t²(tr Y + ((tr X)² − tr(X·X))/2)] = t³·[(2·tr X·tr Y − tr(X·Y) − tr(Y·X))/2 + t((tr Y)² − tr(Y·Y))/2].
 Each trace of a single matrix is a sum of n entries, so |tr X|, |tr Y| ≤ nκ'; each trace of a product is a sum of n² products of entries, so |tr(X·Y)|, |tr(Y·X)|, |tr(Y·Y)| ≤ n²κ'². With |t| ≤ 1 and n ≤ N the bracket has absolute value ≤ 2N²κ'² + N²κ'² = 3N²κ'².

8. (Conclusion.) Combining steps 6 and 7: |det(I + tX + t²Y) − (1 + t·tr X + t²(tr Y + ((tr X)² − tr(X·X))/2))| ≤ N·β|t|³ + 3N²κ'²|t|³ = C|t|³. ∎

## Key steps

1. det(I + tX + t²Y) = p_A(t) with A = X + tY and p_A = det(1 + 𝐗A), whose 𝐗^k-coefficient e_k(A) is the sum of the k×k principal minors.
2. e_0 = 1, e_1 = tr A, and e_2 = ((tr A)² − tr(A²))/2 from comparing 𝐗²-coefficients in det(1 + 𝐗A)·det(1 − 𝐗A) = det(1 − 𝐗²A²).
3. Leibniz bound |e_k(A)| ≤ 2^N·N!·b^N controls the cubic remainder; expanding tr A, tr(A²) in t costs at most 3N²κ'²|t|³.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; sha256sum local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `sed -n 1,457p GMT/Ch07/Submission.lean (Euclid, IsEmbeddedSubmanifold, tangentSpace, μHE, main_theorem placeholder)`
- `python3 scans of dag.json: selected node, its depends_on (area_formula, lipschitz_approx, smooth_charts, chart_tangent_space, locally_closed) with statuses and frozen lean_statements; hypercone_plane decomposition-v1.json (reused chart_tangent_space entry)`
- `rg -c codim1_hcp_stab_ local-references/123e8435b4a2469b/project lake-packages-25730c7c/simongmt GMT runs/.../dag.json (no match)`
- `rg -n -i 'second.?variation|stability|jacobian' lake-packages-25730c7c/simongmt/Poincare -t lean`
- `rg -n 'theorem coeff_det_one_add_X_smul_eq_sum_minors|exists_contDiff_support_eq_eq_one_iff|det_eq_prod_eigenvalues|ContDiffAt.isSymmSndFDerivAt|trace_eq_sum_inner|exists_compact_between|tendsto_integral_filter_of_dominated_convergence|setIntegral_eq_of_subset_of_forall_sdiff_eq_zero|IntegrableOn.of_forall_sdiff_eq_zero|norm_image_sub_le_of_norm_fderiv_le|det_nonneg' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `lean #check after import GMT.Ch07.Submission (/tmp/stab-decomp-q7/Avail*.lean): Matrix.PosSemidef.det_nonneg, Matrix.posSemidef_conjTranspose_mul_self, Matrix.det_le, Poincare.SimonGMT.Chapter08.quadraticMatrixDeterminant, LinearMap.normDet (absent); LinearMap.IsSymmetric.det_eq_prod_eigenvalues, Matrix.coeff_det_one_add_X_smul_eq_sum_minors, LinearMap.trace_eq_sum_inner, exists_contDiff_support_eq_eq_one_iff, ContDiffAt.isSymmSndFDerivAt, Submodule.finrank_add_inf_finrank_orthogonal (present)`
- `git show --stat d626082a69a0 (accepted chart_tangentSpace_eq_range_fderiv: proof appended to GMT/Ch07/Submission.lean, imports unchanged)`
- `sed -n 1385,1440p; 1700,1960p; 6640,6728p /runtime/flows/gmt-claude-252c8df06c56/_recursive_lean/runtime.py (_decompose depth gate, _solve_children name reuse, _existing_lean_name_problem)`
- `lean -DautoImplicit=false /tmp/stab-decomp-q7/{Assembly,Parse,AProof,BProof,CProof,D1Proof,D2Proof,EProof,FProof,IProof,GProof,H1Proof,H2Proof,Full}.lean with LEAN_PATH = workspace .lake/build/lib/lean plus every package's .lake/build/lib/lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-74ac1ba807/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-b5d5990773/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/JacobianBounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/AppendixB/SimonsInequalities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/Charpoly/Coeff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Spectrum.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/LocallyCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Matrix/PosDef.lean`
- `/runtime/flows/gmt-claude-252c8df06c56/_recursive_lean/runtime.py`
- `/tmp/stab-decomp-q7/Full.lean`

Pins match: the manifest records project b4d606db and Mathlib 25730c7c, equal to workspace HEAD and .lake/packages/mathlib; the snapshot Contract.lean, workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…). Reuse: chart_tangentSpace_eq_range_fderiv is accepted (candidate d626082a69a0) and is reused with its byte-identical frozen type; area_formula (codim1_hcp_submanifold_area_formula) and lipschitz_approx (codim1_hcp_lipschitz_smooth_approx) are active nodes under another parent, so they are not children: they enter smooth_case and lipschitz_extension as hypotheses and are discharged in this node's glue, where they are resolved dependencies; locally_closed likewise supplies MeasurableSet M in the glue. The 11 codim1_hcp_stab_ names occur nowhere in dag.json, GMT/, SimonGMT or the snapshot (rg: no match). Library: SimonGMT has related but unusable material (Chapter08/JacobianBounds.lean: quadraticMatrixDeterminant = det(1 + t•X + t²•Y) with first-order Lipschitz bounds; Chapter02/AreaApproximation.lean; AppendixB algebra), none in Submission's import closure and none giving a second-order expansion, so det_second_order and jacobian_bound are new. The pinned Mathlib (inside the import closure) supplies Matrix.coeff_det_one_add_X_smul_eq_sum_minors (Charpoly/Coeff.lean:398), LinearMap.IsSymmetric.det_eq_prod_eigenvalues (Spectrum.lean:389), ContDiffAt.isSymmSndFDerivAt (FDeriv/Symmetric.lean:533), LinearMap.trace_eq_sum_inner (InnerProductSpace/Trace.lean:25), exists_contDiff_support_eq_eq_one_iff (PartitionOfUnity.lean:789), exists_compact_between (LocallyCompact.lean:172), tendsto_integral_filter_of_dominated_convergence (DominatedConvergence.lean:67), setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (Bochner/Set.lean:466), IntegrableOn.of_forall_sdiff_eq_zero (IntegrableOn.lean:435), Convex.norm_image_sub_le_of_norm_fderiv_le (MeanValue.lean:499); Matrix.PosSemidef.det_nonneg (Analysis/Matrix/PosDef.lean:51) exists but is outside the closure, so det ≥ 0 is proved via the spectral theorem. Lean: all 11 new child types elaborate after import GMT.Ch07.Submission in namespace GMT.Ch07 with the contract opens; Full.lean (1626 lines, 0 errors, no sorry) proves every child and the selected frozen type; #print axioms lists only propext, Classical.choice, Quot.sound for the children (plus chart_tangentSpace_eq_range_fderiv for tangent_projection, shape_operator, smooth_case), and for the selected theorem additionally only its resolved dependencies chart_tangentSpace_eq_range_fderiv, dimred_rpd_embedded_locally_closed, codim1_hcp_submanifold_area_formula and codim1_hcp_lipschitz_smooth_approx (as axioms with their frozen types). The runtime caps depth at 6, so these depth-6 children are leaves.
