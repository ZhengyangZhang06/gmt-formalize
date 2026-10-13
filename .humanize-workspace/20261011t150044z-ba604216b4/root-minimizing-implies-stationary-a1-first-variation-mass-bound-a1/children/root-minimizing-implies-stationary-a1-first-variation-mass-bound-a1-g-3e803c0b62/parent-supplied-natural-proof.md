# Parent-supplied natural-language proof

- Parent DAG node: `root.minimizing_implies_stationary-a1.first_variation_mass_bound-a1`
- Child DAG node: `root.minimizing_implies_stationary-a1.first_variation_mass_bound-a1.gram_det_exp_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 of the parent proof (det G = Πλ_a ≤ Π e^{λ_a − 1} = exp(tr G − n)). Background: Simon Ch. 4, 1.9 (book/chapter-04.txt lines 95–113, J^M_f = (det(D_{τ_k}f·D_{τ_ℓ}f))^{1/2}) and Ch. 2, §5 (book/chapter-02.txt lines 1162–1256), where the Jacobian is the square root of such a Gram determinant. The inequality is the exponential form of the AM–GM inequality for the eigenvalues of a positive semidefinite matrix; compare Hadamard's determinant inequality. Notation: u·w is the Euclidean inner product and G := (v_i·v_j)_{i,j=1}^n (Matrix.of fun i j => inner ℝ (v i) (v j)).
1. Operator realizing G. Let F := ℝ^n (EuclideanSpace ℝ (Fin n)) with its standard orthonormal basis e_1, …, e_n (EuclideanSpace.basisFun). Let V : F → ℝ^P be the linear map with V e_a = v_a for every a, i.e. V w = Σ_a w_a v_a (in Mathlib, (basisFun).toBasis.constr ℝ v). Let V* : ℝ^P → F be its adjoint, characterized by x·V*y = Vx·y for x ∈ F, y ∈ ℝ^P, and put S := V*∘V : F → F.
2. S is symmetric with a nonnegative quadratic form. For x, y ∈ F, x·Sy = Vx·Vy by the definition of the adjoint, and likewise Sx·y = Vx·Vy. Hence Sx·y = x·Sy, and x·Sx = |Vx|² ≥ 0 (Mathlib LinearMap.isSymmetric_adjoint_comp_self).
3. Matrix, determinant and trace of S. In the orthonormal basis (e_a), the (a, b) entry of the matrix of S is e_a·Se_b = Ve_a·Ve_b = v_a·v_b = G_{ab}. So the matrix of S in this basis is G, and det S = det G, because the determinant of an endomorphism equals the determinant of its matrix in any basis (LinearMap.det_toMatrix). Also trace S = Σ_a e_a·Se_a (trace in an orthonormal basis, LinearMap.trace_eq_sum_inner) = Σ_a Ve_a·Ve_a = Σ_a |v_a|².
4. Spectral theorem. S is symmetric on the n-dimensional real inner product space F (finrank F = n). So there are an orthonormal basis u_1, …, u_n of F and real numbers λ_1, …, λ_n with Su_i = λ_i u_i, det S = Π_i λ_i and trace S = Σ_i λ_i. (Mathlib: LinearMap.IsSymmetric.eigenvalues, eigenvectorBasis, apply_eigenvectorBasis, det_eq_prod_eigenvalues and IsSymmetric.trace_eq_sum_eigenvalues.)
5. Nonnegativity: λ_i = λ_i|u_i|² = u_i·(λ_i u_i) = u_i·Su_i = |Vu_i|² ≥ 0, by step 2.
6. Exponential AM–GM. For every real s, s + 1 ≤ e^s (Real.add_one_le_exp); with s = λ_i − 1 this gives λ_i ≤ e^{λ_i − 1}. Since 0 ≤ λ_i ≤ e^{λ_i − 1} for every i, multiplying these n inequalities between nonnegative numbers gives Π_i λ_i ≤ Π_i e^{λ_i − 1} = exp(Σ_i (λ_i − 1)) = exp(Σ_i λ_i − n) (Finset.prod_le_prod₀, Real.exp_sum).
7. Conclusion: det G = det S = Π_i λ_i ≤ exp(trace S − n) = exp(Σ_a |v_a|² − n). For n = 0 every product is empty and every sum is 0, so the same argument gives 1 ≤ exp 0 = 1. ∎

## Key steps

1. Realize G = (v_i·v_j) as the matrix of the symmetric operator S = V*V on ℝ^n (V e_a = v_a) in the standard orthonormal basis, so det S = det G and tr S = Σ_a |v_a|².
2. Spectral theorem for S: det S = Π λ_i, tr S = Σ λ_i, and λ_i = |V u_i|² ≥ 0 for the orthonormal eigenvectors u_i.
3. 0 ≤ λ_i ≤ e^{λ_i − 1}; multiplying these nonnegative inequalities gives Π λ_i ≤ exp(Σ λ_i − n).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (mode local-project, project b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib 25730c7c759d108ef87ab70af2342a196760f79d); cmp project/GMT/Ch07/Contract.lean vs workspace GMT/Ch07/Contract.lean (identical)`
- `python3 -I: read nodes/root-minimizing-implies-stationary-a1-first-variation-mass-bound-a1/{parent-child-handoff.json,parent-supplied-plan.md,parent-supplied-natural-proof.md,decomposition-scope-v1.json,decomposition-v1.json,decomposition-audit-v1.json,decomposition-review-receipt-v1.json}`
- `python3 -I: read nodes/root-minimizing-implies-stationary-a1/decomposition-v2.json (frozen sibling types covectorEuclideanNorm_gram_bounds, imrep_approxTangent_starProjection_aesm)`
- `python3 -I: dag.json scan (451 nodes): selected node entry (status decomposing, attempts 2, children []); lean_name collision check for the four fvmb_ names (none); lean_statement scan for IsUnitOrientationOf|Matrix.det|LinearMap.trace|Orthonormal|fvmb (no identical type)`
- `git log --all --oneline -S"fvmb_" -- GMT/Ch07/Submission.lean (2037 refs, no hits)`
- `git show 2fd8f6f:GMT/Ch07/Submission.lean | grep covectorEuclideanNorm_gram_bounds; git show 36b2d37:GMT/Ch07/Submission.lean | grep imrep_approxTangent_starProjection_aesm (accepted sibling declarations, types identical to the sibling contracts)`
- `grep -rn in mathlib/Mathlib: det_eq_prod_eigenvalues, apply_eigenvectorBasis, IsSymmetric.trace_eq_sum_eigenvalues, trace_eq_sum_inner, isSymmetric_adjoint_comp_self, det_toMatrix, trace_smulRight, eq_starProjection_of_mem_of_inner_eq_zero, sum_repr', add_one_le_exp, abs_exp_sub_one_sub_id_le, sqrt_le_sqrt, prod_le_prod₀, compContinuousLinearMap_apply, support_fderiv_subset, fderiv_of_notMem_tsupport, HasCompactSupport.fderiv, bounded_above_of_compact_support, measurable_fderiv, integral_undef, setIntegral_eq_integral_of_forall_compl_eq_zero, det_isEmpty`
- `grep -n 'def HasApproximateTangentSpaceAt|HasApproximateTangentSpaceAt.unique' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean; sed -n 1,140p Chapter06/Mass.lean; sed -n 100,200p Chapter06/Currents.lean; sed -n 1,130p Chapter06/Forms.lean`
- `sed -n 1015,1050p and 1150,1280p book/chapter-02.txt (4.18-4.20; §5, 5.1-5.3); sed -n 85,165p book/chapter-04.txt (1.8-1.9, 2.1-2.4); sed -n 80,90p book/chapter-03.txt (Remark 1.5(1)); sed -n 730,760p book/chapter-06.txt (Definition 3.1)`
- `sed -n 540,640p verifier/gmt-compare.py; python3 -I /tmp/fvmb2/gen_challenges.py /tmp/fvmb2/children.json (comparator contract_scope/child_modules replay)`
- `lake env lean /tmp/fvmb2/Children.lean (four child types elaborate after import GMT.Ch07.Submission)`
- `lake env lean /tmp/fvmb2/A/Full.lean and /tmp/fvmb2/B/Full.lean (all four children proved; #print axioms; rfl link to tangentialDivergence)`
- `lake env lean /tmp/fvmb2/C/Assembly.lean (frozen parent type from six stubs as axioms)`
- `lake env lean /tmp/fvmb2/D/EndToEnd.lean (children proved + assembly; #print axioms)`
- `lake env lean /tmp/fvmb2/E/SolutionCheck.lean (replayed contract scope; exact Submission.X for four children and the parent)`
- `WebSearch: positive semidefinite matrix determinant trace inequality det A ≤ (tr A / n)^n AM-GM eigenvalues Hadamard inequality Gram determinant`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-first-variation-mass-bound-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-first-variation-mass-bound-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-first-variation-mass-bound-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-first-variation-mass-bound-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-first-variation-mass-bound-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Spectrum.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Complex/Exponential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Real/Sqrt.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/BigOperators/GroupWithZero/Finset.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/fvmb2/Children.lean`
- `/tmp/fvmb2/A/Full.lean`
- `/tmp/fvmb2/B/Full.lean`
- `/tmp/fvmb2/C/Assembly.lean`
- `/tmp/fvmb2/D/EndToEnd.lean`
- `/tmp/fvmb2/E/SolutionCheck.lean`
- `/tmp/fvmb2/gen_challenges.py`
- `/tmp/fvmb2/children.json`

The four child statements are new: the pinned snapshot (project b4d606d, Mathlib 25730c7c) has none of them. Its Contract.lean is byte-identical to the workspace contract. No DAG node (451 scanned) has an identical type, and no fvmb_ name occurs in the DAG or in the Submission.lean history of any of the 2037 refs. Related accepted nodes, such as rsdic_imrep_ae_tangent_orient_of_subset and dorag_th_trace_proj_comp_compl, have different types.

Every library fact the child proofs cite exists in the snapshot:
- Spectral and trace API: LinearMap.IsSymmetric.eigenvalues and eigenvectorBasis; apply_eigenvectorBasis (Spectrum.lean:324); det_eq_prod_eigenvalues (Spectrum.lean:389); IsSymmetric.trace_eq_sum_eigenvalues (InnerProductSpace/Trace.lean:37); LinearMap.trace_eq_sum_inner (InnerProductSpace/Trace.lean:25); LinearMap.isSymmetric_adjoint_comp_self (Adjoint.lean:760); LinearMap.det_toMatrix (Determinant.lean:206); LinearMap.trace_smulRight (LinearAlgebra/Trace.lean:272).
- Projections and bases: Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Projection/Basic.lean:180); OrthonormalBasis.sum_repr' (PiL2.lean:499).
- Real analysis: Real.add_one_le_exp (Exponential.lean:632); Real.abs_exp_sub_one_sub_id_le (Exponential.lean:537); Real.sqrt_le_sqrt (Real/Sqrt.lean:208); Finset.prod_le_prod₀.
- SimonGMT: HasApproximateTangentSpaceAt.unique (Chapter03/Rectifiable.lean:232). massOn is the sSup of ofReal(T ω) over massAdmissibleOn (Chapter06/Mass.lean).
- Used by the parent assembly: fderiv_of_notMem_tsupport and support_fderiv_subset (FDeriv/Const.lean:375-379); integral_undef (Bochner/Basic.lean:204); setIntegral_eq_integral_of_forall_compl_eq_zero (Bochner/Set.lean:486).

Matrix.PosSemidef, Matrix.IsHermitian and Matrix.gram are not in scope after import GMT.Ch07.Submission. So the Gram bound is stated for Matrix.of Gram matrices and proved with the operator API.

Printed sources for the child proofs:
- Simon Ch. 2, 4.18-4.20 (chapter-02.txt lines 1027-1043) and §5 (lines 1162-1256).
- Ch. 4, 1.8-1.9 and 2.1-2.3 (chapter-04.txt lines 95-150).
- Ch. 3, Remark 1.5(1) (chapter-03.txt line 86).
- Ch. 6, Definition 3.1 (chapter-06.txt lines 733-747).

Lean results (v4.35.0-rc3):
- The four child types elaborate in the contract scope that the comparator replays.
- All four are proved using only propext, Classical.choice and Quot.sound.
- The exact frozen parent type is proved from the proved children. The only extra axioms are the accepted siblings covectorEuclideanNorm_gram_bounds and imrep_approxTangent_starProjection_aesm. The run exits 0 with no warnings.
- `exact Submission.X` closes every frozen child type and the parent type.

Public background for det G ≤ exp(tr G − n), via AM-GM and Hadamard-type determinant-trace inequalities: https://www.sciencedirect.com/science/article/pii/S0024379517303890 and https://arxiv.org/pdf/2003.04520.
