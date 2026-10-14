# Parent-supplied natural-language proof

- Parent DAG node: `root.minimizing_implies_stationary-a1.first_variation_mass_bound-a1`
- Child DAG node: `root.minimizing_implies_stationary-a1.first_variation_mass_bound-a1.orient_approx_tangent_plane-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1 of the parent proof. Simon Ch. 6, Definition 3.1 (book/chapter-06.txt lines 733–747): for H^n-a.e. x ∈ M, ξ(x) = τ_1∧⋯∧τ_n with τ an orthonormal basis of the approximate tangent space T_xM. Simon Ch. 3, Remark 1.5(1) (book/chapter-03.txt line 86): the approximate tangent space is unique if it exists (SimonGMT HasApproximateTangentSpaceAt.unique, Chapter03/Rectifiable.lean:232). Write M := R.carrier, ξ := R.orient and μ := μHE[n] restricted to M.
1. By the field R.orients, for μ-almost every x there is a subspace Q with HasApproximateTangentSpaceAt n M x Q and IsUnitOrientationOf (ξ x) Q. Fix such x and Q. It suffices to prove approxTangentPlane n M x = Q, because IsUnitOrientationOf (ξ x) (approxTangentPlane n M x) is then the second property of Q.
2. By definition, approxTangentPlane n M x is the chosen witness Q₀ of the proposition ∃ Q', HasApproximateTangentSpaceAt n M x Q' when this proposition holds, and ⊥ otherwise. Here the proposition holds, with Q as a witness. So approxTangentPlane n M x = Q₀, and by the defining property of the choice, HasApproximateTangentSpaceAt n M x Q₀.
3. Approximate tangent planes are unique: HasApproximateTangentSpaceAt n M x Q₀ and HasApproximateTangentSpaceAt n M x Q imply Q₀ = Q (HasApproximateTangentSpaceAt.unique). Hence approxTangentPlane n M x = Q.
4. Therefore IsUnitOrientationOf (ξ x) (approxTangentPlane n M x) holds at every x of the full-measure set from step 1, i.e. for μ-almost every x. ∎

## Key steps

1. R.orients gives, μHE[n]⌞M-a.e., a plane Q with HasApproximateTangentSpaceAt n M x Q that ξ(x) orients.
2. At such x, approxTangentPlane n M x is the chosen witness, which equals Q by HasApproximateTangentSpaceAt.unique.

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
