# Parent-supplied natural-language proof

- Parent DAG node: `root.tilt_excess_decay-a1.graph_weak_equation-a1.graph_jacobian_bounds-a1`
- Child DAG node: `root.tilt_excess_decay-a1.graph_weak_equation-a1.graph_jacobian_bounds-a1.det_one_add_bounds-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Context. This child is steps 1-7 of the parent proof in matrix form. The parent applies it to the Gram matrix G = (<D e_a, D e_b>) of D. The sibling gwe_gjb_gram_symm_psd_trace supplies the symmetry and positive semidefiniteness of G and trace G = hsNormSq D. Then 1 <= det(I + G) gives part (i) after taking square roots, and det(I + G) <= exp(trace G) = exp(hsNormSq D) is step 7.

Notation.
- A := I + G, a real n x n matrix indexed by Fin n.
- For x, y : Fin n -> R, x . y := dotProduct x y = sum_i x_i y_i.
- A x := Matrix.mulVec A x, with (A x)_i = sum_j A_ij x_j.
- The symmetry hypothesis is essential. G = [[0, 1], [-1, 0]] has x . (G x) = 0 for every x, but det(I + G) = 2 > 1 = exp(trace G).

1. A is symmetric, hence Hermitian. A^T = I^T + G^T = I + G = A (transpose_add, transpose_one and the hypothesis G^T = G). Over R the star operation is trivial, so the conjugate transpose of A equals A^T (Matrix.conjTranspose_eq_transpose_of_trivial). Hence A^H = A, i.e. A is Hermitian (Matrix.IsHermitian A).
2. Quadratic form of A. For every x : Fin n -> R we have A x = x + G x (Matrix.add_mulVec, Matrix.one_mulVec). So, by dotProduct_add and the hypothesis,
   x . (A x) = x . x + x . (G x) >= x . x.
3. Spectral theorem. A is Hermitian, so the spectral theorem for Hermitian matrices (Mathlib.Analysis.Matrix.Spectrum) applies. It gives real numbers lambda_i := hA.eigenvalues i (i in Fin n) and an orthonormal basis u_i := hA.eigenvectorBasis i of EuclideanSpace R (Fin n), with A u_i = lambda_i u_i. It also gives lambda_i = re(star u_i . (A u_i)) (Matrix.IsHermitian.eigenvalues_eq). Over R, re is the identity and star u_i = u_i, so lambda_i = u_i . (A u_i).
4. Every eigenvalue is at least 1. The basis is orthonormal, so ||u_i|| = 1. Also ||u_i||^2 = sum_j (u_i)_j^2 = u_i . u_i (EuclideanSpace.norm_sq_eq), so u_i . u_i = 1. By steps 2 and 3,
   lambda_i = u_i . (A u_i) = u_i . u_i + u_i . (G u_i) >= 1.
   In particular every lambda_i > 0.
5. Determinant and trace via eigenvalues. det A = prod_i lambda_i (Matrix.IsHermitian.det_eq_prod_eigenvalues) and trace A = sum_i lambda_i (Matrix.IsHermitian.trace_eq_sum_eigenvalues). Over R the coercions R -> R in these formulas are the identity.
6. Lower bound. Every factor lambda_i is >= 1, so det A = prod_i lambda_i >= 1, since a finite product of factors >= 1 is >= 1 (Finset.one_le_prod₀). For n = 0 the product is empty and equals 1.
7. Trace of A. trace A = trace I + trace G = n + trace G (Matrix.trace_add, Matrix.trace_one, card (Fin n) = n).
8. Upper bound. For each i, lambda_i = (lambda_i - 1) + 1 <= exp(lambda_i - 1) (Real.add_one_le_exp), and lambda_i >= 0 by step 4. All factors are nonnegative, so the products compare factor by factor (Finset.prod_le_prod₀):
   det A = prod_i lambda_i <= prod_i exp(lambda_i - 1) = exp(sum_i (lambda_i - 1)) = exp(trace A - n) = exp(trace G).
   The first equality is Real.exp_sum. The second uses sum_i (lambda_i - 1) = sum_i lambda_i - n = trace A - n (step 5). The third is step 7.
9. Conclusion. Since A is literally (1 : Matrix (Fin n) (Fin n) R) + G, steps 6 and 8 are the two claimed inequalities.
10. Case n = 0. All products are empty and all sums vanish: det A = 1 and trace G = 0. So the claims read 1 <= 1 and 1 <= exp 0 = 1, and steps 6 and 8 cover this case verbatim. QED

Lean notes. Checked against the pinned toolchain.
- Imports: the contract's imports do not provide Matrix.IsHermitian or the spectral API. Add `import Mathlib.Analysis.Matrix.Spectrum` to GMT/Ch05/Submission.lean. Other accepted candidates in this run also add Mathlib imports, and the verifier byte-checks every frozen input except Submission.lean. If Submission.lean already imports Poincare.SimonGMT.Chapter02.AreaLipschitz (as the area-formula siblings do), that import already provides the module.
- Products: in this Mathlib, Finset.prod_le_prod is the ordered-monoid version. It needs MulLeftMono, which R lacks. Use Finset.prod_le_prod₀ (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ g i) and Finset.one_le_prod₀.
- Useful names:
  - transpose and Hermitian: Matrix.transpose_add, Matrix.transpose_one, Matrix.IsSymm.eq, Matrix.conjTranspose_eq_transpose_of_trivial;
  - eigenvalues: Matrix.IsHermitian.eigenvalues_eq, OrthonormalBasis.orthonormal, EuclideanSpace.norm_sq_eq, RCLike.re_to_real, star_trivial;
  - quadratic form: Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add;
  - det and trace: Matrix.IsHermitian.det_eq_prod_eigenvalues and Matrix.IsHermitian.trace_eq_sum_eigenvalues (remove the coercions with simpa), Matrix.trace_add, Matrix.trace_one, Fintype.card_fin;
  - exponential: Real.add_one_le_exp, Real.exp_sum, Finset.sum_sub_distrib.

## Key steps

1. A = I + G is symmetric, hence Hermitian over R, and x . (A x) = x . x + x . (G x) >= x . x.
2. Spectral theorem: A has real eigenvalues lambda_i with orthonormal eigenvectors u_i, and lambda_i = u_i . (A u_i) >= u_i . u_i = 1.
3. det A = prod lambda_i >= 1.
4. trace A = sum lambda_i = n + trace G.
5. lambda_i <= exp(lambda_i - 1), so det A <= exp(sum (lambda_i - 1)) = exp(trace G).

## Reference use

### local-project

Queries:
- `cmp GMT/Ch05/Contract.lean GMT/Ch05/Submission.lean; cmp GMT/Ch05/Contract.lean <snapshot>/project/GMT/Ch05/Contract.lean (both identical)`
- `cat <snapshot>/manifest.json`
- `git show 5bbe8ae4f8fe0a36d50423feae34d64cadb59ca3:GMT/Ch05/Submission.lean | grep -n '^import\|^theorem' (proof base is contract-only, 463 lines)`
- `grep -rn 'theorem det_eq_prod_eigenvalues\|theorem trace_eq_sum_eigenvalues\|theorem eigenvalues_eq\|lemma eigenvalues_nonneg\|posSemidef_gram\|def gram' <snapshot>/mathlib/Mathlib`
- `sed -n 1,260p <snapshot>/mathlib/Mathlib/Analysis/Matrix/Spectrum.lean`
- `grep -n '^theorem\|^lemma\|^def' <snapshot>/mathlib/Mathlib/LinearAlgebra/Matrix/PosDef.lean; sed -n 55,70p and 295,312p of it; sed -n 1,80p <snapshot>/mathlib/Mathlib/Analysis/Matrix/PosDef.lean; sed -n 30,100p <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/GramMatrix.lean`
- `grep -rn 'theorem prod_le_prod₀\|lemma prod_le_prod₀\|lemma one_le_prod₀' <snapshot>/mathlib/Mathlib`
- `lean Avail.lean / Avail2.lean: #check after import GMT.Ch05.Submission of Matrix.PosSemidef, Matrix.IsHermitian(.eigenvalues/.det_eq_prod_eigenvalues/.trace_eq_sum_eigenvalues/.eigenvalues_eq), Matrix.gram, Matrix.IsSymm, dotProduct, Matrix.mulVec, Matrix.det, Matrix.trace, Real.exp_half, Real.add_one_le_exp, Real.exp_sum, LinearMap.IsSymmetric.eigenvalues`
- `lean Sig.lean: #check @Finset.prod_le_prod / @Finset.one_le_prod / @Finset.prod_le_one under Mathlib.Analysis.Matrix.Spectrum`
- `python3 -I: dag.json census of lean_statements containing hsNormSq, Matrix.det or Real.exp; full fields of node lean_name lgc_hsNormSq_bounds; children lists of graph_plane_dist-a1 and small_tilt_plane-a1; duplicate-lean_name scan`
- `git show 7372f81c6640dd17bd99bd3c9bbe79675f27d126 --stat; git show 7372f81c6640dd17bd99bd3c9bbe79675f27d126:GMT/Ch05/Submission.lean | grep -n lgc_hsNormSq_bounds`
- `git show d6f38af23b12fb6e368b6b80cdb925d6287ac6ea:GMT/Ch05/Submission.lean | grep -n 'Matrix.det\|IsHermitian\|eigenvalues' (accepted dohr_vel_linear_graph_area: only 0 < det, via det_mul/det_transpose)`
- `grep -rl 'gwe_gjb_gram_symm_psd_trace\|gwe_gjb_det_one_add_bounds\|gwe_gjb_exp_half_le\|gwe_gjb_' <run>/dag.json <run>/nodes <snapshot>/project/GMT .lake/packages/simongmt/Poincare; git show <every ref>:GMT/Ch05/Submission.lean | grep gwe_gjb (no match)`
- `python3 -I: import survey of accepted candidate commits (31 add Mathlib/SimonGMT imports); sed -n 249,370p and 419,645p verifier/gmt-compare.py (frozen_inputs/candidate_inputs exempt Submission.lean; contract_scope/child_modules)`
- `lean -o /tmp/gjb-decomp-20261012/olean/GMT/Ch05/Submission.olean GMT/Ch05/Submission.lean (contract-only)`
- `python3 -I /tmp/gjb-decomp-20261012/scripts/scope.py and gen_checks.py (verifier contract_scope/child_modules) -> checks/challenge/*.lean, TypesSubmission.lean, Assembly.lean`
- `lean checks/challenge/{PARENT,gwe_gjb_gram_symm_psd_trace,gwe_gjb_det_one_add_bounds,gwe_gjb_exp_half_le,lgc_hsNormSq_bounds}.lean; lean TypesSubmission.lean; lean Assembly.lean (#print axioms parent_check); lean Inst.lean; lean ProofA.lean ProofB.lean ProofC.lean EndToEnd.lean (#print axioms); lean ImpCheck.lean (import Poincare.SimonGMT.Chapter02.AreaLipschitz provides the spectral API)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/PROBLEM.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1-graph-jacobian-bounds-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1-graph-jacobian-bounds-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1-graph-jacobian-bounds-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1/decomposition-scope-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-graph-corollary-a1-hole-estimate-a1-hs-norm-bounds-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-decay-at-origin-a1-graph-plane-dist-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Matrix/Spectrum.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Matrix/PosDef.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/LinearAlgebra/Matrix/PosDef.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/GramMatrix.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Spectrum.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Algebra/Order/BigOperators/GroupWithZero/Finset.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/tmp/gjb-decomp-20261012/scripts/scope.py`
- `/tmp/gjb-decomp-20261012/scripts/gen_checks.py`
- `/tmp/gjb-decomp-20261012/scripts/build_draft.py`
- `/tmp/gjb-decomp-20261012/out/stmts.json`
- `/tmp/gjb-decomp-20261012/out/subproblems_draft.json`
- `/tmp/gjb-decomp-20261012/checks/Avail.lean`
- `/tmp/gjb-decomp-20261012/checks/Avail2.lean`
- `/tmp/gjb-decomp-20261012/checks/challenge/PARENT.lean`
- `/tmp/gjb-decomp-20261012/checks/challenge/gwe_gjb_gram_symm_psd_trace.lean`
- `/tmp/gjb-decomp-20261012/checks/challenge/gwe_gjb_det_one_add_bounds.lean`
- `/tmp/gjb-decomp-20261012/checks/challenge/gwe_gjb_exp_half_le.lean`
- `/tmp/gjb-decomp-20261012/checks/challenge/lgc_hsNormSq_bounds.lean`
- `/tmp/gjb-decomp-20261012/checks/TypesSubmission.lean`
- `/tmp/gjb-decomp-20261012/checks/Assembly.lean`
- `/tmp/gjb-decomp-20261012/checks/Inst.lean`
- `/tmp/gjb-decomp-20261012/checks/ProofA.lean`
- `/tmp/gjb-decomp-20261012/checks/ProofB.lean`
- `/tmp/gjb-decomp-20261012/checks/ProofC.lean`
- `/tmp/gjb-decomp-20261012/checks/EndToEnd.lean`
- `/tmp/gjb-decomp-20261012/checks/ImpCheck.lean`

Revisions. Snapshot a7f8fcd21d5c8fc7 pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. Its Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. The node's proof base 5bbe8ae4 is contract-only.

Statement-level API (contract imports only).
- Unknown: Matrix.PosSemidef, Matrix.PosDef, Matrix.IsHermitian (and its eigenvalues, eigenvectorBasis, det_eq_prod_eigenvalues, trace_eq_sum_eigenvalues, eigenvalues_eq), Matrix.gram, LinearMap.IsSymmetric.eigenvalues.
- Available: Matrix.IsSymm, dotProduct, Matrix.mulVec, Matrix.det, Matrix.trace, Real.exp_half, Real.add_one_le_exp, Real.exp_sum, ContinuousLinearMap.le_opNorm.
- So the matrix child is stated with IsSymm and dotProduct/mulVec.

Spectral API (snapshot Mathlib/Analysis/Matrix/Spectrum.lean).
- eigenvalues, eigenvectorBasis, mulVec_eigenvectorBasis, eigenvalues_eq (line 147), det_eq_prod_eigenvalues (line 192) and trace_eq_sum_eigenvalues (line 239) exist.
- Matrix.posSemidef_gram is at Analysis/InnerProductSpace/GramMatrix.lean:82; PosSemidef is defined at LinearAlgebra/Matrix/PosDef.lean:62.
- Finset.prod_le_prod is the MulLeftMono version, unusable on ℝ. The usable ones are Finset.prod_le_prod₀ and one_le_prod₀ (Algebra/Order/BigOperators/GroupWithZero/Finset.lean:38, 83).
- Importing Mathlib.Analysis.Matrix.Spectrum, or Poincare.SimonGMT.Chapter02.AreaLipschitz, provides this API.
- The verifier byte-checks every frozen input except Submission.lean, and 31 accepted candidates add imports.

Reuse.
- lgc_hsNormSq_bounds (node root.lipschitz_graph_corollary-a1.hole_estimate-a1.hs_norm_bounds-a1) is accepted with depends_on [].
- Commit 7372f81c contains theorem lgc_hsNormSq_bounds with the identical type.
- The child copies lean_statement, title and statement byte-for-byte, and its proof is the accepted proof text.
- Precedent: the accepted graph_plane_dist-a1 lists this node among its children.
- No accepted node gives 1 <= det <= exp(trace). The closest, dohr_vel_linear_graph_area (d6f38af2), only gives 0 < det.

Names. gwe_gjb_gram_symm_psd_trace, gwe_gjb_det_one_add_bounds and gwe_gjb_exp_half_le occur nowhere in dag.json, nodes/**, the snapshot project, simongmt, or any branch's Submission.lean. No duplicate lean_names exist in the DAG.

Lean checks.
- All five verifier-generated challenge files (four children and the parent) elaborate.
- TypesSubmission elaborates with three sorry warnings and no errors.
- Assembly: the sorry-free parent_check uses only propext, Classical.choice and Quot.sound.
- Inst.lean confirms the intended matrix and inner-product instances, and the 2x2 counterexample shows IsSymm is needed.
- ProofA (contract imports only), ProofB (plus Mathlib.Analysis.Matrix.Spectrum), ProofC and EndToEnd (parent proved from Submission children by name, plus the HumanizeNodeComparator.target) all compile with the standard axioms only.
