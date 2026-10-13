# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_regularity-a1.graph_plane_algebra-a1.graph_proj_smooth-a1`
- Child DAG node: `root.allard_regularity-a1.graph_plane_algebra-a1.graph_proj_smooth-a1.hs_block_swap-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 8 (Hilbert-Schmidt norm), stated for any operator D with the block form [[0, H^T],[H, 0]]. No sibling result is used; proj_fderiv_zero supplies this hypothesis for D = DPi(0)[H] only in the parent assembly.

1. Norms of graph points. ||graphPoint x y||^2 = ||x||^2 + ||y||^2: on EuclideanSpace, ||z||^2 = sum_k z_k^2 (EuclideanSpace.real_norm_sq_eq); split the sum over Fin (n+l) into castAdd and natAdd parts (Fin.sum_univ_add), where the coordinates of graphPoint x y are x_i, resp. y_j (Fin.append_left/right).

2. Standard basis of R^(n+l). Let E_k := EuclideanSpace.single k 1 in R^(n+l) and f_j := EuclideanSpace.single j 1 in R^l. Then E_(castAdd l i) = graphPoint e_i 0 and E_(natAdd n j) = graphPoint 0 f_j. Compare coordinates at the indices castAdd l i' and natAdd n j' (Fin.addCases): E_(castAdd l i) has coordinate 1 exactly at castAdd l i (castAdd is injective, and castAdd l i' is never natAdd n j' because their values satisfy i' < n <= n + j'), which matches the coordinates (e_i)_(i') and 0 of graphPoint e_i 0. Likewise E_(natAdd n j) has coordinate 1 exactly at natAdd n j (natAdd n is injective and never equals castAdd l i'), which matches the coordinates 0 and (f_j)_(j') of graphPoint 0 f_j.

3. Splitting the sum. By definition hsNormSq D = sum_{k in Fin (n+l)} ||D E_k||^2 = sum_{i in Fin n} ||D E_(castAdd l i)||^2 + sum_{j in Fin l} ||D E_(natAdd n j)||^2 (Fin.sum_univ_add).

4. Horizontal columns. For i in Fin n, by step 2 and the hypothesis, D E_(castAdd l i) = D(graphPoint e_i 0) = graphPoint (sum_{i'} <H e_(i'), 0> e_(i')) (H e_i) = graphPoint 0 (H e_i) (<z, 0> = 0). By step 1, ||D E_(castAdd l i)||^2 = ||H e_i||^2.

5. Vertical columns. For j in Fin l, D E_(natAdd n j) = D(graphPoint 0 f_j) = graphPoint (sum_{i'} <H e_(i'), f_j> e_(i')) (H 0) = graphPoint (sum_{i'} (H e_(i'))_j e_(i')) 0, because <z, f_j> = z_j (EuclideanSpace.inner_single_right) and H 0 = 0. By step 1, ||D E_(natAdd n j)||^2 = ||sum_{i'} (H e_(i'))_j e_(i')||^2 = sum_{i} (H e_i)_j^2, since the i-th coordinate of sum_{i'} c_(i') e_(i') is c_i (EuclideanSpace.real_norm_sq_eq).

6. Summation. Combining steps 3-5 and exchanging the finite sums (Finset.sum_comm):
 hsNormSq D = sum_i ||H e_i||^2 + sum_j sum_i (H e_i)_j^2 = sum_i ||H e_i||^2 + sum_i sum_j (H e_i)_j^2 = sum_i ||H e_i||^2 + sum_i ||H e_i||^2 = 2 hsNormSq H,
 using ||z||^2 = sum_j z_j^2 for z in R^l (EuclideanSpace.real_norm_sq_eq) and hsNormSq H = sum_i ||H e_i||^2 by definition.

## Key steps

1. ||graphPoint x y||^2 = ||x||^2 + ||y||^2
2. E_(castAdd l i) = graphPoint e_i 0 and E_(natAdd n j) = graphPoint 0 f_j
3. Split hsNormSq D over castAdd/natAdd indices (Fin.sum_univ_add)
4. Horizontal columns contribute ||H e_i||^2; vertical columns contribute sum_i (H e_i)_j^2
5. Exchange the finite sums: hsNormSq D = hsNormSq H + hsNormSq H

## Reference use

### local-project

Queries:
- `rg -c 'allard52_gps' <snapshot>/project  (exit 1, no match)`
- `rg -c 'allard52_gps|gps_transpose_exists|starProjection_eq_gram|hsNormSq_swap|gps_fderiv_zero_apply' <snapshot>/mathlib/Mathlib  (no match)`
- `python3 -I over dag.json nodes: all 431 lean_name values (unique); none equals or contains a proposed name; none contains 'gps'`
- `git for-each-ref refs/heads | xargs git grep -l allard52_gps  (955 branches, no match)`
- `rg -n 'theorem contDiffAt_ringInverse|theorem hasFDerivAt_ringInverse' <snapshot>/mathlib/Mathlib/Analysis/Calculus`
- `rg -n 'theorem HasFDerivAt.clm_comp|theorem ContDiff.clm_comp' <snapshot>/mathlib/Mathlib/Analysis/Calculus`
- `rg -n 'theorem eq_starProjection_of_mem_of_inner_eq_zero' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace`
- `rg -n 'theorem isUnit_iff_isUnit_toLinearMap|theorem isUnit_iff_ker_eq_bot' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem ext_inner_right' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace; rg -n 'finAddEquivProd|def basisFun|theorem sum_repr' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `rg -n 'theorem mul_inverse_cancel|theorem inverse_one' <snapshot>/mathlib/Mathlib/Algebra/GroupWithZero`
- `rg -n 'theorem hasFDerivAt_const_add_iff|theorem contDiff_iff_contDiffAt' <snapshot>/mathlib/Mathlib/Analysis/Calculus; grep -n 'HasFDerivAt.const_add' FDeriv/Add.lean`
- `rg -n 'def toContinuousLinearMap' <snapshot>/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `rg -n 'ContinuousLinearMap.adjoint' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean; rg -n '^import' <snapshot>/project/GMT/Ch05/Contract.lean`
- `diff -q <snapshot>/project/GMT/Ch05/Contract.lean and Submission.lean against the workspace copies (identical)`
- `git show 9f89be4c -- GMT/Ch05/Submission.lean (accepted aetp_starProjection_range_continuousOn); git show 18a457c4 (accepted rsod_graphPoint_eq_finAddEquivProd_symm)`
- `lean Probe.lean (#check of every cited lemma) and Probe3.lean (adjoint absence, instances, Amb n ℓ = Rn (n+ℓ) by rfl) against a scratch Submission.olean built from the workspace Submission.lean`
- `lean Stmts.lean (5 child types by sorry plus the parent frozen type proved from them)`
- `lean Full.lean (all 5 children proved, parent assembled, #print axioms)`
- `comparator-style NodeChallenge/NodeSolution per child, scope from gmt-compare.py contract_scope, compiled against scratch Submission2.lean containing the children`
- `python3 -I lean_contract.validate_lean_statement on all 5 lean_statements`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Operator/Banach.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Algebra/GroupWithZero/Units/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-graph-plane-algebra-a1-graph-proj-smooth-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-graph-plane-algebra-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/gps-decomp-8uUBVY/check/Probe.lean`
- `/tmp/gps-decomp-8uUBVY/check/Probe3.lean`
- `/tmp/gps-decomp-8uUBVY/check/Stmts.lean`
- `/tmp/gps-decomp-8uUBVY/check/Full.lean`
- `/tmp/gps-decomp-8uUBVY/Submission2.lean`
- `/tmp/gps-decomp-8uUBVY/cmp/Chal_allard52_gps_fderiv_zero_apply.lean`
- `/tmp/gps-decomp-8uUBVY/cmp/Sol_allard52_gps_fderiv_zero_apply.lean`

The snapshot pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The snapshot's Contract.lean and Submission.lean are byte-identical to the workspace copies.

Names
- The proposed bare names allard52_gps_{transpose_exists, starProjection_eq_gram, contDiff, fderiv_zero_apply, hsNormSq_swap} have no match in the snapshot project, the snapshot Mathlib, the 431 DAG lean_names or 955 local branches.

Mathlib lemmas used by the child proofs (all inside the import closure)
- contDiffAt_ringInverse (Calculus/ContDiff/Operations.lean:772)
- hasFDerivAt_ringInverse (Calculus/FDeriv/Mul.lean:661)
- HasFDerivAt.clm_comp (FDeriv/CompCLM.lean:61)
- ContDiff.clm_comp (ContDiff/Comp.lean:472)
- contDiff_iff_contDiffAt (ContDiff/Defs.lean:1103)
- hasFDerivAt_const_add_iff and its alias HasFDerivAt.const_add (FDeriv/Add.lean:344, 348)
- Submodule.eq_starProjection_of_mem_of_inner_eq_zero (InnerProductSpace/Projection/Basic.lean:180)
- ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap (Normed/Operator/Banach.lean:477)
- LinearMap.isUnit_iff_ker_eq_bot (LinearAlgebra/FiniteDimensional/Basic.lean:456)
- ext_inner_right (InnerProductSpace/Basic.lean:330)
- EuclideanSpace.finAddEquivProd (PiL2.lean:378)
- EuclideanSpace.basisFun (PiL2.lean:802)
- OrthonormalBasis.sum_repr (PiL2.lean:494)
- Ring.mul_inverse_cancel and Ring.inverse_one (GroupWithZero/Units/Basic.lean:99, 129)
- LinearMap.toContinuousLinearMap (Topology/Algebra/Module/FiniteDimension.lean:307)

Import gaps and instances
- ContinuousLinearMap.adjoint exists in Mathlib (InnerProductSpace/Adjoint.lean) but is an unknown constant after `import GMT.Ch05.Submission`. This confirms that the hand-built transpose child is needed.
- These instances are inferred: HasSummableGeomSeries (Rn n →L[ℝ] Rn n) and FiniteDimensional ℝ (Rn n →L[ℝ] Rn ℓ). Also Amb n ℓ = Rn (n+ℓ) holds by rfl.

Accepted precedents (reused as proof patterns, not as dependencies)
- Commit 9f89be4c (aetp_starProjection_range_continuousOn) uses the same hand-built transpose and the same Gram projection identity.
- Commit 18a457c4 proves graphPoint = finAddEquivProd.symm with ext, Fin.addCases and simp [graphPoint].
- Neither theorem's type equals a child here, so no accepted declaration is reused.

Lean results
- Full.lean proves all five children and then the parent's exact frozen type from them. #print axioms reports only propext, Classical.choice and Quot.sound.
- Every comparator-style challenge and solution module compiles.
- validate_lean_statement accepts all five statements.

No public source beyond Simon p. 123, which the parent proof already cites, was needed.
