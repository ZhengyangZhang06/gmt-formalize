# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_regularity-a1.graph_plane_algebra-a1.graph_proj_smooth-a1.proj_fderiv_zero-a1`
- Child DAG node: `root.allard_regularity-a1.graph_plane_algebra-a1.graph_proj_smooth-a1.proj_fderiv_zero-a1.graph_point_inner-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 2 (inner products of graph points).

1. The inner product of EuclideanSpace R (Fin m) is the coordinate sum <a, b> = sum_k <a_k, b_k> (PiLp.inner_apply), where <a_k, b_k> is the inner product of the real scalars a_k, b_k. Apply this to each of the three inner products in the claim.

2. Unfold graphPoint: graphPoint x y = toLp 2 (Fin.append (ofLp x) (ofLp y)), so its k-th coordinate is Fin.append x y k, and likewise for graphPoint x' y'. Split the sum over Fin (n+l) into its castAdd and natAdd parts (Fin.sum_univ_add): sum_{k : Fin (n+l)} f k = sum_{i : Fin n} f (Fin.castAdd l i) + sum_{j : Fin l} f (Fin.natAdd n j).

3. At castAdd indices the coordinates of graphPoint x y and graphPoint x' y' are x_i and x'_i (Fin.append_left); at natAdd indices they are y_j and y'_j (Fin.append_right). Hence <graphPoint x y, graphPoint x' y'> = sum_i <x_i, x'_i> + sum_j <y_j, y'_j>, which equals <x, x'> + <y, y'> by step 1. (In Lean the single call simp only [graphPoint, PiLp.inner_apply, Fin.sum_univ_add, Fin.append_left, Fin.append_right] closes the goal.)

## Key steps

1. Inner product on EuclideanSpace is the coordinate sum (PiLp.inner_apply)
2. Split the sum over Fin (n+l) into castAdd and natAdd parts (Fin.sum_univ_add)
3. Coordinates there are x_i, x'_i resp. y_j, y'_j (Fin.append_left/right), giving <x, x'> + <y, y'>

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; diff -q GMT/Ch05/Contract.lean <snapshot>/project/GMT/Ch05/Contract.lean; diff -q GMT/Ch05/Submission.lean <snapshot>/project/GMT/Ch05/Submission.lean (identical)`
- `git show 6f3e09432a4729ab700be0e23e98a86bfb2cbd27:GMT/Ch05/Submission.lean (proof base = frozen copy, no extra declarations)`
- `rg -c 'allard52_gfz' <snapshot>/project (exit 1, no match)`
- `rg -c 'allard52_gfz|graphPoint_split|gram_fderiv_zero|transpose_eq_sum' <snapshot>/mathlib/Mathlib (exit 1, no match)`
- `rg -n 'theorem hasFDerivAt_ringInverse' Mathlib/Analysis/Calculus/FDeriv/Mul.lean; rg -n 'theorem HasFDerivAt.clm_comp' FDeriv/CompCLM.lean; rg -n 'HasFDerivAt.const_add|hasFDerivAt_const_add_iff' FDeriv/Add.lean`
- `rg -n 'theorem ext_inner_right' InnerProductSpace/Basic.lean; rg -n 'finAddEquivProd|def basisFun|theorem sum_repr|basisFun_apply|basisFun_repr|inner_single_left|PiLp.inner_apply' InnerProductSpace/PiL2.lean`
- `rg -n 'theorem prod_univ_add' Algebra/BigOperators/Fin.lean; rg -n 'theorem inverse_one' Algebra/GroupWithZero/Units/Basic.lean; rg -n 'def compL' Analysis/Normed/Operator/Bilinear.lean`
- `grep -rn 'theorem one_def|theorem id_comp|theorem mul_def|theorem comp_zero|theorem comp_assoc|instance monoidWithZero' Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Basic.lean`
- `python3 -I over dag.json: 486 lean_names, none contains 'gfz'; all graphPoint lean_statements listed (accepted rsod_graphPoint_eq_finAddEquivProd_symm, any_radius_gr_la_graphPoint_algebra, rsod_norm_graphPoint_sq: types differ from every proposed child)`
- `git grep -l -E 'allard52_gfz' <2437 refs> -- GMT/Ch05/Submission.lean (0 hits; control rsod_graphPoint_eq_finAddEquivProd_symm: 86 hits)`
- `git show 18a457c4 -- GMT/Ch05/Submission.lean; git show 9f89be4c -- GMT/Ch05/Submission.lean (accepted precedents: graphPoint = finAddEquivProd.symm; hand-built transpose + Gram projection)`
- `lake build GMT.Ch05.Submission (scratch copy of frozen project); lake env lean Probe.lean (#check of every cited lemma; HasSummableGeomSeries (Rn n →L[ℝ] Rn n); Amb n ℓ = Rn (n+ℓ) by rfl; ∘L right-associative by rfl)`
- `lake env lean Stmts.lean / Leaves.lean / Analytic.lean / Full.lean (#print axioms) / Inst.lean (Ring.inverse instance = ContinuousLinearMap.monoidWithZero, f * g = f ∘L g by rfl)`
- `python3 -I: lean_contract.validate_lean_statement on all 4 statements; gmt-compare.child_modules(contract mode) -> NodeChallenge/NodeSolution; lake env lean on all 8 against scratch proj2 Submission with the 4 children`
- `sed -n 1105,1135p book/sources/chapter-05-source.txt (Simon p. 123: P = [[I, Df],[Df^t, O]] + F(Df), F(0) = 0, DF(0) = 0)`
- `WebSearch: Golub Pereyra 1973 differentiation of pseudo-inverses derivative of orthogonal projector (cross-check citation only)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Algebra/BigOperators/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Algebra/GroupWithZero/Units/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Operator/Bilinear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-graph-plane-algebra-a1-graph-proj-smooth-a1-29d2ac9c30/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-graph-plane-algebra-a1-graph-proj-smooth-a1-29d2ac9c30/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-graph-plane-algebra-a1-graph-proj-smooth-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-graph-plane-algebra-a1-graph-proj-smooth-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-05-source.txt`
- `/tmp/gfz-decomp-0gZz8u/check/Probe.lean`
- `/tmp/gfz-decomp-0gZz8u/check/Stmts.lean`
- `/tmp/gfz-decomp-0gZz8u/check/Leaves.lean`
- `/tmp/gfz-decomp-0gZz8u/check/Analytic.lean`
- `/tmp/gfz-decomp-0gZz8u/check/Full.lean`
- `/tmp/gfz-decomp-0gZz8u/check/Inst.lean`
- `/tmp/gfz-decomp-0gZz8u/proj2/GMT/Ch05/Submission.lean`
- `/tmp/gfz-decomp-0gZz8u/cmp/allard52_gfz_gram_fderiv_zero/NodeSolution.lean`
- `/tmp/gfz-decomp-0gZz8u/draft/subproblems.json`
- `/tmp/gfz-review-MvEFEG/Implication.lean`

Snapshot and base
- The snapshot pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d.
- The workspace Contract.lean and Submission.lean are byte-identical to the snapshot copies.
- The proof base 6f3e0943 contains only the frozen Submission, so the children must be self-contained; none uses the uncles.

Names
- 'allard52_gfz' has no match in the snapshot project, the snapshot Mathlib, the 486 DAG lean_names, or 2437 local refs (the control name appears in 86 refs).
- No accepted declaration has a type identical to any child, so nothing is reused.

Mathlib lemmas used by the child proofs (all in the import closure)
- hasFDerivAt_ringInverse (FDeriv/Mul.lean:661)
- HasFDerivAt.clm_comp (FDeriv/CompCLM.lean:61)
- HasFDerivAt.const_add (FDeriv/Add.lean:348)
- ext_inner_right (InnerProductSpace/Basic.lean:330)
- In PiL2.lean: EuclideanSpace.finAddEquivProd (:378), PiLp.inner_apply (:101), EuclideanSpace.inner_single_left (:318), OrthonormalBasis.sum_repr (:494), EuclideanSpace.basisFun / basisFun_apply / basisFun_repr (:802/806/810)
- Fin.sum_univ_add, the additive form of prod_univ_add (BigOperators/Fin.lean:159)
- Ring.inverse_one (GroupWithZero/Units/Basic.lean:129)
- ContinuousLinearMap.compL (Normed/Operator/Bilinear.lean:355)
- In ContinuousLinearMap/Basic.lean: one_def (:374), id_comp (:492), comp_zero (:514), comp_assoc (:551), mul_def (:571), monoidWithZero instance (:584)

Instances
- HasSummableGeomSeries (Rn n →L[ℝ] Rn n) is inferred.
- Ring.inverse uses ContinuousLinearMap.monoidWithZero, i.e. composition.

Lean results
- The scratch files prove all four children with only propext, Classical.choice and Quot.sound.
- They also prove the exact frozen parent type from the children plus the two uncles.
- All comparator-style modules compile, and all four statements validate.

Sources
- Simon p. 123 is the printed source. Golub & Pereyra, SIAM J. Numer. Anal. 10 (1973) 413-432, doi:10.1137/0710036 (https://ui.adsabs.harvard.edu/abs/1973SJNA...10..413G/abstract), is consulted only as a cross-check on the projector-derivative formula; no proof depends on it.
