# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.holder_succ_iff_fderiv-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.holder_succ_iff_fderiv-a1.column_iterated_bounds-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3 ('Components') of the parent proof of dohr_eb_holder_succ_iff_fderiv, stated for an arbitrary map g into L(R^n, E) that is C^m on the open set U.
Notation. R^n = Rn n. e_k = EuclideanSpace.single k 1. For h in R^n, h_k = h k. g_k(z) := g(z) e_k. D^m = iteratedFDeriv R m (global). For a continuous linear map L : F -> G and a continuous m-linear map A on (R^n)^m with values in F, write L o A := L.compContinuousMultilinearMap A. All spaces of linear and multilinear maps carry operator norms.
1. Evaluation maps. ev_k := ContinuousLinearMap.apply R E e_k : L(R^n, E) -> E, T -> T e_k. For every T, ||T e_k|| <= ||T|| ||e_k|| = ||T||, because ||e_k|| = 1. Hence ||ev_k|| <= 1 (ContinuousLinearMap.opNorm_le_bound).
2. Reconstruction maps. iota_k := ContinuousLinearMap.smulRightL R (Rn n) E (EuclideanSpace.proj k) : E -> L(R^n, E), so iota_k(w) = (h -> h_k . w) = (EuclideanSpace.proj k).smulRight w. Then ||iota_k(w)|| = ||EuclideanSpace.proj k|| ||w|| (ContinuousLinearMap.norm_smulRight_apply). Also ||EuclideanSpace.proj k|| <= 1, because |h_k| <= ||h|| for every h (PiLp.norm_apply_le). Hence ||iota_k|| <= 1.
3. Algebra of L o A. For fixed L, the map A -> L o A is additive: L o A - L o B = L o (A - B), since at any v we have L(A v) - L(B v) = L((A - B) v). Moreover ||L o A|| <= ||L|| ||A|| (ContinuousLinearMap.norm_compContinuousMultilinearMap_le).
4. Pointwise smoothness. U is open, so it is a neighbourhood of each z in U. Since g is C^m on U, g is C^m at every z in U (ContDiffOn.contDiffAt with IsOpen.mem_nhds). Each column g_k = ev_k o g is C^m on U, as a composition with a continuous linear map (g.clm_apply contDiffOn_const), and hence C^m at every z in U. Likewise iota_k o g_k is C^m at every z in U, because iota_k is C^infinity.
5. Column formula. For z in U and k in Fin n, D^m g_k(z) = ev_k o D^m g(z). This is ContinuousLinearMap.iteratedFDeriv_comp_left (Mathlib/Analysis/Calculus/ContDiff/Basic.lean:255) applied to L = ev_k and the map g, which is C^m at z by step 4, with order i = m <= m.
6. Proof of (i). Let x, y be in U and k in Fin n. By step 5 at x and at y, and by step 3, D^m g_k(x) - D^m g_k(y) = ev_k o (D^m g(x) - D^m g(y)). Hence, by step 3 and step 1, ||D^m g_k(x) - D^m g_k(y)|| <= ||ev_k|| ||D^m g(x) - D^m g(y)|| <= ||D^m g(x) - D^m g(y)||.
7. Reconstruction of g. For every T in L(R^n, E), T = sum_k iota_k(T e_k). Indeed, for h in R^n we have h = sum_k h_k . e_k (expansion in EuclideanSpace.basisFun (Fin n) R, whose k-th vector is e_k by EuclideanSpace.basisFun_apply), so T h = sum_k h_k . T e_k = (sum_k iota_k(T e_k)) h. Applying this with T = g(z) for every z gives the equality of functions g = (z -> sum_k iota_k(g_k(z))).
8. Sum formula. Let z be in U. By step 7, D^m g(z) = D^m(z' -> sum_k iota_k(g_k(z')))(z). Every summand z' -> iota_k(g_k(z')) is C^m at z by step 4. So the iterated derivative of the finite sum is the sum of the iterated derivatives (iteratedFDeriv_fun_sum_apply, Mathlib/Analysis/Calculus/ContDiff/Operations.lean:411). Each summand gives D^m(iota_k o g_k)(z) = iota_k o D^m g_k(z), by ContinuousLinearMap.iteratedFDeriv_comp_left with L = iota_k (g_k is C^m at z). Hence D^m g(z) = sum_k iota_k o D^m g_k(z).
9. Proof of (ii). Let x, y be in U. By step 8 at x and at y, Finset.sum_sub_distrib and step 3, D^m g(x) - D^m g(y) = sum_k iota_k o (D^m g_k(x) - D^m g_k(y)). By the triangle inequality for finite sums (norm_sum_le), step 3 and step 2: ||D^m g(x) - D^m g(y)|| <= sum_k ||iota_k|| ||D^m g_k(x) - D^m g_k(y)|| <= sum_k ||D^m g_k(x) - D^m g_k(y)||.
10. Steps 6 and 9 prove both claims for all x, y in U. If n = 0, Fin n is empty and claim (i) is vacuous. In (ii) the right side is the empty sum 0, and L(R^0, E) = {0} forces g = 0 identically, so D^m g = 0 and the left side is 0. Steps 7-9 cover this case without change. QED

## Key steps

1. ||ev_k|| <= 1 and ||iota_k|| <= 1; L o A - L o B = L o (A - B) and ||L o A|| <= ||L|| ||A||
2. U open: g, g_k = ev_k o g and iota_k o g_k are C^m at every point of U
3. D^m g_k(z) = ev_k o D^m g(z) (ContinuousLinearMap.iteratedFDeriv_comp_left), which gives bound (i)
4. g = sum_k iota_k o g_k, so D^m g(z) = sum_k iota_k o D^m g_k(z) (iteratedFDeriv_fun_sum_apply + comp_left), which gives bound (ii) by the triangle inequality

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; cmp GMT/Ch05/Contract.lean <snapshot>/project/GMT/Ch05/Contract.lean; cmp GMT/Ch05/Submission.lean <snapshot>/project/GMT/Ch05/Contract.lean`
- `rg -n -A6 'theorem contDiffOn_succ_iff_fderiv_of_isOpen' <snapshot>/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean; rg -n -A8 'theorem contDiffOn_clm_apply' .../ContDiff/FiniteDimension.lean; rg -n -A6 'theorem iteratedFDeriv_succ_eq_comp_right' .../ContDiff/FTaylorSeries.lean`
- `rg -n -A8 'theorem ContinuousLinearMap.iteratedFDerivWithin_comp_left|theorem ContinuousLinearMap.iteratedFDeriv_comp_left|theorem ContinuousLinearMap.norm_iteratedFDerivWithin_comp_left|theorem iteratedFDerivWithin_of_isOpen|theorem iteratedFDerivWithin_sum_apply|theorem iteratedFDeriv_sum|theorem iteratedFDerivWithin_sum' <snapshot>/mathlib/Mathlib/Analysis/Calculus/`
- `rg -n 'def smulRightL|theorem norm_smulRightL|theorem smulRightL_apply|def compContinuousMultilinearMapL|theorem norm_compContinuousMultilinearMap_le|theorem norm_apply_le|theorem basisFun_apply|theorem basisFun_repr|def basisFun|def proj ' over Analysis/Normed/Operator, Analysis/InnerProductSpace/PiL2.lean, Topology/Algebra/Module, Analysis/Normed/Module, Analysis/Normed/Lp`
- `rg -n 'EuclideanSpace.proj|abbrev proj' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean; sed -n 705,720p .../Analysis/Normed/Lp/PiLp.lean; rg -n 'theorem norm_smulRight_apply' .../Analysis/Normed/Operator/*.lean`
- `python3 scan of dag.json: all lean_name values (prefix dohr_eb, names containing holder/fderiv/partial/component/curry) and exact lean_statement equality with the three proposed child types; rg -l 'dohr_eb_hsif' <run>/dag.json <run>/nodes <snapshot>/project`
- `rg -n 'iteratedFDeriv_succ_eq_comp_right|compContinuousMultilinearMap|contDiffOn_clm_apply' <snapshot>/project/GMT lake-packages-25730c7c/simongmt/Poincare; grep -c 'Mathlib.Analysis.Calculus.ContDiff.FiniteDimension' <snapshot>/project/GMT/Ch05/Contract.lean`
- `grep -n 'holder_succ_iff_fderiv' in the speculative parent draft .swarm-worktrees/000e0c36def75b69b337/gmt-ch05/GMT/Ch05/Submission.lean (usage: .1.mpr / .1.mp)`
- `python3 gmt-compare.py contract_scope/child_modules (contract mode) to generate NodeChallenge/NodeSolution text for the 3 children and the parent`
- `LEAN_PATH=<shared lake-packages-25730c7c build dirs>:/tmp/hsif-decomp-jzApUd/build lean -o build/GMT/Ch05/Submission.olean src/Submission.lean (frozen file, Lean 4.35.0-rc3)`
- `lean checks/AllChallenges.lean (3 child types + frozen parent type in replayed scope, sorry bodies): exit 0, only sorry warnings`
- `lean checks/Assembly.lean (3 child types as axioms in GMT.Ch05.Submission, parent proved, #print axioms): exit 0`
- `lean checks/Full.lean (3 children proved, parent assembled, exact Submission.X targets, #print axioms): exit 0, 0 errors, no sorry`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-holder-su-d401bf599b/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Bounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Operator/Bilinear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Operator/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Module/Multilinear/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Algebra/Module/Multilinear/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/.swarm-worktrees/000e0c36def75b69b337/gmt-ch05/GMT/Ch05/Submission.lean`
- `/tmp/hsif-decomp-jzApUd/checks/AllChallenges.lean`
- `/tmp/hsif-decomp-jzApUd/checks/Assembly.lean`
- `/tmp/hsif-decomp-jzApUd/checks/Full.lean`

Snapshot pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The workspace Contract.lean and Submission.lean are byte-identical to the snapshot Contract, and HEAD is ea560759.

Pinned Mathlib declarations used by the children all exist:
- iteratedFDeriv_succ_eq_comp_right (ContDiff/FTaylorSeries.lean:926, with (continuousMultilinearCurryRightEquiv' 𝕜 n E F).symm)
- contDiffOn_succ_iff_fderiv_of_isOpen (ContDiff/Defs.lean:891, with an analyticity clause that is vacuous for finite m)
- ContinuousLinearMap.iteratedFDeriv_comp_left (ContDiff/Basic.lean:255, needs only ContDiffAt)
- iteratedFDeriv_fun_sum_apply (ContDiff/Operations.lean:411) and ContDiffOn.sum (Operations.lean:375)
- ContDiffOn.clm_apply (ContDiff/Comp.lean:500)
- ContinuousLinearMap.smulRightL (Normed/Operator/Bilinear.lean:511) and norm_smulRight_apply (Bilinear.lean:449)
- ContinuousLinearMap.norm_compContinuousMultilinearMap_le (Normed/Module/Multilinear/Basic.lean:919)
- EuclideanSpace.proj (PiL2.lean:285) and EuclideanSpace.basisFun_apply (PiL2.lean:806)
- PiLp.norm_apply_le (PiLp.lean:713)

contDiffOn_clm_apply (ContDiff/FiniteDimension.lean:52) exists, but its module is not in the frozen import closure ('Unknown identifier' in the scratch check). The children's proofs therefore use the iota_k reconstruction from the parent proof instead.

The project and simongmt contain no reusable column/currying Hölder lemma; simongmt Chapter06/Currents.lean only uses iteratedFDeriv_succ_eq_comp_right internally. No dohr_eb_hsif_* name exists in dag.json, the node directories or the snapshot, and no DAG node has a lean_statement equal to any proposed child type. The parent draft uses this node via .1.mpr/.1.mp, which is exactly child curry_succ_iff.

Lean checks in the scratch build all passed:
- AllChallenges: the 3 child types and the parent type elaborate in the replayed scope.
- Assembly: the parent type follows from the 3 child types as axioms.
- Full: the 3 children are proved, the parent depends only on propext, Classical.choice and Quot.sound, and the exact Submission.X targets close.
