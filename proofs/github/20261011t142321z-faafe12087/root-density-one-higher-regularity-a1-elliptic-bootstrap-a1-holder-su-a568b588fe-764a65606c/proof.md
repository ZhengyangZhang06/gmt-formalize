# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.holder_succ_iff_fderiv-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.holder_succ_iff_fderiv-a1.clm_columns_contdiff-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1 (second half) of the parent proof of dohr_eb_holder_succ_iff_fderiv ('by linearity in v it suffices to take v in {e_1,...,e_n}, because Df(x) = sum_k iota_k(D_k f(x)) where iota_k ... is a fixed continuous linear map'), stated for an arbitrary map g into L(R^n, E).
Notation. R^n = Rn n = EuclideanSpace R (Fin n). e_k = EuclideanSpace.single k 1 for k in Fin n. For h in R^n, h_k = h k is its k-th coordinate. 'C^m on U' means ContDiffOn R m . U, with m : N cast into WithTop N-infinity. U is an arbitrary subset of R^n. For k in Fin n put g_k(x) := g(x) e_k.
1. Fixed continuous linear maps. ev_k : L(R^n, E) -> E, T -> T e_k, is continuous linear (ContinuousLinearMap.apply R E e_k), and g_k = ev_k o g. iota_k : E -> L(R^n, E), iota_k(w) := (h -> h_k . w), is continuous linear: iota_k = ContinuousLinearMap.smulRightL R (Rn n) E (EuclideanSpace.proj k) (Mathlib/Analysis/Normed/Operator/Bilinear.lean:511; by smulRightL_apply_apply, iota_k w h = h_k . w).
2. Reconstruction identity. For every T in L(R^n, E), T = sum_{k in Fin n} iota_k(T e_k). To see this, let h be in R^n and expand h in the orthonormal basis EuclideanSpace.basisFun (Fin n) R. Its k-th vector is e_k (EuclideanSpace.basisFun_apply) and its k-th coordinate is h_k, so h = sum_k h_k . e_k. By linearity of T, T h = sum_k h_k . T e_k = (sum_k iota_k(T e_k)) h. For n = 0 both sides are the zero map. (Lean: ext h; rw [ContinuousLinearMap.sum_apply]; simp only [ContinuousLinearMap.smulRightL_apply_apply]; conv_lhs => rw [<- (EuclideanSpace.basisFun (Fin n) R).sum_repr h]; simp [map_sum, map_smul, EuclideanSpace.basisFun_apply].)
3. (=>) Suppose g is C^m on U and let k be in Fin n. Then g_k = ev_k o g is C^m on U, because composing a map that is C^m on U with a continuous linear map gives a map that is C^m on U. (Lean: hg.clm_apply contDiffOn_const, Mathlib/Analysis/Calculus/ContDiff/Comp.lean:500.)
4. (<=) Suppose every g_k is C^m on U. Applying step 2 to T = g(x) for each x in R^n gives the equality of functions g = (x -> sum_k iota_k(g_k(x))). For each k, the map x -> iota_k(g_k(x)) is C^m on U: it is the continuous linear map iota_k, which is C^infinity (ContinuousLinearMap.contDiff), composed with g_k (ContDiff.comp_contDiffOn). A finite sum of maps that are C^m on U is C^m on U (ContDiffOn.sum, Mathlib/Analysis/Calculus/ContDiff/Operations.lean:375). Hence g is C^m on U.
5. Steps 3 and 4 prove the equivalence. QED
(The argument uses only the imports of the frozen contract. Mathlib's contDiffOn_clm_apply lives in Mathlib.Analysis.Calculus.ContDiff.FiniteDimension, which is not imported there, and is not needed.)

## Key steps

1. g_k = ev_k o g with ev_k = ContinuousLinearMap.apply R E e_k continuous linear, which gives the (=>) direction
2. reconstruction T = sum_k iota_k(T e_k) with iota_k = smulRightL R (Rn n) E (EuclideanSpace.proj k), via the EuclideanSpace.basisFun expansion of h
3. g = sum_k iota_k o g_k; continuous linear images and finite sums of C^m maps are C^m, which gives the (<=) direction

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
