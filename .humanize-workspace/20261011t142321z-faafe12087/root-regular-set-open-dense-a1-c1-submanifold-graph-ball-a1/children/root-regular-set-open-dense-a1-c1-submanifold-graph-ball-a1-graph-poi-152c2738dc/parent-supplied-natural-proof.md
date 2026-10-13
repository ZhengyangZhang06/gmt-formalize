# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_open_dense-a1.c1_submanifold_graph_ball-a1`
- Child DAG node: `root.regular_set_open_dense-a1.c1_submanifold_graph_ball-a1.graph_point_linear_equiv-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1 of the parent proof (G(x, y) := graphPoint x y = toLp 2 (Fin.append (ofLp x) (ofLp y)) is linear in the pair (x, y), hence a continuous linear map ℝⁿ × ℝ^ℓ → ℝ^{n+ℓ}, and G(x, y) determines x by comparing the first n coordinates, Fin.append_left); this child makes that precise by identifying G with the inverse of Mathlib's canonical equivalence, by comparing coordinates. Fix n, ℓ ∈ ℕ, x ∈ ℝⁿ, y ∈ ℝ^ℓ, let E := EuclideanSpace.finAddEquivProd : ℝ^{n+ℓ} ≃L[ℝ] ℝⁿ × ℝ^ℓ and w := E.symm (x, y).
1. (Coordinates of E.) By its definition (Mathlib/Analysis/InnerProductSpace/PiL2.lean, section finAddEquivProd), E is the composite of the coordinate reindexing LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv.symm : EuclideanSpace ℝ (Fin (n+ℓ)) → EuclideanSpace ℝ (Fin n ⊕ Fin ℓ), which sends z to the vector b ↦ z (finSumFinEquiv b), with EuclideanSpace.sumEquivProd, which splits a vector indexed by Fin n ⊕ Fin ℓ into its Sum.inl-part and its Sum.inr-part. Since finSumFinEquiv (Sum.inl j) = Fin.castAdd ℓ j and finSumFinEquiv (Sum.inr k) = Fin.natAdd n k (finSumFinEquiv_apply_left/right), for every z ∈ ℝ^{n+ℓ} we get E z = ((z (Fin.castAdd ℓ j))_{j : Fin n}, (z (Fin.natAdd n k))_{k : Fin ℓ}).
2. (Coordinates of w.) Since E is an equivalence, E w = E (E.symm (x, y)) = (x, y). Applying the formula of step 1 to z = w gives (w (Fin.castAdd ℓ j))_{j : Fin n} = x and (w (Fin.natAdd n k))_{k : Fin ℓ} = y, i.e. w (Fin.castAdd ℓ j) = x_j for all j : Fin n and w (Fin.natAdd n k) = y_k for all k : Fin ℓ.
3. (Coordinates of graphPoint x y.) By definition (graphPoint x y)(i) = Fin.append (ofLp x) (ofLp y) i for all i : Fin (n+ℓ), so (graphPoint x y)(Fin.castAdd ℓ j) = x_j (Fin.append_left) and (graphPoint x y)(Fin.natAdd n k) = y_k (Fin.append_right).
4. (Conclusion.) Two vectors of EuclideanSpace ℝ (Fin (n+ℓ)) are equal as soon as all their coordinates agree (ext), and every index i : Fin (n+ℓ) is of the form Fin.castAdd ℓ j with j : Fin n or Fin.natAdd n k with k : Fin ℓ (Fin.addCases). By steps 2 and 3 the coordinates of graphPoint x y and of w agree in both cases. Hence graphPoint x y = w = E.symm (x, y). (Lean outline, checked against the pinned Mathlib: ext i; refine Fin.addCases (fun j => ?_) (fun k => ?_) i, then simp [graphPoint] closes each case.)

## Key steps

1. E = finAddEquivProd (piLpCongrLeft finSumFinEquiv.symm followed by sumEquivProd) sends z to ((z (castAdd ℓ j))_j, (z (natAdd n k))_k)
2. E w = (x, y) for w := E.symm (x, y), so w (castAdd ℓ j) = x_j and w (natAdd n k) = y_k
3. Coordinates of graphPoint x y: castAdd ℓ j ↦ x_j, natAdd n k ↦ y_k (Fin.append_left/right)
4. ext + Fin.addCases: all coordinates agree, so graphPoint x y = E.symm (x, y)

## Reference use

### local-project

Queries:
- `grep -n 'graphPoint\|graphOver\|IsC1Submanifold\|def \|abbrev \|structure \|^theorem\|namespace\|^open' <snapshot>/project/GMT/Ch05/Contract.lean; diff <snapshot>/project/GMT/Ch05/Contract.lean <snapshot>/project/GMT/Ch05/Submission.lean`
- `rg -n 'Fin.append' Mathlib -t lean -l  (in <snapshot>/mathlib)`
- `rg -n 'finAddEquivProd|appendEquiv|appendIsometry|appendLinear|sumPiLp|appendHomeomorph' Mathlib -t lean`
- `rg -n 'theorem norm_eq|theorem nnnorm_eq|theorem norm_sq_eq|lemma norm_eq' Mathlib/Analysis/InnerProductSpace/PiL2.lean; sed -n 330,420p Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `rg -n 'theorem EuclideanSpace.real_norm_sq_eq|abbrev EuclideanSpace.finAddEquivProd' Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `rg -n 'theorem sum_univ_add|theorem prod_univ_add' Mathlib/Algebra/BigOperators/Fin.lean; rg -n 'theorem append_left|theorem append_right' Mathlib/Data/Fin/Tuple/Basic.lean`
- `rg -n 'theorem ContinuousOn.isOpen_inter_preimage|theorem ContinuousOn.preimage_isClosed_of_isClosed' Mathlib/Topology; rg -n 'theorem IsCompact.of_isClosed_subset' Mathlib/Topology`
- `rg -n 'theorem ContDiffOn.contDiffAt' Mathlib/Analysis/Calculus; rg -n 'theorem HasFDerivAt.prodMk' Mathlib/Analysis/Calculus/FDeriv; rg -n 'theorem finSumFinEquiv_apply_left|theorem finSumFinEquiv_apply_right' Mathlib`
- `grep -rhoE '(theorem|lemma) [A-Za-z_.0-9]+' --include=*.lean .swarm-worktrees/*/gmt-ch05/GMT; grep -rhoE '^(theorem|lemma|def|noncomputable def|abbrev) [A-Za-z_.0-9]*[gG]raph[A-Za-z_.0-9]*' --include=*.lean .swarm-worktrees/*/gmt-ch05`
- `grep -rlE 'rsod_norm_graphPoint_sq|rsod_graphPoint_eq_finAddEquivProd_symm|rsod_graphChart_injective_contDiffOn_fderiv_injective' gmt-ch05/.humanize .swarm-worktrees/*/gmt-ch05/GMT (name-collision check)`
- `python3 over runs/.../dag.json: list lean_name/lean_statement of all 60 nodes (incl. exists_open_graph_domain_of_closedBall_graph, rsod_isC1Submanifold_open_inter)`
- `grep -n -i submanifold book/chapter-02.txt; sed -n 849,895p book/chapter-02.txt`
- `lean -o build/GMT/Ch05/Submission.olean GMT/Ch05/Submission.lean (scratch /tmp/c1gb-check, snapshot copy); /tmp/c1gb-check/run.sh T/All2.lean (full proofs + #print axioms); reviewer: review/Review1.lean (comparator scope), review/Review2.lean (children as sorry)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Algebra/BigOperators/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Logic/Equiv/Fin/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Isometry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Homeomorph/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/ContinuousOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-c1-submanifold-graph-ball-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/c1gb-check/draft/All2.lean`
- `/tmp/c1gb-check/review/Review1.lean`
- `/tmp/c1gb-check/review/Review2.lean`

The snapshot is pinned at project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. Contract.lean and Submission.lean are identical.

No prior work to reuse: no graphPoint or graphOver lemmas exist in the project snapshot or in any of the 22 Ch05 swarm worktrees. Their only declarations are the frozen defs. None of the three proposed names appears anywhere in the run, the snapshot or the worktrees.

Usable Mathlib items:
- EuclideanSpace.finAddEquivProd (PiL2.lean:378), defined as piLpCongrLeft finSumFinEquiv.symm followed by sumEquivProd. graphPoint x y = finAddEquivProd.symm (x, y) holds by ext with Fin.addCases and simp [graphPoint].
- EuclideanSpace.real_norm_sq_eq (PiL2.lean:153).
- Fin.sum_univ_add (to_additive of prod_univ_add, Algebra/BigOperators/Fin.lean:159).
- Fin.append_left and Fin.append_right (Data/Fin/Tuple/Basic.lean:312 and 323).
- finSumFinEquiv_apply_left and finSumFinEquiv_apply_right (Logic/Equiv/Fin/Basic.lean:231 and 236).
- ContinuousOn.isOpen_inter_preimage and ContinuousOn.preimage_isClosed_of_isClosed (Topology/ContinuousOn.lean:188 and 197).
- IsCompact.of_isClosed_subset (Compactness/Compact.lean:105).
- ContDiffOn.contDiffAt (ContDiff/Defs.lean:962).
- HasFDerivAt.prodMk (FDeriv/Prod.lean:70).

Mathlib does not package graphPoint itself, so the two graphPoint lemmas are new obligations.

Simon Ch. 2 §4 (4.1) matches the contract's IsC1Submanifold.

Lean check (scratch build of the snapshot Submission, Lean v4.35.0-rc3): /tmp/c1gb-check/draft/All2.lean proves all three children and the parent with 0 sorry and only the axioms propext, Classical.choice and Quot.sound. Review1.lean elaborates the frozen types in the comparator scope, and Review2.lean shows the parent compiles from the three child types alone.
