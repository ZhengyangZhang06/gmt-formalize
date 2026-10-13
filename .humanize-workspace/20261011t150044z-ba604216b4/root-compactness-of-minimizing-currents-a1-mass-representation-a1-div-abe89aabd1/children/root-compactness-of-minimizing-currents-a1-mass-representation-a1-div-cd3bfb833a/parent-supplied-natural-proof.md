# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.divergence_form-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.divergence_form-a1.contraction_extderiv-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 2 (derivative of η). Here b and G are arbitrary maps that are differentiable at the point x. The parent applies it at every x with G := ι ∘ g ∘ p, which is C^∞.

Notation.
- C := θ.curryLeft = ContinuousAlternatingMap.curryLeft θ : ℝ^P →L[ℝ] Covector(ℝ^P, m). This is a continuous linear map, and C(u)(v) = θ(Matrix.vecCons u v) = θ(Fin.cons u v) for u ∈ ℝ^P and v : Fin m → ℝ^P (ContinuousAlternatingMap.curryLeft_apply_apply).
- η(y) := b(y)•C(G y) ∈ Covector(ℝ^P, m).
- Fix w : Fin (m+1) → ℝ^P.

1. (Derivative of η.) The map y ↦ C(G y) is differentiable at x with derivative C ∘L DG(x). This is the chain rule for the continuous linear map C, whose derivative is C itself (ContinuousLinearMap.fderiv, fderiv_fun_comp). By the product rule for a scalar function times a vector-valued function (fderiv_fun_smul), η is differentiable at x, and for all h ∈ ℝ^P:
 Dη(x)h = b(x)•C(DG(x)h) + Db(x)h•C(G x).

2. (Exterior derivative formula.) η is differentiable at x, so the exterior derivative formula (Poincare.SimonGMT.Chapter06.exteriorDerivative_apply) gives
 dη(x)(w) = Σ_{i ∈ Fin (m+1)} (−1)^i • D_x[y ↦ η(y)(i.removeNth w)](w i).
 Here (−1)^i is an integer acting on ℝ.

3. (Differentiating an evaluation.) Fix a tuple v : Fin m → ℝ^P. Evaluation at v is a continuous linear map on m-covectors (ContinuousAlternatingMap.apply). So y ↦ η(y)(v) is differentiable at x, and D_x[y ↦ η(y)(v)](h) = (Dη(x)h)(v) for all h (fderiv_continuousAlternatingMap_apply_const_apply).

4. (Evaluating the derivative.) By steps 1 and 3 and the formula for C:
 D_x[y ↦ η(y)(v)](h) = b(x)·θ(Fin.cons (DG(x)h) v) + Db(x)h·θ(Fin.cons (G x) v).

5. (Conclusion.) Take h := w i and v := i.removeNth w in step 4, and substitute into step 2. Write the integer (−1)^i as the real number (−1)^i (zsmul_eq_mul) and reorder the two summands. This gives
 dη(x)(w) = Σ_i (−1)^i·[Db(x)(w i)·θ(Fin.cons (G x) (i.removeNth w)) + b(x)·θ(Fin.cons (DG(x)(w i)) (i.removeNth w))],
 which is the claim.

Lean route (compiled, about 25 lines).
- Differentiability: hη := hb.smul ((ContinuousAlternatingMap.curryLeft θ).differentiableAt.comp x hG).
- `rw [exteriorDerivative_apply hη w]`, then Finset.sum_congr rfl, then `rw [fderiv_continuousAlternatingMap_apply_const_apply hη]`.
- Rewrite fderiv ℝ η x using fderiv_fun_smul hb hc, fderiv_fun_comp x (ContinuousAlternatingMap.curryLeft θ).differentiableAt hG, and ContinuousLinearMap.fderiv.
- Finish with `simp only` using the root lemmas add_apply and smul_apply (ContinuousLinearMap.add_apply and ContinuousLinearMap.smul_apply are deprecated aliases), ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.smulRight_apply, ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.curryLeft_apply_apply, smul_eq_mul and zsmul_eq_mul. Then `simp only [Matrix.vecCons]`, `push_cast` and `ring`.

## Key steps

1. η = b•(θ.curryLeft ∘ G) is differentiable at x, with Dη(x)h = b(x)•θ.curryLeft(DG(x)h) + Db(x)h•θ.curryLeft(G x) (chain rule for the CLM θ.curryLeft, product rule).
2. exteriorDerivative_apply: dη(x)(w) = Σ_i (−1)^i D_x[η(·)(i.removeNth w)](w i).
3. Differentiation commutes with evaluation at a fixed tuple (fderiv_continuousAlternatingMap_apply_const_apply), and θ.curryLeft u v = θ(Fin.cons u v). Substitute h = w i and v = i.removeNth w.

## Reference use

### local-project

Queries:
- `cmp GMT/Ch07/Contract.lean .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical); git rev-parse HEAD in lake-packages-25730c7c/simongmt (2b3663083f3f) and .lake/packages/mathlib (25730c7c759d)`
- `cmp -s of 16 cited Mathlib files between local-references/123e8435b4a2469b/mathlib and lake-packages-25730c7c/mathlib (all identical)`
- `grep -n 'def Covector|abbrev Covector|def DifferentialForm|abbrev DifferentialForm|def IsTestForm|def covectorEuclideanNorm|def exteriorDerivative|theorem exteriorDerivative_apply' simongmt/Poincare/SimonGMT/Chapter06/*.lean`
- `grep -rn 'Leibniz|extDeriv_smul|smul_extDeriv|curryLeft' simongmt/Poincare/SimonGMT; grep '^theorem|^def' Chapter06/WedgeForms.lean (no Leibniz rule for b•ω; curryLeft unused)`
- `grep -n '^theorem|^lemma|^def' mathlib/Mathlib/Analysis/Calculus/DifferentialForm/*.lean (extDeriv = alternatizeUncurryFin ∘ fderiv; extDeriv_apply/add/smul; no product rule)`
- `grep -rn 'def curryLeft|norm_curryLeft|curryLeft_apply_apply' and 'insertNth' in Mathlib/LinearAlgebra/Alternating and Mathlib/Analysis/Normed/Module/Alternating; sed Analysis/Normed/Module/Alternating/Uncurry/Fin.lean (map_insertNth, alternatizeUncurryFin_apply, norm_alternatizeUncurryFin_le)`
- `grep -rn trace Mathlib/LinearAlgebra/Matrix/Determinant/*.lean Mathlib/LinearAlgebra/Matrix/Charpoly/*.lean (only derivative_det_one_add_X_smul, det_one_add_smul); grep det_updateCol_*, AlternatingMap.eq_smul_basis_det, LinearMap.trace_eq_matrix_trace, cramer_apply, cramer_eq_adjugate_mulVec, mul_adjugate, trace_mul_comm, toMatrix_mulVec_repr, Basis.det_apply, AlternatingMap.map_swap`
- `grep -n continuousAlternatingMap_apply_const Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean; grep 'def apply' Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `grep Continuous.bounded_above_of_compact_support, fderiv_of_notMem_tsupport, HasCompactSupport.fderiv, HasCompactSupport.mono', HasCompactSupport.smul_right, tsupport_smul_subset_left in Mathlib`
- `python3 -I scan of dag.json: lean_statements mentioning covectorEuclideanNorm with an operator norm, exteriorDerivative/extDeriv/alternatizeUncurryFin/curryLeft, or LinearMap.trace with det; lean_name lookup for cmr_df_* (none) and rsd_mw_tfa_norm_props (accepted, candidate f492ba4a)`
- `git show 9dcae6bdd56d (accepted dgcr_bwd_extDeriv_smul_const Lean proof); git show f492ba4a003c:GMT/Ch07/Submission.lean (accepted rsd_mw_tfa_norm_props Lean proof)`
- `find workspaces -maxdepth 6 -name Submission.lean -path '*Ch07*' (689 files) | xargs grep -l cmr_df_ (no match)`
- `grep -n 'def _existing_lean_name_problem|def _accepted_checkpoint' _recursive_lean/runtime.py; contract_scope and child_modules in verifier/gmt-compare.py; validate_lean_statement from _recursive_lean/lean_contract.py on all four statements (pass)`
- `lake env lean /tmp/cmr-div-split/Stmts.lean Assembly.lean Children.lean JacobiAlt.lean Full.lean gen/Final.lean gen2/Final2.lean; reviewer: lake env lean /tmp/cmr-div-review/FinalCopy.lean Mine.lean JacobiAdj.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-div-abe89aabd1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-mass-eq-weight-a1-test-form-approx-a1-norm-props-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/WedgeForms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/Charpoly/Coeff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/Adjugate.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/ToLin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/cmr-div-split/Stmts.lean`
- `/tmp/cmr-div-split/Assembly.lean`
- `/tmp/cmr-div-split/Children.lean`
- `/tmp/cmr-div-split/JacobiAlt.lean`
- `/tmp/cmr-div-split/Full.lean`
- `/tmp/cmr-div-split/gen/Final.lean`
- `/tmp/cmr-div-split/gen2/Final2.lean`
- `/tmp/cmr-div-split/gen/decomposition_draft.json`

Pinned sources. The snapshot contract (project b4d606db, Mathlib 25730c7c) is byte-identical to the workspace Contract.lean and Submission.lean. SimonGMT is pinned at 2b366308. All 16 cited Mathlib files are byte-identical between the snapshot and the build tree.

Available and used. Mathlib provides:
- extDeriv = alternatizeUncurryFin ∘ fderiv, with extDeriv_apply (wrapped by SimonGMT exteriorDerivative_apply);
- ContinuousAlternatingMap.map_insertNth and Fin.insertNth_removeNth, which together are the parent's (F2);
- ContinuousAlternatingMap.curryLeft with norm_curryLeft;
- fderiv_continuousAlternatingMap_apply_const_apply;
- AlternatingMap.eq_smul_basis_det, LinearMap.trace_eq_matrix_trace and the cramer/adjugate lemmas;
- support and bound lemmas: fderiv_of_notMem_tsupport, HasCompactSupport.mono', Continuous.bounded_above_of_compact_support.

Not available (no match), so these became children:
- Jacobi's column-replacement identity Σ_i det(update) = tr·det. Mathlib has only derivative_det_one_add_X_smul, for polynomial matrices.
- Any Leibniz or contraction formula for extDeriv(b•θ.curryLeft∘G). SimonGMT has no Leibniz rule and does not use curryLeft.

DAG.
- The accepted theorem rsd_mw_tfa_norm_props (candidate f492ba4a) supplies (F1). It is reused with its byte-identical type.
- The accepted dgcr_bwd_extDeriv_smul_const is the constant-covector analogue of the contraction child. It served as a model but is not needed.
- No cmr_df_* name occurs in dag.json or in any of the 689 Ch07 Submission.lean worktrees.

Lean checks, after import GMT.Ch07.Submission in the comparator scope:
- The four child types elaborate and pass validate_lean_statement.
- The verbatim parent type is proved from the four children.
- Complete proofs of the three new children compile.
- The whole chain is sorry-free, and #print axioms gives only propext, Classical.choice and Quot.sound.
- An independent reviewer reproduced these checks and accepted.
