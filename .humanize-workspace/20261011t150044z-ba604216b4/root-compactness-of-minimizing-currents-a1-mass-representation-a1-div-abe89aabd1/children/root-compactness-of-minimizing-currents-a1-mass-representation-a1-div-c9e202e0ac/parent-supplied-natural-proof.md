# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.divergence_form-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.divergence_form-a1.coordinate_trace-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 3 (S_x = tr(Dg(p x))·θ) together with fact (F2). Here L is an arbitrary map in place of DG(x), and A an arbitrary linear map in place of Dg(p x). The parent applies it with A := (fderiv ℝ g (p x)).toLinearMap and L := fderiv ℝ G x = ι ∘ Dg(p x) ∘ p. Then (L v)(I k) = (Dg(p x)(p v))_k, because (ι y)(I k) = y_k.

Notation.
- n := m + 1.
- For v ∈ ℝ^P, p v := WithLp.toLp 2 (fun k => v (I k)) ∈ ℝⁿ, so (p v)_k = v(I k).
- For v : Fin n → ℝⁿ, D(v) := det(Matrix.of fun k j => v j k).
- Fix w : Fin n → ℝ^P and put u_j := p(w j) ∈ ℝⁿ for j ∈ Fin n.

1. (Sign rule; parent fact (F2).) For every i ∈ Fin n and x ∈ ℝ^P,
 (−1)^i·θ(Fin.cons x (i.removeNth w)) = θ(Function.update w i x).
 Proof.
 - Function.update w i x = i.insertNth x (i.removeNth w) (Fin.insertNth_removeNth).
 - For a continuous alternating map, θ(i.insertNth x v) = (−1)^i • θ(Matrix.vecCons x v) (ContinuousAlternatingMap.map_insertNth). The tuple i.insertNth x v comes from Matrix.vecCons x v by moving the entry in position 0 to position i. This is a cyclic permutation of the positions 0, …, i, of sign (−1)^i.
 - Matrix.vecCons x v is Fin.cons x v by definition. The integer (−1)^i acts on ℝ as multiplication by the real number (−1)^i (zsmul_eq_mul).
 Apply this with x := L(w i):
 (−1)^i·θ(Fin.cons (L(w i)) (i.removeNth w)) = θ(Function.update w i (L(w i))).

2. (Coordinate form of each term.) Fix i. By the hypothesis on θ, θ(Function.update w i (L(w i))) = det N with N_{k,j} := (Function.update w i (L(w i)) j)(I k). Let N' be the matrix of D(Function.update u i (A(u i))), so N'_{k,j} := (Function.update u i (A(u i)) j)_k. We compare entries.
 - If j = i: N_{k,i} = (L(w i))(I k) = (A(p(w i)))_k = (A(u i))_k = N'_{k,i}. This is the hypothesis on L with v := w i.
 - If j ≠ i: N_{k,j} = (w j)(I k) = (p(w j))_k = (u j)_k = N'_{k,j}.
 So N = N', and θ(Function.update w i (L(w i))) = D(Function.update u i (A(u i))).

3. (Jacobi.) Sum steps 1 and 2 over i, and apply the sibling theorem cmr_df_det_update_sum_trace (Jacobi's identity) to n, A and u:
 Σ_i (−1)^i·θ(Fin.cons (L(w i)) (i.removeNth w)) = Σ_i D(Function.update u i (A(u i))) = tr(A)·D(u).

4. (Back to θ.) By the hypothesis on θ, D(u) = det(Matrix.of fun k j => (u j)_k) = det(Matrix.of fun k j => w j (I k)) = θ(w). So the sum equals tr(A)·θ(w) = LinearMap.trace ℝ (Euclid (m+1)) A · θ(w).

Remarks.
- (i) The proof does not use that I is injective or monotone.
- (ii) Lean route (compiled). Step 1: `rw [← Fin.insertNth_removeNth, ContinuousAlternatingMap.map_insertNth]`, then `zsmul_eq_mul` with `push_cast`, then `rfl`, since Matrix.vecCons = Fin.cons. Step 2: `rw [hθ]; congr 1; ext k j`, then `by_cases hj : j = i` with `simp [hL]`. Finally `simp_rw` the two steps, `rw` the sibling theorem, and finish with `hθ`.

## Key steps

1. (−1)^i·θ(Fin.cons (L(w i)) (i.removeNth w)) = θ(Function.update w i (L(w i))), by Fin.insertNth_removeNth and ContinuousAlternatingMap.map_insertNth.
2. With u_j := p_I(w j), the hypothesis (L v)(I k) = (A(p_I v))_k gives θ(Function.update w i (L(w i))) = D(Function.update u i (A(u i))), entry by entry.
3. Jacobi's identity (sibling cmr_df_det_update_sum_trace) gives Σ_i D(Function.update u i (A(u i))) = tr(A)·D(u).
4. D(u) = θ(w), by the formula for θ.

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
