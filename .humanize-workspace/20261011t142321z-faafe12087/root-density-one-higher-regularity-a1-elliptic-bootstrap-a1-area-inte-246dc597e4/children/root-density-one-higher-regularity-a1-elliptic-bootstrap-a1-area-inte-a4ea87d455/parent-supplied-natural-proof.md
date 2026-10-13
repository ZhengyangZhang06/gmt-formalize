# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.area_integrand_legendre-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.area_integrand_legendre-a1.hessian_local_unif-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Write H(x) := fderiv ℝ (fderiv ℝ F) x, an element of the normed space E →L[ℝ] (E →L[ℝ] ℝ) of bounded bilinear forms with the operator norm.

1. Continuity of H. F is C^2, so DF = fderiv ℝ F is C^1 (ContDiff.fderiv_right, since 1 + 1 <= 2). Hence its derivative H is continuous (ContDiff.continuous_fderiv, as 1 != 0).

2. Choice of eps. By continuity of H at x0 there is r > 0 with ||H(x) - H(x0)|| < delta whenever dist(x, x0) = ||x - x0|| < r. Put eps := r/2 > 0. If ||x - x0|| <= eps then ||x - x0|| < r, so ||H(x) - H(x0)|| < delta.

3. Bilinear estimate. Let B := H(x) - H(x0). For all Q, Q': B Q Q' = H(x) Q Q' - H(x0) Q Q', since subtraction of continuous linear maps is pointwise (applied twice). Also |B Q Q'| <= ||B|| ||Q|| ||Q'|| (ContinuousLinearMap.le_opNorm₂).

4. Conclusion. For ||x - x0|| <= eps and all Q, Q': |H(x) Q Q' - H(x0) Q Q'| <= ||H(x) - H(x0)|| ||Q|| ||Q'|| <= delta (||Q|| ||Q'||). QED

Source: parent step 6 (continuity of D^2J gives eps with error at most 1/2). The parent's coordinate version (basis E_1..E_N of L, constant c_L) only worked around instance synthesis on the concrete bilinear-form type over L. For a type variable E the operator norm on E →L[ℝ] E →L[ℝ] ℝ is directly available, so no finite-dimensionality is needed.

Lean note (checked at the pin; a complete proof compiled):
- `have hc : Continuous (fderiv ℝ (fderiv ℝ F)) := (hF.fderiv_right (by norm_num)).continuous_fderiv (by norm_num)`.
- `obtain ⟨r, hr, hball⟩ := (Metric.continuousAt_iff (f := fderiv ℝ (fderiv ℝ F)) (a := x₀)).mp hc.continuousAt δ hδ`. Without the explicit `(f := …)`, the topology of the operator type fails to unify.
- Convert dist to the norm with `lt_of_eq_of_lt (@dist_eq_norm (E →L[ℝ] E →L[ℝ] ℝ) _ _ _).symm (hball hdist)`. A plain `rw [dist_eq_norm]` does not fire on this type.
- `have key := (fderiv ℝ (fderiv ℝ F) x - fderiv ℝ (fderiv ℝ F) x₀).le_opNorm₂ Q Q'`, then `simp only [ContinuousLinearMap.sub_apply, Real.norm_eq_abs] at key`.
- Finish with `rw [mul_assoc]; exact mul_le_mul_of_nonneg_right hlt.le (by positivity)`.

## Key steps

1. C^2 makes x -> fderiv (fderiv F) x continuous in the operator norm
2. continuity at x0 gives r; with eps = r/2, ||H(x) - H(x0)|| < delta when ||x - x0|| <= eps
3. |B Q Q'| <= ||B|| ||Q|| ||Q'|| for B = H(x) - H(x0), with B Q Q' = H(x)QQ' - H(x0)QQ'
4. hence |H(x)QQ' - H(x0)QQ'| <= delta (||Q|| ||Q'||)

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; cmp GMT/Ch05/Contract.lean <snapshot>/project/GMT/Ch05/Contract.lean; cmp GMT/Ch05/Submission.lean <snapshot>/project/GMT/Ch05/Contract.lean`
- `grep -rn 'det_one_add_smul|det_one_add_X_smul|PosDef.det_pos|posSemidef_gram|add_posSemidef|posSemidef_conjTranspose_mul_self|dotProduct_self_eq_zero' <snapshot>/mathlib/Mathlib`
- `grep -rn 'ContDiff.continuous_fderiv|ContDiff.fderiv_right|le_opNorm₂|ContDiff.sqrt|contDiffAt_sqrt|ContDiff.sum|contDiff_prod|contDiff_det|Matrix.det' <snapshot>/mathlib/Mathlib/Analysis/Calculus`
- `grep -rn 'HasDerivAt.fun_|HasDerivAt.pow|HasDerivAt.div|HasDerivAt.clm_apply|HasDerivAt.sqrt|EventuallyEq.deriv_eq|Continuous.matrix_det|intermediate_value_Icc|exists_mulVec_eq_zero_iff|opNorm_le_bound' <snapshot>/mathlib/Mathlib`
- `#check under `import GMT.Ch05.Submission`: Matrix.PosDef, Matrix.PosSemidef, Matrix.PosDef.det_pos, Matrix.posSemidef_conjTranspose_mul_self, Matrix.gram, Matrix.IsHermitian, Matrix.det_one_add_smul, Matrix.exists_mulVec_eq_zero_iff, intermediate_value_Icc', Continuous.matrix_det, Polynomial.hasDerivAt, HasDerivAt.sqrt, Filter.EventuallyEq.deriv_eq, ContDiff.inner, ContDiff.sum, contDiff_prod, HasDerivAt.clm_apply, Real.sum_mul_le_sqrt_mul_sqrt`
- `python3 scan of dag.json lean_name / lean_statement values (dohr_eb_ail_*, opNorm/hsNorm lemmas, area integrand nodes); grep -rl dohr_eb_ail nodes <snapshot>/project`
- `git show d6f38af2 and 8ce39d78 (accepted dohr_vel_linear_graph_area / dohr_vel_area_integrand_fderiv: Submission imports unchanged)`
- `lake build GMT.Ch05.Submission in scratch /tmp/ail-decomp-8LoHju/proj (shared lake-packages-25730c7c)`
- `lake env lean Checks/Children.lean (7 child types in the replay scope computed by verifier/gmt-compare.py contract_scope)`
- `lake env lean Checks/Assembly.lean (parent type and hessian_at_zero from children posed as axioms; #print axioms)`
- `lake env lean Checks/EndToEnd.lean (complete proofs of all 7 children and the parent, plus `exact Submission.X` targets; #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/LinearAlgebra/Matrix/Charpoly/Coeff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/LinearAlgebra/Matrix/PosDef.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/GramMatrix.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/LinearAlgebra/Matrix/DotProduct.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/LinearAlgebra/Matrix/ToLinearEquiv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Instances/Matrix.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Order/IntermediateValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Sqrt.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Operator/Bilinear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Deriv/Pow.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`

The snapshot pins project ea560759 and Mathlib 25730c7c, and the workspace Contract.lean and Submission.lean are byte-identical to the snapshot Contract.

Available: Matrix.det_one_add_smul (Charpoly/Coeff.lean:207).

Not importable: Matrix.PosDef.det_pos (PosDef.lean:549), Matrix.posSemidef_gram (GramMatrix.lean:82) and dotProduct_self_eq_zero (DotProduct.lean:77) exist in the pinned Mathlib. They are NOT imported by GMT.Ch05.Submission (#check reports unknown constants for Matrix.PosDef, PosSemidef, gram and IsHermitian), and the accepted candidates d6f38af2 and 8ce39d78 leave the imports unchanged. The parent's step 1 is therefore re-proved for the child via Matrix.exists_mulVec_eq_zero_iff (ToLinearEquiv.lean), Continuous.matrix_det (Topology/Instances/Matrix.lean:212) and intermediate_value_Icc' (Topology/Order/IntermediateValue.lean:592).

No smoothness lemma for Matrix.det exists, so smoothness goes through Matrix.det_apply, ContDiff.sum (ContDiff/Operations.lean:381), contDiff_prod (:496), ContDiff.inner and ContDiff.sqrt (Sqrt.lean:164).

Calculus used:
- ContDiff.fderiv_right (ContDiff/Comp.lean:750)
- ContDiff.continuous_fderiv (ContDiff/Defs.lean:1271)
- le_opNorm₂ (Normed/Operator/Bilinear.lean:71)
- opNorm_le_bound (Normed/Operator/Basic.lean:196)
- HasDerivAt.clm_apply (Deriv/Mul.lean:630)
- HasDerivAt.sqrt (Sqrt.lean:84)
- HasDerivAt.fun_pow (to_fun of Deriv/Pow.lean:109)
- HasDerivAt.fun_div (Deriv/Inv.lean:168)
- Filter.EventuallyEq.deriv_eq (Deriv/Basic.lean:638)

Naming: no dohr_eb_ail_* name exists in dag.json, the node directories or the snapshot. An accepted cousin of opnorm_sq_le_hs exists in another branch (arp_opNorm_le_hsNorm : ‖A‖ ≤ hsNorm A) but has a different type, so a fresh name is used.

Scratch-build checks:
- All 7 child types elaborate in the comparator's replay scope.
- With them posed as axioms, the frozen parent type is proved (axioms: propext, Classical.choice, Quot.sound plus 4 children).
- Complete proofs of all 7 children and of the parent compile with only the standard axioms.
- `exact Submission.X` closes each frozen child type.
