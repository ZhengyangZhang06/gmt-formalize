# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.area_integrand_legendre-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.area_integrand_legendre-a1.line_second_deriv-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Regularity. F is C^2 and 2 != 0, so F is differentiable everywhere. Since 1 + 1 <= 2, the derivative map DF = fderiv ℝ F : E -> (E →L[ℝ] ℝ) is C^1 (ContDiff.fderiv_right), hence differentiable everywhere.

2. The line. gamma(t) := x + t v satisfies gamma'(t) = v for every t in R.

3. First derivative of g. By the chain rule, for every t, g has derivative DF(x + t v)[v] = fderiv ℝ F (x + t v) v at t. So the function deriv g equals t -> fderiv ℝ F (x + t v) v for all t.

4. Second derivative. By the chain rule again, the curve t -> DF(x + t v) in E →L[ℝ] ℝ has derivative D(DF)(gamma(0))[gamma'(0)] = fderiv ℝ (fderiv ℝ F) x v at t = 0, since gamma(0) = x + 0 v = x. Evaluation at the fixed vector v is a continuous linear map (E →L[ℝ] ℝ) -> R. Equivalently, apply the product rule to the pairing of this operator-valued curve with the constant curve v, whose derivative is 0. Hence t -> DF(x + t v) v has derivative (fderiv ℝ (fderiv ℝ F) x v) v at 0.

5. Conclusion. By steps 3 and 4, deriv (deriv g) 0 = deriv (t -> fderiv ℝ F (x + t v) v) 0 = fderiv ℝ (fderiv ℝ F) x v v. QED

Source: the chain-rule part of parent step 4 (f''(t) = D^2J(tQ)[Q][Q] along t -> tQ), stated for a general C^2 function and base point.

Lean note (checked at the pin; a complete proof compiled):
- Regularity: `hF.differentiable (by norm_num)`, and `hF.fderiv_right (by norm_num) : ContDiff ℝ 1 (fderiv ℝ F)` followed by `.differentiable (by norm_num)` (the argument is `n ≠ 0`, not `1 ≤ n`).
- Line: `by simpa using ((hasDerivAt_id t).smul_const v).const_add x`.
- Step 3: `funext t; exact ((hF1 _).hasFDerivAt.comp_hasDerivAt t (hline t)).deriv`.
- Step 4: `have h0 := (hD _).hasFDerivAt.comp_hasDerivAt (0:ℝ) (hline 0)`, then `have h2 := h0.clm_apply (hasDerivAt_const (0:ℝ) v)`, `simp only [zero_smul, add_zero, map_zero] at h2`, `exact h2.deriv`.

## Key steps

1. C^2 gives F differentiable and fderiv F of class C^1
2. deriv of t -> F(x + t v) is t -> fderiv F (x + t v) v by the chain rule
3. t -> fderiv F (x + t v) has derivative fderiv (fderiv F) x v at 0
4. evaluating at the constant v gives deriv (deriv g) 0 = fderiv (fderiv F) x v v

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
