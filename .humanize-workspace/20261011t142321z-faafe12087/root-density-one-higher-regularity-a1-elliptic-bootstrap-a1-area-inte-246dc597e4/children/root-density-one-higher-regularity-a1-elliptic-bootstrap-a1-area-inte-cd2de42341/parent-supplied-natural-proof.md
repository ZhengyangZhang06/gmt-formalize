# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.area_integrand_legendre-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.area_integrand_legendre-a1.sqrt_det_second_deriv-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation: tau := trace S. For a polynomial R in R[X], R' is its derivative and R(u) its value at u.

1. Expansion. By Matrix.det_one_add_smul, det(I + r S) = 1 + tau r + R(r) r^2 for every r in R, where R := (det(1 + X • S.map C)).divX.divX is a fixed real polynomial. With r = t^2: p(t) := det(I + t^2 S) = 1 + tau t^2 + R(t^2) t^4 for every t, and f(t) = sqrt(p(t)).

2. First derivative of p. p is differentiable at every t with p'(t) = 2 tau t + R'(t^2) (2t) t^4 + R(t^2) (4 t^3). This uses the chain rule for t -> R(t^2) (derivative R'(t^2) * 2t), the power rule, and the product and sum rules.

3. Second derivative of p at 0. p' is differentiable at 0 with p''(0) = 2 tau:
- 2 tau t has derivative 2 tau;
- u(t) t^4 with u(t) = R'(t^2) 2t has derivative u'(0) * 0^4 + u(0) * 4 * 0^3 = 0 at 0;
- w(t) * 4t^3 with w(t) = R(t^2) has derivative w'(0) * 4 * 0^3 + w(0) * 12 * 0^2 = 0 at 0.
The last two use the product rule with u, w differentiable.

4. Values at 0. p(0) = 1 and p'(0) = 0.

5. Localization. p is continuous at 0 (it is differentiable) and p(0) = 1 > 0, so p > 0 on a neighbourhood U of 0. For t in U, f = sqrt o p is differentiable at t with f'(t) = p'(t) / (2 sqrt(p(t))) (derivative of sqrt at a positive point). So deriv f agrees on U with g(t) := p'(t) / (2 sqrt(p(t))). A derivative at a point depends only on the function near that point, so deriv (deriv f) 0 = g'(0) (Filter.EventuallyEq.deriv_eq).

6. Quotient rule. d(t) := 2 sqrt(p(t)) is differentiable at 0 with d(0) = 2 sqrt(1) = 2 != 0 and d'(0) = 2 p'(0) / (2 sqrt(p(0))) = 0. So g'(0) = (p''(0) d(0) - p'(0) d'(0)) / d(0)^2 = (2 tau * 2 - 0) / 4 = tau.

7. Conclusion. deriv (deriv f) 0 = tau = trace S. QED

Source: parent step 3. There, det(I + sS) = 1 + s tr S + s^2 r(s) (Matrix.det_one_add_smul), phi(s) = sqrt(det(I + sS)), f(t) = phi(t^2) and f''(0) = 2 phi'(0) = tr S. Here the same computation is done directly on p(t) = det(I + t^2 S).

Lean note (checked at the pin; a complete proof compiled):
- Rewrite under the binder with `funext t; rw [Matrix.det_one_add_smul (t ^ 2) S]`.
- For t -> Q.eval (t^2): take `h2 : HasDerivAt (fun t => t ^ 2) (2 * t) t := by simpa using hasDerivAt_pow 2 t`, then `have := (Q.hasDerivAt (t ^ 2)).comp t h2; simpa [Function.comp_def] using this`.
- Use the lambda-form lemmas `HasDerivAt.fun_pow` and `HasDerivAt.fun_div`. The plain `.pow` and `.div` give Pi-operation forms (f ^ 2, c / d) that do not match lambda goals.
- After `.add`/`.mul`, use `convert this using 1` followed by `simp` or `ring`.
- Positivity near 0: `continuousAt_const.eventually_lt (hp' 0).continuousAt (by rw [hp0]; norm_num)`.
- Step 5: `filter_upwards [hpos] with t ht; exact ((hp' t).sqrt ht.ne').deriv`, then `rw [hderiv.deriv_eq]`.
- Step 6: `hp''.fun_div (((hp' 0).sqrt h).const_mul 2) h'`, then `rw [hfin.deriv, hp'0, hp0]; simp; ring`.

## Key steps

1. det(I + t^2 S) = 1 + tau t^2 + R(t^2) t^4 by Matrix.det_one_add_smul
2. p(0) = 1, p'(0) = 0, p''(0) = 2 tau
3. near 0, deriv f = p' / (2 sqrt p) because p > 0 there
4. quotient rule at 0 gives f''(0) = p''(0)/2 = trace S

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
