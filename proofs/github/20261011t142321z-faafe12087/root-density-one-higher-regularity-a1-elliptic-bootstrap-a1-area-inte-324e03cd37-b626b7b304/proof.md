# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.area_integrand_legendre-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.area_integrand_legendre-a1.hessian_at_zero-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation: fix n, l, Q. L := Rn n →L[ℝ] Rn ℓ, J is the area integrand, and S := G(Q) is the n x n matrix S_{ab} = <Q e_a, Q e_b>.

1. J is C^2. By the sibling integrand_smooth (Submission.dohr_eb_ail_contDiff), J is C^infinity on L, hence C^2 (2 <= infinity).

2. Reduction to a line. Apply the sibling line_second_deriv (Submission.dohr_eb_ail_line_second_deriv) with E = L, F = J, x = 0, v = Q: fderiv ℝ (fderiv ℝ J) 0 Q Q = deriv (deriv (t -> J(0 + t Q))) 0.

3. Scaling of the Gram matrix. For t in R and a in Fin n, (0 + t Q) e_a = t (Q e_a). So G(0 + t Q)_{ab} = <t Q e_a, t Q e_b> = t^2 <Q e_a, Q e_b> = (t^2 S)_{ab}. Hence J(0 + t Q) = sqrt(det(I + t^2 S)) for every t, i.e. the two functions of t are equal.

4. One-variable computation. By the sibling sqrt_det_second_deriv (Submission.dohr_eb_ail_sqrt_det_second_deriv) applied to S: deriv (deriv (t -> sqrt(det(I + t^2 S)))) 0 = trace S.

5. Trace. trace S = sum_a S_{aa} = sum_a <Q e_a, Q e_a> = sum_a ||Q e_a||^2.

Combining steps 2-5: fderiv ℝ (fderiv ℝ J) 0 Q Q = sum_a ||Q e_a||^2. QED

Source: parent steps 3-4.

Lean note (checked at the pin; a complete proof compiled):
- `have hC2 := (Submission.dohr_eb_ail_contDiff n ℓ).of_le (m := 2) (by norm_cast)`. The side goal `(2 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)` closes by `norm_cast`, not by `exact_mod_cast le_top`.
- `rw [← Submission.dohr_eb_ail_line_second_deriv _ hC2 0 Q]`.
- Step 3: state the equality of the function `fun t : ℝ => Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ ((0 + t • Q) (EuclideanSpace.single a (1 : ℝ))) ((0 + t • Q) (EuclideanSpace.single b (1 : ℝ)))))` with `fun t : ℝ => Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + t ^ 2 • Matrix.of fun a b : Fin n => inner ℝ (Q (EuclideanSpace.single a (1 : ℝ))) (Q (EuclideanSpace.single b (1 : ℝ)))))`, proved by `funext t; congr 3; ext a b; simp [inner_smul_left, inner_smul_right, pow_two, mul_assoc]`.
- Finish with `rw [hfun, Submission.dohr_eb_ail_sqrt_det_second_deriv]; simp [Matrix.trace]`.

## Key steps

1. J is C^2 by integrand_smooth
2. D^2J(0)[Q][Q] is the second derivative of t -> J(0 + tQ) at 0 (line_second_deriv)
3. G(tQ) = t^2 G(Q), so J(tQ) = sqrt(det(I + t^2 G(Q)))
4. that second derivative is trace G(Q) = sum_a ||Q e_a||^2 (sqrt_det_second_deriv)

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
