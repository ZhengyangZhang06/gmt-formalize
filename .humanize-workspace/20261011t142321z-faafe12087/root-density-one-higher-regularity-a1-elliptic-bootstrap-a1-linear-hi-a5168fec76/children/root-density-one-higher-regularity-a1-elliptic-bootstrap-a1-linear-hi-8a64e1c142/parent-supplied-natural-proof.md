# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1.coeff_uniform_bounds-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1.coeff_uniform_bounds-a1.scalar_c1_bounds-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 3-5 of the parent proof, specialized to one scalar function f. Those steps are the bounds on the compact K, the mean value inequality on the convex K, and Lipschitz implies alpha-Hoelder via the diameter of K. The parent applies this lemma to each component a_rt(x) = a(x)[E_r][E_t].

Lean note (checked by a trial proof at the pin):
- ContDiffOn.differentiableOn takes (hn : n ≠ 0) here, so use one_ne_zero.
- Use ContDiffOn.continuousOn_fderiv_of_isOpen hU le_rfl.
- IsCompact.exists_bound_of_continuousOn gives ‖g x‖ ≤ C; convert with Real.norm_eq_abs.
- In Convex.norm_image_sub_le_of_norm_fderiv_le, pass the bound explicitly as (C := max S1 0).
- Take D := Metric.diam K and use Metric.diam_nonneg, Metric.dist_le_diam_of_mem hK.isBounded hx hy and dist_eq_norm.

1. Regularity. Since f is C^1 on U, f is continuous on U (ContDiffOn.continuousOn). Because U is open and 1 <= 1, the derivative x ↦ Df(x) := fderiv ℝ f x is continuous on U (ContDiffOn.continuousOn_fderiv_of_isOpen). Since 1 ≠ 0, f is differentiable on U (ContDiffOn.differentiableOn). U is open, so it is a neighbourhood of each of its points, and f is therefore differentiable at every x in U (DifferentiableOn.differentiableAt with IsOpen.mem_nhds). Since K ⊆ U, f is differentiable at every point of K, and f and Df are continuous on K (ContinuousOn.mono).

2. Bounds on K. A function that is continuous on the compact set K has bounded norm on K (IsCompact.exists_bound_of_continuousOn). So there are real numbers S0, S1 with |f(x)| <= S0 and ||Df(x)|| <= S1 for all x in K; on R the norm is the absolute value. Put S0+ := max(S0, 0) and S1+ := max(S1, 0). Then S0+ >= 0, S1+ >= 0, and |f(x)| <= S0+ and ||Df(x)|| <= S1+ for all x in K.

3. Mean value inequality. K is convex, f is differentiable at every point of K, and ||Df(z)|| <= S1+ for every z in K. The mean value inequality on convex sets (Convex.norm_image_sub_le_of_norm_fderiv_le, applied to the points y, x in K) gives ||f(x) - f(y)|| <= S1+ ||x - y||. That is, |f(x) - f(y)| <= S1+ ||x - y|| for all x, y in K.

4. Diameter. K is compact, hence bounded (IsCompact.isBounded). Let D := diam K. Then D >= 0 (Metric.diam_nonneg), and ||x - y|| = dist(x, y) <= D for all x, y in K (dist_eq_norm, Metric.dist_le_diam_of_mem).

5. Elementary inequality. Claim: t <= D^(1 - alpha) * t^alpha for every real t with 0 <= t <= D.
   Case t = 0: since alpha ≠ 0, 0^alpha = 0 (Real.zero_rpow). The right-hand side is 0, so the claim reads 0 <= 0.
   Case t > 0: by Real.rpow_add for the positive base t, t^alpha * t^(1 - alpha) = t^(alpha + (1 - alpha)) = t^1 = t. Since 0 <= t <= D and 1 - alpha >= 0 (because alpha <= 1), t^(1 - alpha) <= D^(1 - alpha) (Real.rpow_le_rpow). Since t^alpha >= 0 (Real.rpow_nonneg), t = t^alpha * t^(1 - alpha) <= t^alpha * D^(1 - alpha) = D^(1 - alpha) * t^alpha.

6. Hoelder estimate. Let x, y be in K and put t := ||x - y||; by step 4, 0 <= t <= D. Steps 3 and 5, together with S1+ >= 0, give |f(x) - f(y)| <= S1+ ||x - y|| <= S1+ * D^(1 - alpha) * ||x - y||^alpha.

7. Conclusion. Put S := max(S0+, S1+ * D^(1 - alpha)). Then S >= S0+ >= 0. Let x, y be in K.
   - By step 2, |f(x)| <= S0+ <= S.
   - Since ||x - y||^alpha >= 0 (Real.rpow_nonneg), step 6 gives |f(x) - f(y)| <= (S1+ * D^(1 - alpha)) * ||x - y||^alpha <= S * ||x - y||^alpha.
   If K is empty, the pointwise claims are vacuous and S >= 0 still holds, so no case distinction is needed. QED

## Key steps

1. f is continuous on U, Df is continuous on U (U open), and f is differentiable at every point of K ⊆ U
2. compactness of K: |f| <= S0 and ||Df|| <= S1 on K; replace them by S0+ := max(S0,0) and S1+ := max(S1,0)
3. mean value inequality on the convex K: |f(x) - f(y)| <= S1+ ||x - y||
4. K is bounded: ||x - y|| <= D := diam K, and t <= D^(1-alpha) t^alpha for 0 <= t <= D (rpow_add, rpow_le_rpow, zero_rpow)
5. S := max(S0+, S1+ D^(1-alpha)) >= 0 gives |f(x)| <= S and |f(x) - f(y)| <= S ||x - y||^alpha

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json`
- `git show a0cbb004:GMT/Ch05/Submission.lean | cmp - GMT/Ch05/Contract.lean; git show a0cbb004:GMT/Ch05/Contract.lean | cmp - <snapshot>/project/GMT/Ch05/Contract.lean`
- `python3 scan of dag.json: parent node and its six children (statuses), statements containing Convex+ContDiffOn / FiniteDimensional / rpow / Module.finBasis, lean_names containing holder/lipschitz/bilinear/basis`
- `grep -c dohr_eb_lhr_cub_scalar_c1_bounds|dohr_eb_lhr_cub_bilinear_basis_bound|dohr_eb_lhr_cub in dag.json, nodes/, <snapshot>/project; git grep -l dohr_eb_lhr_cub over every local branch/remote head (no match)`
- `rg -n in <snapshot>/mathlib/Mathlib for: ContDiffOn.continuousOn, ContDiffOn.continuousOn_fderiv_of_isOpen, ContDiffOn.differentiableOn, exists_bound_of_continuousOn, norm_image_sub_le_of_norm_fderiv_le, IsCompact.isBounded, diam_nonneg, dist_le_diam_of_mem, rpow_add, rpow_le_rpow, zero_rpow, rpow_nonneg, finBasis, Basis.sum_repr, coord_apply, toContinuousLinearMap, coe_toContinuousLinearMap', le_opNorm, abs_sum_le_sum_abs, single_le_sum, prod_comm/sum_comm, ContinuousLinearMap.finiteDimensional`
- `rg -n -i 'schauder|holder|hölder|finBasis|bilinear' <snapshot>/project/GMT/Ch05`
- `rg -l -i 'finBasis|exists_bound_of_continuousOn|norm_image_sub_le_of_norm_fderiv_le' lake-packages-25730c7c/simongmt/Poincare`
- `lake build GMT.Ch05.Submission in scratch /tmp/cub-decomp-SOIqD6/proj (Lean 4.35.0-rc3, shared lake-packages-25730c7c)`
- `python3 -I scripts/gen.py (verifier gmt-compare.py child_modules, contract mode) then lake env lean Checks/Challenge_scalar_c1_bounds.lean and Checks/Challenge_bilinear_basis_bound.lean`
- `lake env lean Checks/Assembly.lean (parent frozen type from the two child types as axioms; #print axioms)`
- `lake env lean Checks/ChildA.lean, Checks/ChildB.lean, Checks/Full.lean (#check of cited names, trial proofs, #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/LinearAlgebra/Dimension/Free.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/LinearAlgebra/Basis/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Algebra/Order/BigOperators/Group/Finset.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Sigma.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`

The snapshot pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The proof-base Submission.lean (commit a0cbb004) is byte-identical to Contract.lean, which is byte-identical to the snapshot Contract.

Neither child statement exists in the project, the snapshot or the DAG. The project mentions Hölder only in IsHolderCkα / IsLocallyHolderCkα, and has no bilinear or basis lemmas. simongmt only uses these Mathlib lemmas and has no reusable lemma. The nearest accepted declaration, dohr_eb_holder_of_contDiffOn_succ, has a different type, so it is not reused.

The names dohr_eb_lhr_cub_scalar_c1_bounds and dohr_eb_lhr_cub_bilinear_basis_bound are fresh: no match in dag.json, the node directories, the snapshot, or any local branch or remote head.

All cited Mathlib lemmas exist at the pin:
- ContDiffOn.continuousOn (ContDiff/Defs.lean:557)
- ContDiffOn.differentiableOn (Defs.lean:578; it takes n ≠ 0, so use one_ne_zero)
- ContDiffOn.continuousOn_fderiv_of_isOpen (Defs.lean:916)
- IsCompact.exists_bound_of_continuousOn (to_additive, Normed/Group/Bounded.lean:91)
- Convex.norm_image_sub_le_of_norm_fderiv_le (MeanValue.lean:499; pass C explicitly)
- IsCompact.isBounded (MetricSpace/Bounded.lean:192), Metric.diam_nonneg (:411), Metric.dist_le_diam_of_mem (:494)
- Real.zero_rpow (Pow/Real.lean:128), Real.rpow_nonneg (:163), Real.rpow_add (:207), Real.rpow_le_rpow (:549)
- Module.finBasis (Dimension/Free.lean:334), Basis.sum_repr (Basis/Defs.lean:258)
- LinearMap.toContinuousLinearMap (FiniteDimension.lean:307), coe_toContinuousLinearMap' (:323), ContinuousLinearMap.finiteDimensional (:80-89)
- ContinuousLinearMap.le_opNorm (Operator/Basic.lean:234)
- Finset.abs_sum_le_sum_abs (Order/BigOperators/Group/Finset.lean:371)
- Finset.sum_comm (to_additive of prod_comm, Sigma.lean:121)
- ContinuousLinearMap.sum_apply / smul_apply are deprecated aliases but still usable.

Lean checks in the scratch build:
- Both child types elaborate in the comparator's contract-scope challenge files.
- The parent's frozen type follows from the two child types as axioms. #print axioms lists propext, Classical.choice, Quot.sound, childA, childB.
- Trial proofs of both children and of the whole chain compile using only propext, Classical.choice and Quot.sound.
