# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1.coeff_uniform_bounds-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the bounds (H2), (H3) of step 4 of the parent proof, obtained there from P1 (components on a basis) and step 1 (Lipschitz, hence alpha-Hoelder, on the convex compact K0); here K is any compact convex subset of U.
Lean note: L := Rn n →L[ℝ] Rn ℓ has FiniteDimensional, and the linear-form type L →L[ℝ] ℝ has AddCommGroup/NormedSpace instances at the default maxSynthPendingDepth (checked at the pin). A basis is b := Module.finBasis ℝ L (index Fin (Module.finrank ℝ L)), coordinates π_r := LinearMap.toContinuousLinearMap (b.coord r) with π_r P = b.repr P r, and P = Σ_r b.repr P r • b r (Module.Basis.sum_repr, i.e. b.sum_repr P). No algebraic structure on the bilinear-form type L →L[ℝ] L →L[ℝ] ℝ is needed: only the scalars a x P Q are manipulated (if such structure is ever wanted, use set_option maxSynthPendingDepth 3).
1. Basis. L is finite-dimensional. Fix a basis E_1, ..., E_N of L and its coordinate functionals pi_r (linear, hence continuous on the finite-dimensional L), so that P = Σ_r pi_r(P) E_r. Let c := max(1, ||pi_1||, ..., ||pi_N||); then |pi_r(P)| ≤ c ||P||.
2. Expansion. For x in R^n put a_rt(x) := a(x)[E_r][E_t]. By bilinearity of a(x), a(x)[P][Q] = Σ_{r,t} pi_r(P) pi_t(Q) a_rt(x) for all P, Q.
3. If K is empty the claim is trivial; assume K ≠ ∅. Each a_rt is C^1 on the open set U, so a_rt and x ↦ D a_rt(x) (fderiv) are continuous on U (ContDiffOn.continuousOn, ContDiffOn.continuousOn_fderiv_of_isOpen). As K ⊆ U is compact and there are finitely many pairs (r, t), there are S ≥ 0 and S' ≥ 0 with |a_rt(x)| ≤ S and ||D a_rt(x)|| ≤ S' for all r, t and x in K.
4. Mean value. Every a_rt is differentiable at every point of K (K ⊆ U, U open), K is convex and ||D a_rt|| ≤ S' on K, so by the mean value inequality on convex sets (Convex.norm_image_sub_le_of_norm_fderiv_le) |a_rt(x) - a_rt(y)| ≤ S' |x - y| for x, y in K.
5. Lipschitz implies Hoelder. K is bounded: fix D ≥ 0 with |x - y| ≤ D for x, y in K. Let x, y in K. If x = y, then |x - y| = 0 = |x - y|^alpha (alpha > 0). If x ≠ y, then |x - y| = |x - y|^alpha |x - y|^(1 - alpha) (Real.rpow_add for the positive base |x - y|, with alpha + (1 - alpha) = 1) and |x - y|^(1 - alpha) ≤ D^(1 - alpha) because 1 - alpha ≥ 0 (Real.rpow_le_rpow). In both cases |x - y| ≤ D^(1 - alpha) |x - y|^alpha, hence |a_rt(x) - a_rt(y)| ≤ S' D^(1 - alpha) |x - y|^alpha.
6. Bounds for all P, Q. By steps 2 and 1, for x, y in K:
   |a(x)[P][Q]| ≤ Σ_{r,t} |pi_r(P)| |pi_t(Q)| |a_rt(x)| ≤ N^2 c^2 S ||P|| ||Q||, and
   |a(x)[P][Q] - a(y)[P][Q]| = |Σ_{r,t} pi_r(P) pi_t(Q) (a_rt(x) - a_rt(y))| ≤ N^2 c^2 S' D^(1 - alpha) |x - y|^alpha ||P|| ||Q||.
7. M := N^2 c^2 max(S, S' D^(1 - alpha)) satisfies both inequalities (all factors are nonnegative). QED

## Key steps

1. expand a(x)[P][Q] on a basis of L with coordinates bounded by c||P||
2. components and their derivatives are bounded on the compact K
3. mean value on the convex K: components Lipschitz, hence alpha-Hoelder since |x-y| <= D^(1-alpha)|x-y|^alpha
4. sum over the basis: M = N^2 c^2 max(S, S' D^(1-alpha))

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; cmp GMT/Ch05/Contract.lean <snapshot>/project/GMT/Ch05/Contract.lean; cmp GMT/Ch05/Contract.lean GMT/Ch05/Submission.lean`
- `python3 scan of dag.json: sibling lean_statements of schauder_estimate-a1, difference_quotient_limit-a1, holder_succ_iff_fderiv-a1, holder_of_contdiff_succ-a1, holder_bilinear-a1 and their statuses; collision check for dohr_eb_lhr_* names`
- `rg -c dohr_eb_lhr <snapshot> and the run's nodes directory (no match)`
- `rg -n -i 'schauder|campanato|caccioppoli|difference quotient' <snapshot>/project`
- `rg -n in <snapshot>/mathlib/Mathlib for: contDiffOn_of_locally_contDiffOn, lebesgue_number_lemma_of_metric, ContDiffOn.continuousOn_fderiv_of_isOpen, IsCompact.exists_bound_of_continuousOn, norm_image_sub_le_of_norm_fderiv_le, norm_image_sub_le_of_norm_hasDerivWithin_le, integral_mul_right_eq_self (to_additive integral_add_right_eq_self), Continuous.integrable_of_hasCompactSupport, setIntegral_eq_integral_of_forall_compl_eq_zero, setIntegral_congr_fun, tsupport_fderiv_subset, fderiv_comp_add_right, fderiv_comp_sub, ContDiffAt.isSymmSndFDerivAt, iteratedFDeriv_one_apply, norm_iteratedFDeriv_one, Filter.EventuallyEq.iteratedFDeriv, iteratedFDeriv_sub_apply, iteratedFDeriv_sum_apply, IsCompact.exists_cthickening_subset_open, IsCompact.cthickening, IsCompact.uniformContinuousOn_of_continuous, Basis.sum_repr, Basis.coord, coe_toContinuousLinearMap', fderiv_fun_sum, fderiv_const_mul, fderiv_clm_apply`
- `lake build GMT.Ch05.Submission in scratch copy /tmp/lhr-decomp-ULIRRR/proj (Lean 4.35.0-rc3, shared lake-packages-25730c7c)`
- `lake env lean Checks/Inst.lean (instances on the linear-form type at default depth; FiniteDimensional for L and L*)`
- `lake env lean Checks/v1/*.lean (six child challenge files generated by the verifier's contract_scope/child_modules)`
- `lake env lean Checks/Assembly.lean (parent frozen type from 6 child + 5 sibling types posed as axioms; #print axioms)`
- `lake env lean Checks/Names.lean and Checks/Names2.lean (#check of cited names; ContDiffAt.isSymmSndFDerivAt needs import Mathlib.Analysis.Calculus.FDeriv.Symmetric)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Group/Integral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/VectorMeasure/SetIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/UniformSpace/HeineCantor.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/LinearAlgebra/Basis/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`

Snapshot pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The workspace Contract.lean is byte-identical to the snapshot Contract, and Submission.lean is still identical to it. There is no elliptic regularity theory at the pin. The project only mentions Schauder in README.md:152, as a citation for 7.1(ii). No dohr_eb_lhr_ name exists in the snapshot, dag.json or the node directories, so the six names are fresh. Of the five siblings only dohr_eb_holder_of_contDiffOn_succ is accepted; the others are decomposing, waiting-children or speculative-ready. Children therefore cannot depend on them, so all sibling uses are kept in the parent assembly. Every Mathlib lemma cited in the child proofs exists at the pin. Locations: contDiffOn_of_locally_contDiffOn (ContDiff/Defs.lean:586), ContDiffOn.continuousOn_fderiv_of_isOpen (Defs.lean:916), lebesgue_number_lemma_of_metric (Pseudo/Lemmas.lean:120), Convex.norm_image_sub_le_of_norm_fderiv_le (MeanValue.lean:499), Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (MeanValue.lean:694), integral_add_right_eq_self (to_additive of Group/Integral.lean:101), Continuous.integrable_of_hasCompactSupport (LocallyIntegrable.lean:622), setIntegral_eq_integral_of_forall_compl_eq_zero (SetIntegral.lean:325), tsupport_fderiv_subset (FDeriv/Const.lean:383), fderiv_comp_add_right (FDeriv/Add.lean:855), fderiv_comp_sub (Add.lean:892), ContDiffAt.isSymmSndFDerivAt (FDeriv/Symmetric.lean:533; not imported by Submission, so add import Mathlib.Analysis.Calculus.FDeriv.Symmetric), iteratedFDeriv_one_apply (FTaylorSeries.lean:938), Filter.EventuallyEq.iteratedFDeriv (FTaylorSeries.lean:885), iteratedFDeriv_sub_apply (Operations.lean:339) and iteratedFDeriv_sum_apply (Operations.lean:404), the last two needing only ContDiffAt, IsCompact.exists_cthickening_subset_open (Thickening.lean:426), IsCompact.uniformContinuousOn_of_continuous (HeineCantor.lean:49), Module.Basis.sum_repr (Basis/Defs.lean:258), contDiffOn_clm_apply (FiniteDimension.lean:52). Lean checks on the scratch build: the linear-form type (Rn n ->L Rn l) ->L R has AddCommGroup and NormedSpace at the default synthesis depth, and FiniteDimensional holds for L and L*. All six child types elaborate in the comparator's replayed Contract scope. With the 6 child types and 5 sibling types as axioms, the frozen parent type is proved without sorry, and #print axioms lists propext, Classical.choice, Quot.sound and exactly those 11.
