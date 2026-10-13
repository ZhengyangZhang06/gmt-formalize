# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1.differentiated_system-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1.differentiated_system-a1.clm_family-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1–2 of the parent proof (basis expansion of the coefficients; linearity of the derivative in the frozen argument). Mathlib's contDiffOn_clm_apply (Mathlib/Analysis/Calculus/ContDiff/FiniteDimension.lean) is not in the frozen import closure and imports may not be changed, so the basis argument is carried out directly.
1. Basis. L is finite-dimensional. Let E_1, ..., E_N be a basis of L (b := Module.finBasis ℝ L) with coordinate functionals π_r := b.coord r. These are continuous because L is finite-dimensional (LinearMap.toContinuousLinearMap). We have π_r(P) = b.repr P r and P = Σ_r π_r(P) E_r for every P (Module.Basis.sum_repr).
2. Expansion. For every x and P, linearity of Φ(x) gives Φ(x)[P] = Φ(x)[Σ_r π_r(P) E_r] = Σ_r π_r(P) Φ(x)[E_r]. Hence Φ(x) = Σ_r Φ_r(x) · π_r as elements of L*, with Φ_r(x) := Φ(x)[E_r]: the two continuous linear forms agree at every P (ContinuousLinearMap.ext).
3. C^1. Each Φ_r is C^1 on U (the hypothesis with P := E_r). Multiplying the scalar C^1 function Φ_r by the constant vector π_r ∈ L* gives a C^1 map on U (ContDiffOn.smul with contDiffOn_const), and a finite sum of C^1 maps is C^1 (ContDiffOn.sum). Φ coincides with this sum at every point (step 2), so Φ is C^1 on U (ContDiffOn.congr).
4. Evaluation commutes with differentiation. Let x ∈ U. Since U is open and Φ is C^1 on U, Φ is differentiable at x (1 ≠ 0). For fixed P, z ↦ Φ(z)[P] is the application of the operator-valued map Φ to the constant map z ↦ P. The product rule for evaluation (fderiv_clm_apply), together with the fact that a constant has derivative 0, gives D(Φ(·)[P])(x) = Φ(x) ∘ 0 + (DΦ(x)).flip P = (DΦ(x)).flip P. Applying both sides to e: D(Φ(·)[P])(x) e = (DΦ(x) e)[P]. QED
Lean notes:
- To expand P = Σ_r π_r(P) E_r, state an explicit equation proved by rw [b.sum_repr], then use map_sum and map_smul; plain simp folds the sum back into P.
- ContDiffOn.smul into L* needs the instance IsBoundedSMul ℝ ((Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ). It is found only at maxSynthPendingDepth 3, so start the proof with the tactic-level `set_option maxSynthPendingDepth 3 in` followed by a `·` block. The theorem statement itself elaborates at the default depth.
- The proof is a single theorem; no imports or helper declarations are added.

## Key steps

1. basis E_r of L with continuous coordinate functionals π_r; Φ(x) = Σ_r Φ(x)[E_r] π_r in L*
2. finite sum of C^1 scalar multiples of constant forms ⇒ Φ is C^1 on U
3. Φ differentiable at x ∈ U; fderiv_clm_apply with the constant P gives D(Φ(·)[P])(x)e = (DΦ(x)e)[P]

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json`
- `rg -n -i 'weak (equation|solution)|difference quotient|isSymmSndFDerivAt|translat' <snapshot>/project`
- `rg -n in <snapshot>/mathlib/Mathlib for: hasDerivAt_integral_of_dominated_loc_of_deriv_le, hasFDerivAt_of_tendstoUniformlyOnFilter, hasFDerivAt_of_tendstoLocallyUniformlyOn, ContDiffAt.isSymmSndFDerivAt, contDiffOn_clm_apply, continuousOn_clm_apply, setIntegral_eq_integral_of_forall_compl_eq_zero, integral_mul_right_eq_self (to_additive integral_add_right_eq_self), fderiv_comp_sub, fderiv_clm_apply, HasFDerivAt.clm_apply, HasDerivAt.clm_apply, HasDerivAt.tendsto_slope_zero, tsupport_fderiv_subset, IsCompact.exists_cthickening_subset_open, IsCompact.uniformContinuousOn_of_continuous, norm_image_sub_le_of_norm_fderiv_le', ContDiffOn.fderiv_of_isOpen, ContDiffOn.continuousOn_fderiv_of_isOpen, Continuous.integrable_of_hasCompactSupport, fderiv_smul, ContDiffOn.smul, ContDiffOn.sum, Module.Basis.sum_repr`
- `python3 scan of dag.json: statuses and lean_statements of linear_higher_regularity-a1 children and of difference_quotient_limit-a1.diffquot_uniform-a1; grep -c dohr_eb_lhr_ds in dag.json, nodes/ and the snapshot project`
- `git show 33d90ae6 (accepted dohr_eb_dql_diffQuot_tendstoUniformlyOn proof); git show a9fe7dd1 (leaf rejected for an added import); git log --all -G '^import ' -- GMT/Ch05/Submission.lean; scan of set_option usage in accepted workspace_result_commits`
- `read nodes/root-allard-any-radius-a1-patching-a1-global-graph-a1-local-c1-a1/rlcr-plan-v1.md and rlcr-config-v1.json (leaf gate rules)`
- `lake build GMT.Ch05.Submission in scratch copy /tmp/ds-decomp-igeL4K/proj (frozen header); lake env lean Checks/Names*.lean, Checks/OptTest.lean, Checks/InstTest.lean (lemma availability and instance depth at the frozen imports)`
- `lake env lean Checks/Six.lean, Checks/ChildDE2.lean, Checks/Assembly.lean, Checks/AssemblyAx.lean; lake build of Submission with six children and parent inserted (imports unchanged); gmt-compare.py child_modules NodeChallenge/NodeSolution files S0..S6 with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch08/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/UniformLimitsDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Group/Integral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Deriv/Slope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/UniformSpace/HeineCantor.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/LinearAlgebra/Basis/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-patching-a1-global-graph-a1-local-c1-a1/rlcr-plan-v1.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-patching-a1-global-graph-a1-local-c1-a1/rlcr-config-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`

The snapshot pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The project contains no weak-solution, difference-quotient or symmetry lemma; the only rg hit is an unrelated Ch08 README line about the constancy theorem.

Mathlib at the pin contains every lemma used, but two of them sit outside the frozen import closure of Submission. ContDiffAt.isSymmSndFDerivAt (FDeriv/Symmetric.lean:533) and contDiffOn_clm_apply (ContDiff/FiniteDimension.lean:52) both report 'Unknown identifier' after importing the frozen Submission. The leaf gate forbids adding imports or helper declarations (rlcr-plan rules; commit a9fe7dd1 was rejected for an added import).

These are available at the frozen imports:
- hasDerivAt_integral_of_dominated_loc_of_deriv_le (ParametricIntegral.lean:286)
- hasFDerivAt_of_tendstoUniformlyOnFilter (UniformLimitsDeriv.lean:308)
- continuousOn_clm_apply (Normed/Module/FiniteDimension.lean:518)
- setIntegral_eq_integral_of_forall_compl_eq_zero (Bochner/Set.lean:486)
- integral_add_right_eq_self (to_additive of Group/Integral.lean:101)
- fderiv_clm_apply (CompCLM.lean:143), fderiv_comp_sub (FDeriv/Add.lean:892)
- tsupport_fderiv_subset, IsCompact.exists_cthickening_subset_open (Thickening.lean:426), IsCompact.uniformContinuousOn_of_continuous (HeineCantor.lean:49)
- Convex.norm_image_sub_le_of_norm_fderiv_le' (MeanValue.lean:549), ContDiffOn.fderiv_of_isOpen and ContDiffOn.continuousOn_fderiv_of_isOpen (ContDiff/Defs.lean:907/916).

Instances on the bilinear-form type, on Rn n →L (L →L ℝ), and IsBoundedSMul ℝ (L →L ℝ) need maxSynthPendingDepth 3. Supplying them locally with haveI/letI fails on instance-path mismatches, so the proofs use a tactic-level set_option; accepted leaves already use set_option … in.

The accepted sibling-branch lemma dohr_eb_dql_diffQuot_tendstoUniformlyOn covers only Rn ℓ-valued maps, and its proof is codomain-generic. The child diffquot_uniform generalizes it to an arbitrary normed E, needed for L-valued Dv. No dohr_eb_lhr_ds_* name exists in dag.json, the node directories or the snapshot.

In the scratch build with the frozen header unchanged, all six children and the selected theorem were proven. The verifier-generated challenge and solution files pass with axioms propext, Classical.choice and Quot.sound only.
