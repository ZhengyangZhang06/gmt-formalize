# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1.differentiated_system-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1.differentiated_system-a1.translate_weak-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 of the parent proof (testing the weak equation with translates of the test function and substituting x = y + s e). No regularity of ω₁, ω₂ and no integrability are needed: both sides are related by exact identities that hold for the Bochner integral of arbitrary functions.
1. Translated test function. Let φ(x) := ζ(x − s e), i.e. φ = ζ ∘ τ with the homeomorphism τ(x) := x − s e (Homeomorph.subRight (s • e)). φ is C^1, as the composition of the C^1 map ζ with the affine map x ↦ x − s e, and it has compact support (HasCompactSupport.comp_homeomorph).
2. Support. tsupport φ = τ^{-1}(tsupport ζ) (tsupport_comp_eq_preimage). If x ∈ tsupport φ, then y := x − s e ∈ tsupport ζ, so x = y + s e ∈ U by hypothesis. Thus tsupport φ ⊆ U and the hypothesis applies to φ: ∫_U ω₁(x)[Dφ(x)] dx = ∫_U ω₂(x)[Dφ(x)] dx.
3. Derivative. By the chain rule, Dφ(x) = Dζ(x − s e) for every x (fderiv_comp_sub).
4. Vanishing off U. Let x ∉ U. Then x − s e ∉ tsupport ζ, since otherwise x = (x − s e) + s e ∈ U. As tsupport(Dζ) ⊆ tsupport ζ (tsupport_fderiv_subset), Dζ(x − s e) = 0, so ω_i(x)[Dφ(x)] = ω_i(x)[0] = 0 for i = 1, 2. Consequently ∫_U ω_i(x)[Dφ(x)] dx = ∫_{R^n} ω_i(x)[Dζ(x − s e)] dx (setIntegral_eq_integral_of_forall_compl_eq_zero, which needs neither measurability nor integrability).
5. Translation invariance. Lebesgue measure on R^n is invariant under x ↦ x + s e, so ∫ f(y + s e) dy = ∫ f(x) dx for every function f (integral_add_right_eq_self). Take f(x) := ω_i(x)[Dζ(x − s e)]; then f(y + s e) = ω_i(y + s e)[Dζ(y)]. Hence ∫_{R^n} ω_i(y + s e)[Dζ(y)] dy = ∫_{R^n} ω_i(x)[Dζ(x − s e)] dx = ∫_U ω_i(x)[Dφ(x)] dx for i = 1, 2.
6. Combining step 5 for i = 1, 2 with the identity of step 2 gives ∫ ω₁(y + s e)[Dζ(y)] dy = ∫ ω₂(y + s e)[Dζ(y)] dy. QED
Lean note: the proof is a single theorem using only the frozen imports, with no options.

## Key steps

1. φ := ζ(· − se) = ζ ∘ Homeomorph.subRight (se) is C^1 with compact support and tsupport φ = tsupport ζ + se ⊆ U
2. Dφ(x) = Dζ(x − se); apply the weak identity to φ
3. the integrands vanish off U, so the set integrals over U equal whole-space integrals
4. translation invariance x = y + se turns them into ∫ ω_i(y+se)[Dζ(y)] dy

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
