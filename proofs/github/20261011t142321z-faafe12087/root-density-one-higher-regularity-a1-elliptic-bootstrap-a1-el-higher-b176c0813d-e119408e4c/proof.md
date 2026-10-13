# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.el_higher_step-a1.differentiated_el-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.el_higher_step-a1.differentiated_el-a1.test_admissible-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 3 and 5 of the parent proof of dohr_eb_ehs_differentiated_el (margin, and admissibility and derivative of the difference-quotient test maps).
Notation: Kz := tsupport zeta; phi_h(x) := h^{-1}(zeta(x) - zeta(x - he)).
1. Margin. Kz is compact (zeta has compact support) and Kz ⊆ U with U open, so there is delta > 0 with K' := cthickening delta Kz ⊆ U (IsCompact.exists_cthickening_subset_open). K' is closed (isClosed_cthickening) and compact (IsCompact.cthickening). Put h0 := delta/(||e|| + 1) > 0. The set {h : |h| < h0} is a neighbourhood of 0, so it suffices to prove the four properties for every h with |h| < h0. Fix such an h; then ||he|| = |h| ||e|| <= |h| (||e|| + 1) < delta.
2. C^1. The translation x -> x - he is affine, hence C^infinity, so x -> zeta(x - he) is C^1 as a composition; differences of C^1 maps and constant multiples (by h^{-1}) of C^1 maps are C^1. Thus phi_h is C^1.
3. Support. Suppose phi_h(x) ≠ 0. Then zeta(x) ≠ 0 or zeta(x - he) ≠ 0. In the first case x lies in Kz ⊆ K'. In the second case x - he lies in Kz and dist(x, x - he) = ||he|| < delta, so x lies in K' (mem_cthickening_of_dist_le). Hence support(phi_h) ⊆ K', and since K' is closed, tsupport(phi_h) = closure(support(phi_h)) ⊆ K' ⊆ U.
4. Compact support. tsupport(phi_h) is closed and contained in the compact set K', hence compact (IsCompact.of_isClosed_subset); i.e. phi_h has compact support.
5. Derivative. zeta is differentiable everywhere (C^1). For every y, the map x -> zeta(x - he) has derivative Dzeta(y - he) at y (chain rule with the translation, whose derivative is the identity; hasFDerivAt_comp_sub). By linearity of differentiation, phi_h has derivative h^{-1}(Dzeta(y) - Dzeta(y - he)) at y, so fderiv ℝ (fun x => h⁻¹ • (ζ x - ζ (x - h • e))) y = h⁻¹ • (fderiv ℝ ζ y - fderiv ℝ ζ (y - h • e)). This holds for every y (and in fact for every h). QED
Lean note (verified at the pin, Lean 4.35.0-rc3, Mathlib 25730c7c; #print axioms: propext, Classical.choice, Quot.sound; no extra import).
- Verified script (tactic block of `theorem dohr_eb_ehs_del_test_admissible`, whose type is exactly this node's lean_statement):
  intro n ℓ ζ U e hU hζ hζc hζU
  obtain ⟨δ, hδ, hδU⟩ := hζc.isCompact.exists_cthickening_subset_open hU hζU
  have he1 : 0 < ‖e‖ + 1 := by positivity
  have hpos : 0 < δ / (‖e‖ + 1) := div_pos hδ he1
  have hev : ∀ᶠ h in 𝓝[≠] (0 : ℝ), |h| < δ / (‖e‖ + 1) := by
    apply nhdsWithin_le_nhds
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hpos] with h hh
    simpa [Real.dist_eq] using hh
  filter_upwards [hev] with h hh
  have hdiff : Differentiable ℝ ζ := hζ.differentiable one_ne_zero
  have hhe : ‖h • e‖ < δ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |h| * ‖e‖ ≤ |h| * (‖e‖ + 1) := by gcongr; linarith
      _ < δ / (‖e‖ + 1) * (‖e‖ + 1) := by gcongr
      _ = δ := div_mul_cancel₀ _ he1.ne'
  have hsupp : Function.support (fun x => h⁻¹ • (ζ x - ζ (x - h • e))) ⊆
      cthickening δ (tsupport ζ) := by
    intro x hx
    by_contra hxK
    apply hx
    have h1 : ζ x = 0 := by
      by_contra h1
      exact hxK (self_subset_cthickening _ (subset_tsupport _ h1))
    have h2 : ζ (x - h • e) = 0 := by
      by_contra h2
      apply hxK
      apply mem_cthickening_of_dist_le x (x - h • e) δ (tsupport ζ) (subset_tsupport _ h2)
      rw [dist_eq_norm, sub_sub_cancel]
      exact hhe.le
    simp [h1, h2]
  have htsupp : tsupport (fun x => h⁻¹ • (ζ x - ζ (x - h • e))) ⊆ cthickening δ (tsupport ζ) :=
    closure_minimal hsupp isClosed_cthickening
  refine ⟨?_, ?_, htsupp.trans hδU, ?_⟩
  · exact (hζ.sub (hζ.comp (contDiff_id.sub contDiff_const))).const_smul h⁻¹
  · exact IsCompact.of_isClosed_subset hζc.isCompact.cthickening (isClosed_tsupport _) htsupp
  · intro y
    have hd1 : HasFDerivAt (fun x => ζ (x - h • e)) (fderiv ℝ ζ (y - h • e)) y :=
      (hasFDerivAt_comp_sub (h • e)).mpr (hdiff (y - h • e)).hasFDerivAt
    exact ((((hdiff y).hasFDerivAt).sub hd1).const_smul h⁻¹).fderiv

## Key steps

1. margin: delta > 0 with K' := cthickening delta (tsupport zeta) ⊆ U; restrict to |h| < delta/(||e|| + 1)
2. phi_h is C^1 as a combination of zeta and its translate
3. support phi_h ⊆ K' (closed), so tsupport phi_h ⊆ K' ⊆ U and it is compact
4. chain rule for the translation and linearity give Dphi_h(y) = h^{-1}(Dzeta(y) - Dzeta(y - he))

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; cmp <snapshot>/project/GMT/Ch05/Contract.lean GMT/Ch05/Contract.lean; cmp GMT/Ch05/Contract.lean GMT/Ch05/Submission.lean`
- `python3 -I scan of dag.json nodes[*].lean_name (486 unique) for 'ehs', 'diffquot', 'del_' and the prefix dohr_eb_ehs_del; rg -l 'dohr_eb_ehs_del|isSymmSndFDerivAt' <snapshot>/project`
- `rg -n 'theorem fderiv_comp|theorem fderiv_clm_apply|theorem ContDiffAt.isSymmSndFDerivAt|def IsSymmSndFDerivAt|theorem fderiv_comp_add_right|theorem fderiv_const_smul|theorem setIntegral_eq_integral_of_forall_compl_eq_zero|theorem tendsto_integral_filter_of_dominated_convergence|theorem setIntegral_congr_fun' <snapshot>/mathlib/Mathlib`
- `rg -n 'integral_add_right_eq_self|integral_sub_right_eq_self' <snapshot>/mathlib/Mathlib, then sed -n 100,215p Analysis/Calculus/Rademacher.lean (difference-quotient integration-by-parts template)`
- `rg -n 'theorem TendstoUniformlyOn.tendsto_at|theorem norm_inner_le_norm|theorem ContinuousOn.inner|theorem integrableOn_const|theorem integrable_indicator_iff|theorem norm_setIntegral_le_of_norm_le_const|theorem ContinuousOn.aestronglyMeasurable' <snapshot>/mathlib/Mathlib`
- `rg -n 'setIntegral_eq_of_subset_of_forall_diff_eq_zero|IntegrableOn.integrable_of_forall_notMem_eq_zero|integrableOn_iff_integrable_of_support_subset|ContinuousOn.clm_apply|norm_le_insert' <snapshot>/mathlib/Mathlib; sed -n 455,492p MeasureTheory/Integral/Bochner/Set.lean; sed -n 185,202p Analysis/Normed/Group/Basic.lean; sed -n 95,104p MeasureTheory/Group/Integral.lean`
- `rg -n 'exists_cthickening_subset_open|IsCompact.uniformContinuousOn_of_continuous|ContDiffOn.continuousOn_fderiv_of_isOpen|ContDiffOn.fderiv_of_isOpen|ContDiff.fderiv_right|ContDiff.continuous_fderiv|norm_image_sub_le_of_norm_fderiv_le'|tsupport_fderiv_subset|HasCompactSupport.fderiv' in the corresponding snapshot files`
- `git show 33d90ae6:GMT/Ch05/Submission.lean (Submission.dohr_eb_dql_diffQuot_tendstoUniformlyOn, E = Rn ℓ, other branch); git show <conical-approximation branch>:GMT/Ch05/Submission.lean | grep '^import' (precedent for added Mathlib imports)`
- `lake build GMT.Ch05.Submission in scratch /tmp/del-split-I5hsTm/proj (Lean 4.35.0-rc3, .lake/packages -> lake-packages-25730c7c)`
- `lake env lean Checks/Challenge_*.lean (6 types generated by verifier gmt-compare.py child_modules in contract scope); python3 -I validate_lean_statement (verifier/lean_contract.py) on all 6`
- `lake env lean Checks/Assembly.lean (parent from child axioms; #print axioms); Checks/NoSymm.lean (#check of the Schwarz lemmas under frozen imports)`
- `lake env lean Checks/Proofs{A,U,D,B,C}.lean and Checks/Combined.lean (all children proved, parent proved, Expr-equality of declared vs contract types, #print axioms)`
- `lake build of /tmp/del-split-I5hsTm/proj-mod with the 6 theorems in namespace Submission and the Symmetric import; lake env lean Checks/Solution_*.lean (comparator NodeSolution files, exact Submission.X)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/UniformSpace/HeineCantor.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Group/Integral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/VectorMeasure/SetIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Continuous.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-el-higher-932635b125/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`

The snapshot pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The snapshot Contract.lean, the workspace Contract.lean and the workspace Submission.lean are byte-identical.

Neither the snapshot project nor any of the 486 DAG lean_names contains the prefix dohr_eb_ehs_del, so the 5 proposed names are fresh.

All cited Mathlib lemmas exist at the pin:
- ContDiffAt.isSymmSndFDerivAt: FDeriv/Symmetric.lean:533.
- fderiv_clm_apply: FDeriv/CompCLM.lean:143.
- fderiv_comp: FDeriv/Comp.lean:179 (the script uses fderiv_fun_comp).
- fderiv_comp_sub: FDeriv/Add.lean:892.
- support_fderiv_subset and tsupport_fderiv_subset: FDeriv/Const.lean:379 and 383.
- HasCompactSupport.fderiv: FDeriv/Const.lean:389.
- ContDiffOn.fderiv_of_isOpen and ContDiffOn.continuousOn_fderiv_of_isOpen: ContDiff/Defs.lean:907 and 916.
- ContDiff.continuous_fderiv: ContDiff/Defs.lean:1271.
- ContDiff.fderiv_right: ContDiff/Comp.lean:750.
- norm_image_sub_le_of_norm_fderiv_le': MeanValue.lean:549.
- IsCompact.exists_cthickening_subset_open: Thickening.lean:426.
- IsCompact.uniformContinuousOn_of_continuous: HeineCantor.lean:49.
- TendstoUniformlyOn.tendsto_at: UniformConvergence.lean:154.
- setIntegral_eq_of_subset_of_forall_sdiff_eq_zero and setIntegral_eq_integral_of_forall_compl_eq_zero: Bochner/Set.lean:466 and 486.
- tendsto_integral_filter_of_dominated_convergence: DominatedConvergence.lean:67.
- IntegrableOn.integrable_of_forall_notMem_eq_zero: IntegrableOn.lean:453.
- integrableOn_const: IntegrableOn.lean:119.
- ContinuousOn.aestronglyMeasurable: IntegrableOn.lean:791.
- integral_add_right_eq_self: the to_additive of Group/Integral.lean:101.
- norm_inner_le_norm: InnerProductSpace/Basic.lean:455.
- ContinuousOn.inner: InnerProductSpace/Continuous.lean:88.
- norm_le_insert': Normed/Group/Basic.lean:201.
- ContinuousOn.clm_apply: BoundedLinearMaps.lean:476.

Under the frozen imports, ContDiffAt.isSymmSndFDerivAt and second_derivative_symmetric(_of_eventually) are unknown (checked with #check). Only chain_symm needs to add import Mathlib.Analysis.Calculus.FDeriv.Symmetric. The conical-approximation solution branch already adds Mathlib imports, so this has precedent.

Rademacher.lean:103-195 (integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul and integral_lineDeriv_mul_eq) is the Mathlib template for the difference-quotient integration by parts. It requires global Lipschitz bounds and does not apply directly to F, which is only C^1 on U.

The snapshot has no ready-made lemma for any of the 5 children. The closest DAG item is dohr_eb_dql_diffQuot_tendstoUniformlyOn, accepted on another branch, which covers only E = Rn ℓ.

All 5 children, the parent assembly and the comparator NodeSolution targets compile at the pin with only propext, Classical.choice and Quot.sound.
