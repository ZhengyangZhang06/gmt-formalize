# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.el_higher_step-a1.differentiated_el-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.el_higher_step-a1.differentiated_el-a1.diffquot_uniform-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 7 (and Step 9(a)-(b)) of the parent proof of dohr_eb_ehs_differentiated_el: uniform convergence of difference quotients by the mean value inequality and Heine-Cantor. It is stated once for a C^1 map with values in an arbitrary real normed space E (a type in universe 0, as in the Lean statement) so that it serves both the left side (F = DPsi o Du with values in L* = (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) and the right side (zeta with values in Rn ℓ).
1. Margin. K is compact and K ⊆ U with U open, so there is eps > 0 with K_eps := cthickening eps K = {z : dist(z, K) <= eps} ⊆ U (IsCompact.exists_cthickening_subset_open). K_eps is compact (IsCompact.cthickening) and contains K.
2. Regularity. Since f is C^1 on the open set U, f is differentiable at every point of U and Df = fderiv R f is continuous on U (ContDiffOn.continuousOn_fderiv_of_isOpen). Hence Df is uniformly continuous on the compact set K_eps (Heine-Cantor; IsCompact.uniformContinuousOn_of_continuous).
3. Constants. Let eta > 0. By step 2 choose theta > 0 such that ||Df(w) - Df(x)|| < eta/(||e|| + 1) whenever w, x lie in K_eps and ||w - x|| < theta. Put r := min(eps, theta)/(||e|| + 1) > 0. The set {h : 0 < |h| < r} belongs to the filter 𝓝[≠] 0.
4. Geometry. Let 0 < |h| < r and x in K. Then ||he|| = |h| ||e|| <= |h| (||e|| + 1) < min(eps, theta). The closed ball B(x, ||he||) is convex, contains x and x + he, and is contained in B(x, eps) ⊆ K_eps ⊆ U (closedBall_subset_cthickening). Hence the segment [x, x + he] lies in K_eps, and each w on it satisfies ||w - x|| <= ||he|| < theta.
5. Mean value inequality. On the segment f is differentiable (it lies in U), and ||Df(w) - Df(x)|| <= eta/(||e|| + 1) by steps 3-4 (w and x are in K_eps). The mean value inequality relative to the fixed linear map Df(x) (Convex.norm_image_sub_le_of_norm_fderiv_le') gives ||f(x + he) - f(x) - Df(x)(he)|| <= (eta/(||e|| + 1)) ||he||.
6. Division by h. Since h ≠ 0 and Df(x)(he) = h Df(x)e, we have Df(x)e - h^{-1}(f(x + he) - f(x)) = -h^{-1}(f(x + he) - f(x) - Df(x)(he)). Therefore ||h^{-1}(f(x + he) - f(x)) - Df(x)e|| <= |h|^{-1} (eta/(||e|| + 1)) |h| ||e|| = eta ||e||/(||e|| + 1) < eta.
7. Conclusion. For every eta > 0 the estimate of step 6 holds for all x in K and all h with 0 < |h| < r, i.e. eventually along 𝓝[≠] 0, uniformly in x in K. By the metric characterisation of uniform convergence (Metric.tendstoUniformlyOn_iff) this is exactly TendstoUniformlyOn (fun h x => h⁻¹ • (f (x + h • e) - f x)) (fun x => fderiv ℝ f x e) (𝓝[≠] 0) K. (The case e = 0 is included; then both sides vanish.) QED
Lean note (verified at the pin, Lean 4.35.0-rc3, Mathlib 25730c7c; #print axioms: propext, Classical.choice, Quot.sound; no extra import needed). The DAG node Submission.dohr_eb_dql_diffQuot_tendstoUniformlyOn (another branch, accepted, commit 33d90ae6) proves this statement only for E = Rn ℓ. The sibling lhs_limit needs E = (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ, and depends_on may only name siblings, so this node keeps the general E under a fresh name; its exact type is not that of the accepted node. The script below is the same argument with E general. Both uses instantiate it with full arguments: `dohr_eb_ehs_del_diffquot_uniform n _ F U (tsupport τ) e hU hF hK hτU` (E inferred as L*) and `dohr_eb_ehs_del_diffquot_uniform n (Rn ℓ) ζ univ K' (-e) isOpen_univ hζ.contDiffOn hK' (subset_univ _)`.
- Verified script (tactic block of `theorem dohr_eb_ehs_del_diffquot_uniform`, whose type is exactly this node's lean_statement):
  intro n E _ _ f U K e hU hf hK hKU
  obtain ⟨ε, hε, hεU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hK' : IsCompact (cthickening ε K) := hK.cthickening
  have hcont : ContinuousOn (fderiv ℝ f) U := hf.continuousOn_fderiv_of_isOpen hU le_rfl
  have huc : UniformContinuousOn (fderiv ℝ f) (cthickening ε K) :=
    hK'.uniformContinuousOn_of_continuous (hcont.mono hεU)
  have hdiff : ∀ z ∈ U, DifferentiableAt ℝ f z := fun z hz =>
    (hf.differentiableOn one_ne_zero z hz).differentiableAt (hU.mem_nhds hz)
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  rw [Metric.uniformContinuousOn_iff] at huc
  have he1 : 0 < ‖e‖ + 1 := by positivity
  obtain ⟨θ, hθ, hθK⟩ := huc (η / (‖e‖ + 1)) (div_pos hη he1)
  have hpos : 0 < min ε θ / (‖e‖ + 1) := div_pos (lt_min hε hθ) he1
  have hev : ∀ᶠ d in 𝓝[≠] (0 : ℝ), |d| < min ε θ / (‖e‖ + 1) := by
    apply nhdsWithin_le_nhds
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hpos] with d hd
    simpa [Real.dist_eq] using hd
  filter_upwards [hev, self_mem_nhdsWithin] with d hd hd0
  have hd0' : d ≠ 0 := hd0
  intro x hx
  have hde : ‖d • e‖ < min ε θ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |d| * ‖e‖ ≤ |d| * (‖e‖ + 1) := by gcongr; linarith
      _ < min ε θ / (‖e‖ + 1) * (‖e‖ + 1) := by gcongr
      _ = min ε θ := div_mul_cancel₀ _ he1.ne'
  have hball : closedBall x ‖d • e‖ ⊆ cthickening ε K :=
    (closedBall_subset_closedBall (hde.le.trans (min_le_left _ _))).trans
      (closedBall_subset_cthickening hx ε)
  have hxde : x + d • e ∈ closedBall x ‖d • e‖ := by
    rw [mem_closedBall, dist_eq_norm]; simp
  have hseg : segment ℝ x (x + d • e) ⊆ closedBall x ‖d • e‖ :=
    (convex_closedBall x _).segment_subset (mem_closedBall_self (norm_nonneg _)) hxde
  have hxK' : x ∈ cthickening ε K := self_subset_cthickening K hx
  have hmvt : ‖f (x + d • e) - f x - fderiv ℝ f x ((x + d • e) - x)‖ ≤
      η / (‖e‖ + 1) * ‖(x + d • e) - x‖ := by
    refine (convex_segment x (x + d • e)).norm_image_sub_le_of_norm_fderiv_le'
      (fun w hw => hdiff w (hεU (hball (hseg hw)))) (fun w hw => ?_) (left_mem_segment ℝ _ _)
      (right_mem_segment ℝ _ _)
    have hw := hseg hw
    have hwx : dist w x < θ := by
      rw [mem_closedBall] at hw
      exact hw.trans_lt (hde.trans_le (min_le_right _ _))
    have := hθK w (hball hw) x hxK' hwx
    rw [dist_eq_norm] at this
    exact this.le
  have hsub : (x + d • e) - x = d • e := by abel
  rw [hsub] at hmvt
  rw [dist_eq_norm]
  have hrw : fderiv ℝ f x e - d⁻¹ • (f (x + d • e) - f x) =
      -(d⁻¹ • (f (x + d • e) - f x - fderiv ℝ f x (d • e))) := by
    rw [map_smul, smul_sub d⁻¹ (f (x + d • e) - f x) (d • fderiv ℝ f x e), smul_smul,
      inv_mul_cancel₀ hd0', one_smul]; abel
  rw [hrw, norm_neg, norm_smul, norm_inv, Real.norm_eq_abs]
  calc |d|⁻¹ * ‖f (x + d • e) - f x - fderiv ℝ f x (d • e)‖
      ≤ |d|⁻¹ * (η / (‖e‖ + 1) * ‖d • e‖) := by gcongr
    _ = η * (‖e‖ / (‖e‖ + 1)) := by
      rw [norm_smul, Real.norm_eq_abs]; field_simp
    _ < η * 1 := by
      gcongr
      rw [div_lt_one he1]; linarith
    _ = η := mul_one η

## Key steps

1. choose eps > 0 with K_eps := cthickening eps K ⊆ U; K_eps is compact
2. Df is continuous on U, hence uniformly continuous on K_eps (Heine-Cantor)
3. for eta > 0 pick theta and restrict to 0 < |h| < min(eps, theta)/(||e|| + 1); the segment [x, x + he] lies in K_eps
4. mean value inequality relative to Df(x): ||f(x + he) - f(x) - Df(x)(he)|| <= eta ||he||/(||e|| + 1)
5. divide by |h| to get ||h^{-1}(f(x + he) - f(x)) - Df(x)e|| < eta uniformly on K

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
