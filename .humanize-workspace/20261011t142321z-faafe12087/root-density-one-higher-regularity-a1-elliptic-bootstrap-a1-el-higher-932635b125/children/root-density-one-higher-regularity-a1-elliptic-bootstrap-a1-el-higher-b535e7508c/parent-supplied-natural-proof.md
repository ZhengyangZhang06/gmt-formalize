# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.el_higher_step-a1.differentiated_el-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.el_higher_step-a1.differentiated_el-a1.rhs_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 3, 4(b) and 9 of the parent proof of dohr_eb_ehs_differentiated_el (limit of the right side), with the uniform convergence of the difference quotients of zeta supplied by the sibling dohr_eb_ehs_del_diffquot_uniform.
Notation: Kz := tsupport zeta; phi_h(x) := h^{-1}(zeta(x) - zeta(x - he)); Dzeta(x)e := fderiv R zeta x e.
1. Margin. Kz is compact and Kz ⊆ U with U open, so there is delta > 0 with K' := cthickening delta Kz ⊆ U (IsCompact.exists_cthickening_subset_open); K' is compact (IsCompact.cthickening), hence closed and of finite Lebesgue measure. Put h0 := delta/(||e|| + 1) > 0.
2. Bounds. g is continuous on U ⊇ K' and K' is compact, so ||g(x)|| <= C_g for x in K'. The map x -> Dzeta(x)e is continuous (zeta is C^1), so ||Dzeta(x)e|| <= C_z for x in K'.
3. Rewriting. For all h and x, x - he = x + h(-e), so phi_h(x) = -h^{-1}(zeta(x + h(-e)) - zeta(x)), and Dzeta(x)e = -Dzeta(x)(-e) by linearity. Hence phi_h(x) - Dzeta(x)e = -(h^{-1}(zeta(x + h(-e)) - zeta(x)) - Dzeta(x)(-e)).
4. Uniform and pointwise convergence (sibling). zeta is C^1 on the open set R^n. Applying dohr_eb_ehs_del_diffquot_uniform with E := R^l, f := zeta, the open set R^n, the compact set K' and the direction -e, and using step 3: phi_h -> Dzeta(.)e uniformly on K' as h -> 0, h ≠ 0. Applying it with the compact set {x} in place of K': phi_h(x) -> Dzeta(x)e for every x in R^n.
5. Support. Let 0 < |h| < h0 and x outside K'. Then zeta(x) = 0 because x is not in Kz ⊆ K'; and zeta(x - he) = 0, since otherwise x - he would lie in Kz and dist(x, x - he) = |h| ||e|| < delta would give x in K'. Hence phi_h(x) = 0.
6. Domination. By step 4 there is a punctured neighbourhood of 0 on which, besides |h| < h0, ||phi_h(x) - Dzeta(x)e|| < 1 for all x in K'. For such h and x in K', ||phi_h(x)|| <= C_z + 1, and by Cauchy-Schwarz |<phi_h(x), g(x)>| <= (C_z + 1) C_g. For x outside K' the integrand is 0 by step 5. So |<phi_h(x), g(x)>| <= G(x) := (C_z + 1) C_g 1_{K'}(x) for every x.
7. Measurability and integrability. phi_h is continuous on R^n (zeta and translations are continuous) and g is continuous on U, so x -> <phi_h(x), g(x)> is continuous on U, hence a.e.-strongly measurable for Lebesgue measure restricted to the open (measurable) set U. G is integrable on U: it is a constant times the indicator of the compact set K', which has finite measure.
8. Limit. By step 4 and continuity of the inner product, <phi_h(x), g(x)> -> <Dzeta(x)e, g(x)> for every x. The filter 𝓝[≠] 0 is countably generated, so the dominated convergence theorem (tendsto_integral_filter_of_dominated_convergence, for Lebesgue measure restricted to U) yields ∫_U <phi_h(x), g(x)> dx -> ∫_U <Dzeta(x)e, g(x)> dx as h -> 0, h ≠ 0, which is the claim. (Equivalently, as in the parent's estimate (5): both integrands vanish off K' (Dzeta = 0 off Kz by support_fderiv_subset), so for small h, |∫_U <phi_h - Dzeta(.)e, g>| <= |K'| C_g sup_{K'} ||phi_h - Dzeta(.)e||, which tends to 0 by step 4.) QED
Lean note (verified at the pin, Lean 4.35.0-rc3, Mathlib 25730c7c, inside `namespace Submission`, with the sibling dohr_eb_ehs_del_diffquot_uniform available; #print axioms: propext, Classical.choice, Quot.sound; default maxSynthPendingDepth; no extra import).
- Verified script (tactic block of `theorem dohr_eb_ehs_del_rhs_tendsto`, whose type is exactly this node's lean_statement):
  intro n ℓ ζ g U e hU hζ hζc hζU hg
  obtain ⟨δ, hδ, hδU⟩ := hζc.isCompact.exists_cthickening_subset_open hU hζU
  have hK' : IsCompact (cthickening δ (tsupport ζ)) := hζc.isCompact.cthickening
  obtain ⟨Cg, hCg⟩ := hK'.exists_bound_of_continuousOn (hg.mono hδU)
  have hDζc : Continuous (fun x => fderiv ℝ ζ x e) :=
    (hζ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  obtain ⟨Cz, hCz⟩ := hK'.exists_bound_of_continuousOn hDζc.continuousOn
  have hUC := Submission.dohr_eb_ehs_del_diffquot_uniform n (Rn ℓ) ζ univ
    (cthickening δ (tsupport ζ)) (-e) isOpen_univ hζ.contDiffOn hK' (subset_univ _)
  have hφ : ∀ (h : ℝ) (x : Rn n), h⁻¹ • (ζ x - ζ (x - h • e)) =
      -(h⁻¹ • (ζ (x + h • (-e)) - ζ x)) := by
    intro h x
    rw [smul_neg, ← sub_eq_add_neg, ← smul_neg, neg_sub]
  have hDneg : ∀ x, fderiv ℝ ζ x e = -(fderiv ℝ ζ x (-e)) := by
    intro x; simp
  have he1 : 0 < ‖e‖ + 1 := by positivity
  have hpos : 0 < δ / (‖e‖ + 1) := div_pos hδ he1
  have hev : ∀ᶠ h in 𝓝[≠] (0 : ℝ), |h| < δ / (‖e‖ + 1) := by
    apply nhdsWithin_le_nhds
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hpos] with h hh
    simpa [Real.dist_eq] using hh
  have hev1 : ∀ᶠ h in 𝓝[≠] (0 : ℝ), ∀ x ∈ cthickening δ (tsupport ζ),
      ‖h⁻¹ • (ζ x - ζ (x - h • e)) - fderiv ℝ ζ x e‖ < 1 := by
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hUC) 1 one_pos] with h hh x hx
    have := hh x hx
    rw [dist_eq_norm] at this
    rw [hφ, hDneg, neg_sub_neg]
    exact this
  apply tendsto_integral_filter_of_dominated_convergence
    ((cthickening δ (tsupport ζ)).indicator (fun _ => (Cz + 1) * Cg))
  · filter_upwards with h
    apply ContinuousOn.aestronglyMeasurable _ hU.measurableSet
    apply ContinuousOn.inner _ hg
    have hζ0 := hζ.continuous
    exact Continuous.continuousOn (by fun_prop)
  · filter_upwards [hev, hev1] with h hh hh1
    filter_upwards with x
    by_cases hx : x ∈ cthickening δ (tsupport ζ)
    · rw [indicator_of_mem hx]
      have h1 : ‖h⁻¹ • (ζ x - ζ (x - h • e))‖ ≤ Cz + 1 := by
        have := hh1 x hx
        calc ‖h⁻¹ • (ζ x - ζ (x - h • e))‖
            = ‖(h⁻¹ • (ζ x - ζ (x - h • e)) - fderiv ℝ ζ x e) + fderiv ℝ ζ x e‖ := by
              rw [sub_add_cancel]
          _ ≤ ‖h⁻¹ • (ζ x - ζ (x - h • e)) - fderiv ℝ ζ x e‖ + ‖fderiv ℝ ζ x e‖ :=
              norm_add_le _ _
          _ ≤ 1 + Cz := by linarith [hCz x hx]
          _ = Cz + 1 := by ring
      calc ‖inner ℝ (h⁻¹ • (ζ x - ζ (x - h • e))) (g x)‖
          ≤ ‖h⁻¹ • (ζ x - ζ (x - h • e))‖ * ‖g x‖ := norm_inner_le_norm _ _
        _ ≤ (Cz + 1) * Cg := by
            gcongr
            · linarith [norm_nonneg (fderiv ℝ ζ x e), hCz x hx]
            · exact hCg x hx
    · rw [indicator_of_notMem hx]
      have h1 : ζ x = 0 := by
        by_contra h1
        exact hx (self_subset_cthickening _ (subset_tsupport _ h1))
      have h2 : ζ (x - h • e) = 0 := by
        by_contra h2
        apply hx
        apply mem_cthickening_of_dist_le x (x - h • e) δ (tsupport ζ) (subset_tsupport _ h2)
        rw [dist_eq_norm, sub_sub_cancel, norm_smul, Real.norm_eq_abs]
        calc |h| * ‖e‖ ≤ |h| * (‖e‖ + 1) := by gcongr; linarith
          _ ≤ δ / (‖e‖ + 1) * (‖e‖ + 1) := by gcongr
          _ = δ := div_mul_cancel₀ _ he1.ne'
      simp [h1, h2]
  · rw [integrable_indicator_iff hK'.isClosed.measurableSet]
    exact integrableOn_const (ne_of_lt (lt_of_le_of_lt
      (Measure.restrict_apply_le _ _) hK'.measure_lt_top))
  · filter_upwards with x
    apply Tendsto.inner _ tendsto_const_nhds
    have hx := (Submission.dohr_eb_ehs_del_diffquot_uniform n (Rn ℓ) ζ univ {x} (-e) isOpen_univ
      hζ.contDiffOn isCompact_singleton (subset_univ _)).tendsto_at (mem_singleton x)
    simp only [hφ, hDneg]
    exact hx.neg

## Key steps

1. margin: delta > 0 with K' := cthickening delta (tsupport zeta) ⊆ U; bounds C_g for ||g|| and C_z for ||Dzeta(.)e|| on K'
2. rewrite phi_h(x) = -h^{-1}(zeta(x + h(-e)) - zeta(x)) and apply sibling diffquot_uniform (E = R^l, open set R^n, direction -e) on K' and on singletons
3. for small h, phi_h vanishes off K' and |<phi_h, g>| <= (C_z + 1) C_g 1_{K'}
4. integrands are continuous on U; the bound is integrable; pointwise convergence by continuity of the inner product
5. dominated convergence along 𝓝[≠] 0

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
