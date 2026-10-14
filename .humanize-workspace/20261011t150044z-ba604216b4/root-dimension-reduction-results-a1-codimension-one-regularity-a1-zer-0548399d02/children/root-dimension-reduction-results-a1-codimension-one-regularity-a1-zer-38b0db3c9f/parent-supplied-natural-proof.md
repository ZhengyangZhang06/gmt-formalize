# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.bv_compactness-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.bv_compactness-a1.smooth_translate-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Supplied proof of the parent node, step 4, first sentence: (u_i)_ε(v + h) − (u_i)_ε(v) = ∫₀¹∇(u_i)_ε(v + th)·h dt, followed by Tonelli and translation invariance (B_R + th ⊆ B_{R+1}). Here it is stated for an arbitrary C¹ function and with the sharper radius R + |h|. No sibling child is used.

Notation. B_ρ := ball(0, ρ). G(w) := ‖Df(w)‖ ∈ [0, ∞), which is continuous because f is C¹.

1. (FTC along a segment.) Fix v. The map t ↦ f(v + th) is differentiable on ℝ, with derivative Df(v + th)h (chain rule), and this derivative is continuous in t. By the fundamental theorem of calculus,
   f(v + h) − f(v) = ∫₀¹ Df(v + th)h dt.
2. (Pointwise bound.) Hence
   |f(v + h) − f(v)| ≤ ∫⁻_{(0,1]} |Df(v + th)h| dt ≤ |h|·∫⁻_{(0,1]} G(v + th) dt,
   using |Ah| ≤ ‖A‖|h|.
3. (Tonelli.) The map (v, t) ↦ G(v + th) is continuous, hence measurable. Integrate step 2 over v ∈ B_R and exchange the order of integration:
   ∫⁻_{B_R}|f(v + h) − f(v)| dv ≤ |h|·∫⁻_{t∈(0,1]} ∫⁻_{v∈B_R} G(v + th) dv dt.
4. (Translation.) For t ∈ (0, 1] we have |th| ≤ |h|. So v ∈ B_R implies |v + th| ≤ |v| + |h| < R + |h|, i.e. B_R ⊆ (· + th)⁻¹(B_{R+|h|}). Since v ↦ v + th preserves Lebesgue measure,
   ∫⁻_{v∈B_R} G(v + th) dv ≤ ∫⁻_{(·+th)⁻¹(B_{R+|h|})} G(v + th) dv = ∫⁻_{B_{R+|h|}} G(w) dw.
5. (Conclusion.) Integrating the constant ∫⁻_{B_{R+|h|}} G over t ∈ (0, 1] gives that constant, because L¹((0, 1]) = 1. Combining steps 3–5 proves the claim. ∎
If R ≤ 0 the left side is 0; if m = 0 then h = 0. Both cases are covered.

Appendix (Lean proof, kernel-checked). Compiled with the pinned toolchain (Lean v4.35.0-rc3, Mathlib 25730c7c) inside namespace GMT.Ch07 of a file importing GMT.Ch07.Submission, with the contract's opens. It is one declaration with no helper declaration and no set_option. #print axioms gives propext, Classical.choice and Quot.sound.

theorem Submission.codim1_zsl_pc_smooth_translate_l1 : ∀ (m : ℕ) (f : Euclid m → ℝ) (h : Euclid m) (R : ℝ), ContDiff ℝ 1 f → ∫⁻ v in ball (0 : Euclid m) R, ‖f (v + h) - f v‖ₑ ≤ ‖h‖ₑ * ∫⁻ w in ball (0 : Euclid m) (R + ‖h‖), ‖fderiv ℝ f w‖ₑ := by
  intro m f h R hf
  have hcont : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  have hdiff : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hGc : Continuous (fun w : Euclid m => ‖fderiv ℝ f w‖ₑ) := hcont.enorm
  have hGm : Measurable (fun w : Euclid m => ‖fderiv ℝ f w‖ₑ) := hGc.measurable
  have hshift : Continuous (fun p : Euclid m × ℝ => p.1 + p.2 • h) :=
    continuous_fst.add (continuous_snd.smul continuous_const)
  have hmeas2 : Measurable (uncurry fun (v : Euclid m) (t : ℝ) => ‖fderiv ℝ f (v + t • h)‖ₑ) :=
    (hGc.comp hshift).measurable
  -- Steps 1–2: pointwise bound via the fundamental theorem of calculus along `t ↦ v + t • h`
  have key : ∀ v : Euclid m, ‖f (v + h) - f v‖ₑ ≤
      ‖h‖ₑ * ∫⁻ t in Ioc (0 : ℝ) 1, ‖fderiv ℝ f (v + t • h)‖ₑ := by
    intro v
    have hseg : Continuous (fun t : ℝ => v + t • h) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => f (v + s • h))
        (fderiv ℝ f (v + t • h) h) t := by
      intro t
      have h1 : HasDerivAt (fun s : ℝ => v + s • h) h t :=
        (((hasDerivAt_id' t).smul_const h).const_add v).congr_deriv (one_smul ℝ h)
      exact (hdiff (v + t • h)).hasFDerivAt.comp_hasDerivAt t h1
    have hc1 : Continuous (fun t : ℝ => fderiv ℝ f (v + t • h) h) :=
      (hcont.comp hseg).clm_apply continuous_const
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
      (hc1.intervalIntegrable 0 1)
    simp only [one_smul, zero_smul, add_zero] at hFTC
    rw [← hFTC, intervalIntegral.integral_of_le zero_le_one]
    calc ‖∫ t in Ioc (0 : ℝ) 1, fderiv ℝ f (v + t • h) h‖ₑ
        ≤ ∫⁻ t in Ioc (0 : ℝ) 1, ‖fderiv ℝ f (v + t • h) h‖ₑ :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ t in Ioc (0 : ℝ) 1, ‖h‖ₑ * ‖fderiv ℝ f (v + t • h)‖ₑ :=
          lintegral_mono fun t =>
            (ContinuousLinearMap.le_opENorm (fderiv ℝ f (v + t • h)) h).trans_eq (mul_comm _ _)
      _ = ‖h‖ₑ * ∫⁻ t in Ioc (0 : ℝ) 1, ‖fderiv ℝ f (v + t • h)‖ₑ :=
          lintegral_const_mul _ (hGc.comp hseg).measurable
  have hmeasv : Measurable
      (fun v : Euclid m => ∫⁻ t in Ioc (0 : ℝ) 1, ‖fderiv ℝ f (v + t • h)‖ₑ) :=
    hmeas2.lintegral_prod_right
  -- Step 4: translation invariance of Lebesgue measure and inclusion of balls
  have hball : ∀ t ∈ Ioc (0 : ℝ) 1, ∫⁻ v in ball (0 : Euclid m) R, ‖fderiv ℝ f (v + t • h)‖ₑ ≤
      ∫⁻ w in ball (0 : Euclid m) (R + ‖h‖), ‖fderiv ℝ f w‖ₑ := by
    intro t ht
    have ht' : ‖t • h‖ ≤ ‖h‖ := by
      rw [norm_smul, Real.norm_of_nonneg ht.1.le]
      exact mul_le_of_le_one_left (norm_nonneg h) ht.2
    have hsub : ball (0 : Euclid m) R ⊆
        (fun v => v + t • h) ⁻¹' ball (0 : Euclid m) (R + ‖h‖) := by
      intro v hv
      rw [mem_preimage, mem_ball_zero_iff]
      exact (norm_add_le _ _).trans_lt (add_lt_add_of_lt_of_le (mem_ball_zero_iff.mp hv) ht')
    calc ∫⁻ v in ball (0 : Euclid m) R, ‖fderiv ℝ f (v + t • h)‖ₑ
        ≤ ∫⁻ v in (fun v => v + t • h) ⁻¹' ball (0 : Euclid m) (R + ‖h‖),
            ‖fderiv ℝ f (v + t • h)‖ₑ := lintegral_mono_set hsub
      _ = ∫⁻ w in ball (0 : Euclid m) (R + ‖h‖), ‖fderiv ℝ f w‖ₑ :=
          (measurePreserving_add_right volume (t • h)).setLIntegral_comp_preimage
            measurableSet_ball hGm
  -- Step 3 and 5: integrate, swap the order of integration (Tonelli), and conclude
  calc ∫⁻ v in ball (0 : Euclid m) R, ‖f (v + h) - f v‖ₑ
      ≤ ∫⁻ v in ball (0 : Euclid m) R,
          ‖h‖ₑ * ∫⁻ t in Ioc (0 : ℝ) 1, ‖fderiv ℝ f (v + t • h)‖ₑ := lintegral_mono key
    _ = ‖h‖ₑ * ∫⁻ v in ball (0 : Euclid m) R,
          ∫⁻ t in Ioc (0 : ℝ) 1, ‖fderiv ℝ f (v + t • h)‖ₑ := lintegral_const_mul _ hmeasv
    _ = ‖h‖ₑ * ∫⁻ t in Ioc (0 : ℝ) 1,
          ∫⁻ v in ball (0 : Euclid m) R, ‖fderiv ℝ f (v + t • h)‖ₑ :=
        congrArg (‖h‖ₑ * ·) (lintegral_lintegral_swap hmeas2.aemeasurable)
    _ ≤ ‖h‖ₑ * ∫⁻ t in Ioc (0 : ℝ) 1,
          ∫⁻ w in ball (0 : Euclid m) (R + ‖h‖), ‖fderiv ℝ f w‖ₑ :=
        mul_le_mul_right (setLIntegral_mono' measurableSet_Ioc hball) _
    _ = ‖h‖ₑ * ∫⁻ w in ball (0 : Euclid m) (R + ‖h‖), ‖fderiv ℝ f w‖ₑ := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one]

## Key steps

1. FTC: f(v + h) − f(v) = ∫₀¹ Df(v + th)h dt, so |f(v + h) − f(v)| ≤ |h|∫₀¹‖Df(v + th)‖ dt.
2. Tonelli: exchange ∫_{B_R} dv and ∫₀¹ dt.
3. Translation invariance: ∫_{B_R}‖Df(v + th)‖ dv ≤ ∫_{B_{R+|h|}}‖Df‖ for t ∈ [0, 1].
4. Integrate the constant over t ∈ (0, 1].

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; grep -A4 '"simongmt"' local-references/123e8435b4a2469b/project/lake-manifest.json`
- `sha256sum local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `rg -n 'theorem (IsCompact.tendsto_subseq|isCompact_univ_pi|measure_limsup_atTop_eq_zero|ae_eventually_notMem|tendsto_measure_iInter_atTop|lintegral_lintegral_swap|volume_pi_Ico|addHaar_closedBall |lintegral_liminf_le |integral_eq_sub_of_hasDerivAt |integral_comp_comm|exists_lt_subset_ball|tendsto_lintegral_of_dominated_convergence |measurable_to_countable'|preimage_floor_singleton|_root_.HasCompactSupport.hasFDerivAt_convolution_right|_root_.HasCompactSupport.contDiff_convolution_left|toDual_symm_apply|support_eq|tsupport_eq|one_of_mem_closedBall)' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -n 'exists_thickening_subset_open|trace_eq_sum_inner|integral_neg_eq_self|volume_preserving_ofLp|_root_.MeasurableSet.exists_isCompact_sdiff_lt|_root_.MeasurableSet.exists_isOpen_sdiff_lt|Int.measurable_floor|hasFDerivAt_apply' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -n -i 'kolmogorov|rellich|BoundedVariation|perimeter|caccioppoli' -l local-references/123e8435b4a2469b/mathlib/Mathlib; rg -n -i 'compactness|BV|perimeter' local-references/123e8435b4a2469b/project/GMT/Ch02/Contract.lean; rg -n -i 'theorem .*compact|TendstoLocallyInL1On' .lake/packages/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `lake env lean /tmp/bvc-split/Closure.lean (import-closure module list of GMT.Ch07.Submission filtered for Chapter02|Convolution|BumpFunction|HeineCantor|Floor)`
- `lake env lean /tmp/bvc-split/Ctx.lean and /tmp/bvc-split/Probe.lean (#check of about 35 cited lemmas in the contract scope)`
- `python3 scan of dag.json (lean_name, lean_statement, status) for reusable nodes: mollif|convolution|translation|integration by parts|divergence|trace|indicator|symmDiff|diagonal|subseq|StrictMono|BV|perimeter|cube; lookup of dorag_ha_lsc_ibp_c1_ball, dorag_ha_lsc_ibp_lipschitz, dgcr_stc_exists_normalized_mollifier, dorag_ha_rb_l2_subseq, cmc_fc_cs_diagonal_subseq, codim1_rdo_dg_bv_set_compactness`
- `uniqueness scan of the 11 names codim1_zsl_pc_* in dag.json, issue-workers.json, nodes/*/*.json|md, GMT/, .lake/packages/simongmt/Poincare and git grep over all 1661 refs; byte comparison of the frozen type of dorag_ha_lsc_ibp_c1_ball`
- `git show 46877ce9:GMT/Ch07/Submission.lean (accepted proofs of dorag_ha_lsc_ibp_lipschitz and dorag_ha_lsc_ibp_c1_ball); grep -n 'def check_source_delta' -A40 /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/leaf_verification.py; sed -n 4370,4390p and 6525,6570p /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `lake env lean /tmp/bvc-split/Types.lean, GlueT2.lean, agentT/T.lean, agentK/K.lean, agentK1/K1.lean, agentK23/K23.lean, agentT4a/T4a.lean, agentT4/T4.lean, agentT5/T5.lean, agentT2a/T2a.lean, agentT2b/T2b.lean and full/Full.lean (#print axioms of all 13 declarations)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/BorelCantelli.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Floor.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/Floor/Ring.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/WithLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Dual.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/ProperSpace/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-0548399d02/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-0b4bc9c57a/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/bvc-split/Types.lean`
- `/tmp/bvc-split/full/Full.lean`

Pins match.
- The snapshot manifest records project b4d606db and Mathlib 25730c7c; both equal workspace HEAD and .lake/packages/mathlib.
- The snapshot pins simongmt 2b366308.
- The snapshot Contract.lean and the workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f9503…).

Import closure.
- GMT.Ch07.Submission has 5034 modules. They include Mathlib.Analysis.Convolution, Analysis.Calculus.ContDiff.Convolution, BumpFunction.Basic/InnerProduct/FiniteDimension and Topology.UniformSpace.HeineCantor.
- They do not include BumpFunction.Normed, BumpFunction.Convolution, MeasureTheory.Function.Floor (so Int.measurable_floor is unavailable), LineDeriv integration by parts, or SimonGMT Chapter02.BV.

Snapshot Mathlib provides every tool the children use. Locations:
- Topology/Sequences.lean:298 IsCompact.tendsto_subseq
- Topology/Compactness/Compact.lean:1172 isCompact_univ_pi
- MeasureTheory/OuterMeasure/BorelCantelli.lean:62/92 measure_limsup_atTop_eq_zero, ae_eventually_notMem
- MeasureTheory/Measure/Continuity.lean:220 tendsto_measure_iInter_atTop
- MeasureTheory/Measure/Prod.lean:1071 lintegral_lintegral_swap
- MeasureTheory/Measure/Lebesgue/Basic.lean:262 volume_pi_Ico
- MeasureTheory/Measure/Lebesgue/EqHaar.lean:500 addHaar_closedBall
- MeasureTheory/Integral/Lebesgue/Add.lean:233 lintegral_liminf_le
- MeasureTheory/Integral/Lebesgue/DominatedConvergence.lean:48 tendsto_lintegral_of_dominated_convergence
- MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean:1148 integral_eq_sub_of_hasDerivAt
- MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean:70 integral_comp_comm
- MeasureTheory/Integral/Prod.lean:297 Integrable.mul_prod
- MeasureTheory/MeasurableSpace/Constructions.lean:42 measurable_to_countable'
- Algebra/Order/Floor/Ring.lean:154 preimage_floor_singleton
- Analysis/Calculus/ContDiff/Convolution.lean:61/427 hasFDerivAt_convolution_right, contDiff_convolution_left
- MeasureTheory/Measure/Regular.lean:385/843 exists_isOpen_sdiff_lt, exists_isCompact_sdiff_lt
- Topology/MetricSpace/Thickening.lean:439 exists_thickening_subset_open
- Analysis/InnerProductSpace/Trace.lean:25 trace_eq_sum_inner
- Analysis/InnerProductSpace/Dual.lean:178 toDual_symm_apply
- MeasureTheory/Measure/Haar/InnerProductSpace.lean:134 PiLp.volume_preserving_ofLp
- Topology/MetricSpace/ProperSpace/Lemmas.lean:45 exists_lt_subset_ball
- Analysis/Calculus/BumpFunction/Basic.lean:137/151/157 one_of_mem_closedBall, support_eq, tsupport_eq

No existing BV compactness to reuse.
- Mathlib has no Kolmogorov–Riesz or perimeter compactness; its BoundedVariation files are one-dimensional.
- The project's Ch02 BVCompactness is an unproved Prop definition outside the closure.
- SimonGMT BV.lean has only TendstoLocallyInL1On lemmas.

DAG.
- One theorem is reusable with an identical type: dorag_ha_lsc_ibp_c1_ball. It is accepted, candidate 46877ce9, its type is byte-identical, and its accepted dependency dorag_ha_lsc_ibp_lipschitz is in the same candidate history.
- dgcr_stc_exists_normalized_mollifier, dorag_ha_rb_l2_subseq and cmc_fc_cs_diagonal_subseq were not reused, because their types do not fit.
- The eleven new names codim1_zsl_pc_* have 0 hits in dag.json, issue-workers.json, the node files, GMT/, SimonGMT and all 1661 git refs.

Lean.
- Types.lean elaborates all 12 frozen types and proves the parent from them.
- Each child was proved separately, with siblings as stubs.
- Full.lean holds the accepted IBP proofs, the 11 new proofs and the parent assembly. It compiles in about 64 s, and #print axioms gives [propext, Classical.choice, Quot.sound] for every declaration, including the exact frozen parent type.
- check_source_delta forbids helper declarations and set_option in leaf proofs, which is why the argument is split into single-declaration children.
