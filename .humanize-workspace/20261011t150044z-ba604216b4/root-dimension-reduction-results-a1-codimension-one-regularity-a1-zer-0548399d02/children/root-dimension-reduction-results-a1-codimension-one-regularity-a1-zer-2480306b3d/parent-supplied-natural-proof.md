# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.bv_compactness-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.bv_compactness-a1.mollify_l1-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Supplied proof of the parent node, step 2, first half: f_ε(v) − f(v) = ∫ρ_ε(z)(f(v − z) − f(v)) dz, so by Tonelli ‖f_ε − f‖_{1,B_R} ≤ sup_{|z|≤ε}∫_{B_R}|f(v − z) − f(v)| dv. See also Simon Ch. 2, 2.5 (chapter-02.txt lines 531–546). Here ρ is an arbitrary continuous mollifier supported in closedBall(0, δ). Uses the sibling child translate_continuity (Submission.codim1_zsl_pc_translate_tendsto_zero).

Notation. u := 1_F; B_R := ball(0, R); F − y := {v : v + y ∈ F}; Φ(y) := L^m(((F − y) Δ F) ∩ B_R). Since |u(v + y) − u(v)| = 1_{(F − y) Δ F}(v), we have Φ(y) = ∫⁻_{B_R}|u(v + y) − u(v)| dv.

1. (Choice of δ.) By translate_continuity, Φ(y) → 0 as y → 0. Since ofReal η > 0, there is ε₀ > 0 with Φ(y) < ofReal η whenever |y| < ε₀ (Metric.eventually_nhds_iff). Put δ := ε₀/2 > 0. Then Φ(y) ≤ ofReal η whenever |y| ≤ δ. Note that δ depends only on m, F, R and η, as the order of quantifiers requires.
2. (Integrability.) Let ρ be continuous, ρ ≥ 0, ρ(z) = 0 for |z| > δ, and ∫ρ = 1. Then ρ has compact support (inside closedBall(0, δ)), so it is integrable. For each v the function z ↦ ρ(z)u(v − z) is measurable with |ρ(z)u(v − z)| ≤ ρ(z), hence integrable.
3. (Pointwise bound.) Using ∫ρ = 1,
   f(v) − u(v) = ∫ρ(z)u(v − z) dz − u(v)∫ρ(z) dz = ∫ρ(z)(u(v − z) − u(v)) dz.
   Hence |f(v) − u(v)| ≤ ∫⁻ |ρ(z)|·|u(v − z) − u(v)| dz (enorm_integral_le_lintegral_enorm).
4. (Tonelli.) The map (v, z) ↦ |ρ(z)|·|u(v − z) − u(v)| is measurable on ℝ^m × ℝ^m. Integrate step 3 over v ∈ B_R and exchange the integrals (lintegral_lintegral_swap). Since u(v − z) = u(v + (−z)), this gives
   ∫⁻_{B_R}|f − u| ≤ ∫⁻_z |ρ(z)|·(∫⁻_{v∈B_R}|u(v − z) − u(v)| dv) dz = ∫⁻_z |ρ(z)|·Φ(−z) dz.
5. (Bound.) If ρ(z) ≠ 0 then |z| ≤ δ, so |−z| ≤ δ and Φ(−z) ≤ ofReal η by step 1. If ρ(z) = 0 the integrand is 0. So the integrand is ≤ |ρ(z)|·ofReal η for every z. Since ρ ≥ 0 is integrable with ∫ρ = 1,
   ∫⁻|ρ|·ofReal η = (∫⁻|ρ|)·ofReal η = ofReal(∫ρ)·ofReal η = ofReal η.
   Therefore ∫⁻_{B_R}|f − u| ≤ ofReal η. ∎
The edge cases R ≤ 0 and m = 0 are covered by the same argument.

Appendix (Lean proof, kernel-checked). Compiled with the pinned toolchain (Lean v4.35.0-rc3, Mathlib 25730c7c) inside namespace GMT.Ch07 of a file importing GMT.Ch07.Submission, with the contract's opens and with the sibling Submission.codim1_zsl_pc_translate_tendsto_zero declared with its frozen type. It is one declaration with no helper declaration and no set_option. In the end-to-end file (all twelve children, the accepted proofs from commit 46877ce9, and the parent assembly), #print axioms gives propext, Classical.choice and Quot.sound.

theorem Submission.codim1_zsl_pc_mollify_indicator_l1 : ∀ (m : ℕ) (F : Set (Euclid m)) (R η : ℝ), MeasurableSet F → 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ ρ : Euclid m → ℝ, Continuous ρ → (∀ z, 0 ≤ ρ z) → (∀ z, δ < ‖z‖ → ρ z = 0) → ∫ z, ρ z = 1 → ∫⁻ v in ball (0 : Euclid m) R, ‖(∫ z, ρ z * F.indicator (fun _ => (1 : ℝ)) (v - z)) - F.indicator (fun _ => (1 : ℝ)) v‖ₑ ≤ ENNReal.ofReal η := by
  intro m F R η hF hη
  have hev : ∀ᶠ y in 𝓝 (0 : Euclid m),
      volume (symmDiff ((fun v => v + y) ⁻¹' F) F ∩ ball (0 : Euclid m) R) < ENNReal.ofReal η :=
    (Submission.codim1_zsl_pc_translate_tendsto_zero m F R hF).eventually
      (eventually_lt_nhds (ENNReal.ofReal_pos.2 hη))
  obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro ρ hρc hρ0 hρsupp hρ1
  -- facts about the indicator `u = 1_F`, which is then made opaque
  have hu_meas : Measurable (F.indicator (fun _ => (1 : ℝ))) := measurable_const.indicator hF
  have hu_bd : ∀ x, ‖F.indicator (fun _ => (1 : ℝ)) x‖ ≤ 1 := by
    intro x
    by_cases hx : x ∈ F <;> simp [hx]
  have hu_sd : ∀ v y : Euclid m,
      ‖F.indicator (fun _ => (1 : ℝ)) (v + y) - F.indicator (fun _ => (1 : ℝ)) v‖ₑ
        = (symmDiff ((fun w => w + y) ⁻¹' F) F).indicator 1 v := by
    intro v y
    by_cases h1 : v + y ∈ F <;> by_cases h2 : v ∈ F <;>
      simp [h1, h2, Set.mem_symmDiff]
  generalize F.indicator (fun _ => (1 : ℝ)) = u at hu_meas hu_bd hu_sd ⊢
  -- integrability of `ρ` (compact support) and of the convolution integrand
  have hρ_cs : HasCompactSupport ρ := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid m) (ε / 2)) fun x hx => ?_
    apply hρsupp
    simpa using hx
  have hρ_int : Integrable ρ := hρc.integrable_of_hasCompactSupport hρ_cs
  have hρ_meas : Measurable ρ := hρc.measurable
  have hint : ∀ v, Integrable (fun z => ρ z * u (v - z)) := by
    intro v
    refine hρ_int.mono
      (by exact (hρ_meas.mul (hu_meas.comp (measurable_const_sub v))).aestronglyMeasurable)
      (ae_of_all _ fun z => ?_)
    rw [norm_mul]
    calc ‖ρ z‖ * ‖u (v - z)‖ ≤ ‖ρ z‖ * 1 := by gcongr; exact hu_bd _
      _ = ‖ρ z‖ := mul_one _
  -- pointwise bound, using `∫ ρ = 1`
  have hpt : ∀ v, ‖(∫ z, ρ z * u (v - z)) - u v‖ₑ ≤ ∫⁻ z, ‖ρ z‖ₑ * ‖u (v - z) - u v‖ₑ := by
    intro v
    have h1 : (∫ z, ρ z * u (v - z)) - u v = ∫ z, (ρ z * u (v - z) - ρ z * u v) := by
      rw [integral_sub (hint v) (hρ_int.mul_const (u v)), integral_mul_const (u v) ρ, hρ1,
        one_mul]
    rw [h1]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun z => ?_
    rw [← mul_sub, enorm_mul]
  -- the inner integral is the translation defect of the stub
  have hΦ : ∀ z, ∫⁻ v in ball (0 : Euclid m) R, ‖u (v - z) - u v‖ₑ
      = volume (symmDiff ((fun v => v + -z) ⁻¹' F) F ∩ ball (0 : Euclid m) R) := by
    intro z
    have hS : MeasurableSet (symmDiff ((fun v => v + -z) ⁻¹' F) F) :=
      (hF.preimage (measurable_add_const _)).symmDiff hF
    rw [← Measure.restrict_apply hS, ← lintegral_indicator_one hS]
    refine lintegral_congr fun v => ?_
    rw [sub_eq_add_neg v z]
    exact hu_sd v (-z)
  have hmeas : Measurable (Function.uncurry fun (v z : Euclid m) =>
      ‖ρ z‖ₑ * ‖u (v - z) - u v‖ₑ) := by
    have : Measurable fun p : Euclid m × Euclid m => ‖ρ p.2‖ₑ * ‖u (p.1 - p.2) - u p.1‖ₑ :=
      (hρ_meas.comp measurable_snd).enorm.mul
        ((hu_meas.comp (measurable_fst.sub measurable_snd)).sub
          (hu_meas.comp measurable_fst)).enorm
    exact this
  calc ∫⁻ v in ball (0 : Euclid m) R, ‖(∫ z, ρ z * u (v - z)) - u v‖ₑ
      ≤ ∫⁻ v in ball (0 : Euclid m) R, ∫⁻ z, ‖ρ z‖ₑ * ‖u (v - z) - u v‖ₑ :=
        lintegral_mono fun v => hpt v
    _ = ∫⁻ z, ∫⁻ v in ball (0 : Euclid m) R, ‖ρ z‖ₑ * ‖u (v - z) - u v‖ₑ :=
        lintegral_lintegral_swap hmeas.aemeasurable
    _ = ∫⁻ z, ‖ρ z‖ₑ * ∫⁻ v in ball (0 : Euclid m) R, ‖u (v - z) - u v‖ₑ := by
        refine lintegral_congr fun z => ?_
        exact lintegral_const_mul _ (by fun_prop)
    _ ≤ ∫⁻ z, ‖ρ z‖ₑ * ENNReal.ofReal η := by
        refine lintegral_mono fun z => ?_
        by_cases hz : ρ z = 0
        · simp [hz]
        · have hz' : ‖z‖ ≤ ε / 2 := by
            by_contra h
            exact hz (hρsupp z (not_le.1 h))
          gcongr
          rw [hΦ z]
          refine (hεP ?_).le
          rw [dist_zero_right, norm_neg]
          linarith
    _ = (∫⁻ z, ‖ρ z‖ₑ) * ENNReal.ofReal η := lintegral_mul_const _ (by fun_prop)
    _ = ENNReal.ofReal η := by
        rw [← ofReal_integral_norm_eq_lintegral_enorm hρ_int]
        have : (fun x => ‖ρ x‖) = ρ := funext fun x => Real.norm_of_nonneg (hρ0 x)
        rw [this, hρ1, ENNReal.ofReal_one, one_mul]

## Key steps

1. translate_continuity gives δ > 0 with L(((F − y) Δ F) ∩ B_R) ≤ η for |y| ≤ δ.
2. ∫ρ = 1 gives |f(v) − 1_F(v)| ≤ ∫ρ(z)|1_F(v − z) − 1_F(v)| dz.
3. Tonelli: ∫_{B_R}|f − 1_F| ≤ ∫ρ(z)·L(((F + z) Δ F) ∩ B_R) dz.
4. ρ(z) ≠ 0 forces |z| ≤ δ, so the right side is ≤ η∫ρ = η.

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
