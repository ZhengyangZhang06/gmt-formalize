# Parent-supplied natural-language proof

- Parent DAG node: `root.harmonic_approximation-a1.poincare_inequality-a1`
- Child DAG node: `root.harmonic_approximation-a1.poincare_inequality-a1.smooth_estimate-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Step 1 of the parent proof ('Smooth estimate'), assembled from the two sibling lemmas: (1) Submission.poincare_c1_segment_sq_bound (key segment_bound) and (2) Submission.poincare_ball_convex_combination_bound (key convex_combination_bound).

Notation. B := B_r = ball(0, r), B_1 = ball(0, 1); |·| is Lebesgue measure on ℝ^n and λ Lebesgue measure on ℝ; all integrals are lintegrals in [0, ∞].

Proof.
1. Regularity. φ is C^1, so Dφ is continuous (ContDiff.continuous_fderiv, 1 ≠ 0) and ∇φ = toDual⁻¹ ∘ Dφ is continuous. Hence h(z) := ‖∇φ(z)‖ₑ² is measurable, and (x, y, t) ↦ h((1 − t)·y + t·x) is measurable both as a function on (ℝ^n × ℝ^n) × ℝ and as a function on (ℝ^n × ℝ) × ℝ^n (a measurable function composed with continuous maps).
2. Pointwise bound. Let x, y ∈ B. Then |x − y| ≤ |x| + |y| < 2r ≤ 2, so ‖x − y‖ₑ² ≤ 4, and by sibling (1): ‖φ(x) − φ(y)‖ₑ² ≤ ‖x − y‖ₑ² ∫⁻_{[0,1]} h((1 − t)·y + t·x) dt ≤ 4 ∫⁻_{[0,1]} h((1 − t)·y + t·x) dt.
3. Integrating step 2 over y ∈ B and then over x ∈ B (setLIntegral_mono') and pulling out the constant 4 (lintegral_const_mul', twice): ∫_B∫_B ‖φ(x) − φ(y)‖ₑ² dy dx ≤ 4 ∫_{x ∈ B}∫_{y ∈ B}∫_{t ∈ [0,1]} h((1 − t)·y + t·x) dt dy dx.
4. Tonelli. For each fixed x swap the y- and t-integrals (lintegral_lintegral_swap, measurability from step 1); then swap the x- and t-integrals (lintegral_lintegral_swap, using that (x, t) ↦ ∫_{y ∈ B} h((1 − t)·y + t·x) dy is measurable by Measurable.lintegral_prod_right'). Thus the triple integral equals ∫_{t ∈ [0,1]} (∫_{x ∈ B}∫_{y ∈ B} h((1 − t)·y + t·x) dy dx) dt.
5. For every t ∈ [0,1], sibling (2) applied to the measurable h, the radius r > 0 and t gives ∫_{x ∈ B}∫_{y ∈ B} h((1 − t)·y + t·x) dy dx ≤ 2^n |B| ∫_B h. Integrating over t ∈ [0,1] (setLIntegral_mono') and using λ([0,1]) = 1 (setLIntegral_const, Real.volume_Icc), the t-integral is ≤ 2^n |B| ∫_B h.
6. Hence ∫_B∫_B ‖φ(x) − φ(y)‖ₑ² ≤ 4 · 2^n |B| ∫_B h = 2^{n+2} |B_r| ∫_{B_r} ‖∇φ‖ₑ² (pow_add). Since r ≤ 1, B_r ⊆ B_1 and |B_r| ≤ |B_1| (measure_mono, ball_subset_ball), so the left side is ≤ 2^{n+2} |B_1| ∫_{B_r} ‖∇φ‖ₑ². ∎

Appendix: verified Lean proof. The following text was compiled on 2026-10-11 against the frozen contract (lean4 v4.35.0-rc3, Mathlib 25730c7c759d108ef87ab70af2342a196760f79d) inside namespace GMT.Ch05.Submission, with the two sibling theorems poincare_c1_segment_sq_bound and poincare_ball_convex_combination_bound declared earlier (their frozen statements) and no other Submission declarations; #print axioms reports only propext, Classical.choice, Quot.sound once the siblings are proved.
```lean
theorem poincare_c1_ball_double_integral_bound : ∀ (n : ℕ) (φ : Rn n → ℝ), ContDiff ℝ 1 φ → ∀ r : ℝ, 0 < r → r ≤ 1 → ∫⁻ x in ball (0 : Rn n) r, ∫⁻ y in ball (0 : Rn n) r, ‖φ x - φ y‖ₑ ^ 2 ≤ (2 : ℝ≥0∞) ^ (n + 2) * volume (ball (0 : Rn n) 1) * ∫⁻ x in ball (0 : Rn n) r, ‖gradient φ x‖ₑ ^ 2 := by
  intro n φ hφ r hr0 hr1
  set B := ball (0 : Rn n) r with hB
  have hgc : Continuous (gradient φ) :=
    (InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.comp (hφ.continuous_fderiv one_ne_zero)
  have hgm : Measurable (fun z => ‖gradient φ z‖ₑ ^ 2) := hgc.measurable.enorm.pow_const 2
  -- the integrand as a function of ((x, y), t), and of ((x, t), y)
  have hG1 : Measurable (fun p : (Rn n × Rn n) × ℝ => ‖gradient φ ((1 - p.2) • p.1.2 + p.2 • p.1.1)‖ₑ ^ 2) :=
    hgm.comp (by fun_prop : Continuous (fun p : (Rn n × Rn n) × ℝ => (1 - p.2) • p.1.2 + p.2 • p.1.1)).measurable
  have hG2 : Measurable (fun p : (Rn n × ℝ) × Rn n => ‖gradient φ ((1 - p.1.2) • p.2 + p.1.2 • p.1.1)‖ₑ ^ 2) :=
    hgm.comp (by fun_prop : Continuous (fun p : (Rn n × ℝ) × Rn n => (1 - p.1.2) • p.2 + p.1.2 • p.1.1)).measurable
  have step1 : ∀ x ∈ B, ∀ y ∈ B, ‖φ x - φ y‖ₑ ^ 2 ≤
      4 * ∫⁻ t in Icc (0:ℝ) 1, ‖gradient φ ((1 - t) • y + t • x)‖ₑ ^ 2 := by
    intro x hx y hy
    refine (poincare_c1_segment_sq_bound n φ hφ x y).trans ?_
    gcongr
    have hxy : ‖x - y‖ ≤ 2 := by
      have := norm_sub_le x y
      rw [hB, mem_ball, dist_zero_right] at hx hy
      linarith
    have : ‖x - y‖ₑ ≤ 2 := by
      rw [← ofReal_norm]
      calc ENNReal.ofReal ‖x - y‖ ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal hxy
        _ = 2 := by simp
    calc ‖x - y‖ₑ ^ 2 ≤ 2 ^ 2 := by gcongr
      _ = 4 := by norm_num
  calc ∫⁻ x in B, ∫⁻ y in B, ‖φ x - φ y‖ₑ ^ 2
      ≤ ∫⁻ x in B, ∫⁻ y in B, 4 * ∫⁻ t in Icc (0:ℝ) 1, ‖gradient φ ((1 - t) • y + t • x)‖ₑ ^ 2 := by
        refine setLIntegral_mono' measurableSet_ball fun x hx => ?_
        exact setLIntegral_mono' measurableSet_ball fun y hy => step1 x hx y hy
    _ = 4 * ∫⁻ x in B, ∫⁻ y in B, ∫⁻ t in Icc (0:ℝ) 1, ‖gradient φ ((1 - t) • y + t • x)‖ₑ ^ 2 := by
        rw [← lintegral_const_mul' _ _ (by norm_num)]
        congr 1; ext x
        rw [← lintegral_const_mul' _ _ (by norm_num)]
    _ = 4 * ∫⁻ t in Icc (0:ℝ) 1, ∫⁻ x in B, ∫⁻ y in B, ‖gradient φ ((1 - t) • y + t • x)‖ₑ ^ 2 := by
        congr 1
        have inner : ∀ x, ∫⁻ y in B, ∫⁻ t in Icc (0:ℝ) 1, ‖gradient φ ((1 - t) • y + t • x)‖ₑ ^ 2
            = ∫⁻ t in Icc (0:ℝ) 1, ∫⁻ y in B, ‖gradient φ ((1 - t) • y + t • x)‖ₑ ^ 2 := by
          intro x
          refine lintegral_lintegral_swap ?_
          exact (hG1.comp (measurable_const.prodMk measurable_fst |>.prodMk measurable_snd)).aemeasurable
        simp_rw [inner]
        refine lintegral_lintegral_swap ?_
        exact (hG2.lintegral_prod_right').aemeasurable
    _ ≤ 4 * ∫⁻ t in Icc (0:ℝ) 1, (2 : ℝ≥0∞) ^ n * volume B * ∫⁻ z in B, ‖gradient φ z‖ₑ ^ 2 := by
        gcongr 4 * ?_
        refine setLIntegral_mono' measurableSet_Icc fun t ht => ?_
        exact poincare_ball_convex_combination_bound n _ hgm r t hr0 ht.1 ht.2
    _ = 4 * ((2 : ℝ≥0∞) ^ n * volume B * ∫⁻ z in B, ‖gradient φ z‖ₑ ^ 2) := by
        rw [setLIntegral_const, Real.volume_Icc]; simp
    _ ≤ (2 : ℝ≥0∞) ^ (n + 2) * volume (ball (0 : Rn n) 1) * ∫⁻ x in B, ‖gradient φ x‖ₑ ^ 2 := by
        have hvol : volume B ≤ volume (ball (0 : Rn n) 1) := measure_mono (ball_subset_ball hr1)
        calc 4 * ((2 : ℝ≥0∞) ^ n * volume B * ∫⁻ z in B, ‖gradient φ z‖ₑ ^ 2)
            = (2 : ℝ≥0∞) ^ (n + 2) * volume B * ∫⁻ z in B, ‖gradient φ z‖ₑ ^ 2 := by
              rw [pow_add]; ring
          _ ≤ _ := by gcongr
```

## Key steps

1. ∇φ continuous, so h = ‖∇φ‖ₑ² and (x, y, t) ↦ h((1 − t)y + tx) are measurable
2. For x, y ∈ B_r: ‖x − y‖ₑ² ≤ 4, so sibling segment_bound gives ‖φ(x) − φ(y)‖ₑ² ≤ 4 ∫_[0,1] h((1 − t)y + tx) dt
3. Integrate over B_r × B_r and pull out 4
4. Tonelli twice to move the t-integral outermost
5. Sibling convex_combination_bound for each t ∈ [0,1], then λ([0,1]) = 1
6. 4 · 2^n = 2^{n+2} and |B_r| ≤ |B_1| for r ≤ 1

## Reference use

### local-project

Queries:
- `rg -n "theorem (lintegral_comp_smul|setLIntegral_comp_smul|lintegral_comp_mul_left|lintegral_comp_inv_smul|map_addHaar_smul|lintegral_comp_smul_of_pos|setLIntegral_comp_smul_of_pos|integral_comp_smul|setIntegral_comp_smul_of_pos|lintegral_add_right_eq_self|lintegral_add_left_eq_self|lintegral_sub_right_eq_self)" <snapshot>/mathlib/Mathlib`
- `rg -n "lintegral_comp_smul|lintegral_comp_mul|lintegral_add_right_eq_self|lintegral_add_left_eq_self|lintegral_sub_right_eq_self|lintegral_map_equiv|addHaar_smul\b|addHaar_preimage_smul|lintegral_smul_measure" <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean <snapshot>/mathlib/Mathlib/MeasureTheory/Group/LIntegral.lean <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `rg -n "theorem (lintegral_iUnion_of_directed|setLIntegral_iUnion_of_directed|tendsto_setLIntegral_of_monotone|lintegral_iSup_directed|lintegral_liminf_le|lintegral_iSup\b|lintegral_iSup'|tendstoInMeasure_of_tendsto_eLpNorm|exists_seq_tendsto_ae\b|eLpNorm_add_le|enorm_integral_le_lintegral_enorm|lintegral_mul_le_Lp_mul_Lq|setAverage_eq|lintegral_lintegral_swap|eLpNorm_eq_lintegral_rpow_enorm|integral_eq_sub_of_hasDerivAt|setLIntegral_measure_zero|lintegral_const_mul'|lintegral_prod_right'|Measure.restrict_iUnion_apply_eq_iSup|restrict_iUnion_le)" <snapshot>/mathlib/Mathlib`
- `rg -n "theorem (Measurable\.lintegral_prod_right'|ContDiff\.continuous_fderiv|toDual_symm_apply|lintegral_map|volume_Icc|MemLp\.integrable|eLpNorm_eq_lintegral_rpow_enorm|measure_ball_lt_top|measure_ball_pos|lintegral_add_left_eq_self|lintegral_mono_set|ofReal_toReal|ae_restrict_of_ae_restrict_of_subset|AEStronglyMeasurable\.mono_set|hasGradientAt_iff_hasFDerivAt|gradient_eq|lintegral_indicator|setLIntegral_le_lintegral)\b" <snapshot>/mathlib/Mathlib`
- `rg -n "lintegral_prod_right'|theorem eLpNorm_eq_lintegral_rpow|theorem eLpNorm_eq_eLpNorm'|theorem lintegral_rpow_enorm_eq_rpow_eLpNorm'|theorem lintegral_lintegral_swap|theorem prod_restrict|theorem restrict_prod_eq_prod_univ" <snapshot>/mathlib/Mathlib/MeasureTheory`
- `rg -l -i "poincar" <snapshot>/mathlib/Mathlib; rg -n -i "poincare_inequality|poincaré inequality|poincare inequality" <snapshot>/mathlib/Mathlib; rg -n -i "poincar" <snapshot>/project/GMT/Ch05/*.lean`
- `sed -n 330,370p <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean; sed -n 40,75p <snapshot>/mathlib/Mathlib/MeasureTheory/Group/LIntegral.lean; sed -n 660,690p <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean; sed -n 210,245p <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean; sed -n 265,300p and 445,470p <snapshot>/mathlib/Mathlib/MeasureTheory/Function/ConvergenceInMeasure.lean; sed -n 400,412p <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Average.lean`
- `head -n 460 GMT/Ch05/Contract.lean | cmp - <check prefix>; sha256sum GMT/Ch05/Contract.lean; python3 listing of lean_name fields in runs/20261011T142321Z-faafe12087/dag.json and nodes/root-harmonic-approximation-a1/decomposition-v1.json`
- `grep -rl <each proposed lean_name> .humanize ../.swarm-worktrees/*/gmt-ch05/GMT (collision check: 0 hits each)`
- `lake env lean /tmp/poincare-decomp-check-7c1/Check.lean (frozen contract + sibling (A) and six child types as sorry + sorry-free parent assembly)`
- `lake env lean /tmp/poincare-review-9q2/Full.lean; lake env lean /tmp/poincare-decomp-check-7c1/iso/T1.lean ... T6.lean (each child alone, declared siblings stubbed); lake env lean /tmp/poincare-decomp-check-7c1/iso/TAll.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Group/LIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/ConvergenceInMeasure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/TriangleInequality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/MeanInequalities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Average.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Dual.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/CurveIntegral/Poincare.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-harmonic-approximation-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-harmonic-approximation-a1-poincare-inequality-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/tmp/poincare-decomp-check-7c1/Check.lean`
- `/tmp/poincare-review-9q2/Full.lean`
- `/tmp/poincare-decomp-check-7c1/iso/TAll.lean`

Pinned snapshot: project ea5607598f3133b40a13241f2e51517a8c6423cd, Mathlib 25730c7c759d108ef87ab70af2342a196760f79d (manifest.json). The workspace and snapshot GMT/Ch05/Contract.lean are identical (sha256 c966f51efddb5a68ce15ef2a2a322fd9df0ca69da4626c7acef05b05d1691e12). The Lean checks reuse its first 460 lines byte-for-byte, with declarations placed in namespace GMT.Ch05.Submission.

No usable match: Mathlib has no Sobolev or W^{1,p} Poincaré inequality. rg -i 'poincar' finds only CurveIntegral/Poincare.lean (Poincaré lemma for curve integrals), Geometry/Manifold/PoincareConjecture.lean, UpperHalfPlane/Metric.lean, Dynamics/Ergodic/Conservative.lean and Lie/ring-theory files. 'Poincare' in the project is just the SimonGMT package namespace. The parent's own reference audit already showed no W^{1,2} Poincaré in simongmt; Chapter04/Poincare.lean is a varifold Poincaré-type inequality, a different statement. So the inequality must be built from the lemmas below.

Usable Mathlib API, all confirmed to exist and used in the verified child proofs:
- Change of variables and translation: Measure.map_addHaar_smul (Lebesgue/EqHaar.lean:336); lintegral_map (Integral/Lebesgue/Map.lean:27); lintegral_add_left_eq_self (to_additive of lintegral_mul_left_eq_self, Group/LIntegral.lean); finrank_euclideanSpace_fin.
- Directed unions and Fatou: setLIntegral_iUnion_of_directed (Integral/Lebesgue/Basic.lean:668), which needs no measurability; lintegral_iSup (Add.lean:36); lintegral_liminf_le (Add.lean:233); lintegral_const_mul' (Add.lean:420).
- Convergence in measure: tendstoInMeasure_of_tendsto_eLpNorm (ConvergenceInMeasure.lean:452), which in this version needs no measurability hypotheses; TendstoInMeasure.exists_seq_tendsto_ae (ConvergenceInMeasure.lean:273).
- Lp norms: eLpNorm_add_le (TriangleInequality.lean:54); eLpNorm_le_eLpNorm_mul_rpow_measure_univ and eLpNorm_eq_lintegral_rpow_enorm_toReal.
- Integrals and averages: enorm_integral_le_lintegral_enorm (Bochner/Basic.lean:333); setAverage_eq (Average.lean:402); MemLp.integrable (L1Space/Integrable.lean:657).
- Products: lintegral_lintegral_swap (Measure/Prod.lean:1071); Measurable.lintegral_prod_right' (Measure/Prod.lean:123).
- Calculus: intervalIntegral.integral_eq_sub_of_hasDerivAt (FundThmCalculus.lean:1148); ContDiff.continuous_fderiv (ContDiff/Defs.lean:1271); InnerProductSpace.toDual (Dual.lean); gradient (Gradient/Basic.lean).
- Balls and sets: Real.volume_Icc; measure_ball_pos; measure_ball_lt_top; ae_restrict_of_ae_restrict_of_subset.

Sibling (A) w12_ball_smooth_approximation has its frozen type taken from nodes/root-harmonic-approximation-a1/decomposition-v1.json. It is used only by the parent assembly. No proposed lean_name occurs in dag.json, any node JSON, or any swarm worktree.

Lean results:
(1) Check.lean (frozen contract, (A) and the six child types as sorry, sorry-free parent assembly) compiles. The only warnings are the seven expected 'declaration uses sorry'; there is none for w12_ball_poincare_inequality.
(2) Full proofs of all six children were written by an independent reviewer (Full.lean) and re-verified by me. Each child compiles in isolation with only its declared sibling dependencies stubbed (iso/T1–T6). The combined iso/TAll.lean compiles, and #print axioms gives [propext, Classical.choice, Quot.sound] for every child; the parent picks up sorryAx only through (A).

Public mathematical sources (textbook-level, cited in the child proofs): Gilbarg–Trudinger, Elliptic PDE of Second Order, Lemma 7.16 and (7.45) (Poincaré on convex domains, as cited by the parent); Evans, PDE, §5.8.1.
