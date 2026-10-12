# Parent-supplied natural-language proof

- Parent DAG node: `root.harmonic_approximation-a1.poincare_inequality-a1`
- Child DAG node: `root.harmonic_approximation-a1.poincare_inequality-a1.mean_deviation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Step 4 of the parent proof ('The mean': f(x) − λ = |B|^{−1} ∫_B (f(x) − f(y)) dy and Cauchy–Schwarz), for an arbitrary measurable set of finite measure. The hypothesis |s| < ∞ is essential (for |s| = ∞ the Bochner average is the junk value 0).

Notation. μ := Lebesgue measure restricted to s; |s| := volume s ∈ [0, ∞); λ := ⨍_s f = (volume.real s)^{−1} ∫_s f (setAverage_eq); integrals of nonnegative functions are lintegrals in [0, ∞].

Proof.
1. Null set. If |s| = 0 then volume.restrict s = 0 (Measure.restrict_eq_zero), so the left side is 0 and the claim holds. Assume |s| ≠ 0. Together with |s| ≠ ∞, μ is a finite measure with μ(ℝ^n) = |s|, and m := volume.real s = |s|.toReal > 0.
2. Representative. Let f' be strongly measurable with f = f' μ-a.e. (AEStronglyMeasurable.mk); then f' ∈ L²(μ) (memLp_congr_ae). Replacing f by f' changes neither the double integral (lintegral_congr_ae twice), nor λ (setAverage_eq and integral_congr_ae), nor the left side (its integrands agree μ-a.e.). Write f for f' from now on.
3. Reduction. Since |s|^{−1} ≠ ∞, |s|^{−1} ∫_s∫_s ‖f(x) − f(y)‖ₑ² dy dx = ∫_s |s|^{−1} ∫_s ‖f(x) − f(y)‖ₑ² dy dx (lintegral_const_mul'), so by monotonicity of the lintegral it suffices to show, for every x: ‖f(x) − λ‖ₑ² ≤ |s|^{−1} ∫_s ‖f(x) − f(y)‖ₑ² dy.
4. Representation. f ∈ L¹(μ) (MemLp.integrable with 1 ≤ 2, μ finite) and constants are μ-integrable, so ∫_s (f(x) − f(y)) dy = m f(x) − ∫_s f (integral_sub, integral_const). With λ = m^{−1} ∫_s f this gives f(x) − λ = m^{−1} ∫_s (f(x) − f(y)) dy (m ≠ 0).
5. First bound. ‖f(x) − λ‖ₑ = ‖m^{−1}‖ₑ · ‖∫_s (f(x) − f(y)) dy‖ₑ ≤ |s|^{−1} ∫_s ‖f(x) − f(y)‖ₑ dy, because ‖m^{−1}‖ₑ = ENNReal.ofReal(m^{−1}) = |s|^{−1} (ENNReal.ofReal_inv_of_pos, ENNReal.ofReal_toReal) and ‖∫u‖ₑ ≤ ∫⁻‖u‖ₑ (enorm_integral_le_lintegral_enorm).
6. Cauchy–Schwarz on s. For u(y) := f(x) − f(y) (a.e.-strongly measurable), comparing the L¹ and L² norms on the finite measure μ (eLpNorm_le_eLpNorm_mul_rpow_measure_univ with p = 1 ≤ q = 2, then eLpNorm_one_eq_lintegral_enorm and eLpNorm_eq_lintegral_rpow_enorm_toReal) gives ∫_s ‖u‖ₑ ≤ (∫_s ‖u‖ₑ²)^{1/2} |s|^{1/2}, hence (∫_s ‖u‖ₑ)² ≤ |s| ∫_s ‖u‖ₑ².
7. Combining 5 and 6: ‖f(x) − λ‖ₑ² ≤ (|s|^{−1})² (∫_s ‖u‖ₑ)² ≤ (|s|^{−1})² |s| ∫_s ‖u‖ₑ² = |s|^{−1} ∫_s ‖f(x) − f(y)‖ₑ² dy, using |s|^{−1}·|s| = 1 (ENNReal.inv_mul_cancel, 0 < |s| < ∞). By step 3 this proves the claim. ∎

Appendix: verified Lean proof. The following text was compiled on 2026-10-11 against the frozen contract (lean4 v4.35.0-rc3, Mathlib 25730c7c759d108ef87ab70af2342a196760f79d) inside namespace GMT.Ch05.Submission, with no imports beyond the contract and no other Submission declarations; #print axioms reports only propext, Classical.choice, Quot.sound.
```lean
theorem poincare_set_mean_deviation_sq_bound : ∀ (n : ℕ) (s : Set (Rn n)) (f : Rn n → ℝ), MeasurableSet s → volume s ≠ ∞ → MemLp f 2 (volume.restrict s) → ∫⁻ x in s, ‖f x - ⨍ y in s, f y‖ₑ ^ 2 ≤ (volume s)⁻¹ * ∫⁻ x in s, ∫⁻ y in s, ‖f x - f y‖ₑ ^ 2 := by
  intro n s f hs hfin hf
  -- 1. null set: the left side vanishes
  by_cases h0 : volume s = 0
  · have : volume.restrict s = 0 := Measure.restrict_eq_zero.mpr h0
    simp [this]
  -- 2. pass to a strongly measurable representative (no side changes)
  have hfa := hf.aestronglyMeasurable
  have hff' : f =ᵐ[volume.restrict s] hfa.mk f := hfa.ae_eq_mk
  have hf'L2 : MemLp (hfa.mk f) 2 (volume.restrict s) := (memLp_congr_ae hff').mp hf
  have hdbl : ∫⁻ x in s, ∫⁻ y in s, ‖f x - f y‖ₑ ^ 2 =
      ∫⁻ x in s, ∫⁻ y in s, ‖hfa.mk f x - hfa.mk f y‖ₑ ^ 2 := by
    have h1 : ∀ x, ∫⁻ y in s, ‖f x - f y‖ₑ ^ 2 = ∫⁻ y in s, ‖f x - hfa.mk f y‖ₑ ^ 2 := fun x =>
      lintegral_congr_ae (hff'.mono fun y hy => by simp [hy])
    simp_rw [h1]
    exact lintegral_congr_ae (hff'.mono fun x hx => by simp [hx])
  rw [hdbl]
  have havg : ⨍ y in s, f y = ⨍ y in s, hfa.mk f y := by
    rw [setAverage_eq, setAverage_eq, integral_congr_ae hff']
  rw [havg]
  set f' := hfa.mk f with hf'def
  set c := ⨍ y in s, f' y with hc
  rw [lintegral_congr_ae (g := fun x => ‖f' x - c‖ₑ ^ 2) (hff'.mono fun x hx => by simp only [hx])]
  have : IsFiniteMeasure (volume.restrict s) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hfin.lt_top⟩
  rw [← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr h0)]
  apply lintegral_mono
  intro x
  -- 3. f(x) - λ = |s|⁻¹ ∫_s (f(x) - f(y)) dy
  have hint : Integrable f' (volume.restrict s) := hf'L2.integrable one_le_two
  have hkey : f' x - c = (volume.real s)⁻¹ * ∫ y in s, (f' x - f' y) := by
    have hu : (volume.restrict s).real univ = volume.real s := by simp [Measure.real]
    have hreal : volume.real s ≠ 0 := by
      simp [Measure.real, ENNReal.toReal_eq_zero_iff, h0, hfin]
    rw [integral_sub (integrable_const _) hint, integral_const, hu, hc, setAverage_eq]
    simp only [smul_eq_mul]
    field_simp
  -- 4. Cauchy–Schwarz on s: (∫_s |u|)^2 ≤ |s| ∫_s |u|^2
  have hCS : (∫⁻ y in s, ‖f' x - f' y‖ₑ) ^ 2 ≤ volume s * ∫⁻ y in s, ‖f' x - f' y‖ₑ ^ 2 := by
    have hh : AEStronglyMeasurable (fun y => f' x - f' y) (volume.restrict s) :=
      aestronglyMeasurable_const.sub hint.aestronglyMeasurable
    have key := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2)
      (μ := volume.restrict s) one_le_two hh
    rw [eLpNorm_one_eq_lintegral_enorm hh,
      eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hh] at key
    have e1 : (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = 1 / 2 := by norm_num
    rw [e1, Measure.restrict_apply_univ] at key
    have e2 : ∀ y, ‖f' x - f' y‖ₑ ^ (2 : ℝ≥0∞).toReal = ‖f' x - f' y‖ₑ ^ 2 := fun y => by simp
    simp_rw [e2] at key
    calc (∫⁻ y in s, ‖f' x - f' y‖ₑ) ^ 2
        ≤ ((∫⁻ y in s, ‖f' x - f' y‖ₑ ^ 2) ^ (1 / (2 : ℝ≥0∞).toReal) *
            volume s ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
      _ = volume s * ∫⁻ y in s, ‖f' x - f' y‖ₑ ^ 2 := by
        rw [mul_pow, ← ENNReal.rpow_mul_natCast, ← ENNReal.rpow_mul_natCast]
        norm_num
        rw [mul_comm]
  -- 5. pointwise bound and conclusion
  have hnorm : ‖f' x - c‖ₑ ≤ (volume s)⁻¹ * ∫⁻ y in s, ‖f' x - f' y‖ₑ := by
    rw [hkey, enorm_mul]
    gcongr
    · rw [Measure.real, Real.enorm_eq_ofReal (inv_nonneg.mpr ENNReal.toReal_nonneg),
        ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos h0 hfin), ENNReal.ofReal_toReal hfin]
    · exact enorm_integral_le_lintegral_enorm _
  calc ‖f' x - c‖ₑ ^ 2 ≤ ((volume s)⁻¹ * ∫⁻ y in s, ‖f' x - f' y‖ₑ) ^ 2 := by gcongr
    _ = (volume s)⁻¹ ^ 2 * (∫⁻ y in s, ‖f' x - f' y‖ₑ) ^ 2 := by rw [mul_pow]
    _ ≤ (volume s)⁻¹ ^ 2 * (volume s * ∫⁻ y in s, ‖f' x - f' y‖ₑ ^ 2) := by gcongr
    _ = (volume s)⁻¹ * ∫⁻ y in s, ‖f' x - f' y‖ₑ ^ 2 := by
      rw [pow_two, ← mul_assoc, mul_assoc _ _ (volume s), ENNReal.inv_mul_cancel h0 hfin, mul_one]
```

## Key steps

1. If |s| = 0 both sides vanish; otherwise μ = Lebesgue|s is finite with total mass |s| ∈ (0, ∞)
2. Pass to a strongly measurable representative (average, double integral and left side unchanged)
3. Reduce to the pointwise bound ‖f(x) − λ‖ₑ² ≤ |s|^{−1} ∫_s ‖f(x) − f(y)‖ₑ² dy via lintegral_const_mul'
4. f(x) − λ = m^{−1} ∫_s (f(x) − f(y)) dy using integrability of f on s
5. ‖f(x) − λ‖ₑ ≤ |s|^{−1} ∫⁻_s ‖f(x) − f(y)‖ₑ
6. Cauchy–Schwarz (∫⁻_s ‖u‖ₑ)² ≤ |s| ∫⁻_s ‖u‖ₑ² and |s|^{−2}·|s| = |s|^{−1}

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
