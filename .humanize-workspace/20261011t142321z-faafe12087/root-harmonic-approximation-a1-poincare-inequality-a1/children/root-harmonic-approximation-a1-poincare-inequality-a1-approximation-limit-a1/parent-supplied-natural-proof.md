# Parent-supplied natural-language proof

- Parent DAG node: `root.harmonic_approximation-a1.poincare_inequality-a1`
- Child DAG node: `root.harmonic_approximation-a1.poincare_inequality-a1.approximation_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Step 2 of the parent proof ('Passage to f on B_r': Minkowski, an a.e.-convergent subsequence, Fatou first in y and then in x), stated for an arbitrary approximating sequence of the form produced by the uncle lemma Submission.w12_ball_smooth_approximation, so that this lemma itself only needs the sibling (3) Submission.poincare_c1_ball_double_integral_bound (key smooth_estimate). The measurability hypothesis on g is essential (lintegrals of non-measurable functions are lower integrals).

Notation. B := B_r; μ := Lebesgue measure restricted to B (a finite measure); C := 2^{n+2}|B_1|, which is finite since |B_1| < ∞; ‖u‖_2 := eLpNorm u 2 μ. For a.e.-strongly measurable u, ‖u‖_2 = (∫‖u‖ₑ² dμ)^{1/2} (eLpNorm_eq_lintegral_rpow_enorm_toReal), hence ‖u‖_2² = ∫‖u‖ₑ² dμ, and if ∫‖u_j‖ₑ² dμ → 0 then ‖u_j‖_2 → 0 (continuity of a ↦ a^{1/2} on [0, ∞] and 0^{1/2} = 0).

Proof.
0. Representative. Let f' be strongly measurable with f = f' μ-a.e. (AEStronglyMeasurable.mk). Then ∫_B∫_B ‖f(x) − f(y)‖ₑ² = ∫_B∫_B ‖f'(x) − f'(y)‖ₑ²: for each x the inner integrands agree μ-a.e. in y, and then the outer integrands agree μ-a.e. in x (lintegral_congr_ae twice). Likewise ∫_B ‖φ_j − f'‖ₑ² = ∫_B ‖φ_j − f‖ₑ² → 0. So it suffices to prove the claim for f'.
1. Regularity. Each φ_j is continuous and ∇φ_j = toDual⁻¹ ∘ Dφ_j is continuous (φ_j is C^1).
2. A.e.-convergent subsequence. ‖φ_j − f'‖_2 → 0, hence φ_j → f' in μ-measure (tendstoInMeasure_of_tendsto_eLpNorm with p = 2 ≠ 0), and there is a strictly increasing ns : ℕ → ℕ with φ_{ns(i)}(x) → f'(x) for μ-a.e. x (TendstoInMeasure.exists_seq_tendsto_ae).
3. Inner Fatou. Fix x at which the convergence of step 2 holds (this is μ-a.e. x). For μ-a.e. y the convergence holds at y too; by continuity of (a, b) ↦ ‖a − b‖ₑ² : ℝ × ℝ → [0, ∞], ‖φ_{ns i}(x) − φ_{ns i}(y)‖ₑ² → ‖f'(x) − f'(y)‖ₑ², so ‖f'(x) − f'(y)‖ₑ² = liminf_i ‖φ_{ns i}(x) − φ_{ns i}(y)‖ₑ² (Tendsto.liminf_eq). By lintegral_congr_ae and Fatou's lemma (lintegral_liminf_le; each y ↦ ‖φ_{ns i}(x) − φ_{ns i}(y)‖ₑ² is measurable): ∫_B ‖f'(x) − f'(y)‖ₑ² dy ≤ liminf_i G_i(x), where G_i(x) := ∫_B ‖φ_{ns i}(x) − φ_{ns i}(y)‖ₑ² dy.
4. Outer Fatou. Each G_i is measurable (Measurable.lintegral_prod_right', the integrand being measurable on ℝ^n × ℝ^n). By step 3 (μ-a.e. in x; lintegral_mono_ae) and Fatou again: ∫_B∫_B ‖f'(x) − f'(y)‖ₑ² ≤ ∫_B liminf_i G_i ≤ liminf_i ∫_B G_i = liminf_i D_i, with D_i := ∫_B∫_B ‖φ_{ns i}(x) − φ_{ns i}(y)‖ₑ² dy dx.
5. Smooth estimate and Minkowski. By sibling (3) (φ_{ns i} is C^1 and 0 < r ≤ 1): D_i ≤ C ∫_B ‖∇φ_{ns i}‖ₑ² = C ‖∇φ_{ns i}‖_2². Writing ∇φ_{ns i} = g + (∇φ_{ns i} − g), Minkowski's inequality in L²(μ) (eLpNorm_add_le, 1 ≤ 2) gives ‖∇φ_{ns i}‖_2 ≤ ‖g‖_2 + ε_i with ε_i := ‖∇φ_{ns i} − g‖_2. Hence D_i ≤ C (‖g‖_2 + ε_i)².
6. Limit. Since ∇φ_j − g is a.e.-strongly measurable and ∫_B ‖∇φ_j − g‖ₑ² → 0, we get ‖∇φ_j − g‖_2 → 0, so ε_i → 0 (composition with ns, which tends to ∞; StrictMono.tendsto_atTop). By continuity of addition and squaring on [0, ∞] and of multiplication by the finite constant C (ENNReal.Tendsto.const_mul), C(‖g‖_2 + ε_i)² → C‖g‖_2².
7. Conclusion. ∫_B∫_B ‖f'(x) − f'(y)‖ₑ² ≤ liminf_i D_i ≤ liminf_i C(‖g‖_2 + ε_i)² (liminf_le_liminf) = C‖g‖_2² (Tendsto.liminf_eq) = C ∫_B ‖g‖ₑ² = 2^{n+2} |B_1| ∫_{B_r} ‖g‖ₑ². All steps are valid in [0, ∞], including the case ∫_{B_r} ‖g‖ₑ² = ∞. ∎

Appendix: verified Lean proof. The following text was compiled on 2026-10-11 against the frozen contract (lean4 v4.35.0-rc3, Mathlib 25730c7c759d108ef87ab70af2342a196760f79d) inside namespace GMT.Ch05.Submission, with the sibling theorem poincare_c1_ball_double_integral_bound declared earlier (its frozen statement) and no other Submission declarations; #print axioms reports only propext, Classical.choice, Quot.sound once the sibling is proved.
```lean
theorem poincare_approx_ball_double_integral_bound : ∀ (n : ℕ) (f : Rn n → ℝ) (g : Rn n → Rn n) (φ : ℕ → Rn n → ℝ) (r : ℝ), 0 < r → r ≤ 1 → AEStronglyMeasurable f (volume.restrict (ball (0 : Rn n) r)) → AEStronglyMeasurable g (volume.restrict (ball (0 : Rn n) r)) → (∀ j, ContDiff ℝ 1 (φ j)) → Tendsto (fun j => ∫⁻ x in ball (0 : Rn n) r, ‖φ j x - f x‖ₑ ^ 2) atTop (𝓝 0) → Tendsto (fun j => ∫⁻ x in ball (0 : Rn n) r, ‖gradient (φ j) x - g x‖ₑ ^ 2) atTop (𝓝 0) → ∫⁻ x in ball (0 : Rn n) r, ∫⁻ y in ball (0 : Rn n) r, ‖f x - f y‖ₑ ^ 2 ≤ (2 : ℝ≥0∞) ^ (n + 2) * volume (ball (0 : Rn n) 1) * ∫⁻ x in ball (0 : Rn n) r, ‖g x‖ₑ ^ 2 := by
  intro n f g φ r hr0 hr1 hf hg hφ h1 h2
  set B := ball (0 : Rn n) r with hB
  set μ : Measure (Rn n) := volume.restrict B with hμ
  set C : ℝ≥0∞ := (2 : ℝ≥0∞) ^ (n + 2) * volume (ball (0 : Rn n) 1) with hC
  have hCtop : C ≠ ∞ := ENNReal.mul_ne_top (by simp) measure_ball_lt_top.ne
  -- L² bookkeeping: eLpNorm u 2 μ = (∫ ‖u‖ₑ²)^{1/2}
  have eL2 : ∀ {E : Type} [NormedAddCommGroup E] {u : Rn n → E}, AEStronglyMeasurable u μ →
      eLpNorm u 2 μ = (∫⁻ x, ‖u x‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
    intro E _ u hu
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hu]
    simp
  have eL2sq : ∀ {E : Type} [NormedAddCommGroup E] {u : Rn n → E}, AEStronglyMeasurable u μ →
      eLpNorm u 2 μ ^ 2 = ∫⁻ x, ‖u x‖ₑ ^ 2 ∂μ := by
    intro E _ u hu
    rw [eL2 hu, ← ENNReal.rpow_mul_natCast]
    norm_num
  have tL2 : ∀ {E : Type} [NormedAddCommGroup E] {u : ℕ → Rn n → E},
      (∀ j, AEStronglyMeasurable (u j) μ) → Tendsto (fun j => ∫⁻ x, ‖u j x‖ₑ ^ 2 ∂μ) atTop (𝓝 0) →
      Tendsto (fun j => eLpNorm (u j) 2 μ) atTop (𝓝 0) := by
    intro E _ u hu h
    simp_rw [eL2 (hu _)]
    have := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp h
    rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at this
  -- 0. replace f by a strongly measurable representative (both sides unchanged)
  have hff' := hf.ae_eq_mk
  have hfm : StronglyMeasurable (hf.mk f) := hf.stronglyMeasurable_mk
  set f' := hf.mk f
  have hdbl : ∫⁻ x in B, ∫⁻ y in B, ‖f x - f y‖ₑ ^ 2 = ∫⁻ x in B, ∫⁻ y in B, ‖f' x - f' y‖ₑ ^ 2 := by
    have hin : ∀ x, ∫⁻ y in B, ‖f x - f y‖ₑ ^ 2 = ∫⁻ y in B, ‖f x - f' y‖ₑ ^ 2 := fun x =>
      lintegral_congr_ae (hff'.mono fun y hy => by simp [hy])
    simp_rw [hin]
    exact lintegral_congr_ae (hff'.mono fun x hx => by simp [hx])
  rw [hdbl]
  have h1' : Tendsto (fun j => ∫⁻ x in B, ‖φ j x - f' x‖ₑ ^ 2) atTop (𝓝 0) := by
    refine h1.congr fun j => ?_
    exact lintegral_congr_ae (hff'.mono fun x hx => by simp only [hx])
  have hφc : ∀ j, Continuous (φ j) := fun j => (hφ j).continuous
  have hgc : ∀ j, Continuous (gradient (φ j)) := fun j =>
    (InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.comp ((hφ j).continuous_fderiv one_ne_zero)
  -- 1. an a.e.-convergent subsequence
  have hconv : Tendsto (fun j => eLpNorm (φ j - f') 2 μ) atTop (𝓝 0) :=
    tL2 (fun j => (hφc j).aestronglyMeasurable.sub hfm.aestronglyMeasurable) h1'
  obtain ⟨ns, hns, hae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero hconv).exists_seq_tendsto_ae
  -- 2. Fatou, first in y then in x
  have hsqc : Continuous (fun p : ℝ × ℝ => ‖p.1 - p.2‖ₑ ^ 2) :=
    (ENNReal.continuous_pow 2).comp (continuous_enorm.comp (continuous_fst.sub continuous_snd))
  have hFatou : ∫⁻ x in B, ∫⁻ y in B, ‖f' x - f' y‖ₑ ^ 2 ≤
      liminf (fun i => ∫⁻ x in B, ∫⁻ y in B, ‖φ (ns i) x - φ (ns i) y‖ₑ ^ 2) atTop := by
    have hpt : ∀ᵐ x ∂μ, ∫⁻ y in B, ‖f' x - f' y‖ₑ ^ 2 ≤
        liminf (fun i => ∫⁻ y in B, ‖φ (ns i) x - φ (ns i) y‖ₑ ^ 2) atTop := by
      filter_upwards [hae] with x hx
      calc ∫⁻ y in B, ‖f' x - f' y‖ₑ ^ 2
          = ∫⁻ y in B, liminf (fun i => ‖φ (ns i) x - φ (ns i) y‖ₑ ^ 2) atTop := by
            refine lintegral_congr_ae ?_
            filter_upwards [hae] with y hy
            exact (((hsqc.tendsto _).comp (hx.prodMk_nhds hy)).liminf_eq).symm
        _ ≤ liminf (fun i => ∫⁻ y in B, ‖φ (ns i) x - φ (ns i) y‖ₑ ^ 2) atTop :=
            lintegral_liminf_le fun i =>
              ((measurable_const.sub (hφc _).measurable).enorm.pow_const 2)
    calc ∫⁻ x in B, ∫⁻ y in B, ‖f' x - f' y‖ₑ ^ 2
        ≤ ∫⁻ x in B, liminf (fun i => ∫⁻ y in B, ‖φ (ns i) x - φ (ns i) y‖ₑ ^ 2) atTop :=
          lintegral_mono_ae hpt
      _ ≤ liminf (fun i => ∫⁻ x in B, ∫⁻ y in B, ‖φ (ns i) x - φ (ns i) y‖ₑ ^ 2) atTop :=
          lintegral_liminf_le fun i =>
            ((((hφc _).measurable.comp measurable_fst).sub
              ((hφc _).measurable.comp measurable_snd)).enorm.pow_const 2).lintegral_prod_right'
  -- 3. the smooth estimate (sibling) plus Minkowski in L²(B_r)
  have hbound : ∀ i, ∫⁻ x in B, ∫⁻ y in B, ‖φ (ns i) x - φ (ns i) y‖ₑ ^ 2 ≤
      C * (eLpNorm g 2 μ + eLpNorm (gradient (φ (ns i)) - g) 2 μ) ^ 2 := by
    intro i
    refine (poincare_c1_ball_double_integral_bound n (φ (ns i)) (hφ _) r hr0 hr1).trans ?_
    gcongr
    rw [← eL2sq (hgc _).aestronglyMeasurable]
    gcongr
    calc eLpNorm (gradient (φ (ns i))) 2 μ
        = eLpNorm (g + (gradient (φ (ns i)) - g)) 2 μ := by rw [add_sub_cancel]
      _ ≤ _ := eLpNorm_add_le one_le_two
  have hε : Tendsto (fun j => eLpNorm (gradient (φ j) - g) 2 μ) atTop (𝓝 0) :=
    tL2 (fun j => (hgc j).aestronglyMeasurable.sub hg) h2
  have hlim : Tendsto (fun i => C * (eLpNorm g 2 μ + eLpNorm (gradient (φ (ns i)) - g) 2 μ) ^ 2)
      atTop (𝓝 (C * (eLpNorm g 2 μ + 0) ^ 2)) := by
    refine ENNReal.Tendsto.const_mul ?_ (Or.inr hCtop)
    exact ((ENNReal.continuous_pow 2).tendsto _).comp
      (tendsto_const_nhds.add (hε.comp hns.tendsto_atTop))
  -- 4. conclusion
  calc ∫⁻ x in B, ∫⁻ y in B, ‖f' x - f' y‖ₑ ^ 2
      ≤ liminf (fun i => ∫⁻ x in B, ∫⁻ y in B, ‖φ (ns i) x - φ (ns i) y‖ₑ ^ 2) atTop := hFatou
    _ ≤ liminf (fun i => C * (eLpNorm g 2 μ + eLpNorm (gradient (φ (ns i)) - g) 2 μ) ^ 2) atTop :=
        liminf_le_liminf (Eventually.of_forall hbound)
    _ = C * (eLpNorm g 2 μ + 0) ^ 2 := hlim.liminf_eq
    _ = C * ∫⁻ x in B, ‖g x‖ₑ ^ 2 := by rw [add_zero, eL2sq hg]
```

## Key steps

1. Replace f by a strongly measurable a.e.-representative; both sides and the hypothesis are unchanged
2. L² convergence φ_j → f on B_r gives convergence in measure and an a.e.-convergent subsequence φ_{ns i}
3. Inner Fatou in y for a.e. x, using continuity of (a, b) ↦ ‖a − b‖ₑ²
4. Outer Fatou in x (inner integrals measurable via Measurable.lintegral_prod_right')
5. Sibling smooth_estimate for each φ_{ns i} plus Minkowski: D_i ≤ C(‖g‖_2 + ‖∇φ_{ns i} − g‖_2)²
6. The right side converges to C‖g‖_2² = C ∫_{B_r} ‖g‖ₑ²; conclude with liminf_le_liminf and Tendsto.liminf_eq

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
