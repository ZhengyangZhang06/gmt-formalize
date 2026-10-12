# Parent-supplied natural-language proof

- Parent DAG node: `root.harmonic_approximation-a1.poincare_inequality-a1`
- Child DAG node: `root.harmonic_approximation-a1.poincare_inequality-a1.exhaustion-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Step 3 of the parent proof ('r → 1': r_m = 1 − 1/(m + 2) increases to 1 and monotone convergence for the iterated lintegral), with the measurability bookkeeping of the parent's step 0 made explicit.

Notation. B_s := ball(0, s); D_u(S) := ∫_{x ∈ S}∫_{y ∈ S} ‖u(x) − u(y)‖ₑ² dy dx (lintegrals in [0, ∞]).

Proof.
1. Congruence. If S ⊆ ℝ^n and f₁ = f₂ a.e. for Lebesgue measure restricted to S, then D_{f₁}(S) = D_{f₂}(S): for every x the inner integrands y ↦ ‖f₁(x) − f₁(y)‖ₑ² and y ↦ ‖f₁(x) − f₂(y)‖ₑ² agree a.e. on S, and then the outer integrands x ↦ ∫_S ‖f₁(x) − f₂(y)‖ₑ² dy and x ↦ ∫_S ‖f₂(x) − f₂(y)‖ₑ² dy agree for a.e. x ∈ S (lintegral_congr_ae twice).
2. Representative. Let f' be strongly measurable with f = f' a.e. for Lebesgue measure restricted to B_1 (AEStronglyMeasurable.mk). For every r ≤ 1 we have B_r ⊆ B_1, so f = f' a.e. on B_r as well (ae_restrict_of_ae_restrict_of_subset).
3. Radii. r_m := 1 − 1/(m + 2) (m ∈ ℕ) satisfies 0 < r_m < 1 and is increasing, so S_m := B_{r_m} is an increasing (hence directed) sequence with ⋃_m S_m = B_1: each S_m ⊆ B_1, and if |x| < 1 choose m ∈ ℕ with m > 1/(1 − |x|) (exists_nat_gt); then 1/(m + 2) < 1 − |x|, i.e. |x| < r_m.
4. By steps 1–2 and the hypothesis (with r = r_m): D_{f'}(S_m) = D_f(S_m) ≤ K for every m, and D_f(B_1) = D_{f'}(B_1).
5. Let F(x, y) := ‖f'(x) − f'(y)‖ₑ², measurable on ℝ^n × ℝ^n, and G_m(x) := ∫_{S_m} F(x, y) dy; G_m is measurable in x (Measurable.lintegral_prod_right') and increasing in m (lintegral_mono_set). By the union formula for directed unions (setLIntegral_iUnion_of_directed, valid for arbitrary integrands): for every x, ∫_{B_1} F(x, y) dy = sup_m G_m(x); and ∫_{B_1} sup_m G_m = sup_k ∫_{S_k} sup_m G_m. By monotone convergence (lintegral_iSup): ∫_{S_k} sup_m G_m = sup_m ∫_{S_k} G_m. Hence D_{f'}(B_1) = sup_k sup_m ∫_{S_k} G_m.
6. For all k, m let p := max(k, m). Then ∫_{S_k} G_m ≤ ∫_{S_p} G_p = D_{f'}(S_p) ≤ K, by monotonicity of the lintegral in the domain (S_k ⊆ S_p) and in the integrand (S_m ⊆ S_p), and step 4. Therefore D_{f'}(B_1) ≤ K, and by step 4, D_f(B_1) ≤ K. ∎

Appendix: verified Lean proof. The following text was compiled on 2026-10-11 against the frozen contract (lean4 v4.35.0-rc3, Mathlib 25730c7c759d108ef87ab70af2342a196760f79d) inside namespace GMT.Ch05.Submission, with no imports beyond the contract and no other Submission declarations; #print axioms reports only propext, Classical.choice, Quot.sound.
```lean
theorem poincare_ball_double_integral_exhaustion : ∀ (n : ℕ) (f : Rn n → ℝ) (K : ℝ≥0∞), AEStronglyMeasurable f (volume.restrict (ball (0 : Rn n) 1)) → (∀ r : ℝ, 0 < r → r < 1 → ∫⁻ x in ball (0 : Rn n) r, ∫⁻ y in ball (0 : Rn n) r, ‖f x - f y‖ₑ ^ 2 ≤ K) → ∫⁻ x in ball (0 : Rn n) 1, ∫⁻ y in ball (0 : Rn n) 1, ‖f x - f y‖ₑ ^ 2 ≤ K := by
  intro n f K hf hK
  -- double integrals over s only depend on the a.e.-class of f on s
  have dbl : ∀ {s : Set (Rn n)} {f₁ f₂ : Rn n → ℝ}, f₁ =ᵐ[volume.restrict s] f₂ →
      ∫⁻ x in s, ∫⁻ y in s, ‖f₁ x - f₁ y‖ₑ ^ 2 = ∫⁻ x in s, ∫⁻ y in s, ‖f₂ x - f₂ y‖ₑ ^ 2 := by
    intro s f₁ f₂ h
    have h1 : ∀ x, ∫⁻ y in s, ‖f₁ x - f₁ y‖ₑ ^ 2 = ∫⁻ y in s, ‖f₁ x - f₂ y‖ₑ ^ 2 := fun x =>
      lintegral_congr_ae (h.mono fun y hy => by simp [hy])
    simp_rw [h1]
    exact lintegral_congr_ae (h.mono fun x hx => by simp [hx])
  have hff' := hf.ae_eq_mk
  have hm : StronglyMeasurable (hf.mk f) := hf.stronglyMeasurable_mk
  set f' := hf.mk f
  -- 1. radii r_m = 1 - 1/(m+2) ↑ 1
  let r : ℕ → ℝ := fun m => 1 - 1 / ((m : ℝ) + 2)
  have hr0 : ∀ m, 0 < r m := fun m => by
    have : (1 : ℝ) / ((m : ℝ) + 2) < 1 := by
      rw [div_lt_one (by positivity)]; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
    simp only [r]; linarith
  have hr1 : ∀ m, r m < 1 := fun m => by
    have : (0 : ℝ) < 1 / ((m : ℝ) + 2) := by positivity
    simp only [r]; linarith
  have hrmono : Monotone r := by
    intro a b hab
    simp only [r]
    have hab' : (a : ℝ) + 2 ≤ (b : ℝ) + 2 := by exact_mod_cast Nat.add_le_add_right hab 2
    have : (1 : ℝ) / ((b : ℝ) + 2) ≤ 1 / ((a : ℝ) + 2) :=
      one_div_le_one_div_of_le (by positivity) hab'
    linarith
  set B : ℕ → Set (Rn n) := fun m => ball 0 (r m) with hBdef
  have hBmono : Monotone B := fun a b hab => ball_subset_ball (hrmono hab)
  have hBdir : Directed (· ⊆ ·) B := hBmono.directed_le
  have hU : ⋃ m, B m = ball (0 : Rn n) 1 := by
    ext x
    simp only [mem_iUnion, mem_ball, dist_zero_right, B]
    constructor
    · rintro ⟨m, hm⟩; exact hm.trans (hr1 m)
    · intro hx
      have h1 : 0 < 1 - ‖x‖ := by linarith
      obtain ⟨m, hm⟩ := exists_nat_gt (1 / (1 - ‖x‖))
      refine ⟨m, ?_⟩
      simp only [r]
      have : 1 / ((m:ℝ) + 2) < 1 - ‖x‖ := by
        rw [div_lt_iff₀ (by positivity)]
        rw [div_lt_iff₀ h1] at hm
        nlinarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
      linarith
  -- 2. the hypothesis transfers to the representative
  have hK' : ∀ m, ∫⁻ x in B m, ∫⁻ y in B m, ‖f' x - f' y‖ₑ ^ 2 ≤ K := fun m => by
    rw [← dbl (ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (hr1 m).le) hff')]
    exact hK _ (hr0 m) (hr1 m)
  rw [dbl hff', ← hU]
  have hF : Measurable (fun p : Rn n × Rn n => ‖f' p.1 - f' p.2‖ₑ ^ 2) :=
    ((hm.measurable.comp measurable_fst).sub (hm.measurable.comp measurable_snd)).enorm.pow_const 2
  -- 3. inner integrals: continuity along the directed union
  have hG : ∀ x, ∫⁻ y in ⋃ m, B m, ‖f' x - f' y‖ₑ ^ 2 = ⨆ m, ∫⁻ y in B m, ‖f' x - f' y‖ₑ ^ 2 :=
    fun x => setLIntegral_iUnion_of_directed _ hBdir
  simp_rw [hG]
  -- 4. outer integral: union formula, then monotone convergence
  rw [setLIntegral_iUnion_of_directed _ hBdir]
  refine iSup_le fun k => ?_
  rw [lintegral_iSup (fun m => hF.lintegral_prod_right') (fun a b hab x => lintegral_mono_set (hBmono hab))]
  refine iSup_le fun m => ?_
  -- 5. diagonal comparison
  calc ∫⁻ x in B k, ∫⁻ y in B m, ‖f' x - f' y‖ₑ ^ 2
      ≤ ∫⁻ x in B (max k m), ∫⁻ y in B (max k m), ‖f' x - f' y‖ₑ ^ 2 := by
        refine (lintegral_mono_set (hBmono (le_max_left k m))).trans ?_
        exact lintegral_mono fun x => lintegral_mono_set (hBmono (le_max_right k m))
    _ ≤ K := hK' _
```

## Key steps

1. Double integrals over S depend only on the a.e.-class of f on S
2. Pass to a strongly measurable representative f' (valid on every B_r ⊆ B_1)
3. r_m = 1 − 1/(m + 2): increasing balls S_m with ⋃ S_m = B_1
4. Union formula for directed unions (setLIntegral_iUnion_of_directed) for inner and outer integrals
5. Monotone convergence for the measurable, increasing inner integrals G_m
6. Diagonal comparison ∫_{S_k} G_m ≤ D_{f'}(S_max(k,m)) ≤ K

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
