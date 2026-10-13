# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.mean_value-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.mean_value-a1.ball_of_kernel-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 6 of the parent proof (piecewise-linear profiles g_k → 1_{[0, r²)}, dominated convergence, and the reflection y ↦ x − y), with details.

1. (Profiles.) For k ∈ ℕ let g_k(t) := min{1, max{0, (k + 1)(r² − t)}}. Each g_k is continuous and 0 ≤ g_k ≤ 1. If t ≥ r² then (k + 1)(r² − t) ≤ 0, so g_k(t) = min{1, 0} = 0. In particular g_k(|y|²) = 0 whenever |y| ≥ r.

2. (Pointwise limit.) For every y, g_k(|y|²) → 1_{ball(0,r)}(y) as k → ∞.
- If |y| < r, then c := r² − |y|² > 0. Choose K ∈ ℕ with K ≥ 1/c. For k ≥ K, (k + 1)c ≥ 1, so g_k(|y|²) = 1.
- If |y| ≥ r, then g_k(|y|²) = 0 for all k, by step 1.

3. (Bounds.) closedBall(x, r) is compact and h is continuous on it, so there is A₀ with |h(z)| ≤ A₀ for all z ∈ closedBall(x, r).
- If |y| ≤ r, then x − y ∈ closedBall(x, r), so |h(x − y)·g_k(|y|²)| ≤ A₀.
- If |y| > r, the product is 0.
Hence |h(x − y)·g_k(|y|²)| ≤ A₀·1_{closedBall(0,r)}(y) and |g_k(|y|²)| ≤ 1_{closedBall(0,r)}(y). Both bounds are integrable: constants times the indicator of a set of finite measure.

4. (Measurability.) y ↦ g_k(|y|²) is continuous. The function y ↦ h(x − y)·g_k(|y|²) vanishes for |y| > r, so it equals its own product with 1_{closedBall(0,r)}. On the closed, hence measurable, set closedBall(0, r) it is continuous, because y ↦ x − y maps closedBall(0, r) into closedBall(x, r), where h is continuous. So it is a.e.-strongly measurable (ContinuousOn.aestronglyMeasurable together with aestronglyMeasurable_indicator_iff).

5. (Dominated convergence.) By tendsto_integral_of_dominated_convergence and steps 2–4,
a_k := ∫ h(x − y)·g_k(|y|²) dy → ∫ h(x − y)·1_{ball(0,r)}(y) dy, and
b_k := ∫ g_k(|y|²) dy → ∫ 1_{ball(0,r)}(y) dy.

6. (Use the hypothesis.) Each g_k is continuous and vanishes on [r², ∞) (step 1), so the hypothesis gives a_k = h(x)·b_k for all k. Hence a_k → h(x)·∫ 1_{ball(0,r)}, and by uniqueness of limits
∫ h(x − y)·1_{ball(0,r)}(y) dy = h(x)·∫ 1_{ball(0,r)}(y) dy.

7. (Left side.) h(x − y)·1_{ball(0,r)}(y) = 1_{ball(0,r)}(y)·h(x − y), so the left side is ∫_{ball(0,r)} h(x − y) dy (integral_indicator). The map φ(y) := x − y preserves Lebesgue measure (Measure.measurePreserving_sub_left) and is a measurable embedding, being a measurable equivalence. Also φ⁻¹(ball(x, r)) = ball(0, r), since |(x − y) − x| = |y|. Hence
∫_{ball(0,r)} h(x − y) dy = ∫_{φ⁻¹(ball(x,r))} h(φ(y)) dy = ∫_{ball(x,r)} h(z) dz (MeasurePreserving.setIntegral_preimage_emb).

8. (Right side.) ∫ 1_{ball(0,r)} = Lⁿ(ball(0, r)) as a real number (integral_indicator_one). By translation invariance (Measure.addHaar_ball_center), Lⁿ(ball(0, r)) = Lⁿ(ball(x, r)), which is finite; its real value is (volume(ball(x, r))).toReal.

9. Combining steps 6–8: ∫_{ball(x,r)} h = h(x)·(volume(ball(x, r))).toReal = (volume(ball(x, r))).toReal·h(x). ∎

Formalization appendix. Compiled at decomposition time inside namespace GMT.Ch07 under the frozen header, with no extra import (Lean 4.35.0-rc3, Mathlib 25730c7c). #print axioms reports propext, Classical.choice, Quot.sound. If a transcription detail fails, the numbered proof above is authoritative.

theorem Submission.dorag_ha_mv_ball_of_kernel : ∀ (n : ℕ) (h : Euclid n → ℝ) (x : Euclid n) (r : ℝ), 0 < r → ContinuousOn h (closedBall x r) → (∀ g : ℝ → ℝ, Continuous g → (∀ t : ℝ, r ^ 2 ≤ t → g t = 0) → ∫ y : Euclid n, h (x - y) * g (‖y‖ ^ 2) = h x * ∫ y : Euclid n, g (‖y‖ ^ 2)) → ∫ y in ball x r, h y = (volume (ball x r)).toReal * h x := by
  intro n h x r hr hhc hker
  set gk : ℕ → ℝ → ℝ := fun k t => min 1 (max 0 (((k : ℝ) + 1) * (r ^ 2 - t))) with hgk
  have gk_cont : ∀ k, Continuous (gk k) := fun k => by
    simp only [hgk]; fun_prop
  have gk_zero : ∀ k t, r ^ 2 ≤ t → gk k t = 0 := by
    intro k t ht
    simp only [hgk]
    have : ((k : ℝ) + 1) * (r ^ 2 - t) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    rw [max_eq_left this, min_eq_right zero_le_one]
  have gk_nonneg : ∀ k t, 0 ≤ gk k t := fun k t => le_min zero_le_one (le_max_left _ _)
  have gk_le : ∀ k t, gk k t ≤ 1 := fun k t => min_le_left _ _
  have gkz : ∀ k (y : Euclid n), r ≤ ‖y‖ → gk k (‖y‖ ^ 2) = 0 := fun k y hy =>
    gk_zero k _ (pow_le_pow_left₀ hr.le hy 2)
  have gk_lim : ∀ y : Euclid n, Tendsto (fun k => gk k (‖y‖ ^ 2)) atTop
      (𝓝 ((ball (0 : Euclid n) r).indicator 1 y)) := by
    intro y
    by_cases hy : ‖y‖ < r
    · rw [indicator_of_mem (by rwa [mem_ball, dist_zero_right]), Pi.one_apply]
      have hpos : 0 < r ^ 2 - ‖y‖ ^ 2 := by nlinarith [norm_nonneg y]
      obtain ⟨K, hK⟩ := exists_nat_ge (1 / (r ^ 2 - ‖y‖ ^ 2))
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop K] with k hk
      simp only [hgk]
      have hKk : (K : ℝ) ≤ k := by exact_mod_cast hk
      rw [div_le_iff₀ hpos] at hK
      have : 1 ≤ ((k : ℝ) + 1) * (r ^ 2 - ‖y‖ ^ 2) := by nlinarith
      rw [max_eq_right (by linarith), min_eq_left this]
    · push Not at hy
      rw [indicator_of_notMem (by rwa [mem_ball, dist_zero_right, not_lt])]
      exact tendsto_const_nhds.congr' (Eventually.of_forall fun k => (gkz k y hy).symm)
  obtain ⟨A₀, hA₀⟩ := (isCompact_closedBall x r).exists_bound_of_continuousOn hhc
  have hmem : ∀ y : Euclid n, ‖y‖ ≤ r → x - y ∈ closedBall x r := by
    intro y hy; rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg]; exact hy
  have hcb : ∀ y : Euclid n, y ∈ closedBall (0 : Euclid n) r ↔ ‖y‖ ≤ r := fun y => by
    rw [mem_closedBall, dist_zero_right]
  have hF_meas : ∀ k, AEStronglyMeasurable (fun y : Euclid n => h (x - y) * gk k (‖y‖ ^ 2)) volume := by
    intro k
    have : (fun y : Euclid n => h (x - y) * gk k (‖y‖ ^ 2)) =
        (closedBall (0 : Euclid n) r).indicator (fun y => h (x - y) * gk k (‖y‖ ^ 2)) := by
      funext y
      by_cases hy : ‖y‖ ≤ r
      · rw [indicator_of_mem ((hcb y).2 hy)]
      · rw [indicator_of_notMem (fun h' => hy ((hcb y).1 h')), gkz k y (le_of_not_ge hy), mul_zero]
    rw [this, aestronglyMeasurable_indicator_iff measurableSet_closedBall]
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_closedBall
    refine ContinuousOn.mul ?_ ((gk_cont k).comp (by fun_prop : Continuous fun y : Euclid n => ‖y‖ ^ 2)).continuousOn
    exact hhc.comp (by fun_prop : Continuous fun y : Euclid n => x - y).continuousOn
      (fun y hy => hmem y ((hcb y).1 hy))
  have hbint : ∀ c : ℝ, Integrable ((closedBall (0 : Euclid n) r).indicator fun _ => c) := fun c =>
    (integrableOn_const (measure_closedBall_lt_top (x := (0 : Euclid n)) (r := r)).ne).integrable_indicator
      measurableSet_closedBall
  have lim1 : Tendsto (fun k => ∫ y : Euclid n, h (x - y) * gk k (‖y‖ ^ 2)) atTop
      (𝓝 (∫ y : Euclid n, h (x - y) * (ball (0 : Euclid n) r).indicator 1 y)) := by
    refine tendsto_integral_of_dominated_convergence
      ((closedBall (0 : Euclid n) r).indicator fun _ => A₀) hF_meas (hbint A₀) ?_ ?_
    · intro k
      refine Eventually.of_forall fun y => ?_
      by_cases hy : ‖y‖ ≤ r
      · rw [indicator_of_mem ((hcb y).2 hy), norm_mul]
        have h1 := hA₀ _ (hmem y hy)
        have h2 : ‖gk k (‖y‖ ^ 2)‖ ≤ 1 := by
          rw [Real.norm_eq_abs, abs_of_nonneg (gk_nonneg _ _)]; exact gk_le _ _
        nlinarith [norm_nonneg (h (x - y)), norm_nonneg (gk k (‖y‖ ^ 2))]
      · rw [indicator_of_notMem (fun h' => hy ((hcb y).1 h')), gkz k y (le_of_not_ge hy), mul_zero,
          norm_zero]
    · exact Eventually.of_forall fun y => (gk_lim y).const_mul (h (x - y))
  have lim2 : Tendsto (fun k => ∫ y : Euclid n, gk k (‖y‖ ^ 2)) atTop
      (𝓝 (∫ y : Euclid n, (ball (0 : Euclid n) r).indicator 1 y)) := by
    refine tendsto_integral_of_dominated_convergence
      ((closedBall (0 : Euclid n) r).indicator fun _ => 1)
      (fun k => ((gk_cont k).comp (by fun_prop : Continuous fun y : Euclid n => ‖y‖ ^ 2)).aestronglyMeasurable)
      (hbint 1) ?_ (Eventually.of_forall gk_lim)
    intro k
    refine Eventually.of_forall fun y => ?_
    by_cases hy : ‖y‖ ≤ r
    · rw [indicator_of_mem ((hcb y).2 hy), Real.norm_eq_abs, abs_of_nonneg (gk_nonneg _ _)]
      exact gk_le _ _
    · rw [indicator_of_notMem (fun h' => hy ((hcb y).1 h')), gkz k y (le_of_not_ge hy), norm_zero]
  have heq : (fun k => ∫ y : Euclid n, h (x - y) * gk k (‖y‖ ^ 2)) =
      fun k => h x * ∫ y : Euclid n, gk k (‖y‖ ^ 2) :=
    funext fun k => hker (gk k) (gk_cont k) (gk_zero k)
  rw [heq] at lim1
  have hlim := tendsto_nhds_unique lim1 (lim2.const_mul (h x))
  have e1 : ∫ y : Euclid n, h (x - y) * (ball (0 : Euclid n) r).indicator 1 y = ∫ y in ball x r, h y := by
    have : (fun y : Euclid n => h (x - y) * (ball (0 : Euclid n) r).indicator 1 y) =
        (ball (0 : Euclid n) r).indicator (fun y => h (x - y)) := by
      funext y; by_cases hy : y ∈ ball (0 : Euclid n) r <;> simp [hy]
    rw [this, integral_indicator measurableSet_ball]
    have hmp : MeasurePreserving (fun y : Euclid n => x - y) volume volume :=
      Measure.measurePreserving_sub_left volume x
    have hpre : (fun y : Euclid n => x - y) ⁻¹' (ball x r) = ball 0 r := by
      ext y; simp [mem_ball, dist_eq_norm]
    rw [← hpre]
    exact hmp.setIntegral_preimage_emb (MeasurableEquiv.subLeft x).measurableEmbedding h (ball x r)
  have e2 : ∫ y : Euclid n, (ball (0 : Euclid n) r).indicator 1 y = (volume (ball x r)).toReal := by
    rw [integral_indicator_one measurableSet_ball, Measure.addHaar_ball_center volume x r]
    rfl
  rw [← e1, hlim, e2, mul_comm]

## Key steps

1. Use g_k(t) = min{1, max{0, (k+1)(r² − t)}}: continuous, 0 ≤ g_k ≤ 1, zero on [r², ∞), and g_k(|y|²) → 1_{ball(0,r)}(y) pointwise.
2. Apply the hypothesis to each g_k: ∫ h(x − y)·g_k(|y|²) = h(x)·∫ g_k(|y|²).
3. Dominated convergence with bounds A₀·1_{closedBall(0,r)} and 1_{closedBall(0,r)}, where A₀ = max |h| on closedBall(x, r); the integrands are measurable since they vanish off closedBall(0, r) and are continuous on it.
4. Identify the limits: ∫_{ball(0,r)} h(x − y) dy = ∫_{ball(x,r)} h by the measure-preserving reflection y ↦ x − y, and ∫ 1_{ball(0,r)} = volume(ball(x, r)).toReal by translation invariance.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json  (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean && cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean  (IDENTICAL)`
- `grep -rn 'theorem integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable|theorem integral_lineDeriv_mul_eq|theorem hasDerivAt_integral_of_dominated_loc_of_deriv_le|theorem integral_hasDerivAt_right|theorem HasFDerivAt.norm_sq|theorem hasStrictFDerivAt_norm_sq|theorem tsupport_eq|theorem iteratedFDeriv_two_apply|theorem exists_hasDerivAt_eq_slope|theorem constant_of_derivWithin_zero|theorem tendsto_integral_of_dominated_convergence|theorem cthickening_closedBall|theorem comp_right_fderiv|theorem fderiv_comp_sub' <snapshot>/mathlib/Mathlib`
- `grep -rn 'iteratedFDeriv_comp_add_left|iteratedFDeriv_comp_right|iteratedFDeriv_comp_sub|exists_cthickening_subset_open|lipschitzWith_of_hasCompactSupport|measurePreserving_sub_left|iteratedFDeriv_const_smul|ContinuousLinearEquiv.iteratedFDerivWithin_comp_right|inner_single_right|support_fderiv_subset|fderiv_comp_add_left|addHaar_ball_center' <snapshot>/mathlib/Mathlib`
- `sed -n 1,60p and 215,250p Analysis/Calculus/LineDeriv/IntegrationByParts.lean; sed -n 280,310p Analysis/Calculus/ParametricIntegral.lean; sed -n 940,985p Analysis/Calculus/ContDiff/FTaylorSeries.lean; sed -n 430,500p Analysis/Calculus/ContDiff/Basic.lean; sed -n 190,215p Analysis/InnerProductSpace/Calculus.lean`
- `grep -n '^theorem|^lemma|^def' Analysis/InnerProductSpace/Laplacian.lean; ls Analysis/InnerProductSpace/Harmonic/; grep -rn -E 'theorem .*(mean|Mean)' Analysis/InnerProductSpace/Harmonic/*.lean; grep -n '^theorem' Analysis/Complex/Harmonic/MeanValue.lean`
- `grep -rn -i -E 'mean_value|meanValue|mean value|laplacian|harmonic|integral_mul_fderiv|lineDeriv_mul' <snapshot>/project/GMT; grep -rln -i -E 'mean_value|meanValue|laplacian|harmonic' .lake/packages/simongmt; grep -n -E '^(theorem|lemma|def) ' SimonGMT/Chapter08/DistributionalConstancy.lean Chapter05/HarmonicEnergy.lean Chapter05/Basic.lean Chapter04/FirstVariation.lean`
- `sed -n 336,386p and 540,640p verifier/gmt-compare.py (child scope replay; only Contract.lean and build inputs are frozen, new Lean files allowed under GMT/Ch07/); git show <ref>:GMT/Ch07/Submission.lean | grep '^import' over all 957 refs (accepted branches add Mathlib/SimonGMT imports)`
- `python3 -I scan of dag.json (325 nodes) and nodes/*/*.json lean_name fields (566 distinct names) for the 6 proposed dorag_ha_mv_* names: no collision`
- `lean (toolchains/lean-4.35.0-rc3-linux, LEAN_PATH = workspace .lake builds) /tmp/mv-decomp/Scope.lean, Children.lean, Assembly.lean, Flux.lean, AffineTest.lean, RadialGreenTest.lean, DerivTest.lean, BallTest.lean, Avail.lean, AllChildren.lean, AllChildrenClean.lean (#print axioms)`
- `ls lake-packages-25730c7c/mathlib/.lake/build/lib/lean/Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.olean (present)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Equiv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Laplacian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Harmonic`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Complex/Harmonic/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Deriv/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Ball/Pointwise.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Equiv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter05/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter05/HarmonicEnergy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-9f82487345/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/.lake/build/lib/lean/Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.olean`
- `/tmp/mv-decomp/Children.lean`
- `/tmp/mv-decomp/Assembly.lean`
- `/tmp/mv-decomp/Flux.lean`
- `/tmp/mv-decomp/AffineTest.lean`
- `/tmp/mv-decomp/RadialGreenTest.lean`
- `/tmp/mv-decomp/DerivTest.lean`
- `/tmp/mv-decomp/BallTest.lean`
- `/tmp/mv-decomp/Avail.lean`
- `/tmp/mv-decomp/AllChildrenClean.lean`

Snapshot and scope:
- The snapshot pins project b4d606d and Mathlib 25730c7c.
- GMT/Ch07/Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean, so child types are checked in exactly the comparator scope.

Nothing reusable exists for this node:
- The project snapshot has none of the needed lemmas; Ch05 HarmonicApproximationLemma is only a Prop.
- SimonGMT has no mean value, Green or radial-potential lemma; Chapter05/Basic.lean only re-exports HarmonicOn vocabulary.
- Mathlib's only harmonic mean value theorem is HarmonicOnNhd.circleAverage_eq on ℂ (Complex/Harmonic/MeanValue.lean).
- Laplacian.lean has no composition-on-the-right lemma.
So the general-n argument must be built from the following pinned Mathlib lemmas.

Pinned Mathlib lemmas used by the children:
- integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (LineDeriv/IntegrationByParts.lean:226). It requires each factor to be differentiable only on the other's tsupport, which removes the parent's cutoff. The frozen header does not import it, so green_identity adds the import; the olean is present in the comparator package tree.
- hasDerivAt_integral_of_dominated_loc_of_deriv_le (ParametricIntegral.lean:286).
- Continuous.integral_hasStrictDerivAt, contDiff_one_iff_deriv, hasStrictFDerivAt_norm_sq / contDiff_norm_sq (InnerProductSpace/Calculus.lean:197,140).
- iteratedFDeriv_two_apply and iteratedFDeriv_comp_add_left (FTaylorSeries.lean:948,958).
- ContinuousLinearEquiv.iteratedFDerivWithin_comp_right (ContDiff/Basic.lean:436) and ContinuousLinearEquiv.comp_right_fderiv (FDeriv/Equiv.lean:227).
- fderiv_comp_add_left (FDeriv/Add.lean:867) and support_fderiv_subset (FDeriv/Const.lean:379).
- exists_hasDerivAt_eq_slope (Deriv/MeanValue.lean:123).
- IsCompact.exists_cthickening_subset_open (Thickening.lean:426) and cthickening_closedBall (Ball/Pointwise.lean:318).
- tendsto_integral_of_dominated_convergence (DominatedConvergence.lean:57), Measure.measurePreserving_sub_left, MeasurePreserving.setIntegral_preimage_emb and Measure.addHaar_ball_center (EqHaar.lean:418).
All except the IBP lemma are reachable from the frozen imports, as Avail.lean confirmed.

Comparator and names:
- gmt-compare.py freezes only Contract.lean and the build inputs, and allows new Lean files under GMT/Ch07/.
- The six dorag_ha_mv_* names are unreserved: no collision among the 566 lean_names in dag.json and the node files.

Lean checks:
- All six child types elaborate in comparator scope.
- Complete proofs of all six children compile, and so does the parent assembly of the exact frozen dorag_ha_mean_value type (AllChildrenClean.lean).
- Axioms are only propext, Classical.choice and Quot.sound.
