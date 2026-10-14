# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.null_off_image-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.null_off_image-a1.smooth_cutoff_seq-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the cutoff construction in step 3 of the parent proof (K_j, r_j, smooth Urysohn functions b_j), stated for an arbitrary open set V ⊆ ℝⁿ = Euclid n.
1. (Compact exhaustion.) For j ∈ ℕ put K_j := {y ∈ ℝⁿ : (j+1)⁻¹ ≤ infEDist(y, ℝⁿ ∖ V)} ∩ closedBall(0, j), where infEDist is the [0,∞]-valued infimum distance (Metric.infEDist) and (j+1)⁻¹ is computed in [0,∞]. The map y ↦ infEDist(y, Vᶜ) is continuous (Metric.continuous_infEDist), so the first set is closed (isClosed_le against a constant). closedBall(0, j) is compact (isCompact_closedBall). Hence K_j is compact (IsCompact.inter_left).
2. (K_j ⊆ V.) Let y ∈ K_j and suppose y ∉ V. Then y ∈ Vᶜ, so infEDist(y, Vᶜ) = 0 (Metric.infEDist_zero_of_mem), and (j+1)⁻¹ ≤ 0 in [0,∞], i.e. (j+1)⁻¹ = 0. But (j+1)⁻¹ > 0 because j+1 ≠ ∞ (ENNReal.inv_pos). This is a contradiction, so K_j ⊆ V.
3. (Every point of V lies in K_j for all large j.) Let y ∈ V. As V is open, Vᶜ is closed, so y ∉ Vᶜ = closure(Vᶜ) and therefore infEDist(y, Vᶜ) > 0 (Metric.infEDist_pos_iff_notMem_closure; if V = ℝⁿ the infimum over ∅ is ∞). Since (j+1)⁻¹ → 0 in [0,∞] (ENNReal.tendsto_inv_nat_nhds_zero composed with j ↦ j+1, tendsto_add_atTop_nat), eventually (j+1)⁻¹ < infEDist(y, Vᶜ). Choose N ∈ ℕ with ‖y‖ ≤ N (exists_nat_ge). For j ≥ N, dist(y, 0) = ‖y‖ ≤ N ≤ j, i.e. y ∈ closedBall(0, j). Hence y ∈ K_j for all sufficiently large j.
4. (Radii.) Fix j. K_j is compact and contained in the open set V (step 2), so there is δ_j > 0 with cthickening(δ_j, K_j) ⊆ V (IsCompact.exists_cthickening_subset_open). Put r_j := δ_j / 2 > 0; then cthickening(2 r_j, K_j) ⊆ V.
5. (Smooth Urysohn functions.) The set thickening(2 r_j, K_j) is open (isOpen_thickening), cthickening(r_j, K_j) is closed (isClosed_cthickening), and cthickening(r_j, K_j) ⊆ thickening(2 r_j, K_j) because 0 < 2 r_j and r_j < 2 r_j (cthickening_subset_thickening'). Since ℝⁿ is a finite-dimensional real normed space, exists_contDiff_support_eq_eq_one_iff (with smoothness parameter ⊤ : ℕ∞) gives b_j : ℝⁿ → ℝ such that: b_j is ContDiff ℝ (⊤ : ℕ∞); range b_j ⊆ [0, 1]; support b_j = thickening(2 r_j, K_j); and for every x, x ∈ cthickening(r_j, K_j) ↔ b_j(x) = 1. Choose such r_j and b_j for every j (choice over j ∈ ℕ).
6. (Support and range.) tsupport b_j = closure(support b_j) = closure(thickening(2 r_j, K_j)) ⊆ cthickening(2 r_j, K_j) (closure_thickening_subset_cthickening) ⊆ V (step 4). The set cthickening(2 r_j, K_j) is compact because K_j is compact and ℝⁿ is proper (IsCompact.cthickening), and tsupport b_j is closed (isClosed_tsupport). So tsupport b_j is compact (IsCompact.of_isClosed_subset), i.e. HasCompactSupport b_j, and tsupport b_j ⊆ V. Since range b_j ⊆ [0, 1], 0 ≤ b_j(y) ≤ 1 for all y.
7. (Pointwise convergence.) Let y ∈ ℝⁿ.
- If y ∈ V, then 1_V(y) = 1. By step 3, for all large j we have y ∈ K_j ⊆ cthickening(r_j, K_j) (self_subset_cthickening), hence b_j(y) = 1 by step 5. The sequence (b_j(y)) is eventually constant equal to 1, so it converges to 1 = 1_V(y) (tendsto_const_nhds.congr').
- If y ∉ V, then 1_V(y) = 0. For every j, b_j(y) ≠ 0 would give y ∈ support b_j ⊆ tsupport b_j ⊆ V (subset_tsupport and step 6), which is impossible. So b_j(y) = 0 for every j, and the sequence converges to 0 = 1_V(y).
This proves all five properties. ∎

Appendix (reference only): a Lean script of exactly this argument. It was checked with `lake env lean` after `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the frozen contract's `open`s (project b4d606db, Mathlib 25730c7c), inserted before `main_theorem`. It compiles without `sorry` and uses only the axioms propext, Classical.choice and Quot.sound.
```lean
theorem Submission.cbr_ci_pw_noi_smooth_cutoff_seq : ∀ (n : ℕ) (V : Set (Euclid n)), IsOpen V → ∃ b : ℕ → Euclid n → ℝ, (∀ j, ContDiff ℝ (⊤ : ℕ∞) (b j)) ∧ (∀ j, HasCompactSupport (b j)) ∧ (∀ j, tsupport (b j) ⊆ V) ∧ (∀ j y, 0 ≤ b j y ∧ b j y ≤ 1) ∧ ∀ y, Tendsto (fun j => b j y) atTop (𝓝 (V.indicator (fun _ => (1 : ℝ)) y)) := by
  intro n V hV
  -- compact exhaustion `K j = {y : infEDist y Vᶜ ≥ 1/(j+1)} ∩ closedBall 0 j`
  set K : ℕ → Set (Euclid n) := fun j =>
    {y | ((j : ℝ≥0∞) + 1)⁻¹ ≤ infEDist y Vᶜ} ∩ closedBall 0 j with hK
  have hKc : ∀ j, IsCompact (K j) := fun j =>
    (isCompact_closedBall 0 (j : ℝ)).inter_left (isClosed_le continuous_const continuous_infEDist)
  have hKV : ∀ j, K j ⊆ V := by
    intro j y hy
    by_contra hyV
    have h1 : ((j : ℝ≥0∞) + 1)⁻¹ ≤ infEDist y Vᶜ := hy.1
    rw [infEDist_zero_of_mem hyV] at h1
    exact (ENNReal.inv_pos.mpr (by simp)).ne' (le_antisymm h1 bot_le)
  have hKev : ∀ y ∈ V, ∀ᶠ j in atTop, y ∈ K j := by
    intro y hy
    have hpos : 0 < infEDist y Vᶜ := by
      rw [infEDist_pos_iff_notMem_closure, hV.isClosed_compl.closure_eq]
      exact fun h => h hy
    have h1 : ∀ᶠ j : ℕ in atTop, ((j : ℝ≥0∞) + 1)⁻¹ ≤ infEDist y Vᶜ := by
      have ht : Tendsto (fun j : ℕ => ((j : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
        have := ENNReal.tendsto_inv_nat_nhds_zero
        exact (this.comp (tendsto_add_atTop_nat 1)).congr (fun j => by simp)
      filter_upwards [ht.eventually (gt_mem_nhds hpos)] with j hj using hj.le
    have h2 : ∀ᶠ j : ℕ in atTop, y ∈ closedBall (0 : Euclid n) j := by
      obtain ⟨N, hN⟩ := exists_nat_ge ‖y‖
      filter_upwards [eventually_ge_atTop N] with j hj
      rw [mem_closedBall, dist_zero_right]
      exact hN.trans (by exact_mod_cast hj)
    filter_upwards [h1, h2] with j hj1 hj2 using ⟨hj1, hj2⟩
  -- radii with `cthickening (2 r) (K j) ⊆ V`
  have hr : ∀ j, ∃ r : ℝ, 0 < r ∧ cthickening (2 * r) (K j) ⊆ V := by
    intro j
    obtain ⟨δ, hδ, hsub⟩ := (hKc j).exists_cthickening_subset_open hV (hKV j)
    exact ⟨δ / 2, by positivity, by rwa [mul_div_cancel₀ _ two_ne_zero]⟩
  choose r hr0 hrV using hr
  -- smooth Urysohn functions
  have hb : ∀ j, ∃ f : Euclid n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ range f ⊆ Icc 0 1 ∧
      support f = thickening (2 * r j) (K j) ∧ ∀ x, x ∈ cthickening (r j) (K j) ↔ f x = 1 := by
    intro j
    exact exists_contDiff_support_eq_eq_one_iff isOpen_thickening isClosed_cthickening
      (cthickening_subset_thickening' (by linarith [hr0 j]) (by linarith [hr0 j]) _)
  choose b hbsmooth hbrange hbsupp hbone using hb
  have htsupp : ∀ j, tsupport (b j) ⊆ cthickening (2 * r j) (K j) := by
    intro j
    rw [tsupport, hbsupp]
    exact closure_thickening_subset_cthickening _ _
  refine ⟨b, hbsmooth, ?_, ?_, ?_, ?_⟩
  · intro j
    exact (hKc j).cthickening.of_isClosed_subset (isClosed_tsupport _) (htsupp j)
  · intro j
    exact (htsupp j).trans (hrV j)
  · intro j y
    exact hbrange j ⟨y, rfl⟩
  · intro y
    by_cases hy : y ∈ V
    · rw [indicator_of_mem hy]
      apply tendsto_const_nhds.congr'
      filter_upwards [hKev y hy] with j hj
      exact ((hbone j y).mp (self_subset_cthickening _ hj)).symm
    · rw [indicator_of_notMem hy]
      apply tendsto_const_nhds.congr'
      filter_upwards with j
      by_contra hne
      exact hy ((htsupp j).trans (hrV j) (subset_tsupport _ (Ne.symm hne)))
```

## Key steps

1. Compact exhaustion K_j := {y : infEDist(y, Vᶜ) ≥ (j+1)⁻¹} ∩ closedBall(0, j): each K_j is compact, K_j ⊆ V, and every y ∈ V lies in K_j for all large j.
2. Radii r_j > 0 with cthickening(2r_j, K_j) ⊆ V (IsCompact.exists_cthickening_subset_open).
3. Smooth Urysohn function b_j (exists_contDiff_support_eq_eq_one_iff): values in [0,1], support = thickening(2r_j, K_j), and b_j = 1 exactly on cthickening(r_j, K_j).
4. tsupport b_j ⊆ cthickening(2r_j, K_j), which is compact and contained in V.
5. b_j(y) is eventually 1 for y ∈ V and identically 0 for y ∉ V, so b_j → 1_V pointwise.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); git show b1f7ad57dc2d4b5bf68702805f4f51beebe5d575:GMT/Ch07/Submission.lean (proof base = frozen contract only, 457 lines, no helper declarations)`
- `python3 -I scans of dag.json: lean_name prefix cbr_ci_pw (17 existing names; cbr_ci_pw_noi_smooth_cutoff_seq, cbr_ci_pw_noi_restrict_eq_of_smooth_test, cbr_ci_pw_noi_setIntegral_eq_preimage each occur 0 times); accepted lean_statements containing Measure+HasCompactSupport+ContDiff or withDensity/toMeasurable/'μ G = ν G' (found rsd_mw_tfa_smooth_cutoff, cmc_ml_measure_eq_of_eq_on_open_subsets, cbr_setIntegral_eq_of_integral_eq, rsd_ae_tendsto_withDensity_div_closedBall; none has a needed type)`
- `rg -n in local-references/123e8435b4a2469b/mathlib/Mathlib: 'theorem exists_contDiff_support_eq_eq_one_iff' (Geometry/Manifold/PartitionOfUnity.lean:789), 'exists_cthickening_subset_open' (Topology/MetricSpace/Thickening.lean:426), 'IsCompact.cthickening' (Thickening.lean:283), "theorem cthickening_subset_thickening'" (Thickening.lean:261), 'theorem closure_thickening_subset_cthickening' (:293), 'theorem self_subset_cthickening' (:313), 'theorem continuous_infEDist' / 'theorem infEDist_zero_of_mem' / 'theorem infEDist_pos_iff_notMem_closure' (Topology/MetricSpace/HausdorffDistance.lean:140/107/174, namespace Metric, capital-D infEDist), 'theorem tendsto_inv_nat_nhds_zero' (Topology/Instances/ENNReal/Lemmas.lean:486)`
- `rg -n in the snapshot Mathlib: 'theorem tendsto_integral_of_dominated_convergence' (MeasureTheory/Integral/DominatedConvergence.lean:57), 'theorem integral_indicator_one' (Integral/Bochner/Set.lean:533), 'theorem ext_of_generate_finite' (Measure/Typeclasses/Finite.lean:458), 'theorem isPiSystem_isOpen' (Constructions/BorelSpace/Basic.lean:81), 'class BorelSpace' (BorelSpace/Basic.lean:113), 'theorem integral_withDensity_eq_integral_toReal_smul₀' (Integral/Bochner/ContinuousLinearMap.lean:311, root namespace), 'theorem isFiniteMeasure_withDensity_ofReal' (Function/L1Space/HasFiniteIntegral.lean:310), 'Measure.isFiniteMeasure_map' (Measure/Typeclasses/Finite.lean:124), 'theorem integral_map ' (Integral/Bochner/Basic.lean:1081), 'theorem integral_add_measure' (Bochner/Basic.lean:1012), 'theorem integral_sub ' (Bochner/Basic.lean:263)`
- `rg -n in the snapshot Mathlib: 'Continuous.integrable_of_hasCompactSupport' (Function/LocallyIntegrable.lean:622), 'Continuous.bounded_above_of_compact_support' (Analysis/Normed/Group/Bounded.lean:153), 'theorem Integrable.mul_bdd' / 'theorem Integrable.pos_part' (Function/L1Space/Integrable.lean:1072/948), 'max_zero_sub_max_neg_zero_eq_self' (Algebra/Order/Group/MinMax.lean, to_additive), "theorem toReal_ofReal'" (Basic/ENNReal/Basic.lean:255), "toReal_eq_toReal_iff'" (Basic/ENNReal/Basic.lean:431), 'theorem toReal_add ' (Basic/ENNReal/Real.lean:41), 'theorem integral_eq_lintegral_pos_part_sub_lintegral_neg_part' (Bochner/Basic.lean:486), 'theorem withDensity_apply ' (Measure/WithDensity.lean:44), 'theorem map_apply (hf : Measurable f)' (Measure/Map.lean:170), 'theorem restrict_restrict (hs' (Measure/Restrict.lean:205), 'theorem measure_toMeasurable_inter_of_sFinite' (Typeclasses/SFinite.lean:477), 'theorem integral_eq_zero_iff_of_nonneg_ae' (Bochner/Basic.lean:763), 'theorem ae_restrict_of_ae_restrict_of_subset' (Measure/Restrict.lean:654)`
- `rg -n 'theorem ext_of_forall_integral_eq|theorem ext_of_integral|ext_of_integral_eq_on_compactlySupported|ae_eq_zero_of_integral_contDiff_smul_eq_zero' in the snapshot Mathlib (RieszMarkovKakutani/Real.lean:412 needs equal integrals for all of C_c(X, ℝ) and regular measures; Analysis/Distribution/AEEqOfIntegralContDiff.lean:205 concerns one locally integrable function, not a push-forward measure; HasOuterApproxClosed.lean:269 needs all bounded continuous functions)`
- `lake env lean /tmp/noi-decomp/T0.lean, T2.lean, T3.lean (#check reachability after import GMT.Ch07.Submission; instance check IsFiniteMeasure → IsFiniteMeasureOnCompacts)`
- `lake env lean /tmp/noi-decomp/C1.lean (child 1 fully proved), C2.lean (child 2 from child 1), C3.lean (child 3 from child 2), Asm.lean and Full.lean (all four theorems, no sorry; #print axioms → propext, Classical.choice, Quot.sound), SubTest.lean (the four theorems inserted into a copy of GMT/Ch07/Submission.lean before main_theorem; only the frozen main_theorem sorry remains)`
- `python3 -I validate_lean_statement from verifier/lean_contract.py on the three child types (pass); regex replica of leaf_verification.check_source_delta forbidden-token test on each proof body (no match)`
- `sed of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_decompose: node depth 5 < max_depth 6; _existing_lean_name_problem; _install_parent_supplied_child_handoff), leaf_verification.py check_source_delta, prompts.py DECOMPOSE / DECOMPOSITION_AUDIT / RLCR_LEAN_TASK`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-c27abc1fef/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-c27abc1fef/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L1Space/HasFiniteIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/Group/MinMax.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/prompts.py`
- `/tmp/noi-decomp/C1.lean`
- `/tmp/noi-decomp/C2.lean`
- `/tmp/noi-decomp/C3.lean`
- `/tmp/noi-decomp/Asm.lean`
- `/tmp/noi-decomp/Full.lean`
- `/tmp/noi-decomp/SubTest.lean`

The snapshot (project b4d606db, Mathlib 25730c7c) contract equals the workspace Contract.lean and Submission.lean, and proof base b1f7ad57 adds no helper declarations. Every Mathlib lemma cited in the three child proofs exists in the snapshot under the cited name (note Metric.infEDist with a capital D and the root-namespace integral_withDensity_eq_integral_toReal_smul₀) and is reachable from import GMT.Ch07.Submission. No Mathlib or DAG declaration has the exact child types: Measure.ext_of_integral_eq_on_compactlySupported needs all C_c(X) tests and regular measures; IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero concerns a single locally integrable function, not a push-forward; and the accepted cmc_ml_measure_eq_of_eq_on_open_subsets and rsd_mw_tfa_smooth_cutoff have different types. The three proposed names are absent from dag.json. All child types elaborate in the contract scope and pass validate_lean_statement. Complete Lean proofs of the three children, and of the frozen parent from child 3 alone, compile in a copy of Submission.lean with standard axioms only, and the forbidden-token check is clean.
