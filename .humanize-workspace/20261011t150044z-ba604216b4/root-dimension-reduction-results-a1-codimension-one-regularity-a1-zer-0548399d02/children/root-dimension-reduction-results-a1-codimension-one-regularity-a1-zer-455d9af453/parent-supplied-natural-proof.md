# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.bv_compactness-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.bv_compactness-a1.cauchy_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Supplied proof of the parent node, steps 7–8: a fast Cauchy subsequence, a.e. eventual constancy, F' := liminf, and convergence on balls. The summability/a.e. step is phrased with the Borel–Cantelli lemma. This is the parent's monotone convergence argument in measure form: Σ_l|u_{σ(l+1)} − u_{σ(l)}| = Σ_l 1_{E_l}. No sibling child is used.

1. (Fast subsequence.) For l ∈ ℕ apply the hypothesis with R := l + 1 and η := 2^{−l}: there is N_l with L^m((F_i Δ F_j) ∩ B_{l+1}) ≤ 2^{−l} for all i, j ≥ N_l. Put σ(l) := l + Σ_{k≤l} N_k. Then σ is strictly increasing, and σ(l') ≥ N_l whenever l ≤ l'.
2. (Limit set.) F' := ⋃_{l₀}⋂_{l≥l₀} F_{σ(l)}, the set of points lying in F_{σ(l)} for all large l. It is measurable.
3. (Summability.) Let E_l := (F_{σ(l+1)} Δ F_{σ(l)}) ∩ B_{l+1}. Since σ(l+1), σ(l) ≥ N_l, L^m(E_l) ≤ 2^{−l}. So Σ_l L^m(E_l) ≤ 2 < ∞.
4. (Borel–Cantelli.) Hence for a.e. v, v ∉ E_l for all large l (ae_eventually_notMem; equivalently measure_limsup_atTop_eq_zero). Fix such a v.
   - v ∈ B_{l+1} for all l > |v|. So there is l₁ such that for all l ≥ l₁, v ∉ F_{σ(l+1)} Δ F_{σ(l)}, i.e. v ∈ F_{σ(l+1)} ⇔ v ∈ F_{σ(l)}.
   - By induction, v ∈ F_{σ(l)} ⇔ v ∈ F_{σ(l₁)} for all l ≥ l₁. Therefore v ∈ F' ⇔ v ∈ F_{σ(l₁)}.
   - Consequently v ∉ F_{σ(l)} Δ F' for all l ≥ l₁.
   So for a.e. v, v ∉ F_{σ(l)} Δ F' for all large l.
5. (Convergence on B_R.) Fix R and let G_{l₀} := ⋃_{l≥l₀}(F_{σ(l)} Δ F') ∩ B_R.
   - The G_{l₀} form a decreasing sequence of measurable sets with L^m(G_0) ≤ L^m(B_R) < ∞.
   - ⋂_{l₀}G_{l₀} consists of the v ∈ B_R with v ∈ F_{σ(l)} Δ F' for infinitely many l, so it is null by step 4.
   - Continuity from above (tendsto_measure_iInter_atTop) gives L^m(G_{l₀}) → 0.
   - 0 ≤ L^m((F_{σ(l₀)} Δ F') ∩ B_R) ≤ L^m(G_{l₀}).
   Hence L^m((F_{σ(i)} Δ F') ∩ B_R) → 0 for every R ∈ ℝ. For R ≤ 0 the ball is empty. ∎
Alternatively, as in the parent, use dominated convergence on B_R with |1_{F_{σ(l)}} − 1_{F'}| ≤ 1.

Appendix (Lean proof, kernel-checked). Compiled with the pinned toolchain (Lean v4.35.0-rc3, Mathlib 25730c7c) inside namespace GMT.Ch07 of a file importing GMT.Ch07.Submission, with the contract's opens. It is one declaration with no helper declaration and no set_option. #print axioms gives propext, Classical.choice and Quot.sound.

theorem Submission.codim1_zsl_pc_cauchy_limit_set : ∀ (m : ℕ) (F : ℕ → Set (Euclid m)), (∀ i, MeasurableSet (F i)) → (∀ R : ℝ, 0 < R → ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j → volume (symmDiff (F i) (F j) ∩ ball (0 : Euclid m) R) ≤ ENNReal.ofReal η) → ∃ (σ : ℕ → ℕ) (F' : Set (Euclid m)), StrictMono σ ∧ MeasurableSet F' ∧ ∀ R : ℝ, Tendsto (fun i => volume (symmDiff (F (σ i)) F' ∩ ball (0 : Euclid m) R)) atTop (𝓝 0) := by
  intro m F hF hC
  have hN : ∀ l : ℕ, ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j →
      volume (symmDiff (F i) (F j) ∩ ball (0 : Euclid m) ((l : ℝ) + 1)) ≤
        ENNReal.ofReal ((1 / 2 : ℝ) ^ l) :=
    fun l => hC ((l : ℝ) + 1) (by positivity) ((1 / 2 : ℝ) ^ l) (by positivity)
  choose N hN using hN
  obtain ⟨σ, hσdef⟩ : ∃ σ : ℕ → ℕ, ∀ l, σ l = l + ∑ k ∈ Finset.range (l + 1), N k :=
    ⟨_, fun _ => rfl⟩
  have hσmono : StrictMono σ := by
    apply strictMono_nat_of_lt_succ
    intro l
    simp only [hσdef, Finset.sum_range_succ]
    omega
  have hσge : ∀ l l', l ≤ l' → N l ≤ σ l' := by
    intro l l' h
    have h1 : N l ≤ ∑ k ∈ Finset.range (l' + 1), N k :=
      Finset.single_le_sum (f := N) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
    rw [hσdef]
    omega
  obtain ⟨F', hF'def⟩ : ∃ F' : Set (Euclid m), F' = ⋃ l₀ : ℕ, ⋂ l : ℕ, ⋂ (_ : l₀ ≤ l), F (σ l) :=
    ⟨_, rfl⟩
  have hF'meas : MeasurableSet F' := by
    rw [hF'def]
    exact MeasurableSet.iUnion fun l₀ => MeasurableSet.iInter fun l =>
      MeasurableSet.iInter fun _ => hF _
  have hF'mem : ∀ v, v ∈ F' ↔ ∃ l₀, ∀ l, l₀ ≤ l → v ∈ F (σ l) := by
    intro v
    rw [hF'def]
    simp only [mem_iUnion, mem_iInter]
  obtain ⟨E, hEdef⟩ : ∃ E : ℕ → Set (Euclid m), ∀ l,
      E l = symmDiff (F (σ (l + 1))) (F (σ l)) ∩ ball (0 : Euclid m) ((l : ℝ) + 1) :=
    ⟨_, fun _ => rfl⟩
  have hEle : ∀ l, volume (E l) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ l) := by
    intro l
    rw [hEdef]
    exact hN l _ _ (hσge l (l + 1) (Nat.le_succ l)) (hσge l l le_rfl)
  have hsum : ∑' l, volume (E l) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hEle)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) summable_geometric_two]
    exact ENNReal.ofReal_ne_top
  have hae : ∀ᵐ v ∂(volume : Measure (Euclid m)),
      ∀ᶠ l in atTop, v ∉ symmDiff (F (σ l)) F' := by
    filter_upwards [ae_eventually_notMem hsum] with v hv
    have hball : ∀ᶠ l : ℕ in atTop, v ∈ ball (0 : Euclid m) ((l : ℝ) + 1) := by
      obtain ⟨n, hn⟩ := exists_nat_gt ‖v‖
      filter_upwards [eventually_ge_atTop n] with l hl
      rw [mem_ball_zero_iff]
      have : (n : ℝ) ≤ l := Nat.cast_le.mpr hl
      linarith
    obtain ⟨l₁, hl₁⟩ := eventually_atTop.mp (hv.and hball)
    have hstep : ∀ l, l₁ ≤ l → (v ∈ F (σ (l + 1)) ↔ v ∈ F (σ l)) := by
      intro l hl
      obtain ⟨h1, h2⟩ := hl₁ l hl
      rw [hEdef] at h1
      have h3 : v ∉ symmDiff (F (σ (l + 1))) (F (σ l)) := fun h => h1 (Set.mem_inter h h2)
      rw [Set.mem_symmDiff] at h3
      tauto
    have hconst : ∀ l, l₁ ≤ l → (v ∈ F (σ l) ↔ v ∈ F (σ l₁)) := by
      intro l hl
      induction l, hl using Nat.le_induction with
      | base => exact Iff.rfl
      | succ l hl ih => exact (hstep l hl).trans ih
    have hF'iff : v ∈ F' ↔ v ∈ F (σ l₁) := by
      rw [hF'mem]
      constructor
      · rintro ⟨l₀, hl₀⟩
        exact (hconst (max l₀ l₁) (le_max_right _ _)).mp (hl₀ _ (le_max_left _ _))
      · intro h
        exact ⟨l₁, fun l hl => (hconst l hl).mpr h⟩
    filter_upwards [eventually_ge_atTop l₁] with l hl
    rw [Set.mem_symmDiff]
    have := hconst l hl
    tauto
  refine ⟨σ, F', hσmono, hF'meas, fun R => ?_⟩
  obtain ⟨G, hGdef⟩ : ∃ G : ℕ → Set (Euclid m), ∀ l₀,
      G l₀ = ⋃ l : ℕ, ⋃ (_ : l₀ ≤ l), symmDiff (F (σ l)) F' ∩ ball (0 : Euclid m) R :=
    ⟨_, fun _ => rfl⟩
  have hGmem : ∀ l₀ v, v ∈ G l₀ ↔ ∃ l, l₀ ≤ l ∧ v ∈ symmDiff (F (σ l)) F' ∩ ball (0 : Euclid m) R := by
    intro l₀ v
    rw [hGdef]
    simp only [mem_iUnion, exists_prop]
  have hGmeas : ∀ l₀, NullMeasurableSet (G l₀) volume := by
    intro l₀
    rw [hGdef]
    exact (MeasurableSet.iUnion fun l => MeasurableSet.iUnion fun _ =>
      ((hF _).symmDiff hF'meas).inter measurableSet_ball).nullMeasurableSet
  have hGanti : Antitone G := by
    intro a b hab v hv
    rw [hGmem] at hv ⊢
    obtain ⟨l, hl, hv⟩ := hv
    exact ⟨l, hab.trans hl, hv⟩
  have hGfin : ∃ i, volume (G i) ≠ ∞ := by
    refine ⟨0, ne_top_of_le_ne_top
      (measure_ball_lt_top (μ := volume) (x := (0 : Euclid m)) (r := R)).ne (measure_mono ?_)⟩
    intro v hv
    rw [hGmem] at hv
    obtain ⟨l, _, hv⟩ := hv
    exact hv.2
  have hGnull : volume (⋂ l₀, G l₀) = 0 := by
    refine measure_mono_null ?_ (ae_iff.mp hae)
    intro v hv
    rw [mem_iInter] at hv
    intro hev
    obtain ⟨l₁, hl₁⟩ := eventually_atTop.mp hev
    obtain ⟨l, hl, hvl⟩ := (hGmem l₁ v).mp (hv l₁)
    exact hl₁ l hl hvl.1
  have hGlim := tendsto_measure_iInter_atTop hGmeas hGanti hGfin
  rw [hGnull] at hGlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hGlim (fun _ => zero_le) ?_
  intro l
  exact measure_mono (fun v hv => (hGmem l v).mpr ⟨l, le_rfl, hv⟩)

## Key steps

1. Choose N_l for R = l + 1 and η = 2^{−l}; σ(l) := l + Σ_{k≤l}N_k is strictly increasing with σ(l') ≥ N_l for l ≤ l'.
2. E_l := (F_{σ(l+1)} Δ F_{σ(l)}) ∩ B_{l+1} has measure ≤ 2^{−l}; by Borel–Cantelli, a.e. v lies in only finitely many E_l.
3. For such v, membership in F_{σ(l)} is eventually constant and equals membership in F' := liminf F_{σ(l)}.
4. Continuity from above on the finite-measure ball B_R gives L((F_{σ(l)} Δ F') ∩ B_R) → 0.

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
