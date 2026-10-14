# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.blowup_halfspace-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.blowup_halfspace-a1.l1loc_transfer-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 4 ('hence ∫_{F_{r_{k_j}}} f → ∫_{F₀} f for every bounded Borel f vanishing outside some B_R') and the limit passages of steps 5–6. Notation: L := L^{m+1}, B_s := B_s(0), e_k(R) := L((F_k Δ F₀) ∩ B_R) → 0 for every R.
1. (a) Setup. Let f be continuous with compact support. Then M := sup|f| < ∞, there is R with tsupport f ⊆ B_R (a compact set is bounded), and f is L-integrable; so all integrals below are finite and ∫_{F_k} f − ∫_{F₀} f = ∫ (1_{F_k} − 1_{F₀})·f dL.
2. (a) Estimate. |1_{F_k} − 1_{F₀}| = 1_{F_k Δ F₀} and f = 0 outside B_R, so |(1_{F_k} − 1_{F₀})f| ≤ M·1_{(F_k Δ F₀) ∩ B_R}. Hence |∫_{F_k} f − ∫_{F₀} f| ≤ M·L((F_k Δ F₀) ∩ B_R) = M·e_k(R) → 0 (e_k(R) ≤ L(B_R) < ∞). This proves (a).
3. (b) Fix s ∈ ℝ; put a_k := L(F_k ∩ B_s) and a := L(F₀ ∩ B_s) ≤ L(B_s) < ∞. Since F_k ∩ B_s ⊆ (F₀ ∩ B_s) ∪ ((F_k Δ F₀) ∩ B_s) and F₀ ∩ B_s ⊆ (F_k ∩ B_s) ∪ ((F_k Δ F₀) ∩ B_s), subadditivity gives a_k ≤ a + e_k(s) and a ≤ a_k + e_k(s). All quantities are finite, so |a_k − a| ≤ e_k(s) → 0, i.e. a_k → a. (If s ≤ 0 the ball is empty and everything is 0.)
4. (c) Fix s ∈ ℝ; put b_k := L(B_s ∖ F_k) and b := L(B_s ∖ F₀) < ∞. Since (B_s ∖ F_k) Δ (B_s ∖ F₀) = (F_k Δ F₀) ∩ B_s, we have B_s ∖ F_k ⊆ (B_s ∖ F₀) ∪ ((F_k Δ F₀) ∩ B_s) and B_s ∖ F₀ ⊆ (B_s ∖ F_k) ∪ ((F_k Δ F₀) ∩ B_s); as in step 3, b_k ≤ b + e_k(s) and b ≤ b_k + e_k(s), so b_k → b. ∎
Formalization pointers (verified): (b) and (c) use ENNReal.tendsto_nhds (needs a ≠ ∞), tsub_le_iff_right, measure_mono, measure_union_le, measure_ball_lt_top and Set.mem_symmDiff. (a) uses hfc.isCompact.isBounded.subset_ball 0, Continuous.bounded_above_of_compact_support, Continuous.integrable_of_hasCompactSupport, integral_indicator, integral_sub and Integrable.indicator. The bound is norm_integral_le_of_norm_le with (E_k).indicator (fun _ => M), which is integrable by (integrableOn_const _).integrable_indicator. Then integral_indicator_const, image_eq_zero_of_notMem_tsupport, ENNReal.tendsto_toReal, squeeze_zero_norm and tendsto_sub_nhds_zero_iff. Write the difference with explicit parentheses, ‖(∫ z in F_k, f z) − ∫ z in F₀, f z‖; otherwise the binder of the first integral swallows the subtraction.

Appendix (an optional aid; the numbered argument above is the proof). The Lean 4 script below proves exactly the frozen statement. It compiled against the pinned toolchain (Lean v4.35.0-rc3, Mathlib 25730c7c, project b4d606db) after `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the contract's `open Filter Function Set MeasureTheory Metric` and `open scoped ENNReal Topology`. Compiled together with the other eight child proofs, `#print axioms` reported only propext, Classical.choice and Quot.sound. The exact compiled source of all nine children, plus the parent assembly, is saved at .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-632b252050/bh-split-v2-lean-prototype.lean.txt.
```lean
theorem Submission.codim1_rdo_dg_bh_l1loc_transfer : ∀ (m : ℕ) (Fs : ℕ → Set (Euclid (m + 1))) (F₀ : Set (Euclid (m + 1))), (∀ k, MeasurableSet (Fs k)) → MeasurableSet F₀ → (∀ R : ℝ, Tendsto (fun k => volume (symmDiff (Fs k) F₀ ∩ ball (0 : Euclid (m + 1)) R)) atTop (𝓝 0)) → (∀ f : Euclid (m + 1) → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ z in Fs k, f z) atTop (𝓝 (∫ z in F₀, f z))) ∧ (∀ s : ℝ, Tendsto (fun k => volume (Fs k ∩ ball (0 : Euclid (m + 1)) s)) atTop (𝓝 (volume (F₀ ∩ ball (0 : Euclid (m + 1)) s)))) ∧ ∀ s : ℝ, Tendsto (fun k => volume (ball (0 : Euclid (m + 1)) s \ Fs k)) atTop (𝓝 (volume (ball (0 : Euclid (m + 1)) s \ F₀))) := by
  intro m Fs F₀ hFs hF₀ hconv
  have key : ∀ (a : ℕ → ℝ≥0∞) (b : ℝ≥0∞) (e : ℕ → ℝ≥0∞), b ≠ ∞ → Tendsto e atTop (𝓝 0) →
      (∀ k, a k ≤ b + e k) → (∀ k, b ≤ a k + e k) → Tendsto a atTop (𝓝 b) := by
    intro a b e hb he h1 h2
    rw [ENNReal.tendsto_nhds hb]
    intro ε hε
    filter_upwards [he.eventually (gt_mem_nhds hε)] with k hk
    constructor
    · rw [tsub_le_iff_right]
      exact (h2 k).trans (by gcongr)
    · exact (h1 k).trans (by gcongr)
  refine ⟨?_, ?_, ?_⟩
  · intro f hf hfc
    obtain ⟨R, hR⟩ : ∃ R, tsupport f ⊆ ball (0 : Euclid (m + 1)) R := by
      obtain ⟨R, hR⟩ := hfc.isCompact.isBounded.subset_ball 0
      exact ⟨R, hR⟩
    obtain ⟨M, hM⟩ : ∃ M, ∀ z, ‖f z‖ ≤ M := hf.bounded_above_of_compact_support hfc
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
    have hfi : Integrable f := hf.integrable_of_hasCompactSupport hfc
    set E : ℕ → Set (Euclid (m + 1)) := fun k => symmDiff (Fs k) F₀ ∩ ball (0 : Euclid (m + 1)) R
    have hEm : ∀ k, MeasurableSet (E k) := fun k =>
      ((hFs k).symmDiff hF₀).inter measurableSet_ball
    have hEfin : ∀ k, volume (E k) ≠ ∞ := fun k =>
      ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono Set.inter_subset_right)
    have hbound : ∀ k, ‖(∫ z in Fs k, f z) - ∫ z in F₀, f z‖ ≤ M * (volume (E k)).toReal := by
      intro k
      rw [← integral_indicator (hFs k), ← integral_indicator hF₀,
        ← integral_sub (hfi.indicator (hFs k)) (hfi.indicator hF₀)]
      have hgi : Integrable ((E k).indicator (fun _ => M)) :=
        (integrableOn_const (hEfin k)).integrable_indicator (hEm k)
      have hM' : ∀ z, |f z| ≤ M := fun z => by simpa [Real.norm_eq_abs] using hM z
      calc ‖∫ z, ((Fs k).indicator f z - F₀.indicator f z)‖
          ≤ ∫ z, (E k).indicator (fun _ => M) z := by
            apply norm_integral_le_of_norm_le hgi
            refine Eventually.of_forall fun z => ?_
            by_cases hzR : z ∈ ball (0 : Euclid (m + 1)) R
            · by_cases h1 : z ∈ Fs k <;> by_cases h2 : z ∈ F₀
              · simp [h1, h2, Set.indicator_of_mem, hM0]
                by_cases hz : z ∈ E k <;> simp [hz, hM0]
              · have hz : z ∈ E k := ⟨Set.mem_symmDiff.mpr (Or.inl ⟨h1, h2⟩), hzR⟩
                simp [h1, h2, hz, hM' z]
              · have hz : z ∈ E k := ⟨Set.mem_symmDiff.mpr (Or.inr ⟨h2, h1⟩), hzR⟩
                simp [h1, h2, hz, hM' z]
              · simp [h1, h2]
                by_cases hz : z ∈ E k <;> simp [hz, hM0]
            · have hfz : f z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hzR (hR h))
              have hz : z ∉ E k := fun h => hzR h.2
              have e1 : (Fs k).indicator f z = 0 := by
                by_cases h1 : z ∈ Fs k
                · rw [Set.indicator_of_mem h1, hfz]
                · rw [Set.indicator_of_notMem h1]
              have e2 : F₀.indicator f z = 0 := by
                by_cases h2 : z ∈ F₀
                · rw [Set.indicator_of_mem h2, hfz]
                · rw [Set.indicator_of_notMem h2]
              rw [e1, e2, Set.indicator_of_notMem hz]
              simp
        _ = M * (volume (E k)).toReal := by
            rw [integral_indicator_const _ (hEm k), smul_eq_mul, mul_comm]
            rfl
    have hlim : Tendsto (fun k => M * (volume (E k)).toReal) atTop (𝓝 0) := by
      have := (ENNReal.tendsto_toReal (ENNReal.zero_ne_top)).comp (hconv R)
      simpa using this.const_mul M
    rw [← tendsto_sub_nhds_zero_iff]
    exact squeeze_zero_norm hbound hlim
  · intro s
    have hb : volume (F₀ ∩ ball (0 : Euclid (m + 1)) s) ≠ ∞ :=
      ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono Set.inter_subset_right)
    refine key _ _ _ hb (hconv s) (fun k => ?_) (fun k => ?_)
    · calc volume (Fs k ∩ ball (0 : Euclid (m + 1)) s)
          ≤ volume ((F₀ ∩ ball (0 : Euclid (m + 1)) s) ∪ (symmDiff (Fs k) F₀ ∩ ball (0 : Euclid (m + 1)) s)) := by
            apply measure_mono
            intro z hz
            by_cases h : z ∈ F₀
            · exact Or.inl ⟨h, hz.2⟩
            · exact Or.inr ⟨Set.mem_symmDiff.mpr (Or.inl ⟨hz.1, h⟩), hz.2⟩
        _ ≤ _ := measure_union_le _ _
    · calc volume (F₀ ∩ ball (0 : Euclid (m + 1)) s)
          ≤ volume ((Fs k ∩ ball (0 : Euclid (m + 1)) s) ∪ (symmDiff (Fs k) F₀ ∩ ball (0 : Euclid (m + 1)) s)) := by
            apply measure_mono
            intro z hz
            by_cases h : z ∈ Fs k
            · exact Or.inl ⟨h, hz.2⟩
            · exact Or.inr ⟨Set.mem_symmDiff.mpr (Or.inr ⟨hz.1, h⟩), hz.2⟩
        _ ≤ _ := measure_union_le _ _
  · intro s
    have hb : volume (ball (0 : Euclid (m + 1)) s \ F₀) ≠ ∞ :=
      ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono Set.sdiff_subset)
    refine key _ _ _ hb (hconv s) (fun k => ?_) (fun k => ?_)
    · calc volume (ball (0 : Euclid (m + 1)) s \ Fs k)
          ≤ volume ((ball (0 : Euclid (m + 1)) s \ F₀) ∪ (symmDiff (Fs k) F₀ ∩ ball (0 : Euclid (m + 1)) s)) := by
            apply measure_mono
            intro z hz
            by_cases h : z ∈ F₀
            · exact Or.inr ⟨Set.mem_symmDiff.mpr (Or.inr ⟨h, hz.2⟩), hz.1⟩
            · exact Or.inl ⟨hz.1, h⟩
        _ ≤ _ := measure_union_le _ _
    · calc volume (ball (0 : Euclid (m + 1)) s \ F₀)
          ≤ volume ((ball (0 : Euclid (m + 1)) s \ Fs k) ∪ (symmDiff (Fs k) F₀ ∩ ball (0 : Euclid (m + 1)) s)) := by
            apply measure_mono
            intro z hz
            by_cases h : z ∈ Fs k
            · exact Or.inr ⟨Set.mem_symmDiff.mpr (Or.inl ⟨h, hz.2⟩), hz.1⟩
            · exact Or.inl ⟨hz.1, h⟩
        _ ≤ _ := measure_union_le _ _
```

## Key steps

1. For continuous compactly supported f with |f| ≤ M and tsupport f ⊆ B_R: |∫_{F_k} f − ∫_{F₀} f| ≤ M·L((F_k Δ F₀) ∩ B_R) → 0.
2. Local volumes: |L(F_k ∩ B_s) − L(F₀ ∩ B_s)| ≤ L((F_k Δ F₀) ∩ B_s) → 0.
3. Same for B_s ∖ F_k, using (B_s ∖ F_k) Δ (B_s ∖ F₀) = (F_k Δ F₀) ∩ B_s.

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD`
- `sha256sum <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `python3 over dag.json: selected node record (status, message, attempts, children); frozen lean_statement of cutoff_estimates-a1, volume_density_lower-a1, bv_compactness-a1 and halfspace_rigidity-a1; name-collision and identical-type scan of the nine codim1_rdo_dg_bh_* children (1010 nodes, re-run at 1119 nodes)`
- `grep -l '"child_id": "...blowup_halfspace-a1.' nodes/*/parent-child-handoff.json; grep -rl codim1_rdo_dg_bh_ nodes/ .humanize/publication-intents .humanize/issue-claims (no match outside decomposition-v1.json)`
- `sed -n runtime.py: _solve loop (960-1060), _decompose (1388-1560), _parent_supplied_child_checkpoint (1741-1799), _solve_children (1801-1990), _existing_lean_name_problem (6532-6575); cat swarm-project.json; cat run.json`
- `rg -n 'blowUp|blowup|symmDiff|GaussGreen|gaussGreen|reducedBoundary|rescal|L1loc|halfspace' <snapshot>/project/GMT/Ch07; rg -n 'DeGiorgi|reducedBoundary|symmDiff|blow' <snapshot>/project/GMT/Ch03/Contract.lean; rg -ln 'blowUp|blowUpMap|reducedBoundary|GaussGreen|gaussGreen|symmDiff' simongmt/Poincare; rg -n '^theorem|^lemma|^def|^structure' simongmt/Poincare/SimonGMT/Chapter03/FinitePerimeter.lean`
- `rg -n in <snapshot>/mathlib: tendsto_of_subseq_tendsto | integral_comp_smul | addHaar_preimage_smul | trace_smulRight | fderiv_smul_const | symmDiff_triangle | norm_setIntegral_le_of_norm_le_const | setIntegral_eq_integral_of_forall_compl_eq_zero | norm_integral_le_of_norm_le | integral_mul_left_eq_self | mulTSupport_comp_subset_preimage | HasCompactMulSupport.comp_homeomorph | HasCompactSupport.fderiv_apply | ContDiff.continuous_fderiv | ENNReal.tendsto_nhds | Integrable.of_bound | integral_inner | integral_indicator_const | isFiniteMeasure_restrict | measure_preimage_mul | toReal_le_of_le_ofReal | integrableOn_const`
- `sed -n 560,760p book/chapter-03.txt (Simon Ch. 3, 4.3 printed proof)`
- `git show <last 200 commits>:GMT/Ch07/Submission.lean | grep ^import (import practice of candidate submissions); sed -n 1,28p verifier/gmt-compare.py`
- `lake env lean -DautoImplicit=false /tmp/bh-split-v2/{Types,Assembly,Checks,Rescaled,NormalDefect,L1loc,FirstVariation,Full,SavedCopy}.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/CountablyGenerated.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/SymmDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Group/Integral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Group/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L2Space.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/run.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-632b252050/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-632b252050/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-632b252050/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-632b252050/bh-split-v2-lean-prototype.lean.txt`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/swarm-project.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/FinitePerimeter.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/bh-split-v2/Types.lean`
- `/tmp/bh-split-v2/Assembly.lean`
- `/tmp/bh-split-v2/Checks.lean`
- `/tmp/bh-split-v2/Rescaled.lean`
- `/tmp/bh-split-v2/NormalDefect.lean`
- `/tmp/bh-split-v2/L1loc.lean`
- `/tmp/bh-split-v2/FirstVariation.lean`
- `/tmp/bh-split-v2/Full.lean`

Pins: the snapshot manifest (project b4d606db, Mathlib 25730c7c) equals workspace HEAD and .lake/packages/mathlib. Snapshot Contract.lean, workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).

Reuse: nothing in the snapshot is reusable. The project's only blow-up is the current-level GMT.Ch07.blowUp (Contract.lean:184). The snapshot's GMT/Ch03 has a DeGiorgiTheorem Prop (Contract.lean:325), but its main_theorem is `by sorry` (:339). SimonGMT Chapter03/FinitePerimeter.lean supplies only the reducedBoundary data. No local declaration states the rescaled Gauss–Green identity, the normal-defect estimate, the blow-up perimeter bound, the L¹_loc transfer or the offset lemma, so all become children.

API: snapshot Mathlib supplies everything the child proofs use: CountablyGenerated.lean:125, Haar/NormedSpace.lean:92, Lebesgue/EqHaar.lean:352, LinearAlgebra/Trace.lean:272, FDeriv/Mul.lean:153, FDeriv/Const.lean:393, ContDiff/Defs.lean:1271, Order/SymmDiff.lean:210, Bochner/Set.lean:486/528/613, Bochner/Basic.lean:985, Group/Integral.lean:91, Group/Measure.lean:236, Topology/Algebra/Support.lean:99/562, ENNReal/Lemmas.lean:233, IntegrableOn.lean:119/171, Typeclasses/Finite.lean:40, Basic/ENNReal/Real.lean:283. One exception: integral_inner (Function/L2Space.lean:89) is outside the frozen header's import closure, so normal_defect's pointer uses innerSL ℝ v with integral_comp_comm. Recent candidate commits do add Mathlib imports, so importing it is also an option.

Lean checks (from the workspace root):
- All 13 types elaborate.
- The parent's frozen type is proved from the 9 children and the 4 sibling contracts.
- All 9 children are proved with only propext, Classical.choice, Quot.sound.
- The saved prototype recompiles identically.

DAG and runtime: v1 (identical contract) was accepted at 11:14Z, but its children were never activated before the 11:42Z restart. The node has no children, and there are no leftover handoffs or publication intents. The nine names are unused across the 1119 nodes, and no identical type exists. Config: max_depth 6, max_children 12.
