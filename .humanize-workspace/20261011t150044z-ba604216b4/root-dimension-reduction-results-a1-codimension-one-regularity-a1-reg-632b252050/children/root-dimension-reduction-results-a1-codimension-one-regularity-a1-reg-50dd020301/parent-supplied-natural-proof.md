# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.blowup_halfspace-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.blowup_halfspace-a1.normal_defect-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 3, i.e. printed (1)–(2) of Simon Ch. 3, 4.3 ('lim ∫ν^{n+1}dμ_E/μ_E(B_ρ) = 1 and hence (since |ν| = 1) lim ∫|ν^i|dμ_E/μ_E(B_ρ) = 0'). Notation: B̄_ρ := B̄_ρ(y), M_ρ := μ(B̄_ρ)_ℝ, A(ρ) := M_ρ^{-1}∫_{B̄_ρ} ν dμ, ε(ρ) := 1 − ⟨A(ρ), v⟩.
1. Finiteness and integrability. For 0 < ρ ≤ ρ₀, B̄_ρ ⊆ B̄_{ρ₀}, so μ(B̄_ρ) ≤ μ(B̄_{ρ₀}) < ∞ and M_ρ equals μ(B̄_ρ) as a real number. ν is Borel and bounded (|ν| = 1), so ν, z ↦ ⟨ν(z), v⟩, z ↦ |⟨ν(z), w⟩|, z ↦ |ν(z) − v| and constants are μ-integrable on B̄_ρ.
2. ε(ρ) → 0. Since A(ρ) → v as ρ ↓ 0 and z ↦ ⟨z, v⟩ is continuous, ε(ρ) → 1 − ⟨v, v⟩ = 1 − |v|² = 0.
3. Defect identity. For 0 < ρ ≤ ρ₀: ∫_{B̄_ρ}(1 − ⟨ν, v⟩) dμ = M_ρ·ε(ρ). If M_ρ = 0, then μ(B̄_ρ) = 0 (it is finite), the restricted measure μ⌞B̄_ρ is zero and both sides vanish. Otherwise ∫_{B̄_ρ} ν dμ = M_ρ·A(ρ) by the definition of A, and since the integral is linear and commutes with the continuous linear functional ⟨·, v⟩, ∫_{B̄_ρ}(1 − ⟨ν, v⟩) dμ = M_ρ − ⟨∫_{B̄_ρ} ν dμ, v⟩ = M_ρ − M_ρ⟨A(ρ), v⟩ = M_ρ·ε(ρ).
4. Pointwise inequalities. For every z: |⟨ν(z), v⟩| ≤ |ν(z)||v| = 1, so 1 − ⟨ν(z), v⟩ ≥ 0; and |ν(z) − v|² = |ν(z)|² − 2⟨ν(z), v⟩ + |v|² = 2(1 − ⟨ν(z), v⟩). If ⟨w, v⟩ = 0 then ⟨ν(z), w⟩ = ⟨ν(z) − v, w⟩, so by Cauchy–Schwarz |⟨ν(z), w⟩| ≤ |w|·|ν(z) − v| and ⟨ν(z), w⟩² ≤ 2|w|²(1 − ⟨ν(z), v⟩) (for unit w this is the parent's ⟨ν, w⟩² ≤ 1 − ⟨ν, v⟩² ≤ 2(1 − ⟨ν, v⟩)).
5. Choice of ρ'. Given δ > 0, by step 2 choose ρ' ∈ (0, ρ₀] with ε(ρ) ≤ min{δ, δ²/2} for all 0 < ρ < ρ'. Fix ρ ∈ (0, ρ'). By steps 3–4, M_ρ·ε(ρ) = ∫_{B̄_ρ}(1 − ⟨ν, v⟩) dμ ≥ 0, so ε(ρ) ≥ 0 whenever M_ρ > 0.
6. Proof of (i). By step 3, ∫_{B̄_ρ}(1 − ⟨ν, v⟩) dμ = M_ρ·ε(ρ) ≤ δ·M_ρ, because M_ρ ≥ 0 and ε(ρ) ≤ δ.
7. Proof of (ii), the parent's Cauchy–Schwarz route. Let ⟨w, v⟩ = 0. If M_ρ = 0 both sides are 0. Otherwise, by the Cauchy–Schwarz inequality for the finite measure μ⌞B̄_ρ, step 4 and step 3: ∫_{B̄_ρ}|⟨ν, w⟩| dμ ≤ M_ρ^{1/2}(∫_{B̄_ρ}⟨ν, w⟩² dμ)^{1/2} ≤ M_ρ^{1/2}(2|w|²·M_ρ ε(ρ))^{1/2} = |w|·M_ρ·(2ε(ρ))^{1/2} ≤ δ|w|M_ρ, since 0 ≤ 2ε(ρ) ≤ δ².
7'. Equivalent elementary route for (ii) (no integral Cauchy–Schwarz; convenient for formalization). For t ≥ 0, t ≤ δ/2 + t²/(2δ) because (t − δ)² ≥ 0. With t = |ν(z) − v| and step 4, |⟨ν(z), w⟩| ≤ |w|·|ν(z) − v| ≤ |w|(δ/2 + (1 − ⟨ν(z), v⟩)/δ) for every z. Integrating over B̄_ρ (all functions integrable by step 1) and using step 3: ∫_{B̄_ρ}|⟨ν, w⟩| dμ ≤ |w|(δM_ρ/2 + M_ρ ε(ρ)/δ) ≤ |w|(δM_ρ/2 + δM_ρ/2) = δ|w|M_ρ, because M_ρ ≥ 0 and ε(ρ) ≤ δ²/2.
8. Steps 6–7 hold for every ρ ∈ (0, ρ') and every w ⊥ v simultaneously; this is the asserted eventual statement as ρ ↓ 0 (ρ ∈ 𝓝[>] 0). ∎
Formalization pointers (verified): ⟨A(ρ), v⟩ → 1 from ((continuous_id.inner continuous_const).tendsto v).comp hA and real_inner_self_eq_norm_sq; with η := min δ (δ²/2), use Tendsto.eventually (lt_mem_nhds _) and Ioo_mem_nhdsGT hρ₀; isFiniteMeasure_restrict; Integrable.of_bound. Measurability of z ↦ ⟨ν(z), v⟩ is (continuous_id.inner continuous_const).measurable.comp hν, and of z ↦ |⟨ν(z), w⟩| goes through continuous_abs; Measurable.inner and Measurable.abs are not in the import closure of the frozen Submission header. The commutation ∫⟨v, ν⟩ = ⟨v, ∫ν⟩ is (innerSL ℝ v).integral_comp_comm hνint followed by simp; integral_inner itself lives in Mathlib/MeasureTheory/Function/L2Space.lean, which that header does not import. Also used: real_inner_comm, real_inner_smul_left; for M_ρ = 0, ENNReal.toReal_eq_zero_iff, Measure.restrict_eq_zero and integral_zero_measure; Measure.real and Measure.restrict_apply_univ, to identify (μ.restrict B̄_ρ).real univ with M_ρ; norm_sub_sq_real, inner_sub_left, abs_real_inner_le_norm, sq_nonneg, nlinarith; integral_mono, integral_const_mul, integral_add, integral_div.

Appendix (an optional aid; the numbered argument above is the proof). The Lean 4 script below proves exactly the frozen statement. It compiled against the pinned toolchain (Lean v4.35.0-rc3, Mathlib 25730c7c, project b4d606db) after `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the contract's `open Filter Function Set MeasureTheory Metric` and `open scoped ENNReal Topology`. Compiled together with the other eight child proofs, `#print axioms` reported only propext, Classical.choice and Quot.sound. The exact compiled source of all nine children, plus the parent assembly, is saved at .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-632b252050/bh-split-v2-lean-prototype.lean.txt.
```lean
theorem Submission.codim1_rdo_dg_bh_normal_defect_small : ∀ (m : ℕ) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)) (y v : Euclid (m + 1)), Measurable ν → (∀ z, ‖ν z‖ = 1) → ‖v‖ = 1 → (∃ ρ₀ : ℝ, 0 < ρ₀ ∧ μ (closedBall y ρ₀) ≠ ∞) → Tendsto (fun ρ : ℝ => (μ (closedBall y ρ)).toReal⁻¹ • ∫ z in closedBall y ρ, ν z ∂μ) (𝓝[>] 0) (𝓝 v) → ∀ δ : ℝ, 0 < δ → ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∫ z in closedBall y ρ, (1 - inner ℝ (ν z) v) ∂μ ≤ δ * (μ (closedBall y ρ)).toReal ∧ ∀ w : Euclid (m + 1), inner ℝ w v = 0 → ∫ z in closedBall y ρ, |inner ℝ (ν z) w| ∂μ ≤ δ * ‖w‖ * (μ (closedBall y ρ)).toReal := by
  intro m μ ν y v hν hν1 hv ⟨ρ₀, hρ₀, hfin⟩ hA δ hδ
  have hε : Tendsto (fun ρ : ℝ => inner ℝ ((μ (closedBall y ρ)).toReal⁻¹ •
      ∫ z in closedBall y ρ, ν z ∂μ) v) (𝓝[>] 0) (𝓝 1) := by
    have hcont : Continuous (fun x : Euclid (m + 1) => inner ℝ x v) :=
      continuous_id.inner continuous_const
    have := (hcont.tendsto v).comp hA
    rwa [real_inner_self_eq_norm_sq, hv, one_pow] at this
  set η := min δ (δ ^ 2 / 2) with hη_def
  have hη : 0 < η := lt_min hδ (by positivity)
  have hηδ : η ≤ δ := min_le_left _ _
  have hηδ2 : η ≤ δ ^ 2 / 2 := min_le_right _ _
  have hev1 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), 1 - η < inner ℝ ((μ (closedBall y ρ)).toReal⁻¹ •
      ∫ z in closedBall y ρ, ν z ∂μ) v :=
    hε.eventually (lt_mem_nhds (by linarith))
  have hev2 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ ∈ Ioo 0 ρ₀ := Ioo_mem_nhdsGT hρ₀
  filter_upwards [hev1, hev2] with ρ h1 h2
  set B := closedBall y ρ with hB
  have hfinρ : μ B ≠ ∞ :=
    ne_top_of_le_ne_top hfin (measure_mono (closedBall_subset_closedBall h2.2.le))
  have : IsFiniteMeasure (μ.restrict B) := isFiniteMeasure_restrict.mpr hfinρ
  set M := (μ B).toReal with hM
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  have hνint : Integrable ν (μ.restrict B) :=
    Integrable.of_bound hν.aestronglyMeasurable 1 (Eventually.of_forall fun z => (hν1 z).le)
  have hνv_meas : Measurable (fun z => inner ℝ (ν z) v) :=
    (continuous_id.inner continuous_const).measurable.comp hν
  have hνv : Integrable (fun z => inner ℝ (ν z) v) (μ.restrict B) := by
    refine Integrable.of_bound hνv_meas.aestronglyMeasurable 1 (Eventually.of_forall fun z => ?_)
    calc ‖inner ℝ (ν z) v‖ = |inner ℝ (ν z) v| := Real.norm_eq_abs _
      _ ≤ ‖ν z‖ * ‖v‖ := abs_real_inner_le_norm _ _
      _ = 1 := by rw [hν1, hv, one_mul]
  have hdefint : Integrable (fun z => 1 - inner ℝ (ν z) v) (μ.restrict B) :=
    (integrable_const 1).sub hνv
  have hdef : ∫ z in B, (1 - inner ℝ (ν z) v) ∂μ ≤ M * η := by
    rcases eq_or_ne M 0 with hM0' | hMne
    · have hμB : μ B = 0 := by
        rcases (ENNReal.toReal_eq_zero_iff _).mp hM0' with h | h
        · exact h
        · exact absurd h hfinρ
      rw [Measure.restrict_eq_zero.mpr hμB, integral_zero_measure, hM0', zero_mul]
    · have hinner : ∫ z in B, inner ℝ (ν z) v ∂μ = inner ℝ (∫ z in B, ν z ∂μ) v := by
        simp_rw [real_inner_comm v]
        have := (innerSL ℝ v).integral_comp_comm hνint
        simpa using this
      rw [integral_sub (integrable_const 1) hνv, hinner, integral_const, smul_eq_mul, mul_one]
      simp only [Measure.real, Measure.restrict_apply_univ]
      have hA' : inner ℝ (∫ z in B, ν z ∂μ) v = M * inner ℝ (M⁻¹ • ∫ z in B, ν z ∂μ) v := by
        rw [real_inner_smul_left, ← mul_assoc, mul_inv_cancel₀ hMne, one_mul]
      rw [hA']
      have : 1 - inner ℝ (M⁻¹ • ∫ z in B, ν z ∂μ) v ≤ η := by linarith
      nlinarith
  refine ⟨?_, ?_⟩
  · calc ∫ z in B, (1 - inner ℝ (ν z) v) ∂μ ≤ M * η := hdef
      _ ≤ M * δ := mul_le_mul_of_nonneg_left hηδ hM0
      _ = δ * M := mul_comm _ _
  · intro w hw
    have hpt : ∀ z, |inner ℝ (ν z) w| ≤ ‖w‖ * (δ / 2 + (1 - inner ℝ (ν z) v) / δ) := by
      intro z
      have e1 : inner ℝ (ν z) w = inner ℝ (ν z - v) w := by
        rw [inner_sub_left, real_inner_comm w v, hw, sub_zero]
      have e2 : ‖ν z - v‖ ^ 2 = 2 - 2 * inner ℝ (ν z) v := by
        rw [norm_sub_sq_real, hν1, hv]; ring
      have e3 : ‖ν z - v‖ ≤ δ / 2 + (1 - inner ℝ (ν z) v) / δ := by
        have ht := sq_nonneg (‖ν z - v‖ - δ)
        have : (1 - inner ℝ (ν z) v) / δ = ‖ν z - v‖ ^ 2 / (2 * δ) := by
          rw [e2]; field_simp
        rw [this, div_add_div _ _ (two_ne_zero) (by positivity), le_div_iff₀ (by positivity)]
        nlinarith
      rw [e1]
      calc |inner ℝ (ν z - v) w| ≤ ‖ν z - v‖ * ‖w‖ := abs_real_inner_le_norm _ _
        _ ≤ (δ / 2 + (1 - inner ℝ (ν z) v) / δ) * ‖w‖ :=
            mul_le_mul_of_nonneg_right e3 (norm_nonneg _)
        _ = _ := mul_comm _ _
    have hint1 : Integrable (fun z => |inner ℝ (ν z) w|) (μ.restrict B) := by
      refine Integrable.of_bound
        ((continuous_abs.comp (continuous_id.inner continuous_const)).measurable.comp
          hν).aestronglyMeasurable ‖w‖
        (Eventually.of_forall fun z => ?_)
      rw [Real.norm_eq_abs, abs_abs]
      calc |inner ℝ (ν z) w| ≤ ‖ν z‖ * ‖w‖ := abs_real_inner_le_norm _ _
        _ = ‖w‖ := by rw [hν1, one_mul]
    have hint2 : Integrable (fun z => ‖w‖ * (δ / 2 + (1 - inner ℝ (ν z) v) / δ)) (μ.restrict B) :=
      ((integrable_const (δ / 2)).add (hdefint.div_const δ)).const_mul ‖w‖
    calc ∫ z in B, |inner ℝ (ν z) w| ∂μ
        ≤ ∫ z in B, ‖w‖ * (δ / 2 + (1 - inner ℝ (ν z) v) / δ) ∂μ :=
          integral_mono hint1 hint2 hpt
      _ = ‖w‖ * (δ / 2 * M + (∫ z in B, (1 - inner ℝ (ν z) v) ∂μ) / δ) := by
          rw [integral_const_mul, integral_add (integrable_const _) (hdefint.div_const δ),
            integral_const, integral_div, smul_eq_mul]
          simp only [Measure.real, Measure.restrict_apply_univ]
          ring
      _ ≤ ‖w‖ * (δ / 2 * M + M * η / δ) := by
          gcongr
      _ ≤ ‖w‖ * (δ / 2 * M + M * (δ ^ 2 / 2) / δ) := by
          gcongr
      _ = δ * ‖w‖ * M := by
          field_simp
          ring
```

## Key steps

1. μ(B̄_ρ(y)) < ∞ for ρ ≤ ρ₀; all integrands are bounded measurable, hence integrable.
2. ε(ρ) := 1 − ⟨A(ρ), v⟩ → 0.
3. ∫_{B̄_ρ}(1 − ⟨ν, v⟩)dμ = μ(B̄_ρ)_ℝ ε(ρ) (integral commutes with ⟨·, v⟩; trivial when μ(B̄_ρ) = 0).
4. Pointwise: 1 − ⟨ν, v⟩ ≥ 0, |ν − v|² = 2(1 − ⟨ν, v⟩), |⟨ν, w⟩| ≤ |w||ν − v| for w ⊥ v.
5. Take ε(ρ) ≤ min{δ, δ²/2}: (i) directly; (ii) by Cauchy–Schwarz or the pointwise AM–GM bound.

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
