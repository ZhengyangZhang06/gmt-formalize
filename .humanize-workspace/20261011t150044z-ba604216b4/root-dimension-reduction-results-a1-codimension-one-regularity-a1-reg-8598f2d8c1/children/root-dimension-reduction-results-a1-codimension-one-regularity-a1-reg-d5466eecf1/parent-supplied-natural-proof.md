# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.tangent_measure_ae-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.tangent_measure_ae-a1.normal_defect-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Extracted from step 4 of the supplied parent proof: the splitting f = f⟨ν, v⟩ + f(1 − ⟨ν, v⟩), with 1 − ⟨ν, v⟩ ≥ 0 and ∫_{B̄_ρ(y)} (1 − ⟨ν, v⟩) dμ = μ(B̄_ρ(y)) ε(ρ), so that the defect term is at most ‖f‖_∞ C₁ R^m ε(rR) → 0; this is the printed appeal 'by 4.1, (1) and (2)' in Simon Ch. 3, 4.3 (†). Notation: B_ρ := B̄_ρ(y), μ(·)_ℝ := ENNReal.toReal ∘ μ, A(ρ) := μ(B_ρ)_ℝ^{-1} ∫_{B_ρ} ν dμ.

1. Choose R ≥ 1 with tsupport f ⊆ B̄_R(0) (compact support), and M ≥ 0 with |f| ≤ M (f is continuous with compact support). For r > 0, if f(r^{-1}(z − y)) ≠ 0 then |r^{-1}(z − y)| ≤ R, i.e. z ∈ B_{rR}.
2. Since |v| = |ν(z)| = 1, Cauchy–Schwarz gives |⟨v, ν(z)⟩| ≤ 1; in particular 0 ≤ 1 − ⟨v, ν(z)⟩ ≤ 2.
3. Integrability. Fix r with 0 < r and rR < ρ₁. Then μ(B_{rR}) ≤ C (rR)^n < ∞. The functions I₁(z) := f(r^{-1}(z − y)) and I₂(z) := f(r^{-1}(z − y)) ⟨v, ν(z)⟩ are measurable (f continuous, ν Borel), bounded by M (step 2) and vanish outside B_{rR} (step 1), hence μ-integrable; ν is μ-integrable on B_{rR} (Borel, bounded by 1, finite measure), and so is z ↦ ⟨v, ν(z)⟩.
4. Splitting. Δ(r) := r^{-n} ∫ I₁ dμ − r^{-n} ∫ I₂ dμ = r^{-n} ∫ f(r^{-1}(z − y)) (1 − ⟨v, ν(z)⟩) dμ(z). By steps 1–2, |f(r^{-1}(z − y)) (1 − ⟨v, ν(z)⟩)| ≤ M (1 − ⟨v, ν(z)⟩) 1_{B_{rR}}(z), so |Δ(r)| ≤ r^{-n} M ∫_{B_{rR}} (1 − ⟨v, ν⟩) dμ.
5. Defect identity. For ρ := rR: ∫_{B_ρ} (1 − ⟨v, ν⟩) dμ = μ(B_ρ)_ℝ − ⟨v, ∫_{B_ρ} ν dμ⟩ (the integral commutes with the continuous linear functional ⟨v, ·⟩) = μ(B_ρ)_ℝ (1 − ⟨v, A(ρ)⟩). Indeed, if μ(B_ρ)_ℝ ≠ 0 this is the definition of A(ρ); if μ(B_ρ)_ℝ = 0 then μ(B_ρ) = 0 (it is finite), so ∫_{B_ρ} ν dμ = 0 and both sides vanish.
6. Bound. Using μ(B_{rR})_ℝ ≤ C (rR)^n, steps 4–5 give |Δ(r)| ≤ M r^{-n} μ(B_{rR})_ℝ |1 − ⟨v, A(rR)⟩| ≤ M r^{-n} C (rR)^n |1 − ⟨v, A(rR)⟩| = M C R^n |1 − ⟨v, A(rR)⟩| for all r ∈ (0, ρ₁/R).
7. Limit. As r ↓ 0 we have rR ↓ 0 (R > 0), so A(rR) → v, hence ⟨v, A(rR)⟩ → ⟨v, v⟩ = 1 and the bound in step 6 tends to 0. By squeezing, Δ(r) → 0 as r ↓ 0.
8. Therefore r^{-n} ∫ f(r^{-1}(z − y)) dμ = r^{-n} ∫ f(r^{-1}(z − y)) ⟨v, ν(z)⟩ dμ + Δ(r) → L + 0 = L. ∎

Appendix (formal check; the numbered proof above is the argument). The Lean proof below of exactly this frozen statement was compiled in the pinned project (Lean v4.35.0-rc3, Mathlib 25730c7c) after `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the contract's opens (`open Filter Function Set MeasureTheory Metric`, `open scoped ENNReal Topology`, `open Poincare.SimonGMT.Chapter06`), as part of one file containing all ten children; it uses no other child, and `#print axioms` reports propext, Classical.choice, Quot.sound.

theorem Submission.codim1_rdo_dg_tma_normal_defect : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (ν : Euclid P → Euclid P) (y v : Euclid P) (ρ₁ C L : ℝ) (f : Euclid P → ℝ), Measurable ν → (∀ z, ‖ν z‖ = 1) → ‖v‖ = 1 → 0 < ρ₁ → 0 ≤ C → (∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → μ (closedBall y ρ) ≤ ENNReal.ofReal (C * ρ ^ n)) → Tendsto (fun ρ : ℝ => (μ (closedBall y ρ)).toReal⁻¹ • ∫ z in closedBall y ρ, ν z ∂μ) (𝓝[>] 0) (𝓝 v) → Continuous f → HasCompactSupport f → Tendsto (fun r : ℝ => (r ^ n)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) * inner ℝ v (ν z) ∂μ) (𝓝[>] 0) (𝓝 L) → Tendsto (fun r : ℝ => (r ^ n)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ) (𝓝[>] 0) (𝓝 L) := by
  intro P n μ ν y v ρ₁ C L f hνm hν1 hv hρ₁ hC hdens hA hf hfc hL
  obtain ⟨R₀, hR₀⟩ := hfc.isCompact.isBounded.subset_closedBall (0 : Euclid P)
  set R := max R₀ 1 with hRdef
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hR : tsupport f ⊆ closedBall 0 R :=
    hR₀.trans (closedBall_subset_closedBall (le_max_left _ _))
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hfc
  have hM' : ∀ w, |f w| ≤ M := fun w => by simpa [Real.norm_eq_abs] using hM w
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM' 0)
  set A : ℝ → Euclid P := fun ρ =>
    (μ (closedBall y ρ)).toReal⁻¹ • ∫ z in closedBall y ρ, ν z ∂μ with hAdef
  have hinner_le : ∀ z, inner ℝ v (ν z) ≤ 1 := by
    intro z
    have := real_inner_le_norm v (ν z)
    rwa [hv, hν1, one_mul] at this
  have hinner_abs : ∀ z, |inner ℝ v (ν z)| ≤ 1 := by
    intro z
    have := abs_real_inner_le_norm v (ν z)
    rwa [hv, hν1, one_mul] at this
  have hνinner_meas : Measurable (fun z => inner ℝ v (ν z)) :=
    (continuous_const.inner continuous_id).measurable.comp hνm
  -- the pointwise estimate on small balls
  have hbound : ∀ r : ℝ, 0 < r → r * R < ρ₁ →
      |(r ^ n)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ -
        (r ^ n)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) * inner ℝ v (ν z) ∂μ| ≤
        M * (C * R ^ n) * |1 - inner ℝ v (A (r * R))| := by
    intro r hr hrR
    set B := closedBall y (r * R) with hBdef
    have hBμ : μ B ≤ ENNReal.ofReal (C * (r * R) ^ n) := hdens _ (by positivity) hrR
    have hBfin : μ B ≠ ∞ := (hBμ.trans_lt ENNReal.ofReal_lt_top).ne
    have hsupp : ∀ z, z ∉ B → f (r⁻¹ • (z - y)) = 0 := by
      intro z hz
      by_contra hne
      have h1 := hR (subset_tsupport f hne)
      apply hz
      rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.le)]
        at h1
      rw [hBdef, mem_closedBall, dist_eq_norm]
      calc ‖z - y‖ = r * (r⁻¹ * ‖z - y‖) := by field_simp
        _ ≤ r * R := mul_le_mul_of_nonneg_left h1 hr.le
    have hcont : Continuous (fun z => f (r⁻¹ • (z - y))) := by fun_prop
    have hint1 : Integrable (fun z => f (r⁻¹ • (z - y))) μ := by
      refine IntegrableOn.integrable_of_forall_notMem_eq_zero ?_ hsupp
      exact Measure.integrableOn_of_bounded hBfin hcont.aestronglyMeasurable (M := M)
        (Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hM' _)
    have hint2 : Integrable (fun z => f (r⁻¹ • (z - y)) * inner ℝ v (ν z)) μ := by
      refine IntegrableOn.integrable_of_forall_notMem_eq_zero ?_
        (fun z hz => by rw [hsupp z hz, zero_mul])
      refine Measure.integrableOn_of_bounded hBfin
        (hcont.aestronglyMeasurable.mul hνinner_meas.aestronglyMeasurable) (M := M)
        (Eventually.of_forall fun z => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      calc |f (r⁻¹ • (z - y))| * |inner ℝ v (ν z)| ≤ M * 1 :=
            mul_le_mul (hM' _) (hinner_abs z) (abs_nonneg _) hM0
        _ = M := mul_one M
    have hνint : IntegrableOn ν B μ :=
      Measure.integrableOn_of_bounded hBfin hνm.aestronglyMeasurable (M := 1)
        (Eventually.of_forall fun z => (hν1 z).le)
    -- ∫_B (1 - ⟪v, ν⟫) = μ(B) (1 - ⟪v, A(rR)⟫)
    have hkey : ∫ z in B, (1 - inner ℝ v (ν z)) ∂μ =
        (μ B).toReal * (1 - inner ℝ v (A (r * R))) := by
      have hint3 : IntegrableOn (fun z => inner ℝ v (ν z)) B μ :=
        Measure.integrableOn_of_bounded hBfin hνinner_meas.aestronglyMeasurable (M := 1)
          (Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hinner_abs z)
      rw [integral_sub (integrableOn_const (C := (1 : ℝ)) hBfin) hint3, setIntegral_const,
        smul_eq_mul, mul_one]
      have hcomm : ∫ z in B, inner ℝ v (ν z) ∂μ = inner ℝ v (∫ z in B, ν z ∂μ) := by
        have := ContinuousLinearMap.integral_comp_comm (innerSL ℝ v) hνint
        simpa using this
      rw [hcomm, Measure.real]
      by_cases h0 : (μ B).toReal = 0
      · have hμ0 : μ B = 0 := by
          rcases (ENNReal.toReal_eq_zero_iff _).1 h0 with h | h
          · exact h
          · exact absurd h hBfin
        have : ∫ z in B, ν z ∂μ = 0 := by
          rw [Measure.restrict_eq_zero.2 hμ0, integral_zero_measure]
        rw [this, h0]
        simp
      · simp only [hAdef]
        rw [← hBdef, real_inner_smul_right]
        field_simp
    have hdiff : (r ^ n)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ -
        (r ^ n)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) * inner ℝ v (ν z) ∂μ =
        (r ^ n)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) * (1 - inner ℝ v (ν z)) ∂μ := by
      rw [← mul_sub, ← integral_sub hint1 hint2]
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only
      ring
    have hle : |∫ z, f (r⁻¹ • (z - y)) * (1 - inner ℝ v (ν z)) ∂μ| ≤
        M * ∫ z in B, (1 - inner ℝ v (ν z)) ∂μ := by
      have hbint : Integrable (fun z => B.indicator (fun z => M * (1 - inner ℝ v (ν z))) z) μ := by
        refine (integrable_indicator_iff measurableSet_closedBall).2 ?_
        refine Measure.integrableOn_of_bounded hBfin
          (aestronglyMeasurable_const.mul
            (aestronglyMeasurable_const.sub hνinner_meas.aestronglyMeasurable)) (M := M * 2)
          (Eventually.of_forall fun z => ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hM0]
        refine mul_le_mul_of_nonneg_left ?_ hM0
        have := hinner_abs z
        rw [abs_le] at this ⊢
        constructor <;> linarith [this.1, this.2]
      rw [← Real.norm_eq_abs]
      refine (norm_integral_le_of_norm_le hbint (Eventually.of_forall fun z => ?_)).trans ?_
      · by_cases hz : z ∈ B
        · rw [indicator_of_mem hz, Real.norm_eq_abs, abs_mul,
            abs_of_nonneg (sub_nonneg.2 (hinner_le z))]
          exact mul_le_mul_of_nonneg_right (hM' _) (sub_nonneg.2 (hinner_le z))
        · rw [indicator_of_notMem hz, hsupp z hz, zero_mul, norm_zero]
      · rw [integral_indicator measurableSet_closedBall, integral_const_mul]
    have hμB : (μ B).toReal ≤ C * (r * R) ^ n :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hBμ
    rw [hdiff, abs_mul, abs_of_pos (inv_pos.2 (pow_pos hr n))]
    calc (r ^ n)⁻¹ * |∫ z, f (r⁻¹ • (z - y)) * (1 - inner ℝ v (ν z)) ∂μ|
        ≤ (r ^ n)⁻¹ * (M * ((μ B).toReal * |1 - inner ℝ v (A (r * R))|)) := by
          gcongr
          refine hle.trans ?_
          rw [hkey]
          gcongr
          exact le_abs_self _
      _ ≤ (r ^ n)⁻¹ * (M * ((C * (r * R) ^ n) * |1 - inner ℝ v (A (r * R))|)) := by
          gcongr
      _ = M * (C * R ^ n) * |1 - inner ℝ v (A (r * R))| := by
          rw [mul_pow]
          field_simp
  -- the bound tends to zero
  have hAr : Tendsto (fun r : ℝ => A (r * R)) (𝓝[>] 0) (𝓝 v) := by
    refine hA.comp ?_
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := (tendsto_id (x := 𝓝 (0 : ℝ))).mul_const R
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hr hRpos
  have hin : Tendsto (fun r : ℝ => inner ℝ v (A (r * R))) (𝓝[>] 0) (𝓝 1) := by
    have hic : Continuous (fun w : Euclid P => inner ℝ v w) := continuous_const.inner continuous_id
    have := (hic.tendsto v).comp hAr
    simpa [Function.comp_def, real_inner_self_eq_norm_sq, hv] using this
  have h0 : Tendsto (fun r : ℝ => M * (C * R ^ n) * |1 - inner ℝ v (A (r * R))|) (𝓝[>] 0)
      (𝓝 0) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub hin).abs.const_mul (M * (C * R ^ n))
    simpa using this
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < ρ₁ / R :=
    nhdsWithin_le_nhds (gt_mem_nhds (div_pos hρ₁ hRpos))
  have hΔ : Tendsto (fun r : ℝ => (r ^ n)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ -
      (r ^ n)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) * inner ℝ v (ν z) ∂μ) (𝓝[>] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_ h0
    filter_upwards [self_mem_nhdsWithin, hsmall] with r hr hrR
    exact hbound r hr (by have := (lt_div_iff₀ hRpos).mp hrR; linarith)
  have := hL.add hΔ
  simpa using this

## Key steps

1. Rescaled test functions are supported in B̄_{rR}(y), where μ ≤ C(rR)^n is finite.
2. Split f = f⟨v, ν⟩ + f(1 − ⟨v, ν⟩) with 0 ≤ 1 − ⟨v, ν⟩.
3. ∫_{B̄_ρ(y)} (1 − ⟨v, ν⟩) dμ = μ(B̄_ρ(y)) (1 − ⟨v, A(ρ)⟩).
4. Defect ≤ ‖f‖_∞ C R^n |1 − ⟨v, A(rR)⟩| → 0 because A(rR) → v.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json; git -C /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07 rev-parse HEAD; git -C /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib rev-parse HEAD`
- `python3 scans of dag.json: frozen lean_statement of the selected node and of siblings normal_average_ae-a1, cutoff_estimates-a1, blowup_halfspace-a1; accepted nodes grepped for μHE[, ᗮ, LinearMap.trace, symmDiff, Ioi and smooth-approximation statements; collision check of the 10 names codim1_rdo_dg_tma_* (0 hits among 993 nodes)`
- `grep -rn codim1_rdo_dg_tma GMT/ and lake-packages-25730c7c/simongmt (no match)`
- `sed -n 1,420p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (μHE API)`
- `rg in snapshot mathlib: trace_eq_sum_inner, integral_Ioi_of_hasDerivAt_of_tendsto, HasCompactSupport.integral_Ioi_deriv_eq, hasDerivAt_integral_of_dominated_loc_of_deriv_le, measurePreserving_repr_symm, LinearIsometryEquiv.measurePreserving, setIntegral_comp_smul_of_pos, integral_comp_smul, integral_mul_right_eq_self, volume_preserving_piFinSuccAbove, snocEquiv, OrthonormalBasis.sum_repr_symm, integral_prod, support_fderiv_subset, contDiff_convolution_left, support_convolution_subset, exists_contDiff_tsupport_subset, finrank_orthogonal_span_singleton, basisOfOrthonormalOfCardEqFinrank, integral_inner, dist_normed_convolution_le, Submodule.measurePreserving_measurableEquivProd`
- `#check probes after import GMT.Ch07.Submission (/tmp/tma-split-check/Probe*.lean): ContDiffBump.normed, ContDiffBump.dist_normed_convolution_le, integral_inner and EuclideanSpace.volume_preserving_measurableEquiv are unknown constants in the contract's import closure; (volume : Measure (Euclid m × ℝ)) = (volume : Measure (Euclid m)).prod volume holds by rfl`
- `sed -n 540,760p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt (printed proof of Simon Ch. 3, 4.3)`
- `lake env lean -DautoImplicit=false /tmp/tma-split-check/Full.lean (exit 0; #print axioms for the 10 children and the selected node)`
- `sed -n runtime.py _decompose, _dependency_problem, _existing_lean_name_problem, _solve_children; cat swarm-project.json (max_depth 6, max_children 12)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-8598f2d8c1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-8598f2d8c1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Group/Integral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L2Space.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/tma-split-check/Full.lean`
- `/tmp/tma-split-check/Assembly.lean`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/swarm-project.json`

Pins: snapshot manifest project b4d606db… and Mathlib 25730c7c… equal the workspace HEAD and .lake/packages/mathlib. Library: snapshot Mathlib supplies everything the children need: Isometry.map_euclideanHausdorffMeasure (Geometry/Euclidean/Volume/Measure.lean:141), EuclideanSpace.euclideanHausdorffMeasure_eq_volume (:187), LinearMap.trace_eq_sum_inner (InnerProductSpace/Trace.lean:25), HasCompactSupport.integral_Ioi_deriv_eq (IntegralEqImproper.lean:820), hasDerivAt_integral_of_dominated_loc_of_deriv_le (ParametricIntegral.lean:286), OrthonormalBasis.measurePreserving_repr_symm (Haar/InnerProductSpace.lean:114), setIntegral_comp_smul_of_pos (Haar/NormedSpace.lean:148), volume_preserving_piFinSuccAbove (Constructions/Pi.lean:818), integral_prod (Integral/Prod.lean:440), support_fderiv_subset (FDeriv/Const.lean:379), HasCompactSupport.contDiff_convolution_left (ContDiff/Convolution.lean:427), support_convolution_subset (Convolution.lean:670), exists_contDiff_tsupport_subset (BumpFunction/FiniteDimension.lean:45), finrank_orthogonal_span_singleton (Projection/FiniteDimensional.lean:125). ContDiffBump.dist_normed_convolution_le (BumpFunction/Convolution.lean:71) and integral_inner (Function/L2Space.lean:89) exist in the snapshot but are not in the contract's import closure, so the child proofs avoid them. No Mathlib, SimonGMT or accepted-DAG declaration states the half-space Gauss–Green formula, the rescaled Gauss–Green identity, the normal-defect estimate or the C¹-to-C⁰ extension; accepted candidates dimred_rpd_bilipschitz_image_measure, pit_setIntegral_range_linear and dgcr_stc_exists_normalized_mollifier were inspected and not needed, so no reuse. The 10 names codim1_rdo_dg_tma_* have no match among 993 DAG nodes, GMT/ or SimonGMT. Lean: /tmp/tma-split-check/Full.lean elaborates all 10 child types in the frozen contract scope, proves each with axioms propext, Classical.choice, Quot.sound, and proves the selected frozen type (byte-identical to dag.json) from them plus the three sibling stubs with exact frozen types (sorryAx only from the stubs). Runtime: depth 5 < max_depth 6, so the children are depth-6 leaves; 10 ≤ max_children 12.
