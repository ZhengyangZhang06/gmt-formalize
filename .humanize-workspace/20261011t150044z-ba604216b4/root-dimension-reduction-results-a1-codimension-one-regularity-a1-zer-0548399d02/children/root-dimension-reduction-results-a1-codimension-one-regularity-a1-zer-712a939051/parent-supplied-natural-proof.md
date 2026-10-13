# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.bv_compactness-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.bv_compactness-a1.cube_average-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Supplied proof of the parent node, step 5: cube averages, with ‖u_i − Au_i‖_{1,B_R} ≤ C_m·c(R + 3)·δ and C_m = L^m(closedBall(0,1))·m^{(m+1)/2}. This replaces Simon's appeal to [GT01, Theorem 7.22] in Simon Ch. 2, 2.6 (chapter-02.txt lines 598–625). It follows the averaging argument of H. Hanche-Olsen and H. Holden, The Kolmogorov–Riesz compactness theorem, Expo. Math. 28 (2010) 385–394 (arXiv:0906.4883), proof of Theorem 5.
Simplification: the outer integral runs over v ∈ B_R only, with Q_δ(v) the cube of v. So the translation estimate is needed on B_R itself, and no covering of B_R by cubes is used.
No sibling child is used.

Notation. u := 1_F; s := √m·δ ∈ [0, 1]; B := B_R(0); cB := closedBall(0, s); a(v) := L^m(F ∩ Q_δ(v))/δ^m, as a real number via toReal. Take K := (√m)^{m+1}·L^m(B_1(0)), which is finite and ≥ 0.

1. (The cube.) For δ > 0 and an integer k, ⌊x/δ⌋ = k ⇔ δk ≤ x < δ(k + 1). So Q_δ(v) is the preimage of the box Π_j[δk_j, δ(k_j + 1)), k_j := ⌊v_j/δ⌋, under the measure-preserving identification of Euclid m with ℝ^{Fin m} (PiLp.volume_preserving_ofLp). Hence Q_δ(v) is measurable and L^m(Q_δ(v)) = δ^m (Real.volume_pi_Ico).
2. (Diameter.) For w ∈ Q_δ(v), |w_j − v_j| ≤ δ for every j. So |w − v| = (Σ_j(w_j − v_j)²)^{1/2} ≤ √m·δ = s, i.e. Q_δ(v) ⊆ closedBall(v, s).
3. (Pointwise bound.) Fix v and put Q := Q_δ(v). Since L^m(Q) = δ^m and ∫_Q u = L^m(F ∩ Q),
   u(v) − a(v) = δ^{−m}∫_Q (u(v) − u(w)) dw.
   By step 2 and then the translation w = v + h,
   |u(v) − a(v)| ≤ δ^{−m}∫⁻_Q|u(v) − u(w)| dw ≤ δ^{−m}∫⁻_{closedBall(v,s)}|u(v) − u(w)| dw = δ^{−m}∫⁻_{h∈cB}|u(v) − u(v + h)| dh.
4. (Tonelli.) The function (v, h) ↦ |u(v) − u(v + h)| is measurable. Integrate step 3 over v ∈ B and exchange the order. (lintegral_mono needs no measurability of a.)
   ∫⁻_B|u − a| ≤ δ^{−m}∫⁻_{h∈cB}∫⁻_{v∈B}|u(v + h) − u(v)| dv dh.
5. (Hypothesis.) For h ∈ cB, |h| ≤ s ≤ 1. The inner integral equals L^m(((F − h) Δ F) ∩ B), because the integrand is the indicator of the symmetric difference. By the hypothesis and C ≥ 0 it is ≤ C|h| ≤ Cs.
6. (Computation.) L^m(cB) = s^m·L^m(B_1(0)) (Measure.addHaar_closedBall; finrank = m). Hence
   ∫⁻_B|u − a| ≤ δ^{−m}·Cs·s^m·L^m(B_1(0)) = (√m)^{m+1}L^m(B_1(0))·C·δ = KCδ. ∎
Edge cases. For m = 0: s = 0, cB = {0}, Q_δ(v) = ℝ^0 = {v}, and both sides are 0. For R ≤ 0 the left side is 0.

Appendix (Lean proof, kernel-checked). Compiled with the pinned toolchain (Lean v4.35.0-rc3, Mathlib 25730c7c) inside namespace GMT.Ch07 of a file importing GMT.Ch07.Submission, with the contract's opens. It is one declaration with no helper declaration and no set_option. #print axioms gives propext, Classical.choice and Quot.sound.
Note: `w j` elaborates to WithLp.ofLp w j, and Set.mem_setOf_eq is deprecated in favour of Set.mem_ofPred_eq.

theorem Submission.codim1_zsl_pc_cube_average_bound : ∀ (m : ℕ), ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : Set (Euclid m)) (R C δ : ℝ), MeasurableSet F → 0 ≤ C → 0 < δ → δ * Real.sqrt m ≤ 1 → (∀ h : Euclid m, ‖h‖ ≤ 1 → volume (symmDiff ((fun v => v + h) ⁻¹' F) F ∩ ball (0 : Euclid m) R) ≤ ENNReal.ofReal (C * ‖h‖)) → ∫⁻ v in ball (0 : Euclid m) R, ‖F.indicator (fun _ => (1 : ℝ)) v - (volume (F ∩ {w : Euclid m | ∀ j, ⌊w j / δ⌋ = ⌊v j / δ⌋})).toReal / δ ^ m‖ₑ ≤ ENNReal.ofReal (K * C * δ) := by
  intro m
  refine ⟨Real.sqrt m ^ (m + 1) * (volume (ball (0 : Euclid m) 1)).toReal, by positivity, ?_⟩
  intro F R C δ hF hC hδ hδm hsd
  have hu_meas : Measurable (F.indicator (fun _ => (1 : ℝ))) := measurable_const.indicator hF
  have hs0 : 0 ≤ Real.sqrt m * δ := by positivity
  have hs1 : Real.sqrt m * δ ≤ 1 := by rw [mul_comm]; exact hδm
  have hδm0 : 0 < δ ^ m := pow_pos hδ m
  -- Step 1: the cube `Q v` is (the preimage of) a half-open box of side `δ`
  have hQbox : ∀ v : Euclid m, {w : Euclid m | ∀ j, ⌊w j / δ⌋ = ⌊v j / δ⌋} =
      (WithLp.ofLp : Euclid m → (Fin m → ℝ)) ⁻¹'
        (Set.pi univ fun j => Ico ((⌊v j / δ⌋ : ℝ) * δ) (((⌊v j / δ⌋ : ℝ) + 1) * δ)) := by
    intro v
    ext w
    simp only [Set.mem_ofPred_eq, mem_preimage, Set.mem_pi, mem_univ, true_implies, mem_Ico]
    refine forall_congr' fun j => ?_
    rw [Int.floor_eq_iff, le_div_iff₀ hδ, div_lt_iff₀ hδ]
  have hbox_meas : ∀ v : Euclid m,
      MeasurableSet (Set.pi univ fun j => Ico ((⌊v j / δ⌋ : ℝ) * δ) (((⌊v j / δ⌋ : ℝ) + 1) * δ)) :=
    fun v => MeasurableSet.univ_pi fun j => measurableSet_Ico
  have hQvol : ∀ v : Euclid m,
      volume {w : Euclid m | ∀ j, ⌊w j / δ⌋ = ⌊v j / δ⌋} = ENNReal.ofReal (δ ^ m) := by
    intro v
    rw [hQbox v, (PiLp.volume_preserving_ofLp (Fin m)).measure_preimage
      (hbox_meas v).nullMeasurableSet, Real.volume_pi_Ico]
    have : ∀ j : Fin m, ((⌊v j / δ⌋ : ℝ) + 1) * δ - (⌊v j / δ⌋ : ℝ) * δ = δ := fun j => by ring
    simp only [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ENNReal.ofReal_pow hδ.le]
  -- Step 2: the cube lies in the closed ball of radius `√m δ` about `v`
  have hQball : ∀ v : Euclid m,
      {w : Euclid m | ∀ j, ⌊w j / δ⌋ = ⌊v j / δ⌋} ⊆ closedBall v (Real.sqrt m * δ) := by
    intro v w hw
    rw [hQbox v] at hw
    simp only [mem_preimage, Set.mem_pi, mem_univ, true_implies, mem_Ico] at hw
    rw [mem_closedBall, EuclideanSpace.dist_eq]
    have hcoord : ∀ j, dist (w j) (v j) ^ 2 ≤ δ ^ 2 := by
      intro j
      have hwj := hw j
      have h1 := Int.floor_le (v j / δ)
      have h2 := Int.lt_floor_add_one (v j / δ)
      rw [le_div_iff₀ hδ] at h1
      rw [div_lt_iff₀ hδ] at h2
      have hab : |w j - v j| ≤ δ := by
        rw [abs_le]; constructor <;> nlinarith [hwj.1, hwj.2]
      rw [Real.dist_eq]
      exact pow_le_pow_left₀ (abs_nonneg _) hab 2
    calc Real.sqrt (∑ j, dist (w j) (v j) ^ 2) ≤ Real.sqrt (∑ _j : Fin m, δ ^ 2) :=
          Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ => hcoord j)
      _ = Real.sqrt m * δ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Real.sqrt_mul (Nat.cast_nonneg m), Real.sqrt_sq hδ.le]
  -- Step 3: pointwise bound by an average of differences over the closed ball
  have hpt : ∀ (v : Euclid m) (Q : Set (Euclid m)), volume Q = ENNReal.ofReal (δ ^ m) →
      Q ⊆ closedBall v (Real.sqrt m * δ) →
      ‖F.indicator (fun _ => (1 : ℝ)) v - (volume (F ∩ Q)).toReal / δ ^ m‖ₑ ≤
        ENNReal.ofReal ((δ ^ m)⁻¹) * ∫⁻ h in closedBall (0 : Euclid m) (Real.sqrt m * δ),
          ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ := by
    intro v Q hQv hQb
    have hQfin : volume Q ≠ ∞ := by rw [hQv]; exact ENNReal.ofReal_ne_top
    have : IsFiniteMeasure (volume.restrict Q) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hQfin.lt_top⟩
    have hint_c : Integrable (fun _ : Euclid m => F.indicator (fun _ => (1 : ℝ)) v)
        (volume.restrict Q) := integrable_const _
    have hint_u : Integrable (F.indicator (fun _ => (1 : ℝ))) (volume.restrict Q) :=
      (integrable_const (1 : ℝ)).indicator hF
    have h1 : ∫ w in Q, F.indicator (fun _ => (1 : ℝ)) w = (volume (F ∩ Q)).toReal := by
      rw [integral_indicator_const (1 : ℝ) hF, smul_eq_mul, mul_one,
        measureReal_restrict_apply hF, measureReal_def]
    have h2 : F.indicator (fun _ => (1 : ℝ)) v - (volume (F ∩ Q)).toReal / δ ^ m =
        (δ ^ m)⁻¹ * ∫ w in Q, (F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) w) := by
      rw [integral_sub hint_c hint_u, setIntegral_const, h1, measureReal_def, hQv,
        ENNReal.toReal_ofReal hδm0.le, smul_eq_mul, mul_sub, ← mul_assoc,
        inv_mul_cancel₀ hδm0.ne', one_mul, div_eq_inv_mul]
    have h3 : ‖F.indicator (fun _ => (1 : ℝ)) v - (volume (F ∩ Q)).toReal / δ ^ m‖ₑ ≤
        ENNReal.ofReal ((δ ^ m)⁻¹) *
          ∫⁻ w in Q, ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) w‖ₑ := by
      rw [h2, enorm_mul, Real.enorm_eq_ofReal (inv_nonneg.2 hδm0.le)]
      exact mul_le_mul' le_rfl (enorm_integral_le_lintegral_enorm _)
    have h4 : ∫⁻ w in Q, ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) w‖ₑ ≤
        ∫⁻ h in closedBall (0 : Euclid m) (Real.sqrt m * δ),
          ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ := by
      calc ∫⁻ w in Q, ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) w‖ₑ
          ≤ ∫⁻ w in closedBall v (Real.sqrt m * δ),
              ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) w‖ₑ :=
            lintegral_mono_set hQb
        _ = ∫⁻ h in closedBall (0 : Euclid m) (Real.sqrt m * δ),
              ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ := by
          rw [← lintegral_indicator measurableSet_closedBall,
            ← lintegral_indicator measurableSet_closedBall,
            ← lintegral_add_left_eq_self ((closedBall v (Real.sqrt m * δ)).indicator fun w =>
              ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) w‖ₑ) v]
          refine lintegral_congr fun h => ?_
          have hmem : v + h ∈ closedBall v (Real.sqrt m * δ) ↔
              h ∈ closedBall (0 : Euclid m) (Real.sqrt m * δ) := by
            rw [mem_closedBall, mem_closedBall, dist_eq_norm, dist_eq_norm, add_sub_cancel_left,
              sub_zero]
          by_cases hh : h ∈ closedBall (0 : Euclid m) (Real.sqrt m * δ)
          · rw [indicator_of_mem (hmem.2 hh), indicator_of_mem hh]
          · rw [indicator_of_notMem (mt hmem.1 hh), indicator_of_notMem hh]
    exact h3.trans (mul_le_mul' le_rfl h4)
  -- Step 4: integrate, swap the order of integration, and use the hypothesis
  have hind : ∀ v h : Euclid m,
      ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ =
        (symmDiff ((fun v => v + h) ⁻¹' F) F).indicator 1 v := by
    intro v h
    by_cases h1 : v ∈ F <;> by_cases h2 : v + h ∈ F <;>
      simp [h1, h2, Set.mem_symmDiff]
  have hinner : ∀ h ∈ closedBall (0 : Euclid m) (Real.sqrt m * δ),
      ∫⁻ v in ball (0 : Euclid m) R,
          ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ ≤
        ENNReal.ofReal (C * (Real.sqrt m * δ)) := by
    intro h hh
    have hh' : ‖h‖ ≤ Real.sqrt m * δ := mem_closedBall_zero_iff.1 hh
    calc ∫⁻ v in ball (0 : Euclid m) R,
          ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ
        = ∫⁻ v in ball (0 : Euclid m) R, (symmDiff ((fun v => v + h) ⁻¹' F) F).indicator 1 v :=
          lintegral_congr fun v => hind v h
      _ ≤ (volume.restrict (ball (0 : Euclid m) R)) (symmDiff ((fun v => v + h) ⁻¹' F) F) :=
          lintegral_indicator_one_le _
      _ = volume (symmDiff ((fun v => v + h) ⁻¹' F) F ∩ ball (0 : Euclid m) R) :=
          Measure.restrict_apply' measurableSet_ball
      _ ≤ ENNReal.ofReal (C * ‖h‖) := hsd h (hh'.trans hs1)
      _ ≤ ENNReal.ofReal (C * (Real.sqrt m * δ)) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hh' hC)
  have hmeas2 : Measurable (uncurry fun (v h : Euclid m) =>
      ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ) := by
    have : Measurable fun p : Euclid m × Euclid m =>
        F.indicator (fun _ => (1 : ℝ)) p.1 - F.indicator (fun _ => (1 : ℝ)) (p.1 + p.2) :=
      (hu_meas.comp measurable_fst).sub (hu_meas.comp (measurable_fst.add measurable_snd))
    exact this.enorm
  have hV1fin : volume (ball (0 : Euclid m) 1) ≠ ∞ := measure_ball_lt_top.ne
  calc ∫⁻ v in ball (0 : Euclid m) R, ‖F.indicator (fun _ => (1 : ℝ)) v -
        (volume (F ∩ {w : Euclid m | ∀ j, ⌊w j / δ⌋ = ⌊v j / δ⌋})).toReal / δ ^ m‖ₑ
      ≤ ∫⁻ v in ball (0 : Euclid m) R, ENNReal.ofReal ((δ ^ m)⁻¹) *
          ∫⁻ h in closedBall (0 : Euclid m) (Real.sqrt m * δ),
            ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ :=
        lintegral_mono fun v => hpt v _ (hQvol v) (hQball v)
    _ = ENNReal.ofReal ((δ ^ m)⁻¹) * ∫⁻ v in ball (0 : Euclid m) R,
          ∫⁻ h in closedBall (0 : Euclid m) (Real.sqrt m * δ),
            ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal ((δ ^ m)⁻¹) * ∫⁻ h in closedBall (0 : Euclid m) (Real.sqrt m * δ),
          ∫⁻ v in ball (0 : Euclid m) R,
            ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ := by
        rw [lintegral_lintegral_swap (μ := volume.restrict (ball (0 : Euclid m) R))
          (ν := volume.restrict (closedBall (0 : Euclid m) (Real.sqrt m * δ)))
          hmeas2.aemeasurable]
    _ ≤ ENNReal.ofReal ((δ ^ m)⁻¹) * ∫⁻ h in closedBall (0 : Euclid m) (Real.sqrt m * δ),
          ENNReal.ofReal (C * (Real.sqrt m * δ)) :=
        mul_le_mul' le_rfl (setLIntegral_mono measurable_const hinner)
    _ = ENNReal.ofReal ((δ ^ m)⁻¹) * (ENNReal.ofReal (C * (Real.sqrt m * δ)) *
          (ENNReal.ofReal ((Real.sqrt m * δ) ^ m) * volume (ball (0 : Euclid m) 1))) := by
        rw [setLIntegral_const, Measure.addHaar_closedBall _ _ hs0, finrank_euclideanSpace_fin]
    _ = ENNReal.ofReal (Real.sqrt m ^ (m + 1) * (volume (ball (0 : Euclid m) 1)).toReal * C * δ) := by
        have e1 : Real.sqrt m ^ (m + 1) * (volume (ball (0 : Euclid m) 1)).toReal * C * δ =
            ((δ ^ m)⁻¹ * (C * (Real.sqrt m * δ)) * (Real.sqrt m * δ) ^ m) *
              (volume (ball (0 : Euclid m) 1)).toReal := by
          rw [mul_pow]
          field_simp
          ring
        rw [e1, ENNReal.ofReal_mul (p := (δ ^ m)⁻¹ * (C * (Real.sqrt m * δ)) * (Real.sqrt m * δ) ^ m)
            (by positivity), ENNReal.ofReal_toReal hV1fin,
          ENNReal.ofReal_mul (p := (δ ^ m)⁻¹ * (C * (Real.sqrt m * δ))) (by positivity),
          ENNReal.ofReal_mul (p := (δ ^ m)⁻¹) (by positivity)]
        ring

## Key steps

1. Q_δ(v) is a half-open box of side δ: measurable, of volume δ^m, and contained in closedBall(v, √mδ).
2. |1_F(v) − a(v)| ≤ δ^{−m}∫_{|h|≤√mδ}|1_F(v) − 1_F(v + h)| dh.
3. Tonelli over v ∈ B_R: the inner integral is L(((F − h) Δ F) ∩ B_R) ≤ C|h| ≤ C√mδ.
4. L(closedBall(0, √mδ)) = (√mδ)^m·L(B_1) gives the bound (√m)^{m+1}·L(B_1)·Cδ.

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
