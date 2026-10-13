# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.density_bounds-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.density_bounds-a1.tangent_lower_density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof Step 5a, specialized to the half the parent actually uses (Simon Ch. 3, Definition 1.4 and Remark 1.5(3), chapter-03.txt lines 77–96). Simon takes f ∈ C_c with 0 ≤ f ≤ 1, f ≡ 1 on B_1(0) and f ≡ 0 off B_{1+ε}(0) in Definition 1.4 and lets ε ↓ 0. Only the lower bound lim inf_{t↓0} Hⁿ(M ∩ B_t(x))/(ω_ntⁿ) ≥ 1 is proved here; it needs no finiteness of Hⁿ⌞M. Library note: SimonGMT's Chapter04/TangentDensity.lean proves the same ingredients (planeMeasure_unit_closedBall, hausdorff_blowUp_image, blowUp_image_inter_closedBall, tangentDensityCutoff), but that module is outside the import closure of GMT.Ch07.Submission. The argument below therefore uses only Mathlib and SimonGMT Chapter03.

Notation: E := ℝ^P (Euclid P); Hⁿ := μHE[n]; ω := unitBallVolume n, the Lebesgue measure of the open unit ball of Euclid n; a⁺ := ENNReal.ofReal a; η_r(y) := r⁻¹(y − x) (blowUpMap x r) for r > 0; B_t(y) closed ball; I(r) := ∫_{η_r(M)} ψ dHⁿ for the cutoff ψ of Step 4.

1. ω ∈ (0, ∞). The open unit ball of Euclid n is nonempty and open, so it has positive Lebesgue measure (measure_ball_pos). It is bounded, so its measure is finite (measure_ball_lt_top). Put ω_ℝ := ω.toReal > 0; then ω = ω_ℝ⁺.
2. Trivial case. If c ≤ 0 then c⁺ = 0 and 0 ≤ Hⁿ(M ∩ B_t(x)) for every t. Assume 0 < c < 1 from now on. The hypothesis gives dim Q = n and the convergence property.
3. Plane ball: (Hⁿ⌞Q)(B_1(0)) = ω.
 (a) The inclusion ι : Q → E is a linear isometry with range Q, so Hⁿ⌞Q is the push-forward of μHE[n] on Q under ι (Isometry.map_euclideanHausdorffMeasure). Also ι⁻¹(B_1(0)) is the closed unit ball of Q.
 (b) Since dim Q = n, μHE[n] on Q is its volume (InnerProductSpace.euclideanHausdorffMeasure_eq_volume).
 (c) Q is nontrivial (n ≥ 1), so its closed and open unit balls have the same volume (Measure.addHaar_closedBall_eq_addHaar_ball).
 (d) An orthonormal basis of Q gives a linear isometric equivalence e : Q → Euclid n. It preserves volume (LinearIsometryEquiv.measurePreserving) and e⁻¹(ball(0,1)) = ball(0,1), so the open unit ball of Q has volume ω.
4. Choice of ε and cutoff.
 (a) As ε ↓ 0, c(1 + ε)ⁿ → c < 1. Fix ε > 0 with c(1 + ε)ⁿ < 1 and put A := 1 + ε.
 (b) Define ψ(y) := max(0, min(1, (A − |y|)/ε)). Then ψ is continuous and 0 ≤ ψ ≤ 1.
 (c) ψ(y) = 1 for |y| ≤ 1, since (A − |y|)/ε ≥ 1; and ψ(y) = 0 for |y| > A, since (A − |y|)/ε < 0.
 (d) So ψ vanishes off the compact ball B_A(0) and ψ ∈ C_c(E, ℝ).
5. Plane integral: L := ∫_Q ψ dHⁿ ≥ ω_ℝ. Hⁿ⌞Q is finite on compact sets (SimonGMT Chapter03 regular_euclideanHausdorffMeasure_restrict_submodule), so ψ is Hⁿ⌞Q-integrable. Since ψ ≥ 0, L ≥ ∫_{B_1(0)} ψ d(Hⁿ⌞Q) (setIntegral_le_integral). As ψ = 1 on B_1(0), the latter equals (Hⁿ⌞Q)(B_1(0)).toReal = ω_ℝ by Step 3.
6. Convergence. The hypothesis applied to f = ψ gives I(r) → L as r ↓ 0. Since cAⁿω_ℝ < ω_ℝ ≤ L (Steps 4 and 5), there is r₀ > 0 with I(r) > cAⁿω_ℝ for all r ∈ (0, r₀).
7. Scaling. Fix r > 0 and S ⊆ E.
 (a) η_r is the translation y ↦ y − x (an isometry) followed by the homothety of ratio r⁻¹ about 0. Hence Hⁿ(η_r(S)) = ((r⁻¹)⁺)ⁿ·Hⁿ(S) (Isometry.euclideanHausdorffMeasure_image, euclideanHausdorffMeasure_homothety_image).
 (b) |η_r(y)| ≤ A ⟺ |y − x| ≤ rA, so η_r(B_{rA}(x) ∩ S) = B_A(0) ∩ η_r(S).
 (c) Therefore (Hⁿ⌞η_r(M))(B_A(0)) = Hⁿ(B_A(0) ∩ η_r(M)) = ((r⁻¹)⁺)ⁿ·Hⁿ(M ∩ B_{rA}(x)).
8. Upper bound. Let r > 0 with Hⁿ(M ∩ B_{rA}(x)) < ∞. By Step 7, ν_r := Hⁿ⌞η_r(M) has ν_r(B_A(0)) < ∞. Since ψ vanishes off B_A(0) and |ψ| ≤ 1:
 I(r) = ∫_{B_A(0)} ψ dν_r (setIntegral_eq_integral_of_forall_compl_eq_zero), and
 |I(r)| ≤ ν_r(B_A(0)).toReal = r^{−n}·Hⁿ(M ∩ B_{rA}(x)).toReal (norm_setIntegral_le_of_norm_le_const_ae).
9. Conclusion. Let t ∈ (0, Ar₀) and r := t/A ∈ (0, r₀), so rA = t.
 (a) If Hⁿ(M ∩ B_t(x)) = ∞, the claim is trivial.
 (b) Otherwise Steps 6 and 8 give cAⁿω_ℝ < I(r) ≤ r^{−n}·Hⁿ(M ∩ B_t(x)).toReal. Multiplying by rⁿ > 0 and using Aⁿrⁿ = tⁿ gives cω_ℝtⁿ ≤ Hⁿ(M ∩ B_t(x)).toReal.
 (c) Hence c⁺·ω·(tⁿ)⁺ = (cω_ℝtⁿ)⁺ ≤ Hⁿ(M ∩ B_t(x)) (ENNReal.ofReal_mul, ENNReal.ofReal_toReal).
 (d) t ↦ t/A maps 𝓝[>]0 into 𝓝[>]0, so (0, Ar₀) ∈ 𝓝[>]0 and the inequality holds for all sufficiently small t > 0. ∎

Appendix: Lean proof of exactly this statement, following Steps 1–9. It was kernel-checked (lean-4.35.0-rc3, Mathlib 25730c7c, after import GMT.Ch07.Submission in the contract scope); #print axioms gives propext, Classical.choice, Quot.sound.
theorem Submission.dorag_dbs_approxTangent_lower_density : ∀ (P n : ℕ) (M : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)), 0 < n → HasApproximateTangentSpaceAt n M x Q → ∀ c : ℝ, c < 1 → ∀ᶠ t in 𝓝[>] (0 : ℝ), ENNReal.ofReal c * unitBallVolume n * ENNReal.ofReal (t ^ n) ≤ μHE[n] (M ∩ closedBall x t) := by
  intro P n M x Q hn hQ c hc
  by_cases hc0 : c ≤ 0
  · filter_upwards with t
    simp [ENNReal.ofReal_of_nonpos hc0]
  push Not at hc0
  obtain ⟨hfin, hconv⟩ := hQ
  -- the unit-ball volume
  have hω0 : unitBallVolume n ≠ 0 := by
    unfold unitBallVolume
    exact (measure_ball_pos volume (0 : Euclid n) one_pos).ne'
  have hωtop : unitBallVolume n ≠ ∞ := by
    unfold unitBallVolume
    exact measure_ball_lt_top.ne
  have hωr : 0 < (unitBallVolume n).toReal := ENNReal.toReal_pos hω0 hωtop
  -- Step 5(a): the plane ball has measure ω_n
  have hQball : (μHE[n].restrict (Q : Set (Euclid P))) (closedBall 0 1) = unitBallVolume n := by
    have : Nontrivial Q := Module.nontrivial_of_finrank_pos (hfin.symm ▸ hn)
    have hrange : Set.range (Q.subtypeₗᵢ : Q → Euclid P) = (Q : Set (Euclid P)) := by
      ext y; simp
    rw [← hrange, ← Q.subtypeₗᵢ.isometry.map_euclideanHausdorffMeasure,
      Measure.map_apply Q.subtypeₗᵢ.continuous.measurable measurableSet_closedBall]
    have hpre : (Q.subtypeₗᵢ : Q → Euclid P) ⁻¹' closedBall (0 : Euclid P) 1 =
        closedBall (0 : Q) 1 := by
      ext y; simp [mem_closedBall, dist_eq_norm]
    have hvol : (μHE[n] : Measure Q) = volume := by
      rw [← hfin]; exact InnerProductSpace.euclideanHausdorffMeasure_eq_volume
    rw [hpre, hvol, Measure.addHaar_closedBall_eq_addHaar_ball]
    rw [← hfin]
    unfold unitBallVolume
    let e := (stdOrthonormalBasis ℝ Q).repr
    have hmp : MeasurePreserving e volume volume := e.measurePreserving
    rw [← hmp.measure_preimage measurableSet_ball.nullMeasurableSet]
    congr 1
    ext y
    simp [e, mem_ball, dist_eq_norm]
  -- choice of ε
  have hεlim : Tendsto (fun ε : ℝ => c * (1 + ε) ^ n) (𝓝[>] (0 : ℝ)) (𝓝 c) := by
    have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 1) := tendsto_const_nhds
    simpa only [id_eq, add_zero, one_pow, mul_one] using
      ((hone.add (tendsto_id.mono_left inf_le_left :
        Tendsto id (𝓝[>] (0 : ℝ)) (𝓝 0))).pow n).const_mul c
  obtain ⟨ε, hεc, hε⟩ :=
    ((hεlim.eventually (gt_mem_nhds hc)).and self_mem_nhdsWithin).exists
  have hε0 : 0 < ε := hε
  have hA : 0 < 1 + ε := by linarith
  -- the cutoff ψ
  let ψf : Euclid P → ℝ := fun y => max 0 (min 1 ((1 + ε - ‖y‖) / ε))
  have hψcont : Continuous ψf := by
    apply continuous_const.max
    apply continuous_const.min
    exact (continuous_const.sub continuous_norm).div_const ε
  have hψ0 : ∀ y, y ∉ closedBall (0 : Euclid P) (1 + ε) → ψf y = 0 := by
    intro y hy
    have hy' : 1 + ε < ‖y‖ := by simpa [mem_closedBall, dist_eq_norm] using hy
    have hneg : (1 + ε - ‖y‖) / ε < 0 := div_neg_of_neg_of_pos (by linarith) hε0
    simp only [ψf]
    exact max_eq_left ((min_le_right _ _).trans hneg.le)
  have hψsupp : HasCompactSupport ψf :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Euclid P) (1 + ε)) hψ0
  let ψ : CompactlySupportedContinuousMap (Euclid P) ℝ :=
    { toFun := ψf, continuous_toFun := hψcont, hasCompactSupport' := hψsupp }
  have hψapp : ∀ y, ψ y = ψf y := fun _ => rfl
  have hψ01 : ∀ y, 0 ≤ ψf y ∧ ψf y ≤ 1 := by
    intro y
    exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hψ1 : ∀ y ∈ closedBall (0 : Euclid P) 1, ψf y = 1 := by
    intro y hy
    have hy' : ‖y‖ ≤ 1 := by simpa [mem_closedBall, dist_eq_norm] using hy
    have h1 : 1 ≤ (1 + ε - ‖y‖) / ε := by
      rw [le_div_iff₀ hε0]; linarith
    simp only [ψf]
    rw [min_eq_left h1]
    exact max_eq_right zero_le_one
  -- Step 5: the plane integral is at least ω_n
  have hplane : (unitBallVolume n).toReal ≤ ∫ y in (Q : Set (Euclid P)), ψ y ∂μHE[n] := by
    have := Poincare.SimonGMT.Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule
      (E := Euclid P) hfin
    have hint : Integrable ψ (μHE[n].restrict (Q : Set (Euclid P))) :=
      ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
    have hle := setIntegral_le_integral (s := closedBall (0 : Euclid P) 1) hint
      (Eventually.of_forall (fun y => (hψ01 y).1))
    have heq : ∫ y in closedBall (0 : Euclid P) 1, ψ y ∂(μHE[n].restrict (Q : Set (Euclid P))) =
        (unitBallVolume n).toReal := by
      have hcongr : ∫ y in closedBall (0 : Euclid P) 1, ψ y ∂(μHE[n].restrict (Q : Set (Euclid P))) =
          ∫ _ in closedBall (0 : Euclid P) 1, (1 : ℝ) ∂(μHE[n].restrict (Q : Set (Euclid P))) :=
        setIntegral_congr_fun measurableSet_closedBall (fun y hy => by rw [hψapp]; exact hψ1 y hy)
      rw [hcongr]
      simp only [integral_const, smul_eq_mul, mul_one, measureReal_def,
        Measure.restrict_apply_univ, hQball]
    rw [heq] at hle
    exact hle
  -- Step 6: eventually the blow-up integrals exceed c (1+ε)^n ω_n
  have hgap : c * (1 + ε) ^ n * (unitBallVolume n).toReal <
      ∫ y in (Q : Set (Euclid P)), ψ y ∂μHE[n] := by
    have : c * (1 + ε) ^ n * (unitBallVolume n).toReal < (unitBallVolume n).toReal := by
      nlinarith
    linarith
  have hev := (hconv ψ).eventually (lt_mem_nhds hgap)
  -- Step 8: scaling of the blow-up
  have hscale : ∀ r : ℝ, 0 < r → ∀ S : Set (Euclid P),
      μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S) =
        ENNReal.ofReal (r⁻¹) ^ n * μHE[n] S := by
    intro r hr S
    have hshift : Isometry (fun y : Euclid P => y - x) := by
      apply Isometry.of_dist_eq
      intro a b
      simp only [dist_eq_norm]
      congr 1
      abel
    have himage : Poincare.SimonGMT.Chapter03.blowUpMap x r '' S =
        AffineMap.homothety (0 : Euclid P) r⁻¹ '' ((fun y : Euclid P => y - x) '' S) := by
      rw [← image_comp]
      congr 1
      funext y
      simp [Poincare.SimonGMT.Chapter03.blowUpMap, AffineMap.homothety_apply]
    rw [himage, euclideanHausdorffMeasure_homothety_image n (0 : Euclid P) (inv_ne_zero hr.ne'),
      hshift.euclideanHausdorffMeasure_image]
    simp only [ENNReal.smul_def, ENNReal.coe_pow, smul_eq_mul]
    congr 2
    rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, Real.norm_of_nonneg (inv_pos.mpr hr).le]
  have hinter : ∀ r : ℝ, 0 < r → ∀ S : Set (Euclid P),
      Poincare.SimonGMT.Chapter03.blowUpMap x r '' (closedBall x (r * (1 + ε)) ∩ S) =
        closedBall (0 : Euclid P) (1 + ε) ∩ (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S) := by
    intro r hr S
    have hmem : ∀ y : Euclid P, Poincare.SimonGMT.Chapter03.blowUpMap x r y ∈
        closedBall (0 : Euclid P) (1 + ε) ↔ y ∈ closedBall x (r * (1 + ε)) := by
      intro y
      simp only [mem_closedBall, dist_eq_norm, sub_zero, Poincare.SimonGMT.Chapter03.blowUpMap,
        norm_smul, Real.norm_of_nonneg (inv_pos.mpr hr).le]
      rw [← div_eq_inv_mul, div_le_iff₀ hr, mul_comm r (1 + ε)]
    ext y
    constructor
    · rintro ⟨z, ⟨hzB, hzS⟩, rfl⟩
      exact ⟨(hmem z).mpr hzB, mem_image_of_mem _ hzS⟩
    · rintro ⟨hyB, z, hzS, rfl⟩
      exact ⟨z, ⟨(hmem z).mp hyB, hzS⟩, rfl⟩
  -- Step 7: upper bound for the blow-up integrals
  have hup : ∀ r : ℝ, 0 < r → μHE[n] (M ∩ closedBall x (r * (1 + ε))) ≠ ∞ →
      (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, ψ y ∂μHE[n]) ≤
        (r⁻¹) ^ n * (μHE[n] (M ∩ closedBall x (r * (1 + ε)))).toReal := by
    intro r hr hfinM
    have hνB : (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap x r '' M))
        (closedBall (0 : Euclid P) (1 + ε)) =
          ENNReal.ofReal (r⁻¹) ^ n * μHE[n] (M ∩ closedBall x (r * (1 + ε))) := by
      rw [Measure.restrict_apply measurableSet_closedBall, ← hinter r hr M, hscale r hr,
        inter_comm]
    have hνfin : (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap x r '' M))
        (closedBall (0 : Euclid P) (1 + ε)) < ∞ := by
      rw [hνB]
      exact ENNReal.mul_lt_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top).lt_top hfinM.lt_top
    have hnorm := norm_setIntegral_le_of_norm_le_const_ae (f := fun y => ψ y) hνfin
      (Eventually.of_forall (fun y => show ‖ψ y‖ ≤ 1 by
        rw [hψapp, Real.norm_of_nonneg (hψ01 y).1]
        exact (hψ01 y).2))
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by rw [hψapp]; exact hψ0 y hy),
      one_mul] at hnorm
    calc (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, ψ y ∂μHE[n])
        ≤ ‖∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, ψ y ∂μHE[n]‖ := le_abs_self _
      _ ≤ _ := hnorm
      _ = (r⁻¹) ^ n * (μHE[n] (M ∩ closedBall x (r * (1 + ε)))).toReal := by
        rw [measureReal_def, hνB, ENNReal.toReal_mul, ENNReal.toReal_pow,
          ENNReal.toReal_ofReal (inv_pos.mpr hr).le]
  -- Step 9: conclusion with r = t / (1 + ε)
  have hrA : Tendsto (fun t : ℝ => t / (1 + ε)) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [zero_div, id_eq] using
        (tendsto_id.mono_left inf_le_left : Tendsto id (𝓝[>] (0 : ℝ)) (𝓝 0)).div_const (1 + ε)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact div_pos ht hA
  filter_upwards [hrA.eventually hev, self_mem_nhdsWithin] with t ht htpos
  have htpos' : 0 < t := htpos
  have hr : 0 < t / (1 + ε) := div_pos htpos' hA
  have hrA' : t / (1 + ε) * (1 + ε) = t := div_mul_cancel₀ _ hA.ne'
  by_cases hH : μHE[n] (M ∩ closedBall x t) = ∞
  · rw [hH]; exact le_top
  have hb := hup (t / (1 + ε)) hr (by rwa [hrA'])
  rw [hrA'] at hb
  have h1 : c * (1 + ε) ^ n * (unitBallVolume n).toReal <
      ((t / (1 + ε))⁻¹) ^ n * (μHE[n] (M ∩ closedBall x t)).toReal := lt_of_lt_of_le ht hb
  have hrn : 0 < (t / (1 + ε)) ^ n := pow_pos hr n
  have h2 : ((t / (1 + ε))⁻¹) ^ n * (t / (1 + ε)) ^ n = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hr.ne', one_pow]
  have h3 : (1 + ε) ^ n * (t / (1 + ε)) ^ n = t ^ n := by
    rw [← mul_pow, mul_comm, hrA']
  have hreal : c * (unitBallVolume n).toReal * t ^ n ≤ (μHE[n] (M ∩ closedBall x t)).toReal := by
    have h4 := mul_lt_mul_of_pos_right h1 hrn
    calc c * (unitBallVolume n).toReal * t ^ n
        = c * (1 + ε) ^ n * (unitBallVolume n).toReal * (t / (1 + ε)) ^ n := by
          rw [← h3]; ring
      _ ≤ ((t / (1 + ε))⁻¹) ^ n * (μHE[n] (M ∩ closedBall x t)).toReal * (t / (1 + ε)) ^ n :=
          h4.le
      _ = (μHE[n] (M ∩ closedBall x t)).toReal := by
          rw [mul_right_comm, h2, one_mul]
  calc ENNReal.ofReal c * unitBallVolume n * ENNReal.ofReal (t ^ n)
      = ENNReal.ofReal (c * (unitBallVolume n).toReal * t ^ n) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hc0.le,
          ENNReal.ofReal_toReal hωtop]
    _ ≤ ENNReal.ofReal (μHE[n] (M ∩ closedBall x t)).toReal := ENNReal.ofReal_le_ofReal hreal
    _ = μHE[n] (M ∩ closedBall x t) := ENNReal.ofReal_toReal hH

## Key steps

1. Trivial for c ≤ 0; for 0 < c < 1 fix ε > 0 with c(1 + ε)ⁿ < 1 and put A = 1 + ε.
2. Hⁿ(Q ∩ B_1(0)) = ω_n, via the isometric inclusion of Q, μHE[n] = volume on Q, equal closed and open ball volumes, and an orthonormal-basis isometry Q ≅ Euclid n.
3. The cutoff ψ = max(0, min(1, (A − |y|)/ε)) lies in C_c with 1_{B_1} ≤ ψ ≤ 1_{B_A}, so ∫_Q ψ dHⁿ ≥ ω_n.
4. Approximate-tangent convergence gives ∫_{η_r(M)} ψ dHⁿ > cAⁿω_n for r ∈ (0, r₀).
5. Scaling: Hⁿ(η_r(M) ∩ B_A(0)) = r^{−n}Hⁿ(M ∩ B_{rA}(x)), so ∫_{η_r(M)} ψ dHⁿ ≤ r^{−n}Hⁿ(M ∩ B_{rA}(x)) when the latter is finite.
6. With r = t/A: cω_ntⁿ ≤ Hⁿ(M ∩ B_t(x)) for t ∈ (0, Ar₀), trivially when the right side is ∞.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json  (mode local-project; project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean  (both identical; HEAD b4d606d)`
- `rg -n '^def unitBallVolume|^structure IMRep|^def IMRep.measure' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean  (lines 143, 61, 88)`
- `rg -n 'dorag_dbs|dorag_standing' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project  (no match)`
- `rg -n 'theorem ae_tendsto_measure_inter_div|instance.*HasBesicovitchCovering|theorem ae_tendsto_rnDeriv' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/`
- `rg -n 'euclideanHausdorffMeasure_homothety_image|theorem EuclideanSpace.euclideanHausdorffMeasure_eq_volume|theorem Isometry.euclideanHausdorffMeasure_image' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean; rg -n 'theorem addHaar_closedBall_eq_addHaar_ball' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean; rg -n 'one_add_mul_le_pow' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order; rg -n 'theorem add_one_le_exp' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib`
- `grep -n 'def HasApproximateTangentSpaceAt' -A 25 /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean; sed -n 123,260p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean  (blowUpMap, regular_euclideanHausdorffMeasure_restrict_submodule, planeMeasure_eq)`
- `grep -rn 'simon_theorem_3_6|measure_toOuterMeasure_isBorelRegular|simonHausdorffMeasureReal_nat_eq_smul_euclideanHausdorffMeasure' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT; sed -n 300,420p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `sed -n 25,260p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean; sed -n 25,200p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/LowerDensityTangents.lean; sed -n 25,200p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/PositiveMultiplicityScale.lean  (proof patterns only)`
- `lean Avail.lean / Avail2.lean after import GMT.Ch07.Submission: #check Besicovitch.ae_tendsto_measure_inter_div (ok), Poincare.SimonGMT.Chapter01.simon_theorem_3_6 / Chapter04.planeMeasure_unit_closedBall / Chapter04.hausdorff_blowUp_image (unknown identifier), example : HasBesicovitchCovering (EuclideanSpace ℝ (Fin P)) := inferInstance (ok)`
- `python3: scan of dag.json for related lean_statements (HasApproximateTangentSpaceAt|unitBallVolume|withDensity|densit) and collision scan of the six dorag_dbs_* names over all 8 workspaces' dag.json (no collision); math-wiki page submission-regcomp-atl-upper-density-zero.md`
- `python3 -I: gmt-compare.py child_modules (contract mode) + lean_contract.validate_lean_statement on the six statements; lean on the six Challenge_*.lean (only the sorry warning)`
- `lean Integrated.lean (six complete child proofs + parent assembly, uncle as axiom; #print axioms)`
- `grep/sed in /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt (2.3–2.4, lines 266–288), chapter-03.txt (1.4–1.5, lines 77–96), chapter-01.txt (3.6–3.7 lines 700–711, 3.11–3.12 lines 773–854, 3.16 lines 905–925), chapter-04.txt (4.7–4.8, lines 536–546)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/Ring/Pow.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Complex/Exponential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaNormalization.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/LowerDensityTangents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/PositiveMultiplicityScale.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-498c875e36/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/math-wiki/submission-regcomp-atl-upper-density-zero.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`

The snapshot pins project b4d606d and Mathlib 25730c7c. Its GMT/Ch07/Contract.lean is byte-identical to the workspace contract and to GMT/Ch07/Submission.lean, the compiler context of every child type.

No declaration in the snapshot proves this node or any child; dorag_dbs_*/dorag_standing have no match.

What is importable after import GMT.Ch07.Submission (checked with lean):
- Not importable: the parent’s Step 5b library pointer simon_theorem_3_6 (Chapter01/DensityComparison.lean) and the SimonGMT Chapter04 tangent-density lemmas; these are used only as proof patterns.
- Importable: Mathlib’s Besicovitch.ae_tendsto_measure_inter_div (Covering/Besicovitch.lean:1105) with the HasBesicovitchCovering instance (BesicovitchVectorSpace.lean:499), euclideanHausdorffMeasure_homothety_image (Volume/Measure.lean:164), EuclideanSpace.euclideanHausdorffMeasure_eq_volume (:187), Isometry.euclideanHausdorffMeasure_image (:131), addHaar_closedBall_eq_addHaar_ball (EqHaar.lean:509), one_add_mul_le_pow (Ring/Pow.lean:99), add_one_le_exp (Complex/Exponential.lean:632), and SimonGMT Chapter03 regular_euclideanHausdorffMeasure_restrict_submodule. The children use these.

Related nodes in other branches:
- rsd_tendsto_closedBall_density_of_approxTangent (full limit, needs finiteness), rsd_ae_tendsto_withDensity_div_closedBall and rsd_imrep_compact_measure_ne_top are still decomposing, so they are not reusable.
- regcomp_atl_upper_density_zero is accepted, but no child needs it.
The six dorag_dbs_* names collide with nothing in any workspace DAG.

Lean checks:
- All six statements elaborate in comparator scope.
- Complete proofs of all six compile with only propext, Classical.choice and Quot.sound.
- The exact parent type compiles from them plus the sibling monotonicity type.
