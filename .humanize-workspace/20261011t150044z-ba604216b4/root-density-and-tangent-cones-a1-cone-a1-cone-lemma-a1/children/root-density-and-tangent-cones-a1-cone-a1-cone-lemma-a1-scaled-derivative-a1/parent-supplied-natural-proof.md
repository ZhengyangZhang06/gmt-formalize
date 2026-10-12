# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.cone-a1.cone_lemma-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.cone-a1.cone_lemma-a1.scaled_derivative-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Steps 0(a), 0(b), 2 and 3 of the parent proof (Simon Ch. 6, Lemma 2.33 via the homotopy formula 2.25–2.27, chapter-06.txt lines 441–478 and 557–567).
- Specialization: the identity parametrization c(s) = s on J = (0, ∞), i.e. β_s(y) = sⁿω(sy) = h_s^#ω for h_s(y) = sy. The parent's Remark records that any smooth positive parametrization works verbatim; here c' ≡ 1.
- Notation: M = R.carrier, θ = R.mult, ξ = R.orient, ν := Hⁿ⌞M = μHE[n].restrict M. Thus R.action φ = ∫ θ(y)·ξ(y)(φ(y)) dν(y) for every form φ.
- Dω(z) = fderiv ℝ ω z; norms on Covector (Euclid P) n and MultiVector P n are operator norms.

1. Orientation bound (parent 0(a)). By R.orients, for ν-a.e. y there is a subspace Q with IsUnitOrientationOf (ξ(y)) Q; by the sibling orientation_norm, ‖ξ(y)‖ ≤ 1. Hence for ν-a.e. y and every covector α: |ξ(y)(α)| ≤ ‖ξ(y)‖·‖α‖ ≤ ‖α‖.
2. Data from ω. ω ∈ TestFormOn univ n is C^∞ with compact support.
- ω and Dω are continuous.
- ω(z) = 0 and Dω(z) = 0 whenever z ∉ tsupport ω, since tsupport(Dω) ⊆ tsupport ω (Mathlib tsupport_fderiv_subset).
- Choose r ∈ ℝ with tsupport ω ⊆ B̄_r(0) (a compact set is bounded).
- Choose K₀ with ‖ω(z)‖ ≤ K₀ for all z (continuous with compact support); then K₀ ≥ ‖ω(0)‖ ≥ 0.
3. Integrands. For s ∈ ℝ and y ∈ ℝ^P put
- Φ(s, y) := n·s^{n−1}·ω(sy) + sⁿ·Dω(sy)[y],
- F(s, y) := θ(y)·ξ(y)(sⁿω(sy)),
- F'(s, y) := θ(y)·ξ(y)(Φ(s, y)).
Then G(s) = ∫ F(s, ·) dν, and the claimed derivative is ∫ F'(t, ·) dν = R.action(y ↦ Φ(t, y)).
4. Pointwise derivative (parent step 2 with c(s) = s). Fix y.
- s ↦ sy has derivative y.
- By the chain rule, s ↦ ω(sy) has derivative Dω(sy)[y] (ω is differentiable).
- s ↦ sⁿ has derivative n·s^{n−1} (Mathlib hasDerivAt_pow, coefficient (n : ℝ)·s^{n−1}).
- By the product rule, s ↦ sⁿω(sy) has derivative sⁿ·Dω(sy)[y] + n·s^{n−1}·ω(sy) = Φ(s, y).
Composing with the continuous linear functional ξ(y) and multiplying by the constant θ(y), s ↦ F(s, y) has derivative F'(s, y) at every s, for every y.
5. Measurability.
- θ is measurable (R.measurable_mult composed with ℕ → ℝ), and ξ is AEStronglyMeasurable for ν (R.aestronglyMeasurable_orient).
- (s, y) ↦ Φ(s, y) is jointly continuous: ω, Dω, the evaluation (A, u) ↦ A u, scalar multiplication and powers are continuous. Also y ↦ sⁿω(sy) is continuous.
- The evaluation (ζ, α) ↦ ζ(α) is continuous on MultiVector P n × Covector (Euclid P) n, so y ↦ ξ(y)(φ(y)) is AEStronglyMeasurable for every continuous φ.
- Multiplying by θ(y), F(s, ·) (each s) and F'(t, ·) are AEStronglyMeasurable for ν.
6. Localization. Let I := (t/2, 2t), an open neighbourhood of t, ρ := 2r/t and B := B̄_ρ(0) (compact, measurable).
- If s ∈ I and sy ∈ tsupport ω, then s‖y‖ = ‖sy‖ ≤ r, so r ≥ 0 and ‖y‖ ≤ r/s ≤ 2r/t = ρ, i.e. y ∈ B.
- If sy ∉ tsupport ω, then ω(sy) = 0 and Dω(sy) = 0 by step 2, so sⁿω(sy) = 0, Φ(s, y) = 0 and F(s, y) = F'(s, y) = 0.
7. Uniform bound (parent step 3). Φ is continuous on the compact set [t/2, 2t] × B, so there is K with ‖Φ(s, y)‖ ≤ K for (s, y) ∈ [t/2, 2t] × B. One may take the parent's explicit constant K = n(2t)^{n−1}K₀ + (2t)ⁿ·sup‖Dω‖·ρ (i.e. M₀ = 2t, m₀ = t/2, |c'| = 1).
Let g(y) := K·θ(y)·1_B(y). For ν-a.e. y (those of step 1) and every s ∈ I:
- if sy ∈ tsupport ω, then y ∈ B by step 6 and |F'(s, y)| ≤ θ(y)·‖ξ(y)‖·‖Φ(s, y)‖ ≤ θ(y)·1·K = g(y);
- otherwise F'(s, y) = 0 ≤ g(y): g(y) = 0 if y ∉ B, and if y ∈ B then K ≥ ‖Φ(t, y)‖ ≥ 0 since (t, y) ∈ [t/2, 2t] × B.
8. Integrability (parent 0(b)).
- B is compact and B ⊆ univ, so R.locallyIntegrable_mult gives ∫_{M∩B} θ dHⁿ < ∞. As θ is measurable, θ·1_B is ν-integrable, hence so is g.
- By step 6 with s = t ∈ I and step 1, |F(t, y)| ≤ tⁿK₀·θ(y)·1_B(y) for ν-a.e. y. Indeed, if ty ∈ tsupport ω then y ∈ B and |F(t, y)| ≤ θ(y)·‖tⁿω(ty)‖ ≤ tⁿK₀θ(y); otherwise F(t, y) = 0 and the right side is ≥ 0. So F(t, ·) is ν-integrable.
9. Conclusion. The dominated differentiation theorem (Mathlib hasDerivAt_integral_of_dominated_loc_of_deriv_le) applies with the neighbourhood I of t:
- F(s, ·) is AEStronglyMeasurable for s near t (step 5);
- F(t, ·) is integrable (step 8);
- F'(t, ·) is AEStronglyMeasurable (step 5);
- |F'(s, y)| ≤ g(y) for ν-a.e. y and all s ∈ I, with g integrable (steps 7–8);
- s ↦ F(s, y) has derivative F'(s, y) on I for every y (step 4).
Hence G(s) = ∫ F(s, ·) dν has derivative ∫ F'(t, ·) dν = R.action(y ↦ n·t^{n−1}·ω(ty) + tⁿ·Dω(ty)[y]) at t. ∎

Implementation note (not part of the numbered proof).
- The Lean proof below of exactly this frozen type was kernel-checked during this decomposition: Lean v4.35.0-rc3, Mathlib 25730c7c, after `import GMT.Ch07.Submission`, placed inside `namespace GMT.Ch07` with the contract's opens, like the accepted Submission theorems. #print axioms gives propext, Classical.choice, Quot.sound.
- Do not put `open scoped ContDiff` in front of this declaration: that scope makes `ω` a reserved token and breaks the binder `ω`.
- Write the smoothness order as `(⊤ : ℕ∞)` instead of `∞`: with `open scoped ENNReal`, `∞` is the ENNReal top.
- Bound the jointly continuous map Φ on the compact set as in step 7. `Continuous.bounded_above_of_compact_support` applied to the CLM-valued `fderiv ℝ ω` hits a deterministic whnf timeout (operator-norm instance unification); the covector-valued Φ is fine.
- The sibling `orientation_norm` is `Submission.unit_orientation_norm_le_one`.
theorem Submission.dtc_cwv_scaled_action_hasDerivAt : ∀ (P n : ℕ) (R : IMRep (univ : Set (Euclid P)) n) (ω : TestFormOn (univ : Set (Euclid P)) n) (t : ℝ), 0 < t → HasDerivAt (fun s : ℝ => R.action (fun y => (s ^ n) • (ω : DifferentialForm (Euclid P) n) (s • y))) (R.action (fun y => ((n : ℝ) * t ^ (n - 1)) • (ω : DifferentialForm (Euclid P) n) (t • y) + (t ^ n) • fderiv ℝ (ω : DifferentialForm (Euclid P) n) (t • y) y)) t := by
  intro P n R ω t ht
  have hws : ContDiff ℝ (⊤ : ℕ∞) (ω : DifferentialForm (Euclid P) n) := ω.property.1.1
  have hwc : HasCompactSupport (ω : DifferentialForm (Euclid P) n) := ω.property.1.2
  set w : DifferentialForm (Euclid P) n := (ω : DifferentialForm (Euclid P) n) with hw_def
  -- Step 1: ‖ξ(x)‖ ≤ 1 for Hⁿ⌞M-a.e. x (sibling `orientation_norm`).
  have hξ : ∀ᵐ x ∂(μHE[n].restrict R.carrier), ‖R.orient x‖ ≤ 1 := by
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    exact Submission.unit_orientation_norm_le_one P n Q _ hQ
  -- Step 2: a support radius, a bound for ω; ω and Dω vanish off spt ω.
  have hwcont : Continuous w := hws.continuous
  have hDw : Continuous (fderiv ℝ w) := hws.continuous_fderiv (by simp)
  obtain ⟨K0, hK0⟩ := hwcont.bounded_above_of_compact_support hwc
  obtain ⟨r, hr⟩ : ∃ r, tsupport w ⊆ closedBall (0 : Euclid P) r :=
    hwc.isCompact.isBounded.subset_closedBall 0
  have hvan : ∀ z, z ∉ tsupport w → w z = 0 ∧ fderiv ℝ w z = 0 := fun z hz =>
    ⟨image_eq_zero_of_notMem_tsupport hz,
      image_eq_zero_of_notMem_tsupport (fun h => hz (tsupport_fderiv_subset ℝ h))⟩
  -- Step 5: measurability of the integrands (Φ jointly continuous).
  have hθm : Measurable fun x => (R.mult x : ℝ) := measurable_from_nat.comp R.measurable_mult
  have happly : Continuous fun p : MultiVector P n × Covector (Euclid P) n => p.1 p.2 :=
    continuous_fst.clm_apply continuous_snd
  have hmeas : ∀ φ : Euclid P → Covector (Euclid P) n, Continuous φ →
      AEStronglyMeasurable (fun y => (R.mult y : ℝ) * R.orient y (φ y)) (μHE[n].restrict R.carrier) :=
    fun φ hφ => hθm.aestronglyMeasurable.mul
      (happly.comp_aestronglyMeasurable (R.aestronglyMeasurable_orient.prodMk hφ.aestronglyMeasurable))
  have hcF : ∀ s : ℝ, Continuous (fun y => (s ^ n) • w (s • y)) := by
    intro s
    have h1 : Continuous (fun y : Euclid P => w (s • y)) := hwcont.comp (continuous_const_smul s)
    exact h1.const_smul (s ^ n)
  have hΦ : Continuous (fun p : ℝ × Euclid P => ((n : ℝ) * p.1 ^ (n - 1)) • w (p.1 • p.2) +
      (p.1 ^ n) • fderiv ℝ w (p.1 • p.2) p.2) := by
    have hsy : Continuous (fun p : ℝ × Euclid P => p.1 • p.2) := continuous_fst.smul continuous_snd
    exact (((continuous_const.mul (continuous_fst.pow _))).smul (hwcont.comp hsy)).add
      ((continuous_fst.pow _).smul ((hDw.comp hsy).clm_apply continuous_snd))
  have hcF' : ∀ s : ℝ, Continuous (fun y => ((n : ℝ) * s ^ (n - 1)) • w (s • y) +
      (s ^ n) • fderiv ℝ w (s • y) y) := fun s =>
    hΦ.comp (continuous_const.prodMk continuous_id)
  -- Steps 6–8: localization in B = B̄_ρ(0), the bound K for Φ on [t/2, 2t] × B, integrability.
  set ρ : ℝ := 2 * r / t with hρ
  set B : Set (Euclid P) := closedBall (0 : Euclid P) ρ with hB
  have hBm : MeasurableSet B := measurableSet_closedBall
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := t / 2) (b := 2 * t)).prod (isCompact_closedBall (0 : Euclid P) ρ)
    |>.exists_bound_of_continuousOn hΦ.continuousOn
  have hθB : IntegrableOn (fun x => (R.mult x : ℝ)) B (μHE[n].restrict R.carrier) := by
    refine ⟨hθm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, Measure.restrict_restrict hBm, inter_comm]
    simpa only [Real.enorm_natCast] using
      (R.locallyIntegrable_mult B (isCompact_closedBall 0 ρ) (subset_univ _)).lt_top
  -- membership: if s • y ∈ spt ω with s > t/2 then y ∈ B
  have hmemB : ∀ s : ℝ, t / 2 < s → ∀ y : Euclid P, s • y ∈ tsupport w → y ∈ B := by
    intro s hs y hy
    have h1 : ‖s • y‖ ≤ r := by simpa using hr hy
    have hs0 : 0 < s := by linarith
    rw [norm_smul, Real.norm_of_nonneg hs0.le] at h1
    simp only [hB, mem_closedBall, dist_zero_right, hρ]
    rw [le_div_iff₀ ht]
    nlinarith [norm_nonneg y]
  -- Steps 7–9: hypotheses of the dominated differentiation theorem (step 4 is `h_diff`).
  have hs : Ioo (t / 2) (2 * t) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  have hF_meas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable
      (fun y => (R.mult y : ℝ) * R.orient y ((s ^ n) • w (s • y))) (μHE[n].restrict R.carrier) :=
    Eventually.of_forall fun s => hmeas _ (hcF s)
  have hF'_meas : AEStronglyMeasurable (fun y => (R.mult y : ℝ) * R.orient y
      (((n : ℝ) * t ^ (n - 1)) • w (t • y) + (t ^ n) • fderiv ℝ w (t • y) y))
      (μHE[n].restrict R.carrier) := hmeas _ (hcF' t)
  have hF_int : Integrable (fun y => (R.mult y : ℝ) * R.orient y ((t ^ n) • w (t • y)))
      (μHE[n].restrict R.carrier) := by
    refine ((hθB.integrable_indicator hBm).const_mul (t ^ n * K0)).mono' (hmeas _ (hcF t)) ?_
    filter_upwards [hξ] with y hy
    by_cases hty : t • y ∈ tsupport w
    · have hyB := hmemB t (by linarith) y hty
      rw [indicator_of_mem hyB, norm_mul, Real.norm_natCast]
      calc (R.mult y : ℝ) * ‖R.orient y ((t ^ n) • w (t • y))‖
          ≤ (R.mult y : ℝ) * (‖R.orient y‖ * ‖(t ^ n) • w (t • y)‖) := by
            gcongr; exact (R.orient y).le_opNorm _
        _ ≤ (R.mult y : ℝ) * (1 * (t ^ n * K0)) := by
            gcongr
            rw [norm_smul, Real.norm_of_nonneg (by positivity)]
            gcongr
            exact hK0 _
        _ = t ^ n * K0 * (R.mult y : ℝ) := by ring
    · rw [(hvan _ hty).1, smul_zero, map_zero, mul_zero, norm_zero]
      have hK0n : 0 ≤ K0 := le_trans (norm_nonneg _) (hK0 0)
      by_cases hyB : y ∈ B
      · rw [indicator_of_mem hyB]; positivity
      · rw [indicator_of_notMem hyB, mul_zero]
  have h_bound : ∀ᵐ y ∂(μHE[n].restrict R.carrier), ∀ s ∈ Ioo (t / 2) (2 * t),
      ‖(R.mult y : ℝ) * R.orient y (((n : ℝ) * s ^ (n - 1)) • w (s • y) +
        (s ^ n) • fderiv ℝ w (s • y) y)‖ ≤ K * B.indicator (fun x => (R.mult x : ℝ)) y := by
    filter_upwards [hξ] with y hy s hs
    obtain ⟨hs1, hs2⟩ := hs
    by_cases hsy : s • y ∈ tsupport w
    · have hyB := hmemB s hs1 y hsy
      rw [indicator_of_mem hyB, norm_mul, Real.norm_natCast]
      have hnorm := hK (s, y) ⟨⟨hs1.le, hs2.le⟩, hyB⟩
      calc (R.mult y : ℝ) * ‖R.orient y (((n : ℝ) * s ^ (n - 1)) • w (s • y) +
            (s ^ n) • fderiv ℝ w (s • y) y)‖
          ≤ (R.mult y : ℝ) * (‖R.orient y‖ * ‖((n : ℝ) * s ^ (n - 1)) • w (s • y) +
            (s ^ n) • fderiv ℝ w (s • y) y‖) := by
            gcongr; exact (R.orient y).le_opNorm _
        _ ≤ (R.mult y : ℝ) * (1 * K) := by gcongr
        _ = K * (R.mult y : ℝ) := by ring
    · rw [(hvan _ hsy).1, (hvan _ hsy).2, smul_zero, zero_apply, smul_zero,
        add_zero, map_zero, mul_zero, norm_zero]
      by_cases hyB : y ∈ B
      · rw [indicator_of_mem hyB]
        have hKn : 0 ≤ K := le_trans (norm_nonneg _)
          (hK (t, y) ⟨⟨by linarith, by linarith⟩, hyB⟩)
        positivity
      · rw [indicator_of_notMem hyB, mul_zero]
  have h_diff : ∀ᵐ y ∂(μHE[n].restrict R.carrier), ∀ s ∈ Ioo (t / 2) (2 * t),
      HasDerivAt (fun s => (R.mult y : ℝ) * R.orient y ((s ^ n) • w (s • y)))
        ((R.mult y : ℝ) * R.orient y (((n : ℝ) * s ^ (n - 1)) • w (s • y) +
          (s ^ n) • fderiv ℝ w (s • y) y)) s := by
    refine Eventually.of_forall fun y s _ => ?_
    have h1 : HasDerivAt (fun s : ℝ => s • y) y s := by
      simpa using (hasDerivAt_id s).smul_const y
    have h2 : HasDerivAt (fun s : ℝ => w (s • y)) (fderiv ℝ w (s • y) y) s :=
      ((hws.differentiable (by simp)).differentiableAt (x := s • y)).hasFDerivAt.comp_hasDerivAt s h1
    have h3 : HasDerivAt (fun s : ℝ => (s ^ n) • w (s • y))
        ((s ^ n) • fderiv ℝ w (s • y) y + ((n : ℝ) * s ^ (n - 1)) • w (s • y)) s :=
      (hasDerivAt_pow n s).smul h2
    have h4 := ((R.orient y).hasFDerivAt.comp_hasDerivAt s h3).const_mul (R.mult y : ℝ)
    rw [add_comm] at h4
    exact h4
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hF_meas hF_int hF'_meas h_bound
    ((hθB.integrable_indicator hBm).const_mul K) h_diff
  exact key.2

## Key steps

1. ‖ξ(y)‖ ≤ 1 for Hⁿ⌞M-a.e. y (orientation_norm via R.orients).
2. For every y, s ↦ θ(y)ξ(y)(sⁿω(sy)) has derivative θ(y)ξ(y)(n s^{n−1}ω(sy) + sⁿDω(sy)[y]) (product and chain rules).
3. For s ∈ (t/2, 2t) the integrands vanish unless y ∈ B̄_{2r/t}(0) (tsupport ω ⊆ B̄_r(0)), and are bounded by Kθ(y)1_B(y) with K the maximum of the continuous Φ on [t/2, 2t] × B.
4. θ1_B is integrable by locallyIntegrable_mult; the integrands are AEStronglyMeasurable.
5. hasDerivAt_integral_of_dominated_loc_of_deriv_le gives G'(t) = R.action(n t^{n−1}ω(t·) + tⁿDω(t·)[·]).

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical); cmp … GMT/Ch07/Submission.lean (identical); cat local-references/123e8435b4a2469b/manifest.json (project b4d606db, mathlib 25730c7c); git -C lake-packages-25730c7c/simongmt rev-parse HEAD (2b366308)`
- `cat simongmt/Poincare/SimonGMT/Chapter06/Forms.lean and Chapter06/AffineCurrentPushforward.lean; sed -n 1,260p Chapter06/Currents.lean; grep -n boundary Chapter06/Currents.lean; sed -n 1,80p Chapter06/CurrentLocalEquality.lean (IsTestForm, TestFormOn, exteriorDerivative_isTestForm, exteriorDerivativeTestOn, GeometricCurrentOn.boundary_apply, affinePullbackForm, affinePullbackTestOn, affinePushforward_apply, restrictDomain_apply, testFormOnInclusion)`
- `rg -n 'theorem hasDerivAt_integral_of_dominated_loc_of_deriv_le' Mathlib/Analysis/Calculus/ParametricIntegral.lean; rg -n 'is_const_of_deriv' Mathlib/Analysis/Calculus/MeanValue.lean; rg -n 'HasCompactSupport.comp_smul' Mathlib/Topology/Algebra/ConstMulAction.lean; rg -n 'ae_withDensity_iff' Mathlib/MeasureTheory/Measure/WithDensity.lean; rg -n 'bounded_above_of_compact_support' Mathlib/Analysis/Normed/Group/Bounded.lean; rg -n 'aestronglyMeasurable_comp₂|apply_continuousLinearMap' Mathlib/MeasureTheory; rg -n 'integrable_indicator_iff|Integrable.mono' Mathlib/MeasureTheory`
- `python3 census of lean_name/lean_statement in dag.json and nodes/*/decomposition-v*.json (patterns IsConeCurrent, R.action with HasDerivAt, curryLeft (β z) z, ‖R.orient x‖, IsUnitOrientationOf with ≤); rg -l -F for each of the five new names in dag.json, nodes, GMT, the project snapshot and simongmt/Poincare (0 hits)`
- `git show 52115c22:GMT/Ch07/Submission.lean (Submission.cone_current_apply_dilation_pullback); git show 77ba6718 (Submission.dtc_cone_euler_cartan); git show f1339f96 (Submission.regcomp_rim_action_integrable); git log/show d90c7c52 (implementation base merging a reused cross-branch child)`
- `sed -n 430,480p and 540,580p book/chapter-06.txt (2.25–2.27, Lemma 2.33); sed -n 340,365p book/chapter-07.txt (7.3.1 proof, 'apply Lemma 2.33 to deduce that C is a cone')`
- `grep -n '_existing_lean_name_problem|_solve_children|_install_parent_supplied_child_handoff|_accepted_checkpoint' /runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/runtime.py; store.py ensure; .humanize/swarm-configs/be41fd7aece94f7eb83ed6e064a802a0.json (max_nodes 1000); dag.json node count 417`
- `python3 -I /tmp/conelemma-scripts/gen.py (gmt-compare.child_modules mode=contract, lean_contract.validate_lean_statement) then lake env lean gen/Ch_*.lean; lake env lean Assembly.lean, Trial1.lean, Trial2.lean, Trial3.lean, final/Final.lean, final/FinalSol.lean, final/FromJson.lean, each with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1-cone-lemma-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1-cone-lemma-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1-euler-cartan-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1-euler-cartan-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1-euler-cartan-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-imrep-measure-unique-a1-orie-c3a822a8f5/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-imrep-measure-unique-a1-orie-c3a822a8f5/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-imrep-measure-unique-a1-orie-c3a822a8f5/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-one-dim-cones-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1-tangent-projection-measurable-a1/parent-implementation-base.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-im-sub-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-mass-eq-measure-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/ConstMulAction.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/store.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/swarm-configs/be41fd7aece94f7eb83ed6e064a802a0.json`
- `/tmp/conelemma-decomp/children.json`
- `/tmp/conelemma-decomp/Assembly.lean`
- `/tmp/conelemma-decomp/Trial1.lean`
- `/tmp/conelemma-decomp/Trial2.lean`
- `/tmp/conelemma-decomp/Trial3.lean`
- `/tmp/conelemma-decomp/final/Final.lean`
- `/tmp/conelemma-decomp/final/FinalSol.lean`
- `/tmp/conelemma-decomp/final/FromJson.lean`
- `/tmp/conelemma-scripts/gen.py`
- `/tmp/conelemma-scripts/build.py`

The snapshot contract (project b4d606d, Mathlib 25730c7c, simongmt 2b36630) is byte-identical to the workspace Contract.lean and Submission.lean. All seven child types therefore elaborate after `import GMT.Ch07.Submission` in the comparator's contract scope (namespace GMT.Ch07 with the contract's opens).

SimonGMT supplies what the children need about forms and currents:
- IsTestForm, TestFormOn, exteriorDerivative_isTestForm and exteriorDerivativeTestOn;
- GeometricCurrentOn.boundary_apply (C.boundary ψ = C(dψ));
- affinePullbackForm, affinePullbackTestOn, affinePushforward_apply and restrictDomain_apply, which make η_{0,λ#}C(ω) = C(ω(λ⁻¹·)∘λ⁻¹) definitional.

The Mathlib snapshot supplies hasDerivAt_integral_of_dominated_loc_of_deriv_le, IsOpen.is_const_of_deriv_eq_zero, HasCompactSupport.comp_smul/fderiv/mono, ae_withDensity_iff, ContinuousAlternatingMap.curryLeftLI/map_smul_univ and ContDiff.clm_apply/fderiv_right. Mathlib has no Lie-derivative or Cartan API; the Euler-field Cartan identity is the accepted Submission.dtc_cone_euler_cartan.

Reuse:
- Submission.unit_orientation_norm_le_one (commit 0325970d) and Submission.dtc_cone_euler_cartan (commit 77ba6718) passed their isolated comparators and have byte-identical frozen types.
- runtime.py maps accepted names with identical types to the existing nodes and skips their handoffs, and implementation bases merge reused commits (d90c7c52).
- The five new dtc_cwv_* names occur nowhere in the run, the project or SimonGMT.
- dag.json has 417 nodes against max_nodes 1000.

Lean checks:
- Kernel-checked proofs of all five new children, the accepted proofs of the two reused declarations and the 8-line parent assembly compile together with axioms propext, Classical.choice and Quot.sound only.
- The comparator solution side `exact Submission.X` elaborates against every frozen type.
- The code embedded in the natural proofs was re-extracted from the final JSON and recompiled.

Pitfalls found:
- `open scoped ContDiff` makes ω a token;
- Continuous.bounded_above_of_compact_support on the CLM-valued fderiv times out.
