# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.bv_estimate-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.bv_estimate-a1.smooth_ae_approx-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 2–3 of the parent proof (mollify the bounded function g₀ by rescaled normalized smooth bumps ψ_ϑ; the mollifications are smooth, bounded by ∫ψ_ϑ = 1, supported in a slightly larger ball, and converge to g₀ at Lebesgue points), for an arbitrary measurable g₀ with |g₀| ≤ 1 vanishing off B_R(0), with the explicit radii θ_j := δ/(j + 2). No assumption on n is needed (n = 0 included).
0. (Integrability of g₀.) If x ∉ B_R(0) then ‖x‖ ≥ R, so g₀(x) = 0. On B_R(0), a set of finite measure, g₀ is measurable and bounded by 1, hence integrable (Measure.integrableOn_of_bounded); its support lies in B_R(0), so g₀ is integrable on ℝⁿ (integrableOn_iff_integrable_of_support_subset), in particular locally integrable.
1. (A normalized bump.) Let b be the ContDiffBump centred at 0 with rIn = 1/4 and rOut = 1/2 (ℝⁿ is finite-dimensional, so Mathlib provides HasContDiffBump). Then b is C^∞, 0 ≤ b ≤ 1, support b = B_{1/2}(0), and b has compact support, hence is integrable. I := ∫ b > 0 by integral_pos_iff_support_of_nonneg, because support b is a nonempty open ball, which has positive measure (measure_ball_pos). Put ρ := b/I. Then ρ is C^∞, 0 ≤ ρ ≤ 1/I, ρ(x) = 0 whenever ‖x‖ ≥ 1/2, and ∫ρ = I/I = 1.
2. (Rescaled mollifiers.) For ε > 0 put ψ_ε(x) := (εⁿ)⁻¹·ρ(ε⁻¹x). Then ψ_ε is C^∞ (a constant times ρ composed with the linear map x ↦ ε⁻¹x); ψ_ε ≥ 0; ψ_ε(x) = 0 whenever ‖x‖ ≥ ε/2 (then ‖ε⁻¹x‖ = ε⁻¹‖x‖ ≥ 1/2); |ψ_ε(x)| ≤ (1/I)/εⁿ; ψ_ε has compact support (it vanishes outside closedBall(0, ε)); and ∫ψ_ε = (εⁿ)⁻¹·εⁿ·∫ρ = 1 by the scaling law ∫ f(ε⁻¹x) dx = ε^{dim ℝⁿ}·∫f (Measure.integral_comp_inv_smul_of_nonneg) with dim ℝⁿ = n (finrank_euclideanSpace_fin). In particular ψ_ε is integrable and ∫ ψ_ε(x − y) dy = ∫ψ_ε = 1 for every x (integral_sub_left_eq_self).
3. (The sequence.) θ_j := δ/(j + 2) satisfies 0 < θ_j < δ (as j + 2 ≥ 2 > 1) and θ_j → 0. Define G_j := g₀ ⋆ ψ_{θ_j}, the convolution with respect to the bilinear map ContinuousLinearMap.lsmul ℝ ℝ and Lebesgue measure, so that G_j(x) = ∫ g₀(y)·ψ_{θ_j}(x − y) dy (convolution_def).
4. (Smoothness.) ψ_{θ_j} is C^∞ with compact support and g₀ is locally integrable, so G_j is C^∞ (HasCompactSupport.contDiff_convolution_right).
5. (Support.) Let ‖x‖ ≥ R + θ_j/2. For each y, either ‖y‖ ≥ R, so g₀(y) = 0, or ‖y‖ < R, so ‖x − y‖ ≥ ‖x‖ − ‖y‖ > θ_j/2 and ψ_{θ_j}(x − y) = 0. Thus the integrand vanishes identically and G_j(x) = 0. Hence support G_j ⊆ closedBall(0, R + θ_j/2), which is compact, so G_j has compact support; and since this closed ball is closed, tsupport G_j ⊆ closedBall(0, R + θ_j/2) ⊆ B_{R+δ}(0) because θ_j/2 < δ.
6. (Uniform bound.) |G_j(x)| ≤ ∫ |g₀(y)·ψ_{θ_j}(x − y)| dy ≤ ∫ ψ_{θ_j}(x − y) dy = 1, using |g₀| ≤ 1, ψ_{θ_j} ≥ 0, integrability of y ↦ ψ_{θ_j}(x − y) (Integrable.comp_sub_left) and step 2.
7. (Convergence at Lebesgue points.) Lebesgue measure on ℝⁿ is uniformly locally doubling (Mathlib instance for additive Haar measures on finite-dimensional spaces). By the Lebesgue differentiation theorem in the form IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub (for the locally integrable g₀, with K = 1), for a.e. x: for every sequence of radii r_j → 0 through positive values and centres c_j with x ∈ closedBall(c_j, r_j), the averages ⨍_{closedBall(c_j, r_j)} |g₀(y) − g₀(x)| dy tend to 0. Fix such an x and use c_j := x, r_j := θ_j. Apply the approximate-identity lemma tendsto_integral_smul_of_tendsto_average_norm_sub with sets a_j := closedBall(x, θ_j), kernels k_j(y) := ψ_{θ_j}(x − y) and constant K₀ := (1/I)·|closedBall(0, 1)|, checking its hypotheses for every j:
   (a) ⨍_{a_j} |g₀ − g₀(x)| → 0 (just shown);
   (b) g₀ is integrable on a_j;
   (c) ∫ k_j = 1 (step 2), so ∫ k_j → 1;
   (d) support k_j ⊆ a_j, because k_j(y) ≠ 0 forces ‖x − y‖ < θ_j/2 ≤ θ_j;
   (e) |k_j(y)| ≤ (1/I)/θ_jⁿ = K₀/|closedBall(x, θ_j)|, because |closedBall(x, r)| = rⁿ·|closedBall(0, 1)| for r ≥ 0 (Measure.addHaar_real_closedBall' with dim ℝⁿ = n) and 0 < |closedBall(0, 1)| < ∞.
   The lemma gives ∫ k_j(y)·g₀(y) dy → g₀(x), i.e. G_j(x) → g₀(x). As this holds for a.e. x, the sequence (G_j) has all the required properties. ∎

Verified Lean realization (supplementary; compiled with `lake env lean` inside a copy of GMT/Ch07/Submission.lean at project b4d606db / Mathlib 25730c7c, inserted before `main_theorem`; no new warnings; axioms propext, Classical.choice, Quot.sound). It may be appended verbatim as the single leaf theorem:
```lean
theorem Submission.cbr_ci_pw_bv_smooth_ae_approx : ∀ (n : ℕ) (R δ : ℝ) (g₀ : Euclid n → ℝ), 0 < δ → Measurable g₀ → (∀ x, |g₀ x| ≤ 1) → (∀ x, R ≤ ‖x‖ → g₀ x = 0) → ∃ G : ℕ → Euclid n → ℝ, (∀ j, ContDiff ℝ (⊤ : ℕ∞) (G j)) ∧ (∀ j, HasCompactSupport (G j)) ∧ (∀ j, tsupport (G j) ⊆ ball 0 (R + δ)) ∧ (∀ j x, |G j x| ≤ 1) ∧ ∀ᵐ x ∂(volume : Measure (Euclid n)), Tendsto (fun j => G j x) atTop (𝓝 (g₀ x)) := by
  intro n R δ g₀ hδ hg₀m hg₀b hg₀z
  -- Step 0: g₀ is integrable
  have hg₀out : ∀ x, x ∉ ball (0 : Euclid n) R → g₀ x = 0 := fun x hx =>
    hg₀z x (by simpa [mem_ball_zero_iff] using hx)
  have hg₀i : Integrable g₀ := by
    have hon : IntegrableOn g₀ (ball (0 : Euclid n) R) :=
      Measure.integrableOn_of_bounded (M := 1) measure_ball_lt_top.ne hg₀m.aestronglyMeasurable
        (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hg₀b x)
    exact (integrableOn_iff_integrable_of_support_subset
      (fun x hx => by by_contra h; exact hx (hg₀out x h))).1 hon
  -- Step 1: a normalized bump
  let b : ContDiffBump (0 : Euclid n) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  have hbi : Integrable (b : Euclid n → ℝ) := b.continuous.integrable_of_hasCompactSupport b.hasCompactSupport
  set I : ℝ := ∫ x, b x with hIdef
  have hI : 0 < I := by
    rw [hIdef, integral_pos_iff_support_of_nonneg (fun x => b.nonneg) hbi, b.support_eq]
    exact measure_ball_pos _ _ (by norm_num)
  set ρ : Euclid n → ℝ := fun x => b x / I with hρdef
  have hρc : ContDiff ℝ (⊤ : ℕ∞) ρ := b.contDiff.div_const I
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => div_nonneg b.nonneg hI.le
  have hρb : ∀ x, ρ x ≤ 1 / I := fun x => div_le_div_of_nonneg_right b.le_one hI.le
  have hρz : ∀ x, (1 / 2 : ℝ) ≤ ‖x‖ → ρ x = 0 := by
    intro x hx
    have : x ∉ support (b : Euclid n → ℝ) := by
      rw [b.support_eq, mem_ball_zero_iff]; exact not_lt.2 hx
    simp [hρdef, notMem_support.1 this]
  have hρ1 : ∫ x, ρ x = 1 := by
    simp only [hρdef]; rw [integral_div, ← hIdef, div_self hI.ne']
  -- Step 2: rescaled mollifiers
  set ψ : ℝ → Euclid n → ℝ := fun ε x => (ε ^ n)⁻¹ * ρ (ε⁻¹ • x) with hψdef
  have hψc : ∀ ε, ContDiff ℝ (⊤ : ℕ∞) (ψ ε) := fun ε =>
    contDiff_const.mul (hρc.comp (contDiff_const_smul ε⁻¹))
  have hψ0 : ∀ ε, 0 < ε → ∀ x, 0 ≤ ψ ε x := fun ε hε x =>
    mul_nonneg (inv_nonneg.2 (pow_nonneg hε.le n)) (hρ0 _)
  have hψz : ∀ ε, 0 < ε → ∀ x, ε / 2 ≤ ‖x‖ → ψ ε x = 0 := by
    intro ε hε x hx
    have : (1 / 2 : ℝ) ≤ ‖ε⁻¹ • x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hε]
      rw [le_inv_mul_iff₀ hε]; linarith
    simp [hψdef, hρz _ this]
  have hψb : ∀ ε, 0 < ε → ∀ x, |ψ ε x| ≤ (1 / I) / ε ^ n := by
    intro ε hε x
    rw [abs_of_nonneg (hψ0 ε hε x), hψdef]
    simp only
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (hρb _) (inv_nonneg.2 (pow_nonneg hε.le n))
  have hψ1 : ∀ ε, 0 < ε → ∫ x, ψ ε x = 1 := by
    intro ε hε
    simp only [hψdef]
    rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg _ _ hε.le,
      finrank_euclideanSpace_fin, hρ1, smul_eq_mul, mul_one, inv_mul_cancel₀ (pow_ne_zero n hε.ne')]
  have hψcs : ∀ ε, 0 < ε → HasCompactSupport (ψ ε) := by
    intro ε hε
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid n) ε) fun x hx => ?_
    rw [mem_closedBall_zero_iff, not_le] at hx
    exact hψz ε hε x (by linarith)
  -- Step 3: the sequence
  set θ : ℕ → ℝ := fun j => δ / ((j : ℝ) + 2) with hθdef
  have hθpos : ∀ j, 0 < θ j := fun j => div_pos hδ (by positivity)
  have hθlt : ∀ j, θ j < δ := fun j => by
    rw [hθdef]; simp only
    rw [div_lt_iff₀ (by positivity)]; nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hG : ∀ j x, convolution g₀ (ψ (θ j)) (ContinuousLinearMap.lsmul ℝ ℝ) volume x
      = ∫ y, g₀ y * ψ (θ j) (x - y) := by
    intro j x
    rw [convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hvan : ∀ j x, R + θ j / 2 ≤ ‖x‖ →
      convolution g₀ (ψ (θ j)) (ContinuousLinearMap.lsmul ℝ ℝ) volume x = 0 := by
    intro j x hx
    rw [hG]
    have : (fun y => g₀ y * ψ (θ j) (x - y)) = fun _ => 0 := by
      funext y
      by_cases hy : R ≤ ‖y‖
      · rw [hg₀z y hy, zero_mul]
      · push Not at hy
        have h1 : θ j / 2 ≤ ‖x - y‖ := by
          have := norm_sub_norm_le x y
          linarith
        rw [hψz (θ j) (hθpos j) _ h1, mul_zero]
    rw [this, integral_zero]
  have hsupp : ∀ j, support (convolution g₀ (ψ (θ j)) (ContinuousLinearMap.lsmul ℝ ℝ) volume)
      ⊆ closedBall 0 (R + θ j / 2) := by
    intro j x hx
    rw [mem_closedBall_zero_iff]
    by_contra h
    exact hx (hvan j x (not_le.1 h).le)
  refine ⟨fun j => convolution g₀ (ψ (θ j)) (ContinuousLinearMap.lsmul ℝ ℝ) volume, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact (hψcs (θ j) (hθpos j)).contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
      hg₀i.locallyIntegrable (hψc (θ j))
  · intro j
    exact HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall _ _) (hsupp j)
  · intro j
    refine (closure_minimal (hsupp j) isClosed_closedBall).trans (closedBall_subset_ball ?_)
    linarith [hθlt j, hθpos j]
  · intro j x
    simp only
    rw [hG]
    have hψi : Integrable (ψ (θ j)) :=
      (hψc (θ j)).continuous.integrable_of_hasCompactSupport (hψcs (θ j) (hθpos j))
    calc |∫ y, g₀ y * ψ (θ j) (x - y)| ≤ ∫ y, |g₀ y * ψ (θ j) (x - y)| := abs_integral_le_integral_abs
      _ ≤ ∫ y, ψ (θ j) (x - y) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun y => abs_nonneg _)
            (hψi.comp_sub_left x) (Eventually.of_forall fun y => ?_)
          show |g₀ y * ψ (θ j) (x - y)| ≤ ψ (θ j) (x - y)
          rw [abs_mul, abs_of_nonneg (hψ0 _ (hθpos j) _)]
          exact mul_le_of_le_one_left (hψ0 _ (hθpos j) _) (hg₀b y)
      _ = 1 := by rw [integral_sub_left_eq_self, hψ1 _ (hθpos j)]
  · have hleb := IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub
      (μ := (volume : Measure (Euclid n))) hg₀i.locallyIntegrable 1
    filter_upwards [hleb] with x hx
    have hθ0 : Tendsto θ atTop (𝓝 0) := by
      have : Tendsto (fun j : ℕ => ((j : ℝ) + 2)) atTop atTop :=
        tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
      simpa [hθdef] using this.const_div_atTop δ
    have hθ : Tendsto θ atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hθ0
        (Eventually.of_forall fun j => hθpos j)
    have havg := hx (fun _ => x) θ hθ
      (Eventually.of_forall fun j => mem_closedBall_self (by simpa using (hθpos j).le))
    have hB1 : 0 < (volume : Measure (Euclid n)).real (closedBall 0 1) := by
      rw [measureReal_def]
      exact ENNReal.toReal_pos (measure_closedBall_pos _ _ one_pos).ne' measure_closedBall_lt_top.ne
    have key := tendsto_integral_smul_of_tendsto_average_norm_sub
      (μ := (volume : Measure (Euclid n))) (f := g₀) (c := g₀ x)
      (a := fun j => closedBall x (θ j)) (g := fun j y => ψ (θ j) (x - y))
      ((1 / I) * (volume : Measure (Euclid n)).real (closedBall 0 1)) havg
      (Eventually.of_forall fun j => hg₀i.integrableOn)
      (by
        refine tendsto_const_nhds.congr' (Eventually.of_forall fun j => ?_)
        simp only
        rw [integral_sub_left_eq_self, hψ1 _ (hθpos j)])
      (Eventually.of_forall fun j y hy => by
        rw [mem_closedBall, dist_comm, dist_eq_norm]
        by_contra h
        exact hy (hψz _ (hθpos j) _ (by linarith [hθpos j])))
      (Eventually.of_forall fun j y => by
        rw [Measure.addHaar_real_closedBall' _ _ (hθpos j).le, finrank_euclideanSpace_fin]
        have hpow : 0 < θ j ^ n := pow_pos (hθpos j) n
        calc |ψ (θ j) (x - y)| ≤ (1 / I) / θ j ^ n := hψb _ (hθpos j) _
          _ = (1 / I) * (volume : Measure (Euclid n)).real (closedBall 0 1) /
              (θ j ^ n * (volume : Measure (Euclid n)).real (closedBall 0 1)) := by
            field_simp)
    refine key.congr' (Eventually.of_forall fun j => ?_)
    simp only
    rw [hG]
    congr 1; funext y
    rw [smul_eq_mul, mul_comm]
```

## Key steps

1. g₀ is integrable: measurable, |g₀| ≤ 1, and g₀ = 0 off B_R(0).
2. Normalized bump ρ = b/∫b (ContDiffBump with radii 1/4, 1/2): C^∞, 0 ≤ ρ ≤ 1/I, ρ = 0 for ‖x‖ ≥ 1/2, ∫ρ = 1; rescalings ψ_ε(x) = ε^{−n}ρ(x/ε) have ∫ψ_ε = 1, vanish for ‖x‖ ≥ ε/2 and satisfy |ψ_ε| ≤ (1/I)ε^{−n}.
3. G_j := g₀ ⋆ ψ_{θ_j} with θ_j = δ/(j + 2): C^∞ (convolution with a smooth compactly supported kernel), |G_j| ≤ ∫ψ = 1, support in closedBall(0, R + θ_j/2) so tsupport G_j ⊆ B_{R+δ}(0).
4. Lebesgue differentiation for the doubling Lebesgue measure plus the approximate-identity lemma give G_j(x) → g₀(x) for a.e. x.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical; workspace HEAD b4d606db)`
- `rg -n 'cbr_ci_pw_bv|mollif|convolution|ae_tendsto_average|l1_duality' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT (no match)`
- `grep -rn in /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/ for: 'theorem tendsto_integral_smul_of_tendsto_average_norm_sub' (MeasureTheory/Integral/Average.lean:835), 'theorem ae_tendsto_average_norm_sub' (MeasureTheory/Covering/DensityTheorem.lean:150; Covering/Differentiation.lean:837), 'HasCompactSupport.contDiff_convolution_right' (Analysis/Calculus/ContDiff/Convolution.lean:420), 'intervalIntegral_integral_swap' (MeasureTheory/Integral/Prod.lean:483), 'theorem integral_integral_swap' (Integral/Prod.lean:478), 'theorem Integrable.mul_prod' (Integral/Prod.lean:297), 'AEStronglyMeasurable.comp_snd' (Integral/Prod.lean:135), 'lemma Integrable.comp_snd' (Integral/Prod.lean:285), 'theorem continuous_of_dominated' (Integral/Bochner/Basic.lean:476), 'theorem integral_comp_inv_smul_of_nonneg' (Measure/Haar/NormedSpace.lean:129), "theorem addHaar_real_closedBall'" (Measure/Lebesgue/EqHaar.lean:479; IsUnifLocDoublingMeasure instance for Haar measures at EqHaar.lean:551), 'theorem fderiv_comp_add_right' (Analysis/Calculus/FDeriv/Add.lean:855), 'theorem norm_integral_le_of_norm_le_const' (IntervalIntegral/Basic.lean:769), 'theorem tendsto_integral_of_dominated_convergence' (Integral/DominatedConvergence.lean:57), 'theorem integral_eq_sub_of_hasDerivAt' (IntervalIntegral/FundThmCalculus.lean:1148), 'theorem integral_pos_iff_support_of_nonneg' (Bochner/Basic.lean:790), 'theorem support_eq' (Analysis/Calculus/BumpFunction/Basic.lean:151), 'theorem integrableOn_iff_integrable_of_support_subset' (Integral/IntegrableOn.lean:462), 'Measure.integrableOn_of_bounded' (Integral/IntegrableOn.lean:716), 'theorem setIntegral_indicator' (Integral/Bochner/Set.lean:194), 'theorem norm_integral_le_of_norm_le' (Bochner/Basic.lean:985)`
- `python3 -I scans of /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json: no lean_name with prefix cbr_ci_pw_bv_ except the selected cbr_ci_pw_bv_mollifier_estimate (rechecked immediately before returning); keyword scan (mollif|dualit|Lebesgue point|convolution|translation) of accepted nodes; frozen types of codim1_rdo_dg_bvc_l1_le_of_tests, codim1_rdo_dg_bvc_translate_test_le, codim1_rdo_dg_bvc_translation_l1_le, codim1_rdo_dg_bvc_mollify_l1_le, dorag_ha_weyl_ae_tendsto, dorag_ha_weyl_radial_mollifier, dgcr_stc_exists_normalized_mollifier compared with the needed obligations (none identical)`
- `git show f471edcde (dorag_ha_weyl_ae_tendsto), 376e5f482 (dgcr_stc_exists_normalized_mollifier), bfd6db12d (codim1_rdo_dg_bvc_mollify_l1_le), 499364f8f (codim1_rdo_dg_bvc_l1_le_of_tests), e2ca2a5c7 (codim1_rdo_dg_bvc_translate_test_le) as proof templates`
- `lake env lean /tmp/bvdec/T0.lean and T1.lean (#check after import GMT.Ch07.Submission: all cited lemmas reachable; Real.sign and measurable_sign NOT reachable, so the sign function is an if-then-else; IsUnifLocDoublingMeasure (volume : Measure (Euclid n)) synthesizes for every n)`
- `lake env lean /tmp/bvdec/Stmts.lean (six child types elaborate; parent assembly compiles against them), /tmp/bvdec/AsmAD.lean (smooth_test_bound from pairing_identity + translate_test; l1_duality from smooth_ae_approx), /tmp/bvdec/C.lean, T.lean, A1.lean, M.lean (complete leaf proofs), /tmp/bvdec/SubmissionCopy.lean (all six children plus the parent inserted before main_theorem in a copy of GMT/Ch07/Submission.lean: only the inherited main_theorem sorry warning; #print axioms Submission.cbr_ci_pw_bv_mollifier_estimate = [propext, Classical.choice, Quot.sound])`
- `python3 -I validate_lean_statement (verifier/lean_contract.py) on the six child types (all pass, normalized text unchanged); regex check that each frozen type is byte-identical to the compiled declaration`
- `sed of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_decompose: max_depth, _existing_lean_name_problem, _solve_children, _reference_use_problem), leaf_verification.py check_source_delta (one appended theorem, no helper declarations or set_option), prompts.py DECOMPOSITION_AUDIT`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Average.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/DensityTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Doubling.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-71f49efaa2/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-71f49efaa2/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-951a399d2e/decomposition-v1.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/prompts.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/bvdec/Stmts.lean`
- `/tmp/bvdec/AsmAD.lean`
- `/tmp/bvdec/SubmissionCopy.lean`

The pinned snapshot (local-project; project b4d606db, Mathlib 25730c7c) has Contract.lean byte-identical to the workspace Contract.lean and Submission.lean, and the project contains no mollification, convolution, duality or Lebesgue-point declaration (rg: no match), so the children rely only on pinned Mathlib. Every Mathlib lemma named in the child proofs was located in the snapshot (paths and lines above) and is reachable from import GMT.Ch07.Submission; Real.sign is not imported and is avoided. No DAG node uses a cbr_ci_pw_bv_* name other than the selected one, so the six names are fresh. Related accepted DAG theorems have different frozen types (codim1_rdo_dg_bvc_l1_le_of_tests needs a bounded measurable integrand and C¹ tests, but u − w is unbounded and only smooth tests are controlled; dorag_ha_weyl_ae_tendsto needs 0 < n), so nothing is reused and the children have no cross-branch dependencies; their accepted proofs were used only as templates. All six child types elaborate in the contract scope and pass validate_lean_statement. Complete Lean proofs of all six, plus the parent proof from mollify_continuous, smooth_test_bound and l1_duality, compile inside a copy of GMT/Ch07/Submission.lean with no new warnings. The parent depends only on propext, Classical.choice and Quot.sound.
