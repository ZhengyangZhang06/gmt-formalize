# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.bv_compactness-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.bv_compactness-a1.smooth_variation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Supplied proof of the parent node, step 3, second half: the choice ψ := χ_N·Gr/√(|Gr|² + θ²) and the passage θ ↓ 0, N → ∞. See also Simon Ch. 2, 2.5, formula (4) ∫f|Du^(σ)| = sup over smooth g with |g| ≤ f of ∫g·∇u^(σ) (chapter-02.txt lines 566–570), and the integration by parts in the display after it (lines 573–580).
Uses the sibling child ibp_c1_ball (accepted theorem, reused) for the integration by parts, instead of the parent's coordinatewise Fubini argument.
Deviation (simplification, kernel-checked): the cut-offs are ContDiffBump functions and the limit is taken with Fatou's lemma, which needs no monotonicity. The parent instead uses smoothTransition cut-offs with monotone convergence.

Notation. B := B_r(0); div ψ(v) := trace(Dψ(v)); e_i := EuclideanSpace.single i 1; ψ_i(x) := ψ(x)_i is the i-th coordinate.

0. If r ≤ 0 then B = ∅ and the left side is 0. Assume r > 0 from now on.
1. (Integration by parts in trace form.) Let ψ be C¹ with compact support and tsupport ψ ⊆ B. Then
   ∫ g div ψ = −∫_B Σ_i Dg(v)(e_i)·ψ_i(v) dv.
   Proof.
   (a) The coordinates ψ_i are C¹ (composition with the continuous linear coordinate map), have compact support, and satisfy tsupport ψ_i ⊆ tsupport ψ ⊆ B. Also g is C¹ on B.
   (b) ibp_c1_ball with n = m, R = r, h = g and Φ_i = ψ_i gives ∫_B Σ_i Dg(v)(e_i)ψ_i(v) = −∫_B g(v)Σ_i Dψ_i(v)(e_i).
   (c) Dψ_i(v)(w) = (Dψ(v)w)_i (PiLp.hasFDerivAt_apply). For the orthonormal basis (e_i), trace A = Σ_i ⟨e_i, A e_i⟩ = Σ_i (A e_i)_i (LinearMap.trace_eq_sum_inner, EuclideanSpace.inner_single_left). So Σ_i Dψ_i(v)(e_i) = div ψ(v).
   (d) div ψ(v) = 0 for v ∉ B, because Dψ vanishes off tsupport ψ ⊆ B (support_fderiv_subset). Hence ∫ g div ψ = ∫_B g div ψ = −∫_B Σ_i Dg(v)(e_i)ψ_i(v).
2. (Gradient.) Let G(v) := (InnerProductSpace.toDual ℝ ℝ^m)⁻¹(Dg(v)), the gradient. It satisfies:
   - ⟨G(v), w⟩ = Dg(v)w for all w, so G(v)_i = Dg(v)(e_i);
   - |G(v)| = ‖Dg(v)‖, since toDual is an isometry;
   - G is C^∞, because each coordinate v ↦ Dg(v)(e_i) is C^∞ (Dg is C^∞ since g is);
   - Σ_i Dg(v)(e_i)·G(v)_i = Σ_i G(v)_i² = |G(v)|².
3. (Cut-offs and test fields.) For k ∈ ℕ let θ_k := 1/(k + 1) ∈ (0, 1]. Let χ_k be the ContDiffBump centred at 0 with inner radius r(1 − θ_k/2) and outer radius r(1 − θ_k/4). So χ_k is C^∞, 0 ≤ χ_k ≤ 1, χ_k = 1 on closedBall(0, r(1 − θ_k/2)), and tsupport χ_k = closedBall(0, r(1 − θ_k/4)) ⊆ B.
   Put s_k(v) := √(|G(v)|² + θ_k²). This is > 0, and it is C^∞ because the argument of √ is ≥ θ_k² > 0. Define
   ψ_k(v) := −(χ_k(v)/s_k(v))·G(v).
   Then:
   - ψ_k is C^∞;
   - tsupport ψ_k ⊆ tsupport χ_k ⊆ B, since ψ_k vanishes where χ_k does; so ψ_k has compact support;
   - |ψ_k(v)| = χ_k(v)|G(v)|/s_k(v) ≤ 1, because |G(v)| ≤ s_k(v) and χ_k ≤ 1.
4. (Integral identity.) Put f_k(v) := χ_k(v)|G(v)|²/s_k(v) ≥ 0. By step 1 and step 2,
   ∫ g div ψ_k = −∫_B Σ_i Dg(v)(e_i)·(−χ_k(v)/s_k(v))G(v)_i dv = ∫_B f_k.
   The hypothesis applied to ψ_k gives ∫_B f_k ≤ c. Since f_k is continuous and B is bounded, f_k is integrable on B. Hence ∫⁻_B ofReal(f_k) = ofReal(∫_B f_k) ≤ ofReal c.
5. (Limit.) Fix v ∈ B.
   - As k → ∞, r(1 − θ_k/2) → r > |v|, so χ_k(v) = 1 for all large k.
   - s_k(v) → |G(v)|, so |G(v)|²/s_k(v) → |G(v)|. This is trivial if G(v) = 0.
   Hence f_k(v) → |G(v)| = ‖Dg(v)‖. By Fatou's lemma (lintegral_liminf_le),
   ∫⁻_B ‖Dg‖ = ∫⁻_B liminf_k ofReal(f_k) ≤ liminf_k ∫⁻_B ofReal(f_k) ≤ ofReal c. ∎
Remark. The parent's monotone version also works: χ_N(v) = smoothTransition(N(1 − |v|²/r²) − 1), with θ ↓ 0, N ↑ ∞ and monotone convergence. For m = 0 everything is 0.

Appendix (Lean proof, kernel-checked). Compiled with the pinned toolchain (Lean v4.35.0-rc3, Mathlib 25730c7c) inside namespace GMT.Ch07 of a file importing GMT.Ch07.Submission, with the contract's opens and with the sibling Submission.dorag_ha_lsc_ibp_c1_ball declared with its frozen type. It is one declaration with no helper declaration and no set_option. In the end-to-end file (all twelve children, the accepted proofs from commit 46877ce9, and the parent assembly), #print axioms gives propext, Classical.choice and Quot.sound.

theorem Submission.codim1_zsl_pc_smooth_grad_bound : ∀ (m : ℕ) (g : Euclid m → ℝ) (r c : ℝ), ContDiff ℝ (⊤ : ℕ∞) g → (∀ ψ : Euclid m → Euclid m, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ ball (0 : Euclid m) r → (∀ v, ‖ψ v‖ ≤ 1) → ∫ v, g v * LinearMap.trace ℝ (Euclid m) (fderiv ℝ ψ v).toLinearMap ≤ c) → ∫⁻ v in ball (0 : Euclid m) r, ‖fderiv ℝ g v‖ₑ ≤ ENNReal.ofReal c := by
  intro m g r c hg hψ
  rcases le_or_gt r 0 with hr | hr
  · rw [ball_eq_empty.2 hr]; simp
  set B := ball (0 : Euclid m) r with hB
  have h1 : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 le_top
  -- Step 1: integration by parts in trace form, from the stub
  have ibp : ∀ ψ : Euclid m → Euclid m, ContDiff ℝ 1 ψ → HasCompactSupport ψ → tsupport ψ ⊆ B →
      ∫ v, g v * LinearMap.trace ℝ (Euclid m) (fderiv ℝ ψ v).toLinearMap
        = -∫ v in B, ∑ i : Fin m, fderiv ℝ g v (EuclideanSpace.single i (1:ℝ)) * ψ v i := by
    intro ψ hψ1 hψc hψB
    have key := Submission.dorag_ha_lsc_ibp_c1_ball m r g (fun i x => ψ x i)
      (hg.of_le h1).contDiffOn (fun i => (contDiff_piLp 2).1 hψ1 i)
      (fun i => hψc.comp_left (g := fun w : Euclid m => w i) (by simp))
      (fun i => (tsupport_comp_subset (g := fun w : Euclid m => w i) (by simp) ψ).trans hψB)
    have hd : ∀ v (i : Fin m), fderiv ℝ (fun x => ψ x i) v
        = (PiLp.proj 2 (fun _ : Fin m => ℝ) i).comp (fderiv ℝ ψ v) := fun v i => by
      have h := (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (ψ v) i).comp v
        ((hψ1.differentiable one_ne_zero) v).hasFDerivAt
      exact h.fderiv
    have htr : ∀ v, LinearMap.trace ℝ (Euclid m) (fderiv ℝ ψ v).toLinearMap
        = ∑ i : Fin m, fderiv ℝ (fun x => ψ x i) v (EuclideanSpace.single i 1) := by
      intro v
      rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin m) ℝ)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hd]
      simp [EuclideanSpace.inner_single_left]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := B) ?_]
    · simp_rw [htr]
      simp only [] at key
      rw [key, neg_neg]
    · intro v hv
      have : fderiv ℝ ψ v = 0 := by
        by_contra hne
        exact hv (hψB (support_fderiv_subset ℝ hne))
      simp [this]
  -- Step 2: the gradient field
  set L := fderiv ℝ g with hLdef
  have hL : ContDiff ℝ (⊤ : ℕ∞) L := (contDiff_infty_iff_fderiv.1 hg).2
  set G : Euclid m → Euclid m := fun v => (InnerProductSpace.toDual ℝ (Euclid m)).symm (L v)
    with hGdef
  have hGi : ∀ v (i : Fin m), G v i = L v (EuclideanSpace.single i 1) := by
    intro v i
    have := EuclideanSpace.inner_single_left i (1:ℝ) (G v)
    rw [real_inner_comm, hGdef, InnerProductSpace.toDual_symm_apply] at this
    simpa using this.symm
  have hGn : ∀ v, ‖G v‖ = ‖L v‖ := fun v => LinearIsometryEquiv.norm_map _ _
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := by
    rw [contDiff_piLp 2]
    intro i
    have : (fun x => G x i) = fun x => L x (EuclideanSpace.single i 1) := funext fun x => hGi x i
    rw [this]
    exact hL.clm_apply contDiff_const
  have hsum : ∀ v, ∑ i : Fin m, L v (EuclideanSpace.single i 1) * G v i = ‖G v‖ ^ 2 := by
    intro v
    rw [PiLp.norm_sq_eq_of_L2]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← hGi, Real.norm_eq_abs, sq_abs, sq]
  -- parameters and cutoffs
  set θ : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hθdef
  have hθpos : ∀ k, 0 < θ k := fun k => by positivity
  have hθle : ∀ k, θ k ≤ 1 := fun k => by
    rw [hθdef, div_le_one (by positivity)]
    have := (Nat.cast_nonneg k : (0:ℝ) ≤ k)
    linarith
  have hθlim : Tendsto θ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set ri : ℕ → ℝ := fun k => r * (1 - θ k / 2) with hridef
  set ro : ℕ → ℝ := fun k => r * (1 - θ k / 4) with hrodef
  have hri : ∀ k, 0 < ri k := fun k => mul_pos hr (by linarith [hθle k])
  have hrio : ∀ k, ri k < ro k := fun k => mul_lt_mul_of_pos_left (by linarith [hθpos k]) hr
  have hro : ∀ k, ro k < r := fun k => mul_lt_of_lt_one_right hr (by linarith [hθpos k])
  let χ : ℕ → ContDiffBump (0 : Euclid m) := fun k => ⟨ri k, ro k, hri k, hrio k⟩
  have hχ1 : ∀ v ∈ B, ∀ᶠ k in atTop, χ k v = 1 := by
    intro v hv
    have hlim : Tendsto ri atTop (𝓝 r) := by
      have := (tendsto_const_nhds (x := r)).mul
        ((tendsto_const_nhds (x := (1:ℝ))).sub (hθlim.div_const 2))
      simpa using this
    have hv' : ‖v‖ < r := by simpa [hB] using hv
    filter_upwards [hlim.eventually_const_lt hv'] with k hk
    exact (χ k).one_of_mem_closedBall (by rw [mem_closedBall_zero_iff]; exact hk.le)
  -- the test fields
  set s : ℕ → Euclid m → ℝ := fun k v => √(‖G v‖ ^ 2 + θ k ^ 2) with hsdef
  have hspos : ∀ k v, 0 < s k v := fun k v => Real.sqrt_pos.2 (by have := hθpos k; positivity)
  have hGs : ∀ k v, ‖G v‖ ≤ s k v := fun k v =>
    Real.le_sqrt_of_sq_le (by have := hθpos k; nlinarith)
  have hsc : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (s k) := fun k =>
    ((hG.norm_sq ℝ).add contDiff_const).sqrt (fun v => by have := hθpos k; positivity)
  set ψ : ℕ → Euclid m → Euclid m := fun k v => (-(χ k v / s k v)) • G v with hψdef
  set f : ℕ → Euclid m → ℝ := fun k v => χ k v * (‖G v‖ ^ 2 / s k v) with hfdef
  have hψs : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (ψ k) := fun k =>
    (((χ k).contDiff.div (hsc k) (fun v => (hspos k v).ne')).neg).smul hG
  have hψsupp : ∀ k, tsupport (ψ k) ⊆ closedBall 0 (ro k) := by
    intro k
    rw [← (χ k).tsupport_eq]
    apply closure_mono
    intro v hv
    rw [Function.mem_support] at hv ⊢
    intro h0
    apply hv
    simp [hψdef, h0]
  have hψB : ∀ k, tsupport (ψ k) ⊆ B := fun k => (hψsupp k).trans (closedBall_subset_ball (hro k))
  have hψc : ∀ k, HasCompactSupport (ψ k) := fun k =>
    (isCompact_closedBall 0 (ro k)).of_isClosed_subset (isClosed_tsupport _) (hψsupp k)
  have hψn : ∀ k v, ‖ψ k v‖ ≤ 1 := by
    intro k v
    have hχ0 := (χ k).nonneg (x := v)
    have hχ1' := (χ k).le_one (x := v)
    simp only [hψdef, norm_smul, norm_neg, norm_div, Real.norm_eq_abs, abs_of_nonneg hχ0,
      abs_of_pos (hspos k v)]
    rw [div_mul_eq_mul_div, div_le_one (hspos k v)]
    calc χ k v * ‖G v‖ ≤ 1 * s k v := mul_le_mul hχ1' (hGs k v) (norm_nonneg _) zero_le_one
      _ = s k v := one_mul _
  -- Step 3: the integral identity and bound
  have hint_eq : ∀ k, ∫ v, g v * LinearMap.trace ℝ (Euclid m) (fderiv ℝ (ψ k) v).toLinearMap
      = ∫ v in B, f k v := by
    intro k
    rw [ibp (ψ k) ((hψs k).of_le h1) (hψc k) (hψB k), ← integral_neg]
    congr 1
    funext v
    have : ∀ i : Fin m, L v (EuclideanSpace.single i 1) * (ψ k v) i
        = -(χ k v / s k v) * (L v (EuclideanSpace.single i 1) * G v i) := fun i => by
      simp only [hψdef, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
      ring
    simp_rw [this, ← Finset.mul_sum, hsum, hfdef]
    ring
  have hle : ∀ k, ∫ v in B, f k v ≤ c := fun k =>
    (hint_eq k) ▸ hψ (ψ k) (hψs k) (hψc k) (hψB k) (hψn k)
  have hfc : ∀ k, Continuous (f k) := fun k =>
    (χ k).continuous.mul (((continuous_norm.comp hG.continuous).pow 2).div (hsc k).continuous
      (fun v => (hspos k v).ne'))
  have hfnn : ∀ k v, 0 ≤ f k v := fun k v =>
    mul_nonneg (χ k).nonneg (div_nonneg (sq_nonneg _) (hspos k v).le)
  have hfi : ∀ k, IntegrableOn (f k) B := fun k =>
    ((hfc k).continuousOn.integrableOn_compact (isCompact_closedBall (0 : Euclid m) r)).mono_set
      ball_subset_closedBall
  have hbound : ∀ k, ∫⁻ v in B, ENNReal.ofReal (f k v) ≤ ENNReal.ofReal c := by
    intro k
    rw [← ofReal_integral_eq_lintegral_ofReal (hfi k) (ae_of_all _ (hfnn k))]
    exact ENNReal.ofReal_le_ofReal (hle k)
  -- Step 4: pointwise convergence and Fatou
  have htend : ∀ v ∈ B, Tendsto (fun k => ENNReal.ofReal (f k v)) atTop
      (𝓝 (ENNReal.ofReal ‖G v‖)) := by
    intro v hv
    apply ENNReal.tendsto_ofReal
    have hχt : Tendsto (fun k => χ k v) atTop (𝓝 1) :=
      tendsto_const_nhds.congr' (by filter_upwards [hχ1 v hv] with k hk; exact hk.symm)
    have hq : Tendsto (fun k => ‖G v‖ ^ 2 / s k v) atTop (𝓝 ‖G v‖) := by
      rcases eq_or_ne ‖G v‖ 0 with h0 | h0
      · simp [h0]
      · have hs : Tendsto (fun k => s k v) atTop (𝓝 (√(‖G v‖ ^ 2 + 0 ^ 2))) :=
          (tendsto_const_nhds.add (hθlim.pow 2)).sqrt
        have hne : √(‖G v‖ ^ 2 + 0 ^ 2) ≠ 0 := by
          rw [zero_pow two_ne_zero, add_zero, Real.sqrt_sq (norm_nonneg _)]; exact h0
        have := (tendsto_const_nhds (x := ‖G v‖ ^ 2)).div hs hne
        convert this using 2
        rw [zero_pow two_ne_zero, add_zero, Real.sqrt_sq (norm_nonneg _), sq, mul_self_div_self]
    have := hχt.mul hq
    rw [one_mul] at this
    exact this
  calc ∫⁻ v in B, ‖L v‖ₑ = ∫⁻ v in B, liminf (fun k => ENNReal.ofReal (f k v)) atTop := by
        refine setLIntegral_congr_fun measurableSet_ball (fun v hv => ?_)
        rw [(htend v hv).liminf_eq, hGn, ofReal_norm]
    _ ≤ liminf (fun k => ∫⁻ v in B, ENNReal.ofReal (f k v)) atTop :=
        lintegral_liminf_le (fun k => (hfc k).measurable.ennreal_ofReal)
    _ ≤ ENNReal.ofReal c := liminf_le_of_frequently_le' (Frequently.of_forall hbound)

## Key steps

1. IBP (reused ibp_c1_ball with the coordinates ψ_i, and trace = Σ_i(Dψ e_i)_i): ∫ g div ψ = −∫_B Dg(ψ) for C¹ ψ with tsupport ⊆ B.
2. The gradient G = toDual⁻¹(Dg) is C^∞, with |G| = ‖Dg‖ and Dg(G) = |G|².
3. Test fields ψ_k = −χ_k G/√(|G|² + θ_k²) with bump cut-offs χ_k → 1 on B are admissible, so ∫_B χ_k|G|²/√(|G|² + θ_k²) ≤ c.
4. The integrands tend pointwise to ‖Dg‖ on B, and Fatou's lemma gives ∫_B‖Dg‖ ≤ c.

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
