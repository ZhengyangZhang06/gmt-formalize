# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.cube_bv_median-a1.smooth_approx-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.cube_bv_median-a1.smooth_approx-a1.mollify_l1-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 of the parent proof, L¹ convergence of mollifications. Its three parts are: (a) the L¹ contraction, (b) the continuous compactly supported case by uniform continuity, and (c) density of continuous compactly supported functions. Here the statement is uniform over all continuous normalized kernels supported in a small ball, in ε–r form. It uses the [0, ∞]-valued lintegral, so the conclusion cannot hold vacuously through a non-integrable Bochner integral. The pointwise estimate of 4(b) is Mathlib's dist_convolution_le for general kernels. In Simon this is the standard fact quoted at the start of the proof of Ch. 2, Lemma 2.5: "the convergence of u^(σ) to u in L¹_loc(U) is standard" (book/chapter-02.txt lines 543–546).

Notation. n ∈ ℕ. ℝⁿ := Euclid n = EuclideanSpace ℝ (Fin n) with Lebesgue measure (volume), and |·| is the Euclidean norm.
- For a ∈ ℝ, ‖a‖ₑ ∈ [0, ∞] is the extended norm ofReal|a|, and ∫⁻ is the [0, ∞]-valued Lebesgue integral.
- For a kernel k and a function a, (k ⋆ a)(x) := ∫ k(t) a(x − t) dt, i.e. Mathlib's `convolution k a (ContinuousLinearMap.lsmul ℝ ℝ) volume x` (convolution_def, ContinuousLinearMap.lsmul_apply).
- B_r(0) is the open ball, and A + B := {a + b : a ∈ A, b ∈ B}.

Import note. Integrable.exists_hasCompactSupport_lintegral_sub_le lives in Mathlib.MeasureTheory.Function.ContinuousMapDense, which is outside the import closure of the frozen GMT/Ch07/Submission.lean. Add `import Mathlib.MeasureTheory.Function.ContinuousMapDense` to Submission.lean; accepted nodes of this run already do this, and the frozen statement elaborates without it. Minkowski sums of sets need `open scoped Pointwise`, e.g. `open scoped Pointwise in` before the theorem. All other cited lemmas are in the frozen import closure.

Fix f integrable and ε > 0.

1. L¹ contraction. Claim: for every continuous k : ℝⁿ → ℝ with k ≥ 0 and ∫k = 1, and every a.e.-strongly measurable g : ℝⁿ → ℝ, ∫⁻ ‖(k ⋆ g)(x)‖ₑ dx ≤ ∫⁻ ‖g(x)‖ₑ dx.
Proof.
- k is integrable (integrable_of_integral_eq_one). As k ≥ 0, ∫⁻ ‖k‖ₑ = ∫⁻ ofReal(k) = ofReal(∫k) = 1 (ofReal_integral_eq_lintegral_ofReal, Real.enorm_eq_ofReal).
- For each x, ‖(k ⋆ g)(x)‖ₑ = ‖∫ k(t) g(x − t) dt‖ₑ ≤ ∫⁻ ‖k(t) g(x − t)‖ₑ dt (enorm_integral_le_lintegral_enorm), and ‖k(t) g(x − t)‖ₑ = ‖k(t)‖ₑ ‖g(x − t)‖ₑ (enorm_mul).
- The function (x, t) ↦ ‖k(t) g(x − t)‖ₑ is a.e.-measurable for the product measure (AEStronglyMeasurable.convolution_integrand, then enorm).
Then Tonelli (lintegral_lintegral_swap), factoring out the constant ‖k(t)‖ₑ < ∞ (lintegral_const_mul'), translation invariance ∫⁻ ‖g(x − t)‖ₑ dx = ∫⁻ ‖g‖ₑ (lintegral_sub_right_eq_self), and factoring out ∫⁻ ‖g‖ₑ against the measurable t ↦ ‖k(t)‖ₑ (lintegral_mul_const) give
   ∫⁻_x ‖(k ⋆ g)(x)‖ₑ ≤ ∫⁻_x ∫⁻_t ‖k(t)‖ₑ ‖g(x − t)‖ₑ = ∫⁻_t ‖k(t)‖ₑ ∫⁻_x ‖g(x − t)‖ₑ = (∫⁻ ‖k‖ₑ)(∫⁻ ‖g‖ₑ) = ∫⁻ ‖g‖ₑ.

2. Density. Lebesgue measure on Euclid n is regular, and ℝⁿ is locally compact and R1. So Integrable.exists_hasCompactSupport_lintegral_sub_le with tolerance ofReal(ε/4) ≠ 0 gives h : ℝⁿ → ℝ with: h continuous, compactly supported and integrable, and ∫⁻ ‖f(x) − h(x)‖ₑ dx ≤ ofReal(ε/4).

3. Choice of r. Let S := tsupport h + closedBall(0, 1). As the sum of two compact sets it is compact (IsCompact.add), hence closed, measurable, and of finite measure. Put τ := ε / (4(vol(S).toReal + 1)) > 0 (called η in the Lean code below). Since h is continuous with compact support, it is uniformly continuous (HasCompactSupport.uniformContinuous_of_continuous). So there is r₀ > 0 with |h(a) − h(b)| < τ whenever |a − b| < r₀ (Metric.uniformContinuous_iff). Put r := min(r₀, 1) > 0.
Now let ρ be continuous with ρ ≥ 0, ∫ρ = 1 and support ρ ⊆ B_r(0). Then ρ has compact support, since support ρ ⊆ closedBall(0, r), which is compact.

4. The continuous compactly supported case. For every x:
 (a) |(ρ ⋆ h)(x) − h(x)| ≤ τ. Apply dist_convolution_le with:
  - kernel ρ, support ρ ⊆ B_r(0), ρ ≥ 0 and ∫ρ = 1;
  - h a.e.-strongly measurable (it is continuous);
  - z₀ = h(x) and the bound dist(h(y), h(x)) ≤ τ for y ∈ B_r(x), valid because |y − x| < r ≤ r₀.
  Equivalently: (ρ ⋆ h)(x) − h(x) = ∫ ρ(t)(h(x − t) − h(x)) dt, with |h(x − t) − h(x)| < τ wherever ρ(t) ≠ 0.
 (b) If x ∉ S, then (ρ ⋆ h)(x) = 0 = h(x).
  - If h(x) ≠ 0, then x = x + 0 ∈ tsupport h + closedBall(0, 1) = S.
  - If (ρ ⋆ h)(x) ≠ 0, then by support_convolution_subset_swap, x = a + t with h(a) ≠ 0 and ρ(t) ≠ 0. So a ∈ tsupport h and |t| < r ≤ 1, giving x ∈ S.
Hence ‖(ρ ⋆ h)(x) − h(x)‖ₑ ≤ 1_S(x) · ofReal(τ) for all x. By lintegral_indicator_const,
   ∫⁻ ‖ρ ⋆ h − h‖ₑ ≤ ofReal(τ) · vol(S) = ofReal(τ · vol(S).toReal) ≤ ofReal(ε/4),
because τ · vol(S).toReal = ε · vol(S).toReal / (4(vol(S).toReal + 1)) ≤ ε/4.

5. Linearity. For every x, (ρ ⋆ f)(x) − (ρ ⋆ h)(x) = (ρ ⋆ (f − h))(x). The convolution integrals of ρ with h and with f − h exist at x, because ρ is continuous with compact support and h, f − h are locally integrable (HasCompactSupport.convolutionExists_left). So ConvolutionExistsAt.distrib_add gives (ρ ⋆ (h + (f − h)))(x) = (ρ ⋆ h)(x) + (ρ ⋆ (f − h))(x), and h + (f − h) = f.

6. Conclusion. For every x, by step 5 and the triangle inequality,
   ‖(ρ ⋆ f)(x) − f(x)‖ₑ ≤ ‖(ρ ⋆ (f − h))(x)‖ₑ + ‖(ρ ⋆ h)(x) − h(x)‖ₑ + ‖f(x) − h(x)‖ₑ.
The functions x ↦ (ρ ⋆ (f − h))(x) and x ↦ (ρ ⋆ h)(x) − h(x) are continuous (HasCompactSupport.continuous_convolution_left; h is continuous), hence measurable. So the lintegral of the sum is the sum of the lintegrals (lintegral_add_left'). The three terms are bounded as follows:
- first: by step 1 (with k = ρ and g = f − h, which is a.e.-strongly measurable) and step 2, it is ≤ ∫⁻ ‖f − h‖ₑ ≤ ofReal(ε/4);
- second: ≤ ofReal(ε/4) by step 4;
- third: ≤ ofReal(ε/4) by step 2.
Therefore ∫⁻ ‖ρ ⋆ f − f‖ₑ ≤ 3 · ofReal(ε/4) = ofReal(3ε/4) ≤ ofReal(ε). ∎
The case n = 0 needs no separate treatment.

Formalization note. The following Lean proof of the exact frozen statement was compiled in a scratch harness. The harness imports `GMT.Ch07.Submission` and `Mathlib.MeasureTheory.Function.ContinuousMapDense`, and the proof sits inside `namespace GMT.Ch07` / `namespace Submission`. #print axioms reports propext, Classical.choice and Quot.sound.
```lean
open scoped Pointwise in
theorem dimred_mbl_dt_cbm_sa_mollify_l1 : ∀ (n : ℕ) (f : Euclid n → ℝ), Integrable f → ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, 0 < r ∧ ∀ ρ : Euclid n → ℝ, Continuous ρ → (∀ z, 0 ≤ ρ z) → ∫ z, ρ z = 1 → support ρ ⊆ ball (0 : Euclid n) r → ∫⁻ x, ‖convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) volume x - f x‖ₑ ≤ ENNReal.ofReal ε := by
  intro n f hf ε hε
  -- density of continuous compactly supported functions
  obtain ⟨h, hhc, hfh, hhcont, hhi⟩ :=
    hf.exists_hasCompactSupport_lintegral_sub_le (μ := volume)
      (ε := ENNReal.ofReal (ε / 4)) (by simp; positivity)
  -- the compact set S
  set S : Set (Euclid n) := tsupport h + closedBall (0 : Euclid n) 1 with hS_def
  have hS : IsCompact S := hhc.isCompact.add (isCompact_closedBall 0 1)
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  have hSfin : volume S < ∞ := hS.measure_lt_top
  set η : ℝ := ε / (4 * ((volume S).toReal + 1)) with hη_def
  have hη : 0 < η := by positivity
  obtain ⟨r₀, hr₀, hr₀h⟩ :=
    Metric.uniformContinuous_iff.1 (hhc.uniformContinuous_of_continuous hhcont) η hη
  refine ⟨min r₀ 1, lt_min hr₀ one_pos, ?_⟩
  intro ρ hρc hρnn hρint hρsupp
  have hρcs : HasCompactSupport ρ := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid n) (min r₀ 1)) fun x hx => ?_
    by_contra hne
    exact hx (ball_subset_closedBall (hρsupp hne))
  have hρi : Integrable ρ := integrable_of_integral_eq_one hρint
  have hρ1 : ∫⁻ t, ‖ρ t‖ₑ = 1 := by
    have h1 := ofReal_integral_eq_lintegral_ofReal hρi (Eventually.of_forall hρnn)
    rw [hρint, ENNReal.ofReal_one] at h1
    rw [h1]
    congr 1; funext t
    rw [Real.enorm_eq_ofReal (hρnn t)]
  -- 1. L¹ contraction
  have contraction : ∀ g : Euclid n → ℝ, AEStronglyMeasurable g volume →
      ∫⁻ x, ‖convolution ρ g (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ ≤ ∫⁻ x, ‖g x‖ₑ := by
    intro g hg
    have hmeas : AEMeasurable (uncurry fun x t =>
        ‖(ContinuousLinearMap.lsmul ℝ ℝ) (ρ t) (g (x - t))‖ₑ)
        ((volume : Measure (Euclid n)).prod volume) :=
      (hρc.aestronglyMeasurable.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hg).enorm
    calc ∫⁻ x, ‖convolution ρ g (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ
        ≤ ∫⁻ x, ∫⁻ t, ‖(ContinuousLinearMap.lsmul ℝ ℝ) (ρ t) (g (x - t))‖ₑ :=
          lintegral_mono fun x => by
            rw [convolution_def]
            exact enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ t, ∫⁻ x, ‖(ContinuousLinearMap.lsmul ℝ ℝ) (ρ t) (g (x - t))‖ₑ :=
          lintegral_lintegral_swap hmeas
      _ = ∫⁻ t, ‖ρ t‖ₑ * ∫⁻ x, ‖g x‖ₑ := by
          congr 1; funext t
          simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, enorm_mul]
          rw [lintegral_const_mul' _ _ enorm_ne_top,
            lintegral_sub_right_eq_self (fun x => ‖g x‖ₑ) t]
      _ = ∫⁻ x, ‖g x‖ₑ := by
          rw [lintegral_mul_const _ hρc.measurable.enorm, hρ1, one_mul]
  set L := ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ) with hL
  have hfloc : LocallyIntegrable f volume := hf.locallyIntegrable
  have hhloc : LocallyIntegrable h volume := hhi.locallyIntegrable
  have hfhloc : LocallyIntegrable (f - h) volume := (hf.sub hhi).locallyIntegrable
  -- 5. linearity
  have hlin : ∀ x, convolution ρ f L volume x - convolution ρ h L volume x =
      convolution ρ (f - h) L volume x := by
    intro x
    have e1 := hρcs.convolutionExists_left L hρc hhloc x
    have e2 := hρcs.convolutionExists_left L hρc hfhloc x
    have e3 := e1.distrib_add e2
    rw [show h + (f - h) = f by funext y; simp] at e3
    rw [e3]; ring
  -- 4. the continuous compactly supported case
  have hRle : min r₀ 1 ≤ r₀ := min_le_left _ _
  have hpt : ∀ x, ‖convolution ρ h L volume x - h x‖ₑ ≤
      S.indicator (fun _ => ENNReal.ofReal η) x := by
    intro x
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
      have hd := dist_convolution_le (μ := volume) (f := ρ) (g := h) (x₀ := x) (R := min r₀ 1)
        (ε := η) (z₀ := h x) hη.le hρsupp hρnn hρint hhcont.aestronglyMeasurable
        (fun y hy => (hr₀h (lt_of_lt_of_le (mem_ball.1 hy) hRle)).le)
      rw [dist_eq_norm] at hd
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal hd
    · rw [indicator_of_notMem hx]
      have h1 : h x = 0 := by
        by_contra hne
        exact hx ⟨x, subset_tsupport _ hne, 0, mem_closedBall_self zero_le_one, add_zero x⟩
      have h2 : convolution ρ h L volume x = 0 := by
        by_contra hne
        obtain ⟨a, ha, t, ht, hat⟩ := support_convolution_subset_swap L hne
        exact hx ⟨a, subset_tsupport _ ha, t,
          ball_subset_closedBall (ball_subset_ball (min_le_right _ _) (hρsupp ht)), hat⟩
      simp [h1, h2]
  have hstep4 : ∫⁻ x, ‖convolution ρ h L volume x - h x‖ₑ ≤ ENNReal.ofReal (ε / 4) := by
    calc ∫⁻ x, ‖convolution ρ h L volume x - h x‖ₑ
        ≤ ∫⁻ x, S.indicator (fun _ => ENNReal.ofReal η) x := lintegral_mono hpt
      _ = ENNReal.ofReal η * volume S := lintegral_indicator_const hSm _
      _ = ENNReal.ofReal (η * (volume S).toReal) := by
          rw [ENNReal.ofReal_mul hη.le, ENNReal.ofReal_toReal hSfin.ne]
      _ ≤ ENNReal.ofReal (ε / 4) := by
          apply ENNReal.ofReal_le_ofReal
          have hV : 0 ≤ (volume S).toReal := ENNReal.toReal_nonneg
          rw [hη_def, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
  -- 6. conclusion
  have hpt2 : ∀ x, ‖convolution ρ f L volume x - f x‖ₑ ≤
      ‖convolution ρ (f - h) L volume x‖ₑ + ‖convolution ρ h L volume x - h x‖ₑ +
        ‖f x - h x‖ₑ := by
    intro x
    have e : convolution ρ f L volume x - f x = convolution ρ (f - h) L volume x +
        (convolution ρ h L volume x - h x) - (f x - h x) := by
      rw [← hlin x]; ring
    rw [e]
    exact (enorm_sub_le).trans (add_le_add_left (enorm_add_le _ _) _)
  have hc1 : Continuous (convolution ρ (f - h) L volume) :=
    hρcs.continuous_convolution_left L hρc hfhloc
  have hc2 : Continuous (convolution ρ h L volume) :=
    hρcs.continuous_convolution_left L hρc hhloc
  have hm1 : AEMeasurable (fun x => ‖convolution ρ (f - h) L volume x‖ₑ) volume :=
    hc1.measurable.enorm.aemeasurable
  have hm2 : AEMeasurable (fun x => ‖convolution ρ h L volume x - h x‖ₑ) volume :=
    (hc2.sub hhcont).measurable.enorm.aemeasurable
  calc ∫⁻ x, ‖convolution ρ f L volume x - f x‖ₑ
      ≤ ∫⁻ x, (‖convolution ρ (f - h) L volume x‖ₑ + ‖convolution ρ h L volume x - h x‖ₑ +
          ‖f x - h x‖ₑ) := lintegral_mono hpt2
    _ = (∫⁻ x, ‖convolution ρ (f - h) L volume x‖ₑ) +
          (∫⁻ x, ‖convolution ρ h L volume x - h x‖ₑ) + ∫⁻ x, ‖f x - h x‖ₑ := by
        have h12 : AEMeasurable (fun x => ‖convolution ρ (f - h) L volume x‖ₑ +
            ‖convolution ρ h L volume x - h x‖ₑ) volume := hm1.add hm2
        rw [lintegral_add_left' h12, lintegral_add_left' hm1]
    _ ≤ ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) := by
        refine add_le_add (add_le_add ?_ hstep4) hfh
        exact (contraction (f - h) (hf.sub hhi).aestronglyMeasurable).trans hfh
    _ = ENNReal.ofReal (3 * ε / 4) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal (by linarith)
```

## Key steps

1. L¹ contraction: ∫⁻‖k⋆g‖ₑ ≤ ∫⁻‖g‖ₑ for continuous k ≥ 0 with ∫k = 1, by Tonelli and translation invariance.
2. Density: choose h continuous with compact support and ∫⁻‖f − h‖ₑ ≤ ε/4.
3. Uniform continuity of h gives r ≤ 1 with |ρ⋆h − h| ≤ τ everywhere, and ρ⋆h − h = 0 off the compact S = tsupport h + closedBall(0,1). Hence ∫⁻‖ρ⋆h − h‖ₑ ≤ τ vol(S) ≤ ε/4.
4. ρ⋆f − f = ρ⋆(f − h) + (ρ⋆h − h) + (h − f), and the three ε/4 bounds sum to at most ε.

## Reference use

### local-project

Queries:
- `cat SNAPSHOT/manifest.json (mode local-project, project_commit b4d606db1da5…, mathlib_commit 25730c7c759d…); cmp SNAPSHOT/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical); cmp GMT/Ch07/Submission.lean GMT/Ch07/Contract.lean (identical)`
- `rg -n -i 'mollif|convolution' SNAPSHOT/project/GMT -g '*.lean' (no match)`
- `rg -n over SNAPSHOT/mathlib/Mathlib for: _root_.HasCompactSupport.hasFDerivAt_convolution_left, _root_.HasCompactSupport.contDiff_convolution_left, normed_neg, integral_normed, support_normed_eq, contDiff_normed, hasCompactSupport_normed, Integrable.exists_hasCompactSupport_lintegral_sub_le, convolution_def, ConvolutionExistsAt.distrib_add, support_convolution_subset_swap, dist_convolution_le, trace_smulRight, toDual_symm_apply, PiLp.norm_apply_le, lintegral_lintegral_swap, enorm_integral_le_lintegral_enorm, integral_eq_lintegral_of_nonneg_ae (all found; no L¹ Young inequality for convolution: only enorm_convolution_le / eLpNorm_convolution_integrand_le, which are pointwise)`
- `rg -n -l 'dimred_mbl_dt_cbm_sa_|codim1_rdo_dg_sp_mollifier_adjoint' SNAPSHOT (no match); grep -c 'dimred_mbl_dt_cbm_sa_' RUN/{dag.json,DAG.md,dag.mmd,issue-workers.json} (0 each); rg over lake-packages simongmt and GMT/ (no match)`
- `python3 scans of RUN/dag.json: selected node (depth 5, status decomposing, children []); twin cmcdt_cbm_smooth_approx (identical lean_statement, waiting-children) with unaccepted children cmcdt_cbm_sa_{mollify_adjoint,smoothed_field,grad_bound,mollify_l1}; nodes matching 'convolution|mollif|ContDiffBump' (accepted codim1_rdo_dg_sp_mollifier_adjoint is the only exact-type match usable here; codim1_zsl_pc_*, codim1_rdo_dg_bvc_*, codim1_rdo_dg_sp_mollify_variation, dgcr_stc_exists_normalized_mollifier have non-matching hypotheses)`
- `git show ae0277d4bed94a51b60fb4c7470fe259ed625e37:GMT/Ch07/Submission.lean (accepted proof, lines 463–543); cat RUN/nodes/…-reg-a9900b6593/{isolated-comparator-result,lean-audit-v1,parent-supplied-natural-proof.md} (passed: true; comparator_passed: true)`
- `cat RUN/nodes/…-cub-458697e68e/{decomposition-v1,decomposition-audit-v1}.json (twin split, audited acceptable); diff of the twin's and this node's parent-supplied natural proofs (same argument)`
- `sed /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py: _decompose (max_depth check), _existing_lean_name_problem, _accepted_checkpoint, _solve_children, _install_parent_supplied_child_handoff, _reference_use_problem; models.py ScopedDecomposition/Subproblem`
- `python3 -I gmt-compare.py contract_scope (replayed scope: open Filter Function Set MeasureTheory Metric; open scoped ENNReal Topology; namespace GMT.Ch07; open Poincare.SimonGMT.Chapter06; open Poincare.SimonGMT.Chapter03 (…); noncomputable section; end)`
- `lake env lean /tmp/dmsa/{Probe,Probe2,Challenge,Assembly,GradBound,SmoothedField,MollifyL1,Adjoint,Full}.lean (Full.lean: all five targets closed by exact Submission.X, axioms [propext, Classical.choice, Quot.sound])`
- `validate_lean_statement (runtime and verifier lean_contract.py) on all five strings (unchanged)`
- `sed -n 525,600p book/chapter-02.txt (Simon Ch. 2: symmetric mollifier lines 532–534, Lemma 2.5 lines 543–546, duality chain lines 573–596)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Dual.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-b5d5f611db/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-b5d5f611db/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-458697e68e/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-458697e68e/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-a9900b6593/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-a9900b6593/lean-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-a9900b6593/parent-supplied-natural-proof.md`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/models.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/dmsa/Challenge.lean`
- `/tmp/dmsa/Full.lean`
- `/tmp/dmsa/Assembly.lean`
- `/tmp/dmsa/GradBound.lean`
- `/tmp/dmsa/SmoothedField.lean`
- `/tmp/dmsa/MollifyL1.lean`
- `/tmp/dmsa/Adjoint.lean`

Pins match: project b4d606db and Mathlib 25730c7c. The snapshot contract is identical to the workspace Contract.lean and to the frozen Submission.lean. The snapshot project has no mollification or convolution lemma, and Mathlib has no L¹ Young inequality for convolution. So the L¹ approximate identity (mollify_l1), the admissible smoothed field (smoothed_field) and the localized gradient bound (grad_bound) are new obligations. Each is built from Mathlib lemmas that exist at the pinned revision: the convolution calculus in ContDiff/Convolution.lean and Analysis/Convolution.lean; ContDiffBump.normed and normed_neg in BumpFunction/Normed.lean; density in ContinuousMapDense.lean, whose import must be added; trace_smulRight; toDual_symm_apply; PiLp.norm_apply_le. The adjoint identity is not new. It is the comparator-accepted Submission.codim1_rdo_dg_sp_mollifier_adjoint (candidate ae0277d4; isolated comparator and machine-leaf audit passed), reused under its exact frozen name and type as the runtime's accepted-checkpoint rule allows. It applies because the parent uses the even normalized ContDiffBump, as the supplied proof suggests and Simon's symmetric mollifier is. The fresh names dimred_mbl_dt_cbm_sa_* collide with nothing. The twin cmcdt_cbm_sa_* children are unaccepted and owned by another parent, so their names cannot be shared. All five types elaborate in the exact comparator challenge form and pass validate_lean_statement. Complete scratch Lean proofs of every child, and of the exact parent type from the children, compile with only propext, Classical.choice and Quot.sound.
