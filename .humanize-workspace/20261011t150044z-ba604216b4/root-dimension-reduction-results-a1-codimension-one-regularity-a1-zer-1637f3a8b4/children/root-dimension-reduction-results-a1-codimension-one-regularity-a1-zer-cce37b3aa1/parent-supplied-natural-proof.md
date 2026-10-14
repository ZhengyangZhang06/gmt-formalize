# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.flat_limit-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.flat_limit-a1.graph_integral_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Steps D1–D4 of the supplied proof of the parent node codim1_zsl_flat_graph_limit (uniform convergence of the integrands from the C¹ convergence g_i → b, and convergence of the integrals from the L¹_loc convergence of the indicators supplied by BV compactness; Simon 7.5.3, chapter-07.txt lines 848–852, "converges in L¹_loc", and 7.5.5, lines 862–901), stated for an arbitrary continuous compactly supported field of m-covectors β in place of dω and for arbitrary dimensions m, k, P. Departure: the uniform continuity argument of D2 is made explicit through the multilinear difference bound ContinuousAlternatingMap.norm_image_sub_le and an ε-argument; no orthogonality of ι and ι' is needed.
Notation. h_i(w) := β(G_i(w))(DG_i(w)e_0, …, DG_i(w)e_{m−1}) and h(w) := β(ιw + ι'b)(ιe_0, …, ιe_{m−1}); L := L^m; |·| Euclidean and operator norms; for u : Fin m → ℝ^P, ‖u‖ := max_j |u_j| (the sup norm, pi_norm_le_iff_of_nonneg).
1. Constants. β is continuous with compact support, hence bounded, |β(y)| ≤ M for all y with some M ≥ 0 (Continuous.bounded_above_of_compact_support), and uniformly continuous (HasCompactSupport.uniformContinuous_of_continuous). B is measurable with L(B) < ∞ (measure_ball_lt_top). |e_j| = 1 and |ιe_j| = 1.
2. The limit integrand. |h(w)| ≤ |β(ιw + ι'b)|·∏_j |ιe_j| ≤ M (ContinuousAlternatingMap.le_opNorm), and h is continuous (w ↦ β(ιw + ι'b) is continuous and evaluation at the fixed family ιe is continuous, continuous_eval_const). Hence h is integrable on every set of finite measure (IntegrableOn.of_bound).
3. Derivative of G_i. If g_i is differentiable at w, then DG_i(w) = ι + ι'∘Dg_i(w) (derivative of the linear map ι plus chain rule for ι'∘g_i: HasFDerivAt.add, HasFDerivAt.comp), so DG_i(w)e_j = ιe_j + ι'(Dg_i(w)e_j).
4. Pointwise estimate. Let g_i be differentiable at w with ‖Dg_i(w)‖ ≤ 1; write T := Dg_i(w), y := G_i(w), y' := ιw + ι'b, u_j := DG_i(w)e_j, u'_j := ιe_j. Then |u_j| ≤ |ιe_j| + |ι'(Te_j)| ≤ 1 + ‖T‖ ≤ 2, |u'_j| = 1 and |u_j − u'_j| = |ι'(Te_j)| ≤ ‖T‖; so ‖u‖ ≤ 2, ‖u'‖ ≤ 1 and ‖u − u'‖ ≤ ‖T‖. Split h_i(w) − h(w) = [β(y)(u) − β(y')(u)] + [β(y')(u) − β(y')(u')]. The first bracket equals (β(y) − β(y'))(u) and is at most |β(y) − β(y')|·∏_j|u_j| ≤ 2^m·|β(y) − β(y')| in absolute value (le_opNorm). The second is at most |β(y')|·m·max(‖u‖, ‖u'‖)^{m−1}·‖u − u'‖ ≤ M·m·2^m·‖T‖ (ContinuousAlternatingMap.norm_image_sub_le, 2^{m−1} ≤ 2^m). Hence |h_i(w) − h(w)| ≤ 2^m·|β(G_i(w)) − β(ιw + ι'b)| + M·m·2^m·‖Dg_i(w)‖.
5. Uniform convergence on B. Let ε > 0. By uniform continuity choose δ > 0 with |β(y) − β(y')| < ε/(2·2^m) whenever |y − y'| < δ. Put X := M·m·2^m ≥ 0 and η := min(1, ε/(2(X + 1))) > 0. By (b) and by (c) with δ and with η, for all large i and all w ∈ B: g_i is differentiable at w, |G_i(w) − (ιw + ι'b)| = |ι'(g_i(w) − b)| = |g_i(w) − b| < δ, and ‖Dg_i(w)‖ < η ≤ 1. By step 4, |h_i(w) − h(w)| ≤ 2^m·ε/(2·2^m) + X·ε/(2(X + 1)) ≤ ε/2 + ε/2 = ε. Thus for every ε > 0, for all large i, |h_i − h| ≤ ε on B.
6. Measurability. For every i such that g_i is differentiable on B, h_i is a.e.-strongly measurable with respect to L restricted to B: G_i is continuous at each point of B, hence continuous on B and a.e.-strongly measurable for L⌞B (ContinuousOn.aestronglyMeasurable, B measurable); w ↦ DG_i(w) is measurable for an arbitrary map (measurable_fderiv), hence a.e.-strongly measurable (finite-dimensional target); and h_i(w) = Φ(G_i(w), DG_i(w)) with Φ(y, T) := β(y)(Te_0, …, Te_{m−1}), which is continuous on ℝ^P × L(ℝ^m, ℝ^P) (continuity of β and of T ↦ Te_j, and joint continuity of evaluation, continuous_eval). A continuous function of an a.e.-strongly measurable map is a.e.-strongly measurable. By (b) this holds for all large i.
7. Symmetric differences in ℝ. L((A_i Δ A) ∩ B) → 0 in [0, ∞] by (a), and toReal is continuous at 0 (ENNReal.tendsto_toReal), so the real numbers L((A_i Δ A) ∩ B) tend to 0.
8. Final estimate. Let ε > 0 and V := L(B) ∈ [0, ∞) (as a real number). By steps 5–7, for all large i simultaneously: |h_i − h| ≤ ε/(2(V + 1)) on B, |h_i − h| ≤ 1 on B, h_i is a.e.-strongly measurable for L⌞B, and L((A_i Δ A) ∩ B) < ε/(4(M + 1)). Fix such i and put s := A_i ∩ B, t := A ∩ B (measurable, of finite measure). h_i is integrable on s (a.e.-strongly measurable for L⌞s since s ⊆ B, and |h_i| ≤ |h_i − h| + |h| ≤ 1 + M on s; IntegrableOn.of_bound), and h is integrable on s and on t (step 2). (a) |∫_s h_i − ∫_s h| = |∫_s (h_i − h)| ≤ ε/(2(V + 1))·L(s) ≤ ε/(2(V + 1))·V < ε/2 (integral_sub, norm_setIntegral_le_of_norm_le_const, L(s) ≤ L(B)). (b) ∫_s h = ∫_{s∩t} h + ∫_{s∖t} h and ∫_t h = ∫_{t∩s} h + ∫_{t∖s} h (integral_inter_add_sdiff), so ∫_s h − ∫_t h = ∫_{s∖t} h − ∫_{t∖s} h. A point of s ∖ t lies in B and in A_i but not in A, and a point of t ∖ s lies in B and in A but not in A_i; so both sets lie in (A_i Δ A) ∩ B, and |∫_s h − ∫_t h| ≤ M·L(s∖t) + M·L(t∖s) ≤ 2M·L((A_i Δ A) ∩ B) ≤ 2(M + 1)·ε/(4(M + 1)) = ε/2. Hence |∫_{A_i∩B} h_i − ∫_{A∩B} h| < ε for all large i. As ε > 0 was arbitrary, the integrals converge (Metric.tendsto_nhds). ∎
Formalization note: unless this child is split further it is a machine leaf (one theorem appended inside `namespace GMT.Ch07` of GMT/Ch07/Submission.lean; no helper declaration, no import, no set_option). The tactic proof below was compiled on the pinned toolchain (Lean v4.35.0-rc3, Mathlib 25730c7c, simongmt 2b36630) in exactly that file context: the frozen Submission.lean, under default maxHeartbeats. It passes the workflow's leaf source-delta check (leaf_verification.check_source_delta), its frozen type passes lean_contract.validate_lean_statement and elaborates in the comparator's replayed contract scope, and #print axioms gives only propext, Classical.choice, Quot.sound. It may be used verbatim:
theorem Submission.codim1_zsl_fl_graph_integral_tendsto : ∀ (m k P : ℕ) (ι : Euclid m →ₗᵢ[ℝ] Euclid P) (ι' : Euclid k →ₗᵢ[ℝ] Euclid P) (b : Euclid k) (R : ℝ) (β : Euclid P → Covector (Euclid P) m) (gs : ℕ → Euclid m → Euclid k) (As : ℕ → Set (Euclid m)) (A : Set (Euclid m)), Continuous β → HasCompactSupport β → (∀ i, MeasurableSet (As i)) → MeasurableSet A → Tendsto (fun i => volume (symmDiff (As i) A ∩ ball (0 : Euclid m) R)) atTop (𝓝 0) → (∀ᶠ i in atTop, ∀ w ∈ ball (0 : Euclid m) R, DifferentiableAt ℝ (gs i) w) → (∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ w ∈ ball (0 : Euclid m) R, ‖gs i w - b‖ < ε ∧ ‖fderiv ℝ (gs i) w‖ < ε) → Tendsto (fun i => ∫ w in As i ∩ ball 0 R, β (ι w + ι' (gs i w)) (fun j => fderiv ℝ (fun w => ι w + ι' (gs i w)) w (EuclideanSpace.single j (1 : ℝ)))) atTop (𝓝 (∫ w in A ∩ ball 0 R, β (ι w + ι' b) (fun j => ι (EuclideanSpace.single j (1 : ℝ))))) := by
  intro m k P ι ι' b R β gs As A hβc hβs hAs hA hsymm hH1 hH2
  classical
  set B : Set (Euclid m) := ball (0 : Euclid m) R with hB
  have hBmeas : MeasurableSet B := measurableSet_ball
  have hBfin : volume B < ⊤ := measure_ball_lt_top
  obtain ⟨M, hM⟩ := hβc.bounded_above_of_compact_support hβs
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hβu : UniformContinuous β := hβs.uniformContinuous_of_continuous hβc
  set e : Fin m → Euclid m := fun j => EuclideanSpace.single j (1 : ℝ) with he
  have hej : ∀ j, ‖e j‖ = 1 := by intro j; simp [he]
  set Φ : Euclid P × (Euclid m →L[ℝ] Euclid P) → ℝ := fun p => β p.1 (fun j => p.2 (e j)) with hΦ
  have hΦc : Continuous Φ := by
    have h1 : Continuous fun p : Euclid P × (Euclid m →L[ℝ] Euclid P) => β p.1 :=
      hβc.comp continuous_fst
    have h2 : Continuous fun p : Euclid P × (Euclid m →L[ℝ] Euclid P) => (fun j => p.2 (e j)) :=
      continuous_pi fun j => (continuous_eval_const (e j)).comp continuous_snd
    exact continuous_eval.comp (h1.prodMk h2)
  set G : ℕ → Euclid m → Euclid P := fun i w => ι w + ι' (gs i w) with hG
  set H : ℕ → Euclid m → ℝ := fun i w => Φ (G i w, fderiv ℝ (G i) w) with hH
  set H' : Euclid m → ℝ := fun w => β (ι w + ι' b) (fun j => ι (e j)) with hH'
  change Tendsto (fun i => ∫ w in As i ∩ B, H i w) atTop (𝓝 (∫ w in A ∩ B, H' w))
  have hD : ∀ i w, DifferentiableAt ℝ (gs i) w →
      fderiv ℝ (G i) w = ι.toContinuousLinearMap + ι'.toContinuousLinearMap.comp (fderiv ℝ (gs i) w) := by
    intro i w hw
    have hι : HasFDerivAt (fun w => ι w) ι.toContinuousLinearMap w :=
      ι.toContinuousLinearMap.hasFDerivAt
    have hι' : HasFDerivAt (fun w => ι' (gs i w))
        (ι'.toContinuousLinearMap.comp (fderiv ℝ (gs i) w)) w :=
      ι'.toContinuousLinearMap.hasFDerivAt.comp w hw.hasFDerivAt
    exact (hι.add hι').fderiv
  have hH'b : ∀ w, ‖H' w‖ ≤ M := by
    intro w
    calc ‖H' w‖ ≤ ‖β (ι w + ι' b)‖ * ∏ j, ‖ι (e j)‖ := ContinuousAlternatingMap.le_opNorm _ _
      _ = ‖β (ι w + ι' b)‖ := by simp [hej]
      _ ≤ M := hM _
  have hH'c : Continuous H' := by
    have h1 : Continuous fun w : Euclid m => β (ι w + ι' b) :=
      hβc.comp (ι.continuous.add continuous_const)
    exact (continuous_eval_const (fun j => ι (e j))).comp h1
  -- pointwise estimate
  have hpt : ∀ i w, DifferentiableAt ℝ (gs i) w → ‖fderiv ℝ (gs i) w‖ ≤ 1 →
      ‖H i w - H' w‖ ≤ 2 ^ m * ‖β (G i w) - β (ι w + ι' b)‖ +
        M * m * 2 ^ m * ‖fderiv ℝ (gs i) w‖ := by
    intro i w hd hL1
    set L := fderiv ℝ (gs i) w with hL
    set u : Fin m → Euclid P := fun j => fderiv ℝ (G i) w (e j) with hueq
    set u' : Fin m → Euclid P := fun j => ι (e j) with hu'eq
    have hu : ∀ j, u j = ι (e j) + ι' (L (e j)) := by
      intro j
      simp [u, hD i w hd, L]
    have hunorm : ‖u‖ ≤ 2 := by
      rw [pi_norm_le_iff_of_nonneg (by norm_num)]
      intro j
      rw [hu j]
      calc ‖ι (e j) + ι' (L (e j))‖ ≤ ‖ι (e j)‖ + ‖ι' (L (e j))‖ := norm_add_le _ _
        _ = 1 + ‖L (e j)‖ := by rw [LinearIsometry.norm_map, LinearIsometry.norm_map, hej]
        _ ≤ 1 + ‖L‖ * ‖e j‖ := by gcongr; exact L.le_opNorm _
        _ ≤ 2 := by rw [hej]; linarith
    have hu'norm : ‖u'‖ ≤ 1 := by
      rw [pi_norm_le_iff_of_nonneg zero_le_one]
      intro j
      simp [u', hej]
    have hdiff : ‖u - u'‖ ≤ ‖L‖ := by
      rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
      intro j
      rw [Pi.sub_apply, hu j]
      simp only [u', add_sub_cancel_left, LinearIsometry.norm_map]
      calc ‖L (e j)‖ ≤ ‖L‖ * ‖e j‖ := L.le_opNorm _
        _ = ‖L‖ := by rw [hej, mul_one]
    have h1 : ‖β (G i w) u - β (ι w + ι' b) u‖ ≤ 2 ^ m * ‖β (G i w) - β (ι w + ι' b)‖ := by
      rw [← ContinuousAlternatingMap.sub_apply]
      calc _ ≤ ‖β (G i w) - β (ι w + ι' b)‖ * ∏ j, ‖u j‖ :=
            ContinuousAlternatingMap.le_opNorm _ _
        _ ≤ ‖β (G i w) - β (ι w + ι' b)‖ * 2 ^ m := by
          gcongr
          calc ∏ j, ‖u j‖ ≤ ∏ _j : Fin m, (2 : ℝ) :=
                Finset.prod_le_prod₀ (fun j _ => norm_nonneg _)
                  (fun j _ => (norm_le_pi_norm u j).trans hunorm)
            _ = 2 ^ m := by simp
        _ = _ := mul_comm _ _
    have h2 : ‖β (ι w + ι' b) u - β (ι w + ι' b) u'‖ ≤ M * m * 2 ^ m * ‖L‖ := by
      calc _ ≤ ‖β (ι w + ι' b)‖ * (Fintype.card (Fin m)) *
              (max ‖u‖ ‖u'‖) ^ (Fintype.card (Fin m) - 1) * ‖u - u'‖ :=
            ContinuousAlternatingMap.norm_image_sub_le _ _ _
        _ ≤ M * m * 2 ^ m * ‖L‖ := by
            rw [Fintype.card_fin]
            have hmax : max ‖u‖ ‖u'‖ ≤ 2 := max_le hunorm (hu'norm.trans (by norm_num))
            have hpow : (max ‖u‖ ‖u'‖) ^ (m - 1) ≤ 2 ^ m :=
              (pow_le_pow_left₀ (le_max_of_le_left (norm_nonneg _)) hmax _).trans
                (pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _))
            gcongr
            exact hM _
    have hsplit : H i w - H' w =
        (β (G i w) u - β (ι w + ι' b) u) + (β (ι w + ι' b) u - β (ι w + ι' b) u') := by
      simp only [H, H', Φ, u, u']
      ring
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add h1 h2)
  -- uniform convergence on B
  have hunif : ∀ ε > 0, ∀ᶠ i in atTop, ∀ w ∈ B, ‖H i w - H' w‖ ≤ ε := by
    intro ε hε
    obtain ⟨δ, hδ, hδβ⟩ := Metric.uniformContinuous_iff.1 hβu (ε / (2 * 2 ^ m)) (by positivity)
    set X : ℝ := M * m * 2 ^ m with hX
    have hX0 : 0 ≤ X := by positivity
    set η : ℝ := min 1 (ε / (2 * (X + 1))) with hη
    have hηpos : 0 < η := lt_min one_pos (by positivity)
    filter_upwards [hH1, hH2 δ hδ, hH2 η hηpos] with i hi1 hi2 hi3
    intro w hw
    have hd := hi1 w hw
    have hL1 : ‖fderiv ℝ (gs i) w‖ ≤ 1 := (hi3 w hw).2.le.trans (min_le_left _ _)
    have hLη : ‖fderiv ℝ (gs i) w‖ ≤ ε / (2 * (X + 1)) :=
      (hi3 w hw).2.le.trans (min_le_right _ _)
    have hβd : ‖β (G i w) - β (ι w + ι' b)‖ ≤ ε / (2 * 2 ^ m) := by
      rw [← dist_eq_norm]
      apply le_of_lt
      apply hδβ
      rw [dist_eq_norm]
      simp only [G]
      rw [add_sub_add_left_eq_sub, ← map_sub, LinearIsometry.norm_map]
      exact (hi2 w hw).1
    refine (hpt i w hd hL1).trans ?_
    have e1 : 2 ^ m * ‖β (G i w) - β (ι w + ι' b)‖ ≤ ε / 2 := by
      calc 2 ^ m * ‖β (G i w) - β (ι w + ι' b)‖ ≤ 2 ^ m * (ε / (2 * 2 ^ m)) := by gcongr
        _ = ε / 2 := by field_simp
    have e2 : X * ‖fderiv ℝ (gs i) w‖ ≤ ε / 2 := by
      calc X * ‖fderiv ℝ (gs i) w‖ ≤ X * (ε / (2 * (X + 1))) := by gcongr
        _ ≤ ε / 2 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
    linarith
  -- measurability
  have hHmeas : ∀ᶠ i in atTop, AEStronglyMeasurable (H i) (volume.restrict B) := by
    filter_upwards [hH1] with i hi
    have hGc : ContinuousOn (G i) B := fun w hw =>
      (ι.continuous.continuousAt.add
        (ι'.continuous.continuousAt.comp (hi w hw).continuousAt)).continuousWithinAt
    have h1 : AEStronglyMeasurable (G i) (volume.restrict B) := hGc.aestronglyMeasurable hBmeas
    have h2 : AEStronglyMeasurable (fderiv ℝ (G i)) (volume.restrict B) :=
      (measurable_fderiv ℝ (G i)).aestronglyMeasurable
    exact hΦc.comp_aestronglyMeasurable (h1.prodMk h2)
  -- the symmetric differences
  have hsymm' : Tendsto (fun i => (volume (symmDiff (As i) A ∩ B)).toReal) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsymm
    simpa [Function.comp_def] using this
  set VB : ℝ := (volume B).toReal with hVB
  have hVB0 : 0 ≤ VB := ENNReal.toReal_nonneg
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hunif (ε / (2 * (VB + 1))) (by positivity), hunif 1 one_pos, hHmeas,
    hsymm'.eventually (gt_mem_nhds (show (0 : ℝ) < ε / (4 * (M + 1)) by positivity))]
    with i hi1 hi1' hi2 hi3
  have hsB : As i ∩ B ⊆ B := inter_subset_right
  have hsfin : volume (As i ∩ B) < ⊤ := (measure_mono hsB).trans_lt hBfin
  have htfin : volume (A ∩ B) < ⊤ := (measure_mono inter_subset_right).trans_lt hBfin
  have hsmeas : MeasurableSet (As i ∩ B) := (hAs i).inter hBmeas
  have htmeas : MeasurableSet (A ∩ B) := hA.inter hBmeas
  have hHi_int : IntegrableOn (H i) (As i ∩ B) := by
    refine IntegrableOn.of_bound hsfin (hi2.mono_measure (Measure.restrict_mono hsB le_rfl)) (M + 1) ?_
    refine (ae_restrict_iff' hsmeas).2 (Eventually.of_forall fun w hw => ?_)
    have h := hi1' w hw.2
    calc ‖H i w‖ = ‖(H i w - H' w) + H' w‖ := by rw [sub_add_cancel]
      _ ≤ ‖H i w - H' w‖ + ‖H' w‖ := norm_add_le _ _
      _ ≤ 1 + M := add_le_add h (hH'b w)
      _ = M + 1 := add_comm _ _
  have hH'_int : ∀ s : Set (Euclid m), volume s < ⊤ → IntegrableOn H' s := fun s hs =>
    IntegrableOn.of_bound hs hH'c.aestronglyMeasurable M (Eventually.of_forall hH'b)
  -- first term
  have hT1 : ‖(∫ w in As i ∩ B, H i w) - ∫ w in As i ∩ B, H' w‖ ≤ ε / (2 * (VB + 1)) * VB := by
    rw [← integral_sub hHi_int (hH'_int _ hsfin)]
    refine (norm_setIntegral_le_of_norm_le_const hsfin fun w hw => hi1 w hw.2).trans ?_
    gcongr
    exact measureReal_mono hsB hBfin.ne
  -- second term
  have hT2 : ‖(∫ w in As i ∩ B, H' w) - ∫ w in A ∩ B, H' w‖ ≤
      2 * M * (volume (symmDiff (As i) A ∩ B)).toReal := by
    have e1 := integral_inter_add_sdiff htmeas (hH'_int _ hsfin)
    have e2 := integral_inter_add_sdiff hsmeas (hH'_int _ htfin)
    rw [inter_comm (A ∩ B)] at e2
    have hsub1 : (As i ∩ B) \ (A ∩ B) ⊆ symmDiff (As i) A ∩ B := by
      rintro w ⟨⟨hwA, hwB⟩, hw⟩
      exact ⟨Or.inl ⟨hwA, fun h => hw ⟨h, hwB⟩⟩, hwB⟩
    have hsub2 : (A ∩ B) \ (As i ∩ B) ⊆ symmDiff (As i) A ∩ B := by
      rintro w ⟨⟨hwA, hwB⟩, hw⟩
      exact ⟨Or.inr ⟨hwA, fun h => hw ⟨h, hwB⟩⟩, hwB⟩
    have hΔfin : volume (symmDiff (As i) A ∩ B) < ⊤ :=
      (measure_mono inter_subset_right).trans_lt hBfin
    have b1 : ‖∫ w in (As i ∩ B) \ (A ∩ B), H' w‖ ≤ M * (volume (symmDiff (As i) A ∩ B)).toReal := by
      refine (norm_setIntegral_le_of_norm_le_const ((measure_mono hsub1).trans_lt hΔfin)
        fun w _ => hH'b w).trans ?_
      gcongr
      exact measureReal_mono hsub1 hΔfin.ne
    have b2 : ‖∫ w in (A ∩ B) \ (As i ∩ B), H' w‖ ≤ M * (volume (symmDiff (As i) A ∩ B)).toReal := by
      refine (norm_setIntegral_le_of_norm_le_const ((measure_mono hsub2).trans_lt hΔfin)
        fun w _ => hH'b w).trans ?_
      gcongr
      exact measureReal_mono hsub2 hΔfin.ne
    have : (∫ w in As i ∩ B, H' w) - ∫ w in A ∩ B, H' w =
        (∫ w in (As i ∩ B) \ (A ∩ B), H' w) - ∫ w in (A ∩ B) \ (As i ∩ B), H' w := by
      linarith
    rw [this]
    calc _ ≤ ‖∫ w in (As i ∩ B) \ (A ∩ B), H' w‖ + ‖∫ w in (A ∩ B) \ (As i ∩ B), H' w‖ :=
          norm_sub_le _ _
      _ ≤ _ := by linarith
  rw [dist_eq_norm]
  have hsum : (∫ w in As i ∩ B, H i w) - ∫ w in A ∩ B, H' w =
      ((∫ w in As i ∩ B, H i w) - ∫ w in As i ∩ B, H' w) +
        ((∫ w in As i ∩ B, H' w) - ∫ w in A ∩ B, H' w) := by ring
  rw [hsum]
  have hlt1 : ε / (2 * (VB + 1)) * VB < ε / 2 := by
    rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hlt2 : 2 * M * (volume (symmDiff (As i) A ∩ B)).toReal ≤ ε / 2 := by
    have h3 : (volume (symmDiff (As i) A ∩ B)).toReal < ε / (4 * (M + 1)) := hi3
    have h4 : 0 ≤ (volume (symmDiff (As i) A ∩ B)).toReal := ENNReal.toReal_nonneg
    calc 2 * M * (volume (symmDiff (As i) A ∩ B)).toReal
        ≤ 2 * (M + 1) * (volume (symmDiff (As i) A ∩ B)).toReal := by gcongr; linarith
      _ ≤ 2 * (M + 1) * (ε / (4 * (M + 1))) := by gcongr
      _ = ε / 2 := by field_simp; ring
  calc _ ≤ _ := norm_add_le _ _
    _ < ε := by linarith

## Key steps

1. β is bounded by M and uniformly continuous; the limit integrand h(w) = β(ιw + ι'b)(ιe) is continuous with |h| ≤ M.
2. Where g_i is differentiable at w with ‖Dg_i(w)‖ ≤ 1, DG_i(w) = ι + ι'∘Dg_i(w) and the multilinear estimates give |h_i(w) − h(w)| ≤ 2^m|β(G_i(w)) − β(ιw + ι'b)| + M·m·2^m·‖Dg_i(w)‖.
3. With the C¹ hypothesis and uniform continuity of β, sup_B |h_i − h| → 0.
4. For large i, h_i is a.e.-strongly measurable on B (G_i continuous on B, measurable_fderiv, Φ continuous), hence integrable on A_i ∩ B.
5. |∫_{A_i∩B} h_i − ∫_{A∩B} h| ≤ L(B)·sup_B|h_i − h| + 2M·L((A_i Δ A) ∩ B) → 0.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; sha256sum GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `python3 scans of dag.json: the selected node (status, message, children, descendants by id prefix); lean_name lookup of the 6 child names and of codim1_zsl_perimeter_compactness; byte equality of the 2 reused lean_statements and statements with decomposition-v1.json; raw count of 'codim1_zsl_fl_'; scan of nodes/*/*.json outside this node for 'codim1_zsl_fl_'`
- `python3 dump of this node's decomposition-v1.json, decomposition-audit-v1.json, decomposition-review-receipt-v1.json, decomposition-scope-v1.json and parent-child-handoff.json; issue-workers.json entries for issue 5038`
- `git log --all --oneline -S'codim1_zsl_fl_' -- 'GMT/*.lean' (0 commits); positive control git log --all --oneline -S'dgcr_bwd_graph_pullback_extDeriv' -- 'GMT/*.lean'`
- `git show dcc3f4b7fc0f6beb359e7585fbca8b266cc0f38f:GMT/Ch07/Submission.lean; git show 42e24164cfdc5445c7426ab7ee11003f8faee961:GMT/Ch07/Submission.lean (the accepted reused blocks)`
- `grep -n 'structure TestFormOn|def IsTestForm|theorem exteriorDerivative_isTestForm|theorem tsupport_exteriorDerivative_subset|def exteriorDerivative|def covectorEuclideanNorm|def affinePullbackForm|theorem exteriorDerivative_affinePullbackForm|theorem affinePullbackForm_isSmoothForm' .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/*.lean`
- `grep -n 'theorem setIntegral_eq_of_subset_of_forall_sdiff_eq_zero|Bornology.IsBounded.subset_ball_lt|theorem norm_add_sq_real' local-references/123e8435b4a2469b/mathlib/Mathlib; grep -rl 'map_euclideanHausdorffMeasure|euclideanHausdorffMeasure_eq_volume' local-references/123e8435b4a2469b/mathlib/Mathlib; diff of snapshot vs .lake/packages/mathlib Bochner/Set.lean (identical)`
- `lake env lean /tmp/fl-v2-decomp/lean/Check2.lean (frozen Submission.lean + accepted dcc3f4b7/42e24164 blocks + sorry placeholder for codim1_zsl_perimeter_compactness + verbatim code of the 4 new children + selected theorem; #print axioms of all 7)`
- `lake env lean /tmp/fl-v2-decomp/lean/Types.lean (import GMT.Ch07.Submission + gmt-compare.contract_scope replay; the 6 child types and the selected type as comparator-style challenges)`
- `lake env lean /tmp/fl-v2-decomp/lean/ContractAssembly2.lean (selected type proved from hypotheses with the frozen perimeter_bound, bv_compactness, graph_integral_limit and isometric_transport types; #print axioms)`
- `python3: lean_contract.validate_lean_statement on the 6 types; leaf_verification.check_source_delta on the 4 new children inserted into GMT/Ch07/Submission.lean; models.ScopedDecomposition validation of this response`
- `sed -n 840,860p book/chapter-07.txt (Simon 7.5.3: by (1) and 5.2 and the BV Compactness 2.6 of Ch. 2 a subsequence converges in L¹_loc)`
- `grep -l '"github_selected_issue": 5038,' .humanize/swarm-configs/* and their max_nodes/max_depth/max_children (cffb5a36…: max_nodes 1000, 08:33Z; 5261729…: max_nodes 5000, 11:17Z); mtime ranges of configs by max_nodes value`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/issue-workers.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-1637f3a8b4/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-1637f3a8b4/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-1637f3a8b4/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-1637f3a8b4/decomposition-scope-v1.json`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/lean_contract.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/models.py`
- `/runtime/flows/gmt-claude-d253855dab51/scripts/gmt-compare.py`
- `/tmp/fl-v2-decomp/lean/Check2.lean`
- `/tmp/fl-v2-decomp/lean/Types.lean`
- `/tmp/fl-v2-decomp/lean/ContractAssembly2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/swarm-configs/cffb5a36c88f487d9fb784e09cf6981b.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/swarm-configs/5261729094924bd1900f1bef36365ca3.json`

Pins match. The snapshot manifest records project b4d606db and Mathlib 25730c7c, equal to the workspace HEAD and .lake/packages/mathlib; simongmt is 2b366308. The snapshot Contract.lean and the workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).
DAG state. The selected node is 'decomposing' at 'subproblem decomposition attempt 2' and has no children or descendants. Its v1 split passed the independent review (all six nodes acceptable, no required changes) but was never activated. The cause is not recorded. The first worker's config had max_nodes 1000 while the DAG approached 1000 nodes; the current worker's config has max_nodes 5000. The four codim1_zsl_fl_* names occur nowhere in dag.json (1083 nodes at 12:11Z), in other nodes' files, in GMT/, in simongmt or in git history. dgcr_bwd_coordinate_covector (dcc3f4b7) and dgcr_bwd_graph_pullback_extDeriv (42e24164) are accepted, and their DAG types and statements are byte-identical to the reused subproblems.
Library. The SimonGMT definitions used by the children check out: TestFormOn is the submodule of IsTestForm forms supported in U; exteriorDerivative is extDeriv; exteriorDerivative_isTestForm and tsupport_exteriorDerivative_subset hold; covectorEuclideanNorm is the root of the sum of squared strictly-increasing coordinate coefficients; and affinePullbackForm commutes with d. The snapshot Mathlib contains every lemma the assembly cites: setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (Bochner/Set.lean:466), Bornology.IsBounded.subset_ball_lt (Bounded.lean:105), norm_add_sq_real (InnerProductSpace/Basic.lean:411), and the Hausdorff isometry lemmas (Geometry/Euclidean/Volume/Measure.lean).
Lean (pinned toolchain v4.35.0-rc3). Check2.lean compiles: each of the six children depends only on propext, Classical.choice and Quot.sound, and the selected theorem adds sorryAx solely through the bv_compactness placeholder. ContractAssembly2.lean proves the selected type from the four frozen contract types alone, with only the three standard axioms. Types.lean elaborates all seven types in the comparator's replayed contract scope. validate_lean_statement and check_source_delta accept every child.
Source. Simon 7.5.3 (book/chapter-07.txt lines 852–856) obtains the L¹_loc subsequence from the BV Compactness 2.6 of Ch. 2, which is the sibling bv_compactness.
