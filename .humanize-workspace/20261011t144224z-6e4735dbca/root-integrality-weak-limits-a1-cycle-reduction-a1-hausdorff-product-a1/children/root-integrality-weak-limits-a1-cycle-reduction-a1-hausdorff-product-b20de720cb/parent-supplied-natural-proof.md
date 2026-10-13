# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.hausdorff_product-a1`
- Child DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.hausdorff_product-a1.piece_product-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source and scope. This is Steps 8–10 of the parent proof of iwl_cr_hausdorff_product_formula (node root.integrality_weak_limits-a1.cycle_reduction-a1.hausdorff_product-a1), for a single piece (G, B), together with the lift properties 9(i)–(iii).
- The Jacobian identity 9(iv) is taken from the sibling lemma iwl_cr_hp_lift_gram_det (key lift_gram_det; depends_on).
- Conclusion (1) also follows from the parametrized form, so the parent's assembly needs no σ-finiteness argument.

Library inputs (pinned Mathlib 25730c7c, SimonGMT 2b36630):
- (L1) Poincare.SimonGMT.Chapter02.weighted_area_formula_lipschitz_injOn (AreaLipschitz.lean:101). Hypotheses: f : E → F with LipschitzWith K f, s ⊆ E with MeasurableSet s and InjOn f s, and any w : F → [0,∞]. Conclusion:
  ∫⁻_{f '' s} w dμHE[finrank ℝ E] = ∫⁻_{x∈s} ENNReal.ofReal(areaJacobianAt f x)·w(f x) dvolume(x).
- (L3) measurable_areaJacobianAt (AreaApproximation.lean:44).
- Jacobian lemmas: areaJacobianAt_eq_normDet and areaJacobianAt_nonneg (Area.lean); LinearMap.normDet_sq_eq_det_gram (Mathlib/Analysis/InnerProductSpace/NormDet.lean:303); EuclideanSpace.basisFun (whose i-th vector is EuclideanSpace.single i 1).
- Volume and integration: PiLp.volume_preserving_ofLp and PiLp.volume_preserving_toLp (Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean:134,139); measurePreserving_piFinSuccAbove (Mathlib/MeasureTheory/Constructions/Pi.lean:806); MeasurePreserving.prod; MeasurePreserving.setLIntegral_comp_preimage; Measure.prod_restrict; lintegral_prod; Measurable.lintegral_prod_right'; setLIntegral_congr_fun; finrank_euclideanSpace_fin.

0. (Notation and coordinate facts.) Write e_k := EuclideanSpace.equiv (Fin k) ℝ and define Φ, π as in the statement. For v ∈ Eucl (m+1) put v_0 := e_{m+1}(v)(0) and tl(v) := e_m⁻¹(Fin.tail(e_{m+1} v)). Coordinatewise (Fin.cases, Fin.sum_univ_succ):
- π(Φ(s,x)) = x and Φ(s,x)_0 = s;
- ‖Φ(s,x)‖² = s² + ‖x‖² and Φ(s,x) − Φ(s′,x′) = Φ(s − s′, x − x′);
- ‖v‖² = v_0² + ‖tl v‖² and tl(v) − tl(v′) = tl(v − v′);
- v is determined by (v_0, tl v);
- (s,x) ↦ Φ(s,x) is continuous, and tl is continuous.
Put J(b) := ENNReal.ofReal(areaJacobianAt G b), which is Borel by (L3).

1. (Area formula in dimension m.) By (L1) with f := G, s := B and finrank ℝ (Eucl m) = m: for every u : Eucl P → [0,∞],
  ∫⁻_{G''B} u dH^m = ∫⁻_{b∈B} J(b)·u(G b) db.   (8.1)

2. (Parameter-side integrand.) H(s, b) := J(b)·g(Φ(s, G b)) is Borel on ℝ × Eucl m, because J is Borel, (s,b) ↦ Φ(s, G b) is continuous and g is Borel. Applying (8.1) with u := g(Φ(s, ·)) gives, for every s ∈ ℝ,
  ∫⁻_{b∈B} H(s, b) db = φ(s).   (∗)

3. (Conclusion (1).) s ↦ ∫⁻ H(s, b) d(volume⌞B)(b) is measurable by Measurable.lintegral_prod_right', since volume⌞B is s-finite and H is measurable. By (∗) this function equals φ, so φ is measurable.

4. (The lift.) Put G̃(v) := Φ(v_0, G(tl v)) and B̃ := tl⁻¹(B), which is Borel.
(i) Lipschitz. For v, v′, using step 0 and LipschitzWith K G,
  ‖G̃ v − G̃ v′‖² = (v_0 − v′_0)² + ‖G(tl v) − G(tl v′)‖² ≤ (v_0 − v′_0)² + K²‖tl v − tl v′‖² ≤ max(1,K)²·‖v − v′‖².
  Hence LipschitzWith (max 1 K) G̃.
(ii) Injectivity on B̃. If G̃ v = G̃ v′, comparing 0-th coordinates gives v_0 = v′_0, and applying π gives G(tl v) = G(tl v′). As tl v, tl v′ ∈ B and G is injective on B, tl v = tl v′. Hence v = v′.
(iii) Image: G̃ '' B̃ = {y : π y ∈ G''B}.
  - (⊆) π(G̃ v) = G(tl v) with tl v ∈ B.
  - (⊇) Suppose π(y) = G(b) with b ∈ B. Put v := e_{m+1}⁻¹(Fin.cons y_0 (e_m b)). Then v_0 = y_0 and tl v = b ∈ B, so v ∈ B̃, and G̃ v = Φ(y_0, G b) = Φ(y_0, π y) = y.
(iv) Jacobian. Let v ∈ B̃; then G is differentiable at tl v ∈ B.
  - The sibling lemma iwl_cr_hp_lift_gram_det, applied with Gt := G̃ (its defining identity holds by rfl), w := v and b := tl v, gives
    det(⟨DG̃(v)E_i, DG̃(v)E_j⟩)_{i,j} = det(⟨DG(tl v)e′_i, DG(tl v)e′_j⟩)_{i,j}.
  - For any f : Eucl k → Eucl Q and any x, areaJacobianAt f x = (fderiv ℝ f x).normDet. LinearMap.normDet_sq_eq_det_gram, applied with the orthonormal basis EuclideanSpace.basisFun (Fin k) ℝ, gives
    (areaJacobianAt f x)² = det(⟨Df(x)e_i, Df(x)e_j⟩)_{i,j}.
    Here basisFun i = EuclideanSpace.single i 1, the entries of Matrix.gram are inner products, and the coercion ℝ → ℝ is the identity.
  - Hence (areaJacobianAt G̃ v)² = (areaJacobianAt G (tl v))². Both are ≥ 0 (areaJacobianAt_nonneg; pow_left_inj₀), so areaJacobianAt G̃ v = areaJacobianAt G (tl v).

5. (Area formula in dimension m+1.) Apply (L1) with f := G̃, s := B̃, weight g and finrank ℝ (Eucl (m+1)) = m+1, and use (iii):
  ∫⁻_{{π ∈ G''B}} g dH^{m+1} = ∫⁻_{G̃''B̃} g dH^{m+1} = ∫⁻_{v∈B̃} ofReal(areaJacobianAt G̃ v)·g(G̃ v) dv = ∫⁻_{v∈B̃} H(v_0, tl v) dv.
The last equality uses (iv) and setLIntegral_congr_fun (B̃ is Borel): on B̃, ofReal(areaJacobianAt G̃ v)·g(G̃ v) = J(tl v)·g(Φ(v_0, G(tl v))) = H(v_0, tl v).

6. (Coordinate splitting.) Ψ(v) := (v_0, tl v) : Eucl (m+1) → ℝ × Eucl m is measure preserving from volume to volume.prod volume. It is the composite of:
- PiLp.volume_preserving_ofLp, from Eucl (m+1) to Fin (m+1) → ℝ;
- measurePreserving_piFinSuccAbove (fun _ => volume) 0, from Fin (m+1) → ℝ to ℝ × (Fin m → ℝ), f ↦ (f 0, f ∘ Fin.succAbove 0), where Fin.succAbove 0 = Fin.succ;
- (MeasurePreserving.id volume).prod PiLp.volume_preserving_toLp.
Moreover B̃ = Ψ⁻¹(univ ×ˢ B). Since univ ×ˢ B and H are Borel, MeasurePreserving.setLIntegral_comp_preimage gives
  ∫⁻_{v∈B̃} H(Ψ v) dv = ∫⁻_{univ ×ˢ B} H d(volume.prod volume).

7. (Tonelli.) (volume.prod volume)⌞(univ ×ˢ B) = volume.prod (volume⌞B) by Measure.prod_restrict and Measure.restrict_univ. Since H is measurable, lintegral_prod gives
  ∫⁻_{univ ×ˢ B} H = ∫⁻_ℝ ∫⁻_{b∈B} H(s, b) db ds = ∫⁻_ℝ φ(s) ds,
the last equality by (∗). Combined with steps 5–6, this is conclusion (2). ∎

Appendix (Lean, verified). The declaration below proves exactly this frozen statement. It was compiled against the frozen project:
- environment: commit d8d46c9, Lean v4.35.0-rc3, Mathlib 25730c7c, SimonGMT 2b36630;
- placement: inside GMT/Ch06/Submission.lean, in `namespace GMT.Ch06` after the contract's `noncomputable section … end`, where accepted `theorem Submission.…` declarations go (the check used a scratch file that imports GMT.Ch06.Submission and replays the contract's namespace and `open` commands);
- `#print axioms` reports [propext, Classical.choice, Quot.sound].
Extra imports to add at the top of GMT/Ch06/Submission.lean: Poincare.SimonGMT.Chapter02.AreaLipschitz, Poincare.SimonGMT.Chapter02.AreaApproximation, Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace. The proof uses no auxiliary top-level declarations. It refers to the sibling declaration Submission.iwl_cr_hp_lift_gram_det; the check compiled it with that sibling's appendix proof placed first.

theorem Submission.iwl_cr_hp_piece_product : ∀ (P m : ℕ) (G : Eucl m → Eucl P) (K : ℝ≥0) (B : Set (Eucl m)), LipschitzWith K G → MeasurableSet B → InjOn G B → (∀ b ∈ B, DifferentiableAt ℝ G b) → ∀ g : Eucl (P + 1) → ℝ≥0∞, Measurable g → Measurable (fun s : ℝ => ∫⁻ x in G '' B, g ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))) ∂(μHE[m] : Measure (Eucl P))) ∧ ∫⁻ y in {y | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ G '' B}, g y ∂(μHE[m + 1] : Measure (Eucl (P + 1))) = ∫⁻ s : ℝ, ∫⁻ x in G '' B, g ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))) ∂(μHE[m] : Measure (Eucl P)) := by
  intro P m G K B hG hB hinj hdiff g hg
  have hgram : ∀ {k Q : ℕ} (f : Eucl k → Eucl Q) (x : Eucl k),
      Poincare.SimonGMT.Chapter02.areaJacobianAt f x ^ 2 =
        (Matrix.of fun i j : Fin k => inner ℝ (fderiv ℝ f x (EuclideanSpace.single i 1))
          (fderiv ℝ f x (EuclideanSpace.single j 1))).det := by
    intro k Q f x
    rw [Poincare.SimonGMT.Chapter02.areaJacobianAt_eq_normDet]
    have h := LinearMap.normDet_sq_eq_det_gram (fderiv ℝ f x).toLinearMap
      (EuclideanSpace.basisFun (Fin k) ℝ)
    simp only [RCLike.ofReal_real_eq_id, id_eq] at h
    rw [h]
    congr 1
    ext i j
    simp [Matrix.gram]
  -- notation
  set Φ : ℝ → Eucl P → Eucl (P + 1) := fun s x =>
    (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))
    with hΦdef
  have hΦc : Continuous fun q : ℝ × Eucl P => Φ q.1 q.2 := by
    have : Continuous fun q : ℝ × Eucl P =>
        (Fin.cons q.1 (EuclideanSpace.equiv (Fin P) ℝ q.2) : Fin (P + 1) → ℝ) := by
      refine continuous_pi fun k => ?_
      refine Fin.cases ?_ (fun j => ?_) k
      · simpa using continuous_fst
      · simp only [Fin.cons_succ]
        exact (continuous_apply j).comp
          ((EuclideanSpace.equiv (Fin P) ℝ).continuous.comp continuous_snd)
    exact (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm.continuous.comp this
  have hfinm : Module.finrank ℝ (Eucl m) = m := finrank_euclideanSpace_fin
  have hfinm1 : Module.finrank ℝ (Eucl (m + 1)) = m + 1 := finrank_euclideanSpace_fin
  -- (8.1): the area formula in dimension m
  set J : Eucl m → ℝ≥0∞ := fun b =>
    ENNReal.ofReal (Poincare.SimonGMT.Chapter02.areaJacobianAt G b) with hJdef
  have harea_m : ∀ u : Eucl P → ℝ≥0∞,
      ∫⁻ x in G '' B, u x ∂(μHE[m] : Measure (Eucl P)) = ∫⁻ b in B, J b * u (G b) := by
    intro u
    have := Poincare.SimonGMT.Chapter02.weighted_area_formula_lipschitz_injOn hG hB hinj u
    rwa [hfinm] at this
  have hJm : Measurable J :=
    ENNReal.measurable_ofReal.comp (Poincare.SimonGMT.Chapter02.measurable_areaJacobianAt G)
  set H : ℝ × Eucl m → ℝ≥0∞ := fun q => J q.2 * g (Φ q.1 (G q.2)) with hHdef
  have hHm : Measurable H := by
    refine (hJm.comp measurable_snd).mul (hg.comp ?_)
    exact (hΦc.comp (continuous_fst.prodMk (hG.continuous.comp continuous_snd))).measurable
  have hinner : ∀ s : ℝ, ∫⁻ b in B, H (s, b) =
      ∫⁻ x in G '' B, g (Φ s x) ∂(μHE[m] : Measure (Eucl P)) := fun s =>
    (harea_m (fun x => g (Φ s x))).symm
  refine ⟨?_, ?_⟩
  · -- measurability of the inner integral
    have hmeas : Measurable fun s : ℝ => ∫⁻ b, H (s, b) ∂((volume : Measure (Eucl m)).restrict B) :=
      hHm.lintegral_prod_right'
    have heq : (fun s : ℝ => ∫⁻ b, H (s, b) ∂((volume : Measure (Eucl m)).restrict B)) =
        fun s => ∫⁻ x in G '' B, g (Φ s x) ∂(μHE[m] : Measure (Eucl P)) := funext hinner
    rw [heq] at hmeas
    exact hmeas
  · -- the lift
    set e1 := EuclideanSpace.equiv (Fin (m + 1)) ℝ with he1
    set tl : Eucl (m + 1) → Eucl m := fun v =>
      (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (e1 v)) with htldef
    have htlc : Continuous tl := by
      have : Continuous fun v : Eucl (m + 1) => Fin.tail (e1 v) :=
        continuous_pi fun i => (continuous_apply i.succ).comp e1.continuous
      exact (EuclideanSpace.equiv (Fin m) ℝ).symm.continuous.comp this
    set Gt : Eucl (m + 1) → Eucl (P + 1) := fun v => Φ (e1 v 0) (G (tl v)) with hGtdef
    set Bt : Set (Eucl (m + 1)) := tl ⁻¹' B with hBtdef
    have hBt : MeasurableSet Bt := hB.preimage htlc.measurable
    -- norm identities
    have hnormΦ : ∀ (s : ℝ) (x : Eucl P), ‖Φ s x‖ ^ 2 = s ^ 2 + ‖x‖ ^ 2 := by
      intro s x
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
      simp [hΦdef]
    have hΦsub : ∀ (s s' : ℝ) (x x' : Eucl P), Φ s x - Φ s' x' = Φ (s - s') (x - x') := by
      intro s s' x x'
      ext k
      refine Fin.cases ?_ (fun j => ?_) k <;> simp [hΦdef]
    have hnormw : ∀ v : Eucl (m + 1), ‖v‖ ^ 2 = (e1 v 0) ^ 2 + ‖tl v‖ ^ 2 := by
      intro v
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
      simp [htldef, he1, Fin.tail]
    have htlsub : ∀ v v' : Eucl (m + 1), tl v - tl v' = tl (v - v') := by
      intro v v'; ext k; simp [htldef, he1, Fin.tail]
    -- (i) Lipschitz
    have hGtL : LipschitzWith (max 1 K) Gt := by
      refine LipschitzWith.of_dist_le_mul fun v v' => ?_
      rw [dist_eq_norm, dist_eq_norm]
      have h1 : ‖Gt v - Gt v'‖ ^ 2 ≤ ((max 1 K : ℝ≥0) * ‖v - v'‖) ^ 2 := by
        simp only [hGtdef]
        rw [hΦsub, hnormΦ, mul_pow, hnormw (v - v')]
        have hK : ‖G (tl v) - G (tl v')‖ ≤ K * ‖tl v - tl v'‖ := by
          have := hG.dist_le_mul (tl v) (tl v')
          rwa [dist_eq_norm, dist_eq_norm] at this
        have hKm : (K : ℝ) ≤ (max 1 K : ℝ≥0) := by exact_mod_cast le_max_right 1 K
        have h1m : (1 : ℝ) ≤ (max 1 K : ℝ≥0) := by exact_mod_cast le_max_left 1 K
        have he0 : e1 v 0 - e1 v' 0 = e1 (v - v') 0 := by simp
        rw [he0, ← htlsub]
        have hA : (e1 (v - v') 0) ^ 2 ≤ ((max 1 K : ℝ≥0) : ℝ) ^ 2 * (e1 (v - v') 0) ^ 2 := by
          have : (1 : ℝ) ≤ ((max 1 K : ℝ≥0) : ℝ) ^ 2 := by nlinarith
          nlinarith [sq_nonneg (e1 (v - v') 0)]
        have hB2 : ‖G (tl v) - G (tl v')‖ ^ 2 ≤ ((max 1 K : ℝ≥0) : ℝ) ^ 2 * ‖tl v - tl v'‖ ^ 2 := by
          have h0 : 0 ≤ ‖G (tl v) - G (tl v')‖ := norm_nonneg _
          have h2 : ‖G (tl v) - G (tl v')‖ ≤ ((max 1 K : ℝ≥0) : ℝ) * ‖tl v - tl v'‖ :=
            hK.trans (mul_le_mul_of_nonneg_right hKm (norm_nonneg _))
          calc ‖G (tl v) - G (tl v')‖ ^ 2 ≤ (((max 1 K : ℝ≥0) : ℝ) * ‖tl v - tl v'‖) ^ 2 :=
                pow_le_pow_left₀ h0 h2 2
            _ = _ := by ring
        nlinarith
      have h0 : 0 ≤ ((max 1 K : ℝ≥0) : ℝ) * ‖v - v'‖ := by positivity
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) h0 two_ne_zero).mp h1
    -- coordinates of Gt
    have hπGt : ∀ v, (EuclideanSpace.equiv (Fin P) ℝ).symm
        (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ (Gt v))) = G (tl v) := by
      intro v; ext k; simp [hGtdef, hΦdef, Fin.tail]
    -- (ii) injectivity
    have hinjt : InjOn Gt Bt := by
      intro v hv v' hv' hvv
      have h0 : e1 v 0 = e1 v' 0 := by
        have := congrArg (fun y => (EuclideanSpace.equiv (Fin (P + 1)) ℝ) y 0) hvv
        simpa [hGtdef, hΦdef] using this
      have htl : tl v = tl v' := by
        have := congrArg (fun y => (EuclideanSpace.equiv (Fin P) ℝ).symm
          (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y))) hvv
        simp only [hπGt] at this
        exact hinj hv hv' this
      ext k
      refine Fin.cases ?_ (fun j => ?_) k
      · simpa [he1] using h0
      · have := congrArg (fun z => z j) htl
        simpa [htldef, he1, Fin.tail] using this
    -- (iii) image
    have himg : Gt '' Bt = {y | (EuclideanSpace.equiv (Fin P) ℝ).symm
        (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ G '' B} := by
      ext y
      constructor
      · rintro ⟨v, hv, rfl⟩
        simp only [mem_ofPred_eq, hπGt]
        exact ⟨tl v, hv, rfl⟩
      · rintro ⟨b, hb, hby⟩
        refine ⟨e1.symm (Fin.cons (EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0)
          (EuclideanSpace.equiv (Fin m) ℝ b)), ?_, ?_⟩
        · have : tl (e1.symm (Fin.cons (EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0)
              (EuclideanSpace.equiv (Fin m) ℝ b))) = b := by
            ext k; simp [htldef, he1, Fin.tail]
          simp only [hBtdef, mem_preimage, this]
          exact hb
        · have htlb : tl (e1.symm (Fin.cons (EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0)
              (EuclideanSpace.equiv (Fin m) ℝ b))) = b := by
            ext k; simp [htldef, he1, Fin.tail]
          simp only [hGtdef, htlb, hby]
          ext k
          refine Fin.cases ?_ (fun j => ?_) k
          · simp [hΦdef, he1]
          · simp [hΦdef, Fin.tail]
    -- (iv) Jacobians
    have hjac : ∀ v ∈ Bt, Poincare.SimonGMT.Chapter02.areaJacobianAt Gt v =
        Poincare.SimonGMT.Chapter02.areaJacobianAt G (tl v) := by
      intro v hv
      have h := Submission.iwl_cr_hp_lift_gram_det P m G Gt v (tl v) (fun v => rfl) rfl (hdiff _ hv)
      rw [← hgram, ← hgram] at h
      exact (pow_left_inj₀ (Poincare.SimonGMT.Chapter02.areaJacobianAt_nonneg _ _)
        (Poincare.SimonGMT.Chapter02.areaJacobianAt_nonneg _ _) two_ne_zero).mp h
    -- area formula in dimension m + 1
    have harea1 := Poincare.SimonGMT.Chapter02.weighted_area_formula_lipschitz_injOn hGtL hBt
      hinjt g
    rw [hfinm1, himg] at harea1
    rw [harea1]
    have hcongr : ∫⁻ v in Bt, ENNReal.ofReal (Poincare.SimonGMT.Chapter02.areaJacobianAt Gt v) *
        g (Gt v) = ∫⁻ v in Bt, H (e1 v 0, tl v) := by
      refine setLIntegral_congr_fun hBt (fun v hv => ?_)
      rw [hjac v hv]
    rw [hcongr]
    -- the coordinate split
    set Ψ : Eucl (m + 1) → ℝ × Eucl m := fun v => (e1 v 0, tl v) with hΨdef
    have hΨ : MeasurePreserving Ψ (volume : Measure (Eucl (m + 1)))
        ((volume : Measure ℝ).prod (volume : Measure (Eucl m))) := by
      have h1 := PiLp.volume_preserving_ofLp (ι := Fin (m + 1))
      have h2 := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => (volume : Measure ℝ)) 0
      have h3 := (MeasurePreserving.id (volume : Measure ℝ)).prod
        (PiLp.volume_preserving_toLp (ι := Fin m))
      have h := h3.comp (h2.comp h1)
      convert h using 1
      funext v
      simp only [Function.comp_apply, hΨdef, htldef, he1]
      ext <;> simp [MeasurableEquiv.piFinSuccAbove, Fin.tail]
    have hpre : Bt = Ψ ⁻¹' (univ ×ˢ B) := by
      ext v; simp [hBtdef, hΨdef]
    rw [hpre, hΨ.setLIntegral_comp_preimage (MeasurableSet.univ.prod hB) hHm,
      ← Measure.prod_restrict, Measure.restrict_univ,
      lintegral_prod H hHm.aemeasurable]
    exact lintegral_congr fun s => hinner s

## Key steps

1. (8.1): the injective Lipschitz area formula (L1) gives ∫⁻_{G(B)} u dH^m = ∫⁻_B J(b) u(G b) db for every u ≥ 0.
2. H(s,b) = J(b) g(Φ(s, G b)) is Borel, and ∫⁻_B H(s,·) = φ(s); Measurable.lintegral_prod_right' then makes φ measurable.
3. The lift G̃(v) = Φ(v_0, G(tl v)) is max(1,K)-Lipschitz and injective on B̃ = tl⁻¹(B), with G̃(B̃) = {π ∈ G(B)}.
4. The sibling Gram identity together with normDet² = det Gram (basisFun) gives areaJacobianAt G̃ v = areaJacobianAt G (tl v) on B̃.
5. (L1) in dimension m+1 turns the LHS into ∫⁻_{B̃} H(v_0, tl v) dv; the measure-preserving split Ψ(v) = (v_0, tl v), Tonelli and (∗) give ∫⁻_ℝ φ.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json  (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `python3: read /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-hausdorff-product-a1/{parent-child-handoff.json, parent-supplied-natural-proof.json, parent-supplied-natural-proof.md, parent-supplied-plan.md}`
- `python3: dag.json node statuses and lean_names (lpf_raf_*, lpf_countably_rectifiable_c1_cover, rectifiability_weighted_tangent_ae, iwl_cr_*); grep -r 'iwl_cr_hp_' over the run directory (no match)`
- `grep -n 'theorem hausdorffMeasure_apply|hausdorffMeasure_le_liminf_tsum|hausdorffMeasure_zero_singleton' Mathlib/MeasureTheory/Measure/Hausdorff.lean; grep 'euclideanHausdorffMeasure_def|euclideanHausdorffMeasure_zero|addHaarScalarFactor_volume_hausdorffMeasure_ne_zero' Mathlib/Geometry/Euclidean/Volume/Measure.lean (snapshot)`
- `sed -n 250,275p Mathlib/MeasureTheory/Function/Jacobian.lean (exists_partition_approximatesLinearOn_of_hasFDerivWithinAt); grep measurePreserving_piFinSuccAbove Mathlib/MeasureTheory/Constructions/Pi.lean; grep 'PiLp.volume_preserving_ofLp|PiLp.volume_preserving_toLp' Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean; grep det_succ_row_zero Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean; grep exists_measurable_subset_ae_eq Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `sed -n 290,320p Mathlib/Analysis/InnerProductSpace/NormDet.lean (LinearMap.normDet_sq_eq_det_gram, any Fintype index)`
- `grep -rn 'setLIntegral_comp_preimage|theorem prod_restrict|theorem lintegral_prod |Measurable.lintegral_prod_right'|MeasurePreserving.prod|LipschitzWith.prodMk' Mathlib/ (snapshot)`
- `grep -rn 'ediam_le|edist_le_ediam_of_mem|ediam_empty|ediam_le_of_forall_dist_le' Mathlib/Topology/EMetricSpace/Diam.lean Mathlib/Topology/MetricSpace/Bounded.lean (snapshot)`
- `simongmt: cat Chapter02/AreaLipschitz.lean; sed Chapter02/Area.lean, Chapter02/AreaParametrization.lean, Chapter02/AreaApproximation.lean; grep -rn 'theorem areaJacobianAt'; sed -n 28,80p Chapter03/Rectifiable.lean (CountablyRectifiable, CountablyRectifiable.mono)`
- `git show 2f36576:GMT/Ch06/Submission.lean (accepted rectifiability_weighted_tangent_ae, hparam/hpart piece construction); git show a46aa05:GMT/Ch06/Submission.lean and accepted candidate diffs (declaration conventions)`
- `verifier: gmt-compare.py contract_scope/child_modules and lean_contract.validate_lean_statement; python3 -I /tmp/hp_decomp/scripts/gen.py children_v1.json -> NodeChallenge files; lake env lean on each (all elaborate)`
- `lake env lean /tmp/hp_decomp/T0.lean (areaJacobianAt, weighted_area_formula_lipschitz_injOn and LinearMap.normDet_sq_eq_det_gram unknown under frozen imports; MeasurableSet.image_of_continuousOn_injOn, measurePreserving_piFinSuccAbove available)`
- `lake env lean /tmp/hp_decomp/scratch/{Assembly,JacBridge,LiftGram,PieceProduct,Pieces,Cyl}.lean and /tmp/hp_decomp/final/{All,Check_iwl_cr_hp_*}.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-hausdorff-product-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-hausdorff-product-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-hausdorff-product-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-hausdorff-product-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/speculative-prompt-v3.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/EMetricSpace/Diam.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaParametrization.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/hp_decomp/T0.lean`
- `/tmp/hp_decomp/scratch/Assembly.lean`
- `/tmp/hp_decomp/scratch/JacBridge.lean`
- `/tmp/hp_decomp/scratch/LiftGram.lean`
- `/tmp/hp_decomp/scratch/PieceProduct.lean`
- `/tmp/hp_decomp/scratch/Pieces.lean`
- `/tmp/hp_decomp/scratch/Cyl.lean`
- `/tmp/hp_decomp/final/All.lean`
- `/tmp/hp_decomp/final/Check_iwl_cr_hp_cylinder_null.lean`
- `/tmp/hp_decomp/final/Check_iwl_cr_hp_injective_pieces.lean`
- `/tmp/hp_decomp/final/Check_iwl_cr_hp_lift_gram_det.lean`
- `/tmp/hp_decomp/final/Check_iwl_cr_hp_piece_product.lean`

Snapshot: project d8d46c95, Mathlib 25730c7c; the frozen contract is Contract.lean, and Submission.lean is identical to it at the dispatch base.

Library inputs found (all with standard axioms):
- Mathlib supplies:
  - Hausdorff measure: hausdorffMeasure_apply (ediam form), hausdorffMeasure_zero_singleton, euclideanHausdorffMeasure_def/_zero, addHaarScalarFactor_volume_hausdorffMeasure_ne_zero;
  - pieces: exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (root namespace), MeasurableSet.image_of_continuousOn_injOn;
  - linear algebra: LinearMap.normDet_sq_eq_det_gram (any Fintype index, so EuclideanSpace.basisFun works), Matrix.det_succ_row_zero;
  - integration: measurePreserving_piFinSuccAbove, PiLp.volume_preserving_ofLp/toLp, MeasurePreserving.setLIntegral_comp_preimage, Measure.prod_restrict, lintegral_prod, Measurable.lintegral_prod_right', NullMeasurableSet.exists_measurable_subset_ae_eq;
  - diameters: Metric.ediam_le_of_forall_dist_le, edist_le_ediam_of_mem.
- SimonGMT 2b36630 supplies weighted_area_formula_lipschitz_injOn, area_image_compl_regularSet_eq_zero, measurableSet_areaRegularSet, measurable_areaJacobianAt, areaJacobianAt_eq_normDet/_nonneg, CountablyRectifiable (F_j : EuclideanSpace ℝ (Fin n) → E) and CountablyRectifiable.mono.
- Neither library has a Hausdorff product formula for rectifiable sets; only hausdorffMeasure_pi_real/prod_real exist.
- No DAG node supplies the needed lemmas with compatible types:
  - the lpf_raf_* area lemmas are chart/fibre-sum forms;
  - lpf_countably_rectifiable_c1_cover is only speculative-ready.
  So the split relies on library theorems only.

Scope check: areaJacobianAt, the SimonGMT area formula and LinearMap.normDet are NOT visible after `import GMT.Ch06.Submission` with the frozen imports. Hence lift_gram_det is stated with Gram determinants (Matrix.of … inner ℝ … EuclideanSpace.single). All four child statements elaborate in verifier-generated challenge modules.

Lean results:
- Scratch proofs of all four children with exactly the proposed types, and of the parent's exact frozen type from them, compile with only propext, Classical.choice and Quot.sound, and with zero warnings.
- Per-child compiles succeed with the minimal imports listed in each appendix.
- The accepted hparam/hpart code (commit 2f36576) was reused for injective_pieces.
- No name collisions with dag.json.
