# Parent-supplied natural-language proof

- Parent DAG node: `root.integral_compactness-a1.diagonal_blowup-a1`
- Child DAG node: `root.integral_compactness-a1.diagonal_blowup-a1.blowup_variation_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 4 and 6 of the parent proof, i.e. Simon 8.5.9 printed (4) ("(by (2)) ‖δW_i‖(B_R(0)) → 0"), for one blow-up; the Riesz and polar-representation facts are SimonGMT Varifold.firstVariationRieszMeasure_eq_norm and Varifold.isFirstVariationPolarRepresentation_riesz. Notation: G := Grassmannian N n; O := B°_R(0) = ball 0 R; σ(y) := ξ + t • y and η(z) := t⁻¹ • (z − ξ), mutually inverse homeomorphisms of ℝ^N (t ≠ 0); Φ(z, S) := (η z, S); V_{ξ,t} := rescaledMeasure V ξ t = ofReal(t⁻¹^n) • (V.measure).map Φ; c_t := t⁻¹^n · t ≥ 0; hV : V.HasLocallyBoundedFirstVariation. By hypothesis σ(O) ⊆ U, and σ(O) ⊆ closedBall ξ (t·R) because |σ(y) − ξ| = t|y|.

1. (The varifold W.) Let m := V_{ξ,t}.restrict (O ×ˢ univ). (a) O is open. (b) m(Oᶜ ×ˢ univ) = V_{ξ,t}((Oᶜ ×ˢ univ) ∩ (O ×ˢ univ)) = V_{ξ,t}(∅) = 0 (Measure.restrict_apply; Oᶜ ×ˢ univ is measurable). (c) Let K ⊆ O be compact. m(K ×ˢ univ) ≤ V_{ξ,t}(K ×ˢ univ) = ofReal(t⁻¹^n) · V.measure(Φ⁻¹(K ×ˢ univ)) (Measure.restrict_apply_le, Measure.map_apply with Φ measurable) and Φ⁻¹(K ×ˢ univ) = η⁻¹(K) ×ˢ univ = σ(K) ×ˢ univ. σ(K) is compact and σ(K) ⊆ σ(O) ⊆ U, so V.measure(σ(K) ×ˢ univ) ≠ ∞ (V.finite_on_compact) and m(K ×ˢ univ) ≠ ∞. Hence W := ⟨isOpen_ball, m, (b), (c)⟩ is an n-varifold on O with W.measure = V_{ξ,t}.restrict (O ×ˢ univ): the first assertion.

2. (Integrals against W.) If h : ℝ^N × G → ℝ is continuous and h = 0 off O ×ˢ univ, then ∫ h dW.measure = ∫ h dV_{ξ,t} (setIntegral_eq_integral_of_forall_compl_eq_zero) = t⁻¹^n · ∫ h(Φ z) dV.measure(z) (integral_smul_measure with (ofReal(t⁻¹^n)).toReal = t⁻¹^n, and integral_map; Φ measurable, h continuous).

3. (Pulled-back test fields.) Let X be a test field on O (Varifold.TestVectorField O: C¹, compact support, tsupport X ⊆ O) and Y := X ∘ η, Y(z) = X(t⁻¹ • (z − ξ)). (a) Y is C¹ (ContDiff.comp with the affine map η). (b) tsupport Y ⊆ η⁻¹(tsupport X) = σ(tsupport X) (tsupport_comp_subset_preimage; σ = η⁻¹ as homeomorphisms); σ(tsupport X) is compact, so Y has compact support, and σ(tsupport X) ⊆ σ(O) ⊆ U. Hence Y is a test field on U. (c) ‖Y z‖ = ‖X(η z)‖, so if ‖X‖ ≤ 1 everywhere then ‖Y‖ ≤ 1 everywhere; if tsupport X ⊆ O' then tsupport Y ⊆ σ(O'). So X.UnitSupportedIn O' implies Y.UnitSupportedIn σ(O'), where σ(O') = (fun y ↦ ξ + t • y) '' O'. (d) By the chain rule (fderiv_comp) and fderiv η z = t⁻¹ • id, fderiv Y z = t⁻¹ • fderiv X (η z); as clmToMatrix is linear, jacobian Y z = t⁻¹ • jacobian X (η z), hence for every S ∈ G: tangentialDivergence Y z S = trace(S.1 * jacobian Y z) = t⁻¹ · tangentialDivergence X (η z) S.

4. (First-variation scaling, printed (4).) For X, Y as in 3, h(y, S) := tangentialDivergence X y S is continuous (Varifold.continuous_tangentialDivergence) and vanishes off tsupport X ×ˢ univ ⊆ O ×ˢ univ (Varifold.support_tangentialDivergence_subset). By 2 and 3(d): δW(X) = ∫ h dW.measure = t⁻¹^n · ∫ tangentialDivergence X (η z) S dV(z, S) = t⁻¹^n · ∫ t · tangentialDivergence Y z S dV(z, S) = t⁻¹^n · t · δV(Y) = c_t · δV(Y) (integral_const_mul).

5. (Comparison of first-variation norms.) For every set O' ⊆ ℝ^N: firstVariationNormOn W O' ≤ ofReal(c_t) · firstVariationNormOn V (σ(O')). Indeed firstVariationNormOn W O' is the supremum over test fields X on O of [ofReal|δW(X)| if X.UnitSupportedIn O', else 0]. The terms 0 are trivially bounded. If X.UnitSupportedIn O', then Y from 3 satisfies Y.UnitSupportedIn σ(O') (3c), so ofReal|δV(Y)| ≤ firstVariationNormOn V (σ(O')) (Varifold.le_firstVariationNormOn), and by 4, ofReal|δW(X)| = ofReal(c_t·|δV(Y)|) = ofReal(c_t)·ofReal|δV(Y)| (ENNReal.ofReal_mul, c_t ≥ 0) ≤ ofReal(c_t)·firstVariationNormOn V (σ(O')). Take the supremum (iSup_le).

6. (W has locally bounded first variation.) Let O' be open with closure O' compact and closure O' ⊆ O. Since σ is a homeomorphism, σ(O') is open and closure σ(O') = σ(closure O'), which is compact and contained in σ(O) ⊆ U. By hV, firstVariationNormOn V (σ(O')) ≠ ∞, so by 5 firstVariationNormOn W O' ≤ ofReal(c_t) · firstVariationNormOn V (σ(O')) ≠ ∞. This proves W.HasLocallyBoundedFirstVariation (hW): the second assertion.

7. (‖δV‖ dominates the norm.) By definition of variationMeasure (dif_pos hV), variationMeasure V = V.firstVariationRieszMeasure hV, and Varifold.firstVariationNormOn_le_of_polarRepresentation applied to Varifold.isFirstVariationPolarRepresentation_riesz V hV gives firstVariationNormOn V A ≤ variationMeasure V A for every set A.

8. (‖δW‖ on all of O.) By 6, variationMeasure W = W.firstVariationRieszMeasure hW. For j ∈ ℕ let R_j := R·(j+1)/(j+2) (so 0 < R_j < R, R_j increasing, R_j → R) and O_j := ball 0 R_j. O_j is open and closure O_j = closedBall 0 R_j (R_j ≠ 0) is compact and contained in O, so Varifold.firstVariationRieszMeasure_eq_norm gives variationMeasure W O_j = firstVariationNormOn W O_j. By 5 and 7 and σ(O_j) ⊆ σ(O) ⊆ closedBall ξ (t·R): variationMeasure W O_j ≤ ofReal(c_t)·firstVariationNormOn V (σ(O_j)) ≤ ofReal(c_t)·variationMeasure V (σ(O_j)) ≤ ofReal(c_t)·variationMeasure V (closedBall ξ (t·R)). The O_j increase and ⋃_j O_j = O (for |y| < R choose j with R_j > |y|), so by continuity from below (Monotone.measure_iUnion) variationMeasure W O = ⨆_j variationMeasure W O_j ≤ ofReal(t⁻¹^n · t)·variationMeasure V (closedBall ξ (t·R)): the third assertion. ∎

Lean realization (informative; compiled during decomposition, complete, depending only on the axioms propext, Classical.choice, Quot.sound, against the pinned toolchain, placed in GMT/Ch08/Submission.lean inside `namespace GMT.Ch08` after `end Definitions`, i.e. in the frozen contract scope `open Set Filter MeasureTheory Metric`, `open scoped Topology ENNReal CompactlySupported Pointwise`, `open Poincare.SimonGMT`, `open Poincare.SimonGMT.Chapter08`; scratch copy /tmp/diagdecomp/FullCheck.lean):

set_option maxHeartbeats 1000000 in
theorem Submission.intcpt_diag_blowup_variation_bound : ∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (ξ : Euclidean N) (t R : ℝ), V.HasLocallyBoundedFirstVariation → 0 < t → 0 < R → (∀ y ∈ ball (0 : Euclidean N) R, ξ + t • y ∈ U) → ∃ W : Varifold N n (ball (0 : Euclidean N) R), W.measure = (rescaledMeasure V ξ t).restrict (ball (0 : Euclidean N) R ×ˢ (univ : Set (Grassmannian N n))) ∧ W.HasLocallyBoundedFirstVariation ∧ variationMeasure W (ball (0 : Euclidean N) R) ≤ ENNReal.ofReal (t⁻¹ ^ n * t) * variationMeasure V (closedBall ξ (t * R)) := by
  intro N n U V ξ t R hV ht hR hσU
  set O : Set (Euclidean N) := ball (0 : Euclidean N) R with hOdef
  have hOm : MeasurableSet O := measurableSet_ball
  -- the homeomorphism σ(y) = ξ + t • y, with inverse η(z) = t⁻¹ • (z - ξ)
  let σ : Euclidean N ≃ₜ Euclidean N :=
    { toFun := fun y ↦ ξ + t • y
      invFun := fun z ↦ t⁻¹ • (z - ξ)
      left_inv := by intro y; simp [smul_smul, ht.ne']
      right_inv := by intro z; simp [smul_smul, ht.ne']
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hσ : ∀ y, σ y = ξ + t • y := fun _ ↦ rfl
  have hσs : ∀ z, σ.symm z = t⁻¹ • (z - ξ) := fun _ ↦ rfl
  have hσO : σ '' O ⊆ U := by
    rintro _ ⟨y, hy, rfl⟩
    exact hσU y hy
  have hσball : σ '' O ⊆ closedBall ξ (t * R) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hσ, mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht]
    rw [hOdef, mem_ball, dist_zero_right] at hy
    exact mul_le_mul_of_nonneg_left hy.le ht.le
  have hΦc : Continuous (fun z : Euclidean N × Grassmannian N n ↦ (t⁻¹ • (z.1 - ξ), z.2)) := by
    fun_prop
  -- Step 1: the varifold W
  let W : Varifold N n O :=
    { isOpen_domain := isOpen_ball
      measure := (rescaledMeasure V ξ t).restrict (O ×ˢ (univ : Set (Grassmannian N n)))
      supported := by
        rw [Measure.restrict_apply (hOm.compl.prod MeasurableSet.univ)]
        have : (Oᶜ ×ˢ (univ : Set (Grassmannian N n))) ∩ (O ×ˢ (univ : Set (Grassmannian N n))) = ∅ := by
          ext z; simp
        rw [this, measure_empty]
      finite_on_compact := by
        intro K hK hKO
        apply ne_top_of_le_ne_top _ (Measure.restrict_apply_le _ _)
        rw [rescaledMeasure, Measure.smul_apply,
          Measure.map_apply hΦc.measurable (hK.measurableSet.prod MeasurableSet.univ), smul_eq_mul]
        apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        have he : (fun z : Euclidean N × Grassmannian N n ↦ (t⁻¹ • (z.1 - ξ), z.2)) ⁻¹'
            (K ×ˢ (univ : Set (Grassmannian N n))) = (σ '' K) ×ˢ (univ : Set (Grassmannian N n)) := by
          ext z
          simp only [mem_preimage, mem_prod, mem_univ, and_true]
          rw [σ.image_eq_preimage_symm]
          rfl
        rw [he]
        exact V.finite_on_compact _ (hK.image σ.continuous) ((image_mono hKO).trans hσO) }
  have hWmeas : W.measure = (rescaledMeasure V ξ t).restrict (O ×ˢ (univ : Set (Grassmannian N n))) := rfl
  refine ⟨W, rfl, ?_⟩
  -- Step 3: pulled-back test fields and the first-variation scaling (Step 4)
  have hη : ContDiff ℝ 1 (fun z : Euclidean N ↦ t⁻¹ • (z - ξ)) := by fun_prop
  have hfd : ∀ z : Euclidean N, fderiv ℝ (fun z : Euclidean N ↦ t⁻¹ • (z - ξ)) z =
      t⁻¹ • ContinuousLinearMap.id ℝ (Euclidean N) :=
    fun z ↦ (((hasFDerivAt_id z).sub_const ξ).const_smul t⁻¹).fderiv
  have hpull : ∀ X : Varifold.TestVectorField (N := N) O, ∃ Y : Varifold.TestVectorField (N := N) U,
      (∀ z, Y z = X (t⁻¹ • (z - ξ))) ∧ tsupport Y.toFun ⊆ σ '' tsupport X.toFun ∧
      W.firstVariation X = t⁻¹ ^ n * t * V.firstVariation Y := by
    intro X
    let Yf : Euclidean N → Euclidean N := fun z ↦ X (t⁻¹ • (z - ξ))
    have hYsupp : tsupport Yf ⊆ σ '' tsupport X.toFun := by
      rw [σ.image_eq_preimage_symm]
      exact tsupport_comp_subset_preimage X.toFun σ.symm.continuous
    let Y : Varifold.TestVectorField (N := N) U :=
      { toFun := Yf
        contDiff := X.contDiff.comp hη
        compactSupport :=
          (X.compactSupport.isCompact.image σ.continuous).of_isClosed_subset (isClosed_tsupport _)
            hYsupp
        support_subset := hYsupp.trans ((image_mono X.support_subset).trans hσO) }
    refine ⟨Y, fun z ↦ rfl, hYsupp, ?_⟩
    have hdiv : ∀ z (S : Grassmannian N n), Varifold.tangentialDivergence Y z S =
        t⁻¹ * Varifold.tangentialDivergence X (t⁻¹ • (z - ξ)) S := by
      intro z S
      have hX' : DifferentiableAt ℝ X.toFun (t⁻¹ • (z - ξ)) :=
        (X.contDiff.differentiable one_ne_zero) _
      have hcomp : fderiv ℝ Yf z = t⁻¹ • fderiv ℝ X.toFun (t⁻¹ • (z - ξ)) := by
        have h1 : fderiv ℝ (X.toFun ∘ fun z ↦ t⁻¹ • (z - ξ)) z =
            (fderiv ℝ X.toFun (t⁻¹ • (z - ξ))).comp (fderiv ℝ (fun z ↦ t⁻¹ • (z - ξ)) z) :=
          fderiv_comp z hX' ((hη.differentiable one_ne_zero) z)
        rw [show Yf = X.toFun ∘ fun z ↦ t⁻¹ • (z - ξ) from rfl, h1, hfd]
        ext v
        simp
      change Matrix.trace (S.1 * Varifold.clmToMatrix (fderiv ℝ Yf z)) =
        t⁻¹ * Matrix.trace (S.1 * Varifold.clmToMatrix (fderiv ℝ X.toFun (t⁻¹ • (z - ξ))))
      rw [hcomp, map_smul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    have hdivX_cont := Varifold.continuous_tangentialDivergence (n := n) X.contDiff
    have hvanish : ∀ z ∉ O ×ˢ (univ : Set (Grassmannian N n)),
        Varifold.tangentialDivergence X.toFun z.1 z.2 = 0 := by
      intro z hz
      by_contra hne
      exact hz (prod_mono X.support_subset subset_rfl
        (Varifold.support_tangentialDivergence_subset X.toFun hne))
    calc W.firstVariation X = ∫ z, Varifold.tangentialDivergence X.toFun z.1 z.2 ∂W.measure := rfl
      _ = ∫ z, Varifold.tangentialDivergence X.toFun z.1 z.2 ∂(rescaledMeasure V ξ t) := by
          rw [hWmeas]; exact setIntegral_eq_integral_of_forall_compl_eq_zero hvanish
      _ = t⁻¹ ^ n * ∫ z, Varifold.tangentialDivergence X.toFun (t⁻¹ • (z.1 - ξ)) z.2 ∂V.measure := by
          rw [rescaledMeasure, integral_smul_measure,
            integral_map hΦc.measurable.aemeasurable hdivX_cont.aestronglyMeasurable,
            ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
      _ = t⁻¹ ^ n * ∫ z, t * Varifold.tangentialDivergence Y z.1 z.2 ∂V.measure := by
          congr 1
          apply integral_congr_ae
          filter_upwards with z
          rw [hdiv]
          field_simp
      _ = t⁻¹ ^ n * t * V.firstVariation Y := by
          rw [integral_const_mul, mul_assoc]
          rfl
  -- Step 5: comparison of the first-variation norms
  have hc0 : (0 : ℝ) ≤ t⁻¹ ^ n * t := by positivity
  have hcmp : ∀ O' : Set (Euclidean N), W.firstVariationNormOn O' ≤
      ENNReal.ofReal (t⁻¹ ^ n * t) * V.firstVariationNormOn (σ '' O') := by
    intro O'
    classical
    generalize hB : V.firstVariationNormOn (σ '' O') = B
    unfold Varifold.firstVariationNormOn
    refine iSup_le fun X ↦ ?_
    split_ifs with hX
    · obtain ⟨Y, hYz, hYsupp, hδ⟩ := hpull X
      have hY : Y.UnitSupportedIn (σ '' O') := by
        refine ⟨hYsupp.trans (image_mono hX.1), fun z ↦ ?_⟩
        rw [hYz]
        exact hX.2 _
      have hle := Varifold.le_firstVariationNormOn V (σ '' O') Y hY
      rw [hB] at hle
      rw [hδ, abs_mul, abs_of_nonneg hc0, ENNReal.ofReal_mul hc0]
      exact mul_le_mul_of_nonneg_left hle zero_le
    · exact zero_le
  -- Step 6: W has locally bounded first variation
  have hW : W.HasLocallyBoundedFirstVariation := by
    intro O' hO' hO'c
    have hσO' : IsOpen (σ '' O') := σ.isOpenMap _ hO'
    have hcl : closure (σ '' O') = σ '' closure O' := (σ.image_closure O').symm
    have hfin := hV (σ '' O') hσO'
      ⟨by rw [hcl]; exact hO'c.1.image σ.continuous,
       by rw [hcl]; exact (image_mono hO'c.2).trans hσO⟩
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) (hcmp O')
  refine ⟨hW, ?_⟩
  -- Steps 7-8: the Riesz measures and the exhaustion of O
  have hvW : variationMeasure W = W.firstVariationRieszMeasure hW := by
    simp [variationMeasure, hW]
  have hvV : variationMeasure V = V.firstVariationRieszMeasure hV := by
    simp [variationMeasure, hV]
  have hpolar : ∀ A, V.firstVariationNormOn A ≤ variationMeasure V A := by
    intro A
    rw [hvV]
    exact V.firstVariationNormOn_le_of_polarRepresentation
      (V.isFirstVariationPolarRepresentation_riesz hV) A
  set r : ℕ → ℝ := fun j ↦ R * (((j : ℝ) + 1) / ((j : ℝ) + 2)) with hr
  have hrpos : ∀ j, 0 < r j := fun j ↦ by positivity
  have hrlt : ∀ j, r j < R := by
    intro j
    have : ((j : ℝ) + 1) / ((j : ℝ) + 2) < 1 := by rw [div_lt_one (by positivity)]; linarith
    calc r j = R * (((j : ℝ) + 1) / ((j : ℝ) + 2)) := rfl
      _ < R * 1 := mul_lt_mul_of_pos_left this hR
      _ = R := mul_one R
  have hrmono : Monotone r := by
    apply monotone_nat_of_le_succ
    intro j
    apply mul_le_mul_of_nonneg_left _ hR.le
    push_cast
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hrlim : Tendsto r atTop (𝓝 R) := by
    have h1 : Tendsto (fun m : ℕ ↦ ((m : ℝ) + 1) / ((m : ℝ) + 2)) atTop (𝓝 1) := by
      have := tendsto_natCast_div_add_atTop (𝕜 := ℝ) (1 : ℝ)
      have h2 : Tendsto (fun m : ℕ ↦ ((m + 1 : ℕ) : ℝ) / ((m + 1 : ℕ) + 1)) atTop (𝓝 1) :=
        this.comp (tendsto_add_atTop_nat 1)
      refine h2.congr (fun m ↦ ?_)
      push_cast
      ring_nf
    simpa using h1.const_mul R
  have hunion : O = ⋃ j, ball (0 : Euclidean N) (r j) := by
    ext y
    simp only [hOdef, mem_iUnion, mem_ball, dist_zero_right]
    constructor
    · intro hy
      exact (hrlim.eventually (lt_mem_nhds hy)).exists
    · rintro ⟨j, hj⟩
      exact hj.trans (hrlt j)
  have hmono : Monotone (fun j ↦ ball (0 : Euclidean N) (r j)) :=
    fun a b hab ↦ ball_subset_ball (hrmono hab)
  have hOj : ∀ j, variationMeasure W (ball (0 : Euclidean N) (r j)) ≤
      ENNReal.ofReal (t⁻¹ ^ n * t) * variationMeasure V (closedBall ξ (t * R)) := by
    intro j
    have hclj : closure (ball (0 : Euclidean N) (r j)) = closedBall 0 (r j) :=
      closure_ball _ (hrpos j).ne'
    rw [hvW, Varifold.firstVariationRieszMeasure_eq_norm W hW _ isOpen_ball
      ⟨by rw [hclj]; exact isCompact_closedBall _ _,
       by rw [hclj]; exact closedBall_subset_ball (hrlt j)⟩]
    refine (hcmp _).trans (mul_le_mul_of_nonneg_left ((hpolar _).trans (measure_mono ?_)) zero_le)
    exact (image_mono (ball_subset_ball (hrlt j).le)).trans hσball
  calc variationMeasure W O = variationMeasure W (⋃ j, ball (0 : Euclidean N) (r j)) :=
        congrArg _ hunion
    _ = ⨆ j, variationMeasure W (ball (0 : Euclidean N) (r j)) := hmono.measure_iUnion
    _ ≤ _ := iSup_le hOj

## Key steps

1. W := V_{ξ,t} ⌞ (B°_R(0) × G) is a varifold on B°_R(0): supported there and finite on K × G since σ(K) = ξ + tK is a compact subset of U.
2. For a test field X on B°_R(0), Y := X(t⁻¹(· − ξ)) is a test field on U with tsupport Y ⊆ σ(tsupport X) and div_S Y(z) = t⁻¹ div_S X(t⁻¹(z − ξ)).
3. First-variation scaling: δW(X) = t^{-n}·t·δV(Y) (rescaling formula for integrals).
4. Hence firstVariationNormOn W O' ≤ ofReal(t^{-n}t)·firstVariationNormOn V (σ(O')) for every O'.
5. σ maps O' ⊂⊂ B°_R(0) to σ(O') ⊂⊂ U, so W has locally bounded first variation.
6. Riesz: ‖δW‖(O_j) = firstVariationNormOn W O_j on balls O_j ↑ B°_R(0); polar representation: firstVariationNormOn V ≤ ‖δV‖; σ(O_j) ⊆ B_{tR}(ξ); continuity from below.

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum project/GMT/Ch08/Contract.lean (2e5cd5b3…, identical to workspace GMT/Ch08/Contract.lean and Submission.lean)`
- `rg -n 'theorem integral_smul_measure|theorem integral_map |theorem _root_.MeasurableEmbedding.integral_map|theorem setIntegral_eq_integral_of_forall_compl_eq_zero|theorem ofReal_integral_eq_lintegral_ofReal|theorem norm_setIntegral_le_of_norm_le_const|lemma Measure.integrableOn_of_bounded|theorem integrableOn_iff_integrable_of_support_subset|theorem Integrable.smul_measure|theorem integrable_map_measure|theorem eventually_all_finset|theorem tendsto_one_div_add_atTop_nhds_zero_nat|theorem tendsto_measure_iUnion_atTop|theorem _root_.Monotone.measure_iUnion|lemma Topology.IsInducing.isCompact_preimage|theorem Countable.exists_eq_range|theorem dist_apply_le_dist|theorem hasBasis_compactConvergenceUniformity|def toCocompactMap|theorem restrict_apply_self|theorem lintegral_indicator_one' mathlib/Mathlib`
- `grep -rn 'theorem exists_continuous_one_zero_of_isCompact|theorem Frequently.and_eventually|frequently_lt_of_liminf_lt|Filter.Tendsto.eventually_const_lt (to_dual eventually_lt_const)|theorem exists_countable_dense_subset|IsSeparable.exists_countable_dense_subset' mathlib/Mathlib`
- `grep -rn 'SeparableSpace C(|SecondCountableTopology C(' mathlib/Mathlib/Topology mathlib/Mathlib/Analysis (only ContinuousMap/SecondCountableSpace.lean)`
- `sed CompactlySupported.lean (CompactlySupportedContinuousMap.comp with →co, Mul/smul instances) and CocompactMap.lean (Homeomorph.toCocompactMap)`
- `grep -n in simongmt Chapter08/{Varifold,VarifoldConvergence,FirstVariationRiesz,FirstVariationBounds,TangentRescaling}.lean, Chapter04/WeightedBlowUp.lean, Chapter03/Rectifiable.lean: structure Varifold, domainMeasure, map_domainMeasure, RadonConverges, divergenceDomainTest, integral_divergenceDomainTest, TestVectorField, firstVariationNormOn, le_firstVariationNormOn, firstVariationNormOn_le_of_polarRepresentation, isFirstVariationPolarRepresentation_riesz, firstVariationRieszMeasure_eq_norm, tangentialDivergence, jacobian, clmToMatrix, support_tangentialDivergence_subset, continuous_tangentialDivergence, blowUpMeasure, blowUp, blowUpHomeomorph, blowUpMap, Grassmannian.instCompactSpace/instSecondCountableTopology`
- `lake env lean /tmp/diagdecomp/{Inst,Avail,Avail2}.lean (#check under import GMT.Ch08.Submission: SecondCountableTopology C(L,ℝ) and SeparableSpace C(L,ℝ) fail; Chapter04.blowUpHomeomorph and Varifold.blowUpMeasure unknown; Stone–Weierstrass, Urysohn, denseSeq, compact-convergence uniformity available)`
- `git show 2721e20337252ca8e1f6204843570bd04ba673c8:GMT/Ch08/Submission.lean (accepted Submission.radon_compactlySupported_countable_approx: inlined second countability of C(X,ℝ))`
- `python3 verifier/gmt-compare.py contract_scope(Contract.lean, GMT.Ch08.main_theorem); verifier/lean_contract.py validate_lean_statement on the 5 lean_statements`
- `lake env lean /tmp/diagdecomp/Chal_*.lean (comparator form) and /tmp/diagdecomp/FullCheck.lean (#print axioms)`
- `grep 'intcpt_diag_' in dag.json and nodes/*; git grep over all 107 local branches and remotes (no matches)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/UrysohnsLemma.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/ContinuousMap/SecondCountableSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/ContinuousMap/CompactlySupported.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/ContinuousMap/CocompactMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/ContinuousMap/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/UniformSpace/CompactConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Order/OrderClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Order/Filter/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Order/Filter/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/VarifoldConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/FirstVariationRiesz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/FirstVariationBounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/TangentRescaling.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/WeightedBlowUp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-08.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-diagonal-blowup-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1/decomposition-v1.json`
- `/tmp/diagdecomp/FullCheck.lean`
- `/tmp/diagdecomp/AssemblyFinal.lean`

Snapshot = project 63436ae6 + Mathlib 25730c7c; its Contract is byte-identical to the workspace Contract and Submission (sha256 2e5cd5b3…). Mathlib has no varifold theory, so the Ch. 8 objects come from the pinned SimonGMT package. SimonGMT already supplies the facts the children need: domainMeasure/map_domainMeasure and divergenceDomainTest, used for the transfer in child (1); RadonConverges; TestVectorField and firstVariationNormOn with le_firstVariationNormOn; the Riesz identities firstVariationRieszMeasure_eq_norm and isFirstVariationPolarRepresentation_riesz with firstVariationNormOn_le_of_polarRepresentation, used in child (4); and the Grassmannian compactness and second-countability instances. These are standard-axiom declarations reachable from `import GMT.Ch08.Submission`. TangentRescaling (blowUpMeasure, definitionally the contract's rescaledMeasure) and Chapter04.blowUpHomeomorph are NOT imported, so the children build the dilation homeomorphism directly. Every Mathlib lemma cited in the child proofs exists in the snapshot with matching hypotheses. The exception is second countability of C(X,ℝ), which sits in a non-imported file and is therefore inlined in child (3), as in the accepted radon_compactlySupported_countable_approx (commit 2721e203). The 5 child statements elaborate in comparator form, and the 5 children were proved completely in Lean with only propext, Classical.choice and Quot.sound. The parent assembly compiles from them plus the sibling rescaled_integral stub, with sorryAx only through that stub. No intcpt_diag_* name is reserved anywhere.
