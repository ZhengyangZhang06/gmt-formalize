# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.l1_constant-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 11 of the parent proof ((a) uniform convergence of u_k∗φ_{s₀}, (b) the BV estimate with the forms ε_j, (c) the combination). Uses the siblings interior_form, mollified_uniform and bv_estimate.
1. (Test functions as top forms.) Let dy ∈ Λⁿ(ℝⁿ) be the determinant of the standard basis (the alternating map (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det, continuous by Continuous.matrix_det, hence a ContinuousAlternatingMap), so dy(e) = 1. For b smooth with compact support and tsupport b ⊆ U, ω_b(y) := b(y)·dy is a test n-form on U (smooth, compact support, tsupport ω_b ⊆ tsupport b ⊆ U) with ω_b(y)(e) = b(y). Hence ∫_U u_k b = Y_k(ω_b) → c∫b.
2. (Mollifier.) Put s := R/4 (so 0 < s < R and 2s < R). Let φ ≥ 0 be smooth with tsupport φ ⊆ B_s(0) and ∫φ = 1: a ContDiffBump centred at 0 with rIn = s/4, rOut = s/2 (smooth, values in [0, 1], equal to 1 on closedBall(0, s/4), tsupport = closedBall(0, s/2)) divided by its integral, which is positive (continuous, ≥ 0 and = 1 on a ball of positive measure; integral_pos_iff_support_of_nonneg).
3. (Uniform convergence of the mollifications.) By mollified_uniform (n, R, s, c, Λ, φ, u_k; s < R; integrability and the eventual Λ-bound; step 1), w_k(x) := ∫_U u_k(y)φ(x − y)dy → c∫φ = c uniformly on closedBall(0, R).
4. (Variation bound.) Let V_k := (M_U(∂Y_k)).toReal ≥ 0. As M_U(∂Y_k) → 0 there is k₀ with M_U(∂Y_k) < ∞ for k ≥ k₀, and V_k → 0 (ENNReal.tendsto_toReal at 0). Claim: for k ≥ k₀, every smooth compactly supported f with tsupport f ⊆ U, every z ∈ ℝⁿ and every M with |f| ≤ M: |∫_U u_k(y)Df(y)(z)dy| ≤ V_k‖z‖M. Proof: by interior_form take ε_z ∈ Λ^d(ℝⁿ) with |ε_z| ≤ ‖z‖ and d(f·ε_z)(y)(e) = Df(y)(z) for every y (f is differentiable everywhere). γ := f·ε_z is a test d-form on U (smooth, tsupport γ ⊆ tsupport f ⊆ U), and dγ is a test n-form on U (exteriorDerivativeTestOn), so by the representation of Y_k: ∂Y_k(γ) = Y_k(dγ) = ∫_U u_k(y)dγ(y)(e)dy = ∫_U u_k(y)Df(y)(z)dy. Pointwise |γ(y)| = |f(y)|·|ε_z| ≤ M‖z‖ (covectorEuclideanNorm (a·α) = |a|·|α|; M ≥ 0 since |f| ≤ M). For every η > 0 the forms ±(M‖z‖ + η)⁻¹γ have coefficient norm ≤ 1 and tsupport ⊆ U, so they belong to massAdmissibleOn U d U and ofReal(±(M‖z‖ + η)⁻¹∂Y_k(γ)) ≤ M_U(∂Y_k) (GeometricCurrentOn.le_massOn, linearity of ∂Y_k); since M_U(∂Y_k) < ∞ this gives |∂Y_k(γ)| ≤ (M‖z‖ + η)V_k, and letting η → 0, |∂Y_k(γ)| ≤ V_k‖z‖M.
5. (BV estimate.) For k ≥ k₀, bv_estimate (n, R, s, V_k, φ, u_k; 2s < R, V_k ≥ 0, φ ≥ 0, tsupport φ ⊆ B_s(0), ∫φ = 1, u_k integrable on U, step 4) gives ∫_{B_R}|u_k − w_k| ≤ sV_k.
6. (Conclusion.) For k ≥ k₀: |u_k − c| ≤ |u_k − w_k| + |w_k − c| pointwise, all functions involved are integrable on B_R(0) (u_k ∈ L¹(B_R), w_k continuous hence bounded on the bounded ball), so ∫_{B_R}|u_k − c| ≤ ∫_{B_R}|u_k − w_k| + ∫_{B_R}|w_k − c| ≤ sV_k + volume(B_R(0)).toReal·sup_{x ∈ closedBall(0,R)}|w_k(x) − c|. Both terms tend to 0 (steps 3–4) and the left side is ≥ 0, so ∫_{B_R(0)}|u_k − c| → 0 (squeeze_zero' / tendsto_of_tendsto_of_tendsto_of_le_of_le'). ∎

Verified Lean realization (supplementary). The single theorem below was compiled with `lake env lean` (Lean v4.35.0-rc3; project b4d606db, Mathlib 25730c7c, SimonGMT 2b366308) in a file that imports GMT.Ch07.Submission and reopens the frozen contract's namespace GMT.Ch07 with its `open`s, with the sibling dependencies Submission.cbr_ci_pw_interior_product_form (interior_form), Submission.cbr_ci_pw_mollified_tendstoUniformlyOn (mollified_uniform) and Submission.cbr_ci_pw_bv_mollifier_estimate (bv_estimate) declared by their exact frozen Lean types: no errors and no warnings; `#count_heartbeats` reports 59551 heartbeats, below the default maxHeartbeats 200000 (no set_option); `#print axioms` lists propext, Classical.choice, Quot.sound and these three siblings; inserted before main_theorem in GMT/Ch07/Submission.lean it passes the runtime's leaf source-delta check (one appended theorem under its exact name; no helper declaration, import, set_option or placeholder). Its local lemmas aux_* are proved inline and correspond to the numbered steps above: aux_exists_det_covector and aux_scalar_test_tendsto are step 1 (a top covector dy with dy(e_0, …, e_d) = 1, the test forms b·dy, and ∫_U u_k b → c∫b); aux_exists_normalized_mollifier is step 2 (with r := R/8, so support φ ⊆ B_{R/8}(0) and tsupport φ ⊆ B_{R/4}(0) = B_s(0)); step 3 calls the sibling mollified_uniform; aux_abs_apply_le_massOn (|T(ω)| ≤ r·M_W(T) when tsupport ω ⊆ W and |ω| ≤ r), aux_norm_props (|t·α| = |t||α| and the other seminorm properties of the coefficient norm) and aux_boundary_variation_bound are step 4, with ε_z from the sibling interior_form; step 5 calls the sibling bv_estimate; aux_l1_squeeze_of_mollified is step 6. It may be appended verbatim as the single leaf theorem:
```lean
theorem Submission.dmcbr_ci_pw_density_l1_tendsto_const : ∀ (d : ℕ) (R c Λ : ℝ) (Y : ℕ → GeometricCurrentOn (ball (0 : Euclid (d + 1)) (2 * R)) (d + 1)) (u : ℕ → Euclid (d + 1) → ℝ), 0 < R → (∀ k, IntegrableOn (u k) (ball 0 (2 * R))) → (∀ᶠ k in atTop, ∫ y in ball 0 (2 * R), |u k y| ≤ Λ) → (∀ (k : ℕ) (ω : TestFormOn (ball (0 : Euclid (d + 1)) (2 * R)) (d + 1)), Y k ω = ∫ y in ball 0 (2 * R), u k y * (ω : DifferentialForm (Euclid (d + 1)) (d + 1)) y (fun i => EuclideanSpace.single i (1 : ℝ))) → Tendsto (fun k => (Y k).boundary.massOn (ball 0 (2 * R))) atTop (𝓝 0) → (∀ ω : TestFormOn (ball (0 : Euclid (d + 1)) (2 * R)) (d + 1), Tendsto (fun k => Y k ω) atTop (𝓝 (c * ∫ y, (ω : DifferentialForm (Euclid (d + 1)) (d + 1)) y (fun i => EuclideanSpace.single i (1 : ℝ))))) → Tendsto (fun k => ∫ y in ball 0 R, |u k y - c|) atTop (𝓝 0) := by
  have aux_exists_det_covector : ∀ n : ℕ, ∃ δ : Covector (Euclid n) n, δ (fun i => EuclideanSpace.single i (1 : ℝ)) = 1 := by
    intro n
    have : Fact (Module.finrank ℝ (Euclid n) = n) := ⟨finrank_euclideanSpace_fin⟩
    let b := EuclideanSpace.basisFun (Fin n) ℝ
    let o : Orientation ℝ (Euclid n) (Fin n) := b.toBasis.orientation
    refine ⟨o.volumeForm.mkContinuous 1 fun m => ?_, ?_⟩
    · rw [one_mul, Real.norm_eq_abs]
      exact o.abs_volumeForm_apply_le m
    · rw [AlternatingMap.coe_mkContinuous, o.volumeForm_robust b rfl]
      have h : (fun i => EuclideanSpace.single i (1 : ℝ)) = ⇑b.toBasis := by
        funext i; simp [b]
      rw [h, Module.Basis.det_self]
  have aux_scalar_test_tendsto : ∀ (n : ℕ) (U : Set (Euclid n)) (c : ℝ) (Y : ℕ → GeometricCurrentOn U n) (u : ℕ → Euclid n → ℝ), (∀ (k : ℕ) (ω : TestFormOn U n), Y k ω = ∫ y in U, u k y * (ω : DifferentialForm (Euclid n) n) y (fun i => EuclideanSpace.single i (1 : ℝ))) → (∀ ω : TestFormOn U n, Tendsto (fun k => Y k ω) atTop (𝓝 (c * ∫ y, (ω : DifferentialForm (Euclid n) n) y (fun i => EuclideanSpace.single i (1 : ℝ))))) → ∀ b : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) b → HasCompactSupport b → tsupport b ⊆ U → Tendsto (fun k => ∫ y in U, u k y * b y) atTop (𝓝 (c * ∫ y, b y)) := by
    intro n U c Y u hrep hweak b hb hbc hbU
    obtain ⟨δ, hδ⟩ := aux_exists_det_covector n
    have hmem : (fun y => b y • δ : DifferentialForm (Euclid n) n) ∈ testFormOnSubmodule (E := Euclid n) U n :=
      ⟨⟨hb.smul contDiff_const, hbc.smul_right⟩, (tsupport_smul_subset_left b (fun _ => δ)).trans hbU⟩
    let ω : TestFormOn U n := ⟨fun y => b y • δ, hmem⟩
    have hωe : ∀ y, (ω : DifferentialForm (Euclid n) n) y (fun i => EuclideanSpace.single i (1 : ℝ)) = b y := by
      intro y
      simp [ω, hδ]
    have h1 := hweak ω
    simp only [hωe] at h1
    refine h1.congr (fun k => ?_)
    rw [hrep k ω]
    simp only [hωe]
  have aux_exists_normalized_mollifier : ∀ (n : ℕ) (r : ℝ), 0 < r → ∃ ρ : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ρ ∧ HasCompactSupport ρ ∧ (∀ x, 0 ≤ ρ x) ∧ ∫ x, ρ x = 1 ∧ support ρ ⊆ ball (0 : Euclid n) r := by
    intro n r hr
    -- the bump `B` with `rIn = r/2`, `rOut = r`
    let B : ContDiffBump (0 : Euclid n) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
    have hBs : HasCompactSupport B := B.hasCompactSupport
    have hBi : Integrable B := B.continuous.integrable_of_hasCompactSupport hBs
    -- `I = ∫ B > 0`: `B ≥ 0` and `support B = B_r(0)` has positive measure
    have hI : 0 < ∫ x, B x := by
      rw [integral_pos_iff_support_of_nonneg (fun x => B.nonneg' x) hBi, B.support_eq]
      exact measure_ball_pos volume 0 hr
    refine ⟨fun x => (∫ y, B y)⁻¹ * B x, contDiff_const.mul B.contDiff, hBs.mul_left,
      fun x => mul_nonneg (inv_nonneg.2 hI.le) (B.nonneg' x), ?_, ?_⟩
    · rw [integral_const_mul, inv_mul_cancel₀ hI.ne']
    · exact (support_mul_subset_right _ _).trans B.support_eq.subset
  have aux_abs_apply_le_massOn : ∀ (P n : ℕ) (U W : Set (Euclid P)) (T : GeometricCurrentOn U n) (ω : TestFormOn U n) (r : ℝ), T.massOn W ≠ ∞ → tsupport (ω : DifferentialForm (Euclid P) n) ⊆ W → (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ r) → |T ω| ≤ r * (T.massOn W).toReal := by
    intro P n U W T ω r hM hW hr
    -- homogeneity of the Euclidean coefficient norm
    have hsmul : ∀ (c : ℝ) (α : Covector (Euclid P) n),
        covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
      intro c α
      unfold covectorEuclideanNorm
      rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg c), Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun I _ => ?_
      split_ifs
      · rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_pow]
      · rw [mul_zero]
    have hr0 : 0 ≤ r := (covectorEuclideanNorm_nonneg _).trans (hr 0)
    -- `|T(ω)| ≤ s M_W(T)` for `0 < s`, `r ≤ s`: every `c • ω` with `|c| ≤ s⁻¹` is admissible
    have hbound : ∀ s : ℝ, 0 < s → r ≤ s → |T ω| ≤ s * (T.massOn W).toReal := by
      intro s hs hrs
      have hadm : ∀ c : ℝ, |c| ≤ s⁻¹ → c * T ω ≤ (T.massOn W).toReal := by
        intro c hc
        have hmem : c • ω ∈ massAdmissibleOn U n W := by
          refine ⟨(tsupport_smul_subset_right (fun _ => c) _).trans hW, fun x => ?_⟩
          show covectorEuclideanNorm (c • (ω : DifferentialForm (Euclid P) n) x) ≤ 1
          rw [hsmul]
          calc |c| * covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ s⁻¹ * s :=
                mul_le_mul hc ((hr x).trans hrs) (covectorEuclideanNorm_nonneg _)
                  (inv_nonneg.2 hs.le)
            _ = 1 := inv_mul_cancel₀ hs.ne'
        have h := (ENNReal.ofReal_le_iff_le_toReal hM).1 (T.le_massOn hmem)
        rwa [show T (c • ω) = c * T ω from T.toCurrent.map_smul c ω] at h
      have h1 := hadm s⁻¹ (abs_of_pos (inv_pos.2 hs)).le
      have h2 := hadm (-s⁻¹) (by rw [abs_neg, abs_of_pos (inv_pos.2 hs)])
      rw [neg_mul, ← mul_neg] at h2
      rw [abs_le]
      exact ⟨neg_le.1 ((inv_mul_le_iff₀ hs).1 h2), (inv_mul_le_iff₀ hs).1 h1⟩
    -- let `s ↓ r`
    have hlim : Tendsto (fun s : ℝ => s * (T.massOn W).toReal) (𝓝[>] r)
        (𝓝 (r * (T.massOn W).toReal)) :=
      ((continuous_mul_const _).tendsto r).mono_left nhdsWithin_le_nhds
    exact ge_of_tendsto hlim
      (eventually_nhdsWithin_of_forall fun s hs => hbound s (hr0.trans_lt hs) (le_of_lt hs))
  have aux_norm_props : ∀ (P n : ℕ), (∀ α α' : Covector (Euclid P) n, covectorEuclideanNorm (α + α') ≤ covectorEuclideanNorm α + covectorEuclideanNorm α') ∧ (∀ (t : ℝ) (α : Covector (Euclid P) n), covectorEuclideanNorm (t • α) = |t| * covectorEuclideanNorm α) ∧ (∃ C : ℝ, 0 ≤ C ∧ ∀ α : Covector (Euclid P) n, covectorEuclideanNorm α ≤ C * ‖α‖) ∧ Continuous (fun α : Covector (Euclid P) n => covectorEuclideanNorm α) := by
    intro P n
    classical
    -- Step 1: the coefficients `c_I α` and the coefficient vector `v α`, with `N α = ‖v α‖`
    let e := EuclideanSpace.basisFun (Fin P) ℝ
    let c : (Fin n → Fin P) → Covector (Euclid P) n → ℝ := fun I α =>
      if StrictMono I then α (fun i => e (I i)) else 0
    let v : Covector (Euclid P) n → EuclideanSpace ℝ (Fin n → Fin P) := fun α =>
      WithLp.toLp 2 (fun I => c I α)
    have hN : ∀ α : Covector (Euclid P) n, covectorEuclideanNorm α = ‖v α‖ := by
      intro α
      rw [EuclideanSpace.norm_eq]
      unfold covectorEuclideanNorm
      congr 1
      refine Finset.sum_congr rfl fun I _ => ?_
      by_cases hI : StrictMono I <;> simp [v, c, e, hI]
    -- Step 2: `v` is additive and `ℝ`-homogeneous
    have hadd : ∀ α α' : Covector (Euclid P) n, v (α + α') = v α + v α' := by
      intro α α'
      simp only [v, ← WithLp.toLp_add]
      congr 1
      funext I
      by_cases hI : StrictMono I <;> simp [c, hI]
    have hsmul : ∀ (t : ℝ) (α : Covector (Euclid P) n), v (t • α) = t • v α := by
      intro t α
      simp only [v, ← WithLp.toLp_smul]
      congr 1
      funext I
      by_cases hI : StrictMono I <;> simp [c, hI]
    -- Step 3: (i), the triangle inequality in `EuclideanSpace ℝ (Fin n → Fin P)`
    have h1 : ∀ α α' : Covector (Euclid P) n,
        covectorEuclideanNorm (α + α') ≤ covectorEuclideanNorm α + covectorEuclideanNorm α' := by
      intro α α'
      rw [hN, hN, hN, hadd]
      exact norm_add_le _ _
    -- Step 4: (ii), homogeneity of the Euclidean norm
    have h2 : ∀ (t : ℝ) (α : Covector (Euclid P) n),
        covectorEuclideanNorm (t • α) = |t| * covectorEuclideanNorm α := by
      intro t α
      rw [hN, hN, hsmul, norm_smul, Real.norm_eq_abs]
    -- Step 5: `|c_I α| ≤ ‖α‖ ∏ₖ ‖e_{I(k)}‖ = ‖α‖`
    have hc : ∀ (I : Fin n → Fin P) (α : Covector (Euclid P) n), |c I α| ≤ ‖α‖ := by
      intro I α
      by_cases hI : StrictMono I
      · simpa [c, e, hI, Real.norm_eq_abs] using α.le_opNorm (fun i => e (I i))
      · simp [c, hI]
    -- Step 6: (iii) with `C = √(card (Fin n → Fin P))`
    have h3 : ∀ α : Covector (Euclid P) n,
        covectorEuclideanNorm α ≤ Real.sqrt (Fintype.card (Fin n → Fin P)) * ‖α‖ := by
      intro α
      have hsum : ∑ I, ‖(v α).ofLp I‖ ^ 2 ≤ ∑ _I : Fin n → Fin P, ‖α‖ ^ 2 :=
        Finset.sum_le_sum fun I _ => by
          simpa [v, Real.norm_eq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hc I α) 2
      rw [hN, EuclideanSpace.norm_eq]
      calc Real.sqrt (∑ I, ‖(v α).ofLp I‖ ^ 2) ≤ Real.sqrt (∑ _I : Fin n → Fin P, ‖α‖ ^ 2) :=
            Real.sqrt_le_sqrt hsum
        _ = Real.sqrt (Fintype.card (Fin n → Fin P)) * ‖α‖ := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
              Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    -- Step 7: (iv), `|N α - N α'| ≤ N (α - α') ≤ C ‖α - α'‖`, so `N` is Lipschitz
    have hlip : ∀ α α' : Covector (Euclid P) n, dist (covectorEuclideanNorm α)
        (covectorEuclideanNorm α') ≤ Real.sqrt (Fintype.card (Fin n → Fin P)) * dist α α' := by
      intro α α'
      have ha : covectorEuclideanNorm α ≤
          covectorEuclideanNorm (α - α') + covectorEuclideanNorm α' := by
        simpa only [sub_add_cancel] using h1 (α - α') α'
      have hb : covectorEuclideanNorm α' ≤
          covectorEuclideanNorm (α - α') + covectorEuclideanNorm α := by
        have h := h1 (α' - α) α
        rwa [sub_add_cancel, ← neg_sub, covectorEuclideanNorm_neg] at h
      have hC := h3 (α - α')
      rw [Real.dist_eq, dist_eq_norm, abs_le]
      constructor <;> linarith
    exact ⟨h1, h2, ⟨_, Real.sqrt_nonneg _, h3⟩,
      (LipschitzWith.of_dist_le_mul (K := ⟨_, Real.sqrt_nonneg _⟩) hlip).continuous⟩
  have aux_boundary_variation_bound : ∀ (d : ℕ) (U : Set (Euclid (d + 1))) (Y : GeometricCurrentOn U (d + 1)) (u : Euclid (d + 1) → ℝ) (ε : Covector (Euclid (d + 1)) d) (f : Euclid (d + 1) → ℝ) (z : Euclid (d + 1)) (M : ℝ), (∀ ω : TestFormOn U (d + 1), Y ω = ∫ y in U, u y * (ω : DifferentialForm (Euclid (d + 1)) (d + 1)) y (fun i => EuclideanSpace.single i (1 : ℝ))) → Y.boundary.massOn U ≠ ∞ → covectorEuclideanNorm ε ≤ ‖z‖ → (∀ y, exteriorDerivative (fun x => f x • ε) y (fun i => EuclideanSpace.single i (1 : ℝ)) = fderiv ℝ f y z) → ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → tsupport f ⊆ U → (∀ y, |f y| ≤ M) → |∫ y in U, u y * fderiv ℝ f y z| ≤ (Y.boundary.massOn U).toReal * ‖z‖ * M := by
    intro d U Y u ε f z M hrep hfin hεn hεd hf hfc hfU hM
    -- the test `d`-form `γ = f ε`, with `spt γ ⊆ spt f ⊆ U`
    have hsupp : tsupport (fun x => f x • ε : DifferentialForm (Euclid (d + 1)) d) ⊆ U :=
      (tsupport_smul_subset_left f (fun _ => ε)).trans hfU
    have hmem : (fun x => f x • ε : DifferentialForm (Euclid (d + 1)) d) ∈
        testFormOnSubmodule (E := Euclid (d + 1)) U d :=
      ⟨⟨hf.smul contDiff_const, hfc.smul_right⟩, hsupp⟩
    let γ : TestFormOn U d := ⟨fun x => f x • ε, hmem⟩
    -- `|γ(x)| = |f(x)| |ε| ≤ M ‖z‖`
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
    have hbound : ∀ x, covectorEuclideanNorm ((γ : DifferentialForm (Euclid (d + 1)) d) x) ≤
        M * ‖z‖ := by
      intro x
      change covectorEuclideanNorm (f x • ε) ≤ M * ‖z‖
      rw [(aux_norm_props (d + 1) d).2.1]
      exact mul_le_mul (hM x) hεn (covectorEuclideanNorm_nonneg ε) hM0
    -- `|∂Y(γ)| ≤ M ‖z‖ M_U(∂Y)`
    have key := aux_abs_apply_le_massOn (d + 1) d U U Y.boundary γ (M * ‖z‖) hfin hsupp
      hbound
    -- `∂Y(γ) = Y(dγ) = ∫_U u Df(z)`
    have heq : Y.boundary γ = ∫ y in U, u y * fderiv ℝ f y z := by
      rw [GeometricCurrentOn.boundary_apply, hrep]
      congr 1
      funext y
      change u y * exteriorDerivative (fun x => f x • ε) y
        (fun i => EuclideanSpace.single i (1 : ℝ)) = _
      rw [hεd y]
    rw [heq] at key
    calc |∫ y in U, u y * fderiv ℝ f y z| ≤ M * ‖z‖ * (Y.boundary.massOn U).toReal := key
      _ = (Y.boundary.massOn U).toReal * ‖z‖ * M := by ring
  have aux_l1_squeeze_of_mollified : ∀ (n : ℕ) (R c : ℝ) (φ : Euclid n → ℝ) (u : ℕ → Euclid n → ℝ) (a : ℕ → ℝ), 0 < R → Continuous φ → HasCompactSupport φ → (∀ k, IntegrableOn (u k) (ball 0 (2 * R))) → TendstoUniformlyOn (fun k x => ∫ y in ball 0 (2 * R), u k y * φ (x - y)) (fun _ => c) atTop (closedBall 0 R) → Tendsto a atTop (𝓝 0) → (∀ᶠ k in atTop, ∫ x in ball 0 R, |u k x - ∫ y in ball 0 (2 * R), u k y * φ (x - y)| ≤ a k) → Tendsto (fun k => ∫ x in ball 0 R, |u k x - c|) atTop (𝓝 0) := by
    intro n R c φ u a hR hφ hφc hint hunif ha hbound
    obtain ⟨C, hC⟩ := hφ.bounded_above_of_compact_support hφc
    -- continuity of the mollifications
    have hwcont : ∀ k, Continuous (fun x => ∫ y in ball (0 : Euclid n) (2 * R), u k y * φ (x - y)) := by
      intro k
      refine continuous_of_dominated (bound := fun y => ‖u k y‖ * C) (fun x => ?_) (fun x => ?_) ?_ ?_
      · exact (hint k).aestronglyMeasurable.mul
          (hφ.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      · refine Eventually.of_forall fun y => ?_
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
      · exact (hint k).norm.mul_const C
      · exact Eventually.of_forall fun y => continuous_const.mul (hφ.comp (continuous_id.sub continuous_const))
    have hBR : ball (0 : Euclid n) R ⊆ ball 0 (2 * R) := ball_subset_ball (by linarith)
    have hvol : volume (ball (0 : Euclid n) R) < ∞ := measure_ball_lt_top
    have hwint : ∀ k, IntegrableOn (fun x => ∫ y in ball (0 : Euclid n) (2 * R), u k y * φ (x - y)) (ball 0 R) :=
      fun k => ((hwcont k).continuousOn.integrableOn_compact (isCompact_closedBall 0 R)).mono_set
        ball_subset_closedBall
    have huint : ∀ k, IntegrableOn (u k) (ball 0 R) := fun k => (hint k).mono_set hBR
    have hcint : IntegrableOn (fun _ : Euclid n => c) (ball 0 R) := integrableOn_const hvol.ne
    have htri : ∀ k, ∫ x in ball 0 R, |u k x - c| ≤
        (∫ x in ball 0 R, |u k x - ∫ y in ball (0 : Euclid n) (2 * R), u k y * φ (x - y)|) +
          ∫ x in ball 0 R, |(∫ y in ball (0 : Euclid n) (2 * R), u k y * φ (x - y)) - c| := by
      intro k
      have hA : IntegrableOn (fun x => |u k x - ∫ y in ball (0 : Euclid n) (2 * R), u k y * φ (x - y)|)
          (ball 0 R) := ((huint k).sub (hwint k)).abs
      have hB : IntegrableOn (fun x => |(∫ y in ball (0 : Euclid n) (2 * R), u k y * φ (x - y)) - c|)
          (ball 0 R) := ((hwint k).sub hcint).abs
      rw [← integral_add hA hB]
      exact integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _) (hA.add hB)
        (Eventually.of_forall fun x => abs_sub_le _ _ _)
    set m := (volume (ball (0 : Euclid n) R)).toReal with hm
    have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hη0 : 0 < ε / (2 * (m + 1)) := by positivity
    have h1 := Metric.tendstoUniformlyOn_iff.1 hunif _ hη0
    have h2 := Metric.tendsto_nhds.1 ha (ε / 2) (by positivity)
    filter_upwards [h1, h2, hbound] with k hk1 hk2 hk3
    have hwc : ∫ x in ball 0 R, |(∫ y in ball (0 : Euclid n) (2 * R), u k y * φ (x - y)) - c| ≤
        ε / (2 * (m + 1)) * m := by
      have := norm_setIntegral_le_of_norm_le_const hvol (C := ε / (2 * (m + 1)))
        (f := fun x => |(∫ y in ball (0 : Euclid n) (2 * R), u k y * φ (x - y)) - c|) (fun x hx => by
          have := hk1 x (ball_subset_closedBall hx)
          rw [Real.dist_eq] at this
          rw [Real.norm_eq_abs, abs_abs, abs_sub_comm]
          exact this.le)
      exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ this)
    have hnn : 0 ≤ ∫ x in ball 0 R, |u k x - c| := integral_nonneg fun x => abs_nonneg _
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
    rw [Real.dist_eq, sub_zero] at hk2
    have hak : a k < ε / 2 := (le_abs_self _).trans_lt hk2
    have hlast : ε / (2 * (m + 1)) * m < ε / 2 := by
      rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have := htri k
    linarith
  intro d R c Λ Y u hR hint hΛ hrep hbd hconv
  -- Step 1: scalar tests `∫_U u_k b → c ∫ b`
  have htest :=
    aux_scalar_test_tendsto (d + 1) (ball 0 (2 * R)) c Y u hrep hconv
  -- Step 2: a normalized mollifier `φ` with `tsupport φ ⊆ B̄_{R/8}(0) ⊆ B_s(0)`, `s = R/4`
  obtain ⟨φ, hφ, hφc, hφ0, hφ1, hφs⟩ :=
    aux_exists_normalized_mollifier (d + 1) (R / 8) (by positivity)
  have hφt : tsupport φ ⊆ ball 0 (R / 4) :=
    (closure_minimal (hφs.trans ball_subset_closedBall) isClosed_closedBall).trans
      (closedBall_subset_ball (by linarith))
  -- Step 3: `w_k → c ∫ φ = c` uniformly on `B̄_R(0)`
  have hunif := Submission.cbr_ci_pw_mollified_tendstoUniformlyOn (d + 1) R (R / 4) c Λ φ u hR
    (by positivity) (by linarith) hφ hφt hint hΛ htest
  rw [hφ1, mul_one] at hunif
  -- Step 4: `V_k = M_U(∂Y_k).toReal → 0`, and eventually `M_U(∂Y_k) ≠ ∞`
  have hV : Tendsto (fun k => ((Y k).boundary.massOn (ball 0 (2 * R))).toReal) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hbd
  have hfin := hbd.eventually_ne ENNReal.zero_ne_top
  -- Step 5: `∫_{B_R} |u_k − w_k| ≤ s V_k`, by the BV estimate; its hypothesis
  -- `|∫_U u_k ∂_z f| ≤ V_k ‖z‖ M` comes from `ε_z` and the boundary-mass bound
  have hbv : ∀ᶠ k in atTop,
      ∫ x in ball 0 R, |u k x - ∫ y in ball 0 (2 * R), u k y * φ (x - y)| ≤
        R / 4 * ((Y k).boundary.massOn (ball 0 (2 * R))).toReal := by
    filter_upwards [hfin] with k hk
    refine Submission.cbr_ci_pw_bv_mollifier_estimate (d + 1) R (R / 4)
      ((Y k).boundary.massOn (ball 0 (2 * R))).toReal φ (u k) hR (by positivity) (by linarith)
      ENNReal.toReal_nonneg hφ hφ0 hφt hφ1 (hint k) fun f z M hf hfc hft hM => ?_
    obtain ⟨ε, hε, hεf⟩ := Submission.cbr_ci_pw_interior_product_form d z
    exact aux_boundary_variation_bound d (ball 0 (2 * R)) (Y k) (u k) ε f z M
      (hrep k) hk hε (fun y => hεf f y (hf.differentiable (by simp) y)) hf hfc hft hM
  -- Step 6: the `L¹` squeeze with `a_k = s V_k → 0`
  exact aux_l1_squeeze_of_mollified (d + 1) R c φ u
    (fun k => R / 4 * ((Y k).boundary.massOn (ball 0 (2 * R))).toReal) hR hφ.continuous hφc hint
    hunif (by simpa only [mul_zero] using hV.const_mul (R / 4)) hbv
```

## Key steps

1. Test functions b give test forms b·dy, so ∫_U u_k b → c∫b; fix a normalized bump φ supported in B_{R/4}.
2. mollified_uniform: w_k = u_k∗φ → c uniformly on B̄_R.
3. interior_form: Y_k((∂_zf)dy) = ∂Y_k(f·ε_z) with |f·ε_z| ≤ |z|sup|f|, so ∫u_k∂_zf is bounded by M_U(∂Y_k)|z|sup|f|; bv_estimate gives ∫_{B_R}|u_k − w_k| ≤ (R/4)M_U(∂Y_k).
4. ∫_{B_R}|u_k − c| ≤ (R/4)M_U(∂Y_k) + |B_R|·sup|w_k − c| → 0.

## Reference use

### local-project

Queries:
- `cat SNAPSHOT/manifest.json -> mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d; git rev-parse HEAD in the workspace, .lake/packages/mathlib and .lake/packages/simongmt -> b4d606db1, 25730c7c, 2b366308; cmp SNAPSHOT/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean -> identical`
- `python3 -I scans of RUN/dag.json (2229 nodes): selected node (depth 5, decomposing, attempt 2 started 2026-10-14T02:29:54Z); subtree of root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1 (cbr_ci_plane_weight_ge_one: identical frozen type, speculative-ready) with statuses, candidate commits and updated_at; lean_name lookup of all 11 proposed names: the 8 reused names each occur once, accepted with candidate commits (latest 02:28:02Z) and identical lean_statement; the 3 dmcbr_ci_pw_* names have no node; byte comparisons dimred_mbl_slice_mass_bounds = cmc_slice_mass_bounds, dmcbr_measure_convergence_tools = cbr_measure_convergence_tools, first conjunct of dimred_mbl_current_foundations = cmc_exists_massRepresentation, and (REP), (SL), (CT) occur verbatim in the selected type`
- `grep -n / sed -n over /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_decompose, _existing_lean_name_problem, _accepted_checkpoint, _solve_children existing_by_name), store.py (refresh, update: accepted status is permanent), leaf_verification.py (check_source_delta), lean_contract.py (validate_lean_statement); swarm-project.json -> max_depth 6, max_children 12`
- `read RUN/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-fc3eb928c0/{parent-child-handoff.json, parent-supplied-plan.md, decomposition-v1.json}: attempt 1 (12 children) was rejected only by the name check on cbr_ci_pw_bv_smooth_test_bound; its child statements, types and proofs were reused here, except smooth_test_bound (dropped) and bv_estimate (now the accepted cbr_ci_pw_bv_mollifier_estimate, with Claim A proved inline)`
- `git show <candidate>:GMT/Ch07/Submission.lean for e55e2ff3e6, f6358e3d52, e42d9153e5, b0c7e18f51, 7bb3791613, 4020906019, 04807323c8, 144655f39d -> each contains 'theorem Submission.<name> : <frozen type> :=' with the reused name occurring exactly once`
- `grep -rn over SNAPSHOT/mathlib/Mathlib for the library names cited in the bv_estimate proof: ae_tendsto_average_norm_sub (Covering/DensityTheorem.lean:150, Covering/Differentiation.lean:837), tendsto_integral_smul_of_tendsto_average_norm_sub, integral_comp_inv_smul_of_nonneg, addHaar_real_closedBall', contDiff_convolution_right, integrableOn_iff_integrable_of_support_subset, integrableOn_of_bounded, continuous_of_dominated, intervalIntegral_integral_swap, norm_integral_le_of_norm_le_const, fderiv_comp_add_right, tsupport_comp_eq_preimage, integral_sub_right_eq_self, Integrable.mul_prod, integral_integral_swap, Integrable.mul_bdd, setIntegral_indicator, integral_pos_iff_support_of_nonneg, measure_ball_pos, Integrable.integral_prod_left, Integrable.integral_prod_right, Continuous.integrable_of_hasCompactSupport, Continuous.bounded_above_of_compact_support, HasCompactSupport.fderiv, integral_eq_sub_of_hasDerivAt -> all present`
- `rg -l dmcbr_ci_pw_projected_current|dmcbr_ci_pw_density_null_off_image|dmcbr_ci_pw_density_l1_tendsto_const over SNAPSHOT/project, GMT and .lake/packages/simongmt -> no match (exit 1)`
- `lake env lean /tmp/dmcbr_ci_a2/lean/Types.lean (the 11 child types as Submission.* theorems) -> only sorry warnings, exit 0`
- `lake env lean /tmp/dmcbr_ci_a2/lean/Assembly.lean (exact frozen parent type from the 11 child types as axioms, no sorry) -> #print axioms: propext, Classical.choice, Quot.sound, cbr_ci_pw_good_level_slices, cbr_ci_pw_isolate_plane, cbr_ci_pw_orthonormal_covector_bounds, cbr_ci_pw_plane_map_volume, cbr_ci_pw_top_current_density, dmcbr_ci_pw_density_l1_tendsto_const, dmcbr_ci_pw_density_null_off_image, dmcbr_ci_pw_projected_current`
- `lake env lean /tmp/dmcbr_ci_a2/lean/check_{projection,null_off_image,l1_constant}.lean (#count_heartbeats in + realization + #print axioms, siblings declared by exact frozen types) -> 102743 / 19932 / 59551 heartbeats, axioms = standard three + declared siblings only`
- `lake env lean /tmp/dmcbr_ci_a2/lean/EndToEnd.lean (3 fresh realizations as theorems + assembly) -> #print axioms: propext, Classical.choice, Quot.sound + the 8 reused accepted declarations, exit 0`
- `python3 -I: AST-extracted leaf_verification.check_source_delta on GMT/Ch07/Submission.lean with each fresh realization inserted before main_theorem's docstring -> OK (3/3); lean_contract.validate_lean_statement on all 11 child types -> valid and unchanged`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/swarm-project.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-fc3eb928c0/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-fc3eb928c0/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-fc3eb928c0/decomposition-v1.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/store.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/DensityTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean`
- `/tmp/dmcbr_ci_a2/lean/Types.lean`
- `/tmp/dmcbr_ci_a2/lean/Assembly.lean`
- `/tmp/dmcbr_ci_a2/lean/check_projection.lean`
- `/tmp/dmcbr_ci_a2/lean/check_null_off_image.lean`
- `/tmp/dmcbr_ci_a2/lean/check_l1_constant.lean`
- `/tmp/dmcbr_ci_a2/lean/EndToEnd.lean`

The snapshot is compatible: pins match, and the snapshot contract is byte-identical to Submission.lean. No dmcbr_ci_pw_* declaration exists in the snapshot, the workspace or SimonGMT. The 8 reused children (covector_bounds, plane_map, isolate_plane, good_level, top_density, interior_form, mollified_uniform, bv_estimate = cbr_ci_pw_bv_mollifier_estimate) are accepted checkpoints. They were accepted before this attempt's DAG refresh, and each candidate commit declares exactly the frozen type. The 3 fresh children take globally unused dmcbr_ci_pw_* names because their other-branch counterparts are unaccepted. All 11 child types elaborate. The sorry-free conditional assembly and the end-to-end file prove the exact parent type using only propext, Classical.choice, Quot.sound and child or reused accepted declarations. The fresh single-theorem realizations compile within the default heartbeats and pass the leaf delta check.
