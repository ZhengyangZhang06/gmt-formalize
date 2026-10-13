# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_tangent-a1`
- Child DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_tangent-a1.slice_identity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 3(a), 4 and 6–10 of the parent proof: undo both blow-ups with blowup_cov; blow-ups of the product are products of blow-ups; transport to the product measure (sibling product_measure); Fubini; substitution s = s₀ + rσ in the interval variable. The hypothesis s₀ ∈ (0,1) is not needed for this identity.

Notation. E := ℝ^P = Eucl P, E′ := ℝ^{P+1} = Eucl (P+1), Hᵏ := μHE[k], L¹ := volume on ℝ. Φ(s, u) := (EuclideanSpace.equiv (Fin (P+1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ u)); π(y) := (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P+1)) ℝ y)); y₀ := (EuclideanSpace.equiv (Fin (P+1)) ℝ y) 0; Φ′(p) := Φ(p.1, p.2). M̃ := {y : π(y) ∈ M ∧ y₀ ∈ (0,1)}; y* := Φ(s₀, x); η := blowUpMap y* r on E′ and η′ := blowUpMap x r on E (η(z) = r⁻¹·(z − y*), η′(u) = r⁻¹·(u − x)), r > 0; ν := Hᵐ⌞M; ρ := (L¹⌞(0,1)) ⊗ ν; a(σ) := ∫_{η′(M)} f(Φ(σ, w))·θ(x + r·w) dHᵐ(w); α := −s₀/r, β := (1 − s₀)/r. The goal is ∫_{η(M̃)} f(z)·θ(π(y* + r·z)) dH^{m+1}(z) = ∫_ℝ 1_{(α, β]}(σ)·a(σ) dσ.
Siblings used: blowup_cov (accepted declaration fiw_tl_blowup_setIntegral): for every n, centre c, r > 0, set S and function h, ∫_{blowUpMap c r '' S} h dHⁿ = (rⁿ)⁻¹·∫_S h(blowUpMap c r z) dHⁿ(z), with no measurability or integrability assumption. product_measure (iwl_cr_ip_wt_product_measure): from (MP) and the hypotheses on M, H^{m+1}⌞M̃ = Φ′_*ρ.

1. (Coordinates.) π(Φ(s, u)) = u (ContinuousLinearEquiv.apply_symm_apply, Fin.tail_cons, symm_apply_apply). Φ is linear in the pair: Φ(s, u) − Φ(s′, u′) = Φ(s − s′, u − u′) and c·Φ(s, u) = Φ(c·s, c·u) (map_sub/map_smul of the equivalences, coordinates compared by Fin.cases). ‖Φ(s, u)‖² = s² + ‖u‖² (EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ), so ‖u‖ ≤ ‖Φ(s, u)‖. Φ′ is continuous, with continuous inverse y ↦ (y₀, π(y)) (Fin.cons_zero, Fin.tail_cons, Fin.cons_self_tail); so Φ′ is a homeomorphism ℝ × E ≃ₜ E′ and a measurable embedding (Homeomorph.measurableEmbedding).
2. (Bounds on f.) Choose R with ‖z‖ ≤ R whenever f(z) ≠ 0 (tsupport f is compact, hence bounded), and C_f with |f(z)| ≤ C_f for all z (Continuous.bounded_above_of_compact_support). By step 1: (*) if f(Φ(σ, w)) ≠ 0 then ‖w‖ ≤ R.
3. (ν and θ.) ν is finite on compact sets: ν(K) = Hᵐ(K ∩ M) = Hᵐ(M ∩ K) < ∞ (Measure.restrict_apply). Hence ν is σ-finite (E is σ-compact). θ is a.e. strongly measurable for ν: M = ⋃_n (M ∩ B̄(0, n)), and θ is integrable, hence a.e. strongly measurable, on each M ∩ B̄(0, n) (the hypothesis on θ with the compact set K = B̄(0, n)); conclude by aestronglyMeasurable_iUnion_iff.
4. (Blow-ups.) For all s ∈ ℝ, u ∈ E: η(Φ(s, u)) = r⁻¹·(Φ(s, u) − Φ(s₀, x)) = Φ(r⁻¹·(s − s₀), r⁻¹·(u − x)) = Φ(r⁻¹·(s − s₀), η′(u)) (step 1). Also y* + r·η(w) = w for w ∈ E′ and x + r·η′(u) = u for u ∈ E (r ≠ 0).
5. (The integrand G is ρ-integrable.) Put G(s, u) := f(Φ(r⁻¹·(s − s₀), η′(u)))·θ(u). G is a.e. strongly measurable for ρ: the first factor is continuous in (s, u), and (s, u) ↦ θ(u) is a.e. strongly measurable (AEStronglyMeasurable.comp_snd, step 3). For every (s, u): |G(s, u)| ≤ b(u) := 1_{B̄(x, rR)}(u)·C_f·|θ(u)|. Indeed, if u ∈ B̄(x, rR) use |f| ≤ C_f. If not, ‖η′(u)‖ = r⁻¹·‖u − x‖ > R, so the f-factor vanishes by (*). b is ν-integrable: by integrable_indicator_iff and Measure.restrict_restrict this is integrability of C_f·|θ| on M ∩ B̄(x, rR), which is the hypothesis on θ applied to the compact set K = B̄(x, rR). L¹⌞(0,1) is a finite measure, so (s, u) ↦ b(u) is ρ-integrable (Integrable.comp_snd). Hence G is ρ-integrable (Integrable.mono').
6. (Undoing the blow-up in E′.) Apply blowup_cov with n = m + 1, centre y*, set M̃ and h(z) := f(z)·θ(π(y* + r·z)), then use step 4. This gives LHS = (r^{m+1})⁻¹·∫_{M̃} f(η(w))·θ(π(w)) dH^{m+1}(w).
7. (Transport to ρ.) By product_measure, ∫_{M̃} F dH^{m+1} = ∫ F d(Φ′_*ρ) for F(w) := f(η(w))·θ(π(w)). By MeasurableEmbedding.integral_map (step 1; valid for every integrand), this equals ∫ F(Φ′(p)) dρ(p). By step 4 and π(Φ(s, u)) = u, F(Φ′(s, u)) = f(Φ(r⁻¹·(s − s₀), η′(u)))·θ(u) = G(s, u). Hence LHS = (r^{m+1})⁻¹·∫ G dρ.
8. (Fubini.) By integral_prod (step 5; ν σ-finite), ∫ G dρ = ∫_{(0,1)} H(s) ds, where H(s) := ∫_M G(s, u) dHᵐ(u). Moreover ∫_{(0,1)} H = ∫_{(0,1]} H (integral_Ioc_eq_integral_Ioo) = ∫_0^1 H(s) ds (intervalIntegral.integral_of_le, 0 ≤ 1).
9. (Substitution.) r·α + s₀ = 0 and r·β + s₀ = 1. intervalIntegral.integral_comp_mul_add (c = r ≠ 0, d = s₀; no integrability needed) gives ∫_α^β H(r·σ + s₀) dσ = r⁻¹·∫_0^1 H(s) ds.
10. (Slices.) Fix σ. Since r⁻¹·((r·σ + s₀) − s₀) = σ, we get H(r·σ + s₀) = ∫_M f(Φ(σ, η′(u)))·θ(u) dHᵐ(u). By blowup_cov (n = m, centre x, set M, h(w) := f(Φ(σ, w))·θ(x + r·w)) and step 4, a(σ) = (r^m)⁻¹·∫_M f(Φ(σ, η′(u)))·θ(u) dHᵐ(u). Hence H(r·σ + s₀) = r^m·a(σ) for every σ.
11. (Assembly.) α ≤ β because r > 0 and −s₀ ≤ 1 − s₀ (div_le_div_of_nonneg_right). RHS = ∫_{(α,β]} a(σ) dσ (integral_indicator, Ioc measurable) = ∫_α^β a(σ) dσ (intervalIntegral.integral_of_le). By steps 9–10 and intervalIntegral.integral_const_mul, r^m·∫_α^β a = ∫_α^β H(r·σ + s₀) dσ = r⁻¹·∫_0^1 H. By steps 6–8, LHS = (r^{m+1})⁻¹·∫_0^1 H = (r^m)⁻¹·(r⁻¹·∫_0^1 H) (pow_succ, mul_inv) = (r^m)⁻¹·r^m·∫_α^β a = ∫_α^β a = RHS. ∎

Formalization aid. The following tactic proof, placed after `theorem Submission.iwl_cr_ip_wt_slice_identity : <the frozen Lean type of this child, verbatim> := by`, was kernel-checked in the contract scope (namespace GMT.Ch06 with the contract's opens) after import GMT.Ch06.Submission at the frozen commit d8d46c9 with the pinned toolchain (Lean v4.35.0-rc3, Mathlib 25730c7c), together with the accepted proof of Submission.fiw_tl_blowup_setIntegral (sibling blowup_cov) and the proof of Submission.iwl_cr_ip_wt_product_measure (sibling product_measure), the only declarations it uses; #print axioms = [propext, Classical.choice, Quot.sound].

  intro P m hMP M θ x s₀ hMmeas hMrect hMfin hθint f hfc hfcs r hr
  -- Coordinates.
  let Φ : ℝ → Eucl P → Eucl (P + 1) := fun s u =>
    (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ u))
  let π : Eucl (P + 1) → Eucl P := fun y =>
    (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y))
  have hπΦ : ∀ s u, π (Φ s u) = u := by
    intro s u
    simp only [Φ, π, ContinuousLinearEquiv.apply_symm_apply, Fin.tail_cons,
      ContinuousLinearEquiv.symm_apply_apply]
  have hΦsub : ∀ s u s' u', Φ s u - Φ s' u' = Φ (s - s') (u - u') := by
    intro s u s' u'
    simp only [Φ, ← map_sub]
    congr 1
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  have hΦsmul : ∀ (c s : ℝ) (u : Eucl P), c • Φ s u = Φ (c * s) (c • u) := by
    intro c s u
    simp only [Φ, ← map_smul]
    congr 1
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  have hnorm : ∀ (s : ℝ) (u : Eucl P), ‖u‖ ≤ ‖Φ s u‖ := by
    intro s u
    have h : ‖Φ s u‖ ^ 2 = s ^ 2 + ‖u‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
      rfl
    exact le_of_sq_le_sq (by rw [h]; nlinarith [sq_nonneg s]) (norm_nonneg _)
  have hΦc : Continuous fun p : ℝ × Eucl P => Φ p.1 p.2 :=
    (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm.continuous.comp
      (Continuous.finCons (A := fun _ : Fin (P + 1) => ℝ) continuous_fst
        ((EuclideanSpace.equiv (Fin P) ℝ).continuous.comp continuous_snd))
  let e : ℝ × Eucl P ≃ₜ Eucl (P + 1) :=
    { toFun := fun p => Φ p.1 p.2
      invFun := fun y => (EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0, π y)
      left_inv := fun p => by
        simp only [Φ, π, ContinuousLinearEquiv.apply_symm_apply, Fin.cons_zero, Fin.tail_cons,
          ContinuousLinearEquiv.symm_apply_apply]
      right_inv := fun y => by
        apply (EuclideanSpace.equiv (Fin (P + 1)) ℝ).injective
        simp only [Φ, π, ContinuousLinearEquiv.apply_symm_apply]
        exact Fin.cons_self_tail _
      continuous_toFun := hΦc
      continuous_invFun := by
        refine Continuous.prodMk ((continuous_apply 0).comp
          (EuclideanSpace.equiv (Fin (P + 1)) ℝ).continuous) ?_
        exact (EuclideanSpace.equiv (Fin P) ℝ).symm.continuous.comp
          (continuous_pi fun i : Fin P => (continuous_apply i.succ).comp
            (EuclideanSpace.equiv (Fin (P + 1)) ℝ).continuous) }
  have hemb : MeasurableEmbedding (fun p : ℝ × Eucl P => Φ p.1 p.2) := e.measurableEmbedding
  -- Support radius and sup bound of `f`.
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ z : Eucl (P + 1), f z ≠ 0 → ‖z‖ ≤ R := by
    obtain ⟨R, hR⟩ := hfcs.isCompact.isBounded.subset_closedBall 0
    refine ⟨R, fun z hz => ?_⟩
    simpa using hR (subset_tsupport _ hz)
  obtain ⟨Cf, hCf⟩ : ∃ C : ℝ, ∀ z, ‖f z‖ ≤ C := hfc.bounded_above_of_compact_support hfcs
  -- `ν = Hᵐ ⌞ M` is finite on compacts (so σ-finite) and `θ` is a.e. strongly measurable for it.
  have : IsFiniteMeasureOnCompacts ((μHE[m] : Measure (Eucl P)).restrict M) :=
    ⟨fun K hK => by
      rw [Measure.restrict_apply hK.measurableSet, inter_comm]
      exact hMfin K hK⟩
  have hθae : AEStronglyMeasurable θ ((μHE[m] : Measure (Eucl P)).restrict M) := by
    have hM : M = ⋃ n : ℕ, M ∩ closedBall (0 : Eucl P) n := by
      ext u
      simp only [mem_iUnion, mem_inter_iff, mem_closedBall, dist_zero_right]
      exact ⟨fun hu => ⟨⌈‖u‖⌉₊, hu, Nat.le_ceil _⟩, fun ⟨_, hu, _⟩ => hu⟩
    rw [hM, aestronglyMeasurable_iUnion_iff]
    intro n
    exact (hθint _ (isCompact_closedBall _ _)).aestronglyMeasurable
  -- Blow-up maps.
  have hηc : Continuous (Poincare.SimonGMT.Chapter03.blowUpMap x r) := by
    show Continuous fun u : Eucl P => r⁻¹ • (u - x)
    fun_prop
  have hηnorm : ∀ u, ‖Poincare.SimonGMT.Chapter03.blowUpMap x r u‖ = r⁻¹ * ‖u - x‖ := by
    intro u
    simp only [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hr]
  -- Blow-ups of the product are products of blow-ups.
  have hprod : ∀ s u, Poincare.SimonGMT.Chapter03.blowUpMap (Φ s₀ x) r (Φ s u) =
      Φ (r⁻¹ * (s - s₀)) (Poincare.SimonGMT.Chapter03.blowUpMap x r u) := by
    intro s u
    simp only [Poincare.SimonGMT.Chapter03.blowUpMap, hΦsub, hΦsmul]
  -- The integrand on the product and its integrability.
  let G : ℝ × Eucl P → ℝ := fun p =>
    f (Φ (r⁻¹ * (p.1 - s₀)) (Poincare.SimonGMT.Chapter03.blowUpMap x r p.2)) * θ p.2
  have hGint : Integrable G (((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)).prod
      ((μHE[m] : Measure (Eucl P)).restrict M)) := by
    have hbint : Integrable ((closedBall x (r * R)).indicator fun u => Cf * |θ u|)
        ((μHE[m] : Measure (Eucl P)).restrict M) := by
      rw [integrable_indicator_iff measurableSet_closedBall, IntegrableOn,
        Measure.restrict_restrict measurableSet_closedBall, inter_comm]
      exact ((hθint _ (isCompact_closedBall x (r * R))).norm.const_mul Cf).congr
        (Filter.Eventually.of_forall fun u => by simp [Real.norm_eq_abs])
    refine Integrable.mono' (hbint.comp_snd _) ?_ (Filter.Eventually.of_forall fun p => ?_)
    · refine AEStronglyMeasurable.mul ?_ hθae.comp_snd
      refine Continuous.aestronglyMeasurable ?_
      exact hfc.comp (hΦc.comp (((continuous_const.mul (continuous_fst.sub continuous_const))).prodMk
        (hηc.comp continuous_snd)))
    · show ‖G p‖ ≤ (closedBall x (r * R)).indicator (fun u => Cf * |θ u|) p.2
      by_cases hu : p.2 ∈ closedBall x (r * R)
      · rw [indicator_of_mem hu, norm_mul, Real.norm_eq_abs (θ p.2)]
        exact mul_le_mul_of_nonneg_right (hCf _) (abs_nonneg _)
      · rw [indicator_of_notMem hu]
        have hf0 : f (Φ (r⁻¹ * (p.1 - s₀)) (Poincare.SimonGMT.Chapter03.blowUpMap x r p.2)) = 0 := by
          by_contra h
          apply hu
          have h1 := (hnorm _ _).trans (hR _ h)
          rw [hηnorm, inv_mul_le_iff₀ hr] at h1
          rw [mem_closedBall, dist_eq_norm]
          exact h1
        show ‖f (Φ (r⁻¹ * (p.1 - s₀)) (Poincare.SimonGMT.Chapter03.blowUpMap x r p.2)) * θ p.2‖ ≤ 0
        rw [hf0, zero_mul, norm_zero]
  -- Step 7 (first half): undo the blow-up in `ℝ^{P+1}`.
  have hL1 : ∫ z in Poincare.SimonGMT.Chapter03.blowUpMap (Φ s₀ x) r ''
        {y : Eucl (P + 1) | π y ∈ M ∧ EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1},
        f z * θ (π (Φ s₀ x + r • z)) ∂(μHE[m + 1] : Measure (Eucl (P + 1))) =
      (r ^ (m + 1))⁻¹ * ∫ p, G p ∂(((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)).prod
        ((μHE[m] : Measure (Eucl P)).restrict M)) := by
    rw [Submission.fiw_tl_blowup_setIntegral (P + 1) (m + 1) (Φ s₀ x) r _
      (fun z => f z * θ (π (Φ s₀ x + r • z))) hr]
    congr 1
    have hmeas := Submission.iwl_cr_ip_wt_product_measure P m hMP M hMmeas hMrect hMfin
    show ∫ w, f (Poincare.SimonGMT.Chapter03.blowUpMap (Φ s₀ x) r w) *
        θ (π (Φ s₀ x + r • Poincare.SimonGMT.Chapter03.blowUpMap (Φ s₀ x) r w))
        ∂((μHE[m + 1] : Measure (Eucl (P + 1))).restrict
          {y : Eucl (P + 1) | π y ∈ M ∧ EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1}) = _
    rw [hmeas, hemb.integral_map]
    have hback : ∀ w, Φ s₀ x + r • Poincare.SimonGMT.Chapter03.blowUpMap (Φ s₀ x) r w = w := by
      intro w
      simp only [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, mul_inv_cancel₀ hr.ne',
        one_smul, add_sub_cancel]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    show f (Poincare.SimonGMT.Chapter03.blowUpMap (Φ s₀ x) r (Φ p.1 p.2)) *
      θ (π (Φ s₀ x + r • Poincare.SimonGMT.Chapter03.blowUpMap (Φ s₀ x) r (Φ p.1 p.2))) = G p
    rw [hback, hπΦ, hprod]
  -- Fubini and the interval.
  let H : ℝ → ℝ := fun s => ∫ u in M, G (s, u) ∂(μHE[m] : Measure (Eucl P))
  have hL2 : ∫ p, G p ∂(((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)).prod
        ((μHE[m] : Measure (Eucl P)).restrict M)) = ∫ s in (0 : ℝ)..1, H s := by
    rw [integral_prod _ hGint, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo]
  -- Substitution `s = r σ + s₀`.
  have hsub : ∫ σ in (-s₀ / r)..((1 - s₀) / r), H (r * σ + s₀) = r⁻¹ * ∫ s in (0 : ℝ)..1, H s := by
    rw [intervalIntegral.integral_comp_mul_add H hr.ne' s₀, smul_eq_mul]
    congr 3
    · field_simp
      ring
    · field_simp
      ring
  -- The slices: `H (r σ + s₀) = rᵐ · a σ`.
  have hslice : ∀ σ : ℝ, H (r * σ + s₀) = r ^ m * ∫ w in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M,
      f (Φ σ w) * θ (x + r • w) ∂(μHE[m] : Measure (Eucl P)) := by
    intro σ
    rw [Submission.fiw_tl_blowup_setIntegral P m x r M (fun w => f (Φ σ w) * θ (x + r • w)) hr,
      ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero m hr.ne'), one_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    have hσ : r⁻¹ * (r * σ + s₀ - s₀) = σ := by
      rw [add_sub_cancel_right, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
    simp only [G, hσ, Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, mul_inv_cancel₀ hr.ne',
      one_smul, add_sub_cancel]
  -- Assemble.
  have hab : -s₀ / r ≤ (1 - s₀) / r := div_le_div_of_nonneg_right (by linarith) hr.le
  rw [hL1, hL2, integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le hab]
  have hsub' := hsub
  simp only [hslice, intervalIntegral.integral_const_mul] at hsub'
  -- `hsub' : r ^ m * ∫ a = r⁻¹ * ∫₀¹ H`
  have hrm : (r ^ (m + 1))⁻¹ = (r ^ m)⁻¹ * r⁻¹ := by rw [pow_succ, mul_inv]
  rw [hrm, mul_assoc, ← hsub', ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero m hr.ne'), one_mul]

## Key steps

1. η(Φ(s,u)) = Φ(r⁻¹(s − s₀), η′u), y* + r·η(w) = w and x + r·η′(u) = u.
2. G(s,u) = f(Φ(r⁻¹(s−s₀), η′u))·θ(u) is ρ-integrable, bounded by C_f|θ(u)|·1_{B̄(x,rR)}(u), with ρ = (L¹⌞(0,1)) ⊗ Hᵐ⌞M.
3. blowup_cov in ℝ^{P+1} and product_measure with MeasurableEmbedding.integral_map: LHS = (r^{m+1})⁻¹∫ G dρ.
4. Fubini: ∫ G dρ = ∫_0^1 H(s) ds with H(s) = ∫_M G(s,u) dHᵐ(u).
5. Substituting s = rσ + s₀ gives ∫_{−s₀/r}^{(1−s₀)/r} H(rσ+s₀) dσ = r⁻¹∫_0^1 H, and blowup_cov in ℝ^P gives H(rσ+s₀) = r^m·a_r(σ).
6. Combine: LHS = ∫_{−s₀/r}^{(1−s₀)/r} a_r = ∫ 1_{(−s₀/r,(1−s₀)/r]}·a_r.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean GMT/Ch06/Contract.lean; cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean; sha256sum (ea3ee0dd…853d)`
- `python3 -I: dag.json status/lean_name/lean_statement of root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1* and of root.flat_iff_weak-a1.tangent_locality-a1.blowup_change_of_variables-a1; its accepted-candidate.json contract.lean_statement == dag lean_statement and audit.comparator_passed`
- `git show 91a22d1bfc9063820dd1583526d3d097beffd0ec:GMT/Ch06/Submission.lean (accepted proof and declaration layout of Submission.fiw_tl_blowup_setIntegral)`
- `grep -rhoE "iwl_cr_ip_[A-Za-z0-9_']+" nodes dag.json (finds the sibling product_triple proposals iwl_cr_ip_pt_slab_restrict_eq_map, iwl_cr_ip_pt_slab_transfer, iwl_cr_ip_pt_cylinder_nullMeasurableSet, iwl_cr_ip_pt_cylinder_countablyRectifiable, iwl_cr_ip_pt_frame_orthonormal); grep -rhoE 'iwl_cr_ip_wt[A-Za-z0-9_]*' nodes dag.json (no match)`
- `python3 -I: nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a1/decomposition-v1.json (parent split, blowup_cov entry) and sibling decomposition-v1.json files (measure_identity, slice_formula: no split; product_triple: split with the names above)`
- `grep -n "theorem\|def\|abbrev" in simongmt Poincare/SimonGMT/Chapter03/Rectifiable.lean: CountablyRectifiable (l.34), countablyRectifiable_range (l.64), blowUpMap (l.96), regular_euclideanHausdorffMeasure_restrict_submodule (l.187), HasWeightedApproximateTangentSpaceAt (l.330)`
- `grep -rn in local-references mathlib/Mathlib: tendsto_integral_filter_of_dominated_convergence, continuous_of_dominated, intervalIntegral.integral_comp_mul_add, integral_Ioc_eq_integral_Ioo, intervalIntegral.integral_of_le, Integrable.comp_snd, MeasureTheory.AEStronglyMeasurable.comp_snd, aestronglyMeasurable_iUnion_iff, integrable_indicator_iff, integral_mono_of_nonneg, norm_integral_le_integral_norm, setIntegral_indicator, Continuous.integrable_of_hasCompactSupport, Measure.prod.instIsFiniteMeasureOnCompacts, integral_prod, MeasurableEmbedding.integral_map, HasCompactMulSupport.comp_homeomorph, Fintype.range_linearCombination, LinearMap.coe_toContinuousLinearMap', EuclideanSpace.real_norm_sq_eq, EuclideanSpace.equiv, abs_le_of_sq_le_sq, le_of_sq_le_sq, Filter.Tendsto.const_mul_atTop, Filter.Tendsto.const_mul_atTop_of_neg, tendsto_inv_nhdsGT_zero, Filter.Tendsto.eventually_lt_const, Continuous.bounded_above_of_compact_support, Continuous.finCons`
- `python3 -I /tmp/ptdec/scripts/gen.py and final.py (lean_contract.validate_lean_statement on all 7 child types; key/name regexes; dependency acyclicity)`
- `python3 -I /tmp/ptdec/scripts/layout.py (gmt-compare.py child_modules, contract mode) and lake env lean /tmp/ptdec/layout/AllChallenges.lean (7 exact comparator challenge targets)`
- `lake env lean /tmp/ptdec/Asm.lean (parent assembly from the 7 child stubs; sorryAx only from stubs)`
- `lake env lean /tmp/ptdec/C1.lean … C6.lean and /tmp/ptdec/Full.lean (complete child proofs + accepted blowup_cov proof + parent assembly + solution-side exact checks; #print axioms = [propext, Classical.choice, Quot.sound])`
- `independent reviewer subagent: re-ran Full.lean and AllChallenges.lean, compared payload statements byte-for-byte with the checked Lean files (scripts under /tmp/ptrev); verdict ACCEPT, minor wording fixes applied`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-b1e58acdf8/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-b1e58acdf8/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-b1e58acdf8/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-6184ff8144/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-930be90ff5/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-ef3d70356e/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-ef3d70356e/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-tangent-locality-a1-blowup-change-of-variables-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Order/OrderClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Order/Field.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Filter/AtTopBot/Field.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Algebra/Order/Ring/Abs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Finsupp/LinearCombination.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/ptdec/scripts/gen.py`
- `/tmp/ptdec/scripts/layout.py`
- `/tmp/ptdec/scripts/full.py`
- `/tmp/ptdec/scripts/final.py`
- `/tmp/ptdec/Check.lean`
- `/tmp/ptdec/layout/AllChallenges.lean`
- `/tmp/ptdec/Asm.lean`
- `/tmp/ptdec/Full.lean`

Snapshot: project d8d46c95, Mathlib 25730c7c. The snapshot's GMT/Ch06/Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean (sha256 ea3ee0dd…853d).

DAG and naming:
- No accepted declaration states any of the six new child statements, so nothing new is reused.
- The only reuse is fiw_tl_blowup_setIntegral: accepted, comparator_passed, with an identical frozen type.
- The sibling product_triple is concurrently proposing iwl_cr_ip_pt_* names (not accepted), two of which overlap product_measure and product_plane (a) mathematically. This node therefore uses the unreserved prefix iwl_cr_ip_wt_, with no match anywhere in the run directory.

SimonGMT Chapter03/Rectifiable.lean supplies blowUpMap, HasWeightedApproximateTangentSpaceAt (Simon Ch. 3, 1.7), countablyRectifiable_range and regular_euclideanHausdorffMeasure_restrict_submodule.

Mathlib supplies every tool used:
- dominated convergence along 𝓝[>] 0 and continuity of parametric integrals (tendsto_integral_filter_of_dominated_convergence, continuous_of_dominated);
- interval substitution (intervalIntegral.integral_comp_mul_add);
- Fubini (integral_prod, Integrable.comp_snd, AEStronglyMeasurable.comp_snd);
- change of variables along the homeomorphism Φ′ (MeasurableEmbedding.integral_map);
- integrability of compactly supported continuous functions (Continuous.integrable_of_hasCompactSupport, Measure.prod.instIsFiniteMeasureOnCompacts);
- the integral estimates integral_mono_of_nonneg and norm_integral_le_integral_norm.

Lean checks:
- All 7 child types elaborate in the exact comparator layout.
- All 6 new children are fully proved with axioms [propext, Classical.choice, Quot.sound].
- The frozen parent type is proved from them and the accepted blow-up lemma with the same axioms.
- An independent reviewer re-ran these checks and accepted the split.

Public sources for the mathematics: L. Simon, Introduction to Geometric Measure Theory, Ch. 3 §1 (Def. 1.7, weighted approximate tangent spaces) and Ch. 6, 3.2(2) (product with an interval); Federer, Geometric Measure Theory, 3.2.23 (product formula behind (MP)).
