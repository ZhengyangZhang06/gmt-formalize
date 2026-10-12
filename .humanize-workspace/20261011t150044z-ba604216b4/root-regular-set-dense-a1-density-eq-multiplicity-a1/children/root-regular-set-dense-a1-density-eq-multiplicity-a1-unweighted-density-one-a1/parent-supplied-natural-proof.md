# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_dense-a1.density_eq_multiplicity-a1`
- Child DAG node: `root.regular_set_dense-a1.density_eq_multiplicity-a1.unweighted_density_one-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 (Unweighted density) of the parent proof. This is Simon Ch. 3, Remark 1.5(3) (chapter-03.txt lines 95-101), with Definition 1.4 at lines 77-84. In Definition 1.4 one chooses f with 0 ≤ f ≤ 1, f ≡ 1 on B_1(0) and f ≡ 0 off B_{1+ε}(0), and lets ε ↓ 0; this gives lim_{ρ↓0} (ω_nρ^n)^{-1} H^n(M ∩ B_ρ(x)) = 1. As in the parent proof, a second cut-off from inside gives the matching lower bound. Only closed balls are needed. The finiteness of H^n(M ∩ B̄_s(x)) is part of the standing hypothesis of Definition 1.4; it makes the Bochner integrals in the hypothesis genuine for small r. The proof covers n = 0 (ℝ^0 is a point and ω_0 = 1) without a separate case. If n > P, no subspace Q has dimension n, so the hypothesis cannot hold.

Notation: H^n = μHE[n] on ℝ^P; ω := unitBallVolume n, and w is ω as a real number. For r > 0, η_r := η_{x,r} = blowUpMap x r, ν_r := H^n⌞η_r(M), and μ_Q := H^n⌞Q. All balls are closed.

1. (ω_n.) ω = vol(B_1(0) ⊆ ℝ^n) is positive, being the measure of a nonempty open set (measure_ball_pos), and finite (measure_ball_lt_top). Hence w > 0 and ω = ofReal(w).

2. (Plane balls.) Since dim Q = n, reindexing an orthonormal basis of Q by Fin n gives a linear isometry ι : ℝ^n → ℝ^P with range Q. For t ≥ 0, ι(B̄_t(0)) = Q ∩ B̄_t(0), because |ι v| = |v| and ι maps onto Q. Three facts compute this measure:
- H^n is invariant under isometries (Isometry.euclideanHausdorffMeasure_image);
- H^n equals Lebesgue measure on ℝ^n (EuclideanSpace.euclideanHausdorffMeasure_eq_volume);
- vol(B̄_t(0)) = t^n vol(B_1(0)) (Measure.addHaar_closedBall, with finrank ℝ^n = n).
Hence μ_Q(B̄_t(0)) = H^n(Q ∩ B̄_t(0)) = ω·t^n. This is finite, with real value w t^n.

3. (Scaling.) Let r > 0 and A ⊆ ℝ^P. Then η_r(A) = r^{-1}·(A − x). The translation y ↦ y − x is an isometry, and H^n(cS) = |c|^n H^n(S) (Measure.euclideanHausdorffMeasure_smul₀). So H^n(η_r(A)) = r^{-n} H^n(A). Moreover |η_r(z)| ≤ t ⟺ dist(z, x) ≤ tr, so η_r(M) ∩ B̄_t(0) = η_r(M ∩ B̄_{tr}(x)). Hence
 ν_r(B̄_t(0)) = H^n(η_r(M) ∩ B̄_t(0)) = r^{-n} H^n(M ∩ B̄_{tr}(x)).
In particular ν_r(B̄_t(0)) < ∞ whenever tr ≤ s, by monotonicity and the hypothesis H^n(M ∩ B̄_s(x)) < ∞.

4. (Cut-off functions.) For 0 < a < b let g_{a,b}(y) := max{0, min{1, (b − |y|)/(b − a)}}.
- g_{a,b} is continuous.
- It vanishes when |y| ≥ b, so its support lies in the compact ball B̄_b(0) and g_{a,b} ∈ C_c(ℝ^P, ℝ).
- 0 ≤ g_{a,b} ≤ 1, and g_{a,b} = 1 when |y| ≤ a.
Consequently 1_{B̄_a(0)} ≤ g_{a,b} ≤ 1_{B̄_b(0)} pointwise.

5. (Integrability.) Let ν' be a measure on ℝ^P with ν'(B̄_t(0)) < ∞. Then 1_{B̄_t(0)} is ν'-integrable, and by domination so is every continuous f with 0 ≤ f ≤ 1_{B̄_t(0)}. By steps 2-3 this applies to ν_r when tr ≤ s, to μ_Q for all t, and to the cut-offs of step 4. For such f, ∫ f dν' and ∫ 1_{B̄_t(0)} dν' = ν'(B̄_t(0)) (as a real number; integral_indicator_one) are genuine finite integrals, and integral_mono compares them.

6. (Normalised mass.) For r > 0 put a(r) := r^{-n}·H^n(M ∩ B̄_r(x)). This is a real number since H^n(M ∩ B̄_r(x)) < ∞ for r ≤ s. By step 3 with t = 1, the real value of ν_r(B̄_1(0)) is a(r).

7. (a(r) → w.) It suffices to show that, as r → 0 within (0, ∞), eventually c < a(r) for each c < w, and eventually a(r) < c for each c > w.
(i) Let c < w.
- The map ε ↦ w(1 − ε)^n is continuous with value w at 0. Pick ε ∈ (0, 1) with c < w(1 − ε)^n and let f₁ := g_{1−ε,1}.
- By steps 2, 4 and 5, ∫_Q f₁ dH^n ≥ ∫ 1_{B̄_{1−ε}(0)} dμ_Q = w(1 − ε)^n > c.
- By the hypothesis applied to f₁, ∫_{η_r(M)} f₁ dH^n → ∫_Q f₁ dH^n, so eventually ∫_{η_r(M)} f₁ dH^n > c.
- For 0 < r ≤ s/2 (so 1·r ≤ s), f₁ ≤ 1_{B̄_1(0)} gives ∫_{η_r(M)} f₁ dH^n ≤ ν_r(B̄_1(0)) = a(r) (steps 5 and 6).
Hence eventually a(r) > c.
(ii) Let c > w.
- Pick ε ∈ (0, 1) with w(1 + ε)^n < c and let f₂ := g_{1,1+ε}.
- ∫_Q f₂ dH^n ≤ ∫ 1_{B̄_{1+ε}(0)} dμ_Q = w(1 + ε)^n < c, so eventually ∫_{η_r(M)} f₂ dH^n < c.
- For 0 < r ≤ s/2 we have (1 + ε)r ≤ 2r ≤ s, so f₂ is ν_r-integrable (step 5).
- 1_{B̄_1(0)} ≤ f₂ gives a(r) = ν_r(B̄_1(0)) ≤ ∫_{η_r(M)} f₂ dH^n.
Hence eventually a(r) < c.
By the order-topology characterisation (tendsto_order), a(r) → w as r ↓ 0.

8. (Back to [0, ∞].) Let 0 < ρ ≤ s. Write H^n(M ∩ B̄_ρ(x)) = ofReal(m), where m is its (finite) real value; also ω = ofReal(w) and ω·ofReal(ρ^n) = ofReal(wρ^n) with wρ^n > 0. Then
 H^n(M ∩ B̄_ρ(x))/(ω·ofReal(ρ^n)) = ofReal(m/(wρ^n)) = ofReal(a(ρ)/w)
(ENNReal.ofReal_div_of_pos). Since a(ρ)/w → w/w = 1 and ofReal is continuous, ofReal(a(ρ)/w) → 1. The two functions agree on (0, s], a right-neighbourhood of 0, so the quotient tends to 1 as ρ ↓ 0. ∎

Appendix (verified Lean realization of the numbered proof above). The declaration below compiles with Lean v4.35.0-rc3 and Mathlib 25730c7c. It was placed after `import GMT.Ch07.Submission` in the child comparator scope, i.e. inside `namespace GMT.Ch07` with the frozen contract's `open` commands, after the contract's `noncomputable section ... end`. `exact Submission.rsd_tendsto_closedBall_density_of_approxTangent` closes the frozen type, and `#print axioms` reports only propext, Classical.choice and Quot.sound.

```lean
open scoped Pointwise CompactlySupported in
theorem Submission.rsd_tendsto_closedBall_density_of_approxTangent : ∀ (P n : ℕ) (M : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)) (s : ℝ), 0 < s → μHE[n] (M ∩ closedBall x s) ≠ ∞ → HasApproximateTangentSpaceAt n M x Q → Tendsto (fun ρ : ℝ => μHE[n] (M ∩ closedBall x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 1) := by
  intro P n M x Q s hs hfin hT
  obtain ⟨hQ, hconv⟩ := hT
  -- Step 1: `ωₙ ∈ (0, ∞)`
  set ω := unitBallVolume n with hωdef
  have hω0 : ω ≠ 0 := (measure_ball_pos volume (0 : Euclid n) one_pos).ne'
  have hωtop : ω ≠ ∞ := measure_ball_lt_top.ne
  set w := ω.toReal with hwdef
  have hw : 0 < w := ENNReal.toReal_pos hω0 hωtop
  -- Step 2: `Hⁿ(Q ∩ B̄_t(0)) = ωₙ tⁿ`
  have hplane0 : ∀ t : ℝ, 0 ≤ t →
      μHE[n] ((Q : Set (Euclid P)) ∩ closedBall 0 t) = ω * ENNReal.ofReal (t ^ n) := by
    intro t ht
    let b : OrthonormalBasis (Fin n) ℝ Q := (stdOrthonormalBasis ℝ Q).reindex (finCongr hQ)
    let ι : Euclid n →ₗᵢ[ℝ] Euclid P := Q.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry
    have himage : ι '' closedBall 0 t = (Q : Set (Euclid P)) ∩ closedBall 0 t := by
      ext y
      constructor
      · rintro ⟨v, hv, rfl⟩
        refine ⟨(b.repr.symm v).2, ?_⟩
        rw [mem_closedBall, dist_zero_right] at hv ⊢
        have : ‖((b.repr.symm v : Q) : Euclid P)‖ = ‖v‖ := b.repr.symm.norm_map v
        simpa [ι, this] using hv
      · rintro ⟨hyQ, hy⟩
        refine ⟨b.repr ⟨y, hyQ⟩, ?_, ?_⟩
        · rw [mem_closedBall, dist_zero_right] at hy ⊢
          simpa using hy
        · simp [ι]
    rw [← himage, ι.isometry.euclideanHausdorffMeasure_image,
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
      Measure.addHaar_closedBall _ _ ht, finrank_euclideanSpace_fin, hωdef, unitBallVolume, mul_comm]
  -- Step 3: scaling `Hⁿ(η_{x,r}(A)) = r⁻ⁿ Hⁿ(A)` and `η_{x,r}(M) ∩ B̄_t(0) = η_{x,r}(M ∩ B̄_{tr}(x))`
  have hscale : ∀ r : ℝ, 0 < r → ∀ A : Set (Euclid P),
      μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' A) = ENNReal.ofReal (r⁻¹ ^ n) * μHE[n] A := by
    intro r hr A
    have h1 : Poincare.SimonGMT.Chapter03.blowUpMap x r '' A = r⁻¹ • ((fun y => y - x) '' A) := by
      ext y
      simp [Poincare.SimonGMT.Chapter03.blowUpMap, Set.mem_smul_set]
    have hiso : Isometry (fun y : Euclid P => y - x) :=
      Isometry.of_dist_eq (fun a c => by simp [dist_eq_norm])
    rw [h1, Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hr.ne'),
      hiso.euclideanHausdorffMeasure_image, ENNReal.smul_def, smul_eq_mul]
    congr 1
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
    simp [abs_of_pos hr]
  have himg : ∀ r : ℝ, 0 < r → ∀ t : ℝ,
      Poincare.SimonGMT.Chapter03.blowUpMap x r '' M ∩ closedBall 0 t =
        Poincare.SimonGMT.Chapter03.blowUpMap x r '' (M ∩ closedBall x (t * r)) := by
    intro r hr t
    have key : ∀ z : Euclid P,
        ‖Poincare.SimonGMT.Chapter03.blowUpMap x r z‖ ≤ t ↔ dist z x ≤ t * r := by
      intro z
      simp only [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, Real.norm_eq_abs, abs_inv,
        abs_of_pos hr, dist_eq_norm]
      rw [inv_mul_le_iff₀ hr, mul_comm r t]
    ext y
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hy⟩
      rw [mem_closedBall, dist_zero_right, key] at hy
      exact ⟨z, ⟨hz, hy⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hzb⟩, rfl⟩
      refine ⟨⟨z, hz, rfl⟩, ?_⟩
      rw [mem_closedBall, dist_zero_right, key]
      exact hzb
  have hνball : ∀ r : ℝ, 0 < r → ∀ t : ℝ,
      (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap x r '' M)) (closedBall 0 t) =
        ENNReal.ofReal (r⁻¹ ^ n) * μHE[n] (M ∩ closedBall x (t * r)) := by
    intro r hr t
    rw [Measure.restrict_apply measurableSet_closedBall, inter_comm, himg r hr t, hscale r hr]
  have hmfin : ∀ r : ℝ, r ≤ s → μHE[n] (M ∩ closedBall x r) ≠ ∞ := fun r hr =>
    ne_top_of_le_ne_top hfin (measure_mono (inter_subset_inter_right _ (closedBall_subset_closedBall hr)))
  have hνfin : ∀ r : ℝ, 0 < r → ∀ t : ℝ, t * r ≤ s →
      (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap x r '' M)) (closedBall 0 t) ≠ ∞ := by
    intro r hr t ht
    rw [hνball r hr t]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hmfin _ ht)
  -- Step 4: radial cut-off functions in `C_c`
  have hbump : ∀ a b : ℝ, 0 < a → a < b → ∃ f : C_c(Euclid P, ℝ), Continuous f ∧ (0 ≤ ⇑f) ∧
      (closedBall (0 : Euclid P) a).indicator 1 ≤ ⇑f ∧ ⇑f ≤ (closedBall (0 : Euclid P) b).indicator 1 := by
    intro a b ha hab
    have hcont : Continuous (fun y : Euclid P => max 0 (min 1 ((b - ‖y‖) / (b - a)))) :=
      continuous_const.max (continuous_const.min ((continuous_const.sub continuous_norm).div_const _))
    have hzero : ∀ y : Euclid P, b ≤ ‖y‖ → max 0 (min 1 ((b - ‖y‖) / (b - a))) = 0 := by
      intro y hy
      have h1 : (b - ‖y‖) / (b - a) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      rw [max_eq_left ((min_le_right _ _).trans h1)]
    let f : C_c(Euclid P, ℝ) :=
      { toFun := fun y => max 0 (min 1 ((b - ‖y‖) / (b - a)))
        continuous_toFun := hcont
        hasCompactSupport' := by
          refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid P) b) ?_
          intro y hy
          rw [mem_closedBall, dist_zero_right, not_le] at hy
          exact hzero y hy.le }
    have hf : ∀ y, f y = max 0 (min 1 ((b - ‖y‖) / (b - a))) := fun y => rfl
    refine ⟨f, f.continuous, fun y => by rw [hf]; exact le_max_left _ _, ?_, ?_⟩
    · intro y
      by_cases hy : y ∈ closedBall (0 : Euclid P) a
      · rw [indicator_of_mem hy, Pi.one_apply, hf]
        rw [mem_closedBall, dist_zero_right] at hy
        have : 1 ≤ (b - ‖y‖) / (b - a) := by
          rw [le_div_iff₀ (by linarith)]; linarith
        rw [min_eq_left this, max_eq_right zero_le_one]
      · rw [indicator_of_notMem hy, hf]; exact le_max_left _ _
    · intro y
      by_cases hy : y ∈ closedBall (0 : Euclid P) b
      · rw [indicator_of_mem hy, Pi.one_apply, hf]
        exact max_le zero_le_one (min_le_left _ _)
      · rw [indicator_of_notMem hy, hf, hzero]
        rw [mem_closedBall, dist_zero_right, not_le] at hy
        exact hy.le
  -- integrability of functions dominated by the indicator of a finite-measure closed ball
  have hindint : ∀ (ν : Measure (Euclid P)) (t : ℝ), ν (closedBall 0 t) ≠ ∞ →
      Integrable ((closedBall (0 : Euclid P) t).indicator (1 : Euclid P → ℝ)) ν := fun ν t h =>
    (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const h)
  have hdomint : ∀ (ν : Measure (Euclid P)) (f : Euclid P → ℝ) (t : ℝ), Continuous f →
      ν (closedBall 0 t) ≠ ∞ → 0 ≤ f → f ≤ (closedBall (0 : Euclid P) t).indicator 1 →
      Integrable f ν := by
    intro ν f t hf hfin' h0 hle
    refine (hindint ν t hfin').mono' hf.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (h0 y)]
    exact hle y
  -- Step 5–6: sandwich
  set a : ℝ → ℝ := fun r => (r⁻¹) ^ n * (μHE[n] (M ∩ closedBall x r)).toReal with hadef
  have hareal : ∀ r : ℝ, 0 < r →
      (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap x r '' M)).real (closedBall 0 1) = a r := by
    intro r hr
    rw [measureReal_def, hνball r hr 1, one_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity)]
  have hplane : ∀ t : ℝ, 0 ≤ t →
      (μHE[n].restrict (Q : Set (Euclid P))) (closedBall 0 t) = ω * ENNReal.ofReal (t ^ n) := by
    intro t ht
    rw [Measure.restrict_apply measurableSet_closedBall, inter_comm, hplane0 t ht]
  have hplanefin : ∀ t : ℝ, 0 ≤ t → (μHE[n].restrict (Q : Set (Euclid P))) (closedBall 0 t) ≠ ∞ := by
    intro t ht
    rw [hplane t ht]
    exact ENNReal.mul_ne_top hωtop ENNReal.ofReal_ne_top
  have hplanereal : ∀ t : ℝ, 0 ≤ t →
      (μHE[n].restrict (Q : Set (Euclid P))).real (closedBall 0 t) = w * t ^ n := by
    intro t ht
    rw [measureReal_def, hplane t ht, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  -- Step 7: `a r → ωₙ`
  have ha : Tendsto a (𝓝[>] 0) (𝓝 w) := by
    rw [tendsto_order]
    constructor
    · intro c hc
      have hcont : Tendsto (fun ε : ℝ => w * (1 - ε) ^ n) (𝓝[>] 0) (𝓝 w) := by
        have : Continuous (fun ε : ℝ => w * (1 - ε) ^ n) := by fun_prop
        simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
      obtain ⟨ε, hcε, hε⟩ :=
        ((hcont.eventually (lt_mem_nhds hc)).and (Ioo_mem_nhdsGT one_pos)).exists
      obtain ⟨f, hfc, hf0, hfge, hfle⟩ := hbump (1 - ε) 1 (by linarith [hε.2]) (by linarith [hε.1])
      -- `∫_Q f ≥ ωₙ (1-ε)ⁿ`
      have hQ1 : w * (1 - ε) ^ n ≤ ∫ y in (Q : Set (Euclid P)), f y ∂μHE[n] := by
        rw [← hplanereal (1 - ε) (by linarith [hε.2]), ← integral_indicator_one measurableSet_closedBall]
        exact integral_mono (hindint _ _ (hplanefin _ (by linarith [hε.2])))
          (hdomint _ _ 1 hfc (hplanefin _ zero_le_one) hf0 hfle) hfge
      filter_upwards [(tendsto_order.1 (hconv f)).1 c (hcε.trans_le hQ1),
        Ioc_mem_nhdsGT (half_pos hs)] with r hr1 hr2
      -- `∫_{η(M)} f ≤ a r`
      have h1 : (1 : ℝ) * r ≤ s := by linarith [hr2.2]
      have hle : ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n] ≤ a r := by
        rw [← hareal r hr2.1, ← integral_indicator_one measurableSet_closedBall]
        exact integral_mono (hdomint _ _ 1 hfc (hνfin r hr2.1 1 h1) hf0 hfle)
          (hindint _ _ (hνfin r hr2.1 1 h1)) hfle
      exact hr1.trans_le hle
    · intro c hc
      have hcont : Tendsto (fun ε : ℝ => w * (1 + ε) ^ n) (𝓝[>] 0) (𝓝 w) := by
        have : Continuous (fun ε : ℝ => w * (1 + ε) ^ n) := by fun_prop
        simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
      obtain ⟨ε, hcε, hε⟩ :=
        ((hcont.eventually (gt_mem_nhds hc)).and (Ioo_mem_nhdsGT one_pos)).exists
      obtain ⟨f, hfc, hf0, hfge, hfle⟩ := hbump 1 (1 + ε) one_pos (by linarith [hε.1])
      -- `∫_Q f ≤ ωₙ (1+ε)ⁿ`
      have hQ2 : ∫ y in (Q : Set (Euclid P)), f y ∂μHE[n] ≤ w * (1 + ε) ^ n := by
        rw [← hplanereal (1 + ε) (by linarith [hε.1]), ← integral_indicator_one measurableSet_closedBall]
        exact integral_mono (hdomint _ _ (1 + ε) hfc (hplanefin _ (by linarith [hε.1])) hf0 hfle)
          (hindint _ _ (hplanefin _ (by linarith [hε.1]))) hfle
      filter_upwards [(tendsto_order.1 (hconv f)).2 c (hQ2.trans_lt hcε),
        Ioc_mem_nhdsGT (half_pos hs)] with r hr1 hr2
      -- `a r ≤ ∫_{η(M)} f`
      have h1 : (1 : ℝ) * r ≤ s := by linarith [hr2.2]
      have h2 : (1 + ε) * r ≤ s := by nlinarith [hr2.1, hr2.2, hε.2]
      have hge : a r ≤ ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n] := by
        rw [← hareal r hr2.1, ← integral_indicator_one measurableSet_closedBall]
        exact integral_mono (hindint _ _ (hνfin r hr2.1 1 h1))
          (hdomint _ _ (1 + ε) hfc (hνfin r hr2.1 _ h2) hf0 hfle) hfge
      exact hge.trans_lt hr1
  -- Step 8: conversion to the `ℝ≥0∞` quotient
  have hconvert : ∀ ρ : ℝ, 0 < ρ → ρ ≤ s →
      μHE[n] (M ∩ closedBall x ρ) / (ω * ENNReal.ofReal (ρ ^ n)) = ENNReal.ofReal (a ρ / w) := by
    intro ρ hρ hρs
    have hρn : 0 < ρ ^ n := pow_pos hρ n
    rw [← ENNReal.ofReal_toReal (hmfin ρ hρs), ← ENNReal.ofReal_toReal hωtop,
      ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ← ENNReal.ofReal_div_of_pos (mul_pos hw hρn)]
    congr 1
    simp only [hadef, inv_pow]
    field_simp
  have hlim : Tendsto (fun ρ : ℝ => ENNReal.ofReal (a ρ / w)) (𝓝[>] 0) (𝓝 1) := by
    have := ENNReal.tendsto_ofReal (ha.div_const w)
    rwa [div_self hw.ne', ENNReal.ofReal_one] at this
  refine hlim.congr' ?_
  filter_upwards [Ioc_mem_nhdsGT hs] with ρ hρ
  exact (hconvert ρ hρ.1 hρ.2).symm
```

## Key steps

1. H^n(Q ∩ B̄_t(0)) = ω_n t^n, via a linear isometry ℝ^n ≅ Q and H^n = Lebesgue measure on ℝ^n.
2. H^n(η_{x,r}(M) ∩ B̄_t(0)) = r^{-n} H^n(M ∩ B̄_{tr}(x)), which is finite when tr ≤ s.
3. The radial cut-offs in C_c satisfy g_{1−ε,1} ≤ 1_{B̄_1(0)} ≤ g_{1,1+ε}. So a(r) = r^{-n}H^n(M ∩ B̄_r(x)) lies between the blow-up integrals of the two cut-offs.
4. Tangent-plane convergence and ∫_Q bounds of ω_n(1∓ε)^n give a(r) → ω_n. Converting to the [0,∞] quotient gives the limit 1.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `rg -n 'theorem ae_tendsto_rnDeriv|theorem rnDeriv_withDensity\b|theorem restrict_withDensity\b|theorem EuclideanSpace.euclideanHausdorffMeasure_eq_volume|theorem Isometry.euclideanHausdorffMeasure_image|theorem addHaar_closedBall\b|theorem addHaar_ball\b|theorem integral_indicator_one' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `grep -n 'theorem\|lemma\|def \|notation\|instance' local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `grep -n 'HasApproximateTangentSpaceAt\|^def \|^theorem ' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean; rg -n 'def blowUpMap' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `rg -n -t lean 'HasApproximateTangentSpaceAt' simongmt/Poincare; rg -n -t lean 'theorem [A-Za-z_.]*(density|Density)[A-Za-z_.]*' simongmt/Poincare/SimonGMT/Chapter03 simongmt/Poincare/SimonGMT/Chapter04`
- `rg -n -t lean 'theorem .*IMRep|IMRep\.measure.*≠ ∞|locallyIntegrable_mult' local-references/123e8435b4a2469b/project`
- `python3 -I scan of dag.json lean_statement fields for closedBall|HasApproximateTangentSpaceAt|withDensity|unitBallVolume (overlap check with other DAG nodes)`
- `grep -l '<four proposed names>' dag.json issue-workers.json DAG.md GMT/Ch07/*.lean; rg -l -t lean '<four proposed names>' simongmt GMT local-references/123e8435b4a2469b/project; git grep -l -E '<four proposed names>' over all 101 refs -- GMT`
- `sed -n 500,595p verifier/gmt-compare.py (contract_scope / child_modules: child statements elaborate after import GMT.Ch07.Submission with the replayed contract opens)`
- `lake env lean /tmp/dem-split/Children.lean (four child types elaborate in the replayed comparator scope)`
- `lake env lean /tmp/dem-split/ChildAFacts.lean (Hn(Q ∩ B̄_r(0)) = unitBallVolume n * r^n and Hn(blowUpMap x r '' A) = r^-n Hn(A))`
- `lake env lean /tmp/dem-split/AllChildren.lean (full proofs of the four children, exact-type checks `exact Submission.<name>`, conditional assembly of the selected type from the children plus rsd_massOn_eq_measure as hypothesis; #print axioms)`
- `lake env lean /tmp/dem-split/out/Solo_<name>.lean for each of the four children (standalone compilation, #print axioms)`
- `book: sed -n 77,101p chapter-03.txt; sed -n 280,325p chapter-03.txt; sed -n 561,592p chapter-01.txt; sed -n 760,975p chapter-01.txt; sed -n 730,770p chapter-06.txt; sed -n 335,360p chapter-04.txt`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1/parent-supplied-natural-proof.md`
- `/tmp/dem-split/Children.lean`
- `/tmp/dem-split/Assembly.lean`
- `/tmp/dem-split/ChildAFacts.lean`
- `/tmp/dem-split/ChildA.lean`
- `/tmp/dem-split/ChildB.lean`
- `/tmp/dem-split/ChildC.lean`
- `/tmp/dem-split/ChildD.lean`
- `/tmp/dem-split/AllChildren.lean`
- `/tmp/dem-split/out/Solo_rsd_tendsto_closedBall_density_of_approxTangent.lean`
- `/tmp/dem-split/out/Solo_rsd_ae_tendsto_withDensity_div_closedBall.lean`
- `/tmp/dem-split/out/Solo_rsd_tendsto_ball_density_of_closedBall.lean`
- `/tmp/dem-split/out/Solo_rsd_imrep_compact_measure_ne_top.lean`

The snapshot (project b4d606d, Mathlib 25730c7c) Ch07 Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

No ready-made lemma exists in the Ch07 environment for any of the four child facts:
- the project has only the IMRep structure fields (e.g. locallyIntegrable_mult) and no IMRep local-finiteness lemma;
- there is no open/closed-ball density transfer lemma and no localized Besicovitch statement;
- simongmt Chapter04/TangentDensity.lean has related lemmas (hausdorff_blowUp_image, blowUp_image_inter_closedBall, one_le_density_of_approximateTangent). They concern simongmt varifold weights, give only the lower bound d ≥ 1, and Chapter04 is not imported by the Ch07 contract, so they are not reused.

Library facts reused, located in the snapshot and exercised in compiled proofs:
- Besicovitch.ae_tendsto_rnDeriv (Covering/Besicovitch.lean:1078), Measure.rnDeriv_withDensity (Decomposition/Lebesgue.lean:591), restrict_withDensity (WithDensity.lean:215);
- Measure.addHaar_closedBall (Lebesgue/EqHaar.lean:500), integral_indicator_one (Bochner/Set.lean:533);
- in Geometry/Euclidean/Volume/Measure.lean: Isometry.euclideanHausdorffMeasure_image (line 131), Measure.euclideanHausdorffMeasure_smul₀ (line 152), EuclideanSpace.euclideanHausdorffMeasure_eq_volume (line 187);
- simongmt HasApproximateTangentSpaceAt (Rectifiable.lean:102) and blowUpMap (Rectifiable.lean:96).

Verification:
- All four child types elaborate in the comparator scope, i.e. import GMT.Ch07.Submission plus the replayed contract opens (verifier/gmt-compare.py, contract_scope).
- Full Lean proofs of all four children compile standalone with exact Submission.<name> type checks.
- The conditional assembly of the selected frozen type from the four children plus rsd_massOn_eq_measure compiles.
- #print axioms reports only propext, Classical.choice and Quot.sound in every case.

The four names occur nowhere in dag.json, issue-workers.json, DAG.md, GMT/, the simongmt sources, the snapshot project, or any of the 101 git refs, so they collide with no reserved declaration.
