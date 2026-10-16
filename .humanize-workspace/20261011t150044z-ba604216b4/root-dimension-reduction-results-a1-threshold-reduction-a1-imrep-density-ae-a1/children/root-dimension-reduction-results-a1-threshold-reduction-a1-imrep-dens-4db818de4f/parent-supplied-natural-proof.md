# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.threshold_reduction-a1.imrep_density_ae-a1`
- Child DAG node: `root.dimension_reduction_results-a1.threshold_reduction-a1.imrep_density_ae-a1.density_on_carrier-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1, 3 and 4 of the parent proof (node root.dimension_reduction_results-a1.threshold_reduction-a1.imrep_density_ae-a1). These are Simon Ch. 3, Remark 1.5(3), Remark 1.8 and Theorem 1.9, specialized to integer multiplicities: the level sets of θ replace Lusin's theorem in Remark 1.8(1). Two sub-arguments of the parent proof are supplied by siblings.
- Step 3 of the parent proof is the unit density of the carrier at approximate-tangent points. It is supplied by unweighted_density_one, the accepted declaration Submission.rsd_tendsto_closedBall_density_of_approxTangent. Its accepted proof is step 3's argument on closed balls: the scaling Hⁿ(η_{x,r}A) = r⁻ⁿHⁿ(A), Hⁿ(Q ∩ B̄_t(0)) = ω_ntⁿ, and radial cut-offs. The passage to open balls is supplied by closed_to_open_ball_density (Submission.rsd_tendsto_ball_density_of_closedBall).
- Lemma U, with (†), is supplied by the sibling upper_density_zero. This is the accepted declaration Submission.idtp_dema_upper_density_zero, reused at its exact type.
The parent's step 4 applies Lemma U to both μ⌞A_m and ν⌞A_m. Below it is applied once per level, to μ. The ν-term is then controlled by ν ≤ μ (step 1(c)), which gives the same estimate. The parent's identity μ(B) = m·[ν(B) − ν(A_m ∩ B)] + μ(A_m ∩ B) is used in the subtraction-free form of two inequalities in [0, ∞] (step 6).

Siblings used (exact statements):
- upper_density_zero: for every measure λ on ℝ^P with λ(K) < ∞ for all compact K, and every Borel A ⊆ ℝ^P: for Hⁿ-a.e. x with x ∉ A, λ(A ∩ B_ρ(x))/(ω_n·ofReal(ρⁿ)) → 0 as ρ ↓ 0.
- unweighted_density_one: if s > 0, Hⁿ(M ∩ B̄_s(x)) ≠ ∞ and HasApproximateTangentSpaceAt n M x Q, then Hⁿ(M ∩ B̄_ρ(x))/(ω_n·ofReal(ρⁿ)) → 1 as ρ ↓ 0.
- closed_to_open_ball_density: for every measure ν′, point x and θ′ ∈ [0, ∞], if ν′(B̄_ρ(x))/(ω_n·ofReal(ρⁿ)) → θ′, then ν′(B_ρ(x))/(ω_n·ofReal(ρⁿ)) → θ′.

Notation.
- Hⁿ := μHE[n] on ℝ^P.
- M := R.carrier, Borel by the field measurableSet_carrier.
- θ := R.mult : ℝ^P → ℕ, measurable by the field measurable_mult, with θ ≥ 1 on M by the field mult_pos.
- M′ := M ∩ W, Borel since W is open.
- μ := R.measure⌞W, i.e. μ(S) = R.measure(S ∩ W) for Borel S.
- ν := Hⁿ⌞M′.
- c(ρ) := ω_n·ofReal(ρⁿ) with ω_n := unitBallVolume n.
- B_ρ(x) is the open ball and B̄_ρ(x) the closed ball.
- All limits are taken as ρ ↓ 0 (filter 𝓝[>] 0) in [0, ∞].
Since R.measure = (Hⁿ⌞M).withDensity θ (definition IMRep.measure), we have R.measure(S′) = ∫_{S′∩M} θ dHⁿ for Borel S′ (withDensity_apply, Measure.restrict_restrict).

1. (Local finiteness and concentration; parent step 1.)
(a) For Borel S: μ(S) = R.measure(S ∩ W) = ∫_{S∩W∩M} θ dHⁿ = ∫_{S∩M′} θ dHⁿ (Measure.restrict_apply).
(b) For compact K: μ(K) = R.measure(K ∩ W) < ∞ by hypothesis (Measure.restrict_apply', W Borel).
(c) For Borel S: ν(S) = Hⁿ(S ∩ M′) = ∫_{S∩M′} 1 dHⁿ ≤ ∫_{S∩M′} θ dHⁿ = μ(S), because θ(y) ≥ 1 for y ∈ M′ ⊆ M (setLIntegral_mono').

2. (Level sets; parent step 4.) For k ∈ ℕ let A_k := M′ ∩ θ⁻¹(ℕ ∖ {k}). In the parent's notation this is A_k = M′ ∖ M′_k, where M′_k = {p ∈ M′ : θ(p) = k}. It is Borel, since M′ is Borel and θ is measurable.

3. (Upper densities; parent step 4, via Lemma U.) Apply upper_density_zero with λ := μ, which is finite on compact sets by 1(b), and the Borel set A_k. For each k this gives: for Hⁿ-a.e. x with x ∉ A_k, e_k(ρ) := μ(A_k ∩ B_ρ(x))/c(ρ) → 0. As there are countably many k (ae_all_iff), for Hⁿ-a.e. x this holds simultaneously for every k with x ∉ A_k.

4. (Approximate tangent planes; parent step 3.) The field orients of R says: for (Hⁿ⌞M)-a.e. x there is a subspace Q with HasApproximateTangentSpaceAt n M x Q (and IsUnitOrientationOf (R.orient x) Q, which is not needed). As M is Borel, this means (ae_restrict_iff'): for Hⁿ-a.e. x, if x ∈ M then such a Q exists.

5. (Unit density of ν; parent step 3.) Let x ∈ M′ = M ∩ W be a point at which steps 3 and 4 hold; this is the case for Hⁿ-a.e. x ∈ M′. Fix Q as in step 4.
- W is open and x ∈ W, so there is r > 0 with B_r(x) ⊆ W. Put s := r/2 > 0. Then B̄_ρ(x) ⊆ B̄_s(x) ⊆ W for 0 < ρ ≤ s.
- Hence B̄_ρ(x) ∩ M′ = M ∩ B̄_ρ(x) for 0 < ρ ≤ s (parent step 3(b)).
- Hⁿ(M ∩ B̄_s(x)) = ν(B̄_s(x)) ≤ μ(B̄_s(x)) < ∞, by 1(c), 1(b) and compactness of B̄_s(x).
- unweighted_density_one, applied to M, x, Q and s, gives Hⁿ(M ∩ B̄_ρ(x))/c(ρ) → 1.
- For 0 < ρ ≤ s, ν(B̄_ρ(x)) = Hⁿ(B̄_ρ(x) ∩ M′) = Hⁿ(M ∩ B̄_ρ(x)) (Measure.restrict_apply). Since (0, s] belongs to 𝓝[>] 0, ν(B̄_ρ(x))/c(ρ) → 1 (Tendsto.congr').
- closed_to_open_ball_density, applied to the measure ν with θ′ = 1, gives b(ρ) := ν(B_ρ(x))/c(ρ) → 1.

6. (Splitting the ball; parent step 4.) With x as in step 5, let k := θ(x); then k ≥ 1, as x ∈ M. Let T := θ⁻¹({k}), a Borel set. Then x ∉ A_k, so e_k(ρ) → 0 by step 3. Fix ρ and write B := B_ρ(x), a Borel set.
- (B ∩ M′) ∖ T = (A_k ∩ B) ∩ M′, directly from the definitions.
- By 1(a), μ(B) = ∫_{B∩M′} θ dHⁿ. Splitting B ∩ M′ along T (lintegral_inter_add_sdiff) and using θ ≡ k on T (setLIntegral_congr_fun, lintegral_const), together with 1(a) for the Borel set A_k ∩ B, gives
 μ(B) = ∫_{(B∩M′)∩T} θ dHⁿ + ∫_{(B∩M′)∖T} θ dHⁿ = k·Hⁿ((B ∩ M′) ∩ T) + μ(A_k ∩ B).
- Similarly (measure_inter_add_sdiff), ν(B) = Hⁿ(B ∩ M′) = Hⁿ((B ∩ M′) ∩ T) + ν(A_k ∩ B).
Now use Hⁿ((B ∩ M′) ∩ T) ≤ Hⁿ(B ∩ M′) = ν(B) and ν(A_k ∩ B) ≤ μ(A_k ∩ B) (1(c)). This gives, for every ρ:
 (U) μ(B) ≤ k·ν(B) + μ(A_k ∩ B);
 (L) k·ν(B) ≤ μ(B) + k·μ(A_k ∩ B).
These two inequalities are the parent's identity μ(B) = m·[ν(B) − ν(A_m ∩ B)] + μ(A_m ∩ B), with m = k, written without subtraction in [0, ∞].

7. (Limits.) The quantity in the statement is R.measure(B_ρ(x) ∩ W)/c(ρ) = μ(B_ρ(x))/c(ρ) =: a(ρ), because the open ball is Borel (Measure.restrict_apply). Divide (U) and (L) by c(ρ) (ENNReal.div_le_div_right, ENNReal.add_div, mul_div_assoc). This gives, for every ρ,
 k·b(ρ) − k·e_k(ρ) ≤ a(ρ) ≤ k·b(ρ) + e_k(ρ),
where the left inequality is (L) rewritten with truncated subtraction (tsub_le_iff_right). Since k ∈ ℕ is finite, b(ρ) → 1 and e_k(ρ) → 0, we get:
- k·b(ρ) + e_k(ρ) → k·1 + 0 = k (ENNReal.Tendsto.const_mul, Tendsto.add);
- k·b(ρ) − k·e_k(ρ) → k − 0 = k (ENNReal.Tendsto.sub, the limit k being finite).
By the squeeze theorem, a(ρ) → k = θ(x).

8. (Conclusion.) Every x ∈ M ∩ W at which the conclusion fails lies in the union of the Hⁿ-null exceptional sets of steps 3 and 4. Hence for Hⁿ-a.e. x with x ∈ M ∩ W, R.measure(B_ρ(x) ∩ W)/(ω_n·ofReal(ρⁿ)) → θ(x) as ρ ↓ 0. The argument uses no case distinction on n, so n = 0 is included; V plays no role. ∎

Appendix (verified Lean realization of the numbered proof above; context, not part of the numbered proof). The declaration below compiles with Lean v4.35.0-rc3 and Mathlib 25730c7c after `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the frozen contract's `open` commands (`open Filter Function Set MeasureTheory Metric`, `open scoped ENNReal Topology`, `open Poincare.SimonGMT.Chapter06`, `open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt)`). It requires the three sibling declarations to be present: Submission.idtp_dema_upper_density_zero, Submission.rsd_tendsto_closedBall_density_of_approxTangent and Submission.rsd_tendsto_ball_density_of_closedBall. It was checked together with the accepted proofs of these three declarations, taken from candidates ee6fe01ff88a4fae79345889f39a366b44e8e0b9, dbef2c15948a21d9574315bea458a9edb4f708e3 and c3ca64f29e6259bb0947d084036f55b096f91e3f. The comments `-- Step k` refer to the numbered steps above. It is a single declaration with no helper lemmas, and `#print axioms Submission.dimred_tr_ida_density_on_carrier` reports only propext, Classical.choice and Quot.sound.

```lean
theorem Submission.dimred_tr_ida_density_on_carrier : ∀ (P n : ℕ) (V W : Set (Euclid P)) (R : IMRep V n), IsOpen W → (∀ K : Set (Euclid P), IsCompact K → R.measure (K ∩ W) ≠ ∞) → ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), x ∈ R.carrier ∩ W → Tendsto (fun ρ : ℝ => R.measure (ball x ρ ∩ W) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 (R.mult x : ℝ≥0∞)) := by
  intro P n V W R hW hfin
  have hWm : MeasurableSet W := hW.measurableSet
  set M := R.carrier with hM
  have hMm : MeasurableSet M := R.measurableSet_carrier
  set M' := M ∩ W with hM'
  have hM'm : MeasurableSet M' := hMm.inter hWm
  set μ : Measure (Euclid P) := R.measure.restrict W with hμ
  set ν : Measure (Euclid P) := (μHE[n] : Measure (Euclid P)).restrict M' with hν
  -- Step 1: μ is finite on compact sets, μ is a set integral over M', and ν ≤ μ
  have hμfin : ∀ K : Set (Euclid P), IsCompact K → μ K ≠ ∞ := by
    intro K hK
    rw [hμ, Measure.restrict_apply' hWm]
    exact hfin K hK
  have hmeas : ∀ S : Set (Euclid P), MeasurableSet S →
      μ S = ∫⁻ y in S ∩ M', (R.mult y : ℝ≥0∞) ∂μHE[n] := by
    intro S hS
    rw [hμ, Measure.restrict_apply hS]
    simp only [IMRep.measure]
    rw [withDensity_apply _ (hS.inter hWm), Measure.restrict_restrict (hS.inter hWm)]
    have hSet : S ∩ W ∩ M = S ∩ M' := by
      ext y
      simp only [hM', mem_inter_iff]
      tauto
    rw [hSet]
  have hνle : ∀ S : Set (Euclid P), MeasurableSet S → ν S ≤ μ S := by
    intro S hS
    rw [hmeas S hS, hν, Measure.restrict_apply hS]
    calc μHE[n] (S ∩ M') = ∫⁻ _y in S ∩ M', (1 : ℝ≥0∞) ∂μHE[n] := by simp
      _ ≤ ∫⁻ y in S ∩ M', (R.mult y : ℝ≥0∞) ∂μHE[n] := by
        apply setLIntegral_mono' (hS.inter hM'm)
        intro y hy
        have h := R.mult_pos y hy.2.1
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr h.ne'
  -- Step 2: the level sets A k = M' ∖ {θ = k}
  set A : ℕ → Set (Euclid P) := fun k => M' ∩ R.mult ⁻¹' ({k}ᶜ) with hA
  have hAm : ∀ k, MeasurableSet (A k) := fun k =>
    hM'm.inter (R.measurable_mult (measurableSet_singleton k).compl)
  -- Step 3: upper densities of μ on the other levels (sibling upper_density_zero)
  have hUD : ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), ∀ k : ℕ, x ∉ A k →
      Tendsto (fun ρ : ℝ => μ (A k ∩ ball x ρ) /
        (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 0) :=
    ae_all_iff.2 fun k => Submission.idtp_dema_upper_density_zero P n μ (A k) (hAm k) hμfin
  -- Step 4: approximate tangent planes (field orients)
  have htan : ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), x ∈ M →
      ∃ Q, HasApproximateTangentSpaceAt n M x Q := by
    have h := R.orients
    rw [ae_restrict_iff' hMm] at h
    filter_upwards [h] with x hx hxM
    obtain ⟨Q, hQ, -⟩ := hx hxM
    exact ⟨Q, hQ⟩
  filter_upwards [hUD, htan] with x hxUD hxtan hxMW
  obtain ⟨hxM, hxW⟩ := hxMW
  obtain ⟨Q, hQ⟩ := hxtan hxM
  -- Step 5: a closed ball around x inside W
  obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.1 hW x hxW
  have hs : 0 < r / 2 := by positivity
  have hsW : closedBall x (r / 2) ⊆ W := (closedBall_subset_ball (by linarith)).trans hrW
  have hloc : ∀ ρ : ℝ, ρ ≤ r / 2 → closedBall x ρ ∩ M' = M ∩ closedBall x ρ := by
    intro ρ hρ
    ext y
    simp only [hM', mem_inter_iff]
    constructor
    · rintro ⟨hyB, hyM, -⟩
      exact ⟨hyM, hyB⟩
    · rintro ⟨hyM, hyB⟩
      exact ⟨hyB, hyM, hsW (closedBall_subset_closedBall hρ hyB)⟩
  -- Step 5: unit density of ν (siblings unweighted_density_one and closed_to_open_ball_density)
  have hfinball : μHE[n] (M ∩ closedBall x (r / 2)) ≠ ∞ := by
    have h1 := hνle (closedBall x (r / 2)) measurableSet_closedBall
    have h2 := hμfin (closedBall x (r / 2)) (isCompact_closedBall x (r / 2))
    rw [hν, Measure.restrict_apply measurableSet_closedBall, hloc _ le_rfl] at h1
    exact ne_top_of_le_ne_top h2 h1
  have hTD := Submission.rsd_tendsto_closedBall_density_of_approxTangent P n M x Q (r / 2) hs
    hfinball hQ
  have hTD' : Tendsto (fun ρ : ℝ => ν (closedBall x ρ) /
      (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 1) := by
    refine hTD.congr' ?_
    have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ ∈ Ioo 0 (r / 2) := Ioo_mem_nhdsGT hs
    filter_upwards [hev] with ρ hρ
    rw [hν, Measure.restrict_apply measurableSet_closedBall, hloc ρ hρ.2.le]
  have hb := Submission.rsd_tendsto_ball_density_of_closedBall P n ν x 1 hTD'
  -- Step 6: splitting the ball along the level k = θ(x)
  set k : ℕ := R.mult x with hk
  have hxA : x ∉ A k := fun h => h.2 (by simp [hk])
  have he := hxUD k hxA
  set T : Set (Euclid P) := R.mult ⁻¹' {k} with hT
  have hTm : MeasurableSet T := R.measurable_mult (measurableSet_singleton k)
  have hset : ∀ ρ : ℝ, (ball x ρ ∩ M') \ T = (A k ∩ ball x ρ) ∩ M' := by
    intro ρ
    ext y
    simp only [hA, hT, mem_inter_iff, Set.mem_sdiff, mem_preimage, mem_compl_iff,
      mem_singleton_iff]
    tauto
  have hsplit : ∀ ρ : ℝ, μ (ball x ρ) =
      (k : ℝ≥0∞) * μHE[n] ((ball x ρ ∩ M') ∩ T) + μ (A k ∩ ball x ρ) := by
    intro ρ
    rw [hmeas _ measurableSet_ball, hmeas _ ((hAm k).inter measurableSet_ball),
      ← lintegral_inter_add_sdiff (B := T) _ _ hTm]
    congr 1
    · rw [setLIntegral_congr_fun ((measurableSet_ball.inter hM'm).inter hTm)
        (g := fun _ => (k : ℝ≥0∞)) (fun y hy => by
          have : R.mult y = k := hy.2
          simp [this])]
      simp
    · rw [hset ρ]
  have hνsplit : ∀ ρ : ℝ, ν (ball x ρ) =
      μHE[n] ((ball x ρ ∩ M') ∩ T) + ν (A k ∩ ball x ρ) := by
    intro ρ
    rw [hν, Measure.restrict_apply measurableSet_ball,
      Measure.restrict_apply ((hAm k).inter measurableSet_ball),
      ← measure_inter_add_sdiff (ball x ρ ∩ M') hTm, hset ρ]
  have hup : ∀ ρ : ℝ, μ (ball x ρ) ≤
      (k : ℝ≥0∞) * ν (ball x ρ) + μ (A k ∩ ball x ρ) := by
    intro ρ
    rw [hsplit ρ]
    have h1 : μHE[n] ((ball x ρ ∩ M') ∩ T) ≤ ν (ball x ρ) := by
      rw [hν, Measure.restrict_apply measurableSet_ball]
      exact measure_mono inter_subset_left
    exact add_le_add (mul_le_mul_right h1 _) le_rfl
  have hlow : ∀ ρ : ℝ, (k : ℝ≥0∞) * ν (ball x ρ) ≤
      μ (ball x ρ) + (k : ℝ≥0∞) * μ (A k ∩ ball x ρ) := by
    intro ρ
    rw [hνsplit ρ, mul_add, hsplit ρ, add_assoc]
    have h2 := hνle (A k ∩ ball x ρ) ((hAm k).inter measurableSet_ball)
    exact add_le_add le_rfl ((mul_le_mul_right h2 _).trans le_add_self)
  -- Step 7: the quantity in the statement is μ (ball x ρ)
  have htarget : ∀ ρ : ℝ, R.measure (ball x ρ ∩ W) = μ (ball x ρ) := by
    intro ρ
    rw [hμ, Measure.restrict_apply measurableSet_ball]
  simp_rw [htarget]
  -- Step 7: limits
  set c : ℝ → ℝ≥0∞ := fun ρ => unitBallVolume n * ENNReal.ofReal (ρ ^ n) with hc
  have hk_top : (k : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top k
  have hupper : Tendsto (fun ρ => (k : ℝ≥0∞) * (ν (ball x ρ) / c ρ) +
      μ (A k ∩ ball x ρ) / c ρ) (𝓝[>] 0) (𝓝 (k : ℝ≥0∞)) := by
    have := (ENNReal.Tendsto.const_mul hb (Or.inr hk_top)).add he
    simpa using this
  have hlower : Tendsto (fun ρ => (k : ℝ≥0∞) * (ν (ball x ρ) / c ρ) -
      (k : ℝ≥0∞) * (μ (A k ∩ ball x ρ) / c ρ)) (𝓝[>] 0) (𝓝 (k : ℝ≥0∞)) := by
    have h1 := ENNReal.Tendsto.const_mul hb (Or.inr hk_top)
    have h2 := ENNReal.Tendsto.const_mul he (Or.inr hk_top)
    have := ENNReal.Tendsto.sub h1 h2 (Or.inl (by simp))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlower hupper (fun ρ => ?_) (fun ρ => ?_)
  · simp only
    rw [tsub_le_iff_right, ← mul_div_assoc, ← mul_div_assoc, ← ENNReal.add_div]
    exact ENNReal.div_le_div_right (hlow ρ) _
  · simp only
    rw [← mul_div_assoc, ← ENNReal.add_div]
    exact ENNReal.div_le_div_right (hup ρ) _
```

## Key steps

1. μ := R.measure⌞W is finite on compact sets and μ(S) = ∫_{S∩M′} θ dHⁿ with M′ = M ∩ W; θ ≥ 1 on M gives ν := Hⁿ⌞M′ ≤ μ.
2. Level sets A_k = M′ ∩ θ⁻¹(ℕ ∖ {k}): sibling upper_density_zero with λ = μ gives μ(A_k ∩ B_ρ(x)) = o(ρⁿ) for Hⁿ-a.e. x ∉ A_k, for all k at once.
3. Field orients, local finiteness in a closed ball inside W, and the siblings unweighted_density_one and closed_to_open_ball_density give ν(B_ρ(x))/(ω_nρⁿ) → 1 at Hⁿ-a.e. x ∈ M′.
4. With k = θ(x) and T = θ⁻¹(k): μ(B) = k·Hⁿ(B ∩ M′ ∩ T) + μ(A_k ∩ B), whence μ(B) ≤ kν(B) + μ(A_k ∩ B) and kν(B) ≤ μ(B) + kμ(A_k ∩ B).
5. Divide by ω_nρⁿ and squeeze: R.measure(B_ρ(x) ∩ W)/(ω_nρⁿ) = μ(B_ρ(x))/(ω_nρⁿ) → k = θ(x).

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; git diff --quiet b4d606d 2d804b9 -- GMT/ lakefile.toml lake-manifest.json lean-toolchain (exit 0)`
- `sha256sum GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean <snapshot>/project/GMT/Ch07/Contract.lean <snapshot>/project/GMT/Ch07/Submission.lean`
- `rg -n 'structure IMRep|def IMRep.measure|def unitBallVolume|orients :' <snapshot>/project/GMT/Ch07/Contract.lean`
- `rg -n 'theorem exists_disjoint_subfamily_covering_enlargement|theorem hausdorffMeasure_le_liminf_tsum|exists_isClosed_sdiff_lt|of_pseudoMetrizableSpace_of_isFiniteMeasure|addHaarScalarFactor_volume_hausdorffMeasure_ne_zero|theorem lintegral_inter_add_sdiff|theorem measure_inter_add_sdiff|theorem setLIntegral_mono|protected theorem Tendsto.sub|protected theorem add_div|theorem div_le_div_right|theorem withDensity_apply|theorem ae_restrict_iff' <snapshot>/mathlib/Mathlib --glob '*.lean'`
- `rg -n 'euclideanHausdorffMeasure_def|notation.*μHE' <snapshot>/mathlib/Mathlib --glob '*.lean'`
- `rg -n -F 'dimred_tr_ida_' <snapshot>/project <snapshot>/mathlib --glob '*.lean' (exit 1, no match)`
- `python3 scans of dag.json: status, candidate_commit, updated_at and lean_statement of the selected node and of the owners of idtp_dema_upper_density_zero, rsd_tendsto_closedBall_density_of_approxTangent, rsd_tendsto_ball_density_of_closedBall and dimred_tr_ida_density_on_carrier; parents and depends_on users of the three reused nodes; accepted statements of the form x ∉ A → … (𝓝 0); cross-branch child edges`
- `cat isolated-comparator-result.json, lean-audit-v1.json, accepted-candidate.json and parent-child-handoff.json of the three reused nodes; comparison of their handoff natural proofs, statements and key steps with the children here`
- `git show {ee6fe01,dbef2c1,c3ca64f}:GMT/Ch07/Submission.lean; difflib extraction of the single block each adds to Contract.lean (/tmp/idae2/scripts/extract_blocks.py)`
- `cat cluster-state/logs/gmt-ch07/322e06219c1847d6b763362645586939.log (worker of issue #7930: attempt 1, name-check failure, attempt 2)`
- `gh api repos/humanfia/math-lean-flow/contents/_recursive_lean/{runtime,store,prompts,models,lean_contract,decomposition_scope}.py?ref=feature/humanize-api-update-claude; read _existing_lean_name_problem, _accepted_checkpoint, _decompose, _solve_children, Store.update/refresh/ensure, _install_parent_supplied_child_handoff, _dependency_problem, _reference_use_problem, validate_lean_statement`
- `python3 /tmp/idae2/scripts/make_lean.py; lake env lean /tmp/idae2/lean/Types3.lean; lake env lean /tmp/idae2/lean/CarrierOnly3.lean; lake env lean /tmp/idae2/lean/Full3.lean (each with #print axioms)`
- `python3 /tmp/idae2/scripts/graph_check.py dag.json decomposition.json (replica of the key/name patterns, _dependency_problem, _existing_lean_name_problem and node bounds)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1-imrep-density-ae-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1-imrep-density-ae-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-5625b30197/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-5625b30197/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1-unweighted-density-one-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1-unweighted-density-one-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1-closed-to-open-b-2625a8c412/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1-closed-to-open-b-2625a8c412/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/cluster-state/logs/gmt-ch07/322e06219c1847d6b763362645586939.log`
- `/tmp/idae2/lean/Types3.lean`
- `/tmp/idae2/lean/CarrierOnly3.lean`
- `/tmp/idae2/lean/Full3.lean`
- `/tmp/idae2/scripts/graph_check.py`

Pins match. The snapshot manifest records project b4d606d and mathlib 25730c7c, equal to the workspace HEAD and to .lake/packages/mathlib; simongmt is 2b36630 as pinned in lakefile.toml. The snapshot Contract.lean and Submission.lean and the workspace ones are byte-identical (sha256 e4148e7f…), and the proof base 2d804b9 changes nothing under GMT/.

Library facts the children use exist in the snapshot:
- Vitali.exists_disjoint_subfamily_covering_enlargement (Covering/Vitali.lean:59) and hausdorffMeasure_le_liminf_tsum (Measure/Hausdorff.lean:555).
- MeasurableSet.exists_isClosed_sdiff_lt (Measure/Regular.lean:1036) and the WeaklyRegular instance of_pseudoMetrizableSpace_of_isFiniteMeasure (Regular.lean:1072).
- euclideanHausdorffMeasure_def and addHaarScalarFactor_volume_hausdorffMeasure_ne_zero (Geometry/Euclidean/Volume/Measure.lean:74, 96).
- lintegral_inter_add_sdiff (Lebesgue/Basic.lean:637), measure_inter_add_sdiff (Measure/Basic.lean:83), setLIntegral_mono' (Lebesgue/Basic.lean:254), withDensity_apply (WithDensity.lean:44) and ae_restrict_iff' (Restrict.lean:629).
- ENNReal.Tendsto.sub (Topology/Instances/ENNReal/Lemmas.lean:309), ENNReal.add_div and ENNReal.div_le_div_right.
The contract defines IMRep with fields measurableSet_carrier, measurable_mult, mult_pos and orients, and defines IMRep.measure = (μHE[n]⌞carrier).withDensity mult and unitBallVolume n = volume(ball 0 1) (Contract.lean:61–143), as the children use them.

Reuse is valid. The three reused nodes are accepted, with candidate commits ee6fe01, dbef2c1 and c3ca64f, isolated comparators passed and comparator_passed audits. Their dag.json types equal the lean_statements here and the declarations in their candidates byte for byte. idtp_dema_upper_density_zero has been accepted since 12:53:48Z. Attempt 1 rejected it only because its worker had loaded the DAG before then, as the worker log and the runtime's in-memory name check show; the runtime's accepted-checkpoint condition now holds. dimred_tr_ida_density_on_carrier is unused in dag.json and in the snapshot.

Lean checks of this attempt all exit 0. The four child types elaborate, and the assembly proves the frozen selected type from them. The carrier proof compiles from its three siblings. Together with the three accepted proofs, all five declarations compile without sorry; #print axioms gives propext, Classical.choice and Quot.sound. The replica graph and name check passes against the live 2416-node DAG.
