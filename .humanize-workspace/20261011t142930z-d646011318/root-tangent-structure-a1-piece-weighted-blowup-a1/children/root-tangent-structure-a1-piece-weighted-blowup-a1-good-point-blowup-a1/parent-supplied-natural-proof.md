# Parent-supplied natural-language proof

- Parent DAG node: `root.tangent_structure-a1.piece_weighted_blowup-a1`
- Child DAG node: `root.tangent_structure-a1.piece_weighted_blowup-a1.good_point_blowup-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 7 of the parent proof (the four-term comparison at a good point; Simon Ch. 3, proof of Theorem 1.6 '⇒' together with Remark 1.8(1)). The good-point properties used there, namely (a'), (b'), the bound (3b), the limit (3a) of the sibling ts_piece_density_blowup and the continuity of θ on the Lusin piece, are here the hypotheses (H2), (H3), (H1), (H4) and ContinuousWithinAt θ K x. No errata apply.

Notation. E := Ambient n ℓ, Hⁿ := μHE[n], M := a.M, θ := a.θ, μ := (mk a).weight, B_r(x) := closed ball, Kᶜ := E ∖ K, μ.real(S) := μ(S).toReal. All integrals are Hⁿ-integrals unless μ is indicated. Uses the sibling ts_pwb_pair_weight_integral (applied to a): (W1) μ(K') < ∞ for every compact K' ⊆ E; (W2) ∫ h dμ = ∫_M θh dHⁿ for every function h: E → ℝ.

1. Constants of f. f is continuous with compact support, so there is m ≥ 0 with |f(z)| ≤ m for every z. The topological support of f is compact, hence bounded: there is C₀ with |z| ≤ C₀ for z ∈ tsupport f. Put R := max(C₀, 1) > 0; then f(z) = 0 whenever |z| > R (such z lies outside tsupport f).

2. Rescaled functions. For t > 0 put g_t(y) := f(t⁻¹(y − x)) and B_t := B_{Rt}(x). Then g_t is continuous, |g_t| ≤ m, and g_t(y) = 0 for every y ∉ B_t: if |y − x| > Rt then |t⁻¹(y − x)| = t⁻¹|y − x| > R.

3. Integrability (t > 0). (a) g_t is Hⁿ-integrable on N, since it is Borel, bounded by m, and Hⁿ(N) < ∞; hence it is also integrable on the subsets K and N ∖ K. (b) θ·g_t is Hⁿ-integrable on M: θ is Hⁿ-integrable on M ∩ B_t because B_t is compact (admissibility of a), and g_t is a bounded measurable function, so θ·g_t is integrable on M ∩ B_t; it vanishes on M ∖ B_t by step 2, and M is Hⁿ-null-measurable, so θ·g_t is integrable on M (IntegrableOn.of_ae_sdiff_eq_zero). Consequently θ·g_t is integrable on K ⊆ M, and so is (θ − θ(x))·g_t = θg_t − θ(x)g_t.

4. Decomposition (t > 0).
(a) ∫ g_t dμ = ∫_M θg_t, by (W2) with h = g_t.
(b) ∫_M θg_t = ∫_{M∩K} θg_t + ∫_{M∖K} θg_t, because K is Borel and θg_t is integrable on M (step 3(b)); and M ∩ K = K since K ⊆ M.
(c) ∫_{M∖K} θg_t = ∫_{Kᶜ} g_t dμ. Indeed, by (W2) with h = 1_{Kᶜ}·g_t: ∫_{Kᶜ} g_t dμ = ∫ 1_{Kᶜ}g_t dμ = ∫_M θ·1_{Kᶜ}g_t = ∫_M 1_{Kᶜ}·(θg_t) = ∫_{M∩Kᶜ} θg_t (Kᶜ is Borel), and M ∩ Kᶜ = M ∖ K.
(d) ∫_K θg_t = θ(x)∫_K g_t + ∫_K (θ − θ(x))g_t, by linearity (both integrands integrable on K by step 3).
(e) ∫_K g_t = ∫_N g_t − ∫_{N∖K} g_t, because K ⊆ N, K is Borel and g_t is integrable on N.
Combining (a)–(e) and multiplying by (tⁿ)⁻¹:
(tⁿ)⁻¹∫ g_t dμ = θ(x)·T₁(t) − θ(x)·T₂(t) + T₃(t) + T₄(t), where
T₁(t) := (tⁿ)⁻¹∫_N g_t, T₂(t) := (tⁿ)⁻¹∫_{N∖K} g_t, T₃(t) := (tⁿ)⁻¹∫_K (θ − θ(x))g_t, T₄(t) := (tⁿ)⁻¹∫_{Kᶜ} g_t dμ.

5. Rescaling the hypotheses. Since R > 0, the map t ↦ Rt sends (0, ∞) into (0, ∞) and tends to 0 as t → 0, so it maps the filter of right-neighbourhoods of 0 into itself. Hence (H2) and (H3) give Q_μ(Rt) → 0 and Q_N(Rt) → 0 as t ↓ 0, where Q_μ(r) := μ.real(Kᶜ ∩ B_r(x))/rⁿ and Q_N(r) := (Hⁿ⌞N).real(Kᶜ ∩ B_r(x))/rⁿ. Note that (tⁿ)⁻¹ = Rⁿ/(Rt)ⁿ for t > 0.

6. T₁(t) → L as t ↓ 0: T₁(t) is exactly the expression in (H4).

7. T₂(t) → 0. Fix t > 0. Since g_t = 0 on (N ∖ K) ∖ B_t, ∫_{N∖K} g_t = ∫_{(N∖K)∩B_t} g_t, and |∫_{(N∖K)∩B_t} g_t| ≤ m·Hⁿ.real((N ∖ K) ∩ B_t) (the set has finite measure, being contained in N). Since (N ∖ K) ∩ B_t = (Kᶜ ∩ B_t) ∩ N and Kᶜ ∩ B_t is Borel, Hⁿ((N ∖ K) ∩ B_t) = (Hⁿ⌞N)(Kᶜ ∩ B_t). Hence |T₂(t)| ≤ (tⁿ)⁻¹·m·(Hⁿ⌞N).real(Kᶜ ∩ B_{Rt}(x)) = mRⁿ·Q_N(Rt), which tends to 0 by step 5. So T₂(t) → 0.

8. T₄(t) → 0. Fix t > 0. Since g_t = 0 on Kᶜ ∖ B_t, ∫_{Kᶜ} g_t dμ = ∫_{Kᶜ∩B_t} g_t dμ, and μ(Kᶜ ∩ B_t) ≤ μ(B_t) < ∞ by (W1) (B_t is compact). Hence |T₄(t)| ≤ (tⁿ)⁻¹·m·μ.real(Kᶜ ∩ B_{Rt}(x)) = mRⁿ·Q_μ(Rt), which tends to 0 by step 5.

9. T₃(t) → 0. Let ε > 0 and put c := mRⁿ·max(Γ, 0) + 1 > 0. By continuity of θ restricted to K at x there is δ > 0 such that |θ(y) − θ(x)| < ε/c for every y ∈ K with |y − x| < δ. Let 0 < t < δ/R, so that Rt < δ. Since g_t = 0 off B_t, ∫_K (θ − θ(x))g_t = ∫_{K∩B_t} (θ − θ(x))g_t, and for y ∈ K ∩ B_t we have |y − x| ≤ Rt < δ, hence |(θ(y) − θ(x))g_t(y)| ≤ (ε/c)·m. Moreover, as K ⊆ N, (H1) with ρ := Rt > 0 gives Hⁿ(K ∩ B_t) ≤ Hⁿ(N ∩ B_t) ≤ ofReal(Γ(Rt)ⁿ) < ∞, so Hⁿ.real(K ∩ B_t) ≤ max(Γ(Rt)ⁿ, 0) ≤ max(Γ, 0)·(Rt)ⁿ. Therefore |T₃(t)| ≤ (tⁿ)⁻¹·(ε/c)·m·max(Γ, 0)·(Rt)ⁿ = (ε/c)·mRⁿmax(Γ, 0) = ε(c − 1)/c < ε for all t ∈ (0, δ/R). As ε > 0 was arbitrary, T₃(t) → 0.

10. Conclusion. By steps 6–9, θ(x)T₁(t) − θ(x)T₂(t) + T₃(t) + T₄(t) → θ(x)L − θ(x)·0 + 0 + 0 = θ(x)L as t ↓ 0. By step 4 this expression equals (tⁿ)⁻¹∫ f(t⁻¹(y − x)) dμ(y) for every t > 0, i.e. on a set belonging to the filter of right-neighbourhoods of 0. Hence (tⁿ)⁻¹∫ f(t⁻¹(y − x)) dμ(y) → θ(x)·L as t ↓ 0. (The hypothesis x ∈ K is not needed for this argument; it is kept because it holds in the application, where ContinuousWithinAt θ K x is obtained from continuity of θ on K.) ∎

Implementation note (not part of the mathematical argument): during the decomposition the following Lean proof of exactly the frozen statement was compiled without errors, placed in the frozen contract scope (after `open MeasureTheory Metric Set Filter Topology`, `open scoped ENNReal ContDiff CompactlySupported`, inside `namespace GMT.Ch04`, `noncomputable section`, `open RectifiableVarifold`, and `namespace Submission`) of a file importing `GMT.Ch04.Submission`, `Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace`, `Poincare.SimonGMT.Chapter01.DensityComparison`, `Poincare.SimonGMT.Chapter01.Lusin` and `Poincare.SimonGMT.Chapter02.AreaLiteral` (pinned Lean v4.35.0-rc3, Mathlib 25730c7c, SimonGMT 2b36630); `#print axioms` reports only propext, Classical.choice and Quot.sound. The proof calls the sibling `ts_pwb_pair_weight_integral`. It follows the numbered argument above and may be reused verbatim.

```lean
theorem ts_pwb_blowup_at_good_point : ∀ (n ℓ : ℕ) (a : RectifiablePair n ℓ) (N K : Set (Ambient n ℓ)) (x : Ambient n ℓ) (f : C_c(Ambient n ℓ, ℝ)) (Γ L : ℝ), MeasurableSet N → (μHE[n] : Measure (Ambient n ℓ)) N ≠ ⊤ → IsCompact K → K ⊆ a.M ∩ N → x ∈ K → ContinuousWithinAt a.θ K x → (∀ ρ : ℝ, 0 < ρ → (μHE[n] : Measure (Ambient n ℓ)) (N ∩ closedBall x ρ) ≤ ENNReal.ofReal (Γ * ρ ^ n)) → Tendsto (fun r : ℝ ↦ (mk a).weight.real (Kᶜ ∩ closedBall x r) / r ^ n) (𝓝[>] 0) (𝓝 0) → Tendsto (fun r : ℝ ↦ ((μHE[n] : Measure (Ambient n ℓ)).restrict N).real (Kᶜ ∩ closedBall x r) / r ^ n) (𝓝[>] 0) (𝓝 0) → Tendsto (fun t : ℝ ↦ (t ^ n)⁻¹ * ∫ y in N, f (t⁻¹ • (y - x)) ∂μHE[n]) (𝓝[>] 0) (𝓝 L) → Tendsto (fun t : ℝ ↦ (t ^ n)⁻¹ * ∫ y, f (t⁻¹ • (y - x)) ∂(mk a).weight) (𝓝[>] 0) (𝓝 (a.θ x * L)) := by
  intro n ℓ a N K x f Γ L hNm hNfin hKc hKMN hxK hθc hΓ hA hB hI1
  obtain ⟨hfin, hint⟩ := ts_pwb_pair_weight_integral n ℓ a
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hKM : K ⊆ a.M := fun y hy ↦ (hKMN hy).1
  have hKN : K ⊆ N := fun y hy ↦ (hKMN hy).2
  have hMm := a.isRectifiablePair.measurable
  obtain ⟨m, hm⟩ : ∃ m, ∀ z, ‖f z‖ ≤ m :=
    f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  have hm0 : 0 ≤ m := (norm_nonneg _).trans (hm 0)
  obtain ⟨R, hR, hRs⟩ : ∃ R : ℝ, 0 < R ∧ ∀ z, R < ‖z‖ → f z = 0 := by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 f.hasCompactSupport.isCompact.isBounded
    refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun z hz ↦ ?_⟩
    apply image_eq_zero_of_notMem_tsupport
    intro hzs
    exact absurd (hC z hzs) (not_le.2 (lt_of_le_of_lt (le_max_left _ _) hz))
  set g : ℝ → Ambient n ℓ → ℝ := fun t y ↦ f (t⁻¹ • (y - x)) with hg
  have hgc : ∀ t, Continuous (g t) := fun t ↦
    f.continuous.comp (by fun_prop)
  have hgb : ∀ t y, ‖g t y‖ ≤ m := fun t y ↦ hm _
  have hgs : ∀ t, 0 < t → ∀ y, y ∉ closedBall x (R * t) → g t y = 0 := by
    intro t ht y hy
    apply hRs
    rw [mem_closedBall, dist_eq_norm, not_le] at hy
    rw [norm_smul, norm_inv, Real.norm_of_nonneg ht.le, lt_inv_mul_iff₀ ht]
    linarith [mul_comm R t]
  -- integrability
  have hgN : ∀ t, IntegrableOn (g t) N μHE[n] := fun t ↦
    IntegrableOn.of_bound (lt_top_iff_ne_top.2 hNfin) (hgc t).aestronglyMeasurable m
      (Eventually.of_forall (hgb t))
  have hθg : ∀ t, 0 < t → IntegrableOn (fun y ↦ a.θ y * g t y) a.M μHE[n] := by
    intro t ht
    have h1 : IntegrableOn a.θ (a.M ∩ closedBall x (R * t)) μHE[n] :=
      a.isRectifiablePair.locallyIntegrable _ (isCompact_closedBall _ _)
    have h2 : IntegrableOn (fun y ↦ a.θ y * g t y) (a.M ∩ closedBall x (R * t)) μHE[n] :=
      Integrable.mul_bdd h1 (hgc t).aestronglyMeasurable (Eventually.of_forall (hgb t))
    refine h2.of_ae_sdiff_eq_zero hMm (Eventually.of_forall fun y hy ↦ ?_)
    rw [hgs t ht y (fun hyB ↦ hy.2 ⟨hy.1, hyB⟩), mul_zero]
  -- decomposition
  have hdec : ∀ t, 0 < t → (t ^ n)⁻¹ * ∫ y, g t y ∂(mk a).weight =
      a.θ x * ((t ^ n)⁻¹ * ∫ y in N, g t y ∂μHE[n]) -
        a.θ x * ((t ^ n)⁻¹ * ∫ y in N \ K, g t y ∂μHE[n]) +
        (t ^ n)⁻¹ * ∫ y in K, (a.θ y - a.θ x) * g t y ∂μHE[n] +
        (t ^ n)⁻¹ * ∫ y in Kᶜ, g t y ∂(mk a).weight := by
    intro t ht
    have e1 : ∫ y, g t y ∂(mk a).weight = ∫ y in a.M, a.θ y * g t y ∂μHE[n] := hint (g t)
    have e2 : ∫ y in a.M, a.θ y * g t y ∂μHE[n] =
        ∫ y in K, a.θ y * g t y ∂μHE[n] + ∫ y in a.M \ K, a.θ y * g t y ∂μHE[n] := by
      rw [← integral_inter_add_sdiff hKm (hθg t ht), inter_eq_right.2 hKM]
    have e3 : ∫ y in a.M \ K, a.θ y * g t y ∂μHE[n] = ∫ y in Kᶜ, g t y ∂(mk a).weight := by
      rw [← integral_indicator hKm.compl, hint, sdiff_eq, ← setIntegral_indicator hKm.compl]
      congr 1
      ext y
      by_cases hy : y ∈ Kᶜ <;> simp [indicator, hy]
    have hgK : IntegrableOn (g t) K μHE[n] := (hgN t).mono_set hKN
    have hθgK : IntegrableOn (fun y ↦ a.θ y * g t y) K μHE[n] := (hθg t ht).mono_set hKM
    have e4 : ∫ y in K, a.θ y * g t y ∂μHE[n] =
        a.θ x * ∫ y in K, g t y ∂μHE[n] + ∫ y in K, (a.θ y - a.θ x) * g t y ∂μHE[n] := by
      have : (fun y ↦ (a.θ y - a.θ x) * g t y) = fun y ↦ a.θ y * g t y - a.θ x * g t y := by
        ext y; ring
      rw [this, integral_sub hθgK (hgK.const_mul _), integral_const_mul]
      ring
    have e5 : ∫ y in K, g t y ∂μHE[n] = ∫ y in N, g t y ∂μHE[n] - ∫ y in N \ K, g t y ∂μHE[n] := by
      rw [← integral_inter_add_sdiff hKm (hgN t), inter_eq_right.2 hKN]
      ring
    rw [e1, e2, e3, e4, e5]
    ring
  have := hfin
  have hRt : Tendsto (fun t : ℝ ↦ R * t) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun t : ℝ ↦ R * t) (𝓝 0) (𝓝 (R * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_pos hR ht
  have hA' := hA.comp hRt
  have hB' := hB.comp hRt
  -- term T2
  have hT2 : Tendsto (fun t ↦ (t ^ n)⁻¹ * ∫ y in N \ K, g t y ∂μHE[n]) (𝓝[>] 0) (𝓝 0) := by
    have hlim : Tendsto (fun t ↦ m * R ^ n * (((μHE[n] : Measure (Ambient n ℓ)).restrict N).real
        (Kᶜ ∩ closedBall x (R * t)) / (R * t) ^ n)) (𝓝[>] 0) (𝓝 0) := by
      simpa using hB'.const_mul (m * R ^ n)
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : (0 : ℝ) < t := ht
    have hsplit : ∫ y in N \ K, g t y ∂μHE[n] =
        ∫ y in (N \ K) ∩ closedBall x (R * t), g t y ∂μHE[n] :=
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hNm.diff hKm) inter_subset_left
        (fun y hy ↦ hgs t ht' y (fun hyB ↦ hy.2 ⟨hy.1, hyB⟩))
    have hmeas : (μHE[n] : Measure (Ambient n ℓ)) ((N \ K) ∩ closedBall x (R * t)) < ⊤ :=
      (measure_mono (inter_subset_left.trans sdiff_subset)).trans_lt (lt_top_iff_ne_top.2 hNfin)
    have hbound := norm_setIntegral_le_of_norm_le_const hmeas (fun y _ ↦ hgb t y)
    have hreal : (μHE[n] : Measure (Ambient n ℓ)).real ((N \ K) ∩ closedBall x (R * t)) =
        ((μHE[n] : Measure (Ambient n ℓ)).restrict N).real (Kᶜ ∩ closedBall x (R * t)) := by
      rw [Measure.real, Measure.real,
        Measure.restrict_apply (hKm.compl.inter measurableSet_closedBall)]
      congr 2
      ext y
      simp only [mem_inter_iff, Set.mem_sdiff, mem_compl_iff]
      tauto
    rw [norm_mul, hsplit, norm_inv, norm_pow, Real.norm_of_nonneg ht'.le]
    calc (t ^ n)⁻¹ * ‖∫ y in (N \ K) ∩ closedBall x (R * t), g t y ∂μHE[n]‖
        ≤ (t ^ n)⁻¹ * (m * (μHE[n] : Measure (Ambient n ℓ)).real
            ((N \ K) ∩ closedBall x (R * t))) := by gcongr
      _ = m * R ^ n * (((μHE[n] : Measure (Ambient n ℓ)).restrict N).real
            (Kᶜ ∩ closedBall x (R * t)) / (R * t) ^ n) := by
        rw [hreal, mul_pow]
        field_simp
  -- term T4
  have hT4 : Tendsto (fun t ↦ (t ^ n)⁻¹ * ∫ y in Kᶜ, g t y ∂(mk a).weight) (𝓝[>] 0) (𝓝 0) := by
    have hlim : Tendsto (fun t ↦ m * R ^ n * ((mk a).weight.real
        (Kᶜ ∩ closedBall x (R * t)) / (R * t) ^ n)) (𝓝[>] 0) (𝓝 0) := by
      simpa using hA'.const_mul (m * R ^ n)
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : (0 : ℝ) < t := ht
    have hsplit : ∫ y in Kᶜ, g t y ∂(mk a).weight =
        ∫ y in Kᶜ ∩ closedBall x (R * t), g t y ∂(mk a).weight :=
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hKm.compl inter_subset_left
        (fun y hy ↦ hgs t ht' y (fun hyB ↦ hy.2 ⟨hy.1, hyB⟩))
    have hmeas : (mk a).weight (Kᶜ ∩ closedBall x (R * t)) < ⊤ :=
      (measure_mono inter_subset_right).trans_lt (isCompact_closedBall _ _).measure_lt_top
    rw [norm_mul, hsplit, norm_inv, norm_pow, Real.norm_of_nonneg ht'.le]
    calc (t ^ n)⁻¹ * ‖∫ y in Kᶜ ∩ closedBall x (R * t), g t y ∂(mk a).weight‖
        ≤ (t ^ n)⁻¹ * (m * (mk a).weight.real (Kᶜ ∩ closedBall x (R * t))) := by
          gcongr
          exact norm_setIntegral_le_of_norm_le_const hmeas (fun y _ ↦ hgb t y)
      _ = m * R ^ n * ((mk a).weight.real (Kᶜ ∩ closedBall x (R * t)) / (R * t) ^ n) := by
        rw [mul_pow]
        field_simp
  -- term T3
  have hT3 : Tendsto (fun t ↦ (t ^ n)⁻¹ * ∫ y in K, (a.θ y - a.θ x) * g t y ∂μHE[n])
      (𝓝[>] 0) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    set c := m * max Γ 0 * R ^ n + 1 with hc
    have hc0 : 0 < c := by positivity
    obtain ⟨δ, hδ, hδθ⟩ := Metric.continuousWithinAt_iff.1 hθc (ε / c) (div_pos hε hc0)
    filter_upwards [Ioo_mem_nhdsGT (div_pos hδ hR)] with t ht
    obtain ⟨ht0, htδ⟩ := ht
    have hRtδ : R * t < δ := by
      rw [lt_div_iff₀ hR] at htδ
      linarith [mul_comm R t]
    have hsplit : ∫ y in K, (a.θ y - a.θ x) * g t y ∂μHE[n] =
        ∫ y in K ∩ closedBall x (R * t), (a.θ y - a.θ x) * g t y ∂μHE[n] :=
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hKm inter_subset_left
        (fun y hy ↦ by rw [hgs t ht0 y (fun hyB ↦ hy.2 ⟨hy.1, hyB⟩), mul_zero])
    have hmeasN : (μHE[n] : Measure (Ambient n ℓ)) (N ∩ closedBall x (R * t)) < ⊤ :=
      (measure_mono inter_subset_left).trans_lt (lt_top_iff_ne_top.2 hNfin)
    have hmeasK : (μHE[n] : Measure (Ambient n ℓ)) (K ∩ closedBall x (R * t)) < ⊤ :=
      (measure_mono (inter_subset_inter_left _ hKN)).trans_lt hmeasN
    have hpt : ∀ y ∈ K ∩ closedBall x (R * t), ‖(a.θ y - a.θ x) * g t y‖ ≤ ε / c * m := by
      intro y hy
      rw [norm_mul]
      have h1 : dist y x < δ := lt_of_le_of_lt (mem_closedBall.1 hy.2) hRtδ
      have h2 := hδθ hy.1 h1
      rw [Real.dist_eq] at h2
      exact mul_le_mul (le_of_lt (by simpa [Real.norm_eq_abs] using h2)) (hgb t y)
        (norm_nonneg _) (div_pos hε hc0).le
    have hbound := norm_setIntegral_le_of_norm_le_const hmeasK hpt
    have hKreal : (μHE[n] : Measure (Ambient n ℓ)).real (K ∩ closedBall x (R * t)) ≤
        max Γ 0 * (R * t) ^ n := by
      calc (μHE[n] : Measure (Ambient n ℓ)).real (K ∩ closedBall x (R * t))
          ≤ (μHE[n] : Measure (Ambient n ℓ)).real (N ∩ closedBall x (R * t)) :=
            measureReal_mono (inter_subset_inter_left _ hKN) hmeasN.ne
        _ ≤ (ENNReal.ofReal (Γ * (R * t) ^ n)).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top (hΓ _ (mul_pos hR ht0))
        _ = max (Γ * (R * t) ^ n) 0 := ENNReal.toReal_ofReal'
        _ ≤ max Γ 0 * (R * t) ^ n := by
          have hp : 0 ≤ (R * t) ^ n := by positivity
          rcases le_total Γ 0 with h | h
          · rw [max_eq_right h, max_eq_right (mul_nonpos_of_nonpos_of_nonneg h hp), zero_mul]
          · rw [max_eq_left h, max_eq_left (mul_nonneg h hp)]
    rw [dist_zero_right, norm_mul, hsplit, norm_inv, norm_pow, Real.norm_of_nonneg ht0.le]
    have hεc : 0 ≤ ε / c * m := mul_nonneg (div_pos hε hc0).le hm0
    calc (t ^ n)⁻¹ * ‖∫ y in K ∩ closedBall x (R * t), (a.θ y - a.θ x) * g t y ∂μHE[n]‖
        ≤ (t ^ n)⁻¹ * (ε / c * m * (μHE[n] : Measure (Ambient n ℓ)).real
            (K ∩ closedBall x (R * t))) := by gcongr
      _ ≤ (t ^ n)⁻¹ * (ε / c * m * (max Γ 0 * (R * t) ^ n)) := by gcongr
      _ = ε / c * (m * max Γ 0 * R ^ n) := by
        rw [mul_pow]
        field_simp
      _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ hc0, hc]
        nlinarith
  have hsum := (((hI1.const_mul (a.θ x)).sub (hT2.const_mul (a.θ x))).add hT3).add hT4
  rw [mul_zero, sub_zero, add_zero, add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (hdec t ht).symm
```

## Key steps

1. Choose m ≥ sup|f| and R > 0 with f = 0 outside B_R(0); g_t(y) := f(t⁻¹(y − x)) is bounded by m and vanishes outside B_{Rt}(x)
2. Integrability: g_t on N (Hⁿ(N) < ∞) and θg_t on M (θ integrable on M ∩ B_{Rt}(x), g_t = 0 elsewhere)
3. Using the sibling formula ∫ h dμ = ∫_M θh dHⁿ twice: (tⁿ)⁻¹∫ g_t dμ = θ(x)T₁ − θ(x)T₂ + T₃ + T₄
4. T₁ → L by (H4); |T₂| ≤ mRⁿ·Q_N(Rt) → 0 by (H3); |T₄| ≤ mRⁿ·Q_μ(Rt) → 0 by (H2) and finiteness of μ on balls
5. |T₃| ≤ (ε/c)·mRⁿmax(Γ,0) < ε for t < δ/R, by continuity of θ|K at x and the bound (H1)
6. Sum the limits: the blow-up tends to θ(x)L

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json`
- `sha256sum GMT/Ch04/Contract.lean GMT/Ch04/Submission.lean <snapshot>/project/GMT/Ch04/Contract.lean`
- `git -C .lake/packages/simongmt rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD`
- `python3: list dag.json nodes (id, status, lean_name, lean_statement) for name-collision and reuse checks`
- `grep -rn 'theorem ae_dimensionalUpperDensity_eq_zero_outside|theorem measure_toOuterMeasure_isBorelRegular|theorem simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure|theorem exists_isClosed_continuousOn_of_measurable|theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn|def dimensionalUpperDensity|def realUnitBallVolume' .lake/packages/simongmt/Poincare/`
- `grep -rn 'def IsOpenSigmaFinite|def IsCaratheodoryMeasurable|realUnitBallVolume_pos|realUnitBallVolume_ne_top' .lake/packages/simongmt/Poincare/SimonGMT`
- `rg -n 'theorem ae_tendsto_measure_inter_div|theorem integral_withDensity_eq_integral_toReal_smul₀|theorem ae_restrict_mem₀|exists_isClosed_sdiff_lt|euclideanHausdorffMeasure_eq_volume' <snapshot>/mathlib/Mathlib`
- `rg -n 'measure_eq_zero_iff_ae_notMem|ae_all_iff|ae_restrict_of_ae|isFiniteMeasure_restrict|aestronglyMeasurable_iUnion_iff|of_pseudoMetrizableSpace_of_isFiniteMeasure|exists_measurable_subset_ae_eq|tendsto_of_liminf_eq_limsup|ofReal_le_enorm' <snapshot>/mathlib/Mathlib`
- `rg -n 'integral_inter_add_sdiff|setIntegral_eq_of_subset_of_forall_sdiff_eq_zero|IntegrableOn.of_ae_sdiff_eq_zero|Integrable.mul_bdd|IntegrableOn.of_bound|norm_setIntegral_le_of_norm_le_const|setIntegral_indicator|lt_inv_mul_iff₀|bounded_above_of_compact_support' <snapshot>/mathlib/Mathlib`
- `lake env lean GMT/Ch04/Submission.lean -o /tmp/pwb-decomp/olean/GMT/Ch04/Submission.olean`
- `python3 /tmp/pwb-decomp/scripts/gen.py (verifier gmt-compare.child_modules + lean_contract.validate_lean_statement); lean /tmp/pwb-decomp/gen/Challenge_*.lean`
- `lean /tmp/pwb-decomp/inst/Plain.lean and /tmp/pwb-decomp/inst/WithImports.lean (pp.all) then diff`
- `lean /tmp/pwb-decomp/asm/Assembly.lean (parent from sorry'd children and sibling)`
- `lean /tmp/pwb-decomp/probe/Full.lean and /tmp/pwb-decomp/out/Verify.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/project/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-piece-weighted-blowup-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-piece-weighted-blowup-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-piece-weighted-blowup-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-piece-density-blowup-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLiteral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Topology/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Normed/Group/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Algebra/Order/GroupWithZero/Basic.lean`
- `/tmp/pwb-decomp/gen/Challenge_ts_pwb_pair_weight_integral.lean`
- `/tmp/pwb-decomp/gen/Challenge_ts_pwb_upper_density_vanish_ae.lean`
- `/tmp/pwb-decomp/gen/Challenge_ts_pwb_lusin_compact_cover.lean`
- `/tmp/pwb-decomp/gen/Challenge_ts_pwb_density_points_of_image_ae.lean`
- `/tmp/pwb-decomp/gen/Challenge_ts_pwb_blowup_at_good_point.lean`
- `/tmp/pwb-decomp/inst/Plain.lean`
- `/tmp/pwb-decomp/inst/WithImports.lean`
- `/tmp/pwb-decomp/asm/Assembly.lean`
- `/tmp/pwb-decomp/probe/Full.lean`
- `/tmp/pwb-decomp/out/Verify.lean`

Snapshot and pins:
- The snapshot contract, the workspace Contract.lean and the workspace Submission.lean are byte-identical (sha256 6e58e5dd…0f4770b).
- simongmt is at the pinned 2b3663083f3fe399b6296fb8eaee52169170e197 and mathlib at 25730c7c759d108ef87ab70af2342a196760f79d, as in the manifest.

Library results used by the children (each exists with the stated meaning; every child built on them prints only propext, Classical.choice, Quot.sound):
- SimonGMT (Chapter01/02): ae_dimensionalUpperDensity_eq_zero_outside (Simon 1.3.6), measure_toOuterMeasure_isBorelRegular, realUnitBallVolume_pos and realUnitBallVolume_ne_top, dimensionalDensityQuotient (closed balls), exists_isClosed_continuousOn_of_measurable (Lusin 1.17), euclideanHausdorffMeasure_image_le_of_lipschitzOn, simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure.
- Mathlib snapshot: Besicovitch.ae_tendsto_measure_inter_div, integral_withDensity_eq_integral_toReal_smul₀, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure, MeasurableSet.exists_isClosed_sdiff_lt, NullMeasurableSet.exists_measurable_subset_ae_eq, aestronglyMeasurable_iUnion_iff, ae_restrict_mem₀, tendsto_of_liminf_eq_limsup, integral_inter_add_sdiff, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero, IntegrableOn.of_ae_sdiff_eq_zero, norm_setIntegral_le_of_norm_le_const.
- The Mathlib snapshot has no Lusin theorem, so the SimonGMT one is used.
- No existing DAG declaration matches any child type. The accepted lusin_compact_exhaustion_of_measurable concerns volume on ℝⁿ.

Elaboration checks:
- All five child types elaborate in comparator-generated challenge files.
- They are unchanged (pp.all byte-identical) when the implementation imports are added.
- The parent's frozen type is proved from them plus the sibling (Assembly.lean).
- All five children are fully proved (Full.lean, Verify.lean).
