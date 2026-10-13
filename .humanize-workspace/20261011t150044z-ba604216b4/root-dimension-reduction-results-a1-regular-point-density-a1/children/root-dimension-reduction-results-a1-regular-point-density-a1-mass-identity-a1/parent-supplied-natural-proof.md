# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.regular_point_density-a1`
- Child DAG node: `root.dimension_reduction_results-a1.regular_point_density-a1.mass_identity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3 of the supplied parent proof ("M_{B_s(z)}(T) = m·H^n(M ∩ B_s(z))"), stated for a general open W and specialized by the parent to W = B_s(z). As in the parent, the upper bound uses the pointwise duality |ξ(x)(α)| ≤ |α|, and the lower bound tests T against smooth admissible forms that approximate the dual field β = sign(m₀)·L(ξ) on a compact set. The only change is in the lower bound. The smoothing lemma is applied directly on a compact K ⊆ M ∩ W chosen by inner regularity, with the open set W itself as the support region. So the auxiliary open set V' and the dominated-convergence step of the parent wording are not needed.
Notation. μ := μHE[n]. For α ∈ Λⁿ := Covector (Euclid P) n, |α| := covectorEuclideanNorm α. m := |m₀| = m₀.natAbs. a := μ(M ∩ W), a finite number by hypothesis. For a test form ω put f_ω(x) := ξ(x)(ω(x)). By definition, T.massOn W is the supremum of ofReal(T(ω)) over the admissible forms massAdmissibleOn U n W. These are the ω ∈ TestFormOn U n with tsupport ω ⊆ W and |ω(x)| ≤ 1 for all x.
1. (Duality; sibling orientation_dual.) By the sibling lemma Submission.dor_ims_unitOrientation_dual, fix a continuous linear map L : Λ_n → Λⁿ such that every ζ ∈ Λ_n and subspace Q with IsUnitOrientationOf ζ Q satisfy:
 - |ζ(α)| ≤ |α| for all α ∈ Λⁿ;
 - |L(ζ)| ≤ 1;
 - ζ(L(ζ)) = 1.
 By the hypothesis on ξ, these three facts hold with ζ = ξ(x) for every x ∈ M.
2. (Pointwise bound and integrability.) Let ω ∈ TestFormOn U n satisfy tsupport ω ⊆ W and |ω(x)| ≤ 1 for all x.
 - For x ∈ M ∩ W, step 1 gives |f_ω(x)| ≤ |ω(x)| ≤ 1.
 - For x ∈ M ∖ W, x ∉ tsupport ω, so ω(x) = 0 and f_ω(x) = ξ(x)(0) = 0.
 Hence |f_ω| ≤ 1_W on M.
 - f_ω is continuous on M: evaluation (ζ, α) ↦ ζ(α) is continuous, ξ is continuous on M, and ω is continuous because it is smooth. Since M is measurable, f_ω is a.e.-strongly measurable for μ⌞M (ContinuousOn.aestronglyMeasurable).
 - 1_W is μ⌞M-integrable, because W is open, hence measurable, and ∫_M 1_W dμ = μ(M ∩ W) = a < ∞.
 Therefore f_ω is μ⌞M-integrable (domination by 1_W), and ∫_M |f_ω| dμ ≤ ∫_M 1_W dμ = a.
3. (Upper bound M_W(T) ≤ m·a.) Let ω be admissible for W. Since tsupport ω ⊆ W, the hypothesis gives T(ω) = m₀ ∫_M f_ω dμ. By step 2,
 T(ω) ≤ |m₀|·|∫_M f_ω dμ| ≤ |m₀| ∫_M |f_ω| dμ ≤ |m₀|·a.
 As a < ∞, ofReal(|m₀|·a) = m·μ(M ∩ W), so ofReal(T(ω)) ≤ m·μ(M ∩ W). Taking the supremum over admissible ω gives T.massOn W ≤ m·μ(M ∩ W).
4. (Lower bound: trivial case and sign.) If m₀ = 0, the right side is 0 ≤ T.massOn W. Assume m₀ ≠ 0. Put s₀ := 1 if m₀ > 0 and s₀ := −1 if m₀ < 0, so that m₀·s₀ = |m₀|.
5. (The dual field.) Put β(x) := s₀·L(ξ(x)) ∈ Λⁿ.
 - β is continuous on M, since L is continuous linear and ξ is continuous on M.
 - For x ∈ M, |β(x)| = |L(ξ(x))| ≤ 1, using |−α| = |α| and step 1.
 - For x ∈ M, m₀·ξ(x)(β(x)) = m₀·s₀·ξ(x)(L(ξ(x))) = |m₀|.
6. (Choice of K and ω for a fixed η > 0.)
 (a) The restricted measure ν := μ⌞(M ∩ W) is a finite Borel measure on ℝ^P, since ν(ℝ^P) = a < ∞. Hence it is inner regular on measurable sets with respect to compact sets: finite measures on ℝ^P are Regular, hence InnerRegularCompactLTTop (MeasurableSet.exists_isCompact_sdiff_lt). Applying this to the measurable set M ∩ W gives a compact K ⊆ M ∩ W with μ((M ∩ W) ∖ K) = ν((M ∩ W) ∖ K) < η.
 (b) Apply the sibling lemma Submission.dor_ims_smooth_unit_approx to:
 - the compact set K and the open set W ⊇ K;
 - the field β, which is continuous on K ⊆ M with |β| ≤ 1 on K by step 5;
 - δ := η.
 It gives a smooth compactly supported form ω₀ with tsupport ω₀ ⊆ W, |ω₀(x)| ≤ 1 for all x, and |ω₀(x) − β(x)| ≤ η for x ∈ K.
 (c) Because W ⊆ U, ω₀ is an element ω of TestFormOn U n, and ω is admissible for W. Hence ofReal(T(ω)) ≤ T.massOn W.
7. (Estimate of T(ω).) Let g := m₀·f_ω. By step 2, g is μ⌞M-integrable and T(ω) = ∫_M g dμ. K ⊆ M is compact, hence measurable, so ∫_M g dμ = ∫_K g dμ + ∫_{M∖K} g dμ.
 (a) On K: for x ∈ K, g(x) = m₀ξ(x)(β(x)) + m₀ξ(x)(ω(x) − β(x)). The first term equals |m₀| by step 5. The second has absolute value at most |m₀|·|ω(x) − β(x)| ≤ |m₀|η by step 1. So g(x) ≥ |m₀|(1 − η). Since μ(K) ≤ a < ∞, ∫_K g dμ ≥ |m₀|(1 − η)·μ(K) (setIntegral_ge_of_const_le_real).
 (b) On M ∖ K: |g| ≤ |m₀|·1_W there by step 2. Hence |∫_{M∖K} g dμ| ≤ |m₀|·μ((M ∖ K) ∩ W) = |m₀|·μ((M ∩ W) ∖ K) ≤ |m₀|η.
 (c) Measures: μ(K) ≤ a because K ⊆ M ∩ W. Also a ≤ μ(K) + μ((M ∩ W) ∖ K) ≤ μ(K) + η, so μ(K) ≥ a − η.
 Combining (a)–(c):
 T(ω) ≥ |m₀|μ(K) − |m₀|η·μ(K) − |m₀|η ≥ |m₀|(a − η) − |m₀|η·a − |m₀|η = |m₀|a − |m₀|η(2 + a).
8. (Conclusion.) By steps 6 and 7, ofReal(|m₀|a − |m₀|η(2 + a)) ≤ T.massOn W for every η > 0. As η ↓ 0 the left side tends to ofReal(|m₀|a) = m·μ(M ∩ W), so m·μ(M ∩ W) ≤ T.massOn W. Together with step 3 this gives T.massOn W = m·μ(M ∩ W).

Lean reference proof (verified). The declaration below was compiled with `lake env lean` (Lean v4.35.0-rc3, Mathlib 25730c7c) inside a copy of GMT/Ch07/Submission.lean at this node's proof base (ee11750), placed after the contract definitions (namespace GMT.Ch07, contract `open`s, noncomputable section), together with the sibling declarations Submission.dor_ims_unitOrientation_dual, Submission.dor_ims_smooth_unit_approx (for reused siblings: their accepted candidate proofs spliced in). `#print axioms` reports only propext, Classical.choice and Quot.sound. It follows the numbered proof above step by step.

```lean
theorem Submission.dimred_rpd_massOn_eq_mult_measure : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (M W : Set (Euclid P)) (m₀ : ℤ) (ξ : Euclid P → MultiVector P n), IsOpen W → W ⊆ U → MeasurableSet M → ContinuousOn ξ M → (∀ x ∈ M, ∃ Q : Submodule ℝ (Euclid P), IsUnitOrientationOf (ξ x) Q) → μHE[n] (M ∩ W) ≠ ∞ → (∀ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Euclid P) n) ⊆ W → T ω = m₀ * ∫ x in M, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]) → T.massOn W = (m₀.natAbs : ℝ≥0∞) * μHE[n] (M ∩ W) := by
  intro P n U T M W m₀ ξ hW hWU hM hξc hξu hfin hrep
  obtain ⟨L, hL⟩ := Submission.dor_ims_unitOrientation_dual P n
  have hMW : MeasurableSet (M ∩ W) := hM.inter hW.measurableSet
  have hdual : ∀ x ∈ M, ∀ α : Covector (Euclid P) n, |ξ x α| ≤ covectorEuclideanNorm α := by
    intro x hx α
    obtain ⟨Q, hQ⟩ := hξu x hx
    exact (hL (ξ x) Q hQ).1 α
  -- the indicator of W is integrable on M
  have hrestW : (μHE[n] : Measure (Euclid P)).restrict M W = μHE[n] (M ∩ W) := by
    rw [Measure.restrict_apply hW.measurableSet, inter_comm]
  have hind : Integrable (W.indicator (fun _ => (1 : ℝ))) ((μHE[n] : Measure (Euclid P)).restrict M) := by
    rw [integrable_indicator_iff hW.measurableSet]
    refine integrableOn_const ?_
    rw [Measure.restrict_apply hW.measurableSet, inter_comm]
    exact hfin
  have hind_int : ∫ x in M, W.indicator (fun _ => (1 : ℝ)) x ∂μHE[n] = (μHE[n] : Measure (Euclid P)).real (M ∩ W) := by
    rw [integral_indicator hW.measurableSet, setIntegral_const, smul_eq_mul, mul_one,
      Measure.real, Measure.real, Measure.restrict_apply hW.measurableSet, inter_comm]
  -- bound and integrability for an admissible-type form
  have hbound : ∀ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Euclid P) n) ⊆ W →
      (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ 1) →
      ∀ x ∈ M, ‖ξ x ((ω : DifferentialForm (Euclid P) n) x)‖ ≤ W.indicator (fun _ => (1 : ℝ)) x := by
    intro ω hωW hω1 x hx
    by_cases hxW : x ∈ W
    · rw [indicator_of_mem hxW, Real.norm_eq_abs]
      exact (hdual x hx _).trans (hω1 x)
    · rw [indicator_of_notMem hxW]
      have h0 : (ω : DifferentialForm (Euclid P) n) x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hxW (hωW h))
      simp [h0]
  have hcontf : ∀ ω : TestFormOn U n,
      ContinuousOn (fun x => ξ x ((ω : DifferentialForm (Euclid P) n) x)) M := by
    intro ω
    have hωc : Continuous (ω : DifferentialForm (Euclid P) n) := ω.property.1.1.continuous
    exact hξc.clm_apply hωc.continuousOn
  have hintf : ∀ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Euclid P) n) ⊆ W →
      (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ 1) →
      Integrable (fun x => ξ x ((ω : DifferentialForm (Euclid P) n) x)) ((μHE[n] : Measure (Euclid P)).restrict M) := by
    intro ω hωW hω1
    refine hind.mono' ((hcontf ω).aestronglyMeasurable hM) ?_
    exact (ae_restrict_iff' hM).2 (Eventually.of_forall (hbound ω hωW hω1))
  have hcast : ENNReal.ofReal |(m₀ : ℝ)| = (m₀.natAbs : ℝ≥0∞) := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast, ENNReal.ofReal_natCast]
  apply le_antisymm
  · -- upper bound
    apply sSup_le
    rintro r ⟨ω, ⟨hωW, hω1⟩, rfl⟩
    have hI : ‖∫ x in M, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]‖ ≤
        (μHE[n] : Measure (Euclid P)).real (M ∩ W) := by
      calc ‖∫ x in M, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]‖
          ≤ ∫ x in M, ‖ξ x ((ω : DifferentialForm (Euclid P) n) x)‖ ∂μHE[n] :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ x in M, W.indicator (fun _ => (1 : ℝ)) x ∂μHE[n] :=
            integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hind
              ((ae_restrict_iff' hM).2 (Eventually.of_forall (hbound ω hωW hω1)))
        _ = _ := hind_int
    have hTω : T ω ≤ |(m₀ : ℝ)| * (μHE[n] : Measure (Euclid P)).real (M ∩ W) := by
      rw [hrep ω hωW]
      calc (m₀ : ℝ) * ∫ x in M, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]
          ≤ |(m₀ : ℝ) * ∫ x in M, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]| :=
            le_abs_self _
        _ = |(m₀ : ℝ)| * ‖∫ x in M, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]‖ := by
            rw [abs_mul, Real.norm_eq_abs]
        _ ≤ _ := mul_le_mul_of_nonneg_left hI (abs_nonneg _)
    calc ENNReal.ofReal (T ω) ≤ ENNReal.ofReal (|(m₀ : ℝ)| * (μHE[n] : Measure (Euclid P)).real (M ∩ W)) :=
          ENNReal.ofReal_le_ofReal hTω
      _ = (m₀.natAbs : ℝ≥0∞) * μHE[n] (M ∩ W) := by
          rw [ENNReal.ofReal_mul (abs_nonneg _), Measure.real, ENNReal.ofReal_toReal hfin, hcast]
  · -- lower bound
    rcases eq_or_ne m₀ 0 with rfl | hm₀
    · simp
    set a : ℝ := (μHE[n] : Measure (Euclid P)).real (M ∩ W) with ha
    have ha0 : 0 ≤ a := measureReal_nonneg
    set s₀ : ℝ := if (0 : ℝ) < m₀ then 1 else -1 with hs₀
    have hs₀m : (m₀ : ℝ) * s₀ = |(m₀ : ℝ)| := by
      rw [hs₀]
      split_ifs with h
      · rw [mul_one, abs_of_pos h]
      · rw [abs_of_nonpos (not_lt.1 h)]; ring
    have hs₀abs : s₀ = 1 ∨ s₀ = -1 := by
      rw [hs₀]; split_ifs <;> simp
    set β : Euclid P → Covector (Euclid P) n := fun x => s₀ • L (ξ x) with hβ
    have hβc : ContinuousOn β M :=
      (L.continuous.comp_continuousOn hξc).const_smul s₀
    have hβ1 : ∀ x ∈ M, covectorEuclideanNorm (β x) ≤ 1 := by
      intro x hx
      obtain ⟨Q, hQ⟩ := hξu x hx
      have h1 := (hL (ξ x) Q hQ).2.1
      rcases hs₀abs with h | h
      · have hx' : β x = L (ξ x) := by
          simp only [hβ, h]; exact one_smul ℝ (L (ξ x))
        rw [hx']; exact h1
      · have hx' : β x = -(L (ξ x)) := by
          simp only [hβ, h]; exact neg_one_smul ℝ (L (ξ x))
        rw [hx', covectorEuclideanNorm_neg]; exact h1
    have hβξ : ∀ x ∈ M, (m₀ : ℝ) * ξ x (β x) = |(m₀ : ℝ)| := by
      intro x hx
      obtain ⟨Q, hQ⟩ := hξu x hx
      have h1 := (hL (ξ x) Q hQ).2.2
      simp only [hβ, map_smul, smul_eq_mul, h1, mul_one]
      exact hs₀m
    -- main estimate for each η ∈ (0, 1)
    have hmain : ∀ η : ℝ, 0 < η →
        ENNReal.ofReal (|(m₀ : ℝ)| * a - |(m₀ : ℝ)| * η * (2 + a)) ≤ T.massOn W := by
      intro η hη
      have : IsFiniteMeasure ((μHE[n] : Measure (Euclid P)).restrict (M ∩ W)) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact hfin.lt_top⟩
      have hνA : ((μHE[n] : Measure (Euclid P)).restrict (M ∩ W)) (M ∩ W) ≠ ∞ := measure_ne_top _ _
      obtain ⟨K, hKA, hKc, hKsmall⟩ :=
        hMW.exists_isCompact_sdiff_lt (μ := (μHE[n] : Measure (Euclid P)).restrict (M ∩ W)) hνA
          (ENNReal.ofReal_pos.2 hη).ne'
      rw [Measure.restrict_apply (hMW.diff hKc.measurableSet)] at hKsmall
      have hdiffeq : (M ∩ W) \ K ∩ (M ∩ W) = (M ∩ W) \ K := by
        ext x; simp only [mem_inter_iff, Set.mem_sdiff]; tauto
      rw [hdiffeq] at hKsmall
      obtain ⟨ω₀, hω₀test, hω₀W, hω₀1, hω₀K⟩ := Submission.dor_ims_smooth_unit_approx P n K W β η
        hKc hW (hKA.trans inter_subset_right) (hβc.mono (hKA.trans inter_subset_left))
        (fun x hx => hβ1 x (hKA hx).1) hη
      let ω : TestFormOn U n := ⟨ω₀, hω₀test, hω₀W.trans hWU⟩
      have hωW : tsupport (ω : DifferentialForm (Euclid P) n) ⊆ W := hω₀W
      have hω1 : ∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ 1 := hω₀1
      have hadm : ω ∈ massAdmissibleOn U n W := ⟨hωW, hω1⟩
      have hle := T.le_massOn hadm
      refine le_trans ?_ hle
      apply ENNReal.ofReal_le_ofReal
      -- lower estimate of T ω
      set f : Euclid P → ℝ := fun x => (m₀ : ℝ) * ξ x ((ω : DifferentialForm (Euclid P) n) x) with hf
      have hfint : Integrable f ((μHE[n] : Measure (Euclid P)).restrict M) :=
        (hintf ω hωW hω1).const_mul _
      have hTω : T ω = ∫ x in M, f x ∂μHE[n] := by
        rw [hrep ω hωW, hf, integral_const_mul]
      have hKM : K ⊆ M := hKA.trans inter_subset_left
      have hsplit : ∫ x in M, f x ∂μHE[n] = ∫ x in K, f x ∂μHE[n] + ∫ x in M \ K, f x ∂μHE[n] := by
        rw [← setIntegral_union disjoint_sdiff_right (hM.diff hKc.measurableSet)
          (hfint.mono_measure (Measure.restrict_mono hKM le_rfl))
          (hfint.mono_measure (Measure.restrict_mono sdiff_subset le_rfl)),
          union_sdiff_cancel hKM]
      have hKfin : μHE[n] K ≠ ∞ := ne_top_of_le_ne_top hfin (measure_mono hKA)
      have hKle : (μHE[n] : Measure (Euclid P)).real K ≤ a :=
        measureReal_mono hKA hfin
      have hKge : a - η ≤ (μHE[n] : Measure (Euclid P)).real K := by
        have h1 : (μHE[n] : Measure (Euclid P)) (M ∩ W) ≤ μHE[n] K + μHE[n] ((M ∩ W) \ K) := by
          calc (μHE[n] : Measure (Euclid P)) (M ∩ W) ≤ μHE[n] (K ∪ (M ∩ W) \ K) :=
                measure_mono (fun x hx => by by_cases h : x ∈ K <;> simp_all)
            _ ≤ _ := measure_union_le _ _
        have h2 : (μHE[n] : Measure (Euclid P)) (M ∩ W) ≤ μHE[n] K + ENNReal.ofReal η :=
          h1.trans (add_le_add le_rfl hKsmall.le)
        have h3 := ENNReal.toReal_mono (by finiteness) h2
        rw [ENNReal.toReal_add hKfin ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hη.le] at h3
        simp only [Measure.real, ha] at h3 ⊢
        linarith
      have hKpart : |(m₀ : ℝ)| * (1 - η) * (μHE[n] : Measure (Euclid P)).real K ≤ ∫ x in K, f x ∂μHE[n] := by
        have hconst : ∀ x ∈ K, |(m₀ : ℝ)| * (1 - η) ≤ f x := by
          intro x hxK
          have hxM : x ∈ M := hKM hxK
          have hsplitx : f x = (m₀ : ℝ) * ξ x (β x) +
              (m₀ : ℝ) * ξ x ((ω : DifferentialForm (Euclid P) n) x - β x) := by
            simp only [hf, map_sub]; ring
          rw [hsplitx, hβξ x hxM]
          have hd : |(m₀ : ℝ) * ξ x ((ω : DifferentialForm (Euclid P) n) x - β x)| ≤ |(m₀ : ℝ)| * η := by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left ((hdual x hxM _).trans (hω₀K x hxK)) (abs_nonneg _)
          have := neg_abs_le ((m₀ : ℝ) * ξ x ((ω : DifferentialForm (Euclid P) n) x - β x))
          nlinarith
        have := setIntegral_ge_of_const_le_real hKc.measurableSet hKfin hconst
          (hfint.mono_measure (Measure.restrict_mono hKM le_rfl))
        simpa [Measure.real] using this
      have hRest : |∫ x in M \ K, f x ∂μHE[n]| ≤ |(m₀ : ℝ)| * η := by
        have hb : ∀ x ∈ M \ K, ‖f x‖ ≤ |(m₀ : ℝ)| * W.indicator (fun _ => (1 : ℝ)) x := by
          intro x hx
          rw [hf, norm_mul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hbound ω hωW hω1 x hx.1) (abs_nonneg _)
        have hint2 : Integrable (fun x => |(m₀ : ℝ)| * W.indicator (fun _ => (1 : ℝ)) x)
            ((μHE[n] : Measure (Euclid P)).restrict (M \ K)) :=
          (hind.mono_measure (Measure.restrict_mono sdiff_subset le_rfl)).const_mul _
        calc |∫ x in M \ K, f x ∂μHE[n]| = ‖∫ x in M \ K, f x ∂μHE[n]‖ := (Real.norm_eq_abs _).symm
          _ ≤ ∫ x in M \ K, ‖f x‖ ∂μHE[n] := norm_integral_le_integral_norm _
          _ ≤ ∫ x in M \ K, |(m₀ : ℝ)| * W.indicator (fun _ => (1 : ℝ)) x ∂μHE[n] :=
              integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hint2
                ((ae_restrict_iff' (hM.diff hKc.measurableSet)).2 (Eventually.of_forall hb))
          _ = |(m₀ : ℝ)| * (μHE[n] : Measure (Euclid P)).real ((M \ K) ∩ W) := by
              rw [integral_const_mul, integral_indicator hW.measurableSet, setIntegral_const,
                smul_eq_mul, mul_one, Measure.real, Measure.real,
                Measure.restrict_apply hW.measurableSet, inter_comm]
          _ ≤ |(m₀ : ℝ)| * η := by
              apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
              have hset : (M \ K) ∩ W = (M ∩ W) \ K := by
                ext x; simp only [mem_inter_iff, Set.mem_sdiff]; tauto
              rw [hset]
              have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hKsmall.le
              rwa [ENNReal.toReal_ofReal hη.le] at this
      rw [hTω, hsplit]
      have hRest' := neg_abs_le (∫ x in M \ K, f x ∂μHE[n])
      have hm0 : 0 ≤ |(m₀ : ℝ)| := abs_nonneg _
      have e1 := mul_le_mul_of_nonneg_left hKge hm0
      have e2 := mul_le_mul_of_nonneg_left hKle (mul_nonneg hm0 hη.le)
      nlinarith [e1, e2, hKpart, hRest, hRest']
    -- pass to the limit η → 0
    have hlim : Tendsto (fun η : ℝ => ENNReal.ofReal (|(m₀ : ℝ)| * a - |(m₀ : ℝ)| * η * (2 + a)))
        (𝓝[>] 0) (𝓝 (ENNReal.ofReal (|(m₀ : ℝ)| * a))) := by
      apply ENNReal.tendsto_ofReal
      have : Tendsto (fun η : ℝ => |(m₀ : ℝ)| * a - |(m₀ : ℝ)| * η * (2 + a)) (𝓝 0)
          (𝓝 (|(m₀ : ℝ)| * a - |(m₀ : ℝ)| * 0 * (2 + a))) := by
        exact (tendsto_const_nhds.sub ((tendsto_const_nhds.mul tendsto_id).mul tendsto_const_nhds))
      simpa using this.mono_left nhdsWithin_le_nhds
    have hge := le_of_tendsto hlim (eventually_nhdsWithin_of_forall fun η hη => hmain η hη)
    calc (m₀.natAbs : ℝ≥0∞) * μHE[n] (M ∩ W) = ENNReal.ofReal (|(m₀ : ℝ)| * a) := by
          rw [ENNReal.ofReal_mul (abs_nonneg _), ha, Measure.real, ENNReal.ofReal_toReal hfin, hcast]
      _ ≤ T.massOn W := hge
```

## Key steps

1. orientation_dual: |ξ(x)(α)| ≤ |α| on M, and β := sign(m₀)·L(ξ) is continuous on M with |β| ≤ 1 and m₀ξ(β) = |m₀|.
2. For admissible ω, |ξ(ω)| ≤ 1_W on M, so T(ω) ≤ |m₀|·Hⁿ(M ∩ W), giving M_W(T) ≤ |m₀|Hⁿ(M ∩ W).
3. Inner regularity of the finite measure Hⁿ⌞(M ∩ W) gives a compact K with Hⁿ((M ∩ W)∖K) < η; smooth_unit_approx gives an admissible ω with |ω − β| ≤ η on K.
4. Splitting ∫_M = ∫_K + ∫_{M∖K} gives T(ω) ≥ |m₀|a − |m₀|η(2 + a); letting η → 0 gives M_W(T) ≥ |m₀|Hⁿ(M ∩ W).

## Reference use

### local-project

Queries:
- `sha256sum GMT/Ch07/Contract.lean local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean; diff GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical; manifest pins project b4d606d, mathlib 25730c7c)`
- `grep -n 'def massOn|def massAdmissibleOn|covectorEuclideanNorm|le_massOn' simongmt/Poincare/SimonGMT/Chapter06/Mass.lean; grep -n 'zeroRegion|def GeometricCurrentOn.support|VanishesOn' Chapter06/CurrentLocalEquality.lean; grep -n 'TestFormOn|structure GeometricCurrentOn' Chapter06/Currents.lean; grep -n 'IsTestForm|DifferentialForm|Covector' Chapter06/Forms.lean`
- `sed -n 1,200p <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (euclideanHausdorffMeasure_def, euclideanHausdorffMeasure_zero, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Isometry.euclideanHausdorffMeasure_image)`
- `grep -n 'hausdorffMeasure_image_le|hausdorffMeasure_zero_singleton' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `grep -rn 'InnerRegularCompactLTTop|exists_isCompact_sdiff_lt' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean Mathlib/MeasureTheory/Measure/RegularityCompacts.lean; Lean: `μHE[n].InnerRegularCompactLTTop` fails under the contract imports but `(μHE[n].restrict A).InnerRegularCompactLTTop` succeeds for finite restrictions`
- `grep -n 'setIntegral_eq_zero_of_forall_eq_zero|setIntegral_union|setIntegral_ge_of_const_le_real|norm_setIntegral_le_of_norm_le_const' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `grep -rn 'theorem ContDiffAt.hasStrictFDerivAt|theorem addHaar_ball_of_pos|theorem IsOpen.inter_closure|theorem IsCompact.image_of_continuousOn|theorem finrank_euclideanSpace_fin|theorem LinearMap.finrank_range_of_inj|theorem invFunOn_eq' <snapshot>/mathlib/Mathlib`
- `grep -n '^theorem|^def' simongmt/Poincare/SimonGMT/Chapter02/{Submanifold,SubmanifoldTopology,AreaFormula,AreaNormalization}.lean (IsSimonLocalRepresentation, isEmbedding_chartMap, injective_area_formula_of_injective_derivative; none imported by the contract)`
- `python3 over dag.json: nodes whose lean_statement mentions IsEmbeddedSubmanifold, regularSet, covectorEuclideanNorm, IsUnitOrientationOf, μHE or massOn; accepted statuses; duplicate lean_names; grep -c dimred_rpd dag.json (0)`
- `git diff <proof_base> <candidate> -- GMT/Ch07/Submission.lean for 9c8432cb (dor_ims_unitOrientation_dual), 89e4c45c (dor_ims_smooth_unit_approx + dor_ims_sua_* helpers), 5e4b2158 (dsmc_chart_inverse_continuity): pure additions after RegularComponentsAreMinimizing`
- `nodes/root-dimension-reduction-results-a1-one-dim-cones-a1/decomposition-v2.json (sibling precedent for reusing accepted declarations)`
- `lake env lean /tmp/rpd-check/Check.lean (types + assembly); /tmp/rpd-check/{C1,C4,C7}.lean; /tmp/rpd-final/Final.lean (stubs for reused); /tmp/rpd-final/Full.lean and /tmp/rpd-final/SubmissionCopy.lean (accepted reused proofs spliced in; #print axioms = propext, Classical.choice, Quot.sound)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Submanifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldTopology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaFormula.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaNormalization.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/RegularityCompacts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Neighborhoods.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-regular-point-density-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1-unit-or-24edf309fb/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1-smooth-49478a38c9/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1-ch-0f11358db9/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-one-dim-cones-a1/decomposition-v2.json`
- `/tmp/rpd-final/Final.lean`
- `/tmp/rpd-final/SubmissionCopy.lean`

Pins match: the snapshot contract is byte-identical to the workspace Contract.lean and Submission.lean (sha256 e4148e7f…), and the manifest pins project b4d606d and mathlib 25730c7c.

Available under the contract imports:
- μHE[d] = c_d·μH[d] with one constant on every metric space, and μHE[n] = volume on Euclid n;
- LipschitzOnWith.hausdorffMeasure_image_le;
- ContDiffAt.hasStrictFDerivAt;
- Measure.addHaar_ball_of_pos;
- inner regularity (InnerRegularCompactLTTop) for finite restrictions μHE[n]⌞A, though not for μHE[n] itself.

Not available: SimonGMT's chart-embedding and area-formula modules (Chapter02) are not imported by the contract. No library lemma gives the mass of a local m₀[[M]] current or the density of a C¹ submanifold.

Reused building blocks: Submission.dor_ims_unitOrientation_dual, Submission.dor_ims_smooth_unit_approx and Submission.dsmc_chart_inverse_continuity are accepted DAG nodes with candidate commits. Their frozen types are reused byte-for-byte, following the sibling precedent one_dim_cones-a1 v2. No new name collides: there are 0 hits for dimred_rpd_.

Lean evidence: all child types and the parent assembly elaborate. With the accepted reused proofs spliced in, the selected theorem compiles inside a copy of Submission.lean with axioms propext, Classical.choice and Quot.sound only.
