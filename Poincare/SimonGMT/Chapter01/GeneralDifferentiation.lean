module

public import Poincare.SimonGMT.Chapter01.GeneralDensity
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

/-!
# Simon GMT, Chapter 1, differentiation under the symmetric Vitali property

The countable level-set argument uses the general upper-density theorem
and the general density theorem, with no separability assumption.
-/

open Filter Metric Set MeasureTheory
open scoped ENNReal Topology Classical

namespace Poincare.SimonGMT.Chapter01

variable {X : Type*} [MetricSpace X]

local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

set_option maxHeartbeats 800000 in
/-- The nonnegative, globally integrable step in Simon (3.17), first for
Borel measurable extended-real functions. -/
theorem ae_tendsto_setLIntegral_div_of_measurable
    (μ : Measure X) (hopen : IsOpenSigmaFinite μ.toOuterMeasure)
    (hV : HasSymmetricVitaliProperty μ.toOuterMeasure)
    {f : X → ℝ≥0∞} (hf : Measurable f) (hfin : ∫⁻ x, f x ∂μ ≠ ∞) :
    ∀ᵐ x ∂μ, Tendsto (fun r : ℝ => (∫⁻ y in closedBall x r, f y ∂μ) /
      μ (closedBall x r)) (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by
  let ν := μ.withDensity f
  let : IsFiniteMeasure ν := isFiniteMeasure_withDensity hfin
  have hμ := measure_toOuterMeasure_isBorelRegular μ
  have hν := measure_toOuterMeasure_isBorelRegular ν
  have hμeq : hμ.toBorelMeasure = μ := by
    ext S hS
    exact hμ.toBorelMeasure_apply_all S
  have hzero : ∀ᵐ x ∂μ, x ∉ zeroBallRegion μ.toOuterMeasure := by
    rw [ae_iff]
    simpa only [not_not, ofPred_mem_eq, Measure.toOuterMeasure_apply] using
      hV.zeroBallRegion_eq_zero_of_openSigmaFinite hopen
  have hupper : ∀ q : ℚ, ∀ᵐ x ∂μ, f x ≤ (Real.toNNReal q : ℝ≥0∞) →
      outerRelativeUpperDensity ν.toOuterMeasure μ.toOuterMeasure x ≤ Real.toNNReal q := by
    intro q
    let c : ℝ≥0∞ := Real.toNNReal q
    let S : Set X := {x | f x ≤ c}
    have hS : MeasurableSet S := measurableSet_le hf measurable_const
    have hden := ae_outerRelativeUpperDensity_restrict_eq_zero_outside
      ν.toOuterMeasure μ.toOuterMeasure hν hμ hopen hV
      (hν.borel_le_caratheodory Sᶜ (by simpa only [BorelSpace.measurable_eq] using hS.compl))
      (measure_lt_top ν Sᶜ)
    rw [hμeq] at hden
    filter_upwards [hden, hzero] with x hx hxzero hfx
    have ht := tendsto_outerRelativeDensityQuotient_zero_of_upperDensity_zero
      (OuterMeasure.restrict Sᶜ ν.toOuterMeasure) μ.toOuterMeasure x
      (hx (not_not.mpr (show x ∈ S from hfx)))
    have htadd : Tendsto (fun r => c + outerRelativeDensityQuotient
        (OuterMeasure.restrict Sᶜ ν.toOuterMeasure) μ.toOuterMeasure x r)
        (𝓝[>] (0 : ℝ)) (𝓝 c) := by simpa using tendsto_const_nhds.add ht
    apply le_trans (limsup_le_limsup (v := fun r => c + outerRelativeDensityQuotient
      (OuterMeasure.restrict Sᶜ ν.toOuterMeasure) μ.toOuterMeasure x r) ?_) htadd.limsup_eq.le
    filter_upwards [eventually_closedBall_measure_ne_top μ.toOuterMeasure hopen x,
      self_mem_nhdsWithin] with r hrfin hrpos
    have hrzero : μ (closedBall x r) ≠ 0 := fun h => hxzero ⟨r, hrpos, h⟩
    have hmass : ν (closedBall x r ∩ S) ≤ c * μ (closedBall x r) := by
      rw [withDensity_apply _ (measurableSet_closedBall.inter hS)]
      calc
        ∫⁻ y in closedBall x r ∩ S, f y ∂μ ≤
            ∫⁻ _ in closedBall x r ∩ S, c ∂μ :=
          setLIntegral_mono' (measurableSet_closedBall.inter hS) fun y hy => hy.2
        _ = c * μ (closedBall x r ∩ S) := by simp
        _ ≤ c * μ (closedBall x r) :=
          mul_le_mul_right (measure_mono (μ := μ) inter_subset_left) c
    simp only [outerRelativeDensityQuotient, OuterMeasure.restrict_apply,
      Measure.toOuterMeasure_apply]
    rw [← measure_inter_add_sdiff (closedBall x r) hS, ENNReal.add_div]
    have hmul : c * μ (closedBall x r) / μ (closedBall x r) = c := by
      rw [mul_div_assoc, ENNReal.div_self hrzero hrfin, mul_one]
    exact add_le_add ((ENNReal.div_le_div_right hmass _).trans_eq hmul) (by rfl)
  have hlower : ∀ q : ℚ, ∀ᵐ x ∂μ, (Real.toNNReal q : ℝ≥0∞) ≤ f x →
      (Real.toNNReal q : ℝ≥0∞) ≤
        outerRelativeLowerDensity ν.toOuterMeasure μ.toOuterMeasure x := by
    intro q
    let c : ℝ≥0∞ := Real.toNNReal q
    let S : Set X := {x | c ≤ f x}
    have hS : MeasurableSet S := measurableSet_le measurable_const hf
    have hden := simon_theorem_3_16 μ.toOuterMeasure hμ hopen hV
      (hμ.borel_le_caratheodory S (by simpa only [BorelSpace.measurable_eq] using hS))
    rw [hμeq] at hden
    filter_upwards [hden] with x hx hfx
    have ht : Tendsto (fun r : ℝ => c * (μ (S ∩ closedBall x r) /
        μ (closedBall x r))) (𝓝[>] (0 : ℝ)) (𝓝 c) := by
      simpa only [indicator_of_mem (show x ∈ S from hfx), mul_one,
        Measure.toOuterMeasure_apply] using
        (ENNReal.Tendsto.const_mul hx (by simp [c]))
    apply le_trans ht.liminf_eq.ge (liminf_le_liminf ?_)
    apply Eventually.of_forall
    intro r
    have hmass : c * μ (S ∩ closedBall x r) ≤ ν (closedBall x r) := by
      calc
        c * μ (S ∩ closedBall x r) = ∫⁻ _ in S ∩ closedBall x r, c ∂μ := by simp
        _ ≤ ∫⁻ y in S ∩ closedBall x r, f y ∂μ :=
          setLIntegral_mono' (hS.inter measurableSet_closedBall) fun y hy => hy.1
        _ = ν (S ∩ closedBall x r) := (withDensity_apply _ (hS.inter measurableSet_closedBall)).symm
        _ ≤ ν (closedBall x r) := measure_mono inter_subset_right
    simpa only [outerRelativeDensityQuotient, Measure.toOuterMeasure_apply,
      mul_div_assoc] using ENNReal.div_le_div_right hmass (μ (closedBall x r))
  filter_upwards [ae_all_iff.mpr hupper, ae_all_iff.mpr hlower] with x hxup hxlo
  have hi : f x ≤ outerRelativeLowerDensity ν.toOuterMeasure μ.toOuterMeasure x := by
    apply le_of_forall_lt
    intro a ha
    obtain ⟨q, _, haq, hqf⟩ := ENNReal.lt_iff_exists_rat_btwn.mp ha
    exact haq.trans_le (hxlo q hqf.le)
  have hs : outerRelativeUpperDensity ν.toOuterMeasure μ.toOuterMeasure x ≤ f x := by
    apply le_of_forall_gt
    intro b hb
    obtain ⟨q, _, hfq, hqb⟩ := ENNReal.lt_iff_exists_rat_btwn.mp hb
    exact (hxup q hfq.le).trans_lt hqb
  have ht := tendsto_of_le_liminf_of_limsup_le hi hs
  convert ht using 1
  ext r
  simp only [outerRelativeDensityQuotient, Measure.toOuterMeasure_apply,
    ν, withDensity_apply _ measurableSet_closedBall]

/-- Completion does not change the differentiation conclusion: the
nonnegative integrand need only be almost everywhere measurable. -/
theorem ae_tendsto_setLIntegral_div_of_aemeasurable
    (μ : Measure X) (hopen : IsOpenSigmaFinite μ.toOuterMeasure)
    (hV : HasSymmetricVitaliProperty μ.toOuterMeasure)
    {f : X → ℝ≥0∞} (hf : AEMeasurable f μ) (hfin : ∫⁻ x, f x ∂μ ≠ ∞) :
    ∀ᵐ x ∂μ, Tendsto (fun r : ℝ => (∫⁻ y in closedBall x r, f y ∂μ) /
      μ (closedBall x r)) (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by
  have heq : ∫⁻ x, f x ∂μ = ∫⁻ x, hf.mk f x ∂μ := lintegral_congr_ae hf.ae_eq_mk
  have h := ae_tendsto_setLIntegral_div_of_measurable μ hopen hV hf.measurable_mk
    (heq ▸ hfin)
  filter_upwards [h, hf.ae_eq_mk] with x hx hfx
  rw [hfx]
  apply hx.congr
  intro r
  congr 1
  exact (lintegral_congr_ae (ae_restrict_of_ae hf.ae_eq_mk)).symm

/-- The nonnegative real-valued, globally integrable case of Simon (3.17). -/
theorem ae_tendsto_setIntegral_div_of_nonneg_integrable
    (μ : Measure X) (hopen : IsOpenSigmaFinite μ.toOuterMeasure)
    (hV : HasSymmetricVitaliProperty μ.toOuterMeasure)
    {f : X → ℝ} (hf : Integrable f μ) (hfnonneg : ∀ x, 0 ≤ f x) :
    ∀ᵐ x ∂μ, Tendsto (fun r : ℝ => (∫ y in closedBall x r, f y ∂μ) /
      (μ (closedBall x r)).toReal) (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by
  have hfin : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≠ ∞ :=
    ((lintegral_ofReal_le_lintegral_enorm f).trans_lt hf.2).ne
  filter_upwards [ae_tendsto_setLIntegral_div_of_aemeasurable μ hopen hV
    hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal hfin] with x hx
  have ht := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp hx
  simpa only [Function.comp_def, ENNReal.toReal_div, ENNReal.toReal_ofReal (hfnonneg x),
    ← integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hfnonneg)
      hf.aestronglyMeasurable.restrict] using ht

/-- The globally integrable signed case of Simon (3.17), obtained by
subtracting the two nonnegative parts. -/
theorem ae_tendsto_setIntegral_div_of_integrable
    (μ : Measure X) (hopen : IsOpenSigmaFinite μ.toOuterMeasure)
    (hV : HasSymmetricVitaliProperty μ.toOuterMeasure)
    {f : X → ℝ} (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun r : ℝ => (∫ y in closedBall x r, f y ∂μ) /
      (μ (closedBall x r)).toReal) (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by
  filter_upwards [ae_tendsto_setIntegral_div_of_nonneg_integrable μ hopen hV
    hf.real_toNNReal (fun _ => NNReal.coe_nonneg _),
    ae_tendsto_setIntegral_div_of_nonneg_integrable μ hopen hV
      hf.neg.real_toNNReal (fun _ => NNReal.coe_nonneg _)] with x hxpos hxneg
  have ht := hxpos.sub hxneg
  simp only [Pi.neg_apply] at ht
  have hval : (Real.toNNReal (f x) : ℝ) - Real.toNNReal (-f x) = f x := by simp
  rw [hval] at ht
  apply ht.congr
  intro r
  rw [← sub_div, ← integral_eq_integral_pos_part_sub_integral_neg_part hf.integrableOn]

/-- Local integrability admits a countable family of integrable balls
covering almost every point.  The countability comes from the source's
symmetric Vitali property, and does not assume a countable topological base. -/
theorem exists_countable_integrable_balls_cover_ae
    (μ : Measure X) (hopen : IsOpenSigmaFinite μ.toOuterMeasure)
    (hV : HasSymmetricVitaliProperty μ.toOuterMeasure)
    {f : X → ℝ} (hf : LocallyIntegrable f μ) :
    ∃ D : Set (X × ℝ), D.Countable ∧
      (∀ b ∈ D, 0 < b.2 ∧ IntegrableOn f (closedBall b.1 (2 * b.2)) μ) ∧
      ∀ᵐ x ∂μ, ∃ b ∈ D, x ∈ ball b.1 (2 * b.2) := by
  obtain ⟨U, hU, hcover⟩ := (isOpenSigmaFinite_iff μ.toOuterMeasure).mp hopen
  let B : ℕ → Set (X × ℝ) := fun j => {b | b.1 ∈ U j ∧ 0 < b.2 ∧
    IntegrableOn f (closedBall b.1 (2 * b.2)) μ}
  have hfine : ∀ j x, x ∈ U j → ∀ ε > 0, ∃ r ∈ Ioo 0 ε, (x, r) ∈ B j := by
    intro j x hx ε hε
    obtain ⟨S, hS, hfS⟩ := hf x
    obtain ⟨R, hR, hRS⟩ := nhds_basis_closedBall.mem_iff.mp hS
    let r := min (ε / 2) (R / 2)
    have hr : 0 < r := lt_min (half_pos hε) (half_pos hR)
    have hrε : r < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
    have hrR : 2 * r ≤ R := by dsimp [r]; have := min_le_right (ε / 2) (R / 2); linarith
    exact ⟨r, ⟨hr, hrε⟩, hx, hr,
      hfS.mono_set ((closedBall_subset_closedBall hrR).trans hRS)⟩
  choose D hDsub hDcount hDdisj hDnull using fun j =>
    hV (U j) (hU j).2 (B j) (fun b hb => ⟨hb.1, hb.2.1⟩) (hfine j)
  refine ⟨⋃ j, D j, countable_iUnion hDcount, ?_, ?_⟩
  · intro b hb
    obtain ⟨j, hbj⟩ := mem_iUnion.mp hb
    exact (hDsub j hbj).2
  · have haej : ∀ j : ℕ, ∀ᵐ x ∂μ, x ∈ U j →
        ∃ b ∈ D j, x ∈ ball b.1 (2 * b.2) := by
      intro j
      have hnull : ∀ᵐ x ∂μ, x ∉ U j \ ⋃ b ∈ D j, closedBall b.1 b.2 := by
        rw [ae_iff]
        simpa only [not_not, ofPred_mem_eq, Measure.toOuterMeasure_apply] using hDnull j
      filter_upwards [hnull] with x hx hxU
      have hxcover : x ∈ ⋃ b ∈ D j, closedBall b.1 b.2 := by
        by_contra h
        exact hx ⟨hxU, h⟩
      obtain ⟨b, hb, hxb⟩ := mem_iUnion₂.mp hxcover
      refine ⟨b, hb, ?_⟩
      have hbpos := (hDsub j hb).2.1
      exact closedBall_subset_ball (by linarith) hxb
    filter_upwards [ae_all_iff.mpr haej] with x hx
    obtain ⟨j, hxj⟩ := mem_iUnion.mp (hcover.symm ▸ mem_univ x)
    obtain ⟨b, hb, hxb⟩ := hx j hxj
    exact ⟨b, mem_iUnion.mpr ⟨j, hb⟩, hxb⟩

/-- Simon (3.17) for the canonical Borel measure, with the full local
integrability hypothesis.  Almost everywhere measurable functions are
included, so completion-measurable functions are included as well. -/
theorem ae_tendsto_setIntegral_div_of_locallyIntegrable
    (μ : Measure X) (hopen : IsOpenSigmaFinite μ.toOuterMeasure)
    (hV : HasSymmetricVitaliProperty μ.toOuterMeasure)
    {f : X → ℝ} (hf : LocallyIntegrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun r : ℝ => (∫ y in closedBall x r, f y ∂μ) /
      (μ (closedBall x r)).toReal) (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by
  obtain ⟨D, hDcount, hDgood, hDcover⟩ :=
    exists_countable_integrable_balls_cover_ae μ hopen hV hf
  let : Countable D := hDcount.to_subtype
  have hlocal : ∀ b : D, ∀ᵐ x ∂μ, x ∈ ball b.val.1 (2 * b.val.2) →
      Tendsto (fun r : ℝ => (∫ y in closedBall x r, f y ∂μ) /
        (μ (closedBall x r)).toReal) (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by
    intro b
    let S := closedBall b.val.1 (2 * b.val.2)
    have hgf : Integrable (S.indicator f) μ :=
      (hDgood b.val b.property).2.integrable_indicator measurableSet_closedBall
    filter_upwards [ae_tendsto_setIntegral_div_of_integrable μ hopen hV hgf] with x hx hxb
    have hxS : x ∈ S := ball_subset_closedBall hxb
    rw [indicator_of_mem hxS] at hx
    apply hx.congr'
    obtain ⟨R, hR, hRS⟩ := nhds_basis_closedBall.mem_iff.mp
      (mem_of_superset (isOpen_ball.mem_nhds hxb)
        (show ball b.val.1 (2 * b.val.2) ⊆ S from ball_subset_closedBall))
    filter_upwards [Ioo_mem_nhdsGT hR] with r hr
    congr 1
    exact setIntegral_congr_fun measurableSet_closedBall fun y hy =>
      indicator_of_mem (hRS ((closedBall_subset_closedBall hr.2.le) hy)) f
  filter_upwards [ae_all_iff.mpr hlocal, hDcover] with x hx hxD
  obtain ⟨b, hb, hxb⟩ := hxD
  exact hx ⟨b, hb⟩ hxb

/-- Simon Corollary (3.17), with exactly the open sigma-finite,
Borel-regular and symmetric-Vitali assumptions of Theorem (3.16).
The Borel measure agrees with the source outer measure on every set;
its Bochner integral includes completed, almost everywhere measurable
integrands. -/
theorem simon_corollary_3_17
    (μ : OuterMeasure X) (hμ : IsBorelRegularOuterMeasure μ)
    (hopen : IsOpenSigmaFinite μ) (hV : HasSymmetricVitaliProperty μ)
    {f : X → ℝ} (hf : LocallyIntegrable f hμ.toBorelMeasure) :
    ∀ᵐ x ∂hμ.toBorelMeasure, Tendsto (fun r : ℝ =>
      (μ (closedBall x r)).toReal⁻¹ * ∫ y in closedBall x r, f y ∂hμ.toBorelMeasure)
      (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by
  have h := ae_tendsto_setIntegral_div_of_locallyIntegrable hμ.toBorelMeasure
    (by simpa only [hμ.toOuterMeasure_toBorelMeasure] using hopen)
    (by simpa only [hμ.toOuterMeasure_toBorelMeasure] using hV) hf
  simpa only [hμ.toBorelMeasure_apply_all, div_eq_inv_mul] using h

/-- Under open sigma-finiteness, a real function measurable for Simon's
full Caratheodory sigma-algebra is almost everywhere Borel measurable. -/
theorem IsBorelRegularOuterMeasure.aemeasurable_of_caratheodory
    {μ : OuterMeasure X} (hμ : IsBorelRegularOuterMeasure μ)
    (hopen : IsOpenSigmaFinite μ) {f : X → ℝ}
    (hf : @Measurable X ℝ μ.caratheodory (borel ℝ) f) :
    AEMeasurable f hμ.toBorelMeasure := by
  apply NullMeasurable.aemeasurable
  intro S hS
  obtain ⟨B, hBsub, hB, hBnull, _⟩ :=
    hμ.exists_borel_subset_mod_null hopen (hf hS)
  apply hB.nullMeasurableSet.congr
  apply ae_eq_set.mpr
  constructor
  · simp only [sdiff_eq_empty.mpr hBsub, measure_empty]
  · simpa only [hμ.toBorelMeasure_apply_all] using hBnull

/-- The literal measurability and local absolute-integral formulation
printed in Simon Corollary (3.17).  This adapter verifies that no Borel-only
measurability restriction is hidden in the integral formulation. -/
theorem simon_corollary_3_17_of_caratheodory
    (μ : OuterMeasure X) (hμ : IsBorelRegularOuterMeasure μ)
    (hopen : IsOpenSigmaFinite μ) (hV : HasSymmetricVitaliProperty μ)
    {f : X → ℝ} (hf : @Measurable X ℝ μ.caratheodory (borel ℝ) f)
    (hlocal : ∀ x : X, ∃ r > 0,
      (∫⁻ y in closedBall x r, ENNReal.ofReal |f y| ∂hμ.toBorelMeasure) < ∞) :
    ∀ᵐ x ∂hμ.toBorelMeasure, Tendsto (fun r : ℝ =>
      (μ (closedBall x r)).toReal⁻¹ * ∫ y in closedBall x r, f y ∂hμ.toBorelMeasure)
      (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by
  apply simon_corollary_3_17 μ hμ hopen hV
  intro x
  obtain ⟨r, hr, hfr⟩ := hlocal x
  refine ⟨closedBall x r, closedBall_mem_nhds x hr,
    (hμ.aemeasurable_of_caratheodory hopen hf).aestronglyMeasurable.restrict, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simpa only [Real.norm_eq_abs] using hfr

end Poincare.SimonGMT.Chapter01
