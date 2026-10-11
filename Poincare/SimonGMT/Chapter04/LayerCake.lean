module

public import Poincare.SimonGMT.Chapter04.LpAnnular
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-!
# Simon GMT, Chapter 4, Lemma 4.11: truncated layer-cake identities

The power identity is stated with nonnegative extended integrals: an `L¹`
function need not have a finite higher moment. This preserves the literal
range of positive powers without an unprinted integrability assumption.
-/

open Filter Function Metric Set MeasureTheory
open scoped ENNReal Topology

namespace Poincare.SimonGMT.Chapter04

noncomputable section

variable {X : Type*} [MeasurableSpace X]

/-- Tonelli's formula above a positive (or arbitrary real) threshold. This
is the common mechanism for both identities in Simon (4.11). -/
theorem lintegral_tail_weight (μ : Measure X) [SFinite μ]
    {f : X → ℝ} (hf : AEMeasurable f μ) {g : ℝ → ℝ} (hg : Measurable g)
    (a : ℝ) (hgpos : ∀ t, a < t → 0 ≤ g t)
    (hgint : ∀ b, a < b → IntervalIntegrable g volume a b) :
    (∫⁻ t in Ioi a, ENNReal.ofReal (g t) * μ {x | t < f x}) =
      ∫⁻ x in {x | a < f x}, ENNReal.ofReal (∫ t in a..f x, g t) ∂μ := by
  let k : X → ℝ → ℝ≥0∞ := fun x t ↦ if t < f x then ENNReal.ofReal (g t) else 0
  have hk : AEMeasurable (uncurry k) (μ.prod (volume.restrict (Ioi a))) := by
    change AEMeasurable
      ({z : X × ℝ | z.2 < f z.1}.indicator (fun z ↦ ENNReal.ofReal (g z.2))) _
    exact ((hg.comp measurable_snd).ennreal_ofReal.aemeasurable).indicator₀
      (nullMeasurableSet_lt measurable_snd.aemeasurable hf.comp_fst)
  have hinner : ∀ x, (∫⁻ t in Ioi a, k x t) =
      ({x | a < f x}.indicator (fun x ↦ ENNReal.ofReal (∫ t in a..f x, g t))) x := by
    intro x
    change (∫⁻ t in Ioi a, (Iio (f x)).indicator (fun t ↦ ENNReal.ofReal (g t)) t) = _
    rw [lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
      inter_comm, Ioi_inter_Iio]
    by_cases hax : a < f x
    · rw [indicator_of_mem (show x ∈ {x | a < f x} from hax)]
      rw [← ofReal_integral_eq_lintegral_ofReal]
      · rw [intervalIntegral.integral_of_le hax.le, integral_Ioc_eq_integral_Ioo]
      · exact (hgint (f x) hax).1.mono_set Ioo_subset_Ioc_self
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        exact hgpos t ht.1
    · simp only [Ioo_eq_empty_of_le (le_of_not_gt hax), Measure.restrict_empty,
        lintegral_zero_measure, indicator_of_notMem (show x ∉ {x | a < f x} from hax)]
  calc
    _ = ∫⁻ t in Ioi a, ∫⁻ x, k x t ∂μ := by
      apply lintegral_congr
      intro t
      change _ = ∫⁻ x, {x | t < f x}.indicator (fun _ ↦ ENNReal.ofReal (g t)) x ∂μ
      rw [lintegral_indicator_const₀ (nullMeasurableSet_lt aemeasurable_const hf)]
    _ = ∫⁻ x, (∫⁻ t in Ioi a, k x t) ∂μ := (lintegral_lintegral_swap hk).symm
    _ = _ := by
      simp_rw [hinner]
      exact lintegral_indicator₀ (nullMeasurableSet_lt aemeasurable_const hf) _

/-- Simon (4.11), power case, with exactly the strict superlevel sets in
the source. This stronger version needs no finite-measure or `L¹` bound;
both sides may be infinite when the indicated moment diverges. -/
theorem layerCake_rpow (μ : Measure X) [SFinite μ]
    {f : X → ℝ} (hf : AEMeasurable f μ) {a α : ℝ} (ha : 0 < a) (hα : 0 < α) :
    (∫⁻ t in Ioi a, ENNReal.ofReal (t ^ (α - 1)) * μ {x | t < f x}) =
      ENNReal.ofReal α⁻¹ * ∫⁻ x in {x | a < f x},
        ENNReal.ofReal (f x ^ α - a ^ α) ∂μ := by
  rw [lintegral_tail_weight μ hf (g := fun t : ℝ ↦ t ^ (α - 1))
    (measurable_id.pow_const _) a
    (fun t ht ↦ Real.rpow_nonneg (ha.trans ht).le _)
    (fun b hb ↦ intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < α - 1))]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem₀ (nullMeasurableSet_lt aemeasurable_const hf)] with x hx
  rw [integral_rpow (Or.inl (by linarith : -1 < α - 1))]
  simp only [sub_add_cancel]
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hα.le)]
  congr 1
  ring

/-- Simon (4.11), logarithmic case. No zero-threshold singularity is
introduced: the positive lower endpoint makes the primitive `log(f/a)`. -/
theorem layerCake_log (μ : Measure X) [SFinite μ]
    {f : X → ℝ} (hf : AEMeasurable f μ) {a : ℝ} (ha : 0 < a) :
    (∫⁻ t in Ioi a, ENNReal.ofReal t⁻¹ * μ {x | t < f x}) =
      ∫⁻ x in {x | a < f x}, ENNReal.ofReal (Real.log (f x / a)) ∂μ := by
  rw [lintegral_tail_weight μ hf (g := fun t : ℝ ↦ t⁻¹) measurable_id.inv a
    (fun t ht ↦ inv_nonneg.mpr (ha.trans ht).le)
    (fun b hb ↦ (continuousOn_id.inv₀ (fun t ht ↦
      (ha.trans_le ht.1).ne')).intervalIntegrable_of_Icc (le_of_lt hb))]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem₀ (nullMeasurableSet_lt aemeasurable_const hf)] with x hx
  rw [integral_inv_of_pos ha (ha.trans hx)]

/-- The logarithmic superlevel moment is finite under the source `L¹`
hypothesis, because `0 ≤ log(f/a) ≤ |f|/a` on `f>a>0`. -/
theorem integrableOn_log_superlevel {μ : Measure X} {f : X → ℝ}
    (hf : Integrable f μ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x ↦ Real.log (f x / a)) {x | a < f x} μ := by
  apply ((hf.norm.div_const a).restrict).mono'
  · exact (hf.aemeasurable.div_const a).log.aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem₀ (nullMeasurableSet_lt aemeasurable_const hf.aemeasurable)]
      with x hx
    have hfx : 0 < f x := ha.trans hx
    have hlog : 0 ≤ Real.log (f x / a) :=
      Real.log_nonneg ((one_le_div ha).mpr hx.le)
    rw [Real.norm_eq_abs, abs_of_nonneg hlog, Real.norm_eq_abs, abs_of_pos hfx]
    linarith [Real.log_le_sub_one_of_pos (div_pos hfx ha)]

/-- The finite real-integral version of the logarithmic identity in
(4.11), under the source finite-measure and `L¹` assumptions. -/
theorem layerCake_log_integral (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → ℝ} (hf : Integrable f μ) {a : ℝ} (ha : 0 < a) :
    (∫ t in Ioi a, t⁻¹ * μ.real {x | t < f x}) =
      ∫ x in {x | a < f x}, Real.log (f x / a) ∂μ := by
  have ht : Antitone (fun t : ℝ ↦ μ {x | t < f x}) := by
    intro s t hst
    exact measure_mono (fun x hx ↦ hst.trans_lt hx)
  have hmeas : Measurable (fun t : ℝ ↦ t⁻¹ * μ.real {x | t < f x}) :=
    measurable_id.inv.mul ht.measurable.ennreal_toReal
  have hpos : ∀ᵐ t ∂volume.restrict (Ioi a), 0 ≤ t⁻¹ * μ.real {x | t < f x} := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (inv_nonneg.mpr (ha.trans ht).le) ENNReal.toReal_nonneg
  rw [integral_eq_lintegral_of_nonneg_ae hpos hmeas.aestronglyMeasurable.restrict]
  have heq : (∫⁻ t in Ioi a, ENNReal.ofReal (t⁻¹ * μ.real {x | t < f x})) =
      ∫⁻ t in Ioi a, ENNReal.ofReal t⁻¹ * μ {x | t < f x} := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [ENNReal.ofReal_mul (inv_nonneg.mpr (ha.trans ht).le), measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [heq, layerCake_log μ hf.aemeasurable ha]
  have hlog : ∀ᵐ x ∂μ.restrict {x | a < f x}, 0 ≤ Real.log (f x / a) := by
    filter_upwards [ae_restrict_mem₀ (nullMeasurableSet_lt aemeasurable_const hf.aemeasurable)]
      with x hx
    exact Real.log_nonneg ((one_le_div ha).mpr hx.le)
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_log_superlevel hf ha) hlog,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hlog)]

end

end Poincare.SimonGMT.Chapter04
