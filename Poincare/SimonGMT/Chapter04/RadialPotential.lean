module

public import Poincare.SimonGMT.Chapter04.WeightedBallIntegration
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

/-!
# The singular-potential estimate in Simon (5.4)--(5.5)

This is a nonnegative Tonelli estimate; no finiteness assumption is placed
on the singular potential. The sharp coefficient is `1/n`.
-/

open Filter Function Metric Set MeasureTheory
open scoped ENNReal Topology

namespace Poincare.SimonGMT.Chapter04

noncomputable section

theorem lintegral_radial_inverse_power (m : ℕ) {r : ℝ} (hr : 0 < r) :
    (∫⁻ t in Ici r, ENNReal.ofReal (r / t ^ (m + 2))) =
      ENNReal.ofReal (1 / (((m + 1 : ℕ) : ℝ) * r ^ m)) := by
  let a : ℝ := -((m + 2 : ℕ) : ℝ)
  have ha : a < -1 := by dsimp only [a]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) m]
  have heq : ∀ t ∈ Ioi r, r * t ^ a = r / t ^ (m + 2) := by
    intro t ht
    dsimp only [a]
    rw [Real.rpow_neg (hr.trans ht).le, Real.rpow_natCast, div_eq_mul_inv]
  have hint : IntegrableOn (fun t : ℝ ↦ r / t ^ (m + 2)) (Ioi r) volume :=
    IntegrableOn.congr_fun ((integrableOn_Ioi_rpow_of_lt ha hr).const_mul r) heq measurableSet_Ioi
  have hvalue : (∫ t in Ioi r, r / t ^ (m + 2)) = 1 / (((m + 1 : ℕ) : ℝ) * r ^ m) := by
    calc
      _ = ∫ t in Ioi r, r * t ^ a := setIntegral_congr_fun measurableSet_Ioi (fun t ht ↦ (heq t ht).symm)
      _ = r * (-r ^ (a + 1) / (a + 1)) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt ha hr]
      _ = _ := by
        have ha1 : a + 1 = -((m + 1 : ℕ) : ℝ) := by dsimp only [a]; push_cast; ring
        rw [ha1, Real.rpow_neg hr.le, Real.rpow_natCast, pow_succ]
        have hn : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        field_simp
  have hint' : IntegrableOn (fun t : ℝ ↦ r / t ^ (m + 2)) (Ici r) volume :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr hint
  rw [← ofReal_integral_eq_lintegral_ofReal hint', integral_Ici_eq_integral_Ioi, hvalue]
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  exact div_nonneg hr.le (pow_pos (hr.trans_le ht) _).le

universe u

variable {E : Type u} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

/-- Tonelli's radial estimate with nonnegative extended-valued weights.
It applies without integrability assumptions. At the centre the radial
energy is zero, so no atomlessness assertion is needed for this estimate. -/
theorem lintegral_radius_energy_le_potential (μ : Measure E) [SFinite μ]
    (ξ : E) (m : ℕ) {P : E → ℝ≥0∞} (hP : AEMeasurable P μ) (σ ρ : ℝ) :
    (∫⁻ t in Ioc σ ρ, ENNReal.ofReal (1 / t ^ (m + 2)) *
      ∫⁻ x in closedBall ξ t, ENNReal.ofReal ‖x - ξ‖ * P x ∂μ) ≤
      ENNReal.ofReal (((m + 1 : ℕ) : ℝ)⁻¹) *
        ∫⁻ x, ENNReal.ofReal (1 / ‖x - ξ‖ ^ m) * P x ∂μ := by
  classical
  let k : E → ℝ → ℝ≥0∞ := fun x t ↦
    (Ici ‖x - ξ‖).indicator (fun t ↦ ENNReal.ofReal (‖x - ξ‖ / t ^ (m + 2)) * P x) t
  have hk : AEMeasurable (uncurry k) (μ.prod (volume.restrict (Ioc σ ρ))) := by
    change AEMeasurable ({z : E × ℝ | ‖z.1 - ξ‖ ≤ z.2}.indicator
      (fun z ↦ ENNReal.ofReal (‖z.1 - ξ‖ / z.2 ^ (m + 2)) * P z.1)) _
    have hm : Measurable (fun z : E × ℝ ↦ ‖z.1 - ξ‖ / z.2 ^ (m + 2)) := by fun_prop
    exact (hm.ennreal_ofReal.aemeasurable.mul hP.comp_fst).indicator
      (isClosed_le (by fun_prop) (by fun_prop)).measurableSet
  have hinner : ∀ x, (∫⁻ t in Ioc σ ρ, k x t) ≤
      ENNReal.ofReal (((m + 1 : ℕ) : ℝ)⁻¹) *
        (ENNReal.ofReal (1 / ‖x - ξ‖ ^ m) * P x) := by
    intro x
    by_cases hx : ‖x - ξ‖ = 0
    · have hz : (fun t ↦ k x t) = 0 := by
        funext t
        simp [k, hx]
      rw [hz]
      change (∫⁻ t in Ioc σ ρ, (0 : ℝ≥0∞)) ≤ _
      rw [lintegral_zero]
      exact bot_le
    · have hr : 0 < ‖x - ξ‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
      calc
        _ ≤ ∫⁻ t, k x t := lintegral_mono' Measure.restrict_le_self le_rfl
        _ = ∫⁻ t in Ici ‖x - ξ‖, ENNReal.ofReal (‖x - ξ‖ / t ^ (m + 2)) * P x :=
          lintegral_indicator measurableSet_Ici _
        _ = (∫⁻ t in Ici ‖x - ξ‖, ENNReal.ofReal (‖x - ξ‖ / t ^ (m + 2))) * P x :=
          lintegral_mul_const _ (by fun_prop)
        _ = ENNReal.ofReal (1 / (((m + 1 : ℕ) : ℝ) * ‖x - ξ‖ ^ m)) * P x := by
          rw [lintegral_radial_inverse_power m hr]
        _ = _ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr (Nat.cast_nonneg _))]
          congr 2
          ring
  calc
    _ = ∫⁻ t in Ioc σ ρ, ∫⁻ x, k x t ∂μ := by
      apply lintegral_congr
      intro t
      have heq : (fun x ↦ k x t) = (closedBall ξ t).indicator
          (fun x ↦ ENNReal.ofReal (1 / t ^ (m + 2)) * (ENNReal.ofReal ‖x - ξ‖ * P x)) := by
        funext x
        by_cases hx : x ∈ closedBall ξ t
        · have hr : t ∈ Ici ‖x - ξ‖ := by simpa only [mem_closedBall, dist_eq_norm, mem_Ici] using hx
          simp only [k, indicator_of_mem hr, indicator_of_mem hx]
          rw [div_eq_mul_inv, ENNReal.ofReal_mul (norm_nonneg _), one_div]
          ac_rfl
        · have hr : t ∉ Ici ‖x - ξ‖ := by simpa only [mem_closedBall, dist_eq_norm, mem_Ici] using hx
          simp only [k, indicator_of_notMem hr, indicator_of_notMem hx]
      rw [heq, lintegral_indicator measurableSet_closedBall,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ∫⁻ x, (∫⁻ t in Ioc σ ρ, k x t) ∂μ := (lintegral_lintegral_swap hk).symm
    _ ≤ ∫⁻ x, ENNReal.ofReal (((m + 1 : ℕ) : ℝ)⁻¹) *
        (ENNReal.ofReal (1 / ‖x - ξ‖ ^ m) * P x) ∂μ := lintegral_mono hinner
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- The same estimate for a real `L¹` energy on the outer ball. The left
side is the finite-radius Bochner expression, while the right side is an
extended nonnegative integral and may be infinite. -/
theorem ofReal_radius_energy_le_potential (μ : Measure E) [SFinite μ]
    (ξ : E) (m : ℕ) {σ ρ : ℝ} (hσ : 0 < σ) (hσρ : σ ≤ ρ)
    {q : E → ℝ} (hq : IntegrableOn q (closedBall ξ ρ) μ)
    (hq0 : ∀ x ∈ closedBall ξ ρ, 0 ≤ q x) :
    ENNReal.ofReal (∫ t in σ..ρ,
      (∫ x in closedBall ξ t, ‖x - ξ‖ * q x ∂μ) / t ^ (m + 2)) ≤
      ENNReal.ofReal (((m + 1 : ℕ) : ℝ)⁻¹) *
        ∫⁻ x in closedBall ξ ρ, ENNReal.ofReal (q x / ‖x - ξ‖ ^ m) ∂μ := by
  have hqr : IntegrableOn (fun x ↦ ‖x - ξ‖ * q x) (closedBall ξ ρ) μ := by
    apply hq.bdd_mul ((continuous_id.sub continuous_const).norm.aestronglyMeasurable.restrict)
      (c := ρ)
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
    change ‖‖x - ξ‖‖ ≤ ρ
    simpa only [norm_norm, mem_closedBall, dist_eq_norm] using hx
  have hTon := lintegral_radius_energy_le_potential (μ.restrict (closedBall ξ ρ)) ξ m
    hq.aestronglyMeasurable.aemeasurable.ennreal_ofReal σ ρ
  have hL : (∫⁻ t in Ioc σ ρ, ENNReal.ofReal (1 / t ^ (m + 2)) *
      ∫⁻ x in closedBall ξ t, ENNReal.ofReal ‖x - ξ‖ * ENNReal.ofReal (q x)
        ∂(μ.restrict (closedBall ξ ρ))) =
      ∫⁻ t in Ioc σ ρ, ENNReal.ofReal (1 / t ^ (m + 2)) *
        ∫⁻ x in closedBall ξ t, ENNReal.ofReal ‖x - ξ‖ * ENNReal.ofReal (q x) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Measure.restrict_restrict measurableSet_closedBall,
      inter_eq_left.mpr (closedBall_subset_closedBall ht.2)]
  rw [hL] at hTon
  have hR : (∫⁻ x in closedBall ξ ρ, ENNReal.ofReal (1 / ‖x - ξ‖ ^ m) *
      ENNReal.ofReal (q x) ∂μ) =
      ∫⁻ x in closedBall ξ ρ, ENNReal.ofReal (q x / ‖x - ξ‖ ^ m) ∂μ := by
    apply lintegral_congr
    intro x
    rw [← ENNReal.ofReal_mul (div_nonneg zero_le_one (pow_nonneg (norm_nonneg _) _))]
    congr 1
    ring
  rw [hR] at hTon
  apply le_trans ?_ hTon
  rw [intervalIntegral.integral_of_le hσρ]
  apply (Real.ofReal_le_enorm _).trans
  apply (enorm_integral_le_lintegral_enorm _).trans
  apply le_of_eq
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have hsub := closedBall_subset_closedBall (x := ξ) ht.2
  have hint := hqr.mono_set hsub
  have hnn : 0 ≤ᵐ[μ.restrict (closedBall ξ t)] (fun x ↦ ‖x - ξ‖ * q x) := by
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
    exact mul_nonneg (norm_nonneg _) (hq0 x (hsub hx))
  have hi0 := integral_nonneg_of_ae hnn
  have ht0 := hσ.trans ht.1
  rw [Real.enorm_eq_ofReal (div_nonneg hi0 (pow_pos ht0 _).le), div_eq_mul_inv,
    ENNReal.ofReal_mul hi0, ofReal_integral_eq_lintegral_ofReal hint hnn, one_div, mul_comm]
  congr 1
  apply lintegral_congr
  intro x
  exact ENNReal.ofReal_mul (norm_nonneg _)

end

end Poincare.SimonGMT.Chapter04
