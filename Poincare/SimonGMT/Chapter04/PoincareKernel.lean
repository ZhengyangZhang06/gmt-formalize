module

public import Poincare.SimonGMT.Chapter04.Sobolev

@[expose] public section

/-!
# Integrating the singular kernel in Simon (5.6)

The ball estimate proved here is the valid consequence of polynomial
mass growth needed in the Poincare proof. It does not use the incorrect
annular estimate printed in (4.10)(2).
-/

open Filter Function Metric Set MeasureTheory
open scoped ENNReal Topology

namespace Poincare.SimonGMT.Chapter04

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

/-- A measure supported in a ball and with `(m+1)`-dimensional ball
growth has an integrable inverse-`m` kernel. The constant is nonsharp,
and no annular growth assertion is assumed. -/
theorem lintegral_inverse_norm_pow_le_of_ballGrowth (μ : Measure E) [SFinite μ]
    (ξ : E) (m : ℕ) {B R : ℝ} (hB : 0 ≤ B) (hR : 0 < R)
    (hsupport : ∀ᵐ x ∂μ, ‖x - ξ‖ ≤ R)
    (hgrowth : ∀ t : ℝ, 0 < t → t ≤ R →
      μ (closedBall ξ t) ≤ ENNReal.ofReal (B * t ^ (m + 1))) :
    (∫⁻ x, ENNReal.ofReal (1 / ‖x - ξ‖ ^ m) ∂μ) ≤
      ENNReal.ofReal (((m + 2 : ℕ) : ℝ) * B * R) := by
  have hmass : μ univ ≤ ENNReal.ofReal (B * R ^ (m + 1)) := by
    apply le_trans (measure_mono_ae ?_) (hgrowth R hR le_rfl)
    filter_upwards [hsupport] with x hx _
    simpa only [mem_closedBall, dist_eq_norm] using hx
  by_cases hm : m = 0
  · subst m
    simpa only [pow_zero, div_one, ENNReal.ofReal_one, lintegral_const, one_mul,
      pow_one, Nat.cast_ofNat] using hmass.trans
      (ENNReal.ofReal_le_ofReal (by
        simpa using (show B * R ≤ (2 : ℝ) * B * R by nlinarith)))
  let k : E → ℝ → ℝ≥0∞ := fun x t ↦
    (Ici ‖x - ξ‖).indicator (fun t ↦ ENNReal.ofReal (‖x - ξ‖ / t ^ (m + 2))) t
  let F : ℝ → ℝ≥0∞ := fun t ↦ ∫⁻ x, k x t ∂μ
  have hk : AEMeasurable (uncurry k) (μ.prod (volume.restrict (Ioi 0))) := by
    change AEMeasurable ({z : E × ℝ | ‖z.1 - ξ‖ ≤ z.2}.indicator
      (fun z ↦ ENNReal.ofReal (‖z.1 - ξ‖ / z.2 ^ (m + 2)))) _
    exact (by fun_prop : Measurable
      (fun z : E × ℝ ↦ ENNReal.ofReal (‖z.1 - ξ‖ / z.2 ^ (m + 2)))).aemeasurable.indicator
      (isClosed_le (by fun_prop) (by fun_prop)).measurableSet
  have hrepr (x : E) : ENNReal.ofReal (1 / ‖x - ξ‖ ^ m) =
      ENNReal.ofReal (((m + 1 : ℕ) : ℝ)) * ∫⁻ t in Ioi 0, k x t := by
    by_cases hx : ‖x - ξ‖ = 0
    · simp [k, hx, zero_pow hm]
    · have hr : 0 < ‖x - ξ‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
      dsimp only [k]
      rw [lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
        inter_eq_left.mpr (show Ici ‖x - ξ‖ ⊆ Ioi (0 : ℝ) from fun _ ht ↦ hr.trans_le ht),
        lintegral_radial_inverse_power m hr,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg (m + 1))]
      congr 1
      have hn : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
  have hF (t : ℝ) : F t =
      ∫⁻ x in closedBall ξ t, ENNReal.ofReal (‖x - ξ‖ / t ^ (m + 2)) ∂μ := by
    dsimp only [F]
    rw [← lintegral_indicator measurableSet_closedBall]
    apply lintegral_congr
    intro x
    simp only [k, mem_Ici, mem_closedBall, dist_eq_norm, indicator]
  have hsmall (t : ℝ) (ht : 0 < t) (htR : t ≤ R) : F t ≤ ENNReal.ofReal B := by
    rw [hF]
    calc
      _ ≤ ∫⁻ _ in closedBall ξ t, ENNReal.ofReal (t / t ^ (m + 2)) ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
        apply ENNReal.ofReal_le_ofReal
        exact div_le_div_of_nonneg_right
          (by simpa only [mem_closedBall, dist_eq_norm] using hx) (pow_pos ht _).le
      _ = ENNReal.ofReal (t / t ^ (m + 2)) * μ (closedBall ξ t) := by simp
      _ ≤ ENNReal.ofReal (t / t ^ (m + 2)) * ENNReal.ofReal (B * t ^ (m + 1)) :=
        mul_le_mul' le_rfl (hgrowth t ht htR)
      _ = _ := by
        rw [← ENNReal.ofReal_mul (div_nonneg ht.le (pow_pos ht _).le)]
        congr 1
        rw [pow_succ t (m + 1)]
        field_simp
  have hlarge (t : ℝ) : F t ≤
      ENNReal.ofReal (B * R ^ (m + 1)) * ENNReal.ofReal (R / t ^ (m + 2)) := by
    have ht : 0 ≤ t ^ (m + 2) ∨ t ^ (m + 2) < 0 := le_or_gt 0 _
    rcases ht with ht | ht
    · calc
        _ ≤ ∫⁻ _ : E, ENNReal.ofReal (R / t ^ (m + 2)) ∂μ := by
          apply lintegral_mono_ae
          filter_upwards [hsupport] with x hx
          dsimp only [k]
          by_cases hxt : t ∈ Ici ‖x - ξ‖
          · rw [indicator_of_mem hxt]
            exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hx ht)
          · rw [indicator_of_notMem hxt]
            exact bot_le
        _ = ENNReal.ofReal (R / t ^ (m + 2)) * μ univ := by simp
        _ ≤ ENNReal.ofReal (R / t ^ (m + 2)) * ENNReal.ofReal (B * R ^ (m + 1)) :=
          mul_le_mul' le_rfl hmass
        _ = _ := mul_comm _ _
    · have hz : F t = 0 := by
        apply lintegral_eq_zero_of_ae_eq_zero
        filter_upwards with x
        dsimp only [k]
        have hz : ENNReal.ofReal (‖x - ξ‖ / t ^ (m + 2)) = 0 :=
          ENNReal.ofReal_eq_zero.mpr (div_nonpos_of_nonneg_of_nonpos (norm_nonneg _) ht.le)
        simp only [indicator, hz, ite_self, Pi.zero_apply]
      rw [hz]
      exact bot_le
  have hhead : (∫⁻ t in Ioc 0 R, F t) ≤ ENNReal.ofReal (B * R) := by
    calc
      _ ≤ ∫⁻ _ in Ioc (0 : ℝ) R, ENNReal.ofReal B := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact hsmall t ht.1 ht.2
      _ = _ := by simp [ENNReal.ofReal_mul hB]
  have htail : (∫⁻ t in Ioi R, F t) ≤ ENNReal.ofReal (B * R / ((m + 1 : ℕ) : ℝ)) := by
    calc
      _ ≤ ∫⁻ t in Ici R, F t := lintegral_mono_set Ioi_subset_Ici_self
      _ ≤ ∫⁻ t in Ici R, ENNReal.ofReal (B * R ^ (m + 1)) *
          ENNReal.ofReal (R / t ^ (m + 2)) := lintegral_mono hlarge
      _ = ENNReal.ofReal (B * R ^ (m + 1)) *
          ENNReal.ofReal (1 / (((m + 1 : ℕ) : ℝ) * R ^ m)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_radial_inverse_power m hR]
      _ = _ := by
        rw [← ENNReal.ofReal_mul (mul_nonneg hB (pow_pos hR _).le)]
        congr 1
        rw [pow_succ]
        field_simp
  calc
    _ = ENNReal.ofReal (((m + 1 : ℕ) : ℝ)) * ∫⁻ t in Ioi 0, F t := by
      simp_rw [hrepr]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_lintegral_swap hk]
    _ ≤ ENNReal.ofReal (((m + 1 : ℕ) : ℝ)) *
        (ENNReal.ofReal (B * R) + ENNReal.ofReal (B * R / ((m + 1 : ℕ) : ℝ))) := by
      apply mul_le_mul' le_rfl
      rw [← Ioc_union_Ioi_eq_Ioi hR.le,
        lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same]
      exact add_le_add hhead htail
    _ = _ := by
      rw [← ENNReal.ofReal_add (mul_nonneg hB hR.le)
        (div_nonneg (mul_nonneg hB hR.le) (Nat.cast_nonneg _)),
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 1
      have hn : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      push_cast
      field_simp
      ring

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ}

namespace RectifiableVarifold

variable (V : RectifiableVarifold (E := E) n)

/-- The uniform kernel bound required when integrating the pointwise
potential in Simon (5.6). The single outer mass bound and bounded mean
curvature supply all smaller-scale growth estimates. -/
theorem HasGeneralizedMeanCurvatureIn.lintegral_local_inverse_kernel_le
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H)
    (hn : 0 < n) {ξ x : E} {ρ Λ α Γ β : ℝ}
    (hρ : 0 < ρ) (hΛ : 0 ≤ Λ) (hα : 0 ≤ α) (hΓ : 0 ≤ Γ)
    (hβ : β ≤ 1) (hball : closedBall ξ (2 * ρ) ⊆ U)
    (hbound : ∀ y ∈ V.carrier ∩ U, ‖H y‖ ≤ Λ)
    (hexp : Real.exp (Λ * ρ) ≤ 1 + α)
    (hmass : V.weight.real (closedBall ξ (2 * ρ)) ≤ Γ * ρ ^ n)
    (hx : x ∈ closedBall ξ ρ) :
    (∫⁻ y in closedBall ξ (β * ρ), ENNReal.ofReal (1 / ‖y - x‖ ^ (n - 1)) ∂V.weight) ≤
      ENNReal.ofReal (((n + 1 : ℕ) : ℝ) * ((1 + α) * 2 ^ n * Γ) * (2 * ρ)) := by
  let μ := V.weight.restrict (closedBall ξ (β * ρ))
  let B := (1 + α) * 2 ^ n * Γ
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg (by linarith) (by positivity)) hΓ
  have hxρ : dist x ξ ≤ ρ := hx
  have hlocal : closedBall x ρ ⊆ U :=
    (closedBall_subset_closedBall' (show ρ + dist x ξ ≤ 2 * ρ by linarith)).trans hball
  have hinner : closedBall ξ (β * ρ) ⊆ closedBall ξ (2 * ρ) :=
    closedBall_subset_closedBall (by nlinarith)
  have hsmallmass : V.weight.real (closedBall x (ρ / 2)) ≤ Γ * ρ ^ n := by
    apply le_trans (measureReal_mono (closedBall_subset_closedBall'
      (show ρ / 2 + dist x ξ ≤ 2 * ρ by linarith)) (isCompact_closedBall ξ (2 * ρ)).measure_ne_top)
      hmass
  have hgrowth : ∀ t : ℝ, 0 < t →
      μ (closedBall x t) ≤ ENNReal.ofReal (B * t ^ n) := by
    intro t ht
    by_cases hthalf : t ≤ ρ / 2
    · have hmono := HasGeneralizedMeanCurvatureIn.exp_normalizedBallMass_monotoneOn
        (V := V) hH hbound x hlocal
        ⟨ht, by linarith⟩ ⟨by linarith, by linarith⟩ hthalf
      have hnonneg : 0 ≤ V.weight.real (closedBall x t) / t ^ n :=
        div_nonneg ENNReal.toReal_nonneg (pow_pos ht _).le
      have hexpt : 1 ≤ Real.exp (Λ * t) := Real.one_le_exp (mul_nonneg hΛ ht.le)
      have hexphalf : Real.exp (Λ * (ρ / 2)) ≤ 1 + α :=
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) hΛ)).trans hexp
      have hratio : V.weight.real (closedBall x t) / t ^ n ≤ B := by
        calc
          _ ≤ Real.exp (Λ * t) * (V.weight.real (closedBall x t) / t ^ n) := by
            simpa only [one_mul] using mul_le_mul_of_nonneg_right hexpt hnonneg
          _ ≤ Real.exp (Λ * (ρ / 2)) *
              (V.weight.real (closedBall x (ρ / 2)) / (ρ / 2) ^ n) := hmono
          _ ≤ (1 + α) * (Γ * ρ ^ n / (ρ / 2) ^ n) := by
            gcongr
          _ = B := by
            dsimp only [B]
            rw [div_pow]
            field_simp
      have hreal : V.weight.real (closedBall x t) ≤ B * t ^ n :=
        (div_le_iff₀ (pow_pos ht _)).mp hratio
      calc
        μ (closedBall x t) ≤ V.weight (closedBall x t) := Measure.restrict_apply_le _ _
        _ = ENNReal.ofReal (V.weight.real (closedBall x t)) :=
          (ENNReal.ofReal_toReal (isCompact_closedBall x t).measure_ne_top).symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal hreal
    · have hlarge : Γ * ρ ^ n ≤ B * t ^ n := by
        have hpow : ρ ^ n ≤ (2 * t) ^ n := pow_le_pow_left₀ hρ.le (by linarith) n
        rw [mul_pow] at hpow
        have hαpow : Γ * (2 ^ n * t ^ n) ≤ (1 + α) * (Γ * (2 ^ n * t ^ n)) := by
          exact le_mul_of_one_le_left (by positivity) (by linarith)
        calc
          _ ≤ Γ * (2 ^ n * t ^ n) := mul_le_mul_of_nonneg_left hpow hΓ
          _ ≤ (1 + α) * (Γ * (2 ^ n * t ^ n)) := hαpow
          _ = _ := by dsimp only [B]; ring
      calc
        μ (closedBall x t) ≤ V.weight (closedBall ξ (2 * ρ)) := by
          rw [Measure.restrict_apply measurableSet_closedBall]
          exact measure_mono (inter_subset_right.trans hinner)
        _ = ENNReal.ofReal (V.weight.real (closedBall ξ (2 * ρ))) :=
          (ENNReal.ofReal_toReal (isCompact_closedBall ξ (2 * ρ)).measure_ne_top).symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal (hmass.trans hlarge)
  have hsupp : ∀ᵐ y ∂μ, ‖y - x‖ ≤ 2 * ρ := by
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with y hy
    rw [← dist_eq_norm]
    calc
      dist y x ≤ dist y ξ + dist ξ x := dist_triangle _ _ _
      _ ≤ β * ρ + ρ := add_le_add hy (by simpa only [dist_comm] using hxρ)
      _ ≤ _ := by nlinarith
  have hkernel := lintegral_inverse_norm_pow_le_of_ballGrowth μ x (n - 1) hB
    (show 0 < 2 * ρ by positivity) hsupp (fun t ht _ ↦ by
      simpa only [Nat.sub_add_cancel hn] using hgrowth t ht)
  have hdim : n - 1 + 2 = n + 1 := by omega
  simpa only [hdim] using hkernel

end RectifiableVarifold

end

end Poincare.SimonGMT.Chapter04
