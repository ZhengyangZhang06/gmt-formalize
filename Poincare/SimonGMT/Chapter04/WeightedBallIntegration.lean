module

public import Poincare.SimonGMT.Chapter04.WeightedRadiusIntegration

@[expose] public section

/-!
# Closed-ball radius estimates for Simon Chapter 4, (5.4)--(5.5)

Dominated convergence is applied twice. The radius integral stays away
from zero, so local `L¹` energy suffices even if the eventual singular
potential at the centre is infinite. Boundary spheres are not discarded.
-/

open Filter Function Metric Set MeasureTheory
open scoped ENNReal Topology

namespace Poincare.SimonGMT.Chapter04

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {n : ℕ}

namespace RectifiableVarifold

variable (V : RectifiableVarifold (E := E) n)

theorem tendsto_radiusIntegral_scaledRadialCutoff_integrable
    (ξ : E) {σ ρ : ℝ} (hσ : 0 < σ) (hσρ : σ ≤ ρ)
    {q : E → ℝ} (hq : Integrable q V.weight) :
    Tendsto (fun ε ↦ ∫ t in σ..ρ,
      (∫ x, scaledRadialCutoff ξ (monotonicityCutoff ε) t x * q x ∂V.weight) / t ^ (n + 1))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ t in σ..ρ, (∫ x in closedBall ξ t, q x ∂V.weight) / t ^ (n + 1))) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ ↦ (∫ x, ‖q x‖ ∂V.weight) / σ ^ (n + 1))
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    change 0 < ε at hε
    have he := (V.continuousOn_integral_scaledRadialCutoff_mul ξ
      (contDiff_monotonicityCutoff ε).continuous (monotonicityCutoff_mem_Icc ε)
      (by linarith : 0 < 1 + ε) (monotonicityCutoff_cutoff hε) hσ hq.restrict).div
      (continuousOn_id.pow (n + 1))
      (fun t (ht : t ∈ Icc σ ρ) ↦ pow_ne_zero _ (hσ.trans_le ht.1).ne')
    rw [uIoc_of_le hσρ]
    exact (he.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · apply Eventually.of_forall
    intro ε
    filter_upwards with t ht
    rw [uIoc_of_le hσρ] at ht
    have ht0 := hσ.trans ht.1
    rw [norm_div, Real.norm_of_nonneg (pow_pos ht0 _).le]
    have hnorm : ‖∫ x, scaledRadialCutoff ξ (monotonicityCutoff ε) t x * q x ∂V.weight‖ ≤
        ∫ x, ‖q x‖ ∂V.weight := by
      apply norm_integral_le_of_norm_le hq.norm
      filter_upwards with x
      rw [norm_mul, scaledRadialCutoff,
        Real.norm_of_nonneg (monotonicityCutoff_mem_Icc ε _).1]
      exact (mul_le_mul_of_nonneg_right (monotonicityCutoff_mem_Icc ε _).2
        (norm_nonneg _)).trans_eq (one_mul _)
    exact (div_le_div_of_nonneg_right hnorm (pow_pos ht0 _).le).trans
      (div_le_div_of_nonneg_left (integral_nonneg fun x ↦ norm_nonneg (q x))
        (pow_pos hσ _) (pow_le_pow_left₀ hσ.le ht.1.le _))
  · exact intervalIntegrable_const
  · filter_upwards with t ht
    rw [uIoc_of_le hσρ] at ht
    exact (V.tendsto_integral_scaledRadialCutoff_mul_integrable ξ (hσ.trans ht.1) hq).div_const _

theorem tendsto_radiusIntegral_scaledRadialCutoff_local
    (ξ : E) {σ ρ S : ℝ} (hσ : 0 < σ) (hσρ : σ ≤ ρ) (hρS : ρ < S)
    {q : E → ℝ} (hq : IntegrableOn q (closedBall ξ S) V.weight) :
    Tendsto (fun ε ↦ ∫ t in σ..ρ,
      (∫ x, scaledRadialCutoff ξ (monotonicityCutoff ε) t x * q x ∂V.weight) / t ^ (n + 1))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ t in σ..ρ, (∫ x in closedBall ξ t, q x ∂V.weight) / t ^ (n + 1))) := by
  classical
  let q' := (closedBall ξ S).indicator q
  have hq' : Integrable q' V.weight := hq.integrable_indicator measurableSet_closedBall
  have hlim := V.tendsto_radiusIntegral_scaledRadialCutoff_integrable ξ hσ hσρ hq'
  have heq : (∫ t in σ..ρ, (∫ x in closedBall ξ t, q' x ∂V.weight) / t ^ (n + 1)) =
      ∫ t in σ..ρ, (∫ x in closedBall ξ t, q x ∂V.weight) / t ^ (n + 1) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hσρ] at ht
    dsimp only
    congr 1
    apply setIntegral_congr_fun measurableSet_closedBall
    intro x hx
    exact indicator_of_mem (closedBall_subset_closedBall (ht.2.trans hρS.le) hx) q
  rw [heq] at hlim
  apply hlim.congr'
  have hρ := hσ.trans_le hσρ
  have hδ : 0 < S / ρ - 1 := by rw [sub_pos, lt_div_iff₀ hρ]; simpa using hρS
  filter_upwards [self_mem_nhdsWithin,
    (gt_mem_nhds hδ).filter_mono inf_le_left] with ε hε hsmall
  change 0 < ε at hε
  have hA : 0 < 1 + ε := by linarith
  have hρA : ρ * (1 + ε) ≤ S := by
    have := (lt_div_iff₀ hρ).mp (show 1 + ε < S / ρ by linarith)
    nlinarith
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hσρ] at ht
  dsimp only [q']
  rw [scaledRadialCutoff_mul_indicator ξ hA (monotonicityCutoff_cutoff hε)
    (hσ.trans_le ht.1) ((mul_le_mul_of_nonneg_right ht.2 hA.le).trans hρA)]

/-- The literal, finite radius-integral inequality immediately before
Simon (5.5), before estimating it by a possibly infinite potential. -/
theorem HasGeneralizedMeanCurvatureIn.weightedBall_radius_inequality
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (hU : IsOpen U)
    {h : E → ℝ} (hh : ContDiffOn ℝ 1 h U) (hhnonneg : ∀ x ∈ U, 0 ≤ h x) (ξ : E)
    {σ ρ : ℝ} (hσ : 0 < σ) (hσρ : σ ≤ ρ) (hball : closedBall ξ ρ ⊆ U) :
    (∫ x in closedBall ξ σ, h x ∂V.weight) / σ ^ n ≤
      (∫ x in closedBall ξ ρ, h x ∂V.weight) / ρ ^ n +
        ∫ t in σ..ρ, (∫ x in closedBall ξ t,
          ‖x - ξ‖ * (‖V.tangentialGradient h x‖ + h x * ‖H x‖) ∂V.weight) / t ^ (n + 1) := by
  have hρ := hσ.trans_le hσρ
  obtain ⟨S, hρS, hSball⟩ := exists_larger_closedBall_subset hU ξ hρ.le hball
  have hhint : IntegrableOn h (closedBall ξ S) V.weight :=
    (hh.continuousOn.mono hSball).integrableOn_compact (isCompact_closedBall _ _)
  have hq : IntegrableOn
      (fun x ↦ ‖x - ξ‖ * (‖V.tangentialGradient h x‖ + h x * ‖H x‖))
      (closedBall ξ S) V.weight :=
    IntegrableOn.continuousOn_mul (by fun_prop)
      (HasGeneralizedMeanCurvatureIn.integrableOn_weightedEnergy (V := V) hH hU hh
        (isCompact_closedBall _ _) hSball) (isCompact_closedBall _ _)
  apply le_of_tendsto_of_tendsto
    ((V.tendsto_integral_scaledRadialCutoff_mul_local ξ hσ (hσρ.trans_lt hρS) hhint).div_const (σ ^ n))
    (((V.tendsto_integral_scaledRadialCutoff_mul_local ξ hρ hρS hhint).div_const (ρ ^ n)).add
      (V.tendsto_radiusIntegral_scaledRadialCutoff_local ξ hσ hσρ hρS hq))
  have hδ : 0 < S / ρ - 1 := by rw [sub_pos, lt_div_iff₀ hρ]; simpa using hρS
  filter_upwards [self_mem_nhdsWithin,
    (gt_mem_nhds hδ).filter_mono inf_le_left] with ε hε hsmall
  change 0 < ε at hε
  have hA : 0 < 1 + ε := by linarith
  have hρA : ρ * (1 + ε) ≤ S := by
    have := (lt_div_iff₀ hρ).mp (show 1 + ε < S / ρ by linarith)
    nlinarith
  exact HasGeneralizedMeanCurvatureIn.weightedCutoff_radius_inequality
    (V := V) hH hU hh hhnonneg ξ (contDiff_monotonicityCutoff ε)
    (monotonicityCutoff_antitone hε) (monotonicityCutoff_mem_Icc ε) hA
    (monotonicityCutoff_cutoff hε) hσ hσρ
    ((closedBall_subset_closedBall hρA).trans hSball)

end RectifiableVarifold

end

end Poincare.SimonGMT.Chapter04
