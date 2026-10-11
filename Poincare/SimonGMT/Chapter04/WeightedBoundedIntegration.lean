module

public import Poincare.SimonGMT.Chapter04.WeightedBallIntegration

@[expose] public section

/-!
# The bounded-curvature radius inequality behind Simon (5.4)

The exponential factor is derived from first variation with the corrected
coefficient in (5.2). The only curvature bound is on the varifold carrier
inside the open domain.
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

theorem HasGeneralizedMeanCurvatureIn.weightedCutoff_bounded_radius_inequality
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (hU : IsOpen U)
    {h : E → ℝ} (hh : ContDiffOn ℝ 1 h U) (hhnonneg : ∀ x ∈ U, 0 ≤ h x) (ξ : E)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (hbound : ∀ x ∈ V.carrier ∩ U, ‖H x‖ ≤ Λ)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφanti : Antitone φ)
    (hφrange : ∀ z, φ z ∈ Icc 0 1) {A σ ρ : ℝ} (hA : 0 < A)
    (hcutoff : ∀ z, A ^ 2 ≤ z → φ z = 0) (hσ : 0 < σ) (hσρ : σ ≤ ρ)
    (hball : closedBall ξ (ρ * A) ⊆ U) :
    V.weightedCutoffMass ξ h φ σ / σ ^ n ≤
      Real.exp (A * Λ * ρ) * (V.weightedCutoffMass ξ h φ ρ / ρ ^ n +
        ∫ t in σ..ρ,
          (∫ x, scaledRadialCutoff ξ φ t x * (‖x - ξ‖ * ‖V.tangentialGradient h x‖) ∂V.weight) /
            t ^ (n + 1)) := by
  let e := fun t ↦
    (∫ x, scaledRadialCutoff ξ φ t x * (‖x - ξ‖ * ‖V.tangentialGradient h x‖) ∂V.weight) /
      t ^ (n + 1)
  have hq : IntegrableOn (fun x ↦ ‖x - ξ‖ * ‖V.tangentialGradient h x‖)
      (closedBall ξ (ρ * A)) V.weight :=
    IntegrableOn.continuousOn_mul (by fun_prop)
      (V.integrableOn_norm_tangentialGradient hU hh (isCompact_closedBall _ _) hball)
      (isCompact_closedBall _ _)
  have he : ContinuousOn e (Icc σ ρ) :=
    (V.continuousOn_integral_scaledRadialCutoff_mul ξ hφ.continuous hφrange hA hcutoff hσ hq).div
      (continuousOn_id.pow _) (fun t ht ↦ pow_ne_zero _ (hσ.trans_le ht.1).ne')
  have he0 : ∀ t ∈ Icc σ ρ, 0 ≤ e t := by
    intro t ht
    exact div_nonneg (integral_nonneg fun x ↦
      mul_nonneg (hφrange _).1 (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
      (pow_pos (hσ.trans_le ht.1) _).le
  have hE : (∫ t in σ..ρ, Real.exp (A * Λ * t) * e t) ≤
      Real.exp (A * Λ * ρ) * ∫ t in σ..ρ, e t := by
    rw [← intervalIntegral.integral_const_mul]
    have hc : ContinuousOn (fun t ↦ Real.exp (A * Λ * t) * e t) (Icc σ ρ) :=
      (show ContinuousOn (fun t ↦ Real.exp (A * Λ * t)) (Icc σ ρ) by fun_prop).mul he
    apply intervalIntegral.integral_mono_on hσρ
      (hc.intervalIntegrable_of_Icc hσρ)
      ((he.const_mul _).intervalIntegrable_of_Icc hσρ)
    intro t ht
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left ht.2 (mul_nonneg hA.le hΛ))) (he0 t ht)
  have hM : 0 ≤ V.weightedCutoffMass ξ h φ σ / σ ^ n := by
    apply div_nonneg ?_ (pow_pos hσ _).le
    apply integral_nonneg
    intro x
    by_cases hx : x ∈ closedBall ξ (σ * A)
    · exact mul_nonneg (hφrange _).1 (hhnonneg x
        (hball (closedBall_subset_closedBall (mul_le_mul_of_nonneg_right hσρ hA.le) hx)))
    · simp only [scaledRadialCutoff_eq_zero_of_notMem_closedBall ξ hA hcutoff hσ hx, zero_mul,
        Pi.zero_apply, le_rfl]
  have hleft : V.weightedCutoffMass ξ h φ σ / σ ^ n ≤
      Real.exp (A * Λ * σ) * (V.weightedCutoffMass ξ h φ σ / σ ^ n) := by
    have := mul_le_mul_of_nonneg_right
      (Real.one_le_exp_iff.mpr (mul_nonneg (mul_nonneg hA.le hΛ) hσ.le)) hM
    simpa only [one_mul] using this
  have hc := HasGeneralizedMeanCurvatureIn.weightedCutoff_exp_radius_inequality
    (V := V) hH hU hh hhnonneg ξ hbound hφ hφanti hφrange hA hcutoff hσ hσρ hball
  change V.weightedCutoffMass ξ h φ σ / σ ^ n ≤
    Real.exp (A * Λ * ρ) * (V.weightedCutoffMass ξ h φ ρ / ρ ^ n + ∫ t in σ..ρ, e t)
  change _ ≤ _ + ∫ t in σ..ρ, Real.exp (A * Λ * t) * e t at hc
  nlinarith

/-- The closed-ball radius-integral form of Simon (5.4). The singular
kernel bound is separated so that infinite potentials remain meaningful. -/
theorem HasGeneralizedMeanCurvatureIn.weightedBall_bounded_radius_inequality
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (hU : IsOpen U)
    {h : E → ℝ} (hh : ContDiffOn ℝ 1 h U) (hhnonneg : ∀ x ∈ U, 0 ≤ h x) (ξ : E)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (hbound : ∀ x ∈ V.carrier ∩ U, ‖H x‖ ≤ Λ)
    {σ ρ : ℝ} (hσ : 0 < σ) (hσρ : σ ≤ ρ) (hball : closedBall ξ ρ ⊆ U) :
    (∫ x in closedBall ξ σ, h x ∂V.weight) / σ ^ n ≤
      Real.exp (Λ * ρ) * ((∫ x in closedBall ξ ρ, h x ∂V.weight) / ρ ^ n +
        ∫ t in σ..ρ, (∫ x in closedBall ξ t,
          ‖x - ξ‖ * ‖V.tangentialGradient h x‖ ∂V.weight) / t ^ (n + 1)) := by
  have hρ := hσ.trans_le hσρ
  obtain ⟨S, hρS, hSball⟩ := exists_larger_closedBall_subset hU ξ hρ.le hball
  have hhint : IntegrableOn h (closedBall ξ S) V.weight :=
    (hh.continuousOn.mono hSball).integrableOn_compact (isCompact_closedBall _ _)
  have hq : IntegrableOn (fun x ↦ ‖x - ξ‖ * ‖V.tangentialGradient h x‖)
      (closedBall ξ S) V.weight :=
    IntegrableOn.continuousOn_mul (by fun_prop)
      (V.integrableOn_norm_tangentialGradient hU hh (isCompact_closedBall _ _) hSball)
      (isCompact_closedBall _ _)
  have hexp : Tendsto (fun ε ↦ Real.exp ((1 + ε) * Λ * ρ)) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.exp (Λ * ρ))) := by
    have hid : Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_id.mono_left inf_le_left
    have hs : Tendsto (fun ε : ℝ ↦ 1 + ε) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
      simpa only [add_zero] using tendsto_const_nhds.add hid
    simpa only [one_mul] using ((hs.mul_const Λ).mul_const ρ).rexp
  apply le_of_tendsto_of_tendsto
    ((V.tendsto_integral_scaledRadialCutoff_mul_local ξ hσ (hσρ.trans_lt hρS) hhint).div_const (σ ^ n))
    (hexp.mul (((V.tendsto_integral_scaledRadialCutoff_mul_local ξ hρ hρS hhint).div_const (ρ ^ n)).add
      (V.tendsto_radiusIntegral_scaledRadialCutoff_local ξ hσ hσρ hρS hq)))
  have hδ : 0 < S / ρ - 1 := by rw [sub_pos, lt_div_iff₀ hρ]; simpa using hρS
  filter_upwards [self_mem_nhdsWithin,
    (gt_mem_nhds hδ).filter_mono inf_le_left] with ε hε hsmall
  change 0 < ε at hε
  have hA : 0 < 1 + ε := by linarith
  have hρA : ρ * (1 + ε) ≤ S := by
    have := (lt_div_iff₀ hρ).mp (show 1 + ε < S / ρ by linarith)
    nlinarith
  exact HasGeneralizedMeanCurvatureIn.weightedCutoff_bounded_radius_inequality
    (V := V) hH hU hh hhnonneg ξ hΛ hbound (contDiff_monotonicityCutoff ε)
    (monotonicityCutoff_antitone hε) (monotonicityCutoff_mem_Icc ε) hA
    (monotonicityCutoff_cutoff hε) hσ hσρ
    ((closedBall_subset_closedBall hρA).trans hSball)

end RectifiableVarifold

end

end Poincare.SimonGMT.Chapter04
