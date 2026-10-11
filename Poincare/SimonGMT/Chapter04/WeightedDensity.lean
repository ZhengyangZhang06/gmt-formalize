module

public import Poincare.SimonGMT.Chapter04.MultiplicityBridge
public import Mathlib.MeasureTheory.Integral.Bochner.FundThmCalculus

@[expose] public section

/-!
# Continuous weighted density and the pointwise consequence before (5.6)

The weighted density limit is derived from the fundamental theorem for
shrinking set integrals. The last theorem explicitly assumes the lower
density bound; it does not infer this from multiplicity.
-/

open Filter Function Metric Set MeasureTheory Asymptotics
open scoped ENNReal Topology

namespace Poincare.SimonGMT.Chapter04

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {n : ℕ}

namespace RectifiableVarifold

variable (V : RectifiableVarifold (E := E) n)

/-- Multiplication by a continuous scalar multiplies the normalized ball
density by its value at the centre. Only local continuity is needed. -/
theorem tendsto_weightedBallAverage_of_tendsto_density
    {U : Set E} (hU : IsOpen U) {h : E → ℝ} (hh : ContinuousOn h U)
    {ξ : E} (hξ : ξ ∈ U) {d : ℝ}
    (hd : Tendsto (fun r ↦ V.weight.real (closedBall ξ r) /
      ((Chapter01.realUnitBallVolume (n : ℝ)).toReal * r ^ n))
      (𝓝[>] (0 : ℝ)) (𝓝 d)) :
    Tendsto (V.weightedBallAverage ξ h) (𝓝[>] (0 : ℝ)) (𝓝 (h ξ * d)) := by
  let ω := (Chapter01.realUnitBallVolume (n : ℝ)).toReal
  have hω : 0 < ω := ENNReal.toReal_pos (Chapter01.realUnitBallVolume_pos (Nat.cast_nonneg n)).ne'
    (Chapter01.realUnitBallVolume_ne_top _)
  have hsmall : Tendsto (closedBall ξ) (𝓝[>] (0 : ℝ)) (𝓝[U] ξ).smallSets := by
    rw [hU.nhdsWithin_eq hξ]
    exact (tendsto_closedBall_smallSets ξ).mono_left inf_le_left
  have ho := hh.integral_sub_linear_isLittleO_ae (μ := V.weight) hξ hU.measurableSet hsmall
  have hO : (fun r ↦ V.weight.real (closedBall ξ r)) =O[𝓝[>] (0 : ℝ)] (fun r ↦ ω * r ^ n) := by
    apply isBigO_of_div_tendsto_nhds ?_ d hd
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact fun hz ↦ False.elim ((mul_ne_zero hω.ne' (pow_ne_zero _ (ne_of_gt hr))) hz)
  have herr := (ho.trans_isBigO hO).tendsto_div_nhds_zero
  have hsum := herr.add (hd.const_mul (h ξ))
  simp only [zero_add] at hsum
  apply hsum.congr
  intro r
  change ((∫ x in closedBall ξ r, h x ∂V.weight) - V.weight.real (closedBall ξ r) • h ξ) /
    (ω * r ^ n) + h ξ * (V.weight.real (closedBall ξ r) / (ω * r ^ n)) = _
  simp only [smul_eq_mul, weightedBallAverage, ω]
  ring

theorem HasGeneralizedMeanCurvatureIn.tendsto_weightedBallAverage
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (hU : IsOpen U)
    {h : E → ℝ} (hh : ContinuousOn h U) {Λ : ℝ}
    (hbound : ∀ x ∈ V.carrier ∩ U, ‖H x‖ ≤ Λ) {ξ : E} (hξ : ξ ∈ U) :
    Tendsto (V.weightedBallAverage ξ h) (𝓝[>] (0 : ℝ))
      (𝓝 (h ξ * V.stationaryDensityReal ξ)) :=
  V.tendsto_weightedBallAverage_of_tendsto_density hU hh hξ
    (HasGeneralizedMeanCurvatureIn.tendsto_densityQuotient_real (V := V) hH hbound hU hξ)

/-- The limit `σ↓0` of (5.4), with its actual density factor. -/
theorem HasGeneralizedMeanCurvatureIn.density_mul_le_weightedPotential
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (hU : IsOpen U)
    (hn : 0 < n) {h : E → ℝ} (hh : ContDiffOn ℝ 1 h U)
    (hhnonneg : ∀ x ∈ U, 0 ≤ h x) (ξ : E)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (hbound : ∀ x ∈ V.carrier ∩ U, ‖H x‖ ≤ Λ)
    {ρ : ℝ} (hρ : 0 < ρ) (hball : closedBall ξ ρ ⊆ U) :
    ENNReal.ofReal (h ξ * V.stationaryDensityReal ξ) ≤ ENNReal.ofReal (Real.exp (Λ * ρ)) *
      (ENNReal.ofReal (V.weightedBallAverage ξ h ρ) +
        ENNReal.ofReal (1 / ((n : ℝ) * (Chapter01.realUnitBallVolume (n : ℝ)).toReal)) *
          V.radialWeightedPotential ξ (fun x ↦ ‖V.tangentialGradient h x‖) ρ) := by
  have hξ := hball (mem_closedBall_self hρ.le)
  apply le_of_tendsto (ENNReal.tendsto_ofReal
    (HasGeneralizedMeanCurvatureIn.tendsto_weightedBallAverage (V := V) hH hU hh.continuousOn hbound hξ))
  filter_upwards [Ioc_mem_nhdsGT hρ] with σ hσ
  exact HasGeneralizedMeanCurvatureIn.weightedBall_le_potential_of_bounded
    (V := V) hH hU hn hh hhnonneg ξ hΛ hbound hσ.1 hσ.2 hball

/-- The pointwise potential bound printed before (5.6), conditional on
the still-separate geometric lower-density statement at the centre. -/
theorem HasGeneralizedMeanCurvatureIn.value_le_weightedPotential_of_one_le_density
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (hU : IsOpen U)
    (hn : 0 < n) {h : E → ℝ} (hh : ContDiffOn ℝ 1 h U)
    (hhnonneg : ∀ x ∈ U, 0 ≤ h x) (ξ : E)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (hbound : ∀ x ∈ V.carrier ∩ U, ‖H x‖ ≤ Λ)
    {ρ : ℝ} (hρ : 0 < ρ) (hball : closedBall ξ ρ ⊆ U)
    (hd : 1 ≤ V.stationaryDensityReal ξ) :
    ENNReal.ofReal (h ξ) ≤ ENNReal.ofReal (Real.exp (Λ * ρ)) *
      (ENNReal.ofReal (V.weightedBallAverage ξ h ρ) +
        ENNReal.ofReal (1 / ((n : ℝ) * (Chapter01.realUnitBallVolume (n : ℝ)).toReal)) *
          V.radialWeightedPotential ξ (fun x ↦ ‖V.tangentialGradient h x‖) ρ) := by
  have hξ := hball (mem_closedBall_self hρ.le)
  have hle : h ξ ≤ h ξ * V.stationaryDensityReal ξ := by
    nlinarith [hhnonneg ξ hξ]
  exact (ENNReal.ofReal_le_ofReal hle).trans
    (HasGeneralizedMeanCurvatureIn.density_mul_le_weightedPotential
      (V := V) hH hU hn hh hhnonneg ξ hΛ hbound hρ hball)

end RectifiableVarifold

end

end Poincare.SimonGMT.Chapter04
