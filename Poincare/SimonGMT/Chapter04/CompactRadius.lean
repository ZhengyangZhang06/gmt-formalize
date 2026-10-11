module

public import Poincare.SimonGMT.Chapter04.CompactWeighted

@[expose] public section

/-!
# All-radius weighted inequalities for compactly supported multipliers

The curvature equation is still assumed only on the original open domain.
Compact support supplies admissibility for every radius and integrability
of all energy terms before the scale inequality is integrated.
-/

open Filter Function Metric Set MeasureTheory
open scoped ENNReal Topology

namespace Poincare.SimonGMT.Chapter04

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {n : ℕ}

namespace RectifiableVarifold

variable (V : RectifiableVarifold (E := E) n)

theorem HasGeneralizedMeanCurvatureIn.weightedCutoff_radius_inequality_compact
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (hU : IsOpen U)
    {h : E → ℝ} (hh : ContDiffOn ℝ 1 h U) (hc : HasCompactSupport h) (hs : tsupport h ⊆ U)
    (hhnonneg : ∀ x, 0 ≤ h x) (ξ : E)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφanti : Antitone φ)
    (hφrange : ∀ z, φ z ∈ Icc 0 1) {A σ ρ : ℝ} (hA : 0 < A)
    (hcutoff : ∀ z, A ^ 2 ≤ z → φ z = 0) (hσ : 0 < σ) (hσρ : σ ≤ ρ) :
    V.weightedCutoffMass ξ h φ σ / σ ^ n ≤
      V.weightedCutoffMass ξ h φ ρ / ρ ^ n +
        ∫ t in σ..ρ, (∫ x, scaledRadialCutoff ξ φ t x *
          (‖x - ξ‖ * (‖V.tangentialGradient h x‖ + h x * ‖H x‖)) ∂V.weight) / t ^ (n + 1) := by
  have hh' := contDiff_of_tsupport_subset hU hh hs
  let q := fun x ↦ ‖x - ξ‖ * (‖V.tangentialGradient h x‖ + h x * ‖H x‖)
  have hq : Integrable q V.weight :=
    HasGeneralizedMeanCurvatureIn.integrable_radialWeightedEnergy_of_hasCompactSupport
      (V := V) hH hU hh hc hs ξ
  let e := fun t ↦ (∫ x, scaledRadialCutoff ξ φ t x * q x ∂V.weight) / t ^ (n + 1)
  have he : ContinuousOn e (Icc σ ρ) :=
    (V.continuousOn_integral_scaledRadialCutoff_mul ξ hφ.continuous hφrange hA hcutoff hσ hq.restrict).div
      (continuousOn_id.pow _) (fun t ht ↦ pow_ne_zero _ (hσ.trans_le ht.1).ne')
  let f := fun t ↦ V.weightedCutoffMass ξ h φ t / t ^ n
  have hd : ∀ t ∈ Icc σ ρ, DifferentiableAt ℝ f t := by
    intro t ht
    exact (HasGeneralizedMeanCurvatureIn.hasDerivAt_normalizedWeightedCutoffMass_compact
      (V := V) hH hU hh hc hs ξ hφ hA hcutoff (hσ.trans_le ht.1)).differentiableAt
  have hle : ∀ t ∈ Icc σ ρ, -e t ≤ deriv f t := by
    intro t ht
    have ht0 := hσ.trans_le ht.1
    have hi : Integrable (fun x ↦ scaledRadialCutoff ξ φ t x * q x) V.weight := by
      apply hq.bdd_mul (c := 1)
        ((hφ.continuous.comp (by fun_prop : Continuous (fun x : E ↦ ‖x - ξ‖ ^ 2 / t ^ 2))).aestronglyMeasurable)
      filter_upwards with x
      rw [Function.comp_apply, Real.norm_of_nonneg (hφrange _).1]
      exact (hφrange _).2
    have hp := (HasGeneralizedMeanCurvatureIn.weightedCutoffMass_deriv_identity_compact
      (V := V) hH hU hh hc hs ξ hφ hA hcutoff ht0).1
    have hpair : -(∫ x, scaledRadialCutoff ξ φ t x * q x ∂V.weight) ≤
        V.weightedCutoffGradientCurvaturePairing ξ h H φ t := by
      rw [weightedCutoffGradientCurvaturePairing, ← integral_neg]
      apply integral_mono hi.neg hp
      intro x
      have hb := mul_le_mul_of_nonneg_left
        (V.weighted_radialPairing_lower_bound ξ x h H (hhnonneg x)) (hφrange (‖x - ξ‖ ^ 2 / t ^ 2)).1
      dsimp only [q, Pi.neg_apply, scaledRadialCutoff] at *
      nlinarith
    have hJ := (V.weightedCutoff_derivatives isOpen_univ hh'.contDiffOn ξ hφ hA hcutoff ht0
      (subset_univ _)).2.2.2
    have hJ0 : 0 ≤ deriv (V.weightedCutoffNormalMass ξ h φ) t := by
      rw [hJ.deriv]
      exact integral_nonneg (fun x ↦ mul_nonneg (scaledRadialCutoffDeriv_nonneg ξ x hφanti ht0)
        (mul_nonneg (hhnonneg x) (V.radialNormalSq_nonneg ξ x)))
    have hderiv := HasGeneralizedMeanCurvatureIn.hasDerivAt_normalizedWeightedCutoffMass_compact
      (V := V) hH hU hh hc hs ξ hφ hA hcutoff ht0
    change -e t ≤ deriv (fun r ↦ V.weightedCutoffMass ξ h φ r / r ^ n) t
    rw [hderiv.deriv]
    have hpair' := div_le_div_of_nonneg_right hpair (pow_pos ht0 (n + 1)).le
    dsimp only [e]
    rw [neg_div] at hpair'
    exact hpair'.trans (le_add_of_nonneg_left (div_nonneg hJ0 (pow_pos ht0 n).le))
  have hint := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hσρ
    (fun t ht ↦ (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hd t ⟨ht.1.le, ht.2.le⟩).hasDerivAt.hasDerivWithinAt)
    (he.neg.integrableOn_Icc) (fun t ht ↦ hle t ⟨ht.1.le, ht.2.le⟩)
  simp only [Pi.neg_apply, intervalIntegral.integral_neg] at hint
  change -(∫ t in σ..ρ, e t) ≤ f ρ - f σ at hint
  change f σ ≤ f ρ + ∫ t in σ..ρ, e t
  linarith

/-- Compact support globalizes the finite-radius estimate preceding (5.5)
to every pair of positive radii, even when the balls leave `U`. -/
theorem HasGeneralizedMeanCurvatureIn.weightedBall_radius_inequality_compact
    {U : Set E} {H : E → E} (hH : V.HasGeneralizedMeanCurvatureIn U H) (hU : IsOpen U)
    {h : E → ℝ} (hh : ContDiffOn ℝ 1 h U) (hc : HasCompactSupport h) (hs : tsupport h ⊆ U)
    (hhnonneg : ∀ x, 0 ≤ h x) (ξ : E)
    {σ ρ : ℝ} (hσ : 0 < σ) (hσρ : σ ≤ ρ) :
    (∫ x in closedBall ξ σ, h x ∂V.weight) / σ ^ n ≤
      (∫ x in closedBall ξ ρ, h x ∂V.weight) / ρ ^ n +
        ∫ t in σ..ρ, (∫ x in closedBall ξ t,
          ‖x - ξ‖ * (‖V.tangentialGradient h x‖ + h x * ‖H x‖) ∂V.weight) / t ^ (n + 1) := by
  have hh' := contDiff_of_tsupport_subset hU hh hs
  have hhi : Integrable h V.weight := hh'.continuous.integrable_of_hasCompactSupport hc
  have hq := HasGeneralizedMeanCurvatureIn.integrable_radialWeightedEnergy_of_hasCompactSupport
    (V := V) hH hU hh hc hs ξ
  apply le_of_tendsto_of_tendsto
    ((V.tendsto_integral_scaledRadialCutoff_mul_integrable ξ hσ hhi).div_const (σ ^ n))
    (((V.tendsto_integral_scaledRadialCutoff_mul_integrable ξ (hσ.trans_le hσρ) hhi).div_const (ρ ^ n)).add
      (V.tendsto_radiusIntegral_scaledRadialCutoff_integrable ξ hσ hσρ hq))
  filter_upwards [self_mem_nhdsWithin] with ε hε
  change 0 < ε at hε
  exact HasGeneralizedMeanCurvatureIn.weightedCutoff_radius_inequality_compact
    (V := V) hH hU hh hc hs hhnonneg ξ (contDiff_monotonicityCutoff ε)
    (monotonicityCutoff_antitone hε) (monotonicityCutoff_mem_Icc ε)
    (by linarith : 0 < 1 + ε) (monotonicityCutoff_cutoff hε) hσ hσρ

end RectifiableVarifold

end

end Poincare.SimonGMT.Chapter04
