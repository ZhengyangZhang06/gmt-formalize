module

public import Poincare.SimonGMT.Chapter08.TangentRescaling
public import Poincare.SimonGMT.Chapter08.ConstancyDomainCounterexample
import all Poincare.SimonGMT.Chapter03.Rectifiable

@[expose] public section

/-!
# The inverse-dilation sign in the printed equation (8.5.3)

The book defines η_{x,λ}(y) = λ⁻¹(y−x). Consequently its displayed
λ⁻ⁿ μ_C(η_{0,λ}(A)) = μ_C(A), with a direct image of A, has the wrong
power of λ. The stationary multiplicity-one line is an actual tangent
varifold and refutes that formula. Its corrected λⁿ identity is proved
for every set, not only measurable sets.

Source: `Simon-gmt new.pdf`, printed pp. 71 and 215.
-/

open Set Filter MeasureTheory Function Metric
open scoped Topology ENNReal Pointwise

namespace Poincare.SimonGMT.Chapter08.TangentScalingCounterexample
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
open ConstancyDomainCounterexample

/-- Multiplicity-one length on the whole line, with its actual tangent. -/
def fullLine : Varifold 1 1 (univ : Set (Euclidean 1)) where
  isOpen_domain := isOpen_univ
  measure := volume.map bundle
  supported := by simp
  finite_on_compact := by
    intro K hK _
    rw [measurableEmbedding_bundle.map_apply]
    have he : bundle ⁻¹' (K ×ˢ (univ : Set (Grassmannian 1 1))) =
        coordinateEquiv ⁻¹' K := by ext t; simp [bundle]
    rw [he]
    exact (coordinateEquiv.toHomeomorph.isCompact_preimage.mpr hK).measure_ne_top

theorem weight_fullLine : fullLine.weight = volume := by
  rw [Varifold.weight, fullLine,
    Measure.map_map measurable_fst measurableEmbedding_bundle.measurable]
  change volume.map coordinateEquiv = volume
  exact coordinateEquiv.measurePreserving.map_eq

/-- Compactly supported scalar derivatives integrate to zero. Thus
stationarity is checked for all genuine admissible vector fields. -/
theorem stationary_fullLine : fullLine.Stationary := by
  intro X
  let g : ℝ → ℝ := fun t ↦ coordinateEquiv.symm (X (coordinateEquiv t))
  have hg : ContDiff ℝ 1 g :=
    coordinateEquiv.symm.toContinuousLinearEquiv.contDiff.comp
      (X.contDiff.comp coordinateEquiv.toContinuousLinearEquiv.contDiff)
  have hgc : HasCompactSupport g :=
    (X.compactSupport.comp_homeomorph coordinateEquiv.toHomeomorph).comp_left
      coordinateEquiv.symm.map_zero
  have hgi : Integrable (deriv g) :=
    (hg.continuous_deriv le_rfl).integrable_of_hasCompactSupport hgc.deriv
  rw [Varifold.firstVariation, fullLine, measurableEmbedding_bundle.integral_map]
  change (∫ t, Varifold.tangentialDivergence X (coordinateEquiv t) fullPlane) = 0
  simp_rw [tangentialDivergence_eq_deriv X.contDiff]
  change (∫ t, deriv g t) = 0
  rw [← integral_add_compl measurableSet_Iic hgi, compl_Iic,
    hgc.integral_Iic_deriv_eq hg (0 : ℝ), hgc.integral_Ioi_deriv_eq hg 0, add_neg_cancel]

/-- The line is unchanged by every genuine varifold dilation. -/
theorem blowUpMeasure_fullLine {r : ℝ} (hr : 0 < r) :
    fullLine.blowUpMeasure 0 r = fullLine.measure := by
  have he : Varifold.blowUpBundleMap (n := 1) (0 : Euclidean 1) r ∘ bundle =
      bundle ∘ (fun t : ℝ ↦ r⁻¹ • t) := by
    funext t
    apply Prod.ext
    · change r⁻¹ • (coordinateEquiv t - 0) = coordinateEquiv (r⁻¹ • t)
      rw [map_smul, sub_zero]
    · rfl
  rw [Varifold.blowUpMeasure, fullLine,
    Measure.map_map (Varifold.continuous_blowUpBundleMap 0 r).measurable
      measurableEmbedding_bundle.measurable, he,
    ← Measure.map_map measurableEmbedding_bundle.measurable (by fun_prop),
    Measure.map_addHaar_smul volume (inv_ne_zero hr.ne'),
    Measure.map_smul _ measurableEmbedding_bundle.measurable.aemeasurable, smul_smul]
  simp only [Module.finrank_self, pow_one, inv_inv, abs_of_pos hr]
  rw [← ENNReal.ofReal_mul (inv_pos.mpr hr).le, inv_mul_cancel₀ hr.ne',
    ENNReal.ofReal_one, one_smul]

theorem density_fullLine (x : Euclidean 1) :
    Chapter01.HasDimensionalDensityAt fullLine.weight.toOuterMeasure (1 : ℝ) univ x 1 := by
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  rw [Chapter01.dimensionalDensityQuotient, weight_fullLine, univ_inter]
  change 1 = volume (closedBall x r) /
    (Chapter01.realUnitBallVolume 1 * ENNReal.ofReal r ^ (1 : ℝ))
  rw [Chapter01.volume_closedBall_eq_densityNormalization 1 x hr]
  simp only [Nat.cast_one, ENNReal.rpow_one]
  symm
  apply ENNReal.div_self
  · exact mul_ne_zero (Chapter01.realUnitBallVolume_pos (by norm_num : (0 : ℝ) ≤ 1)).ne'
      (ENNReal.ofReal_pos.mpr hr).ne'
  · exact ENNReal.mul_ne_top (Chapter01.realUnitBallVolume_ne_top _) ENNReal.ofReal_ne_top

/-- The first-variation part of (5.1) holds for the constructed measure,
not just for a formal zero-variation symbol. -/
theorem firstVariationRieszMeasure_fullLine_closedBall (x : Euclidean 1) (r : ℝ) :
    fullLine.firstVariationRieszMeasure stationary_fullLine.hasLocallyBoundedFirstVariation
      (closedBall x r) = 0 := by
  apply le_antisymm ?_ bot_le
  apply (measure_mono (closedBall_subset_ball (by linarith : r < r + 1))).trans
  rw [fullLine.firstVariationRieszMeasure_eq_norm
    stationary_fullLine.hasLocallyBoundedFirstVariation (ball x (r + 1)) isOpen_ball
    ⟨(isCompact_closedBall x (r + 1)).of_isClosed_subset isClosed_closure
      (closure_minimal ball_subset_closedBall isClosed_closedBall), subset_univ _⟩,
    stationary_fullLine.firstVariationNormOn_eq_zero]
  exact le_rfl

theorem isTangentPoint_fullLine (x : Euclidean 1) : fullLine.IsTangentPoint x 1 where
  mem_domain := mem_univ _
  locallyBoundedFirstVariation := stationary_fullLine.hasLocallyBoundedFirstVariation
  density_ne_zero := one_ne_zero
  density_ne_top := ENNReal.one_ne_top
  density := by simpa only [Nat.cast_one] using density_fullLine x
  variation_decay := by
    simp_rw [firstVariationRieszMeasure_fullLine_closedBall, mul_zero]
    exact tendsto_const_nhds

/-- The correct direct-image homogeneity, with the source's inverse
dilation convention, holds for every set. -/
theorem corrected_image_homogeneity_fullLine {r : ℝ} (hr : 0 < r)
    (A : Set (Euclidean 1)) :
    ENNReal.ofReal (r ^ 1) * fullLine.weight (Chapter03.blowUpMap 0 r '' A) =
      fullLine.weight A := by
  rw [weight_fullLine]
  have he : Chapter03.blowUpMap (0 : Euclidean 1) r '' A = r⁻¹ • A := by
    simp only [Chapter03.blowUpMap, sub_zero]
    rfl
  rw [he, Measure.addHaar_smul_of_nonneg volume (inv_pos.mpr hr).le]
  have hdim : Module.finrank ℝ (Euclidean 1) = 1 := by simp
  simp only [hdim, pow_one]
  rw [← mul_assoc, ← ENNReal.ofReal_mul hr.le, mul_inv_cancel₀ hr.ne',
    ENNReal.ofReal_one, one_mul]

/-- A concrete unit-length test set. -/
def unitSegment : Set (Euclidean 1) := coordinateEquiv '' Icc (0 : ℝ) 1

theorem weight_unitSegment : fullLine.weight unitSegment = 1 := by
  rw [weight_fullLine, ← coordinateEquiv.measurePreserving.map_eq]
  change (volume.map coordinateEquiv.toHomeomorph) unitSegment = 1
  rw [coordinateEquiv.toHomeomorph.measurableEmbedding.map_apply]
  simp [unitSegment, coordinateEquiv.injective.preimage_image]

/-- The literal (5.3) already fails at scale two on the stationary line
that satisfies (5.1) and equals all of its own bundle blow-ups. -/
theorem printed_inverse_scaling_fails :
    ENNReal.ofReal ((2 : ℝ)⁻¹ ^ 1) *
        fullLine.weight (Chapter03.blowUpMap 0 2 '' unitSegment) ≠
      fullLine.weight unitSegment := by
  have hi : fullLine.weight (Chapter03.blowUpMap 0 2 '' unitSegment) = (2 : ℝ≥0∞)⁻¹ := by
    rw [weight_fullLine]
    have he : Chapter03.blowUpMap (0 : Euclidean 1) 2 '' unitSegment =
        (2 : ℝ)⁻¹ • unitSegment := by
      simp only [Chapter03.blowUpMap, sub_zero]
      rfl
    rw [he, Measure.addHaar_smul_of_nonneg volume (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
    rw [← weight_fullLine, weight_unitSegment]
    norm_num [ENNReal.ofReal_div_of_pos]
  rw [hi, weight_unitSegment]
  intro h
  have ht := congrArg ENNReal.toReal h
  norm_num at ht

end
end Poincare.SimonGMT.Chapter08.TangentScalingCounterexample
