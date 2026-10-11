module

public import Poincare.SimonGMT.Chapter02.AreaWeighted

public section

/-!
# Simon GMT, Chapter 2, §3: weighted linear area formula

This file proves the weighted form of Simon's linear area formula in arbitrary
codimension.  It is the constant-derivative model for the nonlinear area
formula: an injective linear map transports its domain-dimensional Euclidean
Hausdorff measure to the restriction of ambient Hausdorff measure to its range,
after multiplication by its metric Jacobian.
-/

open Function MeasureTheory Module Set
open scoped ENNReal

namespace Poincare.SimonGMT.Chapter02

noncomputable section

/-- An injective linear map, supplied at the source with its metric-Jacobian
multiple of Euclidean Hausdorff measure, is measure preserving onto its range.
This is the measure-level form of Simon (3.1). -/
theorem measurePreserving_linearMap_normDet_smul
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F]
    (L : E →ₗ[ℝ] F) (hL : Injective L) :
    MeasurePreserving L
      (ENNReal.ofReal L.normDet • μHE[finrank ℝ E])
      (μHE[finrank ℝ E].restrict (range L)) := by
  have hker : L.ker = ⊥ := LinearMap.ker_eq_bot.mpr hL
  have hemb : MeasurableEmbedding L :=
    (LinearMap.isClosedEmbedding_of_injective hker).measurableEmbedding
  refine ⟨hemb.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply hemb.measurable hs, Measure.smul_apply,
    Measure.restrict_apply hs]
  simp only [smul_eq_mul]
  rw [← L.euclideanHausdorffMeasure_image (L ⁻¹' s)]
  exact congrArg _ Set.image_preimage_eq_inter_range

/-- Weighted arbitrary-codimension linear area formula.  Unlike the
equal-dimensional nonlinear specialization, the target can have larger
dimension than the source; the measure on the image uses the source dimension.
-/
theorem weighted_linear_area_formula
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F]
    (L : E →ₗ[ℝ] F) (hL : Injective L) {A : Set E} (hA : MeasurableSet A)
    (g : F → ℝ≥0∞) :
    ∫⁻ y in L '' A, g y ∂μHE[finrank ℝ E] =
      ENNReal.ofReal L.normDet * ∫⁻ x in A, g (L x) ∂μHE[finrank ℝ E] := by
  let c : ℝ≥0∞ := ENNReal.ofReal L.normDet
  let μE : Measure E := μHE[finrank ℝ E]
  let μF : Measure F := μHE[finrank ℝ E]
  have hemb : MeasurableEmbedding L :=
    (LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hL)).measurableEmbedding
  have hpres : MeasurePreserving L (c • μE) (μF.restrict (range L)) := by
    simpa [c, μE, μF] using measurePreserving_linearMap_normDet_smul L hL
  have hLA : MeasurableSet (L '' A) := hemb.measurableSet_image' hA
  calc
    ∫⁻ y in L '' A, g y ∂μF = ∫⁻ y in L '' A, g y ∂(μF.restrict (range L)) := by
      rw [Measure.restrict_restrict hLA, inter_eq_left.2 (image_subset_range L A)]
    _ = ∫⁻ x in A, g (L x) ∂(c • μE) :=
      (hpres.setLIntegral_comp_emb hemb g A).symm
    _ = c * ∫⁻ x in A, g (L x) ∂μE := by
      simp [smul_eq_mul]
    _ = ENNReal.ofReal L.normDet *
        ∫⁻ x in A, g (L x) ∂μHE[finrank ℝ E] := by
      rfl

end

end Poincare.SimonGMT.Chapter02
