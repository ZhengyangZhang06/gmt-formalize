module

public import Poincare.SimonGMT.Chapter02.AreaNoninjective

@[expose] public section

/-!
# Completed-measurable domains and weights in the area formula

Lipschitz null-image control transports changes on source null sets to
changes on target Hausdorff-null sets. Thus Borel representatives can be
used without narrowing Simon's Lebesgue-measurable domain or weight.
-/

open Function MeasureTheory Module Set Filter
open scoped ENNReal NNReal Topology

namespace Poincare.SimonGMT.Chapter02
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F]

theorem area_image_null_of_lipschitzOn {f : E → F} {K : ℝ≥0} {s : Set E}
    (hL : LipschitzOnWith K f s) (hz : volume s = 0) :
    μHE[finrank ℝ E] (f '' s) = 0 := by
  have h := euclideanHausdorffMeasure_image_le_of_lipschitzOn (finrank ℝ E) hL
  rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume, hz, mul_zero] at h
  exact le_antisymm h bot_le

theorem area_image_ae_eq_of_source_ae {f : E → F} {K : ℝ≥0}
    (hL : LipschitzWith K f) {s t : Set E} (hst : s =ᵐ[volume] t) :
    f '' s =ᵐ[μHE[finrank ℝ E]] f '' t := by
  apply ae_eq_set.mpr
  constructor
  · apply measure_mono_null _
      (area_image_null_of_lipschitzOn hL.lipschitzOnWith (ae_eq_set.mp hst).1)
    rintro _ ⟨⟨x, hx, rfl⟩, hn⟩
    exact ⟨x, ⟨hx, fun ht ↦ hn ⟨x, ht, rfl⟩⟩, rfl⟩
  · apply measure_mono_null _
      (area_image_null_of_lipschitzOn hL.lipschitzOnWith (ae_eq_set.mp hst).2)
    rintro _ ⟨⟨x, hx, rfl⟩, hn⟩
    exact ⟨x, ⟨hx, fun hs ↦ hn ⟨x, hs, rfl⟩⟩, rfl⟩

theorem weightedAreaFiberSum_ae_eq_of_set_ae {f : E → F} {K : ℝ≥0}
    (hL : LipschitzWith K f) {s t : Set E} (hst : s =ᵐ[volume] t) (w : E → ℝ≥0∞) :
    weightedAreaFiberSum s f w =ᵐ[μHE[finrank ℝ E]] weightedAreaFiberSum t f w := by
  have h₁ := measure_eq_zero_iff_ae_notMem.mp
    (area_image_null_of_lipschitzOn hL.lipschitzOnWith (ae_eq_set.mp hst).1)
  have h₂ := measure_eq_zero_iff_ae_notMem.mp
    (area_image_null_of_lipschitzOn hL.lipschitzOnWith (ae_eq_set.mp hst).2)
  filter_upwards [h₁, h₂] with y hy₁ hy₂
  apply weightedAreaFiberSum_congr_fiber
  intro x
  constructor
  · rintro ⟨hx, hxy⟩
    exact ⟨by_contra fun hn ↦ hy₁ ⟨x, ⟨hx, hn⟩, hxy⟩, hxy⟩
  · rintro ⟨hx, hxy⟩
    exact ⟨by_contra fun hn ↦ hy₂ ⟨x, ⟨hx, hn⟩, hxy⟩, hxy⟩

theorem weightedAreaFiberSum_ae_eq_of_weight_ae {f : E → F} {K : ℝ≥0}
    (hL : LipschitzWith K f) {s : Set E} (hs : NullMeasurableSet s volume)
    {w v : E → ℝ≥0∞} (hwv : w =ᵐ[volume.restrict s] v) :
    weightedAreaFiberSum s f w =ᵐ[μHE[finrank ℝ E]] weightedAreaFiberSum s f v := by
  have hz : volume ({x | w x ≠ v x} ∩ s) = 0 := by
    rw [← Measure.restrict_apply₀' hs]
    exact ae_iff.mp hwv
  have him := measure_eq_zero_iff_ae_notMem.mp
    (area_image_null_of_lipschitzOn hL.lipschitzOnWith hz)
  filter_upwards [him] with y hy
  unfold weightedAreaFiberSum
  apply tsum_congr
  intro x
  by_contra hne
  exact hy ⟨x.1, ⟨hne, x.2.1⟩, x.2.2⟩

/-- The weighted formula for Lebesgue-measurable domains and weights,
not merely Borel domains or globally Borel source weights. -/
theorem weighted_area_formula_lipschitz_fiberSum_nullMeasurable
    {f : E → F} {K : ℝ≥0} (hL : LipschitzWith K f)
    {s : Set E} (hs : NullMeasurableSet s volume)
    {w : E → ℝ≥0∞} (hw : AEMeasurable w (volume.restrict s)) :
    (∫⁻ y, weightedAreaFiberSum s f w y ∂μHE[finrank ℝ E]) =
      ∫⁻ x in s, ENNReal.ofReal (areaJacobianAt f x) * w x ∂volume := by
  obtain ⟨t, hts, ht, htae⟩ := hs.exists_measurable_subset_ae_eq
  calc
    _ = ∫⁻ y, weightedAreaFiberSum s f (hw.mk w) y ∂μHE[finrank ℝ E] :=
      lintegral_congr_ae (weightedAreaFiberSum_ae_eq_of_weight_ae hL hs hw.ae_eq_mk)
    _ = ∫⁻ y, weightedAreaFiberSum t f (hw.mk w) y ∂μHE[finrank ℝ E] :=
      lintegral_congr_ae (weightedAreaFiberSum_ae_eq_of_set_ae hL htae.symm _)
    _ = ∫⁻ x in t, ENNReal.ofReal (areaJacobianAt f x) * hw.mk w x ∂volume :=
      weighted_area_formula_lipschitz_fiberSum hL ht hw.measurable_mk
    _ = ∫⁻ x in s, ENNReal.ofReal (areaJacobianAt f x) * hw.mk w x ∂volume :=
      setLIntegral_congr htae
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [hw.ae_eq_mk] with x hx
      rw [hx]

theorem aemeasurable_weightedAreaFiberSum_lipschitz_nullMeasurable
    {f : E → F} {K : ℝ≥0} (hL : LipschitzWith K f)
    {s : Set E} (hs : NullMeasurableSet s volume)
    {w : E → ℝ≥0∞} (hw : AEMeasurable w (volume.restrict s)) :
    AEMeasurable (weightedAreaFiberSum s f w) μHE[finrank ℝ E] := by
  obtain ⟨t, _, ht, htae⟩ := hs.exists_measurable_subset_ae_eq
  have hm := aemeasurable_weightedAreaFiberSum_lipschitz hL ht hw.measurable_mk
  exact hm.congr ((weightedAreaFiberSum_ae_eq_of_weight_ae hL hs hw.ae_eq_mk).trans
    (weightedAreaFiberSum_ae_eq_of_set_ae hL htae.symm _)).symm

theorem injective_area_formula_lipschitz_nullMeasurable
    {f : E → F} {K : ℝ≥0} (hL : LipschitzWith K f)
    {s : Set E} (hs : NullMeasurableSet s volume) (hi : InjOn f s) :
    μHE[finrank ℝ E] (f '' s) =
      ∫⁻ x in s, ENNReal.ofReal (areaJacobianAt f x) ∂volume := by
  obtain ⟨t, hts, ht, htae⟩ := hs.exists_measurable_subset_ae_eq
  calc
    _ = μHE[finrank ℝ E] (f '' t) :=
      measure_congr (area_image_ae_eq_of_source_ae hL htae.symm)
    _ = ∫⁻ x in t, ENNReal.ofReal (areaJacobianAt f x) ∂volume :=
      injective_area_formula_lipschitz hL ht (hi.mono hts)
    _ = _ := setLIntegral_congr htae

/-- Completed-measurable Simon (3.5), with his normalization retained. -/
theorem weighted_area_formula_lipschitz_fiberSum_simon_nullMeasurable
    {f : E → F} {K : ℝ≥0} (hL : LipschitzWith K f)
    {s : Set E} (hs : NullMeasurableSet s volume)
    {w : E → ℝ≥0∞} (hw : AEMeasurable w (volume.restrict s)) :
    (∫⁻ y, weightedAreaFiberSum s f w y
      ∂Chapter01.simonHausdorffMeasureReal (finrank ℝ E : ℝ)) =
      ∫⁻ x in s, ENNReal.ofReal (areaJacobianAt f x) * w x
        ∂Chapter01.simonHausdorffMeasureReal (finrank ℝ E : ℝ) := by
  rw [simonHausdorffMeasureReal_nat_eq_smul_euclideanHausdorffMeasure,
    simonHausdorffMeasureReal_source_eq_smul_volume, Measure.restrict_smul,
    lintegral_smul_measure, lintegral_smul_measure,
    weighted_area_formula_lipschitz_fiberSum_nullMeasurable hL hs hw]

end
end Poincare.SimonGMT.Chapter02
