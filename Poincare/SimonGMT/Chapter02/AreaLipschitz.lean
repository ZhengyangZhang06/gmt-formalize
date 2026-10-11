module

public import Poincare.SimonGMT.Chapter02.AreaCritical

@[expose] public section

/-!
# Area transport for Lipschitz maps without rank restrictions

Critical images and nondifferentiability images are null. Removing them
reduces injective Lipschitz area transport to the regular theorem. The
normalization of Simon's literal Hausdorff measure remains explicit.
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

/-- Actual differentiability points with full source rank. -/
def areaRegularSet (f : E → F) : Set E :=
  {x | DifferentiableAt ℝ f x ∧ Injective (fderiv ℝ f x)}

theorem measurableSet_areaRegularSet (f : E → F) : MeasurableSet (areaRegularSet f) := by
  have he : areaRegularSet f = {x | DifferentiableAt ℝ f x} ∩
      {x | areaJacobianAt f x = 0}ᶜ := by
    ext x
    simp [areaRegularSet, areaJacobianAt_eq_zero_iff_not_injective]
  rw [he]
  exact (measurableSet_of_differentiableAt ℝ f).inter
    (measurableSet_eq_fun (measurable_areaJacobianAt f) measurable_const).compl

/-- Rademacher's exceptional set has null image under the Lipschitz map,
also in higher codimension. -/
theorem area_image_nondifferentiable_eq_zero {f : E → F} {K : ℝ≥0}
    (hL : LipschitzWith K f) :
    μHE[finrank ℝ E] (f '' {x | ¬ DifferentiableAt ℝ f x}) = 0 := by
  have hz : (μHE[finrank ℝ E] : Measure E) {x | ¬ DifferentiableAt ℝ f x} = 0 := by
    rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
    exact ae_iff.mp (hL.ae_differentiableAt (μ := volume))
  have hle :=
    euclideanHausdorffMeasure_image_le_of_lipschitzOn (finrank ℝ E)
      (hL.lipschitzOnWith (s := {x | ¬ DifferentiableAt ℝ f x}))
  rw [hz, mul_zero] at hle
  exact le_antisymm hle bot_le

/-- Every nonregular source point belongs either to the null
nondifferentiability image or to the proved null critical image. -/
theorem area_image_compl_regularSet_eq_zero {f : E → F} {K : ℝ≥0}
    (hL : LipschitzWith K f) (s : Set E) :
    μHE[finrank ℝ E] (f '' (s \ areaRegularSet f)) = 0 := by
  apply measure_mono_null _ (measure_union_null
    (area_image_nondifferentiable_eq_zero hL) (area_image_criticalSet_eq_zero f))
  rintro _ ⟨x, hx, rfl⟩
  by_cases hd : DifferentiableAt ℝ f x
  · exact Or.inr ⟨x, ⟨hd, fun hi ↦ hx.2 ⟨hd, hi⟩⟩, rfl⟩
  · exact Or.inl ⟨x, hd, rfl⟩

theorem area_image_ae_eq_image_regularSet {f : E → F} {K : ℝ≥0}
    (hL : LipschitzWith K f) (s : Set E) :
    f '' s =ᵐ[μHE[finrank ℝ E]] f '' (s ∩ areaRegularSet f) := by
  apply ae_eq_set.mpr
  constructor
  · apply measure_mono_null _ (area_image_compl_regularSet_eq_zero hL s)
    rintro _ ⟨⟨x, hx, rfl⟩, hn⟩
    exact ⟨x, ⟨hx, fun hr ↦ hn ⟨x, ⟨hx, hr⟩, rfl⟩⟩, rfl⟩
  · rw [sdiff_eq_empty.mpr (image_mono inter_subset_left), measure_empty]

/-- Restricting any Jacobian-weighted nonnegative integral to the regular
set changes nothing. The weight itself need not be measurable. -/
theorem lintegral_areaJacobian_inter_regularSet {f : E → F} {K : ℝ≥0}
    (hL : LipschitzWith K f) {s : Set E} (hs : MeasurableSet s) (w : E → ℝ≥0∞) :
    (∫⁻ x in s ∩ areaRegularSet f, ENNReal.ofReal (areaJacobianAt f x) * w x ∂volume) =
      ∫⁻ x in s, ENNReal.ofReal (areaJacobianAt f x) * w x ∂volume := by
  rw [← lintegral_indicator (hs.inter (measurableSet_areaRegularSet f)),
    ← lintegral_indicator hs]
  apply lintegral_congr_ae
  filter_upwards [hL.ae_differentiableAt (μ := volume)] with x hd
  by_cases hx : x ∈ s
  · by_cases hr : x ∈ areaRegularSet f
    · simp only [indicator_of_mem hx,
        indicator_of_mem (show x ∈ s ∩ areaRegularSet f from ⟨hx, hr⟩)]
    · have hz : areaJacobianAt f x = 0 :=
        (areaJacobianAt_eq_zero_iff_not_injective f x).mpr (fun hi ↦ hr ⟨hd, hi⟩)
      simp [hx, hr, hz]
  · simp [hx]

/-- Weighted area transport for an injective Lipschitz map, including
critical points and the Rademacher exceptional set. No rank hypothesis
and no everywhere differentiability assumption remain. -/
theorem weighted_area_formula_lipschitz_injOn {f : E → F} {K : ℝ≥0}
    (hL : LipschitzWith K f) {s : Set E} (hs : MeasurableSet s)
    (hi : InjOn f s) (g : F → ℝ≥0∞) :
    (∫⁻ y in f '' s, g y ∂μHE[finrank ℝ E]) =
      ∫⁻ x in s, ENNReal.ofReal (areaJacobianAt f x) * g (f x) ∂volume := by
  calc
    _ = ∫⁻ y in f '' (s ∩ areaRegularSet f), g y ∂μHE[finrank ℝ E] :=
      setLIntegral_congr (area_image_ae_eq_image_regularSet hL s)
    _ = ∫⁻ x in s ∩ areaRegularSet f,
        ENNReal.ofReal (areaJacobianAt f x) * g (f x) ∂volume :=
      weighted_area_formula_volume_of_injective_derivative
        (hs.inter (measurableSet_areaRegularSet f)) (fun _ hx ↦ hx.2.1)
        (fun _ hx ↦ hx.2.2) (hi.mono inter_subset_left) g
    _ = _ := lintegral_areaJacobian_inter_regularSet hL hs _

/-- The full injective Lipschitz area equality for a Borel source set. -/
theorem injective_area_formula_lipschitz {f : E → F} {K : ℝ≥0}
    (hL : LipschitzWith K f) {s : Set E} (hs : MeasurableSet s) (hi : InjOn f s) :
    μHE[finrank ℝ E] (f '' s) =
      ∫⁻ x in s, ENNReal.ofReal (areaJacobianAt f x) ∂volume := by
  simpa only [setLIntegral_one, mul_one] using
    weighted_area_formula_lipschitz_injOn hL hs hi (fun _ ↦ 1)

/-- Simon's literal normalization on both sides of the Lipschitz area
formula, without assuming that its conversion factor is one. -/
theorem injective_area_formula_lipschitz_simon {f : E → F} {K : ℝ≥0}
    (hL : LipschitzWith K f) {s : Set E} (hs : MeasurableSet s) (hi : InjOn f s) :
    Chapter01.simonHausdorffMeasureReal (finrank ℝ E : ℝ) (f '' s) =
      ∫⁻ x in s, ENNReal.ofReal (areaJacobianAt f x)
        ∂Chapter01.simonHausdorffMeasureReal (finrank ℝ E : ℝ) := by
  rw [simonHausdorffMeasureReal_nat_eq_smul_euclideanHausdorffMeasure,
    simonHausdorffMeasureReal_source_eq_smul_volume, Measure.smul_apply,
    Measure.restrict_smul, lintegral_smul_measure,
    injective_area_formula_lipschitz hL hs hi]

end
end Poincare.SimonGMT.Chapter02
