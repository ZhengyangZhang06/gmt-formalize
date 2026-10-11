module

public import Poincare.SimonGMT.Chapter02.AreaBranches

@[expose] public section

/-!
# Noninjective nonlinear area and weighted fiber sums

The regular branches are constructed from differentiability, while all
critical and nondifferentiability images are proved null. The resulting
formula counts genuine source fibers, with arbitrary finite or infinite
multiplicity. The target measure is source-dimensional Hausdorff measure.

Simon's printed (3.4) has `Hᵐ` in the target integral, unlike (3.5); for
`m > n` that cannot be correct. The statements here use `Hⁿ` explicitly.
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

theorem weighted_area_formula_fiberSum_regular_injOn
    {s : Set E} {f : E → F} (hs : MeasurableSet s)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hr : ∀ x ∈ s, Injective (fderiv ℝ f x)) (hi : InjOn f s) (w : E → ℝ≥0∞) :
    (∫⁻ y, weightedAreaFiberSum s f w y ∂μHE[finrank ℝ E]) =
      ∫⁻ x in s, ENNReal.ofReal (areaJacobianAt f x) * w x ∂volume := by
  classical
  have hm : MeasurableSet (f '' s) := hs.image_of_continuousOn_injOn
    (fun x hx ↦ (hf x hx).continuousAt.continuousWithinAt) hi
  have hind : (f '' s).indicator (weightedAreaFiberSum s f w) =
      weightedAreaFiberSum s f w := by
    funext y
    by_cases hy : y ∈ f '' s
    · exact indicator_of_mem hy _
    · simp only [indicator_of_notMem hy, weightedAreaFiberSum_eq_zero_of_not_mem_image hy]
  calc
    _ = ∫⁻ y in f '' s, weightedAreaFiberSum s f w y ∂μHE[finrank ℝ E] := by
      rw [← lintegral_indicator hm, hind]
    _ = ∫⁻ x in s, ENNReal.ofReal (areaJacobianAt f x) *
        weightedAreaFiberSum s f w (f x) ∂volume :=
      weighted_area_formula_volume_of_injective_derivative hs hf hr hi _
    _ = _ := setLIntegral_congr_fun hs (fun x hx ↦ by
      rw [weightedAreaFiberSum_eq_of_injOn hi w hx])

/-- Borel measurability of the fiber sum on the full regular set follows
from the constructed countable Borel injective partition. -/
theorem measurable_weightedAreaFiberSum_of_regular
    {s : Set E} {f : E → F} (hs : MeasurableSet s)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hr : ∀ x ∈ s, Injective (fderiv ℝ f x))
    {w : E → ℝ≥0∞} (hw : Measurable w) : Measurable (weightedAreaFiberSum s f w) := by
  obtain ⟨t, ht, hd, hcover, hi⟩ := exists_injective_partition_of_regular hs hf hr
  have hsub (i : ℕ) : t i ⊆ s := hcover ▸ subset_iUnion t i
  have hm (i : ℕ) : Measurable (weightedAreaFiberSum (t i) f w) :=
    measurable_weightedAreaFiberSum_of_injOn (ht i)
      (fun x hx ↦ (hf x (hsub i hx)).continuousAt.continuousWithinAt) (hi i) hw
  have he : weightedAreaFiberSum s f w = fun y ↦ ∑' i, weightedAreaFiberSum (t i) f w y := by
    rw [← hcover]
    funext y
    exact weightedAreaFiberSum_iUnion t hd f w y
  rw [he]
  exact Measurable.tsum hm

/-- The noninjective weighted area equality on regular differentiability
points, with its branch partition constructed inside the proof. -/
theorem weighted_area_formula_fiberSum_regular
    {s : Set E} {f : E → F} (hs : MeasurableSet s)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hr : ∀ x ∈ s, Injective (fderiv ℝ f x))
    {w : E → ℝ≥0∞} (hw : Measurable w) :
    (∫⁻ y, weightedAreaFiberSum s f w y ∂μHE[finrank ℝ E]) =
      ∫⁻ x in s, ENNReal.ofReal (areaJacobianAt f x) * w x ∂volume := by
  obtain ⟨t, ht, hd, hcover, hi⟩ := exists_injective_partition_of_regular hs hf hr
  have hsub (i : ℕ) : t i ⊆ s := hcover ▸ subset_iUnion t i
  have hm (i : ℕ) : Measurable (weightedAreaFiberSum (t i) f w) :=
    measurable_weightedAreaFiberSum_of_injOn (ht i)
      (fun x hx ↦ (hf x (hsub i hx)).continuousAt.continuousWithinAt) (hi i) hw
  have he : weightedAreaFiberSum s f w = fun y ↦ ∑' i, weightedAreaFiberSum (t i) f w y := by
    rw [← hcover]
    funext y
    exact weightedAreaFiberSum_iUnion t hd f w y
  rw [he, lintegral_tsum (fun i ↦ (hm i).aemeasurable)]
  conv_rhs => rw [← hcover, lintegral_iUnion ht hd]
  apply tsum_congr
  intro i
  exact weighted_area_formula_fiberSum_regular_injOn (ht i)
    (fun x hx ↦ hf x (hsub i hx)) (fun x hx ↦ hr x (hsub i hx)) (hi i) w

theorem weightedAreaFiberSum_ae_eq_regularSet {f : E → F} {K : ℝ≥0}
    (hL : LipschitzWith K f) (s : Set E) (w : E → ℝ≥0∞) :
    weightedAreaFiberSum s f w =ᵐ[μHE[finrank ℝ E]]
      weightedAreaFiberSum (s ∩ areaRegularSet f) f w := by
  have hz : ∀ᵐ y ∂(μHE[finrank ℝ E] : Measure F), y ∉ f '' (s \ areaRegularSet f) :=
    measure_eq_zero_iff_ae_notMem.mp (area_image_compl_regularSet_eq_zero hL s)
  filter_upwards [hz] with y hy
  apply weightedAreaFiberSum_congr_fiber
  intro x
  constructor
  · rintro ⟨hx, hxy⟩
    exact ⟨⟨hx, by_contra fun hn ↦ hy ⟨x, ⟨hx, hn⟩, hxy⟩⟩, hxy⟩
  · exact fun hx ↦ ⟨hx.1.1, hx.2⟩

/-- General Lipschitz fiber sums are measurable in completed Hausdorff
measure; no finite-fiber assumption is imposed. -/
theorem aemeasurable_weightedAreaFiberSum_lipschitz
    {f : E → F} {K : ℝ≥0} (hL : LipschitzWith K f)
    {s : Set E} (hs : MeasurableSet s) {w : E → ℝ≥0∞} (hw : Measurable w) :
    AEMeasurable (weightedAreaFiberSum s f w) μHE[finrank ℝ E] :=
  (measurable_weightedAreaFiberSum_of_regular (hs.inter (measurableSet_areaRegularSet f))
    (fun _ hx ↦ hx.2.1) (fun _ hx ↦ hx.2.2) hw).aemeasurable.congr
      (weightedAreaFiberSum_ae_eq_regularSet hL s w).symm

/-- Weighted noninjective area for a general Lipschitz map. Critical
points, exceptional nondifferentiability points, and infinite fibers are
all included in the displayed equality. -/
theorem weighted_area_formula_lipschitz_fiberSum
    {f : E → F} {K : ℝ≥0} (hL : LipschitzWith K f)
    {s : Set E} (hs : MeasurableSet s) {w : E → ℝ≥0∞} (hw : Measurable w) :
    (∫⁻ y, weightedAreaFiberSum s f w y ∂μHE[finrank ℝ E]) =
      ∫⁻ x in s, ENNReal.ofReal (areaJacobianAt f x) * w x ∂volume := by
  calc
    _ = ∫⁻ y, weightedAreaFiberSum (s ∩ areaRegularSet f) f w y ∂μHE[finrank ℝ E] :=
      lintegral_congr_ae (weightedAreaFiberSum_ae_eq_regularSet hL s w)
    _ = ∫⁻ x in s ∩ areaRegularSet f, ENNReal.ofReal (areaJacobianAt f x) * w x ∂volume :=
      weighted_area_formula_fiberSum_regular (hs.inter (measurableSet_areaRegularSet f))
        (fun _ hx ↦ hx.2.1) (fun _ hx ↦ hx.2.2) hw
    _ = _ := lintegral_areaJacobian_inter_regularSet hL hs w

/-- The multiplicity form with the correct source-dimensional target
Hausdorff measure. This corrects the dimension printed in (3.4). -/
theorem area_formula_lipschitz_multiplicity
    {f : E → F} {K : ℝ≥0} (hL : LipschitzWith K f)
    {s : Set E} (hs : MeasurableSet s) :
    (∫⁻ y, areaMultiplicity s f y ∂μHE[finrank ℝ E]) =
      ∫⁻ x in s, ENNReal.ofReal (areaJacobianAt f x) ∂volume := by
  simpa only [weightedAreaFiberSum_one, mul_one] using
    weighted_area_formula_lipschitz_fiberSum hL hs (w := fun _ ↦ 1) measurable_const

/-- Simon (3.5), with his literal Hausdorff normalization on both sides. -/
theorem weighted_area_formula_lipschitz_fiberSum_simon
    {f : E → F} {K : ℝ≥0} (hL : LipschitzWith K f)
    {s : Set E} (hs : MeasurableSet s) {w : E → ℝ≥0∞} (hw : Measurable w) :
    (∫⁻ y, weightedAreaFiberSum s f w y
      ∂Chapter01.simonHausdorffMeasureReal (finrank ℝ E : ℝ)) =
      ∫⁻ x in s, ENNReal.ofReal (areaJacobianAt f x) * w x
        ∂Chapter01.simonHausdorffMeasureReal (finrank ℝ E : ℝ) := by
  rw [simonHausdorffMeasureReal_nat_eq_smul_euclideanHausdorffMeasure,
    simonHausdorffMeasureReal_source_eq_smul_volume, Measure.restrict_smul,
    lintegral_smul_measure, lintegral_smul_measure,
    weighted_area_formula_lipschitz_fiberSum hL hs hw]

end
end Poincare.SimonGMT.Chapter02
