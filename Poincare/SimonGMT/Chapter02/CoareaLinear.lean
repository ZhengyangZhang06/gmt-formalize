module

public import Poincare.SimonGMT.Chapter02.CoareaLinearAlgebra
public import Poincare.SimonGMT.Chapter02.AreaLinearWeighted

@[expose] public section

/-!
# Simon (6.2): linear coarea

The fibers carry actual ambient Hausdorff measure. The orthogonal
factorization is constructed from the given linear map, and its determinant
is identified with Simon's `sqrt(det(L L*))`.
-/

open Function MeasureTheory Module Set Filter
open scoped ENNReal NNReal InnerProductSpace

namespace Poincare.SimonGMT.Chapter02
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F]

/-- Volume change of variables between different Euclidean model spaces,
also for a target weight not independently known measurable. -/
theorem lintegral_linearEquiv_normDet (e : E ≃ₗ[ℝ] F) (g : F → ℝ≥0∞) :
    (∫⁻ y, g y ∂volume) =
      ENNReal.ofReal e.toLinearMap.normDet * ∫⁻ x, g (e x) ∂volume := by
  have h := weighted_linear_area_formula e.toLinearMap e.injective MeasurableSet.univ g
  have hr : range e.toLinearMap = univ := range_eq_univ.mpr e.surjective
  rw [image_univ, hr, setLIntegral_univ, setLIntegral_univ,
    InnerProductSpace.euclideanHausdorffMeasure_eq_volume, e.finrank_eq,
    InnerProductSpace.euclideanHausdorffMeasure_eq_volume] at h
  exact h

/-- An isometric parametrization of a fiber of the given surjective map. -/
def linearCoareaFiberEmbedding (L : E →ₗ[ℝ] F) (hL : Surjective L)
    (y : F) (z : L.ker) : E :=
  (coareaCoordinates L).symm
    (projectionFiberEmbedding ((coareaHorizontalEquiv L hL).symm y) z)

theorem isometry_linearCoareaFiberEmbedding (L : E →ₗ[ℝ] F) (hL : Surjective L) (y : F) :
    Isometry (linearCoareaFiberEmbedding L hL y) :=
  (coareaCoordinates L).symm.isometry.comp (isometry_projectionFiberEmbedding _)

theorem range_linearCoareaFiberEmbedding (L : E →ₗ[ℝ] F) (hL : Surjective L) (y : F) :
    range (linearCoareaFiberEmbedding L hL y) = {x | L x = y} := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    rw [mem_ofPred_eq, ← coareaHorizontalLinear_coordinates L]
    change coareaHorizontalEquiv L hL
      ((coareaCoordinates L) ((coareaCoordinates L).symm
        (projectionFiberEmbedding ((coareaHorizontalEquiv L hL).symm y) z))).fst = y
    rw [(coareaCoordinates L).apply_symm_apply]
    exact (coareaHorizontalEquiv L hL).apply_symm_apply y
  · intro hx
    refine ⟨(coareaCoordinates L x).snd, ?_⟩
    apply (coareaCoordinates L).injective
    change (coareaCoordinates L) ((coareaCoordinates L).symm _) = coareaCoordinates L x
    rw [(coareaCoordinates L).apply_symm_apply]
    have he : (coareaHorizontalEquiv L hL).symm y = (coareaCoordinates L x).fst := by
      apply (coareaHorizontalEquiv L hL).injective
      rw [(coareaHorizontalEquiv L hL).apply_symm_apply]
      exact hx.symm.trans (coareaHorizontalLinear_coordinates L x).symm
    rw [he]
    rfl

/-- Exact integration along a linear fiber. -/
theorem lintegral_linearCoareaFiber (L : E →ₗ[ℝ] F) (hL : Surjective L)
    (g : E → ℝ≥0∞) (y : F) :
    (∫⁻ x in {x | L x = y}, g x
      ∂Chapter01.simonHausdorffMeasureReal (finrank ℝ L.ker : ℝ)) =
        ∫⁻ z : L.ker, g (linearCoareaFiberEmbedding L hL y z) ∂volume := by
  rw [simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure,
    ← range_linearCoareaFiberEmbedding L hL y,
    ← (isometry_linearCoareaFiberEmbedding L hL y).map_euclideanHausdorffMeasure,
    InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
  exact (isometry_linearCoareaFiberEmbedding L hL y).isClosedEmbedding.measurableEmbedding.lintegral_map g

/-- Weighted linear coarea for a surjective map, with no finiteness or
support restrictions on the completed-measurable nonnegative weight. -/
theorem coarea_linear_lintegral_surjective (L : E →ₗ[ℝ] F) (hL : Surjective L)
    {g : E → ℝ≥0∞} (hg : AEMeasurable g volume) :
    ENNReal.ofReal (coareaLinearJacobian L) * (∫⁻ x, g x ∂volume) =
      ∫⁻ y : F, ∫⁻ x in {x | L x = y}, g x
        ∂Chapter01.simonHausdorffMeasureReal (finrank ℝ L.ker : ℝ) ∂volume := by
  symm
  simp only [lintegral_linearCoareaFiber L hL]
  rw [lintegral_linearEquiv_normDet (coareaHorizontalEquiv L hL)]
  change ENNReal.ofReal (coareaHorizontalLinear L).normDet * _ = _
  rw [coareaHorizontalLinear_normDet hL]
  congr 1
  have hfun : (fun y : L.kerᗮ ↦ ∫⁻ z : L.ker,
      g (linearCoareaFiberEmbedding L hL (coareaHorizontalEquiv L hL y) z)) =
      (fun y : L.kerᗮ ↦ ∫⁻ z : L.ker,
        g ((coareaCoordinates L).symm (projectionFiberEmbedding y z))) := by
    funext y
    simp only [linearCoareaFiberEmbedding, LinearEquiv.symm_apply_apply]
  rw [hfun]
  have hq : AEMeasurable (fun p ↦ g ((coareaCoordinates L).symm p)) volume :=
    hg.comp_quasiMeasurePreserving (coareaCoordinates L).symm.measurePreserving.quasiMeasurePreserving
  have hp := coarea_projection_lintegral hq
  simp only [simonHausdorffMeasureReal_finrank_eq_volume, lintegral_projectionFiber] at hp
  rw [← hp]
  exact (coareaCoordinates L).symm.measurePreserving.lintegral_comp_emb
    (coareaCoordinates L).symm.toMeasurableEquiv.measurableEmbedding g

/-- The ambient Hausdorff measure of a linear slice is exactly its fiber
coordinate volume, including nonmeasurable individual slices. -/
theorem linear_slice_hausdorff_eq_volume (L : E →ₗ[ℝ] F) (hL : Surjective L)
    (A : Set E) (y : F) :
    Chapter01.simonHausdorffMeasureReal (finrank ℝ L.ker : ℝ)
        (A ∩ {x | L x = y}) =
      volume (linearCoareaFiberEmbedding L hL y ⁻¹' A) := by
  rw [simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure,
    ← range_linearCoareaFiberEmbedding L hL y]
  simpa only [InnerProductSpace.euclideanHausdorffMeasure_eq_volume] using
    ((isometry_linearCoareaFiberEmbedding L hL y).euclideanHausdorffMeasure_preimage
      (d := finrank ℝ L.ker) A).symm

/-- Linear coarea for a surjective map and an arbitrary Lebesgue-measurable
source set. The proof uses completed-set Fubini, so it does not tacitly
replace the source hypothesis by Borel measurability. -/
theorem coarea_linear_surjective (L : E →ₗ[ℝ] F) (hL : Surjective L)
    {A : Set E} (hA : NullMeasurableSet A volume) :
    ENNReal.ofReal (coareaLinearJacobian L) * volume A =
      ∫⁻ y : F, Chapter01.simonHausdorffMeasureReal (finrank ℝ L.ker : ℝ)
        (A ∩ {x | L x = y}) ∂volume := by
  symm
  simp only [linear_slice_hausdorff_eq_volume L hL]
  rw [lintegral_linearEquiv_normDet (coareaHorizontalEquiv L hL)]
  change ENNReal.ofReal (coareaHorizontalLinear L).normDet * _ = _
  rw [coareaHorizontalLinear_normDet hL]
  congr 1
  have hfun : (fun y : L.kerᗮ ↦ volume
      (linearCoareaFiberEmbedding L hL (coareaHorizontalEquiv L hL y) ⁻¹' A)) =
      (fun y : L.kerᗮ ↦ volume (projectionFiberEmbedding y ⁻¹'
        ((coareaCoordinates L).symm ⁻¹' A))) := by
    funext y
    congr 1
    ext z
    simp only [mem_preimage, linearCoareaFiberEmbedding, LinearEquiv.symm_apply_apply]
  rw [hfun]
  have hq := hA.preimage (coareaCoordinates L).symm.measurePreserving.quasiMeasurePreserving
  have hp := coarea_projection hq
  simp only [projection_slice_hausdorff_eq_volume,
    simonHausdorffMeasureReal_finrank_eq_volume] at hp
  rw [hp]
  exact (coareaCoordinates L).symm.measurePreserving.measure_preimage hA

/-- Almost every target fiber of a rank-deficient linear map is empty. -/
theorem ae_empty_fiber_of_not_surjective (L : E →ₗ[ℝ] F) (hL : ¬ Surjective L) :
    ∀ᵐ y ∂volume, {x | L x = y} = ∅ := by
  have hr : volume (range L) = 0 := Measure.addHaar_submodule volume L.range
    (fun h ↦ hL (LinearMap.range_eq_top.mp h))
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hr] with y hy
  apply eq_empty_iff_forall_notMem.mpr
  exact fun x hx ↦ hy ⟨x, hx⟩

/-- Simon (6.2) in full, including the deficient-rank case, with the
literal determinant, fiber dimension `n-m`, and Lebesgue-measurable sets. -/
theorem coarea_linear (L : E →ₗ[ℝ] F) {A : Set E}
    (hA : NullMeasurableSet A volume) :
    ENNReal.ofReal (Real.sqrt (L ∘ₗ L.adjoint).det) * volume A =
      ∫⁻ y : F, Chapter01.simonHausdorffMeasureReal
        ((finrank ℝ E - finrank ℝ F : ℕ) : ℝ) (A ∩ {x | L x = y}) ∂volume := by
  rw [← coareaLinearJacobian_eq_sqrt_det]
  by_cases hL : Surjective L
  · simpa only [coarea_kernel_finrank hL] using coarea_linear_surjective L hL hA
  · rw [(coareaLinearJacobian_eq_zero_iff L).mpr hL, ENNReal.ofReal_zero, zero_mul]
    symm
    apply (lintegral_congr_ae (g := fun _ : F ↦ 0) ?_).trans lintegral_zero
    filter_upwards [ae_empty_fiber_of_not_surjective L hL] with y hy
    simp only [hy, inter_empty, measure_empty]

/-- The complete weighted linear case of Simon (6.6), also when the map
has deficient target rank. -/
theorem coarea_linear_lintegral (L : E →ₗ[ℝ] F)
    {g : E → ℝ≥0∞} (hg : AEMeasurable g volume) :
    ENNReal.ofReal (Real.sqrt (L ∘ₗ L.adjoint).det) * (∫⁻ x, g x ∂volume) =
      ∫⁻ y : F, ∫⁻ x in {x | L x = y}, g x
        ∂Chapter01.simonHausdorffMeasureReal
          ((finrank ℝ E - finrank ℝ F : ℕ) : ℝ) ∂volume := by
  rw [← coareaLinearJacobian_eq_sqrt_det]
  by_cases hL : Surjective L
  · simpa only [coarea_kernel_finrank hL] using coarea_linear_lintegral_surjective L hL hg
  · rw [(coareaLinearJacobian_eq_zero_iff L).mpr hL, ENNReal.ofReal_zero, zero_mul]
    symm
    apply (lintegral_congr_ae (g := fun _ : F ↦ 0) ?_).trans lintegral_zero
    filter_upwards [ae_empty_fiber_of_not_surjective L hL] with y hy
    simp only [hy, setLIntegral_empty]

end
end Poincare.SimonGMT.Chapter02
