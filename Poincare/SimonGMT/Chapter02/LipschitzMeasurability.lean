module

public import Poincare.SimonGMT.Chapter02.Lipschitz

public section

/-!
# Simon GMT, Chapter 2, Theorem 1.8(i): image measurability

This module proves the completed-Hausdorff measurability conclusion for
natural-dimensional Hausdorff measure in Simon's general sigma-compact metric
setting.  The domain may be measurable only in the completed Hausdorff
measure.  The multiplicity assertion 1.8(ii) remains a separate obligation.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal MeasureTheory NNReal Topology

namespace Poincare.SimonGMT.Chapter02

universe u v

variable {X : Type u} {Y : Type v}

/-- Simon Theorem 1.8(i), for a Borel domain in a sigma-compact metric space.
The conclusion is `NullMeasurableSet` because Simon uses the completion of
Hausdorff measure rather than only its Borel sigma-algebra. -/
theorem nullMeasurableSet_image_of_lipschitzOn_sigmaCompact
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SigmaCompactSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {n : ℕ} {A : Set X} {f : X → Y} {K : ℝ≥0}
    (hA : MeasurableSet A) (hAfin : μHE[n] A ≠ ∞)
    (hf : LipschitzOnWith K f A) :
    NullMeasurableSet (f '' A) μHE[n] := by
  let mu : Measure X := μHE[n]
  let nu : Measure X := mu.restrict A
  let : IsFiniteMeasure nu := ⟨by
    change mu.restrict A univ < ∞
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.mpr hAfin⟩
  let : Measure.Regular nu := inferInstance
  choose C hCA hCcompact hAC using fun j : ℕ ↦
    hA.exists_isCompact_sdiff_lt (μ := nu) (measure_ne_top nu A)
      (show ((j : ℝ≥0∞)⁻¹) ≠ 0 by simp)
  let B : Set Y := ⋃ j, f '' C j
  have hBsub : B ⊆ f '' A := by
    intro y hy
    obtain ⟨j, x, hxC, rfl⟩ := mem_iUnion.mp hy
    exact ⟨x, hCA j hxC, rfl⟩
  have hBmeas : MeasurableSet B := by
    apply MeasurableSet.iUnion
    intro j
    exact (hCcompact j).image_of_continuousOn
      ((hf.mono (hCA j)).continuousOn) |>.measurableSet
  let D : Set X := A \ ⋃ j, C j
  have hDsubA : D ⊆ A := sdiff_subset
  have hDmeas : MeasurableSet D :=
    hA.diff (MeasurableSet.iUnion fun j ↦ (hCcompact j).measurableSet)
  have hnuDzero : nu D = 0 := by
    apply le_antisymm
    · apply ge_of_tendsto ENNReal.tendsto_inv_nat_nhds_zero
      filter_upwards [] with j
      exact (measure_mono (show D ⊆ A \ C j by
        intro x hx
        exact ⟨hx.1, fun hxC ↦ hx.2 (mem_iUnion.mpr ⟨j, hxC⟩)⟩)).trans (hAC j).le
    · exact bot_le
  have hDzero : μHE[n] D = 0 := by
    have hrestrict : nu D = mu D := by
      change mu.restrict A D = mu D
      rw [Measure.restrict_apply hDmeas, inter_eq_left.mpr hDsubA]
    exact hrestrict ▸ hnuDzero
  have hresSub : f '' A \ B ⊆ f '' D := by
    rintro y ⟨⟨x, hxA, rfl⟩, hxfB⟩
    refine ⟨x, ⟨hxA, ?_⟩, rfl⟩
    intro hxUnion
    obtain ⟨j, hxC⟩ := mem_iUnion.mp hxUnion
    exact hxfB (mem_iUnion.mpr ⟨j, ⟨x, hxC, rfl⟩⟩)
  have himageDzero : μHE[n] (f '' D) = 0 := by
    apply le_antisymm
    · calc
        μHE[n] (f '' D) ≤ (K : ℝ≥0∞) ^ n * μHE[n] D :=
          euclideanHausdorffMeasure_image_le_of_lipschitzOn n
            (hf.mono hDsubA)
        _ = 0 := by rw [hDzero, mul_zero]
    · exact bot_le
  have hresZero : μHE[n] (f '' A \ B) = 0 :=
    measure_mono_null hresSub himageDzero
  rw [← union_sdiff_cancel hBsub]
  exact hBmeas.nullMeasurableSet.union (NullMeasurableSet.of_null hresZero)

/-- Simon Theorem 1.8(i), completed-measurable-domain form for natural
Hausdorff dimensions.  The Borel part is handled by compact approximation;
the remaining null set has null Lipschitz image. -/
theorem nullMeasurableSet_image_of_lipschitzOn_sigmaCompact_of_nullMeasurable
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SigmaCompactSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {n : ℕ} {A : Set X} {f : X → Y} {K : ℝ≥0}
    (hA : NullMeasurableSet A (μHE[n] : Measure X)) (hAfin : μHE[n] A ≠ ∞)
    (hf : LipschitzOnWith K f A) :
    NullMeasurableSet (f '' A) μHE[n] := by
  obtain ⟨B, hBA, hBmeas, hBae⟩ := hA.exists_measurable_subset_ae_eq
  have hBfinite : μHE[n] B ≠ ∞ :=
    ne_top_of_le_ne_top hAfin (measure_mono hBA)
  have hBimage : NullMeasurableSet (f '' B) μHE[n] :=
    nullMeasurableSet_image_of_lipschitzOn_sigmaCompact hBmeas hBfinite (hf.mono hBA)
  have hDzero : μHE[n] (A \ B) = 0 := ae_le_set.mp hBae.symm.le
  have hDimage : μHE[n] (f '' (A \ B)) = 0 := by
    apply le_antisymm _ bot_le
    calc
      μHE[n] (f '' (A \ B)) ≤ (K : ℝ≥0∞) ^ n * μHE[n] (A \ B) :=
        euclideanHausdorffMeasure_image_le_of_lipschitzOn n (hf.mono sdiff_subset)
      _ = 0 := by rw [hDzero, mul_zero]
  rw [← union_sdiff_cancel hBA, image_union]
  exact hBimage.union (NullMeasurableSet.of_null hDimage)

end Poincare.SimonGMT.Chapter02
