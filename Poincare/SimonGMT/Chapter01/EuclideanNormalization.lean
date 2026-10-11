module

public import Poincare.SimonGMT.Chapter01.SteinerSymmetry

@[expose] public section

/-!
# Simon GMT, Chapter 1, (2.9) and (2.10)

The isodiametric inequality is proved using successive compact coordinate
Steiner replacements.  The sharp inequality then identifies the literal
Gamma-normalized Hausdorff content with volume at every positive scale,
and hence identifies the limiting Hausdorff outer measure as well.
-/

open Metric Set MeasureTheory
open scoped ENNReal

namespace Poincare.SimonGMT.Chapter01

/-- Simon (2.10), the Euclidean isodiametric inequality, for every set in
every natural dimension.  The extended diameter gives the source convention
for unbounded sets; no measurability hypothesis is imposed. -/
theorem simon_theorem_2_10 (n : ℕ) (A : Set (EuclideanSpace ℝ (Fin n))) :
    volume A ≤ realUnitBallVolume (n : ℝ) * (ediam A / 2) ^ (n : ℝ) := by
  by_cases hn : n = 0
  · subst n
    simpa only [Nat.cast_zero] using simon_isodiametric_zero A
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  rw [ENNReal.rpow_natCast]
  by_cases hfin : ediam A = ∞
  · rw [hfin, ENNReal.top_div_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ∞),
      ENNReal.top_pow hn,
      ENNReal.mul_top (realUnitBallVolume_pos (by positivity : 0 ≤ (n : ℝ))).ne']
    exact le_top
  have hbounded : Bornology.IsBounded A := isBounded_iff_ediam_ne_top.mpr hfin
  obtain ⟨K, _, hdiam, hvol, hsym⟩ :=
    exists_centrally_symmetric_compact_replacement hbounded.isCompact_closure
  rw [ediam_closure] at hdiam
  calc
    volume A ≤ volume (closure A) := measure_mono subset_closure
    _ ≤ volume K := hvol
    _ ≤ realUnitBallVolume (n : ℝ) * (ediam K / 2) ^ n :=
      volume_le_normalized_diameter_pow_of_neg_mem hnpos K hsym
    _ ≤ realUnitBallVolume (n : ℝ) * (ediam A / 2) ^ n := by gcongr

/-- The sharp reverse comparison in Simon (2.9).  Unlike the equality,
this direction does not require the scale to be positive. -/
theorem volume_le_simonHausdorffContentOuter_euclidean (n : ℕ) (δ : ℝ≥0∞) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))).toOuterMeasure ≤
      simonHausdorffContentOuter (n : ℝ) δ := by
  rw [simonHausdorffContentOuter,
    OuterMeasure.smul_boundedBy (realUnitBallVolume_ne_top (n : ℝ))]
  apply OuterMeasure.le_boundedBy.mpr
  intro C
  change volume C ≤ realUnitBallVolume (n : ℝ) * simonHausdorffCoverCost (n : ℝ) δ C
  by_cases hC : ediam C < δ
  · rw [simonHausdorffCoverCost,
      extend_eq (m := fun C (_ : ediam C < δ) => (ediam C / 2) ^ (n : ℝ)) (s := C) hC]
    exact simon_theorem_2_10 n C
  · rw [simonHausdorffCoverCost,
      extend_eq_top (m := fun C (_ : ediam C < δ) => (ediam C / 2) ^ (n : ℝ)) (s := C) hC,
      ENNReal.mul_top (realUnitBallVolume_pos (by positivity : 0 ≤ (n : ℝ))).ne']
    exact le_top

/-- Literal Hausdorff content equals Lebesgue outer measure at every
positive extended scale in every Euclidean dimension. -/
theorem simonHausdorffContentOuter_euclidean_eq_volume (n : ℕ)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    simonHausdorffContentOuter (X := EuclideanSpace ℝ (Fin n)) (n : ℝ) δ =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).toOuterMeasure := by
  by_cases hn : n = 0
  · subst n
    simpa only [Nat.cast_zero] using simonHausdorffContentOuter_euclidean_zero_eq_volume hδ
  exact le_antisymm (simonHausdorffContentOuter_euclidean_le_volume (Nat.pos_of_ne_zero hn) hδ)
    (volume_le_simonHausdorffContentOuter_euclidean n δ)

/-- The literal Gamma-normalized limiting Hausdorff outer measure equals
Lebesgue outer measure in every Euclidean dimension. -/
theorem simonHausdorffOuterMeasureReal_euclidean_eq_volume (n : ℕ) :
    simonHausdorffOuterMeasureReal (X := EuclideanSpace ℝ (Fin n)) (n : ℝ) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).toOuterMeasure := by
  rw [simonHausdorffOuterMeasureReal]
  refine le_antisymm (iSup_le fun δ => iSup_le fun hδ =>
    (simonHausdorffContentOuter_euclidean_eq_volume n hδ).le) ?_
  apply le_iSup_of_le 1
  apply le_iSup_of_le (by norm_num : (0 : ℝ≥0∞) < 1)
  exact (simonHausdorffContentOuter_euclidean_eq_volume n (by norm_num : (0 : ℝ≥0∞) < 1)).ge

/-- The corresponding Borel measures have exactly the same normalization. -/
theorem simonHausdorffMeasureReal_euclidean_eq_volume (n : ℕ) :
    (simonHausdorffMeasureReal (n : ℝ) : Measure (EuclideanSpace ℝ (Fin n))) = volume := by
  apply Measure.ext
  intro A _
  change (simonHausdorffMeasureReal (n : ℝ)).toOuterMeasure A =
    (volume : Measure (EuclideanSpace ℝ (Fin n))).toOuterMeasure A
  rw [simonHausdorffMeasureReal_toOuterMeasure (by positivity),
    simonHausdorffOuterMeasureReal_euclidean_eq_volume]

/-- Simon (2.9), with the literal content, the literal limiting Hausdorff
construction, all subsets, and every positive scale. -/
theorem simon_theorem_2_9 (n : ℕ) {δ : ℝ≥0∞} (hδ : 0 < δ)
    (A : Set (EuclideanSpace ℝ (Fin n))) :
    volume A = simonHausdorffOuterValue (n : ℝ) A ∧
      simonHausdorffOuterValue (n : ℝ) A = simonHausdorffContent (n : ℝ) δ A := by
  simp [simonHausdorffOuterValue, simonHausdorffContent,
    simonHausdorffOuterMeasureReal_euclidean_eq_volume,
    simonHausdorffContentOuter_euclidean_eq_volume n hδ]

end Poincare.SimonGMT.Chapter01
