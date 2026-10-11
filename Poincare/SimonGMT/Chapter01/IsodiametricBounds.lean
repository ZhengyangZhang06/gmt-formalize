module

public import Poincare.SimonGMT.Chapter01.EuclideanHausdorffUpper

@[expose] public section

/-!
# Established cases of the isodiametric inequality

These results prove the sharp inequality in dimension one, and for centrally
symmetric sets in every positive dimension, without measurability assumptions.
They also record the compact-enlargement and geometric containment steps used
by Simon's proof.  The general Steiner-symmetrization step is not assumed.
-/

open Metric Set MeasureTheory
open scoped ENNReal

namespace Poincare.SimonGMT.Chapter01

/-- The compact-enlargement step in Simon's proof of (2.10). -/
theorem exists_compact_superset_same_ediam
    {n : ℕ} {A : Set (EuclideanSpace ℝ (Fin n))} (hA : Bornology.IsBounded A) :
    ∃ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K ∧ A ⊆ K ∧
      ediam K = ediam A ∧ volume A ≤ volume K :=
  ⟨closure A, hA.isCompact_closure, subset_closure, ediam_closure A,
    measure_mono subset_closure⟩

/-- A bounded centrally symmetric set lies in the centered ball with half
its diameter.  This is the final geometric step of Simon's symmetrization
argument, valid in every real normed space. -/
theorem subset_closedBall_half_diam_of_neg_mem
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {A : Set E}
    (hA : Bornology.IsBounded A) (hneg : ∀ x ∈ A, -x ∈ A) :
    A ⊆ closedBall 0 (diam A / 2) := by
  intro x hx
  have hdist := dist_le_diam_of_mem hA hx (hneg x hx)
  rw [dist_eq_norm_sub, sub_neg_eq_add, ← two_smul ℝ, norm_smul] at hdist
  norm_num at hdist
  rw [mem_closedBall, dist_zero_right]
  linarith

/-- The sharp Euclidean isodiametric inequality for every centrally
symmetric set, including unbounded and nonmeasurable sets. -/
theorem volume_le_normalized_diameter_pow_of_neg_mem
    {n : ℕ} (hn : 0 < n) (A : Set (EuclideanSpace ℝ (Fin n)))
    (hneg : ∀ x ∈ A, -x ∈ A) :
    volume A ≤ realUnitBallVolume (n : ℝ) * (ediam A / 2) ^ n := by
  by_cases hfin : ediam A = ∞
  · rw [hfin, ENNReal.top_div_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ∞),
      ENNReal.top_pow hn.ne',
      ENNReal.mul_top (realUnitBallVolume_pos (by positivity : 0 ≤ (n : ℝ))).ne']
    exact le_top
  have hA : Bornology.IsBounded A := isBounded_iff_ediam_ne_top.mpr hfin
  calc
    volume A ≤ volume (closedBall 0 (diam A / 2)) :=
      measure_mono (subset_closedBall_half_diam_of_neg_mem hA hneg)
    _ = realUnitBallVolume (n : ℝ) * ENNReal.ofReal (diam A / 2) ^ n :=
      volume_euclidean_closedBall_eq hn _ _
    _ = realUnitBallVolume (n : ℝ) * (ediam A / 2) ^ n := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
        ENNReal.ofReal_ofNat, diam, ENNReal.ofReal_toReal hfin]

/-- Simon (2.10) in dimension one, for every set. -/
theorem simon_isodiametric_one (A : Set (EuclideanSpace ℝ (Fin 1))) :
    volume A ≤ realUnitBallVolume 1 * (ediam A / 2) ^ (1 : ℝ) := by
  rw [realUnitBallVolume_one, ENNReal.rpow_one,
    ENNReal.mul_div_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num)]
  let e : ℝ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 1) :=
    (OrthonormalBasis.singleton (Fin 1) ℝ).repr
  calc
    volume A = volume (e ⁻¹' A) :=
      (e.measurePreserving.measure_preimage_emb e.toHomeomorph.toMeasurableEquiv.measurableEmbedding A).symm
    _ ≤ ediam (e ⁻¹' A) := Real.volume_le_diam _
    _ = ediam A := e.toIsometryEquiv.ediam_preimage A

/-- The literal content equals length at every positive scale in
one-dimensional Euclidean space. -/
theorem simonHausdorffContentOuter_euclidean_one_eq_volume
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    simonHausdorffContentOuter (X := EuclideanSpace ℝ (Fin 1)) 1 δ =
      (volume : Measure (EuclideanSpace ℝ (Fin 1))).toOuterMeasure := by
  refine le_antisymm (by
    simpa only [Nat.cast_one] using
      (simonHausdorffContentOuter_euclidean_le_volume (n := 1) (by decide) hδ)) ?_
  rw [simonHausdorffContentOuter, OuterMeasure.smul_boundedBy (realUnitBallVolume_ne_top 1)]
  apply OuterMeasure.le_boundedBy.mpr
  intro C
  change volume C ≤ realUnitBallVolume 1 * simonHausdorffCoverCost 1 δ C
  by_cases hC : ediam C < δ
  · rw [simonHausdorffCoverCost,
      extend_eq (m := fun C (_ : ediam C < δ) => (ediam C / 2) ^ (1 : ℝ)) (s := C) hC]
    exact simon_isodiametric_one C
  · simp [simonHausdorffCoverCost, extend, hC, realUnitBallVolume_one]

/-- The zero-dimensional Euclidean volume of the whole space is one. -/
theorem volume_euclidean_zero_univ :
    volume (univ : Set (EuclideanSpace ℝ (Fin 0))) = 1 := by
  have hu : ({0} : Set (EuclideanSpace ℝ (Fin 0))) = univ :=
    (singleton_nonempty 0).eq_univ
  rw [← hu, ← simonHausdorffMeasure_euclidean_eq_volume 0,
    simonHausdorffMeasure_zero_singleton]

/-- Simon (2.10) also holds in the zero-dimensional space. -/
theorem simon_isodiametric_zero (A : Set (EuclideanSpace ℝ (Fin 0))) :
    volume A ≤ realUnitBallVolume 0 * (ediam A / 2) ^ (0 : ℝ) := by
  simpa only [realUnitBallVolume_zero, ENNReal.rpow_zero, mul_one,
    volume_euclidean_zero_univ] using
    (measure_mono (μ := (volume : Measure (EuclideanSpace ℝ (Fin 0)))) (subset_univ A))

/-- Every positive-scale literal zero-dimensional content equals volume on
the zero-dimensional Euclidean space. -/
theorem simonHausdorffContentOuter_euclidean_zero_eq_volume
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    simonHausdorffContentOuter (X := EuclideanSpace ℝ (Fin 0)) 0 δ =
      (volume : Measure (EuclideanSpace ℝ (Fin 0))).toOuterMeasure := by
  have hcost (C : Set (EuclideanSpace ℝ (Fin 0))) : simonHausdorffCoverCost 0 δ C = 1 := by
    have hC : C.Subsingleton := fun _ _ _ _ => Subsingleton.elim _ _
    simp [simonHausdorffCoverCost, extend, hC.ediam_eq, hδ]
  rw [simonHausdorffContentOuter, realUnitBallVolume_zero, one_smul]
  apply le_antisymm
  · intro C
    rcases C.eq_empty_or_nonempty with rfl | hC
    · simp
    · rw [hC.eq_univ]
      change OuterMeasure.boundedBy (simonHausdorffCoverCost 0 δ) univ ≤ volume univ
      rw [volume_euclidean_zero_univ]
      exact (OuterMeasure.boundedBy_le _).trans_eq (hcost _)
  · apply OuterMeasure.le_boundedBy.mpr
    intro C
    rw [hcost]
    change volume C ≤ 1
    exact (measure_mono (subset_univ C)).trans_eq volume_euclidean_zero_univ

/-- The full every-positive-scale identity of Simon (2.9) in dimensions
zero and one.  Higher-dimensional normalization is not asserted here. -/
theorem simon_theorem_2_9_zero_one {n : ℕ} (hn : n ≤ 1)
    {δ : ℝ≥0∞} (hδ : 0 < δ) (A : Set (EuclideanSpace ℝ (Fin n))) :
    volume A = simonHausdorffOuterValue (n : ℝ) A ∧
      simonHausdorffOuterValue (n : ℝ) A = simonHausdorffContent (n : ℝ) δ A := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl | rfl
  · simp [simonHausdorffOuterValue, simonHausdorffContent,
      simonHausdorffOuterMeasureReal_euclidean_zero_eq_volume,
      simonHausdorffContentOuter_euclidean_zero_eq_volume hδ]
  · simp [simonHausdorffOuterValue, simonHausdorffContent,
      simonHausdorffOuterMeasureReal_euclidean_one_eq_volume,
      simonHausdorffContentOuter_euclidean_one_eq_volume hδ]

end Poincare.SimonGMT.Chapter01
