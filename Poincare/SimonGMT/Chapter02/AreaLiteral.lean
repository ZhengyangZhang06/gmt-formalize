module

public import Poincare.SimonGMT.Chapter02.AreaDomain
public import Poincare.SimonGMT.Chapter01.EuclideanNormalization

@[expose] public section

/-!
# Exact Simon normalization in the area formula

The Chapter 1 isodiametric theorem now identifies the literal normalization
with Euclidean volume. This file discharges, rather than assumes, the scalar
which the earlier area transport results deliberately retained.
-/

open MeasureTheory Module Set Metric
open scoped ENNReal NNReal

namespace Poincare.SimonGMT.Chapter02
noncomputable section

/-- The explicit scalar in the area transport is exactly one, as a consequence
of the proved Chapter 1 normalization theorem. -/
@[simp] theorem simonAreaNormalization_eq_one (n : ℕ) :
    simonAreaNormalization n = 1 := by
  have h := simonHausdorffMeasureReal_nat_eq_smul_euclideanHausdorffMeasure
    (X := EuclideanSpace ℝ (Fin n)) n
  rw [Chapter01.simonHausdorffMeasureReal_euclidean_eq_volume] at h
  have he : (μHE[n] : Measure (EuclideanSpace ℝ (Fin n))) = volume := by
    simpa using (InnerProductSpace.euclideanHausdorffMeasure_eq_volume
      (V := EuclideanSpace ℝ (Fin n)))
  rw [he] at h
  have hball := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin n)) ↦
    μ (Metric.ball 0 1)) h
  rw [Measure.smul_apply, smul_eq_mul] at hball
  exact (ENNReal.mul_left_inj
    (measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin n)) zero_lt_one).ne'
    measure_ball_lt_top.ne).mp (by simpa using hball.symm)

/-- Literal Simon measure agrees with Euclidean Hausdorff measure in every
ambient metric space, not only in the model Euclidean space. -/
theorem simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (n : ℕ) :
    Chapter01.simonHausdorffMeasureReal (X := X) (n : ℝ) = μHE[n] := by
  rw [simonHausdorffMeasureReal_nat_eq_smul_euclideanHausdorffMeasure,
    simonAreaNormalization_eq_one, one_smul]

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F]

/-- Exact source-volume normalization for every finite-dimensional inner
product space. -/
theorem simonHausdorffMeasureReal_finrank_eq_volume :
    (Chapter01.simonHausdorffMeasureReal (finrank ℝ E : ℝ) : Measure E) = volume := by
  rw [simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure,
    InnerProductSpace.euclideanHausdorffMeasure_eq_volume]

/-- Simon (3.2), now with source Lebesgue measure and no residual scalar. -/
theorem injective_area_formula_lipschitzOn_simon_volume
    {s : Set E} (hs : NullMeasurableSet s volume)
    {f : E → F} {K : ℝ≥0} (hL : LipschitzOnWith K f s) (hi : InjOn f s) :
    Chapter01.simonHausdorffMeasureReal (finrank ℝ E : ℝ) (f '' s) =
      ∫⁻ x in s, ENNReal.ofReal (areaJacobianWithin f s x) ∂volume := by
  rw [simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure]
  exact injective_area_formula_lipschitzOn hs hL hi

/-- The corrected source-dimensional multiplicity formula (3.4), with
literal Simon target measure and exact source Lebesgue normalization. -/
theorem area_formula_lipschitzOn_multiplicity_simon_volume
    {s : Set E} (hs : NullMeasurableSet s volume)
    {f : E → F} {K : ℝ≥0} (hL : LipschitzOnWith K f s) :
    (∫⁻ y, areaMultiplicity s f y
      ∂Chapter01.simonHausdorffMeasureReal (finrank ℝ E : ℝ)) =
      ∫⁻ x in s, ENNReal.ofReal (areaJacobianWithin f s x) ∂volume := by
  rw [area_formula_lipschitzOn_multiplicity_simon hs hL,
    simonAreaNormalization_eq_one, one_mul]

end
end Poincare.SimonGMT.Chapter02
