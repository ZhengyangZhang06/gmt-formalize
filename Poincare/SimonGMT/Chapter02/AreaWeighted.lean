module

public import Poincare.SimonGMT.Chapter02.Area

public section

/-!
# Simon GMT, Chapter 2, §3: weighted equal-dimensional area formula

Mathlib currently supplies the full differentiable change-of-variables theorem
for equal-dimensional finite-dimensional spaces.  This module states its
nonnegative weighted form using the metric Jacobian from Simon (3.3).  It is an
exact specialization of the injective case of (3.5); the higher-codimension and
noninjective multiplicity formulas remain separate obligations.
-/

open Function MeasureTheory Set
open scoped ENNReal

namespace Poincare.SimonGMT.Chapter02

noncomputable section

/-- In equal dimensions the metric Jacobian is the absolute determinant. -/
theorem normDet_eq_abs_det_of_same_space
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : E →L[ℝ] E) :
    L.normDet = |L.det| :=
  L.normDet_eq_abs_det

/-- Injective, equal-dimensional specialization of Simon (3.5), for an
arbitrary nonnegative target weight.  The right-hand factor is the genuine
metric Jacobian `normDet`, not a separately postulated density. -/
theorem weighted_area_formula_equal_dimension
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {A : Set E} {f : E → E} {f' : E → E →L[ℝ] E}
    (hA : MeasurableSet A)
    (hf' : ∀ x ∈ A, HasFDerivWithinAt f (f' x) A x)
    (hinj : InjOn f A) (g : E → ℝ≥0∞) :
    ∫⁻ y in f '' A, g y ∂μ =
      ∫⁻ x in A, ENNReal.ofReal (f' x).normDet * g (f x) ∂μ := by
  simpa only [normDet_eq_abs_det_of_same_space] using
    (lintegral_image_eq_lintegral_abs_det_fderiv_mul μ hA hf' hinj g)

end

end Poincare.SimonGMT.Chapter02
