module

public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.MeasureTheory.Function.Jacobian
public import Poincare.SimonGMT.Chapter02.Lipschitz

public section

/-!
# Simon GMT, Chapter 2, §3: the area formula

The linear formula (3.1) is available in full generality for finite-dimensional
real inner-product spaces.  We also expose Mathlib's equal-dimensional,
injective change-of-variables theorem.  The latter is a genuine specialization
of Simon (3.2), not a replacement for his arbitrary-codomain area formula.
-/

open Function MeasureTheory Module Set
open scoped ENNReal NNReal

namespace Poincare.SimonGMT.Chapter02

/-- Simon (3.3): the metric Jacobian (area magnification factor) of `f` at
`y`, obtained from the Fréchet derivative.  Mathlib's `normDet` is exactly
the nonnegative square root of the determinant of `df⁺ df`. -/
@[expose] noncomputable def areaJacobianAt
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (f : E → F) (y : E) : ℝ :=
  (fderiv ℝ f y).normDet

/-- Unfolding lemma for the metric Jacobian.  Keeping this as a theorem makes
the defining equation available to downstream modules under Lean's module
visibility discipline. -/
theorem areaJacobianAt_eq_normDet
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (f : E → F) (y : E) :
    areaJacobianAt f y = (fderiv ℝ f y).normDet := rfl

/-- The metric Jacobian is nonnegative. -/
theorem areaJacobianAt_nonneg
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (f : E → F) (y : E) :
    0 ≤ areaJacobianAt f y :=
  (fderiv ℝ f y).normDet_nonneg

/-- The determinant formula printed in Simon (3.3). -/
theorem areaJacobianAt_sq_eq_det_adjoint_comp
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (f : E → F) (y : E) :
    areaJacobianAt f y ^ 2 =
      ((fderiv ℝ f y).adjoint ∘L fderiv ℝ f y).det :=
  (fderiv ℝ f y).normDet_sq

/-- Simon's literal square-root presentation of (3.3). -/
theorem areaJacobianAt_eq_sqrt_det_adjoint_comp
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (f : E → F) (y : E) :
    areaJacobianAt f y =
      Real.sqrt (((fderiv ℝ f y).adjoint ∘L fderiv ℝ f y).det) := by
  rw [← areaJacobianAt_sq_eq_det_adjoint_comp]
  exact (Real.sqrt_sq (areaJacobianAt_nonneg f y)).symm

/-- Simon (3.1): normalized Hausdorff measure of the image under a linear map
is multiplied by its metric Jacobian `normDet`.  Mathlib's `normDet` is the
nonnegative square root of `det (L* L)`. -/
theorem linear_area_formula
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F]
    (L : E →ₗ[ℝ] F) (A : Set E) :
    μHE[finrank ℝ E] (L '' A) =
      ENNReal.ofReal L.normDet * μHE[finrank ℝ E] A :=
  L.euclideanHausdorffMeasure_image A

/-- The algebraic identity behind the Jacobian in Simon (3.1) and (3.3). -/
theorem linear_jacobian_sq_eq_det_adjoint_comp
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (L : E →ₗ[ℝ] F) :
    (L.normDet ^ 2 : ℝ) = (L.adjoint ∘ₗ L).det :=
  L.normDet_sq

/-- Equal-dimensional injective case of Simon (3.2), stated for a general
additive Haar measure.  The source's higher-codimension formula uses `normDet`
instead of the ordinary determinant and remains a separate obligation. -/
theorem injective_area_formula_equal_dimension
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {A : Set E} {f : E → E} {f' : E → E →L[ℝ] E}
    (hA : MeasurableSet A)
    (hf' : ∀ x ∈ A, HasFDerivWithinAt f (f' x) A x)
    (hinj : InjOn f A) :
    μ (f '' A) = ∫⁻ x in A, ENNReal.ofReal |(f' x).det| ∂μ := by
  exact (lintegral_abs_det_fderiv_eq_addHaar_image μ hA hf' hinj).symm

end Poincare.SimonGMT.Chapter02
