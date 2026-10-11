module

public import Poincare.SimonGMT.Chapter02.AreaCurve

public section

/-!
# Simon GMT, Chapter 2, §3.6: Gram form of a parametrization Jacobian

For a parametrization of an `n`-dimensional set, Simon writes its Jacobian as
the square root of the determinant of the Gram matrix of its coordinate
derivatives.  The statements below derive that literal presentation from the
metric Jacobian `normDet` for an arbitrary orthonormal basis of the source.
-/

open Module

namespace Poincare.SimonGMT.Chapter02

/-- The square of the area Jacobian is the determinant of the Gram matrix of
the derivative on any orthonormal source basis. -/
theorem areaJacobianAt_sq_eq_det_gram
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (f : E → F) (y : E)
    (b : OrthonormalBasis (Fin (finrank ℝ E)) ℝ E) :
    areaJacobianAt f y ^ 2 =
      (Matrix.gram ℝ (fderiv ℝ f y <| b ·)).det := by
  rw [areaJacobianAt_eq_normDet]
  simpa using LinearMap.normDet_sq_eq_det_gram (fderiv ℝ f y).toLinearMap b

/-- Simon's coordinate formula `Jf = sqrt(det (∂ᵢf · ∂ⱼf))`, stated for an
arbitrary orthonormal source basis. -/
theorem areaJacobianAt_eq_sqrt_det_gram
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (f : E → F) (y : E)
    (b : OrthonormalBasis (Fin (finrank ℝ E)) ℝ E) :
    areaJacobianAt f y =
      Real.sqrt ((Matrix.gram ℝ (fderiv ℝ f y <| b ·)).det) := by
  rw [← areaJacobianAt_sq_eq_det_gram f y b]
  exact (Real.sqrt_sq (areaJacobianAt_nonneg f y)).symm

end Poincare.SimonGMT.Chapter02
