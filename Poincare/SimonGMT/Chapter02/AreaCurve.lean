module

public import Poincare.SimonGMT.Chapter02.AreaMultiplicity
public import Mathlib.Geometry.Manifold.Riemannian.Basic

public section

/-!
# Simon GMT, Chapter 2, §3: the one-dimensional Jacobian

This file identifies the metric Jacobian of a linear map whose domain is the
real line with the norm of its value at `1`.  Applied to a Fréchet derivative,
this is the pointwise algebraic identity behind the speed integrand in the
arc-length formula (3.6).
-/

open Module
open MeasureTheory Set
open scoped Bundle Manifold

namespace Poincare.SimonGMT.Chapter02

/-- A real-linear map out of the real line has metric Jacobian equal to the
norm of the image of the unit tangent vector. -/
theorem normDet_real_domain
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (L : ℝ →ₗ[ℝ] F) :
    L.normDet = ‖L 1‖ := by
  have hsquare : L.normDet ^ 2 = ‖L 1‖ ^ 2 := by
    calc
      L.normDet ^ 2 =
          (Matrix.gram ℝ (L <| OrthonormalBasis.singleton (Fin 1) ℝ ·)).det := by
        simpa using LinearMap.normDet_sq_eq_det_gram L
          (OrthonormalBasis.singleton (Fin 1) ℝ)
      _ = ‖L 1‖ ^ 2 := by
        rw [Matrix.det_fin_one]
        simp [Matrix.gram]
  nlinarith [L.normDet_nonneg, norm_nonneg (L 1)]

/-- The pointwise one-dimensional area Jacobian is the norm of the Fréchet
derivative applied to the unit tangent vector. -/
theorem areaJacobianAt_curve_eq_norm_fderiv_one
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (f : ℝ → F) (t : ℝ) :
    areaJacobianAt f t = ‖fderiv ℝ f t 1‖ := by
  rw [areaJacobianAt_eq_normDet]
  exact normDet_real_domain (fderiv ℝ f t).toLinearMap

/-- Equivalently, the one-dimensional area Jacobian is the usual speed
`‖deriv f t‖`. -/
theorem areaJacobianAt_curve_eq_norm_deriv
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (f : ℝ → F) (t : ℝ) :
    areaJacobianAt f t = ‖deriv f t‖ := by
  simpa only [fderiv_apply_one_eq_deriv] using
    areaJacobianAt_curve_eq_norm_fderiv_one f t

/-- Integrating the curve area Jacobian gives Mathlib's extended path length.
This packages the speed-integral half of Simon's space-curve example without
assuming the still-missing equality with Hausdorff measure of the image. -/
theorem lintegral_areaJacobianAt_curve_eq_pathELength
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (f : ℝ → F) (a b : ℝ) :
    ∫⁻ t in Icc a b, ENNReal.ofReal (areaJacobianAt f t) =
      Manifold.pathELength 𝓘(ℝ, F) f a b := by
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  apply setLIntegral_congr_fun measurableSet_Icc
  intro t _
  change ENNReal.ofReal (areaJacobianAt f t) = ‖mfderiv% f t 1‖ₑ
  have hone : NormedSpace.fromTangentSpace t
      (1 : TangentSpace 𝓘(ℝ, ℝ) t) = (1 : ℝ) := rfl
  rw [areaJacobianAt_curve_eq_norm_fderiv_one, ofReal_norm,
    mfderiv_eq_fderiv, enorm_tangentSpace_vectorSpace]
  simp [hone]

end Poincare.SimonGMT.Chapter02
