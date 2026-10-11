module

public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Poincare.SimonGMT.Chapter03.Rectifiable

public section

/-!
# Simon GMT, Chapter 3, §2: tangential differential and Jacobians

The definitions in this file take the approximate tangent plane as an explicit
argument.  For a countably rectifiable set, Chapter 3 §1 supplies that plane
almost everywhere once the still-open existence direction of Theorem 1.6 is
available.  Keeping the plane explicit makes the differential and both
Jacobians usable without hiding that dependency.
-/

open Module

namespace Poincare.SimonGMT.Chapter03

universe u v

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Simon (2.2): the differential of `f` restricted to the tangent plane
`P`.  At points where the ambient derivative is absent, Mathlib's `fderiv`
uses the zero map; Simon only uses this construction at almost-everywhere
differentiability points. -/
noncomputable def tangentialDifferential
    (P : Submodule ℝ E) (f : E → F) (x : E) : P →L[ℝ] F :=
  (fderiv ℝ f x).domRestrict P

/-- Simon (2.1): the tangential gradient of a real-valued function is the
orthogonal projection of its ambient gradient to the tangent plane. -/
noncomputable def tangentialGradient
    (P : Submodule ℝ E) (f : E → ℝ) (x : E) : E :=
  P.starProjection ((fderiv ℝ f x).adjoint 1)

/-- Simon (2.3): the tangential area Jacobian
`sqrt(det ((d_P f)† ∘ d_P f))`.  Mathlib's `normDet` is precisely this
nonnegative metric Jacobian. -/
noncomputable def tangentialJacobian
    (P : Submodule ℝ E) (f : E → F) (x : E) : ℝ :=
  (tangentialDifferential P f x).toLinearMap.normDet

/-- Simon (2.7): the tangential coarea Jacobian
`sqrt(det (d_P f ∘ (d_P f)†))`.  It is the metric Jacobian of the adjoint. -/
noncomputable def tangentialCoareaJacobian
    (P : Submodule ℝ E) (f : E → F) (x : E) : ℝ :=
  (tangentialDifferential P f x).toLinearMap.adjoint.normDet

theorem tangentialJacobian_nonneg
    (P : Submodule ℝ E) (f : E → F) (x : E) :
    0 ≤ tangentialJacobian P f x :=
  LinearMap.normDet_nonneg _

theorem tangentialCoareaJacobian_nonneg
    (P : Submodule ℝ E) (f : E → F) (x : E) :
    0 ≤ tangentialCoareaJacobian P f x :=
  LinearMap.normDet_nonneg _

@[simp] theorem tangentialDifferential_zero (P : Submodule ℝ E) (x : E) :
    tangentialDifferential P (0 : E → F) x = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  simp [tangentialDifferential]

@[simp] theorem tangentialGradient_zero (P : Submodule ℝ E) (x : E) :
    tangentialGradient P (0 : E → ℝ) x = 0 := by
  simp [tangentialGradient]

end Poincare.SimonGMT.Chapter03
