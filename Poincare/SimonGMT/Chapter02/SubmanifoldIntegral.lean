module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Poincare.SimonGMT.Chapter02.SecondFundamentalFormCalculus

@[expose] public section

/-!
# Simon GMT, Chapter 2, (4.30): the integral curvature decomposition

The differential part of (4.30) is linearity of tangential divergence.  Once
the tangential divergence theorem and the pointwise normal identity (4.29)
are supplied, the displayed integral formula follows without any further
geometric assumption.  This module records that deduction for genuine
Bochner integrals.
-/

open InnerProductSpace MeasureTheory Module

namespace Poincare.SimonGMT.Chapter02

universe u v

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The pointwise splitting used in Simon's deduction of (4.30): the
divergence of `X` is the sum of the divergences of `X - X⊥` and `X⊥`. -/
theorem submanifoldDivergenceAt_eq_tangent_add_normal
    (T : Submodule ℝ E) {X Xnormal : E → E} {x : E}
    (hX : DifferentiableAt ℝ X x)
    (hXnormal : DifferentiableAt ℝ Xnormal x) :
    submanifoldDivergenceAt T X x =
      submanifoldDivergenceAt T (X - Xnormal) x +
        submanifoldDivergenceAt T Xnormal x := by
  rw [submanifoldDivergenceAt_sub T hX hXnormal]
  ring

/-- Simon (4.30), as the exact integral consequence of the tangential
divergence theorem and (4.29).  Here `boundaryFlux` is `X · η` on the smooth
boundary; the theorem is independent of the particular boundary model used
to establish the tangential divergence theorem. -/
theorem integral_submanifoldDivergence_eq_curvature_sub_boundary
    {B : Type v} [MeasurableSpace E] [MeasurableSpace B]
    (T : E → Submodule ℝ E) (X Xnormal H : E → E)
    (boundaryFlux : B → ℝ) (mu : Measure E) (boundaryMeasure : Measure B)
    (hX : ∀ x, DifferentiableAt ℝ X x)
    (hXnormal : ∀ x, DifferentiableAt ℝ Xnormal x)
    (htangent : Integrable
      (fun x ↦ submanifoldDivergenceAt (T x) (X - Xnormal) x) mu)
    (hnormal : Integrable
      (fun x ↦ submanifoldDivergenceAt (T x) Xnormal x) mu)
    (hnormal_eq : ∀ᵐ x ∂mu,
      submanifoldDivergenceAt (T x) Xnormal x = -inner ℝ (X x) (H x))
    (htangent_eq :
      ∫ x, submanifoldDivergenceAt (T x) (X - Xnormal) x ∂mu =
        -∫ z, boundaryFlux z ∂boundaryMeasure) :
    ∫ x, submanifoldDivergenceAt (T x) X x ∂mu =
      -∫ x, inner ℝ (X x) (H x) ∂mu -
        ∫ z, boundaryFlux z ∂boundaryMeasure := by
  have hsplit : ∀ᵐ x ∂mu,
      submanifoldDivergenceAt (T x) X x =
        submanifoldDivergenceAt (T x) (X - Xnormal) x +
          submanifoldDivergenceAt (T x) Xnormal x := by
    filter_upwards [] with x
    exact submanifoldDivergenceAt_eq_tangent_add_normal (T x) (hX x) (hXnormal x)
  rw [integral_congr_ae hsplit, integral_add htangent hnormal, htangent_eq,
    integral_congr_ae hnormal_eq, integral_neg]
  ring

end Poincare.SimonGMT.Chapter02
