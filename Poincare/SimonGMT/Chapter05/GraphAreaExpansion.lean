module

public import Poincare.SimonGMT.Chapter05.Basic

public section

/-!
# Simon GMT, Chapter 5, §1: exact graph-area expansion

This module records the exact identity in Simon (1.1) for the graph area
integrand and for its integral over a ball.  The separate analytic estimates
on the Taylor remainder in (1.2) are not folded into the definition and remain
a distinct obligation.
-/

open MeasureTheory Metric
open scoped RealInnerProductSpace

namespace Poincare.SimonGMT.Chapter05

noncomputable section

/-- The exact pointwise decomposition used in Simon (1.1). -/
theorem graphAreaIntegrand_expansion {n ℓ : ℕ}
    (P : Fin n → EuclideanSpace ℝ (Fin ℓ)) :
    graphAreaIntegrand P =
      1 + (1 / 2 : ℝ) * frobeniusSq P + areaRemainder P := by
  rw [areaRemainder]
  ring

/-- The graph Gram matrix is unchanged when every derivative vector changes
sign. -/
@[simp] theorem graphGram_neg {n ℓ : ℕ}
    (P : Fin n → EuclideanSpace ℝ (Fin ℓ)) :
    graphGram (-P) = graphGram P := by
  ext i j
  simp [graphGram]

/-- The quadratic Frobenius term is even. -/
@[simp] theorem frobeniusSq_neg {n ℓ : ℕ}
    (P : Fin n → EuclideanSpace ℝ (Fin ℓ)) :
    frobeniusSq (-P) = frobeniusSq P := by
  simp [frobeniusSq]

/-- The graph-area integrand is an even function of the derivative matrix. -/
@[simp] theorem graphAreaIntegrand_neg {n ℓ : ℕ}
    (P : Fin n → EuclideanSpace ℝ (Fin ℓ)) :
    graphAreaIntegrand (-P) = graphAreaIntegrand P := by
  simp [graphAreaIntegrand]

/-- Consequently, the exact Taylor remainder used in (1.1) is even. -/
@[simp] theorem areaRemainder_neg {n ℓ : ℕ}
    (P : Fin n → EuclideanSpace ℝ (Fin ℓ)) :
    areaRemainder (-P) = areaRemainder P := by
  simp [areaRemainder]

/-- Simon (1.1): the graph area is the integral of the constant, quadratic,
and exact remainder terms.  No integrability side condition is needed because
the equality is pointwise before integration. -/
theorem graphArea_expansion {n ℓ : ℕ}
    (center : EuclideanSpace ℝ (Fin n)) (radius : ℝ)
    (Du : EuclideanSpace ℝ (Fin n) → Fin n → EuclideanSpace ℝ (Fin ℓ)) :
    graphArea center radius Du =
      ∫ x in ball center radius,
        (1 + (1 / 2 : ℝ) * frobeniusSq (Du x) + areaRemainder (Du x))
        ∂Measure.euclideanHausdorffMeasure n := by
  unfold graphArea
  refine integral_congr_ae ?_
  exact Filter.Eventually.of_forall fun x ↦ graphAreaIntegrand_expansion (Du x)

end

end Poincare.SimonGMT.Chapter05
