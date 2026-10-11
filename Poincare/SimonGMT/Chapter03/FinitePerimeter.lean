module

public import Poincare.SimonGMT.Chapter02.BV
public import Poincare.SimonGMT.Chapter03.Rectifiable

public section

/-!
# Simon GMT, Chapter 3, §4: locally finite perimeter and reduced boundary

This module records the source definitions preceding De Giorgi's theorem.
`HasLocallyFinitePerimeter` is the literal local-BV characteristic-function
condition.  `FinitePerimeterRepresentation` packages the Radon boundary
measure, unit polar normal, and Gauss--Green identity (4.1).  Finally,
`reducedBoundary` is the set in (4.2), defined by convergence of normalized
normal averages to a unit vector.

Existence of the representation from local BV and De Giorgi's rectifiability
theorem are not asserted here.
-/

open Filter MeasureTheory Set
open scoped CompactlySupported ENNReal NNReal Topology

namespace Poincare.SimonGMT.Chapter03

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A set has locally finite perimeter in `U` when its characteristic
function belongs to `BV_loc(U)`, exactly as in the paragraph preceding Simon
(4.1). -/
def HasLocallyFinitePerimeter (U A : Set E) : Prop :=
  Chapter02.IsLocallyBV U (A.indicator fun _ ↦ (1 : ℝ))

/-- Data in Simon (4.1): a locally finite boundary measure, a measurable unit
normal, and the distributional Gauss--Green identity.  The measure is modeled
on the ambient Euclidean space and used only through its restriction to `U`.
-/
structure FinitePerimeterRepresentation (U A : Set E) where
  boundaryMeasure : Measure E
  finiteOnCompact : IsFiniteMeasureOnCompacts boundaryMeasure
  normal : E → E
  normal_aemeasurable : AEMeasurable normal (boundaryMeasure.restrict U)
  norm_normal : ∀ᵐ x ∂boundaryMeasure.restrict U, ‖normal x‖ = 1
  gaussGreen : ∀ g : C_c(E, E), Chapter02.IsC1TestField g → tsupport g ⊆ U →
    ∫ x in A ∩ U, Chapter02.euclideanDivergence (g : E → E) x ∂volume =
      -∫ x in U, inner ℝ (g x) (normal x) ∂boundaryMeasure

namespace FinitePerimeterRepresentation

variable {U A : Set E} (R : FinitePerimeterRepresentation U A)

/-- The normalized average appearing in Simon (4.2).  Inverses are
totalized, as usual in Lean; membership in the reduced boundary forces this
quantity to have a unit limit and hence excludes a persistently zero
denominator. -/
noncomputable def normalAverage (x : E) (r : ℝ) : E :=
  (R.boundaryMeasure (Metric.ball x r)).toReal⁻¹ •
    ∫ y in Metric.ball x r, R.normal y ∂R.boundaryMeasure

/-- Simon (4.2): points in `U` where the normalized normal average converges
as the radius decreases to zero and its limit has length one. -/
def reducedBoundary : Set E :=
  {x | x ∈ U ∧ ∃ v : E,
    Tendsto (R.normalAverage x) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds v) ∧ ‖v‖ = 1}

theorem mem_reducedBoundary_iff {x : E} :
    x ∈ R.reducedBoundary ↔
      x ∈ U ∧ ∃ v : E,
        Tendsto (R.normalAverage x) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds v) ∧
          ‖v‖ = 1 :=
  Iff.rfl

/-- The source's reduced-boundary normal `ν_E(x)`, chosen from the unit
limit in (4.2).  It is totalized by zero away from the reduced boundary. -/
noncomputable def reducedBoundaryNormal (x : E) : E :=
  by
    classical
    exact if hx : x ∈ R.reducedBoundary then Classical.choose hx.2 else 0

theorem tendsto_normalAverage_reducedBoundaryNormal {x : E}
    (hx : x ∈ R.reducedBoundary) :
    Tendsto (R.normalAverage x) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (R.reducedBoundaryNormal x)) := by
  rw [reducedBoundaryNormal, dif_pos hx]
  exact (Classical.choose_spec hx.2).1

theorem norm_reducedBoundaryNormal {x : E} (hx : x ∈ R.reducedBoundary) :
    ‖R.reducedBoundaryNormal x‖ = 1 := by
  rw [reducedBoundaryNormal, dif_pos hx]
  exact (Classical.choose_spec hx.2).2

theorem reducedBoundary_subset_domain : R.reducedBoundary ⊆ U :=
  fun _ hx ↦ hx.1

end FinitePerimeterRepresentation

end Poincare.SimonGMT.Chapter03
