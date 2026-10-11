module

public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Poincare.SimonGMT.Chapter01.Basic

public section

/-!
# Simon GMT, Theorem 1.13: Carathéodory's metric criterion
-/

open Set

namespace Poincare.SimonGMT.Chapter01

universe u

variable {X : Type u} [EMetricSpace X]

/-- Simon Theorem 1.13.  Mathlib calls the separation-additivity hypothesis
`OuterMeasure.IsMetric`; its theorem proves that the Borel σ-algebra is
contained in the Carathéodory σ-algebra. -/
theorem caratheodory_metric_criterion
    {μ : MeasureTheory.OuterMeasure X} (hμ : μ.IsMetric) :
    borel X ≤ μ.caratheodory :=
  hμ.borel_le_caratheodory

end Poincare.SimonGMT.Chapter01
