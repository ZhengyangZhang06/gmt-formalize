# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.cube_bv_median-a1.integer_median-a1.median_minimizes-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-85cada813c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.cube_bv_median-a1.integer_median-a1`
- Child key: `median_minimizes`
- Declaration: `Submission.cmcdt_cbm_im_median_minimizes`
- Exact Lean type: `∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (u : X → ℝ) (β : ℝ), IsProbabilityMeasure μ → Integrable u μ → 1 / 2 ≤ μ.real {x | β ≤ u x} → 1 / 2 ≤ μ.real {x | u x ≤ β} → ∀ c : ℝ, ∫ x, |u x - β| ∂μ ≤ ∫ x, |u x - c| ∂μ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
