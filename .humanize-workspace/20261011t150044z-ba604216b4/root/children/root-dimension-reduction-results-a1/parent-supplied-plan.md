# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root`
- Child key: `dimension_reduction_results`
- Declaration: `Submission.dimension_reduction_results`
- Exact Lean type: `IntegerDensityAndTangentPlanes ∧ SingularSetSmallWhereDensityBelowTwo ∧ CodimensionOneRegularity`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1`
- `root.compactness_of_minimizing_currents-a1`
- `root.density_and_tangent_cones-a1`
- `root.density_one_implies_regular-a1`
- `root.abstract_dimension_reduction-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
